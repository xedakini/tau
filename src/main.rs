/* Credit where due: the inspiration for this code
   was a posting to comp.lang.c for computing pi:
     From: jasonp@Glue.umd.edu (Jason Stratos Papadopoulos)
     Newsgroups: sci.math,comp.lang.c
     Subject: here's a program to calculate pi, in C, version 4.5
     Date: 16 Feb 1997 07:25:10 GMT
     Message-ID: <5e6com$j3e@hecate.umd.edu>

   The core idea of computing N*atan(1) [for a mathematically
   equivalent but computationally better behaved expression] remains,
   and the basic approach to multi-precision calculation is the
   same. Otherwise, apart from some random vestiges (such as error
   messages for the argument parsing), this is a complete rewrite
   in rust.  Also note that the default has been changed here to
   compute 8*atan(1) (aka "tau") instead of 4*atan(1) (aka "pi").
   --kpp 2022-10-04
*/

// --- customizable section ---

// these two related declarations need to be kept in sync:
const WORDDIGITS :usize = 9; //number of decimal digits in each computation unit
type Xword = i64; // must be able to hold signed values up to 100**WORDDIGITS

// more pedestrian modifiable values:
const SCALE     :Xword = 8;       //we will compute SCALE*atan(1); thus 8 will compute tau
const LINELEN   :usize = 80;      //keep output lines no longer than this length
const MINDIGITS :usize = 18;      //base-10 digits; somewhat arbitrary constraint?
const DEFDIGITS :usize = 288;     //the default number of base-10 digits to output
const MAXDIGITS :usize = 1200000; //base-10 digits; somewhat arbitrary limit?

// --- there ought to be no moving parts left below this point ---

#[macro_use]
extern crate static_assertions;
const_assert!((((2*WORDDIGITS) as f64)*std::f64::consts::LOG10_2)
            < ((std::mem::size_of::<Xword>()*8-1) as f64));
const_assert!(MINDIGITS <= DEFDIGITS && DEFDIGITS <= MAXDIGITS);

// derive "BASE" from WORDDIGITS; we adjust computations to be in this base
const BASE :Xword = (10 as Xword).pow(WORDDIGITS as u32);

/*
   Taylor-Maclaurin series for atan(x) (when abs(x) <= 1):
       atan(x) = \sum_0^\infty (-1)^n x^{2n+1} / {2n+1}
               = x - x^3/3 + x^5/5 - ...

    The heart of the calculation here uses the identity
      tau/8 = pi/4 = atan(1) = 4*atan(1/5) - atan(1/239)
    The Taylor-Maclaurin series for atan(1) itself converges rather slowly,
    but each of atan(1/5) and atan(1/239) converge at a reasonable rate.

    Demonstration that 4*atan(1/5) - atan(1/239) == atan(1):
      Recall that:
        tan(x+y) = (tan(x) + tan(y)) / (1 - tan(x)*tan(y))
      and, by the nature of inverse functions,
        x = atan(tan(x)) = tan(atan(x))
      Therefore:
        atan(x) + atan(y)
          = atan( tan(atan(x) + atan(y)) )
          = atan( (tan(atan(x)) + tan(atan(y))) / (1 - tan(atan(x))*tan(atan(y))) )
          = atan( (x + y) / (1 - x*y) )
      And, as a special case,
        2 atan(x) = atan(2x / (1-x^2))

      Thus:
        4 atan(1/5)
          = 2 atan((2/5) / (1 - 1/25))
          = 2 atan(5/12)
          = atan((10/12) / (1 - 25/144))
          = atan(120/119)
      And therefore:
        4*atan(1/5) - atan(1/239)
          = atan(120/119) + atan(-1/239)
          = atan((120/119 - 1/239) / (1 - 120/119 * -1/239))
          = atan(1)
          QED


    Another identity is atan(1) = 8*atan(1/10) - atan(1/239) - 4*atan(1/515).
    This has the disadvantage of requiring three passes, but has the advantage
    that the series for 1/10 converges faster than the series for 1/5, and
    the 1/515 series converges very rapidly.

    The validity of this identity is demonstrated by:
        8 atan(1/10)
          = 4 atan(20/99)
          = 2 atan(3960/9401)
          = atan(74455920/72697201)

        4 atan(1/515)
          = 2 atan(515/132612)
          = atan(136590360/17585677319)

        8 atan(1/10) - atan(1/239) - 4 atan(1/515)
	      = atan(74455920/72697201) - atan(1758719/147153121)
	      = atan(1)
          QED

   Putting this all together, and running calculations using multi-precision
   arithmetic with "digit"s of base BASE is how this code accomplishes its task.
 */

//-----------------------------------------------------------------
// The routines in this section are performance-critical, to the point that
// we write (most of) them as macros.  Normal in-lining isn't aggressive
// enough: we need the compiler to see that certain "variables" are in fact
// compile-time constants, and optimize accordingly.

#[derive(Default)]
struct Data {
    term: Vec<Xword>,    // representation of current term-to-add
    sum: Vec<Xword>,     // representation of running sum
    firstnonzero: usize, // index of first non-zero word in the term Vec
    denom: Xword,        // the denominator of the current iteration
}

enum SumOp { Increment, Decrement }

// We divide a large number of values by the same divisor; on most machines,
// division is much slower than multiplication; libdivide allows us to
// compute a multiplicative inverse which can be used to achieve the bulk
// divisions using bulk multiplications instead - a big performance win!
use libdivide::Divider;

// Written as a macro so that the compiler can observe a constant $denom.
// (This isn't an inner loop, so perhaps this is a gratuitous optimization.)
macro_rules! init_term {
    ($d: ident, $nwords:expr, $numer:expr, $denom:expr) => { {
        $d.term.truncate(0);
        let mut r = $numer;
        $d.term.resize_with($nwords,
                  ||{ let v = r / $denom; r = r % $denom * BASE; v });
        $d.sum.truncate(0);
        $d.sum.extend_from_slice($d.term.as_slice());
        $d.firstnonzero = 0;
        $d.denom = 1;
    } }
}

fn next_denom(d: &mut Data) -> (Xword, Divider<Xword>) {
    d.denom += 2;
    let inv = Divider::new(d.denom).expect("libdivide initialization error");
    (d.denom, inv)
}

// We write this as a macro so that the compiler sees $nn and $op as
// constants.  This is an innermost-loop calculation, so optimizing
// it is important for performance.
macro_rules! atan_grind {
    ($r1:ident, $r2:ident, $term:ident, $sum:ident,
     $nn:expr, $d:expr, $dinv:expr, $op:expr) => { {
        // compute new term
        let v = $r1 * BASE + *$term;
        // We assume that, at least for release builds, the compiler will
        // do libdivide-like optimization on the compile-time constant $nn
        *$term = v / $nn;
        $r1 = v % $nn;

        // apply newly computed term to the running sum
        let v = $r2 * BASE + *$term;
        let q = v / $dinv; // use libdivide to replace actual division with
        $r2 = v - q*$d;    // multiplication-by-inverse logic
        match $op {
            // $op ought to be a compile-time constant, so the generated
            // code should just become one unconditional op.
            SumOp::Increment => *$sum += q,
            SumOp::Decrement => *$sum -= q,
        }
    } }
}

// this is just a macro so that a constant $xinv is propagated aggressively
macro_rules! atan_loop {
    ($nwords:expr, $scale:expr, $xinv:expr) => { {
        let mut d = Data { ..Default::default() };
        init_term!(d, $nwords, $scale, $xinv);
        while d.firstnonzero < $nwords {
            let mut remainder1 :Xword = 0;
            let mut remainder2 :Xword = 0;
            let mut remainder3 :Xword = 0;
            let mut remainder4 :Xword = 0;
            let (denom0, denom0inv) = next_denom(&mut d);
            let (denom2, denom2inv) = next_denom(&mut d);

            for (term,sum) in d.term[d.firstnonzero..].iter_mut()
                          .zip(d.sum[d.firstnonzero..].iter_mut()) {
                atan_grind!(remainder1, remainder2, term, sum, $xinv*$xinv,
                            denom0, &denom0inv, SumOp::Decrement);
                atan_grind!(remainder3, remainder4, term, sum, $xinv*$xinv,
                            denom2, &denom2inv, SumOp::Increment);
            }

            let nword = d.term.len();
            while d.firstnonzero < nword && d.term[d.firstnonzero] == 0 {
                d.firstnonzero += 1;
            }
        }
        d.sum
    } }
}

//-----------------------------------------------------------------
fn get_nwords() -> usize {
    let mut digits :usize = 0;

    use std::env;
    if env::args().len() == 2 {
        match env::args().nth(1).expect("ndigits vanished?").parse::<usize>() {
            Ok(n)  => digits = n,
            Err(e) => println!("error parsing NumberOfDigits: {}\n", e),
        }
        if digits < MINDIGITS {
            println!("Setting to minimum of {} digits.", MINDIGITS);
            digits = MINDIGITS;
        } else if MAXDIGITS < digits {
            println!("Clamping to maximum of {} digits.", MAXDIGITS);
            digits = MAXDIGITS;
        }
    } else {
        println!("\nUsage: tau NumberOfDigits\n\n\
             NumberOfDigits must be in the range {} to {}.\n\n\
             Using a default of {} digits.",
             MINDIGITS, MAXDIGITS, DEFDIGITS);
        digits = DEFDIGITS;
    }

    //round up to nearest number of words:
    1 + (digits-1)/WORDDIGITS
}

fn printout(sum: Vec<Xword>) {
    match SCALE {
        8 => print!("tau"),
        4 => print!("pi"),
        1 => print!("atan(1)"),
        _ => print!("{}*atan(1)", SCALE),
    }
    print!(" = {}.", sum[0]);

    const WORDS_PER_LINE :usize = LINELEN / (WORDDIGITS+1);
    let mut c = WORDS_PER_LINE;
    for v in sum[1..sum.len()-1].iter() {
        if c >= WORDS_PER_LINE { println!(""); c = 0 }
        c += 1;
        print!(" {value:0>width$}", width=WORDDIGITS, value=v);
    }
    println!("");
}

fn main() {
    let nwords = 1 + get_nwords() + 1; // 1 left-of-decimal word; 1 error-terms word
    use cpu_time::ProcessTime;
    let start = ProcessTime::now();

    // alternative formulation: 4*atan(1/5) - atan(1/239)
    // this formulation: 8*atan(1/10) - atan(1/239) - atan(1/515)

    let s10; let s239; let s515;
    const USE_THREADS :bool = false;
    if USE_THREADS {
        use std::thread;
        let t10  = thread::spawn(move || { atan_loop!(nwords, SCALE*8,  10) } );
        let t239 = thread::spawn(move || { atan_loop!(nwords, SCALE*1, 239) } );
        s515 = atan_loop!(nwords, SCALE*4, 515);
        s239 = t239.join().expect("the atan(1/239) thread panicked");
        s10  = t10.join().expect("the atan(1/10) thread panicked");
    } else {
        s515 = atan_loop!(nwords, SCALE*4, 515);
        s239 = atan_loop!(nwords, SCALE*1, 239);
        s10  = atan_loop!(nwords, SCALE*8,  10);
    }

    let mut s = s10;
    // combine sums (into s) while fixing-up any out-of-spec digits
    let mut carry :Xword = 0;
    for i in (0..s.len()).rev() {
        let mut v = carry + s[i] - s239[i] - s515[i];
        carry = 0;
        // digits are typically close-enough to in-spec that doing
        // a division will be more expensive than this loop pair
        while v < 0     { v+=BASE; carry-=1 }
        while BASE <= v { v-=BASE; carry+=1 }
        s[i] = v;
    }
    assert!(carry == 0);

    let elapsed = start.elapsed();
    printout(s);
    println!("Computation time = {:.2?}", elapsed);
}
