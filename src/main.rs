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
const WORDDIGITS :usize = 12; //number of decimal digits in each computation unit
type Xword = i64; // must be signed and able to hold all possible intermediate values

// more pedestrian modifiable values:
const SCALE     :Xword = 8;         //we will compute SCALE*atan(1); thus 8 computes tau
const LINELEN   :usize = 80;        //keep output lines no longer than this length
const DEFDIGITS :usize = 288;       //the default number of base-10 digits to output
const MAXDIGITS :usize = 6_400_000; //base-10 digits; keep intermediate calcs within Xword

// --- there ought to be no moving parts left below this point ---

// derive "BASE" from WORDDIGITS; we adjust computations to be in this base
const BASE :Xword = (10 as Xword).pow(WORDDIGITS as u32);

#[macro_use]
extern crate static_assertions;
const_assert!((-1 as Xword) < 0 && 0 < Xword::BITS); //Xword must be a signed integer type
const_assert!(WORDDIGITS <= DEFDIGITS && DEFDIGITS <= MAXDIGITS); //sanity constraints
const_assert!(1 <= WORDDIGITS && WORDDIGITS < LINELEN); //more sanity constraints

// The following assumes that atan(1/5) is the slowest-converging
// sub-expression to be used; also, since (5 as f64).log10() is apparently
// not const(!?), we approximate log10(5) as 0.698; furthermore, expression
// is written to work using only integer arithmetic.
const_assert!(BASE*(MAXDIGITS as Xword) < Xword::MAX / 1000 * 698); //Xword big enough?
// (BASE as f64 * MAXDIGITS as f64) < (Xword::MAX as f64) * (x as f64).log10()
//    ... where atan(1/x) is slowest-coverging of the atan() terms that we evaluate

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

// We divide a large number of values by the same divisor; on most machines,
// division is much slower than multiplication; libdivide allows us to
// compute a multiplicative inverse which can be used to achieve the bulk
// divisions using bulk multiplications instead - a big performance win!
use libdivide::Divider;

enum SumOp { Increment, Decrement }

// We write this as a macro so that the compiler sees $xxinv and $op as
// constants.  This is an innermost-loop calculation, so optimizing
// it is important for performance.
macro_rules! atan_grind {
    ($r1:ident, $r2:ident, $term:ident, $sum:ident,
     $xxinv:expr, $d:expr, $dinv:expr, $op:expr) => { {
        // compute new term
        let v = $r1 * BASE + *$term;
        // We assume that, at least for release builds, the compiler will
        // do libdivide-like optimization on the compile-time constant $xxinv
        *$term = v / $xxinv;
        $r1 = v % $xxinv;

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
        let mut term = Vec::new();
        let mut r = $scale;
        term.resize_with($nwords, ||{ let v = r / $xinv; r = r % $xinv * BASE; v });
        let (mut sum, mut firstnonzero, mut denom) = (term.to_vec(), 0, 1);
        let mut next_denom = || -> (Xword, Divider<Xword>, Xword, Xword) {
            denom += 2; //captured by closure
            let inv = Divider::new(denom).expect("libdivide initialization error");
            (denom, inv, 0, 0)
        };
        'outer: loop {
            let (denom0, denom0inv, mut remainder0, mut remainder1) = next_denom();
            let (denom2, denom2inv, mut remainder2, mut remainder3) = next_denom();
            for (term,sum) in term[firstnonzero..].iter_mut()
                          .zip(sum[firstnonzero..].iter_mut()) {
                atan_grind!(remainder0, remainder1, term, sum, $xinv*$xinv,
                            denom0, &denom0inv, SumOp::Decrement);
                atan_grind!(remainder2, remainder3, term, sum, $xinv*$xinv,
                            denom2, &denom2inv, SumOp::Increment);
            }
            while term[firstnonzero] == 0 {
                firstnonzero += 1;
                if firstnonzero >= $nwords { break 'outer sum }
            }
        }
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
        if digits < WORDDIGITS {
            println!("Setting to minimum of {} digits.", WORDDIGITS);
            digits = WORDDIGITS;
        } else if MAXDIGITS < digits {
            println!("Clamping to maximum of {} digits.", MAXDIGITS);
            digits = MAXDIGITS;
        }
    } else {
        println!("\nUsage: tau NumberOfDigits\n\n\
             NumberOfDigits must be in the range {} to {}.\n\n\
             Using a default of {} digits.",
             WORDDIGITS, MAXDIGITS, DEFDIGITS);
        digits = DEFDIGITS;
    }

    //one left-of-decimal word; one word for error terms:
    //1+ digits.div_ceil(WORDDIGITS) + 1 //error[E0658]: nightly 'int_roundings'
    1  +    1+(digits-1)/WORDDIGITS  + 1
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
    let nwords = get_nwords();
    use cpu_time::ProcessTime;
    let start = ProcessTime::now();

    // this formulation: atan(1) = 8*atan(1/10) - atan(1/239) - 4*atan(1/515)
    // alternative formulation: atan(1) = 4*atan(1/5) - atan(1/239)
    let mut s = atan_loop!(nwords, SCALE*8,  10);
    let  s239 = atan_loop!(nwords, SCALE*1, 239);
    let  s515 = atan_loop!(nwords, SCALE*4, 515);

    // combine sums (into s) while fixing-up any out-of-spec digits
    let mut carry :Xword = 0;
    for (i, s) in s.iter_mut().enumerate().rev() {
        let mut v = carry + *s - s239[i] - s515[i];
        carry = 0;
        // digits are typically close-enough to in-spec that doing
        // a division will be more expensive than this loop pair
        while v < 0     { v+=BASE; carry-=1 }
        while BASE <= v { v-=BASE; carry+=1 }
        *s = v;
    }
    assert!(carry == 0);

    let elapsed = start.elapsed();
    printout(s);
    println!("Computation time = {:.2?}", elapsed);
}
