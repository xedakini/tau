/* Credit where due: the inspiration for this code
   was a posting to comp.lang.c for computing pi:
     From: jasonp@Glue.umd.edu (Jason Stratos Papadopoulos)
     Newsgroups: sci.math,comp.lang.c
     Subject: here's a program to calculate pi, in C, version 4.5
     Date: 16 Feb 1997 07:25:10 GMT
     Message-ID: <5e6com$j3e@hecate.umd.edu>

   The core idea of computing N*(4*atan(1/5)-atan(1/239)) remains, and
   the basic approach to multi-precision calculation is the same. Otherwise,
   apart from some random vestiges (such as error messages for the argument
   parsing), this is a complete rewrite in rust.  Also note that the default
   has been changed here to compute 8*atan(1) (aka "tau") instead of
   4*atan(1) (aka "pi").  --kpp 2022-10-01
*/

// --- customizable section ---

// these two related declarations need to be kept in sync:
const WORDDIGITS :usize = 9; //number of decimal digits in each computation unit
type Xword = i64; // must be able to hold signed values up to 100**WORDDIGITS

// more pedestrian modifiable values:
const SCALE     :Xword = 8;       //we will compute SCALE*atan(1); thus 8 will compute tau
const LINELEN   :usize = 80;      //keep output lines no longer than this length
const ERRPAD    :usize = 2;       //words of padding to absorb rounding errors; heuristic
const MINDIGITS :usize = 18;      //base-10 digits; somewhat arbitrary constraint?
const DEFDIGITS :usize = 288;     //the default number of base-10 digits to output
const MAXDIGITS :usize = 1200000; //base-10 digits; somewhat arbitrary limit?

// --- there ought to be no moving parts left below this point ---

#[macro_use]
extern crate static_assertions;
const_assert!(MINDIGITS <= DEFDIGITS && DEFDIGITS <= MAXDIGITS);

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
        tan(a+b) = (tan(a) + tan(b)) / (1 - tan(a)*tan(b))

      Let tan(x) = A; equiv. x = atan(A), then
        tan(2x) = (A+A) / (1-A*A)
        2x = 2 atan(A) = atan(2A / (1-A^2))
      Thus:
        4 atan(1/5)
          = 2 atan((2/5) / (1 - 1/25))
          = 2 atan(5/12)
          = atan((10/12) / (1 - 25/144))
          = atan(120/119)

      Now,
        4*atan(1/5) - atan(1/239)
          = atan(120/119) + atan(-1/239)
          = atan(tan(atan(120/119) + atan(-1/239)))
          = atan((120/119 - 1/239) / (1 - 120/119 * -1/239))
          = atan(1)
          QED

   Putting this all together, and running calculations using multi-precision
   arithmetic with "digit"s of base BASE is how this code accomplishes its task.
 */


//-----------------------------------------------------------------
// derive "BASE" from WORDDIGITS
const fn pow10(mut n: usize) -> Xword {
    let mut v :Xword = 1;
    while 0 < n { v *= 10; n -= 1 }
    v
}
const BASE :Xword = pow10(WORDDIGITS); //we adjust computations to be in this base

#[derive(Default)]
struct Data {
    term: Vec<Xword>,    // representation of current term-to-add
    sum: Vec<Xword>,     // representation of running sum
    firstnonzero: usize, // index of first non-zero word in the term Vec
    denom: Xword,        // the denominator of the current iteration
}

//-----------------------------------------------------------------
// The routines in this section are performance-critical, to the point that
// we write (most of) them as macros.  Normal in-lining isn't aggressive
// enough: we need the compiler to see that certain "variables" are in fact
// compile-time constants, and optimize accordingly.
//
// We assume that the compiler can recognize divmod optimization opportunities
// (rather than emitting one assembly instruction for / and a second for %);
// this might require requesting -O3 optimization?

// we divide a large number of values by the same divisor; on most machines,
// division is much slower than multiplication; libdivide allows us to compute
// a multiplicate inverse which can be used to achieve the bulk divisions using
// bulk multiplications instead - a big performance win!
use libdivide::Divider;

// Written as a macro so that the compiler can observe a constant $sub and $denom
// (This isn't an inner loop, so perhaps this is a gratuitous optimization.)
macro_rules! init_term {
    ($d: ident, $numer:expr, $denom:expr, $sub:expr) => { {
        let mut r = $numer;
        for (t,s) in $d.term.iter_mut()
                 .zip($d.sum.iter_mut()) {
            *t = r / $denom;
            r = r % $denom * BASE;
            if $sub { *s -= *t }
            else    { *s += *t }
        }
        $d.firstnonzero=0; $d.denom=3;
    } }
}

// We write this as a macro so that the compiler sees $nn and $sub as
// constants. This is an innermost-loop calculation, so optimizing it
// is important for performance.
macro_rules! atan_grind {
    ($r1:ident, $r2:ident, $t:ident, $s:ident,
     $nn:expr, $d:expr, $dinv:expr, $sub:expr) => { {
        // compute new term
        let v = $r1 * BASE + *$t;
        $r1 = v % $nn; // $nn should be a compile-time constant, so the
        *$t = v / $nn; // compiler should handle a libdivide-like optimization

        // apply newly computed term to the running sum
        let v = $r2 * BASE + *$t;
        let q = v / $dinv; // use libdivide to replace actual division with
        $r2 = v - q*$d;    // multiplication-by-inverse logic
        if $sub { *$s -= q } // $sub should be a compile-time constant, so this
        else    { *$s += q } // should reduce to a single branch-free operation
    } }
}

// We write this a macro so that $n*$n and $subfirst can be passed through
// to atan_grind!() as compile-time constants.
macro_rules! atan_iter {
    ($d:ident, $n:expr, $subfirst:expr) => { {
        let mut remainder4 :Xword = 0;
        let mut remainder3 :Xword = 0;
        let mut remainder2 :Xword = 0;
        let mut remainder1 :Xword = 0;
        // we should see about using the libdivide crate to pre-compute inverses for these...
        let denom0 = $d.denom;
        let denom2 = $d.denom + 2;
        let denom0inv = Divider::new(denom0).expect("libdivide initializaton error");
        let denom2inv = Divider::new(denom2).expect("libdivide initializaton error");
        $d.denom += 4;

        for (t,s) in $d.term[$d.firstnonzero..].iter_mut()
                 .zip($d.sum[$d.firstnonzero..].iter_mut()) {
            atan_grind!(remainder1, remainder2, t, s, $n*$n, denom0, &denom0inv, $subfirst);
            atan_grind!(remainder3, remainder4, t, s, $n*$n, denom2, &denom2inv, !$subfirst);
        }

        let nword = $d.term.len();
        while $d.firstnonzero < nword && $d.term[$d.firstnonzero] == 0 {
            $d.firstnonzero += 1;
        }
    } }
}

// No macro-magic is required here
fn fixup(d: &mut Data) {
    // fix-up any out-of-spec digits
    for i in (1..d.sum.len()).rev() {
        // digits are typically close-enough to in-spec that doing
        // a division will be more expensive than this loop pair
        while d.sum[i] < 0     { d.sum[i]+=BASE; d.sum[i-1]-=1 }
        while BASE <= d.sum[i] { d.sum[i]-=BASE; d.sum[i-1]+=1 }
    }
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
    for v in sum[1..=sum.len()-ERRPAD].iter() {
        if c >= WORDS_PER_LINE { println!(""); c = 0 }
        c += 1;
        print!(" {value:0>width$}", width=WORDDIGITS, value=v);
    }
    println!("");
}

fn main() {
    let nwords = get_nwords() + ERRPAD;
    let mut d = Data {
        term: vec![0; nwords],
        sum:  vec![0; nwords],
        ..Default::default()
    };

    use cpu_time::ProcessTime;
    let start = ProcessTime::now();

    init_term!(d, SCALE*4, 5, false);
    while d.firstnonzero < nwords { atan_iter!(d, 5, true) }
    init_term!(d, SCALE, 239, true);
    while d.firstnonzero < nwords { atan_iter!(d, 239, false) }
    fixup(&mut d);

    let elapsed = start.elapsed();
    printout(d.sum);
    println!("Computation time = {:.2?}", elapsed);
}
