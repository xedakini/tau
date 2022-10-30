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

// name a couple of constants that might be helpful in the next section
#[allow(dead_code)]
const SCALE_TAU  :Xword = 8;  // τ = 8 * atan(1) = tau = 2π
#[allow(dead_code)]
const SCALE_PI   :Xword = 4;  // π = 4 * atan(1) = pi = τ/2

// --- customizable section ---

// These two related declarations need to be kept in sync.  Also note
// that there is a trade-off where a large value for WORDDIGITS means
// less computation time for a given number of output digits, but it also
// limits the number of digits which can be calculated without causing
// some intermediate calculation to panic due to integer overflow.
//
// Xword may only be one of i64 or i32 (due to the need for support from the
// libdivide crate).  For Xword=i32, I suggest WORDDIGITS=4, as anything
// larger excessively constrains the maximum number of digits which can
// be computed.  For Xword=i64, I suggest WORDDIGITS=12.
type Xword = i64; // must be signed and able to hold all possible intermediate values
const WORDDIGITS :usize = 12;  //number of decimal digits in each computation unit

// more pedestrian modifiable values:
const LINELEN    :usize = 80;  //keep output lines no longer than this length (default value)
const DEFLINES   :usize = 2;   //the number of lines to output if default digit count chosen
const DEFSCALE   :Xword = SCALE_TAU; //SCALE_PI is another popular choice

// --- there ought to be no moving parts left below this point ---

// derive "BASE" from WORDDIGITS; we adjust computations to be in this base
const BASE: Xword = (10 as Xword).pow(WORDDIGITS as u32);

use static_assertions::const_assert;
const_assert!((-1 as Xword) < 0 && 0 < Xword::BITS); //Xword must be a signed integer type
const_assert!(1 <= WORDDIGITS && WORDDIGITS < LINELEN); //sanity constraints
const_assert!(((Xword::MAX / (BASE+1)) as u64) < (usize::MAX as u64));

/*
  First, note that: tau/8 = pi/4 = atan(1).

  The Taylor-Maclaurin series for atan(x) (when abs(x) <= 1) is:
      atan(x) = \sum_0^\infty (-1)^n x^{2n+1} / {2n+1}
              = x - x^3/3 + x^5/5 - ...

   The Taylor-Maclaurin series for atan(1) itself converges rather
   slowly, but by using the identity
     atan(1) = 8*atan(1/10) - atan(1/239) - 4*atan(1/515)
   we get three readily combinable terms which each converge from
   quickly to very-quickly.

   See the file "Theory.pdf" for further details.
*/

//-----------------------------------------------------------------
// The routines in this section are performance-critical, to the point that
// we write both of them as macros.  Normal in-lining isn't aggressive
// enough: we need the compiler to see that certain "variables" are in fact
// compile-time constants, and optimize accordingly.

enum SumOp { Increment, Decrement }

// We write this as a macro so that the compiler sees $xxinv and $op as
// constants.  This is an innermost-loop calculation, so optimizing
// it is important for performance.
macro_rules! atan_grind {
    ($r1:ident, $r2:ident, $term:ident, $sum:ident,
     $xxinv:expr, $d:expr, $dinv:expr, $op:expr) => {{
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
    }};
}

// this is just a macro so that a constant $xinv is propagated aggressively
macro_rules! atan_loop {
    ($nwords:expr, $scale:expr, $xinv:expr) => {{
        let mut term = Vec::new();
        let mut r = $scale;
        term.resize_with($nwords, || { let v = r / $xinv; r = r % $xinv * BASE; v });

        let (mut sum, mut firstnonzero, mut denom) = (term.to_vec(), 0, 1);

        // We divide a large number of values by the same divisor; on most machines,
        // division is much slower than multiplication; libdivide allows us to
        // compute a multiplicative inverse which can be used to achieve the bulk
        // divisions using bulk multiplications instead - a big performance win!
        let mut next_denom = || {
            denom += 2; //captured by closure
            let inv = libdivide::Divider::new(denom).expect("libdivide initialization error");
            (denom, inv, 0, 0)
        };

        'outer: loop {
            let (denom0, denom0inv, mut remainder0, mut remainder1) = next_denom();
            let (denom2, denom2inv, mut remainder2, mut remainder3) = next_denom();
            for (term,sum) in term[firstnonzero..].iter_mut()
                          .zip(sum[firstnonzero..].iter_mut()) {
                atan_grind!(remainder0, remainder1, term, sum,
                            $xinv*$xinv, denom0, &denom0inv, SumOp::Decrement);
                atan_grind!(remainder2, remainder3, term, sum,
                            $xinv*$xinv, denom2, &denom2inv, SumOp::Increment);
            }

            while term[firstnonzero] == 0 {
                firstnonzero += 1;
                if firstnonzero >= $nwords { break 'outer sum }
            }
        }
    }}
}

//-----------------------------------------------------------------
fn max_digits() -> usize {
    // See the file Theory.pdf for the derivation of the relation used here.
    // The specific expression used here that the worst-case x being
    // computed for atan(x) is x=1/5; with the current code the worst case
    // is in fact x=1/10, but for now at least I'll stick with the more
    // pessimistic x=1/5.
    // Note that 339/485 is a truncated approximation of log10(5).
    let d = (Xword::MAX / (BASE+1) + 1) * 339 / 485;
    (d - d % (WORDDIGITS as Xword)) as usize
}

fn get_scale(arg: Option<String>) -> Xword {
    if let Some(s) = arg {
        match s.as_str() {
            "tau"|"τ" => SCALE_TAU,
            "pi" |"π" => SCALE_PI,
            _ =>
                match s.parse::<Xword>() {
                    Err(e) => {
                        eprintln!("error parsing scale: {}\n", e);
                        std::process::exit(1);
                    },
                    Ok(scale) => scale,
                },
        }
    } else {
        DEFSCALE
    }
}

fn get_nwords(digit_opt: Option<usize>, digit_param: Option<usize>,
              linelen: usize, maxdigits: usize) -> usize {
    let mut digits;
    if let Some(n) = digit_param {
        digits = n;
    } else if let Some(n) = digit_opt {
        digits = n;
    } else {
        let digits_per_line = linelen / (WORDDIGITS+1);
        digits = digits_per_line * DEFLINES * WORDDIGITS;
        assert!(WORDDIGITS <= digits && digits <= maxdigits); //sanity check
        eprintln!("Using a default of {} digits.", digits);
    }
    if digits == 0 {
        eprintln!("Setting to minimum of {} digits.", WORDDIGITS);
        digits = WORDDIGITS;
    } else if maxdigits < digits {
        eprintln!("Clamping to maximum of {} digits.", maxdigits);
        digits = maxdigits;
    }

    //error[E0658]: needs nightly's 'int_roundings':
    //  digits.div_ceil(WORDDIGITS)
    let div_ceil = |n,d| { assert!(0 < n); 1 + (n-1)/d }; //roll our own :-(

    // convert requested number of digits to the number of Xwords we need to allocate
    let (integer_portion_words, error_terms_words) = (1, 1);
    let fraction_portion_words = div_ceil(digits, WORDDIGITS);
    let actual_digits = fraction_portion_words * WORDDIGITS;
    if digits != actual_digits { eprintln!("Rounding {} up to {}", digits, actual_digits) }
    integer_portion_words + fraction_portion_words + error_terms_words
}

fn parse_cmdline() -> (usize, usize, Xword) {
    let (args, rest) = rustop::opts! {
        synopsis "Compute τ (tau) to specified number of digits";
        opt digits:Option<usize>, desc:"the number of digits to compute";
        opt linelen:usize=LINELEN, desc:"the (maximum) length of an output line";
        opt scale:Option<String>,
              desc:"compute scale*atan(1); can use 'tau', 'pi', or an integer";
        param ndigits:Option<usize>, desc:"the number of digits to compute (overrides -d)";
    }.parse_or_exit();

    let maxdigits = max_digits();
    if ! rest.is_empty() {
        eprintln!(
            "\nUsage: tau [options] [NumberOfDigits]\n\n\
             NumberOfDigits must be in the range {} to {}.\n\
             Use \"--help\" for more options.",
            WORDDIGITS, maxdigits);
        std::process::exit(1);
    }
    let nwords = get_nwords(args.digits, args.ndigits, args.linelen, maxdigits);
    ( nwords, args.linelen, get_scale(args.scale) )
}

fn printout(a: &[Xword], scale: Xword, linelen: usize) {
    let (int_part, a) = a.split_first().unwrap_or((&0, &[]));
    let (_err_part, a) = a.split_last().unwrap_or((&0, &[]));
    match scale {
        8 => print!("τ"),
        4 => print!("π"),
        1 => print!("atan(1)"),
        _ => print!("{}*atan(1)", scale),
    }
    println!(" = {}.", int_part);
    for line in a.chunks(linelen / (WORDDIGITS+1)) {
        for v in line.iter() { print!(" {value:0>width$}", width=WORDDIGITS, value=v) }
        println!();
    }
}

fn main() {
    let (nwords, linelen, scale) = parse_cmdline();
    let cputime = cpu_time::ProcessTime::now();

    // atan(1) = 8*atan(1/10) - atan(1/239) - 4*atan(1/515)
    let mut s = atan_loop!(nwords, scale*8,  10);
    let  s239 = atan_loop!(nwords, scale*1, 239);
    let  s515 = atan_loop!(nwords, scale*4, 515);

    // combine sums (into s) while fixing-up any out-of-spec digits
    let mut carry = 0;
    for (d, (a, b)) in
        s.iter_mut().rev()
        .zip(s239.iter().rev()
        .zip(s515.iter().rev()))
    {
        let mut v = carry + *d - a - b;
        carry = 0;
        // digits are typically close-enough to in-spec that doing
        // a division will be more expensive than this loop pair
        while v < 0     { v+=BASE; carry-=1 }
        while BASE <= v { v-=BASE; carry+=1 }
        *d = v;
    }
    assert!(carry == 0);

    let elapsed = cputime.elapsed();
    printout(&s, scale, linelen);
    eprintln!("Computation time = {:.2?}", elapsed);
}
