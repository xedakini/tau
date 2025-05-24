//! # tau
//!
//! `tau` is a program to compute the digits of the circle constant τ.
//! It can also be used to compute the digits of π, or any other integer
//! multiple of atan(1).
//!
//! Credit where due: the inspiration for this code
//! was a posting to comp.lang.c for computing pi:
//!    <pre><code>From: jasonp@Glue.umd.edu (Jason Stratos Papadopoulos)
//!    Newsgroups: sci.math,comp.lang.c
//!    Subject: here's a program to calculate pi, in C, version 4.5
//!    Date: 16 Feb 1997 07:25:10 GMT
//!    Message-ID: <5e6com$j3e@hecate.umd.edu>
//!    </code></pre>
//!
//! The core idea of computing _N_&times;atan(1) [for a mathematically
//! equivalent but computationally better behaved expression] remains,
//! and the basic approach to multi-precision calculation is the same.
//! Otherwise, apart from some random vestiges (such as error messages
//! from argument parsing), this is a complete rewrite in Rust.
//! Also note that the default has been changed here to compute 8&times;atan(1)
//! (aka "tau") instead of 4&times;atan(1) (aka "pi").

use anyhow::{anyhow, Result}; // override std::Result with anyhow::Result
use libdivide::Divider; // to reduce the amortized cost of repeated quasi-constant divisions

// Name a couple of constants that might be helpful in the "customizable" section below.

/// `SCALE_TAU` is used to compute τ = 8 &times; atan(1) = tau = 2π.
#[allow(dead_code)]
const SCALE_TAU: Xword = 8;

/// `SCALE_PI` is used to compute π = 4 &times; atan(1) = pi = τ/2.
#[allow(dead_code)]
const SCALE_PI:  Xword = 4;

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

/// The basic type used for calculations.
type Xword = i64;
/// The number of decimal digits in each computation unit.
const WORDDIGITS: u8 = 12;

// define some default values:

/// Keep output lines no longer than this length (default value).
const DEFLINELEN: usize = 80;
/// The number of lines to output if the user does not select a digit count.
const DEFLINES:   usize = 2;
/// The default scaling of atan(1) to use.
const DEFSCALE:   Xword = SCALE_TAU; //SCALE_PI is another popular choice.

// --- there ought to be no moving parts left below this point ---

/// The number of decimal digits in each computation unit; usize'd variant.
const WORDDIGITS_USIZE: usize = WORDDIGITS as usize;

// derive "BASE" from WORDDIGITS
/// Computations are adjusted to be done relative to this base.
const BASE: Xword = (10 as Xword).pow(WORDDIGITS as u32);

const _:() = assert!((-1 as Xword) < 0 && 0 < Xword::BITS); //Xword must be a signed integer type
const _:() = assert!(1 <= WORDDIGITS && (WORDDIGITS_USIZE) < DEFLINELEN); //sanity constraints
const _:() = assert!(((Xword::MAX / (BASE+1)) as u64) < (usize::MAX as u64)); //XXX

//-----------------------------------------------------------------
/*
   Background:

   This program computes scale×atan(1).  Since τ/8 = π/4 = atan(1),
   we can readily compute τ or π by choosing `scale` to be either
   8 or 4 (respectively).

  The Taylor-Maclaurin series for atan(x) (when abs(x) <= 1) is:
      atan(x) = \sum_{k=0}^\infty (-1)^k x^{2k+1} / {2k+1}
              = x - x^3/3 + x^5/5 - ...

   The Taylor-Maclaurin series for atan(1) itself converges rather
   slowly, but by using the identity
     atan(1) = 8 atan(1/10) - atan(1/239) - 4 atan(1/515)
   we get three readily combinable terms which each converge either
   quickly or very-quickly.

   See the file "Theory.pdf" for further details.
*/

/*
   The routines in this section are performance-critical, to the point
   that we write both of them as macros — normal in-lining isn't aggressive
   enough.  We need the compiler to see that certain "variables" are in fact
   compile-time constants, and optimize accordingly.  (Multiplications are
   cheaper than divisions on (almost?) all platforms, and the compiler
   knows this and, at least with "release build" levels of optimization,
   will apply the appropriate transformations needed to replace the division
   with multiply-by-inverse logic when it notices division by a compile-time
   constant.)

   Furthermore, in the case where we do not have a compile-time constant,
   but we are dividing a (potentially long) vector of integers by the same
   value (as we do for each "divide by 2*k+1" step in computing the Taylor
   series with our extended-precision math), the libdivide crate allows us
   to (in effect) compute a multiplicative inverse which can be used to
   achieve the bulk divisions using bulk multiplications instead — a big
   performance win!
*/

// We write this as a macro so that the compiler will notice when $alt_divisor
// happens to be a compile-time constant.  Additionally, this being a macro
// gives the compiler an opportunity to micro-optimize the four-in-a-row
// invocation that occurs in the main atan! loop.
/// Compute the next step of the multi-precision calculation.
macro_rules! divmod_step {
    ($register:ident, $value:expr, $divisor:expr, $alt_divisor:expr) => {{
        debug_assert!($divisor / $alt_divisor == 1);
        $register += $value;
        // The following division should compile as a multiply-by-inverse
        // (at least in release builds) if $alt_divisor is an integer
        // constant.  If $alt_divisor is of type &libdivide::Divisor then
        // functionally the same thing happens (a MULT instead of a DIV
        // machine instruction becomes the key operation), though with the
        // overhead of a function call.
        let q = $register / $alt_divisor;
        $register -= q * $divisor; //aka: $register %= $divisor, but using multiplication
        $register *= BASE; //in anticipation of the next iteration
        q
    }};
    ($register:ident, $value:expr, $divisor:expr) => {
        divmod_step!($register, $value, $divisor, $divisor)
    };
}

// This is only a macro to ensure that $xinv remains seen as a compile-time constant.
/// Compute `scale` &times; atan(1/`xinv`) to `nwords` base-`BASE` "digits" of precision.
macro_rules! atan {
    ($nwords:expr, $scale:expr, $xinv:expr) => {{
        let mut term = Vec::new();
        { let mut r = $scale; term.resize_with($nwords, ||{divmod_step!(r, 0, $xinv)}) }

        let (mut sum, mut firstnonzero, mut denom) = (term.clone(), 0, 1);

        let mut next_denom = || {
            denom += 2;
            let altdenom = Divider::new(denom).expect("libdivide initialization error");
            (0, 0, denom, altdenom)
        };

        'outer: loop {
            // Recall that in the Taylor-Maclaurin series for atan(x), the k-th
            // (zero-based) term is (-1)^k * x^(2k+1) / (2k+1).  We handled the
            // k==0 case when initializing `term` and `sum` above.  When k is
            // even, (-1)^k==1, so we should add the term to our running sum;
            // when k is odd, (-1)^k==-1, so we should subtract the term instead.
            //
            // Here we compute and apply two terms of the Taylor series for each
            // pass through our multi-precision value.  The main reason is to
            // keep the alternating-sum logic simple, but we also get a minor
            // loop-unrolling performance benefit.  In principle we could get
            // the alternating-sum effect by always adding, and multiply the k-th
            // term by (-1)^k; but even optimizing the exponentiation to a single
            // negation operation per iteration, actually doing a multiplication
            // (of the variable which would track the 1 or -1 value) per
            // iteration would hurt performance within the innermost loop.

            let (mut t1, mut s1, d1, d1a) = next_denom(); //k odd, so subtract this term from sum
            let (mut t2, mut s2, d2, d2a) = next_denom(); //k even, so add this term to sum
            for (term,sum) in term[firstnonzero..].iter_mut()
                          .zip(sum[firstnonzero..].iter_mut()) {
                *term = divmod_step!(t1, *term, $xinv*$xinv);
                *sum -= divmod_step!(s1, *term, d1, &d1a);

                *term = divmod_step!(t2, *term, $xinv*$xinv);
                *sum += divmod_step!(s2, *term, d2, &d2a);
            }

            while term[firstnonzero] == 0 {
                firstnonzero += 1;
                if firstnonzero >= $nwords { break 'outer sum }
            }
        }
    }};
}

//-----------------------------------------------------------------

/// Determine the scaling of atan(1) to use, per command-line request.
fn get_scale(arg: Option<String>) -> Result<Xword> {
    arg.map_or(Ok(DEFSCALE), |s| match s.as_str() {
        "tau" | "τ" => Ok(SCALE_TAU),
        "pi"  | "π" => Ok(SCALE_PI),
        _ => match s.parse::<Xword>() {
            Err(e) => Err(anyhow!("--scale could not be parsed: {e}")),
            Ok(scale) => {
                if scale < 0 {
                    Err(anyhow!("--scale argument may not be negative"))
                } else {
                    Ok(scale)
                }
            },
        }
    })
}

/// Handle the determination of the number of decimal digits to compute and print.
fn get_nwords(digit_opt: Option<usize>, digit_param: Option<usize>,
              linelen: usize, maxdigits: usize) -> Result<usize> {
    let digits =
        if let Some(n) = digit_param {
            n
        } else if let Some(n) = digit_opt {
            n
        } else {
            if linelen == 0 { return Err(anyhow!("--digits must be specified when --linelen=0")) }
            let words_per_line = linelen / (WORDDIGITS_USIZE+1);
            let n = words_per_line * DEFLINES * WORDDIGITS_USIZE;
            assert!(WORDDIGITS_USIZE <= n && n <= maxdigits); //sanity check
            eprintln!("Using a default of {n} digits.");
            n
        };
    let digits =
        if digits == 0 {
            eprintln!("Setting to minimum of {WORDDIGITS} digits.");
            WORDDIGITS.into()
        } else if maxdigits < digits {
            eprintln!("Clamping to maximum of {maxdigits} digits.");
            maxdigits
        } else {
            digits
        };

    // convert requested number of digits to the number of Xwords we need to allocate
    let (integer_portion_words, error_terms_words) = (1, 1);
    let fraction_portion_words = digits.div_ceil(WORDDIGITS_USIZE);
    let actual_digits = fraction_portion_words * WORDDIGITS_USIZE;
    if digits != actual_digits { eprintln!("Rounding {digits} up to {actual_digits}") }
    Ok(integer_portion_words + fraction_portion_words + error_terms_words)
}

/// Determine the run-time options requested by the end-user.
fn parse_cmdline() -> Result<(usize, usize, Xword)> {
    let (args, rest) = rustop::opts! {
        synopsis "Compute τ (tau) to specified number of digits";
        opt digits:Option<usize>, desc:"the number of digits to compute";
        opt linelen:usize=DEFLINELEN, desc:"the (maximum) length of an output line";
        opt scale:Option<String>,
              desc:"compute `scale`×atan(1) for positive integer values of `scale`; \
                    can also specify 'pi' or 'tau' to compute those constants (default is 'tau')";
        param ndigits:Option<usize>, desc:"the number of digits to compute (overrides -d)";
    }.parse_or_exit();

    // See the file Theory.pdf for the derivation of the relation used here.
    // The specific expression used here takes x=1/5 as the worst-case x
    // being used in an atan(x) computation; with the current code the worst
    // case is in fact x=1/10, but for now at least I'll stick with the more
    // pessimistic x=1/5.
    // Note that 339/485 is a slightly-smaller-than approximation of log10(5).
    let maxdigits = (Xword::MAX.cast_unsigned() / (BASE.cast_unsigned()+1) + 1) * 339 / 485;
    let maxdigits = maxdigits - maxdigits % Xword::from(WORDDIGITS).cast_unsigned();

    if ! rest.is_empty() {
        return Err(anyhow!(
            "\nUsage: tau [options] [NumberOfDigits]\n\n\
             NumberOfDigits must be in the range {WORDDIGITS} to {maxdigits}.\n\
             Use \"--help\" for more options."));
    }
    if args.linelen<=WORDDIGITS_USIZE && args.linelen!=0 {
        return Err(anyhow!("--linelen must be at least {}", WORDDIGITS+1));
    }
    let nwords = get_nwords(args.digits, args.ndigits, args.linelen, usize::try_from(maxdigits)?)?;
    Ok((nwords, args.linelen, get_scale(args.scale)?))
}

/// Output the value of the number packaged in the passed slice of `Xword`-s.
fn printout(a: &[Xword], scale: Xword, linelen: usize) {
    let (int_part, a) = a.split_first().unwrap_or((&0, &[]));
    let (_err_part, a) = a.split_last().unwrap_or((&0, &[]));
    match scale {
        8 => print!("τ"),
        4 => print!("π"),
        1 => print!("atan(1)"),
        _ => print!("{scale} × atan(1)")
    }
    print!(" = {int_part}.");
    let linelen = if linelen == 0 { usize::MAX } else { println!(); linelen };
    for line in a.chunks(linelen / (WORDDIGITS_USIZE+1)) {
        for v in line { print!(" {v:0>WORDDIGITS_USIZE$}") }
        println!();
    }
}

#[expect(clippy::cognitive_complexity, reason="misleading complexity due to macro invocations")]
fn main() -> Result<()> {
    let (nwords, linelen, scale) = parse_cmdline()?;
    let cputime = cpu_time::ProcessTime::now();

    // atan(1) = 8 atan(1/10) - atan(1/239) - 4 atan(1/515)
    let mut s = atan!(nwords, scale*8,  10);
    #[allow(clippy::identity_op)]
    let  s239 = atan!(nwords, scale*1, 239);
    let  s515 = atan!(nwords, scale*4, 515);

    // combine sums into s, while fixing-up any out-of-spec digits
    let mut carry = 0;
    for (d, (a, b)) in
        s.iter_mut().rev()
        .zip(s239.iter().rev()
        .zip(s515.iter().rev()))
    {
        let mut v = carry + *d - a - b;
        carry = 0;
        // value will be close-enough to in-spec that doing
        // a division will be more expensive than this loop pair
        while v < 0     { v+=BASE; carry-=1 }
        while BASE <= v { v-=BASE; carry+=1 }
        *d = v;
    }
    assert!(carry == 0);

    let elapsed = cputime.elapsed();
    printout(&s, scale, linelen);
    #[expect(clippy::use_debug, reason = "it's simple, and essentially debug anyway")]
    { eprintln!("Computation time = {elapsed:.2?}") }
    Ok(())
}
