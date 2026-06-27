#set page("us-letter", numbering: "1")
#set heading(numbering: "1.")
#show heading: set block(below: 2em)
#show heading.where(level: 1): set text(size: 24pt)
#show heading.where(level:1): it => {
  counter(math.equation).update(0)
  it
}
#set math.equation(numbering: it => {
    let count = counter(heading.where(level: 1)).get().first()
    numbering("(1.1)", count, it)
})
#set align(left)
#set par(justify: true)

#let vextra = v(2em)
#let vbreak = v(4em)
#let atan = math.op("atan")
#let err = math.op("err")
#let Imax = $I_"max"$
#let nonum(eq) = math.equation(block: true, numbering: none, eq)
#let QED = $quad square.filled$
#let sfrac(n,d) = text(.9em, math.frac(n,d, style: "skewed"))
#let tfrac(n,d) = math.inline(math.frac(n,d))


= Identities equivalent to $atan(1)$
A demonstration that
  $ 8 atan tfrac(1,10) -  atan tfrac(1,239) - 4 atan tfrac(1,515) =  atan 1 $ <eq:atan1>

#vextra
First, recall the sum-of-angles identity for the tangent function:
  #nonum($ tan(x+y) = (tan x + tan y) / (1 - (tan x)(tan y)) $)
Furthermore, by the nature of inverse functions,
  #nonum($ x = atan(tan x) = tan(atan x) $)
Therefore:
  $ atan x + atan y
       &= atan( tan( atan x + atan y ) ) \
       &= atan  (tan(atan x) + tan(atan y)) / (1 - tan(atan x) tan(atan y)) \
       &= atan (x + y) / (1 - x y)
       $ <eq:atan_sum>
And, as a special case,
  $ 2 atan x
       &= atan x + atan x \
       &= atan (2x) / (1-x^2)
       $ <eq:atan_double>

#vbreak
Thus:
  #nonum($
    & 8 atan tfrac(1, 10)  \
    & quad= 4 atan (2(sfrac(1, 10))) / (1 - (sfrac(1, 10))^2)
      quad= 4 atan tfrac(20, 99) \
    & quad= 2 atan (2(sfrac(20, 99))) / (1 - (sfrac(20, 99))^2)
      quad= 2 atan tfrac(3960, 9401) \
    & quad= atan (2(sfrac(3960, 9401))) / (1 - (sfrac(3960, 9401))^2)
      quad=   atan tfrac(74455920, 72697201)
  $)
And
  #nonum($
    & 4 atan tfrac(1, 515) \
    & quad= 2 atan (2(sfrac(1, 515))) / (1 - (sfrac(1, 515))^2)
      quad= 2 atan tfrac(515, 132612) \
    & quad= atan (2(sfrac(515, 132612))) / (1 - (sfrac(515, 132612))^2)
      quad= atan tfrac(136590360, 17585677319)
  $)
So
  #nonum($
    & 8 atan tfrac(1, 10) - atan tfrac(1, 239) - 4 atan tfrac(1, 515) \
    & quad= atan tfrac(74455920, 72697201) - (atan tfrac(1, 239) + atan tfrac(136590360, 17585677319)) \
    & quad= atan tfrac(74455920, 72697201) + atan tfrac(-1758719, 147153121) \
    & quad= atan 1
      QED
  $)

#vbreak
Another identity that could be used is:
  $ atan 1 = 4 atan tfrac(1, 5) - atan tfrac(1, 239) $ <eq:atan_5_239>
This has the advantage of only requiring two passes,
but has the disadvantage that
the series for $sfrac(1, 5)$ converges more slowly
than those for $sfrac(1, 10)$ and $sfrac(1, 515)$ combined.
The proof of correctness may be obtained in a manner very similar
to the one shown above,
and will not be spelled out here.

[Note that these Taylor-series based computations are not
state-of-the-art for computing absurd quantities of digits of $τ$ or $π$;
the trillion-plus digit record holders use a hypergeometric series
developed by the brothers David and Gregory Chudnovsky,
which cranks out about 15 digits per term computed for the series.
Another approach involves refinements of the Gauss-Legendre algorithm,
such as one by Richard Brent and Eugene Salamin (1976),
which _doubles_ the number of accurate digits with each iteration.
But these approaches are not as easy to understand or implement as
Taylor-series based approaches like the one used in this program.]


#pagebreak()
= Error Analysis
Let
  $ f(x, n) = (x^(2n+1)) / (2n+1) quad  [thin |x| <= 1 thin ] $ <eq:function_f>
Then the Taylor-Maclaurin series for $atan x$ (over $|x| <= 1$)
can be written as:
  #nonum($ atan x = sum_(i=0)^infinity thin (-1)^i thin f(x, i) $)

Recall that if $a_i$ is a monotonically non-increasing sequence
with $lim_(i -> infinity) a_i = 0$,
then the sum $sum_(i=0)^(infinity) (-1)^i thin a_i$ converges;
furthermore, truncating this sum after term $n$
will result in an error whose magnitude is at most $a_(n+1)$.
// ((** double-check that all criteria are named and met **)
Thus for $atan x$, provided that $0 <= x <= 1$,
the error incurred by truncating the series after the $n$-th term is:
  $ err(n)
     <= f(x,n+1) = (x^(2 n+3)) / (2 n+3)
     <   (x^(2 n+1)) / (2 n+1)
     =   f(x,n)
     $ <eq:partial_f_an>

We will restrict ourselves to consideration of positive $x$
(i.e., $0 < x <= 1$, or $1 <= sfrac(1, x)$)
and assume that #box($a=sfrac(1, x)$) is the worst-case choice
for the relations being considered.
Substituting into @eq:partial_f_an gives
  $ err(n) < f(sfrac(1, a), n) $ <eq:constraint1>

#vbreak
We want our error term $err(n)$ to be less than $B^(-D)$,
for some specified base $B$ and
to-be-determined base-$B$-digit-count $D$:
  $ err(n) < B^(-D) $ <eq:target>

Furthermore, we want to fit intermediate results
into an integer which cannot exceed some maximum #Imax.
Each word of our multi-precision vector is
modulo-reduced by $2 n+1$ on outer-loop iteration $n$.
Each step computes
  #nonum($ r_i B + t_i <= #Imax $)
at word-index $i$,
for carry-down residue $r_i$ and previous-term $t_i$,
each of which is in the range
  #box($0 <= star <= (2 n+1) - 1 = 2 n $)
thus the worst-case intermediate result is
  #box($2 thin n B + 2 thin n <= #Imax$).
Solving for n yields:
  $ n <= (#Imax) / (2 thin (B+1)) $ <eq:n-terms>

#vbreak
Our goal is to find the largest $D$ that simultaneously satisfies
relations @eq:constraint1, @eq:target, and @eq:n-terms.
It is acceptable to find a value $D'$
that is less than the actual maximum,
if an approximation makes life easier,
but we must never allow the resultant $D'$ to be bigger than $D$
and we prefer not to underestimate $D$ by _too_ much.

#vextra
Now @eq:constraint1 and @eq:target
do not have a natural ordering,
but given our goal of wanting to derive a "safe" value of $D$,
we choose to combine them with this ordering:
  $ err(n) < f(sfrac(1, a), n) < B^(-D) $ <eq:target-inequality>
For brevity in the sequel, let
  $ R = (#Imax) / (B+1) $ <eq:R-def>
Combining substitutions of @eq:n-terms and @eq:R-def
into equation~@eq:target-inequality gives:
  #nonum($ f(sfrac(1, a), sfrac(R, 2)) < B^(-D) $)
Solving for $D$ yields:
  #nonum($ D < (-log f(sfrac(1, a), sfrac(R, 2))) / (log B) $)
Using $(sfrac(1, a))^x = a^(-x)$,
$sfrac(log x, log B) = log_B x$,
and the definition of $f$ given in equation~@eq:function_f:
  $ D
    < (-log (a^(-(2(sfrac(R, 2))+1))) / (2(sfrac(R, 2))+1)) / (log B)
    = (R+1) log_B a + log_B (R+1)
    $
Converting the digit count to base-10 digits
involves multiplying by $log_(10) B$.
Because
  #nonum($
    (log_B x)(log_(10) B)
    = (log_(10) x) / (log_(10) B) log_(10) B
    = log_(10) x
    $)
we can determine that the constraint on the number of decimal digits $d$ as
  $ d = D log_(10) B < (R+1) log_(10) a + log_(10)(R+1) $ <eq:d-constraint>

#vbreak
To take a concrete example,
let us assume that our worst-case is $a=5$
(as when evaluating the relation in equation~@eq:atan_5_239),
that $B=10^(12)$,
and that $#Imax=2^(63)-1$;
then $R = tfrac(2^(63)-1, 10^(12)+1)$
and we get
  #nonum($
    d
    < (tfrac(2^(63)-1, 10^(12)+1) + 1) log_(10) 5 + log_(10) (tfrac(2^(63)-1, 10^(12)+1) + 1)
    approx 6 thin 446 thin 868
    $)
So for these parameters we want to ensure that no more than
$6 thin 446 thin 868$ decimal digits are allowed to be computed and printed,
in order to avoid the risk of errors from integer overflow
(whether they are silent as in C or panicking as in Rust).

#vbreak
Some further adjustments:
 - To re-iterate, we don't need to be precise in our upper bound;
    lowering by a few digits is acceptable.
 - Hence it is okay to drop the $log_(10)(R+1)$ term
    in equation~@eq:d-constraint;
    even in the situation with
    $#Imax = 2^(64)$ and $B=10$,
    which will give a fairly large $R=tfrac(#Imax, B+1)$,
    we would lose fewer than 20 digits
    in our estimation of $d$.
 - We are assuming that our worst case happens with $a=5$;
    $log_(10)(5) > sfrac(339, 485)$
    with an error in the ballpark of one part per million.
 - To minimize user confusion, we want to round the "maximum"
    down to the nearest multiple of $log_(10) B$,
    since we will always be outputting
    an integer number of base-$B$ "digits".
All of this can be accomplished with integer-only calculations
by using the following Rust function.
Here
```rust Xword``` is the signed-integer type used for calculations,
```rust Xword::MAX``` represents $#Imax$,
```rust WORDDIGITS``` = $log_(10) B$;
we require that ```rust WORDDIGITS``` be an integer,
and so ```rust BASE``` in the code below
is another name for what we called $B$ in the above derivation:
```rust
     const BASE: Xword = (10 as Xword).pow(WORDDIGITS as u32);
     fn max_digits() -> Xword {
       let d = (Xword::MAX / (BASE+1) + 1) * 339 / 485;
       d - d % (WORDDIGITS as Xword)
     }
```

#vextra
Note that if we use $a=10$
(such as when using equation~@eq:atan1)
instead of $a=5$
(as with equation~@eq:atan_5_239),
then instead of using $log_(10) 5 approx sfrac(339, 485)$
we would use $log_(10) 10 = 1$,
which both simplifies the equation and allows for the safe
computation of more digits.

If, instead, we chose to use the Taylor series
to directly compute $atan(1)$,
we would be multiplying by
$log_(10) 1 = 0$ --- thus we would
be limited to the fairly small
quantity of $log_(10)(R+1)$
digits accurately computed
before encountering integer overflow problems
in some intermediate calculation.
This is one of the reasons we seek and use a mathematically
equivalent calculation which is more numerically stable
(the other reason is that even if we had infinite-precision registers,
the rate of convergence for a raw $atan(1)$ is much too slow).
