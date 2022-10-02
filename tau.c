/* The origins of this code was the comp.lang.c posting to compute pi:
     From: jasonp@Glue.umd.edu (Jason Stratos Papadopoulos)
     Newsgroups: sci.math,comp.lang.c
     Subject: here's a program to calculate pi, in C, version 4.5
     Date: 16 Feb 1997 07:25:10 GMT
     Message-ID: <5e6com$j3e@hecate.umd.edu>

   The code has been extensively reformatted (as an aid for me to
   understand the code enough to customize it); the computation
   has been tweaked so that the last _output_ block is correct
   (by *computing* one extra block, which is not output); and the
   computation has been re-jiggered to compute tau instead of pi.
   Furthermore, an extensive comment has been added to explain a
   key piece of the theory behind the computation used.
   --xedakini 2022-09-28

   A reminder from the original posting: it is recommended to use
   -O3 optimization, to ensure sane divmod behavior.
*/

/* --- customizable section --- */

#define SCALE       8        /* we will compute SCALE*atan(1) */
#define LINELEN     80       /* keep output lines no longer than this length */
#define MINDIGITS   20       /* base-10 digits; somewhat arbitrary limit? */
#define MAXDIGITS   1200000  /* base-10 digits; somewhat arbitrary limit? */

#include <stdint.h>
/* these three related declarations need to be kept in sync: */
#define BASE        1000000000  /* we adjust computations to be in this base */
#define BASEDIGITS  9           /* == log10(BASE) */
typedef int_fast64_t word;      /* must be able to hold values up to BASE^2 */

/* --- there ought to be no moving parts left below this point --- */


/*---------------------------------------------------------------*/

/*
   Theory behind computation.

    Note that atan(1) == tau/8 == pi/4.

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
          = atan(1) = tau/8 = pi/4
          QED

    Why use this instead of just atan(1)?
    Because series for atan converge much faster for 1/5 and 1/259 than for 1.


   Taylor-Maclaurin series for atan(x) (when abs(x) <= 1):
       atan(x) = \sum_0^\infty (-1)^n x^{2n+1} / {2n+1}
               = x - x^3/3 + x^5/5 - ...

   Putting this all together, and running calculations using multi-precision
   arithmetic with "digit"s of base BASE is how this code accomplishes its task.
 */

/*---------------------------------------------------------------*/
#include <stdio.h>
#include <stdlib.h>

typedef size_t idx_t;
static size_t nwords;             /* number of elements in each array below: */
static word *sum, *term;          /* arrays of BASE "digit"s */
static idx_t firstword, lastword; /* working-area limits in above two arrays */

#define __NUMFMT(x)  #x
#define _NUMFMT(x)   __NUMFMT(x)
#define NUM2STR(x)   _NUMFMT(x)

/*---------------------------------------------------------------*/
static void
atan5(word denom)
{
    idx_t mark=firstword, i;
    word remainder1=0, remainder2=0, v;

    /*note that this routine is not rolled up like the atan239
      version below. It turns out that things go significantly
      faster here if you check for advancing firstword *before*
      starting on the next term in the series */

    /* subtract the next term of series */
    for (i=firstword; i<=lastword+1; ++i) {
	v = remainder1*BASE + term[i];
	term[i] = v / (5*5);
	remainder1 = v % (5*5);

	v = remainder2*BASE + term[i];
	sum[i] -= v / denom;
	remainder2 = v % denom;
    }
    if (term[i-1]>0 && lastword<nwords)
	++lastword;
    for (; i<=nwords; ++i) {
	v = remainder2*BASE;
	sum[i] -= v / denom;
	remainder2 = v % denom;
    }
    if (term[firstword] == 0)
	++firstword;

    /* adjust out-of-spec digits */
    for (i=nwords; mark<i; --i)
	if (sum[i]<0) { sum[i]+=BASE; --sum[i-1]; }

    /* add the next term of series */
    denom += 2;
    remainder1 = remainder2 = 0;
    for (i=firstword; i<=lastword+1; ++i) {
	v = remainder1*BASE + term[i];
	term[i] = v / (5*5);
	remainder1 = v % (5*5);

	v = remainder2*BASE + term[i];
	sum[i] += v / denom;
	remainder2 = v % denom;
    }
    if (term[i-1]>0 && lastword<nwords)
	++lastword;
    for (; i<=nwords; ++i) {
	v = remainder2*BASE;
	sum[i] += v / denom;
	remainder2 = v % denom;
    }
    if (term[firstword] == 0)
	++firstword;

    /* adjust out-of-spec digits */
    for (i=nwords; mark<i; --i)
	if (sum[i]>=BASE) { sum[i]-=BASE; ++sum[i-1]; }
}

/*---------------------------------------------------------------*/
static void
atan239(word denom)
{
    idx_t mark=firstword;
    word denom2=denom+2,
	  remainder1=term[firstword++],   /*perform 1st divide implicitly*/
	  remainder2=0, remainder3=0, remainder4=0;

    for (idx_t i=firstword; i<=nwords; ++i) {
	/*add next term*/
	word v = remainder1*BASE + term[i];
	term[i] = v / (239*239);
	remainder1 = v % (239*239);

	v = remainder2*BASE + term[i];
	sum[i] += v / denom;
	remainder2 = v % denom;

	/*subtract next term*/
	v = remainder3*BASE + term[i];
	term[i] = v / (239*239);
	remainder3 = v % (239*239);

	v = remainder4*BASE + term[i];
	sum[i] -= v / denom2;
	remainder4 = v % denom2;
    }

    /* adjust out-of-spec digits */
    for (idx_t i=nwords; 1<i; --i) {
	while (sum[i]<0) { sum[i]+=BASE; --sum[i-1]; }
	while (sum[i]>=BASE) { sum[i]-=BASE; ++sum[i-1]; }
    }
    if (term[firstword] == 0)
	++firstword;
}

/*---------------------------------------------------------------*/
static void
allocate(const char *arg)
{
    long digits = 0;

    if (arg) {
	digits = strtol(arg, NULL, 10);
    } else {
	puts("\nusage: tau NumberOfDigits\n\n"
	     "digits must be in the range "
	     NUM2STR(MINDIGITS) " to " NUM2STR(MAXDIGITS) "\n"
	     "To save to an output file, use\n\n"
	     "tau NumberOfDigits > OutputFile\n"
	     );
    }
    if (digits<MINDIGITS || MAXDIGITS<digits) {
	puts("Setting default to " NUM2STR(MINDIGITS) " digits.");
	digits = MINDIGITS;
    }

    /* Allocate array space and initialize */
    nwords = (digits-1)/BASEDIGITS + 3;
    sum = calloc(nwords+2, sizeof *sum);
    term = calloc(nwords+2, sizeof *term);
}

/*---------------------------------------------------------------*/
static void
printout(void)
{
    /* This else-if chain ought to compile-time optimize to exactly one
     * unconditional output statement...
     */
    if (SCALE == 8)
	puts("tau = 6.");
    else if (SCALE == 4)
	puts("pi = 3.");
    else
	printf("%d*atan(1) = %d.\n", SCALE, sum[0]);

    const idx_t words_per_line = (LINELEN) / ((BASEDIGITS)+1);
    for (idx_t i=1; i<nwords-1; ++i) {
	printf(" %." NUM2STR(BASEDIGITS) "d", sum[i]);
	if (i%words_per_line == 0) puts("");
    }
}

/*-----------------------------------------------------------------*/
#include <time.h>  /* for clock(3) */

int
main(int argc, char *argv[])
{
    allocate(argc == 2 ? argv[1] : NULL);
    if (!sum || !term) {
	puts("Memory allocation failed. Try fewer digits.");
	return 1;
    }

    clock_t start = clock();

    /* ----- SCALE*4*atan(1/5) -------*/
    sum[0] = term[0] = SCALE*4 / 5;
    sum[1] = term[1] = (SCALE*4%5)*BASE / 5;
    firstword=0; lastword=1;
    for (word denom=3; firstword<nwords; denom+=4)
	atan5(denom);

    /* ----- SCALE*atan(-1/239) ------- */
    /* crunch out first term manually */
    word remainder = SCALE;
    term[0]=0; firstword=1;
    for (idx_t i=1; i<=nwords; ++i) {
	word v = remainder*BASE;
	sum[i] -= term[i] = v / 239;
	remainder = v % 239;
    }
    for (idx_t i=nwords; 1<i; --i)
	if (sum[i]<0) { sum[i]+=BASE; --sum[i-1]; }
    for (word denom=3; firstword<nwords; denom+=4)
	atan239(denom);

    /* -----Finish up */
    clock_t end = clock();
    printout();
    printf("\nComputation time = %6.2f seconds\n",
	    (double)(end-start)/CLOCKS_PER_SEC);
#ifdef FORCE_CLEANUP
    free(sum); free(term);
#endif
    return 0;
}
