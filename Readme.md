
Q: What is this?\
A: A program to compute τ.

Q: Say what now?\
A: τ = 2π  (tau = 2 pi)

Q: Okay... why?\
A: τ is the ratio of the circumference of a circle to its
   radius; π is the ratio of circumference to diameter.
   The radius of a circle is more fundamental, mathematically
   speaking.

Q: Eh...\
A: Google "tau vs. pi debate".

Q: Alright then.  τ.  Fine, whatever.  Why again?\
A: Why is it interesting to compute τ or π or atan(1)
   to ridiculous precision?  Well... it's not really _that_
   interesting.  It's just a simple self-contained problem
   that was interesting to work on as a puzzle.  I release
   my version in case anyone *does* find it interesting,
   or wants to experiment with further refinements.

Q: Well, okay.  But I'd really rather stick with the well-known
   constant π instead of this τ thing.\
A: Fine: run with the "-s π" command-line option.

Q: Uh, that's awkward to type on my keyboard?\
A: Okay, then spell it "-s pi" instead.  Or modify the
   DEFSCALE declaration in the code to change the default.

Q: So, tell me about how the code works?\
A: That ought to be covered by comments within the code itself.
   I strove to make the code itself readable and reasonably
   self-documenting.  I also created the Theory.pdf file to explain
   some of the less obvious points about the mathematics being used.

   Rust is still a new language to me, so the code might not be
   fully idiomatic, but it should still be straightforward to read.

Q: Meh.  How about a short summary?\
A: τ = 8·atan(1).  However, the Taylor-Maclaurin series
   for atan(1) itself converges rather slowly, so we
   use the identity:\
      ````   atan(1) = 8·atan(1/10) - atan(1/239) - 4·atan(1/515)````\
   The equivalence is demonstrated in the Theory.pdf file.  Note that
   the closer to zero x is, the faster the T-M series for atan(x)
   converges.  Running this program on a mid-range modern processor
   it takes fewer than 3 milliseconds to compute τ to 5000 places,
   and a bit under 2.5 minutes to compute out to one million places.

Q: What is the history of this code?\
A: As mentioned in the opening comment within main.rs, this code
   traces a lineage to a comp.lang.c posting by Jason Papadopoulos
   for computing π, written (of course) in C.  He had several
   iterations of this code; I picked up version 4.5 and was not
   understanding how it worked, so I started reformatting and
   refactoring it.

   At some point I felt that the nature of C code was inhibiting my
   understanding, so I decided to translate to Rust.  I worked on
   polishing the code to my satisfaction, and realized that there
   might be a version newer than 4.5 out there; in fact I found
   that Papadopoulos has a version 4.8 and 5.0 of the C code also.
   The 4.5 code used the relation
      atan(1) = 4·atan(1/5) - atan(1/239)
   but the 5.0 code used the relation quoted in the previous
   answer; the convergence of atan(1/10) and atan(1/515) are
   enough faster than the convergence for atan(1/5) that it is
   worth computing the three terms instead of the two.
   Due to the nature of my refactoring work, it was fairly trivial
   to make the switch-over.

Q: You use macros for two functions.  Isn't that kind of grody?\
A: A point of the code is that it should be high-performance.
   Now, the overhead of using functions should normally be small,
   especially if the compiler is likely to inline the function
   (as would be the case here), but there is a small issue with
   the current state-of-the-art in the code optimization.

   In the multi-precision arithmetic used, we need to do integer
   division to each member of a potentially large vector.
   The hardware division operation is rather slow, but there is
   an optimization that the compiler can do where the division
   is replaced by a much less expensive multiplication (plus a few
   bit-ops), *provided that it recognizes the divisor as being a
   compile-time constant*.  When we pass a constant as an argument
   to a function, however, the compiler looses track of the fact
   that the argument was a constant, even if it later inlines the
   function.  So, in order to be performant, two critical functions
   were re-written as macros, so that the compiler will continue
   to notice that we are doing division by a compile-time constant
   and replace the divisions by multiplications.

Q: Wait, doing division by multiplying?\
A: In essence, to divide by x, the compiler computes the functional
   equivalent of 1/x, then multiplies by that.  This is a somewhat
   simplified version of what's going on, but should suffice for
   an intuitive understanding.  For more details, see
      https://libdivide.com/
      https://github.com/ridiculousfish/libdivide

Q: Wait, libdivide?  I noticed that in the .toml file?\
A: Right.  There is a Rust crate which a port of the C libdivide
   mentioned in the above two links.  This is used for a different
   division, which is not a compile-time constant, yet is also
   repeated across a vector of integers.  The compiler-generated
   code is slightly more efficient than explicitly using libdivide,
   but if one really wanted to rewrite the two macros as ordinary
   functions, one could make use of libdivide to avoid loosing
   *too* much in the way of performance.

Q: Are these questions really frequently asked?\
A: I never said they were.  This is a "Readme" written
   in Q&A format, not a FAQ.
