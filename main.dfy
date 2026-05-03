/*
  ############################################################
  ### SETUP & INSTALLATION
  ############################################################

  This lab runs in GitHub Codespaces — no local install needed.

  1. Open the repository link provided by your instructor.
  2. Click the green "Code" button, then "Codespaces", then "Create codespace".
  3. Wait for the environment to load (this may take a minute).
  4. Open this file in the editor.
  5. To verify, open a terminal (Ctrl+`) and run:

       dafny verify Lab1_Basics.dfy

  The Dafny extension will also show inline red squiggles for
  verification errors as you type, but may take a moment to start.
*/


/*
  ############################################################
  ### INTRODUCTION
  ############################################################

  Dafny is a programming language with built-in verification.

  In Dafny, you write code and specifications together.
  The code says what the program does.
  The specification says what must be true.

  Dafny checks that the code satisfies the specification
  for ALL inputs, not just the ones you test.

  A program can be correct with respect to its specification
  and still be wrong if the specification is too weak.
  Getting both right is your job.
*/


/*
  An `ensures` clause is a postcondition, a property that must
  hold when the method returns.
*/

method Double(x: int) returns (y: int)
  ensures y == 2 * x
{
  y := x + x;
}

/*
  Try breaking the implementation: change `x + x` to `x + 1`.
  Dafny should reject it with a verification error.
*/


/*
  EXERCISE 1: Absolute value

  Implement Abs so that both postconditions are satisfied.

  Hint: use an if/else on x.
*/

method Abs(x: int) returns (y: int)
  ensures y >= 0
  ensures y == x || y == -x
{
  y := 0; // TODO: replace with a correct implementation
}


/*
  A `requires` clause is a precondition, a constraint on inputs
  that the caller must satisfy. Dafny will reject any call site
  that cannot prove the precondition holds.

  Here, dividing by zero is undefined, so we require y != 0.
*/

method Divide(x: int, y: int) returns (r: int)
  requires y != 0
  ensures r == x / y
{
  r := x / y;
}


/*
  EXERCISE 2: Max

  Implement Max. The two postconditions together say that
  m is at least as large as both inputs, and equals one of them.

  This fully pins down what max means.
*/

method Max(x: int, y: int) returns (m: int)
  ensures m >= x && m >= y
  ensures m == x || m == y
{
  m := x; // TODO: replace with a correct implementation
}


/*

*/

/*
  This method verifies, but it is clearly wrong:
*/

method MaxWeak(x: int, y: int) returns (m: int)
  ensures m >= x && m >= y
{
  m := x + y + 1; // not a max, but Dafny accepts it!
}

/*
  Why does Dafny accept this?

  The specification is too weak. It only says m is an upper bound,
  not that m equals one of the inputs. Any sufficiently large value
  satisfies an upper-bound-only spec.

  EXERCISE 3: Strengthen the specification

  Add a second `ensures` clause to MaxWeakFixed so that the bogus
  implementation above is rejected, but a correct one is accepted.

  Change only the spec, not the body.
*/

method MaxWeakFixed(x: int, y: int) returns (m: int)
  ensures m >= x && m >= y
  ensures true // TODO: replace this with the missing ensures clause
{
  m := x + y + 1; // Dafny should reject this once your spec is strong enough
}


/*

  Specifications encode assumptions about the real world.
  Choosing what to specify is a design decision.
*/

/*
  EXERCISE 4: Specify the bank transfer

  Add `requires` and `ensures` clauses to TransferSpec below.

  Think through each of these:
    (a) Conservation: should total money be preserved?
        Hint: what should (a2 + b2) equal?

    (b) Validity: should either balance be allowed to go negative?
        Hint: add a requires relating `a` and `amount`.

    (c) Direction: should `amount` be required to be positive?
        What goes wrong if amount is negative or zero?

  Start with (a), which captures the most fundamental invariant.
*/

method TransferSpec(a: int, b: int, amount: int) returns (a2: int, b2: int)
  requires true // TODO: replace with real preconditions
  ensures true  // TODO: replace with real postconditions
{
  a2 := a - amount;
  b2 := b + amount;
}


/*
  Dafny proves array accesses are in-bounds at verification time,
  before the program runs. If it cannot prove safety, it refuses
  to compile.
*/

method GetAt(arr: array<int>, i: int) returns (x: int)
  requires 0 <= i < arr.Length
{
  x := arr[i];
}

/*
  EXERCISE 5: Unsafe access

  The method below omits the precondition. Observe the verification
  error Dafny reports on the array access.
*/

method GetAtUnsafe(arr: array<int>, i: int) returns (x: int)
{
  x := arr[i]; // <-- Dafny should report: index out of range
}


/*

  When Dafny verifies a loop, it does not run the loop.
  Instead it asks what property is preserved by each iteration.

  A loop invariant is a predicate that:
    (1) holds before the loop starts
    (2) is maintained by every iteration
    (3) combined with the loop exit condition, implies the postcondition

  This is the core concept of Hoare logic for loops.

  The method below does not verify because Dafny has no information
  about what `s` represents at each step. Your job is to add the
  missing invariants to SumFixed.
*/

method Sum(n: int) returns (s: int)
  requires n >= 0
  ensures s == n * (n + 1) / 2
{
  s := 0;
  var i := 0;
  while i <= n
  {
    s := s + i;
    i := i + 1;
  }
}

/*
  EXERCISE 6 (CORE): Add loop invariants to SumFixed

  You need two invariants:
    (a) A range invariant: what are the possible values of i?
        Hint: i starts at 0 and increases; what is its upper bound?

    (b) A value invariant: what does s equal at the start of
        iteration i?
        Hint: after processing 0..i-1, what closed-form equals s?

  Both invariants must hold before the loop (check with i=0, s=0),
  after each iteration, and together imply the postcondition
  when the loop exits at i = n+1.
*/

method SumFixed(n: int) returns (s: int)
  requires n >= 0
  ensures s == n * (n + 1) / 2
{
  s := 0;
  var i := 0;
  while i <= n
    invariant true // TODO: replace with range invariant, e.g. 0 <= i <= ?
    invariant true // TODO: replace with value invariant, e.g. s == ?
  {
    s := s + i;
    i := i + 1;
  }
}


/*

  This method finds the maximum element of a non-empty array.
  The postcondition uses a universal quantifier, saying that
  for all valid indices i, m is at least arr[i].

  `reads arr` is required whenever the spec or body accesses
  array elements.

  The version below does not verify. Dafny cannot establish
  the postcondition without knowing what m represents mid-loop.
*/

method MaxArray(arr: array<int>) returns (m: int)
  requires arr.Length > 0
  ensures forall i :: 0 <= i < arr.Length ==> m >= arr[i]
{
  m := arr[0];
  var i := 1;
  while i < arr.Length
  {
    if arr[i] > m {
      m := arr[i];
    }
    i := i + 1;
  }
}

/*

  You need two invariants:
    (a) A range invariant: what are the valid values of i?
        Hint: i starts at 1 and never exceeds arr.Length.

    (b) A maximality invariant: what does m represent so far?
        Hint: m is the max of arr[0..i). Express this with a
        forall quantifier over the indices already visited.

  When the loop exits at i == arr.Length, the maximality invariant
  covers the whole array, which is exactly the postcondition.
*/

method MaxArrayFixed(arr: array<int>) returns (m: int)
  requires arr.Length > 0
  ensures forall i :: 0 <= i < arr.Length ==> m >= arr[i]
{
  m := arr[0];
  var i := 1;
  while i < arr.Length
    invariant true // TODO: replace with range invariant
    invariant true // TODO: replace with maximality invariant over arr[0..i)
  {
    if arr[i] > m {
      m := arr[i];
    }
    i := i + 1;
  }
}
