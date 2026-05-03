/*
  ############################################################
  ### SETUP & INSTALLATION
  ############################################################

  This lab runs in GitHub Codespaces, no local install needed.

  1. Open the repository link provided by your instructor.
  2. Click the green "Code" button, then "Codespaces", then "Create codespace".
  3. Wait for the environment to load (this may take a minute).
  4. Open this file in the editor.
  5. Open a terminal (Ctrl+`) and run:

       dafny verify Lab1_Basics.dfy

  The Dafny extension will also show inline red squiggles as you
  type, but may take a moment to start.
*/


/*
  ############################################################
  ### INTRODUCTION
  ############################################################

  Dafny is a programming language with built-in verification.
  Programs are written alongside specifications, and Dafny checks
  that the code satisfies the specification for every possible input.

  This is different from testing, which only checks the inputs you
  thought to try. A program can pass all its tests and still be wrong
  if the specification is too weak, or if the specification itself
  does not capture what you intended.

  Getting both the code and the specification right is your job.
*/


/*
  An `ensures` clause is a postcondition: a property Dafny will
  check holds whenever the method returns.
*/

method Double(x: int) returns (y: int)
  ensures y == 2 * x
{
  y := x + x;
}

/*
  Try breaking the implementation by changing `x + x` to `x + 1`.
  Dafny should reject it.
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
  A `requires` clause is a precondition: a constraint on the inputs
  that any caller must satisfy. Dafny will reject call sites that
  cannot prove the precondition holds.

  Division by zero is undefined, so the method below requires y != 0.
*/

method Divide(x: int, y: int) returns (r: int)
  requires y != 0
  ensures r == x / y
{
  r := x / y;
}


/*
  EXERCISE 2: Max

  Implement Max. The two postconditions together express that m is at
  least as large as both inputs and equals one of them, which fully
  pins down what max means.
*/

method Max(x: int, y: int) returns (m: int)
  ensures m >= x && m >= y
  ensures m == x || m == y
{
  m := x; // TODO: replace with a correct implementation
}


/*
  ############################################################
  ### WEAK VS STRONG SPECIFICATIONS
  ############################################################

  The method below verifies, but is clearly wrong:
*/

method MaxWeak(x: int, y: int) returns (m: int)
  ensures m >= x && m >= y
{
  m := x + y + 1; // not a max, but Dafny accepts it!
}

/*
  Dafny accepts this because the specification is too weak. Saying
  that m is an upper bound on x and y is not enough to pin down max,
  since any sufficiently large value will do.

  EXERCISE 3: Strengthen the specification

  Add a second `ensures` clause to MaxWeakFixed so that the bogus
  implementation above is rejected. Change only the spec, not the body.
*/

method MaxWeakFixed(x: int, y: int) returns (m: int)
  ensures m >= x && m >= y
  // TODO: add a second ensures clause here
{
  m := x + y + 1; // Dafny should reject this once your spec is strong enough
}


/*
  ############################################################
  ### WHAT IS CORRECTNESS?
  ############################################################

  Specifications encode assumptions about the real world, and
  choosing what to specify is a design decision.

  EXERCISE 4: Specify the bank transfer

  Add `requires` and `ensures` clauses to TransferSpec below.
  Think through each of these:

    (a) Conservation: should total money be preserved?
        Hint: what should (a2 + b2) equal?

    (b) Validity: should either balance be allowed to go negative?
        Hint: add a requires relating `a` and `amount`.

    (c) Direction: should `amount` be required to be positive?
        What goes wrong if amount is negative or zero?

  Start with (a), which captures the most fundamental property.
*/

method TransferSpec(a: int, b: int, amount: int) returns (a2: int, b2: int)
  requires true // TODO: replace with real preconditions
  ensures true  // TODO: replace with real postconditions
{
  a2 := a - amount;
  b2 := b + amount;
}


/*
  ############################################################
  ### PROOF PREVENTS RUNTIME ERRORS
  ############################################################

  Array accesses in Dafny are checked at verification time. If Dafny
  cannot prove an access is in bounds, it will not compile the program.
*/

method GetAt(arr: array<int>, i: int) returns (x: int)
  requires 0 <= i < arr.Length
{
  x := arr[i];
}

/*
  EXERCISE 5: Unsafe access

  The method below omits the precondition. Observe the error Dafny
  reports on the array access, and compare it to what would happen
  at runtime in Java or Python. Which would you rather have, and why?
*/

method GetAtUnsafe(arr: array<int>, i: int) returns (x: int)
{
  x := arr[i]; // <-- Dafny should report: index out of range
}


/*
  ############################################################
  ### LOOPS AND INVARIANTS
  ############################################################

  Dafny does not verify loops by running them. Instead, it asks
  for a loop invariant: a property that holds before the loop begins,
  is preserved by every iteration, and together with the exit condition
  implies the postcondition. This is the core idea behind Hoare logic.

  The method below does not verify because Dafny has no information
  about what `s` represents at each step. SumFixed is your version
  to complete.
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

  Both must hold before the loop (check with i=0, s=0), be preserved
  by each iteration, and together imply the postcondition when the
  loop exits at i = n+1.
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
  ############################################################
  ### ARRAY MAX
  ############################################################

  Finding the maximum of an array requires reasoning about all
  elements at once. The postcondition below uses a universal
  quantifier to express this: for every valid index i, m >= arr[i].

  Without invariants, Dafny cannot establish this postcondition
  because it has no account of what m represents mid-loop.
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
  EXERCISE 7: Add loop invariants to MaxArrayFixed

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
