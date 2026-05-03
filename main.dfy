/*
  ############################################################
  ### SETUP & INSTALLATION
  ############################################################

  To run and verify this file interactively, use the Dafny extension
  for Visual Studio Code.

  1. Install Visual Studio Code (VS Code).
  2. Open the Extensions pane (Ctrl+Shift+X or Cmd+Shift+X).
  3. Search for "Dafny" (publisher: Dafny) and install it.
  4. Open this file (`Lab1_Basics.dfy`) in VS Code.

  The extension will automatically download the necessary verification
  tools (including the Z3 theorem prover). Verification runs
  automatically as you type. Look for the status bar at the bottom
  or inline red squiggles for verification errors.
*/


/*
  ############################################################
  ### INTRODUCTION
  ############################################################

  Goals of this lab:
    + learning the basics of Dafny
    + understanding what specifications are
    + seeing why testing is not enough
    + discovering loop invariants
    + understanding that writing correct programs means
      writing correct specifications

  Dafny is a programming language with built-in verification.

  In Dafny, we write:
    - code  (what the program does)
    - specifications (what must be true)

  Dafny checks that the code satisfies the specification
  for ALL inputs — not just the ones you test.

  Key idea:
    A program can be correct with respect to its specification,
    and still be wrong if the specification is too weak.
    Getting both right is your job.
*/


/*
  ############################################################
  ### PART 1: BASIC METHODS AND POSTCONDITIONS
  ############################################################

  `ensures` is a postcondition: a property that must hold
  when the method returns.
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
  // TODO
}


/*
  ############################################################
  ### PART 2: PRECONDITIONS
  ############################################################

  `requires` is a precondition: a constraint on inputs that
  the caller must satisfy. Dafny will reject any call site
  that cannot prove the precondition holds.
*/

/*
  NOTE: the postcondition `r * y == x` only holds when x is exactly
  divisible by y (e.g. Divide(6, 2) = 3, and 3*2 = 6).
  For non-divisible inputs, integer division truncates and the
  equation breaks. The second precondition enforces exact divisibility.
*/

method Divide(x: int, y: int) returns (r: int)
  requires y != 0
  requires x % y == 0
  ensures r * y == x
{
  r := x / y;
}


/*
  EXERCISE 2: Max

  Implement Max. The two postconditions together say:
    "m is at least as large as both inputs, and equals one of them."

  This fully pins down what max means.
*/

method Max(x: int, y: int) returns (m: int)
  ensures m >= x && m >= y
  ensures m == x || m == y
{
  // TODO
}


/*
  ############################################################
  ### PART 3: WEAK VS STRONG SPECIFICATIONS
  ############################################################
*/

/*
  This method verifies — but it is clearly wrong:
*/

method MaxWeak(x: int, y: int) returns (m: int)
  ensures m >= x && m >= y
{
  m := x + y + 1; // not a max — but Dafny accepts it!
}

/*
  Why does Dafny accept this?

  Because the specification is too weak. It only says m is an
  upper bound, not that m equals one of the inputs. Any sufficiently
  large value satisfies an upper-bound-only spec.

  EXERCISE 3: Strengthen the specification

  Add a second `ensures` clause to MaxWeakFixed so that the bogus
  implementation above is rejected, but a correct one is accepted.

  (Change only the spec, not the body.)
*/

method MaxWeakFixed(x: int, y: int) returns (m: int)
  ensures m >= x && m >= y
  // TODO: add ensures clause here
{
  m := x + y + 1; // Dafny should now reject this body
}


/*
  ############################################################
  ### PART 4: WHAT IS CORRECTNESS?
  ############################################################

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

  Start with (a) — it captures the most fundamental invariant.
*/

method TransferSpec(a: int, b: int, amount: int) returns (a2: int, b2: int)
  // TODO: requires ...
  // TODO: ensures  ...
{
  a2 := a - amount;
  b2 := b + amount;
}


/*
  ############################################################
  ### PART 5: PROOF PREVENTS RUNTIME ERRORS
  ############################################################

  Dafny proves array accesses are in-bounds at verification time,
  not at runtime. If it cannot prove safety, it refuses to compile.
*/

method GetAt(arr: array<int>, i: int) returns (x: int)
  requires 0 <= i < arr.Length
  reads arr
{
  x := arr[i];
}

/*
  EXERCISE 5: Unsafe access

  The method below omits the precondition. Observe the verification
  error Dafny reports on the array access.

  Reflection question:
    What is the difference between a Dafny verification error here
    and a Java/Python ArrayIndexOutOfBoundsException at runtime?
    Which would you rather have, and why?
*/

method GetAtUnsafe(arr: array<int>, i: int) returns (x: int)
  reads arr
{
  x := arr[i]; // <-- Dafny should report: index out of range
}


/*
  ############################################################
  ### PART 6: LOOPS AND INVARIANTS
  ############################################################

  When Dafny verifies a loop, it does not "run" the loop.
  Instead it asks: what property is preserved by each iteration?

  A loop invariant is a predicate that:
    (1) holds before the loop starts
    (2) is maintained by every iteration
    (3) combined with the loop's exit condition, implies the postcondition

  This is the core concept of Hoare logic for loops.
*/

/*
  The version below does NOT verify because Dafny has no
  information about what `s` represents at each step.
*/

method Sum(n: int) returns (s: int)
  requires n >= 0
  ensures s == n * (n + 1) / 2
{
  s := 0;
  var i := 0;

  while i <= n
    // No invariants — Dafny cannot verify the postcondition
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

  Both invariants must hold before the loop (check: i=0, s=0),
  after each iteration, and together imply the postcondition
  when the loop exits (i = n+1).
*/

method SumFixed(n: int) returns (s: int)
  requires n >= 0
  ensures s == n * (n + 1) / 2
{
  s := 0;
  var i := 0;

  while i <= n
    invariant /* TODO: range invariant, e.g. 0 <= i <= ? */
    invariant /* TODO: value invariant, e.g. s == ? */
  {
    s := s + i;
    i := i + 1;
  }
}


/*
  ############################################################
  ### PART 7: AI AND LOOP INVARIANTS
  ############################################################

  AI coding assistants can suggest loop invariants — but they
  can be subtly wrong. This exercise builds critical evaluation skills.

  EXERCISE 7:

  Step 1: Ask an AI tool (ChatGPT, Copilot, Claude, etc.) the
  following prompt verbatim:

    "What loop invariants are needed to verify this Dafny method?

     method SumFixed(n: int) returns (s: int)
       requires n >= 0
       ensures s == n * (n + 1) / 2
     {
       s := 0;
       var i := 0;
       while i <= n {
         s := s + i;
         i := i + 1;
       }
     }"

  Step 2: Paste the AI's suggested invariants into SumAI below
  and check whether Dafny accepts them.

  Step 3: Record your findings in the comment block at the bottom:
    - Did the invariants verify immediately, or did you need to fix them?
    - Were they the same as your answer to Exercise 6?
    - If Dafny rejected them, what error was reported?
    - Did the AI explain *why* each invariant is needed?
*/

method SumAI(n: int) returns (s: int)
  requires n >= 0
  ensures s == n * (n + 1) / 2
{
  s := 0;
  var i := 0;

  while i <= n
    invariant /* AI suggestion 1 */
    invariant /* AI suggestion 2 */
  {
    s := s + i;
    i := i + 1;
  }
}

/*
  AI observations:
  - Tool used:
  - Invariants suggested:
  - Verified without changes? (yes / no / partially)
  - Notes:
*/


/*
  ############################################################
  ### PART 8: STRONGER EXAMPLE — ARRAY MAX
  ############################################################

  This method finds the maximum element of a non-empty array.
  The postcondition uses a universal quantifier:
    "for all valid indices i, m is at least arr[i]"

  `reads arr` is required whenever specs or the body access
  array elements.

  The version below does NOT verify — Dafny cannot establish
  the postcondition without knowing what m represents mid-loop.
*/

method MaxArray(arr: array<int>) returns (m: int)
  requires arr.Length > 0
  reads arr
  ensures forall i :: 0 <= i < arr.Length ==> m >= arr[i]
{
  m := arr[0];
  var i := 1;

  while i < arr.Length
    // No invariants — Dafny cannot verify the postcondition
  {
    if arr[i] > m {
      m := arr[i];
    }
    i := i + 1;
  }
}


/*
  EXERCISE 8: Add loop invariants to MaxArrayFixed

  You need two invariants:
    (a) A range invariant: what are the valid values of i?
        Hint: i starts at 1 and never exceeds arr.Length.

    (b) A maximality invariant: what does m represent so far?
        Hint: m is the max of arr[0..i). Express this with a
        forall quantifier over the indices already visited.

  When the loop exits, i == arr.Length, so the maximality
  invariant covers the whole array — exactly the postcondition.
*/

method MaxArrayFixed(arr: array<int>) returns (m: int)
  requires arr.Length > 0
  reads arr
  ensures forall i :: 0 <= i < arr.Length ==> m >= arr[i]
{
  m := arr[0];
  var i := 1;

  while i < arr.Length
    invariant /* TODO: range invariant */
    invariant /* TODO: maximality invariant over arr[0..i) */
  {
    if arr[i] > m {
      m := arr[i];
    }
    i := i + 1;
  }
}


/*
  ############################################################
  ### SUMMARY
  ############################################################

  You have seen:

  1. Postconditions (ensures): properties the method guarantees
  2. Preconditions (requires): constraints callers must satisfy
  3. Weak vs. strong specifications: a weak spec admits wrong code
  4. Correctness is relative to a spec: choose specs carefully
  5. Verification vs. runtime errors: caught before execution
  6. Loop invariants: what stays true across every iteration
  7. AI suggestions need verification: always check in Dafny
  8. Quantified postconditions: reasoning about entire arrays

  The central lesson:
    Dafny does not make programs correct — it checks them against
    your specification. Writing good specifications is the hard part.
*/
