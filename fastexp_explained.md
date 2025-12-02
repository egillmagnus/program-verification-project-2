# Fastexp.vpr - Line-by-Line Explanation

This document provides a detailed line-by-line explanation of `fastexp.vpr`, explaining both the Viper syntax and the verification logic for fast exponentiation.

---

## File Overview

This file implements the "exponentiation by squaring" algorithm and proves:
1. **Functional correctness**: The function correctly computes n^e
2. **Runtime bound**: O(log e) iterations - specifically `1 + iterations_needed(e)` time credits

---

## Lines 1-13: Runtime Model (Same as Fibonacci)

```viper
// -----------------------------------------
// Runtime model
predicate time_credit()

method consume_time_credit()
    requires acc(time_credit(), 1/1)
// -----------------------------------------
```

See `fibonacci_explained.md` for detailed explanation of the runtime model.

---

## Lines 15-22: Mathematical Power Function

```viper
// -----------------------------------------
// Mathematical power function. 
// Think of this like your specification (compare to sorting)
function math_pow(n: Int, e: Int) : Int
    requires 0 <= e
{
    e == 0 ? 1 : n * math_pow(n, e - 1)
}
// -----------------------------------------
```

### Line 18: `function math_pow(n: Int, e: Int) : Int`

**Viper Syntax**:
- Multiple parameters separated by commas
- Return type after colon

**Purpose**: 
- Mathematical specification of exponentiation
- Used to specify what the algorithm should compute
- Recursive definition: n^0 = 1, n^e = n × n^(e-1)

### Line 19: `requires 0 <= e`

**Purpose**: Exponentiation is defined for non-negative exponents only.

### Line 21: `e == 0 ? 1 : n * math_pow(n, e - 1)`

**Logic**:
- Base case: n^0 = 1
- Recursive case: n^e = n × n^(e-1)

---

## Lines 24-32: Even Case Lemma (Provided)

```viper
// -----------------------------------------
// You can use this lemma without a proof
method lemma_pow(b: Int, y: Int) 
    requires 0 <= y
    requires y % 2 == 0 // y is even
    ensures math_pow(b, y) == math_pow(b * b, y / 2)
```

### Understanding Lemma Methods

**What is a Lemma in Viper?**:
- A method that establishes a mathematical fact
- Has preconditions (assumptions) and postconditions (conclusions)
- Can be called to "teach" the verifier a fact it can't prove automatically

### Line 27: `method lemma_pow(b: Int, y: Int)`

**Purpose**: States that b^y = (b²)^(y/2) when y is even.

### Line 28: `requires 0 <= y`

**Purpose**: y must be non-negative.

### Line 29: `requires y % 2 == 0`

**Viper Syntax**:
- `%` is the modulo operator
- `y % 2 == 0` means y is even

### Line 30: `ensures math_pow(b, y) == math_pow(b * b, y / 2)`

**Mathematical Meaning**:
- When y is even: b^y = (b×b)^(y/2) = (b²)^(y/2)
- This is the key property for fast exponentiation

**Why No Body?**:
- Comment says "You can use this lemma without a proof"
- This is a provided mathematical fact
- The verifier accepts it as an axiom

---

## Lines 33-53: Odd Case Lemma (Added)

```viper
// Lemma for odd case: proves that when y is odd,
// res * b^y == target implies (res*b) * (b*b)^(y/2) == target
method lemma_pow_odd(b: Int, y: Int, res: Int, target: Int)
    requires 0 < y
    requires y % 2 == 1 // y is odd
    requires res * math_pow(b, y) == target
    ensures (res * b) * math_pow(b * b, y / 2) == target
{
    // Proof:
    // Since y > 0, by definition: math_pow(b, y) == b * math_pow(b, y - 1)
    // Since y is odd, y - 1 is even, so we can apply lemma_pow:
    //   math_pow(b, y - 1) == math_pow(b * b, (y - 1) / 2)
    // When y is odd: (y - 1) / 2 == y / 2 (integer division)
    // Therefore: math_pow(b, y) == b * math_pow(b * b, y / 2)
    // So: res * math_pow(b, y) == res * b * math_pow(b * b, y / 2) == target
    
    // Use the provided lemma for the even case (y - 1 is even)
    lemma_pow(b, y - 1)
    
    // The verifier can now conclude the postcondition
}
```

### Line 36: `method lemma_pow_odd(b: Int, y: Int, res: Int, target: Int)`

**Purpose**: Handles the odd case of the algorithm.

**Parameters**:
- `b`: the base
- `y`: the exponent (odd)
- `res`: current accumulated result
- `target`: the value we're trying to compute (n^e)

### Line 37: `requires 0 < y`

**Purpose**: y must be positive (not just non-negative) because we'll use y-1.

### Line 38: `requires y % 2 == 1`

**Purpose**: y must be odd (this lemma is for the odd case).

### Line 39: `requires res * math_pow(b, y) == target`

**Purpose**: 
- This is the loop invariant before the transformation
- States that `res × b^y = target` (our goal)

### Line 40: `ensures (res * b) * math_pow(b * b, y / 2) == target`

**Purpose**:
- After the algorithm's transformation, the invariant still holds
- When y is odd: multiply res by b, then square b and halve y

### Line 51: `lemma_pow(b, y - 1)`

**Viper Syntax**:
- Calling a lemma method "invokes" the lemma
- The verifier learns the postcondition of the lemma
- Here: math_pow(b, y-1) == math_pow(b*b, (y-1)/2)

**Proof Logic**:
1. Since y is odd, y-1 is even
2. By lemma_pow: b^(y-1) = (b²)^((y-1)/2)
3. Since y is odd: (y-1)/2 = y/2 (integer division)
4. So: b^(y-1) = (b²)^(y/2)
5. Therefore: b^y = b × b^(y-1) = b × (b²)^(y/2)
6. Thus: res × b^y = res × b × (b²)^(y/2) = (res×b) × (b²)^(y/2)

---

## Lines 55-66: Iterations Needed Function

```viper
// -----------------------------------------
// Helper function to calculate the number of iterations needed
// This equals floor(log2(e)) + 1, which is the number of times
// we can divide e by 2 until we reach 0
function iterations_needed(e: Int): Int
    requires 0 < e
    ensures result >= 1
{
    e == 1 ? 1 : 1 + iterations_needed(e / 2)
}
// -----------------------------------------
```

### Line 59: `function iterations_needed(e: Int): Int`

**Purpose**: Calculates the number of loop iterations for exponent e.

### Line 60: `requires 0 < e`

**Purpose**: e must be positive (we don't handle e=0 in the loop).

### Line 61: `ensures result >= 1`

**Purpose**: 
- Guarantees the result is at least 1
- Needed because we use this in permission fractions

### Lines 63-65: Function Body

```viper
{
    e == 1 ? 1 : 1 + iterations_needed(e / 2)
}
```

**Logic**:
- Base case (e=1): 1 iteration
- Recursive case: 1 + iterations for e/2

**Mathematical Meaning**: 
- This equals ⌊log₂(e)⌋ + 1
- E.g., e=8: iterations = 1 + iter(4) = 1 + 1 + iter(2) = 1 + 1 + 1 + iter(1) = 4
- e=7: iter(7) = 1 + iter(3) = 1 + 1 + iter(1) = 3

---

## Lines 68-81: Method Specification

```viper
// -----------------------------------------
// Task 2: Prove a runtime bound for the following recursive method
// ...
method fast_pow(n: Int, e: Int) returns (res: Int)
    requires 0 < e
    ensures res == math_pow(n, e) // functional specification
    requires acc(time_credit(), (1 + iterations_needed(e))/1)
{
```

### Line 76: `method fast_pow(n: Int, e: Int) returns (res: Int)`

**Purpose**: Computes n^e efficiently.

### Line 77: `requires 0 < e`

**Purpose**: Exponent must be positive.

### Line 78: `ensures res == math_pow(n, e)`

**Purpose**: Functional correctness - result equals n^e.

### Line 79: `requires acc(time_credit(), (1 + iterations_needed(e))/1)`

**Purpose**:
- Runtime bound specification
- Needs 1 credit for method call + iterations_needed(e) for loop iterations
- Total: O(log e) credits

---

## Lines 82-86: Method Setup

```viper
    consume_time_credit() // we must spend a credit for every call

    var y : Int := e // local copy of exponent
    var b : Int := n // local copy of base
    res := 1 // accumulator for result
```

### Line 82: `consume_time_credit()`

**Purpose**: Spend 1 credit for the method call itself.

### Line 84: `var y : Int := e`

**Viper Syntax**:
- `var name : Type := value` declares and initializes
- `:=` is assignment

**Purpose**: Working copy of exponent (will be modified).

### Line 85: `var b : Int := n`

**Purpose**: Working copy of base (will be squared).

### Line 86: `res := 1`

**Purpose**: Accumulator starts at 1 (identity for multiplication).

---

## Lines 88-113: Main Loop

```viper
    // loop invariant: res * b^y == n^e
    while (y > 0)
        invariant y >= 0
        invariant res * math_pow(b, y) == math_pow(n, e)
        invariant y > 0 ==> acc(time_credit(), iterations_needed(y)/1)
    {
```

### Line 89: `while (y > 0)`

**Viper Syntax**:
- `while (condition) invariant ... { body }` is a while loop
- Invariants come between condition and body

### Line 90: `invariant y >= 0`

**Purpose**: 
- y is always non-negative
- Needed because math_pow requires non-negative exponent

### Line 91: `invariant res * math_pow(b, y) == math_pow(n, e)`

**Purpose**:
- Core algorithmic invariant
- "Current result times remaining power equals target"
- Initially: 1 × n^e = n^e ✓
- At end (y=0): res × b^0 = res × 1 = res = n^e ✓

### Line 92: `invariant y > 0 ==> acc(time_credit(), iterations_needed(y)/1)`

**Viper Syntax**:
- `==>` is logical implication (if-then)
- `A ==> B` means "if A is true, then B must be true"

**Purpose**:
- When y > 0, we have iterations_needed(y) credits for remaining iterations
- When y = 0, loop exits, no credits needed
- The implication avoids calling iterations_needed(0) which violates its precondition

---

## Lines 93-111: Loop Body

```viper
        consume_time_credit() // we must spend a credit for every iteration

        if (y % 2 == 1) {
            // y is odd: res := res * b before squaring
            // Use lemma to prove invariant preservation
            lemma_pow_odd(b, y, res, math_pow(n, e))
            res := res * b
        } else {
            // y is even: just apply squaring transformation
            lemma_pow(b, y)
        }

        y := y / 2
        b := b * b
    }
```

### Line 93: `consume_time_credit()`

**Purpose**: Each iteration costs 1 credit.

### Lines 95-99: Odd Case

```viper
        if (y % 2 == 1) {
            lemma_pow_odd(b, y, res, math_pow(n, e))
            res := res * b
        }
```

**Algorithm Logic**:
- When y is odd, we can't just halve it
- Instead: b^y = b × b^(y-1) = b × (b²)^((y-1)/2)
- Since (y-1)/2 = y/2 for odd y: b^y = b × (b²)^(y/2)
- So multiply res by b first

**Lemma Call**:
- `lemma_pow_odd(b, y, res, math_pow(n, e))` proves the invariant is preserved
- After: (res×b) × (b²)^(y/2) = n^e

### Lines 99-102: Even Case

```viper
        } else {
            lemma_pow(b, y)
        }
```

**Algorithm Logic**:
- When y is even: b^y = (b²)^(y/2)
- No need to update res

**Lemma Call**:
- `lemma_pow(b, y)` teaches verifier that b^y = (b²)^(y/2)

### Lines 104-105: Update Variables

```viper
        y := y / 2
        b := b * b
```

**Viper Syntax**:
- `/` is integer division when both operands are Int
- `*` is multiplication

**Algorithm Logic**:
- Halve the exponent (integer division)
- Square the base
- Invariant maintained: res × (b²)^(y/2) = res × new_b^new_y = n^e

---

## Lines 113-132: Tightness Comments

```viper
// -----------------------------------------
// PROOF THAT THE BOUND IS TIGHT
// ...
// The bound is tight because the loop must execute exactly iterations_needed(e) times
// ...
// -----------------------------------------
```

**Purpose**: Documents why the bound is tight (O(log e) is optimal for this algorithm).

---

## Complete Algorithm Trace

For `fast_pow(2, 13)` (computing 2^13 = 8192):

| Iteration | y | b | res | Credits Used |
|-----------|---|---|-----|--------------|
| Start | 13 | 2 | 1 | 1 (method) |
| 1 | 13 (odd) → 6 | 2 → 4 | 1 → 2 | 2 |
| 2 | 6 (even) → 3 | 4 → 16 | 2 | 3 |
| 3 | 3 (odd) → 1 | 16 → 256 | 2 → 32 | 4 |
| 4 | 1 (odd) → 0 | 256 → 65536 | 32 → 8192 | 5 |
| End | 0 | - | 8192 | 5 total |

Verify: iterations_needed(13) = 1 + iter(6) = 1 + 1 + iter(3) = 1 + 1 + 1 + iter(1) = 4
Total credits: 1 + 4 = 5 ✓

---

## Deep Dive: The Permission System

Fast exponentiation primarily uses `time_credit()` permissions. Let's understand how permissions work here.

### Permissions in Viper

Every memory access in Viper requires **permission**. For fields like `x.f`, you need `acc(x.f)`. For abstract predicates like `time_credit()`, you need `acc(time_credit())`.

**Key principle**: Permissions must be **accounted for** - you can't create them from nothing, and if you give them away, you don't have them anymore.

### Permission Fractions and Multiple Instances

```viper
requires acc(time_credit(), (1 + iterations_needed(e))/1)
```

**Breaking this down:**
- `acc(resource, amount)` - access permission with a fractional amount
- `time_credit()` - the abstract predicate (no body, just a token)
- `(1 + iterations_needed(e))/1` - the fraction

**What does the fraction mean?**
- For **fields**: fractions between 0 and 1 (e.g., 1/2 for shared read access)
- For **abstract predicates**: can exceed 1 - represents multiple instances
- `5/1` means "5 full units" of the predicate
- `(1 + iterations_needed(e))/1` means "1 + iterations_needed(e)" instances of time_credit

### Permission Flow Through fast_pow

```viper
method fast_pow(n: Int, e: Int) returns (res: Int)
    requires acc(time_credit(), (1 + iterations_needed(e))/1)  // START with these
{
    consume_time_credit()  // (1) Use 1 credit
    // Now have: iterations_needed(e) credits remaining
    
    while (y > 0)
        invariant y > 0 ==> acc(time_credit(), iterations_needed(y)/1)
    {
        consume_time_credit()  // (2) Use 1 credit per iteration
        // Remaining credits decrease each iteration
        y := y / 2
        b := b * b
    }
    // At end: y = 0, no credits required
}
```

**Permission accounting:**
```
Initial:    1 + iterations_needed(e) credits
After (1):  iterations_needed(e) credits
After loop: 0 credits (all consumed)
```

### How Permissions Decrease in the Loop

Consider `fast_pow(2, 13)`:

```
Start:       1 + iterations_needed(13) = 1 + 4 = 5 credits
Consume 1:   4 credits left = iterations_needed(13)
Iteration 1: consume 1, y: 13 → 6, need iterations_needed(6) = 3
Iteration 2: consume 1, y: 6 → 3, need iterations_needed(3) = 2
Iteration 3: consume 1, y: 3 → 1, need iterations_needed(1) = 1
Iteration 4: consume 1, y: 1 → 0, need 0 (loop exits)
Total used: 5 credits ✓
```

The invariant `y > 0 ==> acc(time_credit(), iterations_needed(y)/1)` perfectly tracks this!

### Why the Conditional Permission?

```viper
invariant y > 0 ==> acc(time_credit(), iterations_needed(y)/1)
```

**The implication (==>) is crucial!**

When `y = 0`:
- Loop condition `y > 0` is false, so loop exits
- Invariant becomes: `false ==> acc(...)` which is trivially true
- We don't need to hold any credits (we've used them all)

When `y > 0`:
- Loop will iterate at least once more
- Must hold `iterations_needed(y)` credits for remaining iterations

**Why not just `acc(time_credit(), iterations_needed(y)/1)`?**
- `iterations_needed(y)` requires `y > 0` (precondition!)
- When `y = 0`, calling `iterations_needed(0)` violates its precondition
- The implication guards against this

### Permission Transfer to consume_time_credit

```viper
method consume_time_credit()
    requires acc(time_credit(), 1/1)  // Takes exactly 1 credit
    // No postcondition - credit is "spent"
```

When we call `consume_time_credit()`:
1. We must prove we have at least 1 credit
2. That credit is transferred to the method
3. The method doesn't return it (no `ensures acc(...)`)
4. The credit is "consumed" - permanently gone

### No fold/unfold for Abstract Predicates

`time_credit()` is an **abstract predicate** (no body):

```viper
predicate time_credit()  // Just declared, nothing inside
```

**Implications:**
- Cannot `unfold` it (nothing to unfold)
- Cannot `fold` it (nothing to fold)
- Just tracked as a permission token
- Used for resource counting, not data structure abstraction

**Contrast with concrete predicates:**
```viper
predicate dyn_array(self: Ref) {
    acc(self.length) && ...  // Has a body!
}
```
Concrete predicates CAN be folded/unfolded to access their contents.

---

## Summary of Key Viper Concepts

| Concept | Syntax | Example |
|---------|--------|---------|
| Implication | `A ==> B` | `y > 0 ==> acc(...)` |
| Modulo | `%` | `y % 2 == 1` |
| Integer Division | `/` | `y / 2` |
| Loop Invariant | `invariant condition` | `invariant y >= 0` |
| Lemma Method | Method with specs, no/minimal body | `method lemma_pow(...)` |
| While Loop | `while (cond) invariant ... { body }` | See above |
