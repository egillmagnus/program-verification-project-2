# Fibonacci.vpr - Line-by-Line Explanation

This document provides a detailed line-by-line explanation of `fibonacci.vpr`, explaining both the Viper syntax and the verification logic.

---

## File Overview

This file implements a recursive Fibonacci function and proves:
1. **Functional correctness**: The function returns the correct Fibonacci number
2. **Runtime bound**: The function uses exactly the minimum number of time credits

---

## Lines 1-8: Comment Block

```viper
/*
 * CHALLENGE 1
 * The Viper code below shows a method that recursively computes the n-th Fibonacci number. 
 * First, prove functional correctness, i.e. that the method indeed returns the n-th Fibonacci number.
 * After that, find the smallest upper bound on the method's runtime in our runtime model.
 * Finally, prove that your bound is indeed the smallest upper bound on the method's runtime.
 */
```

**Explanation**: Multi-line comments in Viper use `/* ... */` syntax (same as C/Java). This describes the challenge requirements.

---

## Lines 11-14: Time Credit Predicate

```viper
// -----------------------------------------
// Runtime model
// Notice that we can hold at most one permission
// to *fields*, but this does not apply to *predicates*
predicate time_credit() // represents one abstract unit of time
```

### Line 15: `predicate time_credit()`

**Viper Syntax**: 
- `predicate name()` declares an abstract predicate
- Predicates in Viper represent abstract resources (permissions)
- Unlike fields, predicates can be held in fractional or multiple amounts

**Purpose**: 
- Models an abstract "unit of time" for runtime analysis
- Each time credit represents one operation
- Having `n` time credits means we can perform `n` operations

**Why no body?**: 
- This is an *abstract* predicate - it has no definition
- We only care about *having* the permission, not what it contains
- Think of it like a "token" that gets consumed

---

## Lines 17-20: Consume Time Credit Method

```viper
// models spending an abstract unit of time 
// needs to be called at the beginning of every method
// and loop iteration
method consume_time_credit() // 
    requires acc(time_credit(), 1/1)
```

### Line 20: `method consume_time_credit()`

**Viper Syntax**:
- `method name()` declares a method (can have side effects, unlike functions)
- Methods can have `requires` (preconditions) and `ensures` (postconditions)

### Line 21: `requires acc(time_credit(), 1/1)`

**Viper Syntax**:
- `requires` introduces a precondition (must be true when method is called)
- `acc(predicate, fraction)` means "access permission to predicate with given fraction"
- `1/1` means full (100%) permission

**Purpose**:
- Calling this method "spends" one time credit
- The precondition demands 1 full time credit
- No postcondition means the credit is consumed (not returned)

**Why no body?**:
- This is an abstract model - we don't need actual code
- The *specification* is what matters for verification
- Viper accepts methods without bodies (they're treated as axioms)

---

## Lines 25-30: Fibonacci Definition

```viper
// -----------------------------------------
// Mathematical definition of the Fibonacci sequence
function fib(n: Int): Int
    requires n >= 0
{
    n == 0 ? 0 : (n == 1 ? 1 : fib(n - 1) + fib(n - 2))
}
```

### Line 27: `function fib(n: Int): Int`

**Viper Syntax**:
- `function name(param: Type): ReturnType` declares a pure function
- Functions in Viper are **pure** - no side effects, no state changes
- They can be used in specifications (requires/ensures/invariants)

**Key Difference from Methods**:
- Functions: pure, can appear in specs, must terminate
- Methods: can have side effects, cannot appear in specs directly

### Line 28: `requires n >= 0`

**Viper Syntax**:
- Functions can have preconditions too
- `>=` is the greater-than-or-equal operator

**Purpose**: Fibonacci is only defined for non-negative integers.

### Lines 29-31: Function Body

```viper
{
    n == 0 ? 0 : (n == 1 ? 1 : fib(n - 1) + fib(n - 2))
}
```

**Viper Syntax**:
- `condition ? then_value : else_value` is the ternary conditional operator
- Nested ternaries handle multiple cases
- `==` is equality comparison

**Logic**:
- If n == 0: return 0
- Else if n == 1: return 1  
- Else: return fib(n-1) + fib(n-2)

This is the standard mathematical definition: F(0)=0, F(1)=1, F(n)=F(n-1)+F(n-2)

---

## Lines 33-42: Time Credits Function

```viper
// Helper function to calculate time credits needed
// The recursive structure mirrors fib_recursive's calls:
// T(n) = 1 + T(n-1) + T(n-2) for n >= 2
// T(0) = T(1) = 1
function time_credits(n: Int): Int
    requires n >= 0
    ensures result >= 1
{
    n == 0 || n == 1 ? 1 : 1 + time_credits(n - 1) + time_credits(n - 2)
}
```

### Line 37: `function time_credits(n: Int): Int`

**Purpose**: Calculates the exact number of time credits needed to compute fib(n).

### Line 39: `ensures result >= 1`

**Viper Syntax**:
- `ensures` introduces a postcondition (guaranteed true after function returns)
- `result` is a special keyword referring to the return value
- This postcondition says "the result is always at least 1"

**Why needed?**: 
- Later we use `time_credits(n)/1` as a fraction for permissions
- Viper requires fractions to be positive
- This postcondition proves the fraction is well-formed

### Lines 40-42: Function Body

```viper
{
    n == 0 || n == 1 ? 1 : 1 + time_credits(n - 1) + time_credits(n - 2)
}
```

**Logic**:
- Base cases (n=0 or n=1): need 1 credit (for the method call itself)
- Recursive case: need 1 credit + credits for both recursive calls

**Key Insight**: This mirrors the structure of fib_recursive exactly:
- T(n) = 1 + T(n-1) + T(n-2)
- This is why it's the *tight* bound

---

## Lines 44-53: Method Specification

```viper
// -----------------------------------------
// Task 1: Prove a runtime bound for the following recursive method
// ...
method fib_recursive(n: Int) returns (res: Int)
    requires n >= 0
    // TODO add time credits and functional specification
    requires acc(time_credit(), time_credits(n)/1)
    ensures res == fib(n)
```

### Line 52: `method fib_recursive(n: Int) returns (res: Int)`

**Viper Syntax**:
- `returns (name: Type)` declares return values
- Unlike functions, methods use explicit return variables
- The return variable `res` can be assigned to in the method body

### Line 53: `requires n >= 0`

**Purpose**: Same as the fib function - Fibonacci is only for non-negative integers.

### Line 55: `requires acc(time_credit(), time_credits(n)/1)`

**Viper Syntax**:
- `acc(predicate(), fraction)` requires permission to a predicate
- `time_credits(n)/1` is a fraction (numerator/denominator)
- This requires `time_credits(n)` full permissions to `time_credit()`

**Purpose**:
- States how many time credits the method needs
- The caller must provide exactly this many credits
- This is the runtime bound we're proving

**Why `time_credits(n)/1` syntax?**:
- Viper permissions are fractions between 0 and 1 for fields
- For predicates, we can have more than 1 (multiple instances)
- `k/1` means k full permissions

### Line 56: `ensures res == fib(n)`

**Purpose**: 
- Functional correctness specification
- Guarantees the result equals the mathematical Fibonacci number
- `res` refers to the return value

---

## Lines 57-72: Method Body

```viper
{
    consume_time_credit() // we must spend a credit for every call

    if (n == 0) {
        res := 0
    } elseif (n == 1) {
        res := 1
    } else {
        var sub1: Int
        sub1 := fib_recursive(n - 1)

        var sub2: Int
        sub2 := fib_recursive(n - 2)

        res := sub1 + sub2
    }
}
```

### Line 58: `consume_time_credit()`

**Purpose**: 
- Every method call consumes one time credit
- This models that "calling this method costs 1 unit of time"
- After this call, we have `time_credits(n) - 1` credits remaining

**Verification Logic**:
- Precondition of consume_time_credit: need 1 credit
- We had time_credits(n) credits
- For n >= 2: time_credits(n) = 1 + time_credits(n-1) + time_credits(n-2)
- After consuming 1: we have time_credits(n-1) + time_credits(n-2) left

### Lines 60-62: Base Case n == 0

```viper
    if (n == 0) {
        res := 0
    }
```

**Viper Syntax**:
- `if (condition) { ... }` is standard conditional
- `res := 0` assigns to the return variable
- `:=` is the assignment operator (not `=` which is equality)

**Verification**: 
- fib(0) = 0, so `res == fib(n)` is satisfied
- We consumed 1 credit, and time_credits(0) = 1, so all credits used ✓

### Lines 62-64: Base Case n == 1

```viper
    } elseif (n == 1) {
        res := 1
    }
```

**Viper Syntax**:
- `elseif` (one word) for else-if chains

**Verification**:
- fib(1) = 1, so postcondition satisfied
- time_credits(1) = 1, all credits used ✓

### Lines 64-72: Recursive Case

```viper
    } else {
        var sub1: Int
        sub1 := fib_recursive(n - 1)

        var sub2: Int
        sub2 := fib_recursive(n - 2)

        res := sub1 + sub2
    }
```

### Line 65: `var sub1: Int`

**Viper Syntax**:
- `var name: Type` declares a local variable
- Variables must be declared before use
- Type annotation is required

### Line 66: `sub1 := fib_recursive(n - 1)`

**Verification Logic**:
- Calling fib_recursive(n-1) requires time_credits(n-1) credits
- We have time_credits(n-1) + time_credits(n-2) remaining
- After this call: time_credits(n-2) credits remain
- Postcondition gives us: sub1 == fib(n-1)

### Lines 68-69: Second Recursive Call

```viper
        var sub2: Int
        sub2 := fib_recursive(n - 2)
```

**Verification Logic**:
- Requires time_credits(n-2) credits (exactly what we have!)
- Postcondition: sub2 == fib(n-2)
- After this: 0 credits remain (perfect!)

### Line 71: `res := sub1 + sub2`

**Verification**:
- sub1 == fib(n-1) and sub2 == fib(n-2)
- res = sub1 + sub2 = fib(n-1) + fib(n-2) = fib(n) ✓

---

## Lines 74-86: Tightness Proof Comment

```viper
// -----------------------------------------
// PROOF THAT THE BOUND IS TIGHT
// This lemma demonstrates that using fewer time credits would fail verification.
// ...
```

**Purpose**: Documents why `time_credits(n)` is the minimum needed.

**Key Insight**: 
- The verification itself proves tightness
- If we used `time_credits(n) - 1` credits, verification would fail
- The recursive structure of time_credits exactly matches the algorithm

---

## Deep Dive: Viper's Permission System

The Fibonacci example uses a simple permission model, but understanding it is crucial:

### What Are Permissions?

In Viper, you cannot access memory (fields, predicates) without **permission**. This prevents:
- Data races in concurrent programs
- Use-after-free bugs
- Aliasing problems

### Permission to time_credit()

```viper
requires acc(time_credit(), time_credits(n)/1)
```

**Breaking this down:**
- `acc(resource, amount)` - "access permission to resource with given amount"
- `time_credit()` - the predicate we want permission to
- `time_credits(n)/1` - a fraction meaning "time_credits(n) full permissions"

**Why fractions?**
- For fields: fractions allow shared read access (e.g., 1/2 + 1/2 = 1)
- For predicates: we can hold multiple instances
- `k/1` means k full (100%) permissions to the predicate

### Permission Flow in fib_recursive

```
Caller has: time_credits(n) permissions to time_credit()
    |
    v
fib_recursive(n) starts
    |
    v
consume_time_credit() takes 1 permission
    |
    v
Remaining: time_credits(n) - 1 = time_credits(n-1) + time_credits(n-2)
    |
    +---> fib_recursive(n-1) takes time_credits(n-1) permissions
    |
    +---> fib_recursive(n-2) takes time_credits(n-2) permissions
    |
    v
All permissions consumed (nothing returned to caller)
```

### Why No Postcondition About Permissions?

```viper
method fib_recursive(n: Int) returns (res: Int)
    requires acc(time_credit(), time_credits(n)/1)
    ensures res == fib(n)
    // No "ensures acc(...)" - permissions are consumed!
```

The method consumes all time credits and doesn't return any. This models that computation "uses up" time.

### Abstract vs Concrete Predicates

**Abstract predicate** (no body):
```viper
predicate time_credit()  // Just declared, no definition
```
- Cannot be folded/unfolded
- Only tracked as a permission token
- Used for abstract resources

**Concrete predicate** (with body):
```viper
predicate dyn_array(self: Ref) {
    acc(self.length) && ...
}
```
- CAN be folded/unfolded
- Body specifies what permissions it contains
- Used for data structure invariants

In fibonacci.vpr, `time_credit()` is abstract - we don't care what's "inside" it, just that we have it.

---

## Summary of Key Viper Concepts

| Concept | Syntax | Purpose |
|---------|--------|---------|
| Predicate | `predicate name()` | Abstract resource/permission |
| Function | `function name(): Type` | Pure computation for specs |
| Method | `method name() returns (x: Type)` | Imperative code with side effects |
| Precondition | `requires condition` | Must be true when called |
| Postcondition | `ensures condition` | Guaranteed true after return |
| Permission | `acc(predicate(), frac)` | Access permission to resource |
| Assignment | `x := value` | Assign value to variable |
| Variable | `var x: Type` | Declare local variable |
| Ternary | `c ? a : b` | Conditional expression |
