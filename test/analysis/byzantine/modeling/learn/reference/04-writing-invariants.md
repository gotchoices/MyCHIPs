# Writing an Invariant

**Core Chapter**: Testing specifications with invariants - automated verification that properties hold in every system state.

## What are Invariants?
Invariants are properties that must be true at **every single step** of the program, regardless of initial values or execution path. They're the primary testing mechanism in TLA+.

**Common example**: Type invariants - like static types in programming languages.
```tla+
TypeInvariant ==
  /\ is_unique \in BOOLEAN
  /\ seen \subseteq S  
  /\ index \in 1..Len(seq)+1
```

## Define Blocks
Invariants reference PlusCal variables, so they go in `define` blocks between variable definitions and algorithm body:

```tla+
(*--algorithm dup
variable 
  seq \in S \X S \X S \X S;
  index = 1;
  seen = {};
  is_unique = TRUE;

define
  TypeInvariant ==
    /\ is_unique \in BOOLEAN
    /\ seen \subseteq S
    /\ index \in 1..Len(seq)+1
    
end define; 

begin
  Iterate:
    // algorithm body...
```

## Error Traces
When invariants fail, TLC shows step-by-step execution leading to violation:
- **Initial state**: Starting variable values
- **Each step**: Action taken + changed variables (shown in red)
- **Final state**: Where invariant was violated
- **pc variable**: Tracks current label being executed

## Testing Algorithm Correctness
Beyond type checking, invariants verify algorithm logic:

```tla+
IsCorrect == is_unique = IsUnique(seq)
```

**Problem**: This would fail immediately since `is_unique` starts TRUE but `IsUnique(seq)` might be FALSE.

**Solution**: Only check when algorithm completes using implication:
```tla+
IsCorrect == pc = "Done" => is_unique = IsUnique(seq)
```

## Quantifiers
Essential for expressing complex properties over collections.

**Universal quantifier (`\A`)**: "For all elements"
```tla+
\A x \in {1, 2, 3}: x < 5  // TRUE - every element < 5
```

**Existential quantifier (`\E`)**: "There exists at least one"  
```tla+
\E x \in {1, 2, 3}: x > 2  // TRUE - at least one element > 2
```

**Multiple variables from same set:**
```tla+
IsComposite(num) ==
  \E m, n \in 2..num:
    m * n = num
```

**Sequence operations via indices:**
```tla+
Contains(seq, elem) ==
  \E i \in 1..Len(seq):
    seq[i] = elem

IsUnique(s) == 
  \A i, j \in 1..Len(s): 
    i # j => s[i] # s[j]
```

## The Power of Implication (`=>`)
Critical for ruling out unwanted combinations in quantifiers:

**Problem**: `\A i, j \in 1..Len(s): s[i] # s[j]` fails because `i=j` case always false.

**Solution**: Use implication to exclude equal indices:
```tla+
IsUnique(s) ==
  \A i, j \in 1..Len(s):
    i # j => s[i] # s[j]
```

**Truth table logic**: When `i = j`, `i # j` is FALSE, so `FALSE => anything` is TRUE (passes).

## Critical Rules
- **Empty set behavior**: `\A x \in {}` is always TRUE, `\E x \in {}` is always FALSE
- **Don't use `=>` with `\E`**: Use `/\` instead for existential conditions
- **Types are sets**: Any set can be a "type" (not just BOOLEAN, Integers)
- **Invariants vs assertions**: Invariants check every state; assertions check inline and stop execution

## Common Patterns
- **Type safety**: `variable \in SomeSet` 
- **Conditional checking**: `Condition => Property`
- **Range validation**: `index \in 1..Len(seq)+1`
- **Uniqueness**: `i # j => s[i] # s[j]`
- **Completion checks**: `pc = "Done" => FinalProperty`

## Error Messages
- **Assertion failure**: Error trace ends with step **before** assertion failed
- **Invariant failure**: Error trace ends with the violating step
- Variables changed in each step shown in red 