# TLA+

**Core Chapter**: Transitioning from PlusCal to pure TLA+ - understanding the mathematical foundation and gaining access to advanced features.

## Conceptual Foundation
PlusCal is a DSL that compiles to TLA+. Learning pure TLA+ provides:
- Access to advanced features impossible in PlusCal
- Understanding of the underlying mathematical model
- Higher expressiveness for complex system modeling

**Key Prerequisites:**
- Prime operator: `x'` = value of `x` in next state
- Box operator: `[P]_x` = `P \/ UNCHANGED x`

## Learning from PlusCal Translation

### Basic Structure
```tla+
---- MODULE hourclock ----
EXTENDS Naturals

VARIABLE hr
vars == << hr >>

Init == hr = 1

Next == IF hr = 12
          THEN hr' = 1
          ELSE hr' = hr + 1

Spec == Init /\ [][Next]_vars
====
```

**Key Components:**
- `VARIABLE` declarations (like `CONSTANT`)
- `Init` operator: initial state predicate  
- `Next` operator: next-state relationship (action)
- `Spec` operator: complete temporal formula

### Actions as Boolean Operators
`Next` is a **boolean operator** that describes valid transitions:
- True when it accurately describes the next state
- False when the transition is invalid

**Examples of `Next` evaluation:**
- `<<hr=1, hr'=2>>` → True (valid transition)
- `<<hr=1, hr'=1>>` → False (no progress, would need stuttering)
- `<<hr=12, hr'=1>>` → True (wrap-around)
- `<<hr=4, hr'=6>>` → False (invalid jump)

## Fundamental Rules

### Complete Variable Specification
**Critical Rule:** Next action must fully describe ALL variables.
```tla+
// ❌ Incomplete - TLC error
Next == hr' = hr + 1

// ✅ Complete - all variables specified  
Next == /\ hr' = hr + 1
        /\ UNCHANGED x
```

### Translation Patterns

#### Deterministic `with`
```tla+
// PlusCal: with x = 1 do hr := hr + x end with
// TLA+: LET x == 1 IN hr' = hr + x
```

#### Nondeterministic `with`  
```tla+
// PlusCal: with x \in 1..2 do hr := hr + x end with
// TLA+: \E x \in 1..2: hr' = hr + x
```

#### `either` Branches
```tla+
// PlusCal: either A or B end either
// TLA+: \/ A_action \/ B_action
```

## The EXCEPT Operator
Essential for function updates in pure TLA+:

```tla+
// Update single element
Next == s' = [s EXCEPT ![1] = FALSE]

// Multiple updates
Next == s' = [s EXCEPT ![1] = FALSE, ![2] = 17]

// Reference original value with @
IncCounter(c) == counter' = [counter EXCEPT ![c] = @ + 1]

// Nested updates
Next == s' = [s EXCEPT ![1].x = ~@]
```

**Critical:** `!` is the selector, `[index]` is the key. Syntax is awkward but essential.

## Concurrency in TLA+

### Process Translation
```tla+
// PlusCal process becomes parameterized action
IncCounter(self) == /\ pc[self] = "IncCounter"
                    /\ counter' = counter + 1
                    /\ pc' = [pc EXCEPT ![self] = "Done"]

// Next combines all possible process actions
Next == (\E self \in Threads: thread(self)) \/ Terminating
```

### State Management
- `pc` becomes function: process → label
- Each label maps to one action
- Concurrency via existential quantification over processes
- `await condition` → `/\ condition` in action

## Fairness in Pure TLA+

### Formal Definitions
```tla+
WF_v(A) == <>[](ENABLED <<A>>_v) => []<><<A>>_v  // Weak fairness
SF_v(A) == []<>(ENABLED <<A>>_v) => []<><<A>>_v  // Strong fairness
```

**In English:**
- **Weak fair:** If action permanently enabled → eventually happens
- **Strong fair:** If action not permanently disabled → eventually happens

### Advanced Fairness
```tla+
Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : SF_vars(thread(self))

// Subaction fairness (impossible in PlusCal)
Fairness == /\ SF_status(Succeed)
            /\ WF_status(Retry)
```

## Advanced TLA+ Capabilities

### Helper Actions
```tla+
Trans(state, from, to) ==
  /\ pc[state] = from
  /\ pc' = [pc EXCEPT ![state] = to]

IncCounter(self) ==
  /\ Trans(self, "IncCounter", "Done")
  /\ counter' = counter + 1
```

### Interruptible Algorithms
```tla+
// PlusCal requires duplicated either blocks
// TLA+ allows elegant composition:
Next == \/ A \/ B \/ C \/ D
        \/ pc' = "Start"  // Global reset
```

### Fine-grained Fairness
Apply fairness to subactions rather than entire process labels.

### Refinement Properties
Use entire specs as properties of other specs (advanced topic).

## When to Use Pure TLA+

**Advantages:**
- More expressive power
- Finer fairness control
- Helper actions and cleaner abstractions
- Complex system patterns
- Refinement verification

**PlusCal Limitations:**
- Cannot apply fairness to subactions
- Difficult interruptible algorithms  
- No helper actions
- Verbose concurrent patterns
- Limited refinement capabilities

**Recommendation:** Many practitioners use only PlusCal successfully. Learn pure TLA+ when pushing against PlusCal's limits.

## Critical Insights
- **Everything is comparison:** `x = 5` in current state, `x' = 5` in next state
- **Actions are predicates:** Boolean expressions describing valid transitions
- **Concurrency via quantification:** `\E process: action(process)`
- **Complete specification required:** All variables must be defined in Next
- **Fairness is additional constraint:** Rules out infinite stuttering

## Best Practices
- Start with PlusCal, migrate to TLA+ when needed
- Use helper actions for common patterns
- Apply fairness judiciously (not all processes need it)
- Test translations by comparing PlusCal and hand-written TLA+
- Leverage EXCEPT for all function updates 