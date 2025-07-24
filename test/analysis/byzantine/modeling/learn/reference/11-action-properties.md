# Action Properties

**Core Chapter**: Properties on transitions between states - safety properties that restrict how systems are allowed to change, beyond what invariants can capture.

## Conceptual Foundation
Action properties are safety properties that aren't invariants. While invariants check individual states, action properties check **transitions** between states. They restrict how the system can change.

**Key Insight:** Some violations aren't "bad states" but "bad transitions" between valid states.

Example: `counter = 0` and `counter = 1` are both valid states, but `counter` decreasing from 1 to 0 might be invalid.

## The Prime Operator (`'`)
`x'` is the value of `x` in the **next state**. This enables describing transitions:
- `counter' >= counter` means counter only increases
- `lock' # NULL => lock = NULL` means lock can only be acquired from NULL

**Actions:** Boolean expressions containing primed variables (e.g., `x' > x`).

## Box Action Formula Syntax
Action properties use the form `[][P]_vars` where:
- `[]` means "always true"  
- `[P]_vars` means `P \/ UNCHANGED vars` (handles stuttering)
- `vars` includes all variables referenced in `P`

**Complete Example:**
```tla+
CounterOnlyIncreases == [][counter' >= counter]_counter
```

### Understanding the Expansion
`[][counter' >= counter]_counter` expands to:
1. `[counter' >= counter]_counter`
2. `counter' >= counter \/ UNCHANGED counter`  
3. `counter' >= counter \/ counter' = counter`
4. `counter' >= counter` (simplified)

**Key Point:** The `_vars` part makes properties stutter-invariant (essential for TLA+).

## Practical Examples

### Monotonic Properties
```tla+
CounterOnlyIncreases == [][counter' >= counter]_counter
ValueNeverDecreases == [][x' >= x]_x
```

### State Transition Restrictions
```tla+
// Lock can't go directly between threads
LockCantBeStolen == [][lock # NULL => lock' = NULL]_lock

// Must release before another can acquire  
LockNullBeforeAcquired == [][lock' # NULL => lock = NULL]_lock
```

### Conditional Properties
```tla+
// System behavior when disabled
[][disabled => UNCHANGED x]_<<disabled, x>>

// Lockstep changes
[][x' /= x => y' = x]_<<x, y>>

// Action-triggered invariants
[][Machine => Inv]_vars  // Only Machine actions must maintain Inv
```

### State Machine Validation
```tla+
// Valid server state transitions
Transitions == {<<Offline, Booting>>, <<Booting, Online>>, <<Online, Offline>>}
[][<<status, status'>> \in Transitions]_status

// Prevent invalid direct transitions
[][status = Offline => status' # Online]_status
```

## Quantified Action Properties
TLC limitation: Cannot check `\A x: [][P(x)]_vars` directly.

**Workaround:** Pull quantifier inside the action property.
```tla+
// ❌ This fails - TLC can't check
CounterIncreases == \A c \in Counters: [][values[c]' >= values[c]]_values[c]

// ✅ This works - quantifier inside
CounterIncreases == [][
  \A c \in Counters: values[c]' >= values[c]
]_values
```

**Mathematical Foundation:** `[]` commutes with `\A`, so `\A x: []P(x)` ≡ `[](\A x: P(x))`.

## Advanced Patterns

### Helper Actions
```tla+
BecomesNull(x) == x' = NULL
LockCantBeStolen == [][lock # NULL => BecomesNull(lock)]_lock
```

### Multiple Variable Coordination
```tla+
// If ownership changes from A to B, it must be via valid Accept action
ValidChange(credit) ==
  LET co == owner[credit]
  IN co /= co' => Accept(co, co', credit)

ChangeProp == [][\A c \in Credits: ValidChange(c)]_owner
```

### Append-Only Structures
```tla+
// Log is append-only (prior values never change)
[][SubSeq(log', 1, Len(log)) = log]_log
```

## Verification and Usage
- **Checked as:** Temporal properties (not invariants)
- **In Toolbox:** "Temporal Properties" section
- **CLI:** `PROPERTY` statements in config
- **Performance:** Slower than invariants, faster than liveness properties

## Common Use Cases
1. **Monotonicity:** Values that only increase/decrease
2. **State Machines:** Valid transition validation
3. **Resource Management:** Lock acquisition/release patterns
4. **Data Integrity:** Append-only logs, immutable fields
5. **Conditional Behavior:** System behavior under specific conditions
6. **Multi-Variable Coordination:** Synchronized changes across variables

## Critical Gotchas
- Must include all referenced variables in subscript (`_vars`)
- Action properties check transitions, not states
- Quantifiers need special handling (pull inside `[]`)
- Primed variables represent **next** state values
- `UNCHANGED x` is syntactic sugar for `x' = x`

## Best Practices
- Use action properties for transition validation
- More common than liveness, less than invariants
- Powerful but optional (unlike liveness properties)
- Combine with helper actions for clarity
- Test with simple cases first to verify logic 