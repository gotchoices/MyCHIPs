# Temporal Properties

**Core Chapter**: Beyond invariants - properties across entire behaviors for safety ("bad things don't happen") and liveness ("good things do happen").

## Conceptual Foundation
Invariants are just one type of temporal property. TLA+ provides general temporal operators to express properties across time, not just single states.

**Two Categories:**
- **Safety Properties**: System doesn't do bad things (includes all invariants)
- **Liveness Properties**: System eventually does good things

**Key Distinction:**
- Invariant: "At any point, at least one server online" 
- Safety (non-invariant): "There exists a particular server that's always online"
- Liveness: "Eventually all servers go offline"

## Core Temporal Operators

### `[]` (Always/Box)
`[]P` means P is true in every state of every behavior.
```tla+
Safety == \E s \in Servers: [](s \in online)  // Some server always online
```

**Properties:**
- `[]P` on its own = invariant
- `[]P \/ []Q` = either P or Q is always true (but not necessarily both)
- `[]P => []Q` = P is stronger invariant than Q

### `<>` (Eventually/Diamond) 
`<>P` means P is true in at least one state of every behavior.
```tla+
Liveness == <>(counter = NumThreads)  // Eventually reaches target
```

**Critical Issues:**
- Can be true even if P later becomes false again
- Susceptible to infinite stuttering (crashing)

### `~>` (Leads-To)
`P ~> Q` means whenever P becomes true, Q will eventually be true.
```tla+
TaskCompletion == 
  \A t \in TaskType:
    t \in inbound ~> \E w \in Workers: t \in worker_pool[w]
```

**Properties:**
- Triggered every time P becomes true
- Temporal analog of implication (`=>`)

## Composed Operators

### `<>[]` (Eventually Always)
P eventually becomes true and stays true forever.
```tla+
Convergence == <>[](counter = NumThreads)  // Reaches and maintains target
```

### `[]<>` (Always Eventually) 
P becomes true infinitely often.
```tla+
Periodic == []<>(time = midnight)  // Midnight happens repeatedly
```

## The Stuttering Problem
TLA+ assumes systems can crash (infinite stuttering) at worst possible moment. Any behavior can insert infinite no-op steps.

**Why it matters:**
- Invariants unaffected (no state changes)
- Liveness properties can be violated by preventing good states
- Must explicitly prevent stuttering with fairness

## Fairness - Preventing Infinite Stuttering

### Weak Fairness
`fair process` = process cannot stop forever if it can always make progress.
```tla+
fair process orchestrator = "orchestrator"
```

### Strong Fairness  
`fair+ process` = process cannot stop forever if it can intermittently make progress.
```tla+
fair+ process thread \in Threads  // Prevents starvation
```

**Use Cases:**
- Weak: Process can always proceed → will eventually proceed
- Strong: Process can sometimes proceed → will eventually proceed
- Not all processes need fairness (e.g., user actions)

## Practical Considerations

### Performance & Debugging
- Liveness checking significantly slower than invariants
- Cannot use symmetry sets with liveness properties
- TLC reports "Temporal Properties Violated" without specifics
- Error traces may be longer than optimal

### Development Patterns
- Many invariants, few action properties, fewer liveness properties
- Liveness properties define "what we want to accomplish"
- Use separate models: large constants for safety, small for liveness

## Critical Gotchas
- `P` as property only checks initial state (not `[]P`)
- Stuttering can mask property violations
- `<>P` satisfied even if P becomes false later
- Strong vs weak fairness distinction crucial for lock contention
- Temporal properties are worst-case analysis (systems can always crash) 