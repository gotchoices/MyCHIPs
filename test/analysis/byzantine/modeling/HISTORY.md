# Historical Context and Protocol Evolution

MyCHIPs has undergone significant protocol evolution, each phase analyzed through formal verification. This historical context is essential for understanding the current ChipNet modeling effort.

## Phase 1: Original Protocol (2020) - DSR Analysis

**Location**: [`../dsr/`](../dsr/)  
**Company**: DSR Corporation  
**Problem Identified**: Fundamental **safety vs. liveness tradeoffs**

### Key Findings
- **Core Issue**: "No clear way to assure both [safety and liveness] at the same time"
- **Specific Problems**: 
  - Overlift conditions
  - Interlocking lifts
  - Originator blocking attacks
- **Tools Used**: TLA+ specifications with comprehensive model checking
- **Result**: Protocol revision required due to identified issues

### DSR's Problematic Pattern
```tla
\* DSR Issue: Originator could block lifts indefinitely
ProblematicPattern ==
    OriginatorSends("Promise") /\ OriginatorNeverSends("Commit" \/ "Timeout")
    => \* This could block all other lifts in the circuit
       □(OtherLiftsBlocked)
```

### Files and Documentation
- [`../dsr/phase-1/results.md`](../dsr/phase-1/results.md) - Detailed analysis results
- [`../dsr/phase-1/spec/`](../dsr/phase-1/spec/) - Original TLA+ specifications

## Phase 2: Single Referee Protocol - BYU Analysis

**Location**: [`../byu/`](../byu/)  
**Institution**: Brigham Young University  
**Solution**: Introduction of single referee to resolve commit/rollback decisions

### Verification Approach
Multi-tool validation strategy to ensure comprehensive coverage:

**SPIN Model Checking**:
- Verified safety/liveness properties for 2-entity base case
- Exhaustive state space exploration for small configurations
- Found no violations in referee-based protocol

**Coq Theorem Proving**:
- Machine-checked proofs for scalability to arbitrary entities  
- Inductive proofs showing 2-entity case generalizes
- Formal verification of conformance properties

**TLA+ Specifications**:
- Supplementary formal specifications
- Comparative analysis with DSR models
- Integration testing scenarios

### BYU's Solution Pattern
```tla
\* BYU Pattern: External referee resolves conflicts
RefereeDecision(referee, liftId, decision) ==
    /\ referee \in RefereeNodes
    /\ lifts[liftId].state = "Pend"
    => lifts'[liftId].state \in {"Good", "Void"}
```

### Results
- **Safety**: Verified balance preservation and credit conservation
- **Liveness**: Verified lift progression under referee decisions
- **Scalability**: Inductive proofs for arbitrary number of entities
- **Implementation Guidance**: Clear protocol specifications for developers

### Files and Documentation
- [`../byu/spin/`](../byu/spin/) - SPIN model checking specifications
- [`../byu/coq/`](../byu/coq/) - Coq proofs for conformance  
- [`../byu/tla/`](../byu/tla/) - TLA+ specifications
- [`../byu/README.md`](../byu/README.md) - Complete verification approach

## Phase 3: ChipNet Consensus Protocol (Current)

**Location**: `./` (this folder)  
**Evolution**: ChipNet enables **flexible consensus mechanisms**

### Key Innovations
- **Backward Compatibility**: Can devolve to single referee (preserves BYU results)
- **Multi-Referee Byzantine Tolerance**: Multiple external referees voting
- **Participant Consensus**: Nodes in the lift circuit can vote directly
- **Runtime Selection**: Participants choose consensus mechanism dynamically

### New Challenges Addressed
1. **Byzantine Fault Tolerance**: Variable referee sets with malicious actors
2. **Circuit Starvation Attacks**: [Detailed scenario analysis](../scenarios/circuit-starvation.md)
3. **Insurance Chit Recovery**: Minority recovery mechanism
4. **Economic Incentive Alignment**: Ensuring protocol stability

### ChipNet Extension Pattern
```tla
\* ChipNet Solution: Multiple consensus options
ConsensusMechanisms == {
    "SingleReferee",     \* DSR-compatible fallback
    "MultiReferee",      \* Byzantine fault tolerant
    "ParticipantVote"    \* Decentralized decision
}

\* ChipNet Extension: Byzantine-tolerant referee voting
ByzantineTolerance ==
    HonestMajority(refereeSet) =>
        \* Honest majority ensures correct decisions
        /\ BalancePreservation
        /\ LiftProgression
```

## Circuit Starvation Attack Context

### The Problem
The major new challenge addressed in ChipNet is the circuit starvation attack:

```tla
\* Attack: Majority of nodes go offline after Promise phase
CircuitStarvationAttack ==
    /\ lifts[liftId].state = "Pend"  \* Promises made
    /\ MajorityOffline(lifts[liftId].route)
    => \* Honest minority stuck with promised resources
       HonestMinorityCannotTrade
```

### The Solution: Insurance Chits
```tla
\* Insurance chits neutralize promised resources
InsuranceNeutrality ==
    \* Insurance chit cancels out promised chit effect
    PromisedChitValue + InsuranceChitValue = 0
    => HonestNodesCanContinueTrading
```

## Integration with Current Modeling

### Lessons Applied
1. **From DSR**: Avoid patterns that allow indefinite blocking
2. **From BYU**: Maintain referee-based fallback for proven safety/liveness
3. **From Attack Analysis**: Model circuit starvation explicitly

### Verification Strategy
- **Incremental Complexity**: Start with simple models, build systematically
- **Multi-Tool Approach**: Follow BYU's comprehensive verification methodology
- **Historical Compatibility**: Ensure new models can reproduce historical findings
- **Attack-Focused**: Explicitly model and defend against identified attacks

### Comparative Goals
- **vs DSR**: Solve safety/liveness tradeoffs with flexible consensus
- **vs BYU**: Extend single-referee proven properties to multi-referee Byzantine tolerance
- **vs Current**: Validate insurance chit recovery mechanism formally

This historical progression shows how each formal verification effort built upon previous findings, leading to the current comprehensive ChipNet modeling challenge. 