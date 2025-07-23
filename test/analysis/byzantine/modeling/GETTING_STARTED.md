# Getting Started with MyCHIPs Formal Verification

## Prerequisites

### TLA+ Installation
1. **Download TLA+ Toolbox**: [Official Download](https://lamport.azurewebsites.net/tla/toolbox.html)
2. **Alternative: VS Code Extension**: Search for "TLA+" in VS Code extensions
3. **Command Line Tools**: Optional but recommended for automation

### Historical Context Review
Before working with the models in this folder, familiarize yourself with the evolution:

1. **Read DSR Analysis Results**: [`../../dsr/phase-1/results.md`](../../dsr/phase-1/results.md)
   - Understand why the original protocol failed safety/liveness requirements
   - Review the specific issues identified (overlift, interlocking lifts, etc.)

2. **Study BYU Verification Approach**: [`../../byu/README.md`](../../byu/README.md)
   - See how single-referee protocol resolved DSR issues
   - Understand the multi-tool verification strategy (SPIN + Coq + TLA+)

## Model Overview

### ChipNetBasic.tla

This is the foundational specification for the current ChipNet-based protocol. It builds upon lessons learned from DSR and BYU analyses:

```
ChipNetBasic.tla          # Main specification
├── Type Definitions      # Lift states, message types, consensus mechanisms
├── Core Actions         # Lift proposal, handling, referee decisions
├── Insurance Protocol   # NEW: Circuit starvation mitigation
├── Safety Properties    # Balance preservation, lift progression
└── Byzantine Tolerance  # NEW: Multi-party fault tolerance
```

**Key Innovations over Historical Models**:
- **Flexible Consensus**: Single referee → Multiple referees/participants
- **Insurance Chits**: Circuit starvation attack mitigation
- **Byzantine Modeling**: Explicit malicious node behavior

## Quick Start

### 1. Open in TLA+ Toolbox

```bash
# Clone and navigate to the modeling directory
cd mychips/test/analysis/byzantine/modeling/tla+

# Open TLA+ Toolbox and import ChipNetBasic.tla
```

### 2. Create and Run a Model

1. **Create Model**: In TLA+ Toolbox, right-click `ChipNetBasic.tla` → "New Model"
2. **Load Configuration**: Import settings from `ChipNetBasic.cfg`
3. **Run Model Checker**: Click "Run TLC" to verify properties

### 3. Expected Results

**Successful Verification Should Show**:
- ✅ `TypeInvariant` - All variables maintain correct types
- ✅ `BalancePreservation` - No node loses credits inappropriately
- ✅ `LiftProgression` - All lifts eventually complete
- ✅ `ByzantineTolerance` - System handles minority Byzantine nodes

**If Verification Fails**:
- Review error traces to understand counterexamples
- Check if Byzantine node count exceeds minority threshold
- Ensure all message handling is complete

## Historical Model Comparison

### What We Learned from DSR (2020)

**DSR Found**: Original protocol couldn't guarantee both safety and liveness
```tla
\* DSR Issue: Originator could block lifts indefinitely
ProblematicPattern ==
    OriginatorSends("Promise") /\ OriginatorNeverSends("Commit" \/ "Timeout")
    => \* This could block all other lifts in the circuit
       □(OtherLiftsBlocked)
```

**Our Solution**: ChipNet allows participants to choose consensus mechanisms
```tla
\* ChipNet Solution: Multiple consensus options
ConsensusMechanisms == {
    "SingleReferee",     \* DSR-compatible fallback
    "MultiReferee",      \* Byzantine fault tolerant
    "ParticipantVote"    \* Decentralized decision
}
```

### What We Learned from BYU

**BYU Verified**: Single referee protocol works for 2-entity case with inductive scaling
```tla
\* BYU Pattern: External referee resolves conflicts
RefereeDecision(referee, liftId, decision) ==
    /\ referee \in RefereeNodes
    /\ lifts[liftId].state = "Pend"
    => lifts'[liftId].state \in {"Good", "Void"}
```

**Our Extension**: Multi-referee Byzantine fault tolerance
```tla
\* ChipNet Extension: Byzantine-tolerant referee voting
ByzantineTolerance ==
    HonestMajority(refereeSet) =>
        \* Honest majority ensures correct decisions
        /\ BalancePreservation
        /\ LiftProgression
```

## Understanding the Insurance Chit Protocol

The major innovation in this specification is modeling the Insurance Chit Protocol for circuit starvation attacks:

### Problem: Circuit Starvation
```tla
\* Attack: Majority of nodes go offline after Promise phase
CircuitStarvationAttack ==
    /\ lifts[liftId].state = "Pend"  \* Promises made
    /\ MajorityOffline(lifts[liftId].route)
    => \* Honest minority stuck with promised resources
       HonestMinorityCannotTrade
```

### Solution: Insurance Chits
```tla
\* Insurance chits neutralize promised resources
InsuranceNeutrality ==
    \* Insurance chit cancels out promised chit effect
    PromisedChitValue + InsuranceChitValue = 0
    => HonestNodesCanContinueTrading
```

## Model Development Progression

### Phase 1: Basic Verification (Current)
- [x] Basic lift protocol modeling
- [x] Single/multi-referee consensus
- [x] Insurance chit protocol outline
- [ ] Complete Byzantine behavior modeling

### Phase 2: Attack Scenarios
- [ ] Circuit starvation attack modeling
- [ ] Network partition scenarios  
- [ ] Coordinated Byzantine attacks
- [ ] Insurance chit race condition analysis

### Phase 3: Advanced Properties
- [ ] Liveness under Byzantine conditions
- [ ] Economic incentive modeling
- [ ] Performance and scalability analysis
- [ ] Integration with ChipNet route discovery

## Running Existing Historical Models

### DSR Models
```bash
cd ../../dsr/phase-1/spec/
# Follow DSR documentation to run their TLA+ specifications
# Compare results with our ChipNet models
```

### BYU Models
```bash
cd ../../byu/
# Run the complete verification suite
./verifyMyCHIPs.sh

# Individual tool verification:
cd spin/ && ./verifyMinimalModel.sh    # SPIN model checking
cd coq/  && make verify                # Coq proofs
cd tla/  && # TLA+ specifications
```

## Contributing to the Models

### Before Adding New Features
1. **Review historical models** for similar patterns
2. **Check Byzantine analysis** for relevant attack scenarios
3. **Consider backward compatibility** with single-referee protocol

### Adding New Properties
```tla
\* Template for new safety property
NewSafetyProperty ==
    \A lift \in Lifts :
        Precondition(lift) => AlwaysTrue(lift)

\* Template for new liveness property  
NewLivenessProperty ==
    \A lift \in Lifts :
        Precondition(lift) ~> EventuallyTrue(lift)
```

### Testing Additions
1. **Start small**: Test with 2-3 nodes first
2. **Add incrementally**: One new feature at a time
3. **Compare with BYU**: Ensure single-referee cases still work
4. **Verify Byzantine tolerance**: Test with minority malicious nodes

## Troubleshooting

### Common TLA+ Issues
- **State space explosion**: Reduce constants in `.cfg` file
- **Property violations**: Check if Byzantine assumptions hold
- **Deadlocks**: Ensure fairness conditions are sufficient

### Model Checking Performance
- **Use symmetry**: Enable `Permutations(Nodes)` 
- **Limit state space**: Constrain message queues and lift counts
- **Progressive verification**: Start simple, add complexity gradually

### Integration Questions
- **DSR compatibility**: Can the model reproduce DSR's identified issues?
- **BYU consistency**: Do single-referee scenarios match BYU results?
- **ChipNet extensions**: Do new features preserve proven properties?

## Next Steps

1. **Complete ChipNetBasic.tla**: Fill in TODO sections
2. **Create circuit starvation model**: Dedicated specification for this attack
3. **Develop minority recovery model**: Detailed insurance chit protocol
4. **Build Byzantine attack suite**: Comprehensive malicious behavior modeling
5. **Integration testing**: Combine with actual ChipNet implementation testing

**Bottom Line**: This formal verification effort builds systematically on the strong foundation provided by DSR and BYU analyses, extending their proven approaches to handle the new challenges and capabilities of the ChipNet-based protocol. 