# ChipNetBasic.tla - Formal Specification Documentation

## Overview

`ChipNetBasic.tla` is a TLA+ formal specification that models the ChipNet-based lift protocol, representing the latest evolution of the MyCHIPs credit clearing system. This specification is designed to formally verify that ChipNet's flexible consensus mechanisms maintain proven safety and liveness properties while adding Byzantine fault tolerance capabilities.

⚠️ **Current Status**: This specification is a foundational framework that **has not been tested** and **does not currently work due to syntax errors**. It requires debugging and completion before it can be used for formal verification.

## Historical Context and Protocol Evolution

### Protocol Evolution Timeline

The specification explicitly builds upon prior formal verification work, representing the third major iteration of MyCHIPs protocol development:

#### Phase 1: Original Protocol (2020) - DSR Analysis
- **Problem**: DSR Corporation's TLA+ analysis found fundamental safety vs. liveness tradeoffs
- **Key Finding**: "No clear way to assure both [safety and liveness] at the same time"
- **Result**: Protocol revision required due to identified issues
- **Historical Models**: `../dsr/phase-1/spec/` - Original lift mechanics and safety/liveness issues

#### Phase 2: Single Referee Protocol - BYU Analysis
- **Solution**: Introduction of single referee to resolve commit/rollback decisions
- **Verification**: Multi-tool validation using SPIN + Coq + TLA+
- **Result**: Verified safety and liveness properties for referee-based protocol
- **Historical Models**: `../byu/tla/` - Single referee consensus verification patterns

#### Phase 3: ChipNet Consensus Protocol (Current) - This Analysis
- **Evolution**: ChipNet enables flexible consensus mechanisms
- **Innovation**: Can devolve to single referee (backward compatibility) or use multiple external referees
- **New Challenges**: Byzantine fault tolerance, circuit starvation attacks, minority recovery
- **This Model**: Formal verification of the latest ChipNet-based protocol

## Primary Purpose: Model the Evolution of MyCHIPs Protocol

The specification serves as the **formal verification capstone** for the entire Byzantine analysis documented in the surrounding folders (`attacks/`, `scenarios/`, `alternatives/`). It provides mathematical validation for security claims made throughout the MyCHIPs Byzantine fault tolerance documentation.

### Core Design Goals

1. **Prove ChipNet doesn't break proven properties**
   - Ensure single-referee cases still work (backward compatibility with BYU results)
   - Validate that protocol evolution maintains established safety guarantees

2. **Validate Byzantine claims**
   - Verify that honest majority assumptions actually hold under attack scenarios
   - Quantify fault tolerance bounds mathematically

3. **Prove insurance chit protocol works**
   - Formal verification that minority recovery resolves circuit starvation attacks
   - Validate the [minority recovery protocol](../scenarios/minority-recovery-3.md) developed in Byzantine analysis

4. **Bridge theory and practice**
   - Provide formal backing for security claims made throughout documentation
   - Guide implementation by clearly specifying correctness requirements
   - Enable automated verification of proposed changes

## Key Features Modeled

### 1. Flexible Consensus Mechanisms

```tla
ConsensusMechanisms == {
    "SingleReferee",     \* Compatible with BYU single-referee analysis
    "MultiReferee",      \* Multiple external referees vote
    "ParticipantVote",   \* Lift participants vote directly
    "HybridConsensus"    \* Mix of referees and participants
}
```

**Purpose**: Models ChipNet's key innovation where participants can choose their consensus mechanism at runtime, enabling:
- **Backward compatibility** with proven single-referee protocol (BYU analysis)
- **Scalability** through multi-referee Byzantine fault tolerance
- **Flexibility** for different use cases and trust models

### 2. Byzantine Fault Tolerance

```tla
ByzantineNodes   \* Set of Byzantine (malicious) nodes ⊆ Nodes

HonestNode(node) == node \notin ByzantineNodes

HonestMajority(refereeSet) == 
    Cardinality({r \in refereeSet : HonestNode(r)}) > Cardinality(refereeSet) ÷ 2
```

**Purpose**: Unlike DSR/BYU models which assumed honest behavior, this explicitly models malicious actors and their impact on protocol correctness. This addresses the core question: "Can MyCHIPs actually handle Byzantine faults as claimed?"

**Key Properties to Verify**:
- System remains safe with minority Byzantine nodes
- Fault tolerance bounds are mathematically sound
- Honest majority assumptions are sufficient for correctness

### 3. Insurance Chit Protocol (Circuit Starvation Defense)

```tla
\* Request insurance chit to neutralize promised resources
\* NEW: Circuit starvation attack mitigation
RequestInsuranceChit(node, peer, liftId) ==
    /\ lifts[liftId].state = "Pend"  \* Lift is hung
    /\ HonestNode(node) /\ HonestNode(peer)  \* Both nodes are honest
    \* TODO: Add timeout condition - lift has been pending for too long
```

**Purpose**: Models the insurance chit protocol developed in the Byzantine analysis to defend against circuit starvation attacks. This addresses the scenario where a majority of nodes go offline after the Promise phase, leaving honest minority nodes with unresolvable promised resources.

**Innovation**: This is completely new compared to historical DSR/BYU models, representing a novel solution to a previously unaddressed attack vector.

### 4. Attack Resistance Validation

```tla
\* NEW: Circuit starvation attacks fail to permanently harm honest nodes
CircuitStarvationResistance ==
    \A liftId \in DOMAIN lifts :
        /\ lifts[liftId].state = "Pend"  \* Lift is hung
        /\ Cardinality(ByzantineNodes ∩ DOMAIN lifts[liftId].promises) > 
           Cardinality(Nodes \ ByzantineNodes ∩ DOMAIN lifts[liftId].promises)
        => \* Honest minority can recover via insurance chits
           <> \A honest \in (Nodes \ ByzantineNodes) :
               "CanContinueTrading"  \* TODO: Formalize trading capability
```

**Purpose**: Formally verify that the documented attacks in the `../attacks/` folder actually fail to cause permanent harm to honest participants.

## Integration with Historical Models

### Building on DSR Foundation

**Reused Components**:
- **Lift State Machine**: Basic `Seek → Pend → Good/Void` transitions
- **Tally Operations**: Balance and projected balance calculations  
- **Message Passing**: Distributed protocol communication patterns
- **Property Definitions**: Safety and liveness property structures

### Extending BYU Patterns

**Extended Components**:
- **Referee Interaction**: External decision authority modeling
- **Base Case Verification**: 2-entity lift protocols as building blocks
- **Consensus Verification**: Proven approaches for single-referee scenarios

### New ChipNet Capabilities

**Novel Components**:
- **Variable Referee Sets**: Dynamic consensus participant selection
- **Byzantine Fault Tolerance**: Malicious referee behavior modeling
- **Circuit Starvation**: Coordinated abandonment attack scenarios
- **Insurance Chit Protocol**: Minority recovery mechanism verification

## Expected Verification Properties

### Safety Properties (Must Always Hold)

```tla
\* No node loses credits inappropriately (from DSR safety analysis)
BalancePreservation == 
    \A n1, n2 \in Nodes : 
        tallies[n1][n2] + tallies[n2][n1] = 0  \* Symmetric credit relationships

\* Atomic commitment (extends DSR atomicity requirements)
AtomicCommitment == \A lift \in Lifts :
    (Committed(lift) => AllParticipantsCommitted(lift)) /\
    (Voided(lift) => AllParticipantsVoided(lift))

\* NEW: Insurance chits provide net zero effect
InsuranceNeutrality ==
    \A node \in Nodes, liftId \in DOMAIN lifts :
        \A chit \in nodeStates[node].insuranceChits :
            chit.liftId = liftId => 
                \* Insurance chit value cancels promised chit value
                "NetEffectZero"  \* TODO: Formalize the balance calculation
```

### Liveness Properties (Things That Eventually Happen)

```tla
\* All lifts eventually reach a final state (from BYU liveness analysis)
LiftProgression == 
    \A liftId \in DOMAIN lifts :
        lifts[liftId].state \in {"Seek", "Pend"} ~> 
        lifts[liftId].state \in {"Good", "Void", "Timeout"}

\* NEW: Insurance chits eventually enable trading
InsuranceChitEffectiveness == \A partition \in MinorityPartitions :
    <>(CanTrade(partition.honestNodes))
```

### Byzantine Fault Tolerance Properties

```tla
\* System remains safe with minority Byzantine nodes
ByzantineTolerance ==
    Cardinality(ByzantineNodes) < Cardinality(Nodes) ÷ 2 =>
        /\ BalancePreservation
        /\ LiftProgression
        /\ InsuranceNeutrality
```

## Architecture and Components

### Core Variables

- **`tallies`**: Node credit balances - `[nodeA][nodeB] → balance`
- **`lifts`**: Active lifts - `liftId → lift_record` 
- **`messages`**: Network messages in transit
- **`nodeStates`**: Per-node protocol state including insurance/resolution chits

### Message Types

Extends BYU referee interaction patterns with new ChipNet capabilities:

```tla
MessageTypes == {
    "LiftProposal",      \* Propose lift along route
    "LiftAccept",        \* Accept participation in lift
    "LiftReject",        \* Reject participation in lift
    "RefereePoll",       \* Poll referee for decision
    "RefereeDecision",   \* Referee commit/void decision
    "LiftCommit",        \* Propagate commit decision
    "LiftVoid",          \* Propagate void decision
    "InsuranceRequest",  \* Request insurance chit (NEW for ChipNet)
    "InsuranceGrant",    \* Grant insurance chit (NEW for ChipNet)
    "ResolutionRequest", \* Request resolution chit (NEW for ChipNet)
    "ResolutionGrant"    \* Grant resolution chit (NEW for ChipNet)
}
```

### Core Actions

1. **`ProposeLift`**: Builds on DSR lift proposal mechanics, adds ChipNet consensus selection
2. **`HandleLiftProposal`**: Extends BYU acceptance/rejection patterns with ChipNet considerations
3. **`RefereeDecision`**: Based on BYU referee patterns, extended for ChipNet multi-referee scenarios
4. **`RequestInsuranceChit`**: NEW - Circuit starvation attack mitigation
5. **`GrantInsuranceChit`**: NEW - Neutralize effect of promised resources

## Current Implementation Status

### ✅ Completed Components

- [x] **Basic protocol modeling** - Core lift mechanics defined
- [x] **Consensus mechanism framework** - Single/multi-referee support structure
- [x] **Insurance chit protocol outline** - Basic structure for minority recovery
- [x] **Byzantine node modeling** - Framework for malicious behavior
- [x] **Historical integration** - Building on DSR/BYU patterns

### ⚠️ Known Issues

- **Syntax Errors**: The specification currently has parsing errors and cannot be processed by SANY
- **Incomplete Formalization**: Several TODO items remain for full mathematical specification
- **Untested**: No model checking or validation has been performed

### 🔄 Requires Completion

- [ ] **Complete Byzantine behavior modeling** - Full malicious node action definitions
- [ ] **Detailed balance calculations** - Formal mathematics for insurance/resolution chits
- [ ] **Timeout handling** - Detection mechanisms for hung lifts
- [ ] **Network partition scenarios** - Complete modeling of communication failures
- [ ] **Race condition analysis** - Formal verification of insurance chit timing
- [ ] **Integration testing** - Validation against actual ChipNet implementation

## Verification Goals and Success Metrics

### Technical Validation Targets

- [ ] **All safety properties verified** for basic lift protocol
- [ ] **Race condition analysis complete** for insurance chit protocol  
- [ ] **Byzantine fault tolerance bounds quantified** mathematically
- [ ] **Attack resistance claims validated** for documented attacks in `../attacks/`

### Cross-Reference Validation

This specification directly validates claims made in:

1. **[Attack Analysis](../attacks/)**: Verify that documented attacks actually fail
2. **[Scenario Analysis](../scenarios/)**: Confirm minority recovery protocols work
3. **[Alternative Systems](../alternatives/)**: Validate comparative security claims
4. **[CONTEXT Analysis](../CONTEXT.md)**: Verify stated Byzantine fault tolerance bounds

### Historical Verification Continuity

5. **[DSR Analysis](../dsr/)**: Confirm that ChipNet resolves identified safety/liveness conflicts
6. **[BYU Analysis](../byu/)**: Verify that multi-referee consensus maintains single-referee properties

## Future Development Path

### Phase 1: Debug and Basic Verification
1. **Fix syntax errors** to enable SANY parsing
2. **Complete TODO sections** for basic functionality
3. **Verify type consistency** and basic property checking
4. **Test with simple scenarios** (2-3 nodes, single referee)

### Phase 2: Attack Scenario Modeling
1. **Circuit starvation attack modeling** - Detailed coordinated abandonment scenarios
2. **Network partition scenarios** - Communication failure and recovery
3. **Coordinated Byzantine attacks** - Multi-node malicious behavior
4. **Insurance chit race condition analysis** - Timing and consistency verification

### Phase 3: Advanced Properties and Integration
1. **Liveness under Byzantine conditions** - Progress guarantees with malicious actors
2. **Economic incentive modeling** - Game theory and rational behavior
3. **Performance and scalability analysis** - Large network behavior
4. **Integration testing** - Validation against actual ChipNet implementation

## Relationship to Broader MyCHIPs Analysis

This specification serves as the **mathematical foundation** for the entire Byzantine fault tolerance analysis documented in the surrounding folders:

- **`../attacks/`** - Each attack should be formally modeled and proven to fail
- **`../scenarios/`** - Each recovery scenario should be formally verified  
- **`../alternatives/`** - Comparative claims should be mathematically validated
- **`../CONTEXT.md`** - All Byzantine fault tolerance claims should have formal backing

## Conclusion

`ChipNetBasic.tla` represents an ambitious attempt to provide mathematical rigor to MyCHIPs' Byzantine fault tolerance claims. While currently non-functional due to syntax errors, it establishes a comprehensive framework for formal verification that builds systematically on the proven approaches from DSR and BYU analyses.

Once completed and debugged, this specification would provide **mathematical confidence** that:
- ChipNet's flexible consensus doesn't introduce new safety/liveness issues
- The insurance chit protocol actually prevents circuit starvation attacks  
- Byzantine fault tolerance claims are mathematically sound
- The system gracefully handles the transition from single-referee to multi-referee consensus

The specification embodies the evolution from a problematic original protocol → verified single-referee solution → flexible Byzantine-tolerant consensus system, with each step building on formally verified foundations. 