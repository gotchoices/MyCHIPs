# Byzantine Attack Index

## By Severity

### Critical
Attacks that can potentially cause financial loss or permanent system inconsistency:
- [Split Vote Attack](split-vote.md) - Can cause inconsistent transaction state
- [Double-Commit Attack](double-commit.md) - Can lead to double-spending
- [Message Tampering](message-tampering.md) - Can corrupt transaction integrity
- [False Promise Attack](false-promise.md) - Can cause financial exposure

### High
Attacks that significantly disrupt system operation:
- [Deadbeat Attack](deadbeat.md) - Disrupts lift completion
- [Network Partition](network-partition.md) - Isolates segments of network
- [Selective Communication](selective-communication.md) - Creates information asymmetry
- [Delayed Vote Attack](delayed-vote.md) - Forces timeouts and retries

### Medium
Attacks that degrade system performance or reliability:
- [Signature Withholding](signature-withholding.md) - Delays transaction completion
- [Replay Attacks](replay-attacks.md) - Consumes system resources

## By Likelihood

### High Probability
Common failure modes or easy to execute:
- [Network Partition](network-partition.md) - Natural network failures
- [Deadbeat Attack](deadbeat.md) - Simple node failures/crashes
- [Delayed Vote Attack](delayed-vote.md) - Network latency/congestion

### Medium Probability
Requires some sophistication or coordination:
- [Signature Withholding](signature-withholding.md) - Intentional disruption
- [Selective Communication](selective-communication.md) - Modified software
- [Split Vote Attack](split-vote.md) - Malicious referee behavior

### Low Probability
Requires significant resources or expertise:
- [Message Tampering](message-tampering.md) - Cryptographic attacks
- [Double-Commit Attack](double-commit.md) - Complex coordination
- [Replay Attacks](replay-attacks.md) - Protocol manipulation
- [False Promise Attack](false-promise.md) - Complex timing attack

## By Lift Type Impact

### Linear Lifts Only
Attacks specifically targeting payment transactions:
- [False Promise Attack](false-promise.md) - Targets payment initiation

### Circular Lifts Only
Attacks specifically targeting credit clearing:
- None identified (all attacks affect both types or linear lifts)

### Both Types
Attacks affecting all lift transactions:
- [Deadbeat Attack](deadbeat.md)
- [Double-Commit Attack](double-commit.md)
- [Signature Withholding](signature-withholding.md)
- [Split Vote Attack](split-vote.md)
- [Delayed Vote Attack](delayed-vote.md)
- [Selective Communication](selective-communication.md)
- [Network Partition](network-partition.md)
- [Message Tampering](message-tampering.md)
- [Replay Attacks](replay-attacks.md)

## By Defense Status

### Well-Mitigated
Attacks with strong existing defenses:
- [Deadbeat Attack](deadbeat.md) - Protected by conditional commitments
- [Split Vote Attack](split-vote.md) - Protected by majority consensus
- [Message Tampering](message-tampering.md) - Protected by cryptographic signatures

### Partially Mitigated
Attacks with some existing defenses but potential improvements:
- [Network Partition](network-partition.md) - Has recovery mechanisms
- [Signature Withholding](signature-withholding.md) - Has timeout handling
- [Selective Communication](selective-communication.md) - Has redundant paths
- [Double-Commit Attack](double-commit.md) - Has transaction locking

### Needs Additional Research
Attacks requiring further defense development:
- [False Promise Attack](false-promise.md) - Needs better prevention
- [Delayed Vote Attack](delayed-vote.md) - Needs timing optimization
- [Replay Attacks](replay-attacks.md) - Needs protocol enhancement

## By Detection Difficulty

### Easy to Detect
Clear evidence immediately available:
- [Deadbeat Attack](deadbeat.md)
- [Network Partition](network-partition.md)
- [Delayed Vote Attack](delayed-vote.md)

### Moderate to Detect
Requires some analysis or correlation:
- [Split Vote Attack](split-vote.md)
- [Signature Withholding](signature-withholding.md)
- [Selective Communication](selective-communication.md)
- [Double-Commit Attack](double-commit.md)

### Hard to Detect
Requires sophisticated monitoring or analysis:
- [Message Tampering](message-tampering.md)
- [Replay Attacks](replay-attacks.md)
- [False Promise Attack](false-promise.md) 

## By Social Trust Barrier

### High Trust Barrier
Attacks requiring significant relationship establishment:
- [Double-Commit Attack](double-commit.md) - Multiple trading relationships
- [False Promise Attack](false-promise.md) - Credit history required
- [Deadbeat Attack](deadbeat.md) - Established partnerships needed

### Medium Trust Barrier
Attacks requiring limited relationship establishment:
- [Split Vote Attack](split-vote.md) - Referee relationships
- [Signature Withholding](signature-withholding.md) - Direct partnerships
- [Selective Communication](selective-communication.md) - Network presence

### Low Trust Barrier
Attacks possible without established relationships:
- [Network Partition](network-partition.md) - Network-level attack
- [Message Tampering](message-tampering.md) - Protocol-level attack
- [Replay Attacks](replay-attacks.md) - Technical attack
- [Delayed Vote Attack](delayed-vote.md) - Timing attack

## By Recovery Channel

### Social Recovery Primary
Attacks where social connections aid recovery:
- [Deadbeat Attack](deadbeat.md) - Direct partner contact
- [False Promise Attack](false-promise.md) - Community verification
- [Double-Commit Attack](double-commit.md) - Trading history

### Technical Recovery Primary
Attacks where technical measures drive recovery:
- [Network Partition](network-partition.md) - Network reconnection
- [Message Tampering](message-tampering.md) - Cryptographic validation
- [Replay Attacks](replay-attacks.md) - Protocol mechanisms

### Mixed Recovery
Attacks requiring both social and technical recovery:
- [Split Vote Attack](split-vote.md) - Referee consensus and communication
- [Delayed Vote Attack](delayed-vote.md) - Timing and coordination
- [Selective Communication](selective-communication.md) - Network and trust verification
- [Signature Withholding](signature-withholding.md) - Technical and social pressure 