# User Story: Discovery-Driven Onboarding

## Story Overview

**As a** person who has heard about MyCHIPs through media/marketing  
**I want to** download and explore the app to understand what it offers  
**So that** I can decide if it's useful for my needs.

**Context**: Starting from limited knowledge, curious but cautious, understands that MyCHIPs is an alternative payment (i.e. money substitute) system based on peer-to-peer credit, but does not yet how to use the system.

## Sequence

*[Fill in the step-by-step sequence here]*

- User hears about system on a podast, is directed to mychips.org, sees link to download the app.
- User installs app on smartphone and launches it
- Several tasks need to be completed before he can use it for anything useful:
  - Input his identity information.  This is how he will identify himself to others he will tally with.  Name, email and cell number is important for most any potential partner. Some tally partners may ask for more, to possibly include birthdate, drivers license scan, SSN, proof of citizenship, and so forth.  But at this early onboarding phase, he is not given those details.  He can be prompted for more identifying information later if someone demands it.
  - Establish a signing key to be stored securely in the app and accessible only by providing a pass code, biometrics etc.  The user sees (perhaps via a context help) that this can be done now or later just before he tries to execute a tally with someone.
  - Figure out who to tally with.  He can't use MyCHIPs without tally partners.  This should be limited to relationships of pre-existing trust.  He should not tally with strangers and he should only extend credit trusted parties and limited to an amount appropriate to the other party's ability to pay.
- User can see that he has a zero balance (in CHIPs and his local currency) and no existing tally partners.
- He's not really sure what a CHIP is but there is a context help nearby it that takes him to an online resource where he can learn more.
- He can see and explore a basic menu bar that includes at least a Home screen, a QR scanner, and Preferences.
- The user has an option to visit a markeplace page on mychips.org where he can see vendors who are willing to form tallies with their customers (and/or accept CHIPs indirectly).  He won't really know the difference between tallying or lifting payments to these vendors yet.  But if he clicks on a vendor, he will be taken to a site with QR codes for payment and/or tallying with the vendor.  More will be explained as he explores this.
- User also sees an option to invite others he knows/trusts to tally with him.  This might be friends, family, neighbors, clients, vendors, etc.  
- He clicks it and is prompted with a brief warning about trust and who he should and should not tally with.  There is a context help to learn more detail about this.
- Clicking through, he is told that he will require signing key.  There is a link to learn more about what this means as well.  He follows it to an external resource that gives him the information he needs.
- He is presented with options to import an existing key or create a new one.
- He chooses to create a new one, which is immediately done.
- He is then prompted to export and save the key safely in case he loses his phone or deletes the app.  He is presented with Export Now and Skip.
- He chooses to Skip for now but remembers seeing "Key Management" in the preferences and so will remember to [backup his key](export-signing-key.md) later.
- He sees he is now in a tally review screen but decides to talk to a friend first and will [circle back](first-friend-tally.md) when he is ready to invite his friend to tally.
- This sets him on his journey to start making tallies with others.

## Acceptance Criteria

*[Human defines what success looks like for this journey]*

- [ ] App can be minimally configured (name, email, cell number) in under a minute
- [ ] App defaults to locale settings but user can infer from visual cues that customization settings are possible.
- [ ] User understands that he must execute tallies before further use will be possible.
- [ ] User understands that tallies must only represent/manage independently-existing trust--not be a source of trust.
- [ ] User knows how to use the app to start tallies with trusted partners
- [ ] User knows how to find commercial partners he may recognize who use MyCHIPs

---

## Scenarios

### Scenario 1: Successful Discovery and Setup
*[AI will fill in narrative with screen references]*

### Scenario 2: User Gets Confused and Needs Help
*[AI will fill in narrative with screen references]*

### Scenario 3: User Abandons During Setup
*[AI will fill in narrative with screen references]*

## Related Journeys

- [First Payment Experience](02-onboarding-payment-request.md)
- [Daily Usage Patterns](XX-daily-usage.md)
