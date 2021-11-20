## Bugs and Problems

This file is for tracking identified, unsolved problems with the general 
security related to the Tally and Lift architecture.  It is not intended for 
program bugs that can be solved with better coding.

### Crooked Admin / Hacked Host
(Feb 2021)

In this scenario, a site admin has set out to defraud one of his own users.  He
could modify the server software to earn extra CHIPs he is not entitled to.

To accomplish it, he needs to position himself (his own user account) at the 
upstream end of a segment which will participate in a lift.  His victim is 
somewhere downstream, perhaps at or near the bottom end of the segment.

Once a lift has been agreed to with external sites, it is the server's job to
commit a set of lift chits according to the trading parameters the individual
users have agreed to and signed in their tallies.  But what if he changes the
lift for the victim so the victim trades at an unauthorized margin?

For example, the incoming lift could be for 10 CHIPs.  He can commit 10 CHIPs
coming into the victim's Stock, but commit leaving the victim's Foil.  The 20
CHIPs then propagate along the segment, eventually arriving at the crook's own
user account where he receives 20 CHIPs and only passes 10 chips back along to
the next system.

To the outside world, this will appear normal as all the fraud has occurred
completely inside the bounds of the crook's system.

This would be detectable only to the victim who would be left with a tally
somewhere containing a lift chit that is in violation of his signed trading
parameters.  The fraud would be clearly demonstrable and would likely be a
violation of the subscription agreement signed by the victim and his site
administrator.  By interjecting his own user in the lift chain, the admin
has also broken the tally trading agreement with his immediate partners.
But such a problem might go on for a time without being noticed--especially if 
it were done on a very small scale.

Note: Doing this kind of thing (finding arbitrage pathways) that are in 
harmony with one's users' trading parameters should not be a problem at all.  
In fact it may be a very good way for service providers to make a profit 
without having to charge their users an explicit fee.  But if the authorized
trading parameters are not honored, it is clearly a fraud.

One solution is to have the user's mobile app periodically monitoring the
integrity of all lifts.  This works fine unless your app happens to be a web
app downloaded from your service provider.  Then he can just as well hack that
too to further obscure the fraud from your notice.

This underlies the need for an eventual completely native app that is obtained
from a reputable source, not affiliated with your service provider.  That gives
a check to the integrity of your provider.

Currently the user app connects to the service provider via a web socket.  That
implies it must connect only to the same site that provided the app.

This same fraud could conceivably be executed by a user who hacks into the
system of his provider.  Then, the provider is not the bad guy--just not as
competetent as we would like.  The upside: the tallies tell the story of
exactly what happened, who won and who lost.  Perhaps with judicious crafting
of the EULA, and adequate system logging, enough evidence can be produced to
clearly identify the cheater.

<br>[Back to Index](README.md#contents)
