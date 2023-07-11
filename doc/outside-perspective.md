# A place to record our original thorughts about how the system should work
# Before looking at how it actually works.



# What things do we expect to be able to do?
    1. Login/Create an account
    2. Make payments to friends
    3. Request payments from freinds
    4. Pay vendsors on the spot
    5. Setup QR codes (for a vendor) to request payment on the spot
    6. Initate a tally with a friend. 
    7. Account settings (changing email/password etc)

# First contact with MyCHIPs
## A few cases
1. A friend sent me a payment
    It takes us to a website that describes the payment and asks to create an account
        Log in with email/password or google or facebook or apple
    (In the future It will list any choices for providers but with only one available it just always uses MyCHIPs)
    Once you have an account you can click a button to "Get the App" it downloads the app and (usesing deep link) automatically connects the app with your account. 
        Alternative give the user a "login token" or "login code"
        Alternative login using the same email/password google etc
2. Found on the app store or online, curious
    (Don't have the deep link)
    Prompt them to Create an account (with option to sign in instead below)
        Same options email/password google etc
        This created account is not for app its for the service provider
        The app always logs in using the service provider
    
3. A vendor wanted to use it to receive payment
    Needs to be super fast.
    Vendor has a QR code to connect with them.
        Vendor has an app to genrate a QR code that creates a tally and a payment all at once. Scan the QR code on the app and a modal pops up (pay this guy?) and you confirm and its done.
            In the back end a tally is made a chit is created and consensused. 

# When generatig a Tally what happens?
    A couple of cases:
    1. User asks to make a tally directly
        # What does this look like?
            (A lot like Venmo. Search for folks, use QR code, options to pay and request)
        Makes 2 tallies for bi-directional transactions
        (Q: Do we really need 2 tallies? Can we send CHIPs backwards?)
        (Maybe show tallies all as if bi-directional. Lazily generate them as transactions need)
    2. Scanned a vendor QR code
        Makes a Foil Tally to make payment
    3. Someone sent us payment
        Makes a Stock Tally to make payment 
    

# When scanning a QR code to create a tally (option 1 above)
    Once it scans the tally is automatically generatated with default settings asking no questions. 
    A modal pops up that says "Initiate a tally with ${name}" with a big "Confirm" button
    with a smaller "details button" After opening details there is a "Reject Button" and also "hide details" 
    Details are editable. If you make an edit "Confirm" changes to "Counter offer"
        On a counter offer the other user gets a notification with the same modal (and a little warning saying the default terms have changed)
        If confirmed the tally is created and the modal dismisses. 
    After sending the tally request the pending request shows up in my list of tallies.
        When you tap it pulls up the same modal but "Confirm" is now "Resend" and "Counter offer" becomes "Change offer"

# When scanning a QR to make a payment
    The payment comes with tally terms. It pulls open the same modal except "Confirm" changes to "Pay" and we have details on the payment. 
        It creates a tally based on the vendors settings and adds the payment Chit.
        Vendor may also opt for linear lift:
            In this case no tally is made but the liner lift is searched for.
            If no lift can be found it has a loading indicator with "searching for payment route" and a "Canecl" button. 

# Do we want to show pending lifts?
    Linear lifts from a vendor should be shown. 
        The lift would show up on the tally screen (ish?) 
    Other lifts are opaque and not shown to the user.

# What is a Tally?
    It is a collection of Chits with additional meta data and settings 
    ## Settings
        Credit limit how many CHIPs will I accept from them before cutting them off?
        Debt limit how many CHIPs am I willing to give before stoping. 
        Lift target (I would like to keep a balance of 15 chips)
        Fee for lifts through this channel 
        Reward for lifts through this channel
    ## Meta Data
        #Contract details
        #Personal identifiers (email name, address, picture)
        # Stock or Foil:
            Stock is owed money
            Foil owes money 
            (in genral)
    # Consensus
        Foil decides the order of chits and what chits fit
        Uses hashes for both to confirm that their tally is the same


# Side use cases
    No lift is possible. Discovery failed. But we were really close. If you had a connection with X person it could go. 