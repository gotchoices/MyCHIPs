# General Test Suite

### Homepage
| Page     | Action                                    | Check                                                  |
| -------- | ----------------------------------------- | ------------------------------------------------------ |
| Homepage |                                           | Shows correct profile picture                          |
|          |                                           | Username is correct                                    |
|          |                                           | Total chip value and currnecy value is correct         |
|          |                                           | Open tallies are ordered by date established           |
|          |                                           | You can search open tally users by name                |
|          |                                           | Pending total chit value is correct                    |
|          |                                           | Individual pending chit value is correct               |
|          |                                           | Activity icon red dot shows with new notification      |
|          | Click graph menu icon (upper left corner) |                                                        |
|          |                                           | Homepage changes to graph view                         |
|          | Click list icon view                      |                                                        |
|          |                                           | Homepage changes to list view                          |
|          | Click activity icon                       |                                                        |
| Activity |                                           |                                                        |
|          |                                           | Shows user transaction history                         |
|          |                                           | Transaction history shown                              |
|          |                                           | Transaction history is ordered from newest to oldest   |
|          |                                           | Tally negotiation notifications show here              |
|          |                                           | Pending chit notifications show here                   |
|          | Back button                               |                                                        |
| Homepage |                                           |                                                        |
|          | Click open tally                          |                                                        |
|          |                                           | Modal shows with options 'View Taly', 'Pay', 'Request' |
|          |                                           | Pending chit button shows with pending chits           |
|          | Click filter button                       |                                                        |
| Filters  |                                           |                                                        |
|          |                                           | Default filter is most recent                          |
|          |                                           | When switching filters only, only one on at a time     |
|          |                                           | Filters are correct                                    |



### Payment from open tally

| Page     | Action                   | Check                                            |
| -------- | ------------------------ | ------------------------------------------------ |
| Payment  |                          | Input defaults to Chips                          |
|          |                          | Shows currency amount under Chips                |
|          |                          | Chip defualt amount '0.000'                      |
|          |                          | Currency default amount '0.00'                   |
|          | Click into Chip amount   |                                                  |
|          |                          | Make sure all numbers are showing at all times   |
|          | Type '123'               | Chip input = '123.000'                           |
|          | Clear; Type '123.12      | Chip input = '123.120'                           |
|          | Clear; Type '123.123123' | Chip input = '123.123                            |
|          | Clear; Type '123.....'   | Chip input = '123.000'                           |
|          | Click arrow switch icon  |                                                  |
|          | Clear; Type '123'        | Currnecy input = '123.00'                        |
|          | Clear; Type '123.12'     | Currency input = '123.12'                        |
|          | Clear; Type '123.123123' | Currnecy input = '123.12'                        |
|          | Clear; Type '123.....'   | Currency input = '123.00'                        |
|          | Clear;                   |                                                  |
|          | Click pay with no inputs |                                                  |
|          |                          | Show error that inputs are required              |
|          | Fill in input and memo   |                                                  |
|          | Click Pay                |                                                  |
|          |                          | Payment success modal shows                      |
|          | Back to homepage         |                                                  |
| Homepage |                          |                                                  |
|          |                          | Chip value updated on open tally without refresh |

### Request from open tally

| Page     | Action                       | Check                                            |
| -------- | ---------------------------- | ------------------------------------------------ |
| Request  |                              | Input defaults to Chips                          |
|          |                              | Shows currency amount under Chips                |
|          |                              | Chip defualt amount '0.000'                      |
|          |                              | Currency default amount '0.00'                   |
|          | Click into Chip amount       |                                                  |
|          |                              | Make sure all numbers are showing at all times   |
|          | Type '123'                   | Chip input = '123.000'                           |
|          | Clear; Type '123.12          | Chip input = '123.120'                           |
|          | Clear; Type '123.123123'     | Chip input = '123.123                            |
|          | Clear; Type '123.....'       | Chip input = '123.000'                           |
|          | Click arrow switch icon      |                                                  |
|          | Clear; Type '123'            | Currnecy input = '123.00'                        |
|          | Clear; Type '123.12'         | Currency input = '123.12'                        |
|          | Clear; Type '123.123123'     | Currnecy input = '123.12'                        |
|          | Clear; Type '123.....'       | Currency input = '123.00'                        |
|          | Clear;                       |                                                  |
|          | Click Request with no inputs |                                                  |
|          |                              | Show error that inputs are required              |
|          | Fill in input and memo       |                                                  |
|          | Click Request                |                                                  |
|          |                              | Payment success modal shows                      |
|          | Back to homepage             |                                                  |
| Homepage |                              |                                                  |
|          |                              | Chip value updated on open tally without refresh |

### Request from request page

| Page              | Action                       | Check                                          |
| ----------------- | ---------------------------- | ---------------------------------------------- |
| Request           |                              | Input defaults to Chips                        |
|                   |                              | Shows currency amount under Chips              |
|                   |                              | Chip defualt amount '0.000'                    |
|                   |                              | Currency default amount '0.00'                 |
|                   | Click into Chip amount       |                                                |
|                   |                              | Make sure all numbers are showing at all times |
|                   | Type '123'                   | Chip input = '123.000'                         |
|                   | Clear; Type '123.12          | Chip input = '123.120'                         |
|                   | Clear; Type '123.123123'     | Chip input = '123.123                          |
|                   | Clear; Type '123.....'       | Chip input = '123.000'                         |
|                   | Click arrow switch icon      |                                                |
|                   | Clear; Type '123'            | Currnecy input = '123.00'                      |
|                   | Clear; Type '123.12'         | Currency input = '123.12'                      |
|                   | Clear; Type '123.123123'     | Currnecy input = '123.12'                      |
|                   | Clear; Type '123.....'       | Currency input = '123.00'                      |
|                   | Clear;                       |                                                |
|                   | Click Request with no inputs |                                                |
|                   |                              | Show error that inputs are required            |
|                   | Fill in input and memo       |                                                |
|                   | Click Request                |                                                |
| Request link page |                              |                                                |
|                   |                              | Show QR code                                   |
|                   |                              | Able to share QR code                          |
|                   | Click link tab               |                                                |
|                   |                              | Show link                                      |
|                   |                              | Able to share link                             |

### Working Tally Page


| Page          | Action                             | Check                                 |
| ------------- | ---------------------------------- | ------------------------------------- |
| Working Tally |                                    |                                       |
|               | Click the plus icon                |                                       |
|               |                                    | New tally modal                       |
|               |                                    | Check comments input                  |
|               |                                    | Check stock and foil input            |
|               | Fill comments and foil icon        |                                       |
|               | Click submit                       |                                       |
|               |                                    | Limit input in modal                  |
|               |                                    | Limit input can only input numbers    |
|               | Input numbers                      |                                       |
|               | Click submit                       |                                       |
|               |                                    | Draft tally got created               |
|               | Click on draft tally               |                                       |
|               |                                    | Your limit is set                     |
|               |                                    | Share icon in bottom left shows       |
|               | Share without filling out limit    |                                       |
|               |                                    | Error shows: fill out required fields |
|               | Input partner limit                |                                       |
|               | Click share button on bottom right |                                       |
| Share page    |                                    |                                       |
|               |                                    | Can share with QR code                |
|               |                                    | Can share with link                   |



### Key managaement
| Page           | Action                         | Check                                        |
| -------------- | ------------------------------ | -------------------------------------------- |
| Key Management |                                |                                              |
|                | click generate button          |                                              |
|                |                                | modal pops up explaining action              |
|                | click 'I understand'           |                                              |
|                |                                | modal with passphrases                       |
|                |                                | wording and buttons are same as figma        |
|                | click 'export'                 |                                              |
|                |                                | error saying you need to fill out passphrase |
|                | enter in different passphrases |                                              |
|                | click 'export'                 |                                              |
|                |                                | error saying passphrases don't match         |
|                | enter in same passphrases      |                                              |
|                | click 'export'                 |                                              |
|                |                                | export modal shows                           |
|                |                                | make sure you're able to save the key        |
|                | Go back to key management page |                                              |
|                | click 'export' button          |                                              |
|                |                                | modal pops up with passphrases               |
|                |                                | modal with passphrases                       |
|                |                                | wording and buttons are same as figma        |
|                | click 'export'                 |                                              |
|                |                                | error saying you need to fill out passphrase |
|                | enter in different passphrases |                                              |
|                | click 'export'                 |                                              |
|                |                                | error saying passphrases don't match         |
|                | enter in same passphrases      |                                              |
|                | click 'export'                 |                                              |
|                |                                | export modal shows                           |
|                |                                | make sure you're able to save the key        |
|                | Go back to key management page |                                              |
|                | click import button            |                                              |
|                |                                | modal pops up explaining action              |
|                | click 'I understand'           |                                              |
|                |                                | modal with passphrases                       |
|                |                                | wording and buttons are same as figma        |
|                | click 'export'                 |                                              |
|                |                                | error saying you need to fill out passphrase |
|                | enter in different passphrases |                                              |
|                | click 'export'                 |                                              |
|                |                                | error saying passphrases don't match         |
|                | enter in same passphrases      |                                              |
|                | click 'export'                 |                                              |
|                |                                | export modal shows                           |
|                | click 'import key'             |                                              |
|                |                                | native file upload                           |
|                | Upload a saved key             |                                              |


### Activity Page

| Page        | Action                         | Check                                                      |
| ----------- | ------------------------------ | ---------------------------------------------------------- |
| Activity    |                                | Show list of transactions that the user has made           |
|             |                                | Profile picture is loading for trasaction                  |
|             |                                | The transaction amount is correct                          |
|             |                                | Time each transaction was made is correct                  |
|             |                                | Each item is ordered by most recent                        |
|             | Click on a chit transaction    |                                                            |
| Chit Detail |                                | Show chit details                                          |
|             | Back                           |                                                            |
| Activity    |                                |                                                            |
|             | Send Chit request to this user |                                                            |
|             |                                | Chit request shows above all transactions                  |
|             | Send tally negotiation request |                                                            |
|             |                                | Tally negotiation request shows above all transactions     |
|             | Back                           |                                                            |
| Home        |                                |                                                            |
|             |                                | Red dot on bell icon shows when active notifications       |
|             | Click on bell icon             |                                                            |
| Activity    |                                |                                                            |
|             | Complete chit request          |                                                            |
|             |                                | Show chit request native notification                      |
|             |                                | Chit request is removed from activity page without refresh |
|             | Refresh activity page          |                                                            |
|             |                                | Completed chit request shows as most recent transaction    |