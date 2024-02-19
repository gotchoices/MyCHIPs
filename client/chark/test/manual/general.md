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
|                   |                              |                                                |
|                   |                              |                                                |


