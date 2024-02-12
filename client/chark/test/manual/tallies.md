## Tallies
    This is a tally creation test between two users who. User-A and User-B are unassociated with each other from the start.

| User-A Page   | User-A Action                           | User-A Check                                  | User-B Page           | User-B Action              | User-B Check                                    |
| ------------- | --------------------------------------- | --------------------------------------------- | --------------------- | -------------------------- | ----------------------------------------------- |
| Homepage      | Click on Handshake Icon                 |                                               | Homepage              |                            |                                                 |
| Working Tally | Click plus button                       |                                               |                       |                            |                                                 |
|               |                                         | Show new tally modal                          |                       |                            |                                                 |
|               | Insert comment and choose stock or foil |                                               |                       |                            |                                                 |
|               | Click next                              |                                               |                       |                            |                                                 |
|               | Insert tally limit                      |                                               |                       |                            |                                                 |
|               | Click next                              |                                               |                       |                            |                                                 |
|               |                                         | Show success modal                            |                       |                            |                                                 |
|               | Click done                              |                                               |                       |                            |                                                 |
|               |                                         | Draft tally was created with comments showing |                       |                            |                                                 |
|               | Click on newly created draft tally      |                                               |                       |                            |                                                 |
| Tally Preview |                                         |                                               |                       |                            |                                                 |
|               |                                         | Correct assignment of stock or foil           |                       |                            |                                                 |
|               |                                         | Can switch stock and foil using arrow icon    |                       |                            |                                                 |
|               |                                         | Can update certificate information            |                       |                            |                                                 |
|               |                                         | Can view contract pdf by clicking on eye icon |                       |                            |                                                 |
|               |                                         | Can update limit                              |                       |                            |                                                 |
|               | Click share button                      |                                               |                       |                            |                                                 |
| Share Tally   |                                         |                                               |                       |                            |                                                 |
|               |                                         | Can switch between QR code and link           |                       |                            |                                                 |
|               |                                         | Check that QR code and link share work        |                       |                            |                                                 |
|               | Share to User-B                         |                                               |                       | Click scan icon            |                                                 |
|               |                                         |                                               | Camera                |                            |                                                 |
|               |                                         |                                               |                       | Scan QR code               |                                                 |
|               |                                         |                                               | Tally request modal   |                            |                                                 |
|               |                                         |                                               |                       |                            | Correct information from user-A                 |
|               |                                         |                                               |                       | Click start                |                                                 |
|               |                                         |                                               | Cert options          |                            |                                                 |
|               |                                         |                                               |                       | Click custom               |                                                 |
|               |                                         |                                               | My Custom Certificate |                            |                                                 |
|               |                                         |                                               |                       |                            | Can toggle certificate options                  |
|               |                                         |                                               |                       | Click send certificate     |                                                 |
|               |                                         | Gets notification of selected certificate     | Working Tally         |                            |                                                 |
|               |                                         |                                               |                       |                            | new draft tally created without refresh         |
|               |                                         |                                               |                       |                            | draft tally icon is grey hourglass              |
|               | Click handshake menu                    |                                               |                       |                            |                                                 |
| Working Tally |                                         |                                               |                       |                            |                                                 |
|               | Click User-B draft tally                |                                               |                       |                            |                                                 |
| Tally Preview |                                         |                                               |                       |                            |                                                 |
|               | Click 'review'                          | Check information is correct                  |                       |                            |                                                 |
|               |                                         | Check ability to modify information           |                       |                            |                                                 |
|               | Click 'offer'                           |                                               |                       |                            |                                                 |
|               |                                         | Success modal                                 |                       |                            | Gets notification of offer                      |
|               | Click 'homepage'                        |                                               |                       |                            | draft tally icon is now red '!' without refresh |
| Homepage      |                                         |                                               |                       | Click homescreen           |                                                 |
|               |                                         |                                               | Homepage              |                            |                                                 |
|               |                                         |                                               | Activity              | Click activity 'bell' icon |                                                 |
|               |                                         |                                               |                       |                            | Tally notification is there at the top          |
|               |                                         |                                               |                       |                            | Options to reject or accept                     |
|               |                                         |                                               |                       | Click accept               |                                                 |
|               |                                         | Tally accepted notification                   |                       |                            | Success notification                            |
|               |                                         | New tally is created without refresh          |                       |                            | Tally goes away                                 |
|               |                                         | New tally is at top of homepage               |                       | Back                       |                                                 |
|               |                                         |                                               | Homepage              |                            |                                                 |
|               |                                         |                                               |                       |                            | New tally is created without refresh            |
|               |                                         |                                               |                       |                            | New tally is at top of homepage                 |




## Tally Preview Page [Open Tally]


| Page              | Action                       | Check                                                                            |
| ----------------- | ---------------------------- | -------------------------------------------------------------------------------- |
| Homepage          | Click on open tally          |                                                                                  |
|                   | Click View Tally             |                                                                                  |
| Tally Preview     |                              | Foil and stock are on the right user                                             |
|                   |                              | Limit for stock and foil are correct                                             |
|                   |                              | Cannot edit limit for stock and foil                                             |
|                   |                              | Can view pdf version of contract                                                 |
|                   |                              | Cannot edit contract                                                             |
|                   |                              | Can view my certificate information                                              |
|                   |                              | Can view partners certificate information                                        |
|                   |                              | Shows comments (if any)                                                          |
|                   |                              | All tool tips work (blue question marks)                                         |
|                   | Click show trading variables |                                                                                  |
| Trading variables |                              | Can view trading variables                                                       |
|                   |                              | Can update trading variables                                                     |
|                   | Go back                      |                                                                                  |
| Tally Preview     |                              |                                                                                  |
|                   | Click chit history           |                                                                                  |
| Chit history      |                              | Chit history is shown in order of most recent transaction                        |
|                   |                              | Accurate chit history numbers                                                    |
|                   |                              | Aligns with the figma design                                                     |
|                   | Click chit                   |                                                                                  |
| Chit details page |                              | Show chit details: date, uuid, signature, net, reference, memo, status, state... |
|                   | Go back                      |                                                                                  |
| Chit history      |                              |                                                                                  |
|                   | Go back                      |                                                                                  |
| Tally Preview     |                              |                                                                                  |
|                   | Click pay                    |                                                                                  |
| Payment Details   |                              | Can change value                                                                 |
|                   |                              | Can switch currency                                                              |
|                   |                              | Can edit memo                                                                    |
|                   | Go back                      |                                                                                  |
| Payment Details   |                              |                                                                                  |
|                   | Click request                |                                                                                  |
|                   |                              | Can change value                                                                 |
|                   |                              | Can switch currency                                                              |
|                   |                              | Can edit memo                                                                    |


## Tally Preview Page [Draft Tally]

| Page            | Action                                           | Check                                                                     |
| --------------- | ------------------------------------------------ | ------------------------------------------------------------------------- |
| Working Tallies | Click draft tally                                |                                                                           |
|                 |                                                  | Draft tallies are ordered by date created                                 |
| Tally Preview   |                                                  | Foil and stock are on the right user                                      |
|                 |                                                  | Limit for stock and foil are correct                                      |
|                 |                                                  | Can edit limit for stock and foil                                         |
|                 |                                                  | Can view pdf version of contract                                          |
|                 |                                                  | Can edit contract                                                         |
|                 |                                                  | Can view my certificate information                                       |
|                 |                                                  | Can edit certificate information                                          |
|                 |                                                  | Can edit comments                                                         |
|                 |                                                  | All tool tips work (blue question marks)                                  |
|                 | Edit draft tally                                 |                                                                           |
|                 |                                                  | Bottom right share icon changes to check                                  |
|                 | Click check icon                                 |                                                                           |
|                 |                                                  | Bottom right icon changes from check to share                             |
|                 | Go back                                          |                                                                           |
| Working Tally   |                                                  | Draft tallies are still ordered by date created (Order should not change) |
|                 | Click on same draft tally                        |                                                                           |
|                 |                                                  | Saved changes are still there                                             |
|                 | Repeat edit/save sequence for all editable items |                                                                           |
