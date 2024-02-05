## Chit Transactions
    This test assumes that User-A and User-B have successfully established an open tally with each other.

- User-A request chit from User-B. User-B accepts chit.




| User-A Page          | User-A Action             | User-A Check                                           | User-B Page          | User-B Action                | User-B Check                                           |
| -------------------- | ------------------------- | ------------------------------------------------------ | -------------------- | ---------------------------- | ------------------------------------------------------ |
| Homepage             | Click on User-B           |                                                        | Homepage             |                              |                                                        |
|                      | Click request button      |                                                        |                      |                              |                                                        |
| Request Detail       |                           | User can switch from Chips to currency with arrow icon |                      |                              |                                                        |
|                      | Insert value and memo     |                                                        |                      |                              |                                                        |
|                      | Click Request button      |                                                        |                      |                              |                                                        |
|                      |                           | Success modal shows                                    |                      |                              | Notification of request shows                          |
|                      |                           | Notification of sent request                           |                      | Click notification           |                                                        |
|                      | Click Done                |                                                        | Chit details         |                              |                                                        |
| Homepage             |                           |                                                        |                      |                              | Displays the pending chit value                        |
|                      |                           | Pending chit display without refresh                   |                      |                              | Can switch between chits and currency                  |
|                      | Click on User-B           |                                                        |                      |                              | Is able to edit memo                                   |
|                      |                           | Pending chit button shows without refresh              |                      | Go to homepage               |                                                        |
|                      | Click pending chit button |                                                        | Homepage             |                              | Pending chit display without refresh                   |
| Pending Chits        |                           | Shows pending chit with all information                |                      | Click on User-A              |                                                        |
|                      | Click the pending chit    |                                                        |                      |                              | Pending chit button shows without refresh              |
| Pending Chit Details |                           | Displays the pending chit value                        |                      | Click on pending chit button |                                                        |
|                      |                           | Can switch between chips and currency                  | Pending Chits        |                              | Shows pending chit with accept and reject button       |
|                      |                           | Shows proper memo                                      |                      | Click the pending chit       |                                                        |
|                      |                           |                                                        | Pending Chit Details |                              | Displays the pending chit value                        |
|                      |                           |                                                        |                      |                              | Can switch between chits and currency                  |
|                      |                           |                                                        |                      |                              | Is able to edit memo                                   |
|                      |                           | Async payment received notification                    |                      | Click accept                 |                                                        |
|                      | Go to homepage            |                                                        | Pending Chits        |                              | Navigates to Pending Chit page                         |
| Homepage             |                           |                                                        |                      |                              | Async payment sent notification                        |
|                      |                           | Pending chit display is gone on User-B without refresh |                      |                              | Pending chit is gone                                   |
|                      |                           | Chit value updated without refresh                     |                      | Go to homepage               |                                                        |
|                      |                           |                                                        | Homepage             |                              |                                                        |
|                      |                           |                                                        |                      |                              | Pending chit display is gone on User-A without refresh |
|                      |                           |                                                        |                      |                              | Chit value updated without refresh                     |