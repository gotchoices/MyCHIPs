## Testing the Server
- Now we will add some sample test data to the database:
  Edit the settings file to set IP number of the test machine your database is
  on, and then run the kickstart file.
```  
    cd test
    vi settings.js
    cd sample
    ./kickstart
```
  Reload the user preview in the admin GUI and you should now see 4 users.

- View the live network graph (Network tab)
  See your users on the graph
  Use the graph menu (Upper Right) to Reset or Arrange if necessary

- Add sample tallies/chits (while watching the live Network display)
  Still in test/sample:
```
    psql mychips admin -f tallies.sql
    psql mychips admin -f chits.sql
```  
  Remove them again with
```
    psql mychips admin -c "delete from mychips.tallies"
```
- Add more random users (while still watching the graph)
```
  ./randuser					# or:
  ./randuser -n Number_of_Users_to_Add
```  
  Press Arrange button (or hold it) in graph menu to arrange nodes better

- Launch the agent-model simulator:
```
  cd ../sim
  ./agent
```  
  You can watch as the user nodes will begin to form tallies with each other 
  and begin to trade chits over the tallies.
  
- Lifts
  When the graph accumulates some debits and credits, you can try executing
  some local credit lifts.  Keep in mind, this is not a network simulation
  but only working with a set of users within a single database.
  To work with distributed lifts, see the [docker simulation](../test/sim/README.dock).
  
  To examine the local lift path table, execute this SQL:
```
    select * from mychips.tallies_v_lifts  
```  
  To run a single credit lift, execute this SQL:
```  
    select mychips.lift_cycle(1)		-- Argument = max number of lifts
```

<br>[Next - User Application](use-pki.md)
<br>[Back to Index](README.md#contents)
