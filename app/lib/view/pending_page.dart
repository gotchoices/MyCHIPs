import 'package:flutter/material.dart';
import 'package:flutter_app/objects/transaction.dart';
import 'home_page.dart';
import 'package:random_date/random_date.dart';

class PendingPage extends StatefulWidget {
  @override
  PendingPageState createState() => new PendingPageState();
}

class PendingPageState extends State<PendingPage> {
  //TODO: Fetch transactions. For now statically put in these two
  Transaction tran1 = Transaction(RandomDate.withRange(2000, 2020).random(), "pizza", "John Doe", "you", 12);
  Transaction tran2 = Transaction(RandomDate.withRange(2000, 2020).random(), "wings", "you", "Jane Doe", 9);
  List transactionList = <Transaction>[];

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(
        title: Text("Pending Transactions")
      ),
      body : buildBody(),
      drawer: MainDrawer()
    );
  }

  Widget buildBody() {
    transactionList = <Transaction>[];
    transactionList.add(tran1);
    transactionList.add(tran2);
    transactionList.add(tran2); //TODO: because i put a divider in for even indexes, i had to put this in twice for it to appear. pls fix
    return ListView.builder(
      padding: const EdgeInsets.all(16),
      itemCount: transactionList.length,
      itemBuilder: (context, item) {
        int index = item ~/ 2;
        if(item.isOdd) return Divider();
        if (index >= transactionList.length)
          return SizedBox();
        return buildRow(transactionList[index]);
      },
    );
  }

  Widget buildRow(Transaction t) {
    //TODO: Implement a better system to check if current user is the requester or requestee
    bool usersRequest = false;
    if (t.sender == "you") usersRequest = true;
    return ListTile(
      title: Text(
          t.receiver + " requested ₵" + t.amount.toString() + " from " + t.sender
          , style: TextStyle(fontSize: 18)
      ),
      trailing: usersRequest ? Text("Pending...") : 
          MaterialButton(
            onPressed: null,
            child: Text('Send', style: TextStyle(fontSize: 20)),
            color: Colors.blue,
            textColor: Colors.white,
            elevation: 5,
            height: 50,
          )
    );
  }
}