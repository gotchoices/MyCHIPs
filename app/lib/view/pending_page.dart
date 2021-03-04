import 'package:flutter/material.dart';
import 'package:flutter_app/objects/transaction.dart';
import 'package:flutter_app/presenter/transaction_presenter.dart';
import 'home_page.dart';
import 'package:random_date/random_date.dart';
import 'package:intl/intl.dart';

class PendingPage extends StatefulWidget {
  @override
  PendingPageState createState() => new PendingPageState();
}

class PendingPageState extends State<PendingPage> {
  TransactionPresenter presenter = new TransactionPresenter();
  //TODO: Fetch transactions. For now statically put in these two
  Transaction tran1 = Transaction(RandomDate.withRange(2000, 2020).random(), "pizza", "John Doe", "you", 12);
  Transaction tran2 = Transaction(RandomDate.withRange(2000, 2020).random(), "wings", "you", "Jane Doe", 9);
  List transactionList = <Transaction>[];
  final DateFormat dateFormatter = DateFormat('MMMM d');

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
        return buildRow(transactionList[index], index);
      },
    );
  }

  Widget buildRow(Transaction t, int index) {
    //TODO: Implement a better system to check if current user is the requester or requestee
    bool usersRequest = false;
    if (t.sender == "you") usersRequest = true;
    //TODO: Transactions should only be dismissible if they're incomplete and involve the user (although all they see should involve them)
    return Dismissible (
      key: ValueKey(t),
      onDismissed: (DismissDirection direction) {
        setState(() {
          bool result = false;
          if (usersRequest) result = presenter.cancelRequest(t);
          else result = presenter.declinePayment(t);
          //if the deletion was successful on the server
          if (result) //remove from list
            transactionList.remove(index);
        });
      },
      confirmDismiss: (DismissDirection direction) async{
        return await showDialog(
          context: context,
          builder: (BuildContext context) {
            //TODO: Change this text based on the type of deletion (decline or cancellation)
            return AlertDialog(
              title: const Text("Confirm"),
              content: const Text("Are you sure you wish to delete this item?"),
              actions: <Widget>[
                TextButton(
                    onPressed: () => Navigator.of(context).pop(true),
                    child: const Text("DELETE")
                ),
                TextButton(
                  onPressed: () => Navigator.of(context).pop(false),
                  child: const Text("CANCEL"),
                ),
              ],
            );
          },
        );
      },
      child: ListTile(
      title: Text(
          t.receiver + " requested ₵" + t.amount.toString() + " from " + t.sender
          , style: TextStyle(fontSize: 15)
      ),
      subtitle: Text(dateFormatter.format(t.date)),
      trailing: usersRequest ?
          MaterialButton(
            onPressed: (){},
            child: Text('Send', style: TextStyle(fontSize: 20)),
            color: Colors.blue,
            textColor: Colors.white,
            elevation: 5,
            height: 50,
          )
          : Text("pending...")
    ));
  }

  confirmDelete (DismissDirection direction) async {

  }
}