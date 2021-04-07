import 'package:flutter/material.dart';
import 'package:flutter/services.dart';
import 'package:flutter_app/objects/account.dart';
import 'package:flutter_app/objects/transaction.dart';
import 'package:flutter_app/presenter/transaction_presenter.dart';
import 'error_popup.dart';
import 'main_drawer_view.dart';
import 'success_popup.dart';

const BOTH = 'BOTH';
const PAY = 'PAY';
const REQUEST = 'REQUEST';

class TransactionPage extends StatefulWidget {
  final Account transactionPartner;
  TransactionPage(this.transactionPartner, {Key key})
      : super(key: key);

  @override
  TransactionPageState createState() => new TransactionPageState();
}

class TransactionPageState extends State<TransactionPage> {
  TextEditingController amtController = TextEditingController();
  TextEditingController msgController = TextEditingController();
  Transaction curTransaction;

  @override
  void dispose() {
    amtController.dispose();
    msgController.dispose();
    super.dispose();
  }

  @override
  Widget build(BuildContext context) {
    return Scaffold(
            appBar: AppBar(
                title: Text("Payment Details"),
                automaticallyImplyLeading: false,
                leading: Builder(
                    builder: (BuildContext context) => IconButton(
                          icon: const Icon(Icons.clear_rounded),
                          onPressed: () => Navigator.popUntil(
                              context, (route) => route.isFirst),
                        ))),
            body: buildPage(),
            drawer: MainDrawer())
        // )
        ;
  }

  Widget buildPage() {
    return Stack(children: [
      Column(children: [
        Padding(
            padding: EdgeInsets.fromLTRB(20, 15, 6, 8),
            child: Row(children: [
              buildAccountTitle()
            ])),
        Divider(
          thickness: 2,
          indent: 20,
          endIndent: 20,
        ),
        Padding(
            padding: EdgeInsets.fromLTRB(20, 8, 6, 8),
            child: Row(children: [
              Expanded(flex: 0, child: Text("₵")),
              Expanded(
                  child: TextField(
                      controller: amtController,
                      decoration: InputDecoration(
                          border: InputBorder.none,
                          hintText: "0.00",
                          hintStyle: TextStyle(color: Colors.grey)),
                      style: TextStyle(color: Colors.black),
                      keyboardType: TextInputType.number))
            ])),
        Divider(
          thickness: 2,
          indent: 20,
          endIndent: 20,
        ),
        Padding(
            padding: EdgeInsets.fromLTRB(20, 0, 0, 0),
            child: TextField(
                keyboardType: TextInputType.multiline,
                maxLines: null,
                controller: msgController,
                decoration: InputDecoration(
                    border: InputBorder.none,
                    hintText: "Please enter a payment message",
                    hintStyle: TextStyle(color: Colors.grey, fontSize: 18)),
                style: TextStyle(fontSize: 18))),
      ]),
      Positioned(
        bottom: 10,
        width: (MediaQuery.of(context).size.width),
        child: createButtons(context),
      ),
    ]);
  }

  Widget buildAccountTitle() {
    return Container(
        decoration: BoxDecoration(
            borderRadius: BorderRadius.circular(40), color: Colors.white),
        child: Row(children: [
          CircleAvatar(
              backgroundImage: new NetworkImage(
                  "https://miro.medium.com/max/450/1*W35QUSvGpcLuxPo3SRTH4w.png")),
          Padding(
              padding: EdgeInsets.all(8.0),
              child: Text(
                widget.transactionPartner.displayName,
                style: TextStyle(fontWeight: FontWeight.bold),
              ))
        ]));
  }

  Widget createButtons(context) {
    var presenter = TransactionPresenter();
    //TODO: Verify valid input before allowing button logic to be executed.
    //TODO: tie input to a transaction object to send through the presenter
    return Container(
        child: Padding(
            padding: EdgeInsets.all(10),
            child: Row(mainAxisAlignment: MainAxisAlignment.center, children: [
              MaterialButton(
                onPressed: () {
                  Transaction t = Transaction(DateTime.now(), msgController.text, widget.transactionPartner.displayName, "curUser", amtController.text);
                  print(t.toString());
                  if (presenter.requestPayment(t)) {
                    Navigator.pop(context);
                    succPop(context, "Payment sent successfully");
                  } else {
                    errPop(context, "Payment failed. Try again?");
                  }
                },
                child: Text('REQUEST',
                    style:
                        TextStyle(fontSize: 18, fontWeight: FontWeight.bold)),
                color: Colors.white,
                textColor: Theme.of(context).primaryColor,
                elevation: 5,
                height: 50,
                minWidth: (MediaQuery.of(context).size.width) / 2.5,
              ),
              Padding(
                padding: EdgeInsets.all(10),
              ),
              MaterialButton(
                onPressed: () {
                  Transaction t = Transaction(DateTime.now(), msgController.text, "curUser", widget.transactionPartner.displayName, amtController.text);
                  if (presenter.sendPayment(t)) {
                    //successful transaction
                    Navigator.pop(context);
                    succPop(context, 'great work mate. request sent');
                  } else {
                    //something went wrong...
                    errPop(context, 'request failed.');
                  }
                },
                child: Text('PAY',
                    style:
                        TextStyle(fontSize: 18, fontWeight: FontWeight.bold)),
                color: Colors.white,
                textColor: Theme.of(context).primaryColor,
                elevation: 5,
                height: 50,
                minWidth: (MediaQuery.of(context).size.width) / 2.5,
              ),
            ])));
  }
}
