import 'package:flutter/material.dart';
import 'package:flutter/services.dart';
import 'main.dart';

const BOTH = 'BOTH';

class TransactionPage extends StatefulWidget {
  @override
  TransactionPageState createState() => new TransactionPageState();
}

class TransactionPageState extends State<TransactionPage> {
  @override
  Widget build(BuildContext context) {
    return Scaffold(
        appBar: AppBar(
          title: Text("MyCHIPs Transaction"),
        ),
        body: buildTransactionWidget(context, BOTH),
        drawer: MainDrawer()
    );
  }
}

  Widget buildTransactionWidget(context, transactionType, [friend = null]) {
    return Column(
        children: [
          createPaymentTextFields(friend),
          Divider(
              thickness: 2,
              color: Colors.black
          ),
          Container(
              child: Padding(
                padding: EdgeInsets.only(bottom: 100, left: 5),
                //TODO: Make the text in this textfield wrap
                child: TextField(
                  decoration: InputDecoration(
                      border: InputBorder.none,
                      hintText: "Purpose:",
                      hintStyle: TextStyle(color: Colors.grey)),
                  style: TextStyle(color: Colors.black),),)
          ),
          createButtons(context, transactionType)
        ]);
  }

  Widget createButtons(context, transactionType) {
  //TODO: Verify valid input before allowing button logic to be executed.
    if(transactionType == BOTH) {
    return Container(
      child: Padding(
        padding: EdgeInsets.all(10),
          child: Row(
            children: [
              Expanded(
                child: MaterialButton(
                  onPressed: () {
                    //TODO: PAY LOGIC
                    Navigator.pop(context);
                    print("pressed 'pay'");},
                  child: Text('PAY',
                    style: TextStyle(fontSize: 20)),
                  color: Colors.blue,
                  textColor: Colors.white,
                  elevation: 5,
                  height: 50,
                  minWidth: (MediaQuery.of(context).size.width) / 2.25)),
              MaterialButton(
                onPressed: () {
                  //TODO: REQUEST PAYMENT LOGIC
                  Navigator.pop(context);
                  print("pressed 'request'");},
                child: Text('REQUEST',
                  style: TextStyle(fontSize: 20)),
                color: Colors.blue,
                textColor: Colors.white,
                elevation: 5,
                height: 50,
                minWidth: (MediaQuery.of(context).size.width) / 2.25)
                ])
        )
    );
    }
    return Container (
      child: Padding(
        padding: EdgeInsets.all(10),
        child: Row(
          children: [
            Expanded(
              flex: 1,
              child: MaterialButton(
              onPressed: () {
                Navigator.pop(context);
                print("pressed "+ transactionType);},
              child: Text(transactionType, style: TextStyle(fontSize: 20)),
              color: Colors.blue,
              textColor: Colors.white,
              elevation: 5,
              // height:50
              ))])));
  }

  Widget createPaymentTextFields(friend) {
    return Container(
        child: Padding(
            padding: EdgeInsets.only(left: 5),
            child: Row(
                mainAxisSize: MainAxisSize.min,
                children: [
                  Expanded(
                      flex: 2,
                      child: friend != null ? Text(friend): TextField(
                          onChanged: (input) {
                            searchTallies(input);},
                          decoration: InputDecoration(
                              border: InputBorder.none,
                              hintText: "To Whom:",
                              hintStyle: TextStyle(color: Colors.grey)),
                          style: TextStyle(color: Colors.black))),
                  Expanded(
                      flex: 0,
                      child: Text("\$")),
                  Expanded(
                      child: TextField(
                          decoration: InputDecoration(
                              border: InputBorder.none,
                              hintText: "0",
                              hintStyle: TextStyle(color: Colors.grey)),
                          style: TextStyle(color: Colors.black),
                          keyboardType: TextInputType.number,
                          inputFormatters: [FilteringTextInputFormatter.digitsOnly]))
                ])
        )
    );
  }

  void searchTallies(input){
    //put logic to filter searched users here (probably the same as what's on the tally page)
    print(input);
  }