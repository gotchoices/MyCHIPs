import 'package:flutter/material.dart';

const errorImageDir = "assets/access_denied.png";

Widget buildErrorWidget(context, [errMsg = "Try again later."]) {
  return ListBody(
    children:[
      Text("Something went wrong!"),
      Image.asset(errorImageDir),
      //TODO: Add specificity to this text. What went wrong? Was there no corresponding tally? Server error? Internet connection? Not enough funds?
      Text(errMsg),
      Padding(padding: EdgeInsets.all(16),),
      MaterialButton(
        onPressed: (){Navigator.pop(context);},
        child: Text('okay',
            style: TextStyle(fontSize: 18, fontWeight: FontWeight.bold)),
          color: Colors.white,
          textColor: Theme.of(context).primaryColor,
          elevation: 5,
          height: 50,
          minWidth: (MediaQuery.of(context).size.width) / 2.5
      )
    ]
  );
}

void errPop(context, [errMsg = "Try again later."]) {
  showDialog(context: context, builder: (BuildContext context){
    return AlertDialog(
        scrollable: false,
        content: SingleChildScrollView(
            child: ListBody(
                children:[
                  Text("Something went wrong!"),
                  Image.asset(errorImageDir),
                  //TODO: Add specificity to this text. What went wrong? Was there no corresponding tally? Server error? Internet connection? Not enough funds?
                  Text(errMsg),
                ]
            )
        ),
        actions: <Widget>[
          TextButton(
            child: Text('okay'),
            onPressed: () {
            Navigator.of(context).pop();
          })]
    );
  });
}