import 'package:flutter/material.dart';

const errorImageDir = "assets/access_denied.png";

Widget buildErrorWidget(context, [errMsg = "Try again later."]) {
  return Column(
    children:[
      Text("Something went wrong!"),
      Image.asset(errorImageDir),
      //TODO: Add specificity to this text. What went wrong? Was there no corresponding tally? Server error? Internet connection? Not enough funds?
      Text(errMsg),
      MaterialButton(
        onPressed: (){Navigator.pop(context);},
        child: Text('okay',
            style: TextStyle(fontSize: 20)),
        color: Colors.blue,
        textColor: Colors.white,
        elevation: 5,
      )
    ]
  );
}