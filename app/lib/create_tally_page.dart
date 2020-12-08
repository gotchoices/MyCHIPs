import 'package:flutter/material.dart';
import 'scanner.dart';

class CreateTallyPage extends StatefulWidget {
  @override
  CreateTallyPageState createState() => new CreateTallyPageState();
}

class CreateTallyPageState extends State<CreateTallyPage> {
  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(
        title: Text("Create a New Tally")
      ),
      body: Container(
        child: Stack(
          children: [
            buildTitle(),
            buildQRCode(),
            buildScanButton()
          ],
        )
      )
    );
  }

  Widget buildTitle() {
    return Padding(
      padding: const EdgeInsets.all(25),
      child: Align(
        alignment: Alignment.topCenter,
        child: Text("My Tally Code", style: TextStyle(fontSize: 40))
      )
    );
  }

  Widget buildQRCode() {
    //replace with call to backend
    return Align(
      alignment: Alignment.center,
      child: Image(image : NetworkImage('https://i.pinimg.com/originals/60/c1/4a/60c14a43fb4745795b3b358868517e79.png')));
  }

  Widget buildScanButton() {
    var maxButtonWidth = (MediaQuery.of(context).size.width) / 1.75;
    return Align(
      alignment: Alignment.bottomCenter,
      child : Padding(
        padding: const EdgeInsets.all(15),
        child: MaterialButton(
          onPressed: () {
              print("Load the QRCode scanner page");
            Navigator.push(context, new MaterialPageRoute(
               builder: (BuildContext context) => new QRViewExample()));
          },
          child: const Text("Scan QR Code", style: TextStyle(fontSize: 20)),
          color: Colors.blue,
          textColor: Colors.white,
          elevation: 5,
          height: 50,
          minWidth: maxButtonWidth
      ))
    );
  }
}
