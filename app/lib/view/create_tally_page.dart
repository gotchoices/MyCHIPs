import 'package:flutter/material.dart';
import 'package:flutter_app/objects/singletons.dart';
import 'package:flutter_app/presenter/qr_presenter.dart';
import 'package:qr_flutter/qr_flutter.dart';
import 'scanner_page.dart';

class CreateTallyPage extends StatefulWidget {
  @override
  CreateTallyPageState createState() => new CreateTallyPageState();
}

class CreateTallyPageState extends State<CreateTallyPage> {
  var presenter = QRPresenter();
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
    QrImage qr = QrImage(
      data: UserInfo().personalKey,
      version: QrVersions.auto,
      size: 350.0,
    );
    return Align(
      alignment: Alignment.center,
      child: qr);
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
               builder: (BuildContext context) => new Scanner()));
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
