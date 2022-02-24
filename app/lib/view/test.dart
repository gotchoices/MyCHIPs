import 'package:flutter/material.dart';
import 'package:mychips/managers/connection/connection_manager.dart';
import 'package:mychips/managers/connection/credentials.dart';
import 'package:mychips/managers/host/host_manager.dart';

class MyChipsTestPage extends StatelessWidget {
  @override
  Widget build(BuildContext context) {
    return const MaterialApp(
      title: "Connect Test",
      home: MyChipsTestWidget(),
    );
  }
}

class MyChipsTestWidget extends StatefulWidget {
  const MyChipsTestWidget({Key? key}) : super(key: key);

  @override
  createState() => MyChipsTestState();
}

class MyChipsTestState extends State<MyChipsTestWidget> {
  final _tokenInputController = TextEditingController();
  final _userInputController = TextEditingController();

  @override
  void dispose() {
    _tokenInputController.dispose();
    _userInputController.dispose();
    super.dispose();
  }

  @override
  Widget build(BuildContext context) => MaterialApp(
        home: Column(
          children: [
            StreamBuilder(
                stream: HostManager().configStream,
                builder: (context, snapshot) {
                  return Text(snapshot.hasData ? '${snapshot.data}' : '');
                }),
            Text("Has key: ${ConnectionManager().hasKey}"),
            TextFormField(enabled: !ConnectionManager().hasKey, controller: _userInputController),
            TextFormField(enabled: !ConnectionManager().hasKey, controller: _tokenInputController),
            TextButton(
                child: const Text('Connect'),
                onPressed: (!ConnectionManager().connectionStream.hasValue &&
                        (ConnectionManager().hasKey || _tokenInputController.text != ""))
                    ? () async {
                        if (!ConnectionManager().hasKey) {
                          ConnectionManager().credentials =
                              Credentials(_userInputController.text, _tokenInputController.text);
                        }
                        await ConnectionManager().connection;
                        // TODO: do something with the socket
                      }
                    : null)
          ],
        ),
      );
}
