import 'package:flutter/material.dart';
import 'home_page.dart';
import '../objects/tally.dart';
import 'tally_page.dart';
import 'create_tally_page.dart';

class TallyListPage extends StatefulWidget {
  @override
  TallyListPageState createState() => new TallyListPageState();
}

class TallyListPageState extends State<TallyListPage> {
  final List tallyList = <Tally>[];
  bool searching = false;

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(
        title: searching ? TextField(
          onChanged: (input) {
            filterUsers(input);
          },
          decoration: InputDecoration(
              icon: Icon(Icons.search, color: Colors.white,),
              hintText: "type user here",
              hintStyle: TextStyle(color: Colors.white)),
          style: TextStyle(color: Colors.white),
          cursorColor: Colors.white,
        ) :
        Text("My Tallies"),
        actions: <Widget>[
          searching ?
          IconButton(
              icon: Icon(Icons.cancel_outlined),
              onPressed: () {
                setState(() {
                  searching = !searching;
                });
              }
          ) :
          IconButton(
              icon: Icon(Icons.search),
              onPressed: () {
                setState(() {
                  searching = !searching;
                });}
          ),
        ]
      ),
      body: Container(child:
        Stack(children: [
          Container(child : buildTallyList()),
          Container(child : buildButton())
      ])),
      drawer: MainDrawer(),
    );
  }

  Widget buildTallyList() {
    return ListView.builder (
        padding: const EdgeInsets.all(16),
        itemBuilder:(context, item) {
          if(item.isOdd) return Divider();
          int index = item ~/ 2;
          if (index >= tallyList.length)
            tallyList.addAll(TallyGenerator.generateFakeTallies(10));
          return buildRow(tallyList[index]);
        }
    );
  }

  Widget buildRow(Tally t) {
    return ListTile(
        title : Text(t.friend, style: TextStyle(fontSize: 18)),
        trailing: Text("₵" + t.balance.toString(), style: TextStyle(fontSize: 18)),
        onTap: () {
          Navigator.push(context, new MaterialPageRoute(
              builder: (BuildContext context) => new TallyPage(Tally(t.friend, t.balance))
          ));
        }
    );
  }

  Widget buildButton() {
    var maxButtonWidth = (MediaQuery.of(context).size.width) / 1.75;
    return Align(
      alignment: Alignment.bottomCenter,
      child : Padding(
      padding: const EdgeInsets.all(15),
      child: MaterialButton(
        onPressed: () {
          Navigator.push(context, new MaterialPageRoute(
            builder: (BuildContext context) => new CreateTallyPage()));
        },
        child: const Text("Create a New Tally", style: TextStyle(fontSize: 20)),
        color: Colors.blue,
        textColor: Colors.white,
        elevation: 5,
        height: 50,
        minWidth: maxButtonWidth
      ))
    );
  }

  void filterUsers(input) {
    //put logic to filter searched users here
    print(input);
  }
}