import 'package:flutter/material.dart';
import 'main.dart';
import 'tally.dart';
import 'tally_page.dart';

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
                });
              }
          ),
        ]
      ),
      body: Container(child: new Stack(children: [
        Container(child : buildTallyList()),
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
              builder: (BuildContext context) => new TallyPage(t.friend, t.balance)
          ));
        }
    );
  }

  void filterUsers(input) {
    //put logic to filter searched users here
    print(input);
  }
}