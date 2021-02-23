import 'package:flutter/material.dart';
import 'package:flutter_app/presenter/tally_list_presenter.dart';
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
  final List searchList = <Tally>[];
  bool searching = false;
  var presenter = new TallyListPresenter();

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(
        title: searching ? TextField(
          onChanged: (input) {
            searchList.clear();
            searchList.addAll(presenter.filterUsers(input, tallyList));
            setState(() {});
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
                  searchList.clear();
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
        itemCount: searching ? searchList.length : null,
        itemBuilder:(context, item) {
          int index = item ~/ 2;
          if(item.isOdd) return Divider();
          if (index >= tallyList.length && !searching)
            //if we've reached the end of the list, query the presenter for more, providing the last tally in the list for reference
            tallyList.addAll(tallyList.length == 0 ? presenter.getUserTallies() : presenter.getUserTallies(tallyList[tallyList.length - 1]));
          else if (searching && searchList.length > 0) {
            if (index >= searchList.length) {
              return SizedBox();
            }
            return buildRow(searchList[index]);
          }
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


}