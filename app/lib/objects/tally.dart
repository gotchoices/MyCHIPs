import 'dart:math';

import 'package:flutter_app/objects/account.dart';

import 'tally_generator.dart';

class Tally {
  Account friend;
  var balance;
  int personID;
  String host;
  String port;
  Tally(friend, balance) {
    this.friend = friend;
    this.balance = balance;
    this.personID = Random(12).nextInt(1000);
  }

  static Tally parseTallyTicket(ticket) {
    print(ticket.toString());
    //TODO: Interface with server to turn these tickets into usable tallies.
    return TallyGenerator.generateFakeTally();
  }
}

