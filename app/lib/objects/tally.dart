import 'dart:math';

import '../managers/user/account.dart';

import 'tally_generator.dart';

class Tally {
  Account? friend;
  num balance;
  int personID = Random().nextInt(1000);
  // String host;
  // String port;
  Tally(this.friend, this.balance);

  static Tally parseTallyTicket(ticket) {
    print(ticket.toString());
    //TODO: Interface with server to turn these tickets into usable tallies.
    return TallyGenerator.generateFakeTally();
  }
}
