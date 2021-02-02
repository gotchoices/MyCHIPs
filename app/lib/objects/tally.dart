import 'tally_generator.dart';

class Tally {
  String friend;
  var balance;
  String host;
  String port;
  Tally(friend, balance) {
    this.friend = friend;
    this.balance = balance;
  }

  static Tally parseTallyTicket(ticket) {
    print(ticket.toString());
    //TODO: Interface with server to turn these tickets into usable tallies.
    return TallyGenerator.generateFakeTally();
  }
}

