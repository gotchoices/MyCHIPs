import 'package:flutter_app/objects/account.dart';

class Services {
  //Tally functions
  static Future<int> getUserTallies(var userId) async {
    Future f = Future.delayed(const Duration(milliseconds: 120), () {
      print('returning 10');
      return 10;
    });
    return f;
  }

  static Future<int> createNewTally(var tally) async {
    Future f = Future.delayed(const Duration(microseconds: 90), () {
      return 0;
    });
    return f;
  }

  // send 0 to deny, 1 to accept
  static Future<int> respondToTally(int response) async {
    Future f = Future.delayed(const Duration(microseconds: 90), () {
      return 0;
    });
    return f;
  }

  //User functions
  static Future<Account> getUserData(var userId) async {
    Future f = Future.delayed(const Duration(microseconds: 120), () {
      return new Account('John Doe', 'John', 'Doe', 'JohnDoe@gmail.com');
    });
    return f;
  }

  // return 0 if successful anything else otherwise
  static Future<int> saveNewAccount(Account account) async {
    Future f = Future.delayed(const Duration(microseconds: 120), () {
      return 0;
    });
    return f;
  }

  static String apiCall(var json) { return null; }
}
