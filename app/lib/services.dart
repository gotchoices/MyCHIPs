import 'managers/user/account.dart';

class Services {
  //Tally functions
  static Future<int> getUserTallies(var userId) async {
    return Future.delayed(const Duration(milliseconds: 120), () {
      print('returning 10');
      return 10;
    });
  }

  static Future<int> createNewTally(var tally) async {
    return Future.delayed(const Duration(microseconds: 90), () {
      return 0;
    });
  }

  // send 0 to deny, 1 to accept
  static Future<int> respondToTally(int response) async {
    return Future.delayed(const Duration(microseconds: 90), () {
      return 0;
    });
  }

  //User functions
  static Future<Account> getUserData(var userId) async {
    return Future.delayed(const Duration(microseconds: 120), () {
      return new Account('John Doe', 'John', 'Doe', email: 'JohnDoe@gmail.com');
    });
  }

  // return 0 if successful anything else otherwise
  static Future<int> saveNewAccount(Account account) async {
    return Future.delayed(const Duration(microseconds: 120), () {
      return 0;
    });
  }

  static String apiCall(var json) {
    return "";
  }
}
