import 'package:flutter_app/objects/account.dart';
import '../services.dart';

class AccountDao {
  Future<Account> getAccountData() async {
    //connect to account
    // Account a = await Services.getUserData();
    // return a;
    return new Account();
  }

  void setAccountData(account) async {
    //establish persistence here
    // int check = await Services.setUserData(account);
  }
}
