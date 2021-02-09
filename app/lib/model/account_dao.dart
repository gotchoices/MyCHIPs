import 'package:flutter_app/objects/account.dart';

class AccountDao {

  Account getAccountData() {
    //connect to account
    return new Account('johnDoe', 'john', 'doe', 'johndoe@gmail.com');
  }

  void setAccountData(account) {
    //establish persistence here
  }
}