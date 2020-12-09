class TallyTicket {
  String token;
  String expires;
  String host;
  String port;
  TallyTicket.fromJson(Map<String, dynamic> json)
  : token = json['token'],
    expires = json['expires'],
    host = json['host'],
    port = json['port'];

  String toString() {
    "Token : $token \n Expires: $expires \n Host: $host$port";
  }
  //{"ticket":{"token":"6d8eba30a54a9877a21522b9666f6b1c","expires":"2020-11-17T17:17:07.000Z","host":"spa0","port":60000}}
}