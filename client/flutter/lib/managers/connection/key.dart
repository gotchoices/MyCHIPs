import 'package:json_annotation/json_annotation.dart';
part 'key.g.dart';

@JsonSerializable()
class Key {
  final String host;
  final int port;
  final String user;
  final String privateKey;

  Key(this.host, this.port, this.user, this.privateKey);

  factory Key.fromJson(Map<String, dynamic> json) => _$KeyFromJson(json["login"]);
  Map<String, dynamic> toJson() => {"login": _$KeyToJson(this)};
}
