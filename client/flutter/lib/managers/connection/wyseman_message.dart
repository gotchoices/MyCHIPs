import 'package:json_annotation/json_annotation.dart';

part 'wyseman_message.g.dart';

@JsonSerializable()
class WysemanMessage {
  final String ip;
  final String cookie;
  final String userAgent;
  final String date;

  const WysemanMessage(this.ip, this.cookie, this.userAgent, this.date);

  factory WysemanMessage.fromJson(Map<String, dynamic> json) => _$WysemanMessageFromJson(json);
  Map<String, dynamic> toJson() => _$WysemanMessageToJson(this);
}
