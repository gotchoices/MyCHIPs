import 'package:json_annotation/json_annotation.dart';
part 'ticket.g.dart';

@JsonSerializable()
class Ticket {
  final String token;
  final DateTime expires;
  final String host;
  final int port;
  final String? user;

  const Ticket(this.token, this.expires, this.host, this.port, this.user);
  factory Ticket.fromJson(Map<String, dynamic> json) => _$TicketFromJson(json["ticket"]);
  Map<String, dynamic> toJson() => {"ticket": _$TicketToJson(this)};
}
