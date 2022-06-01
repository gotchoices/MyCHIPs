// GENERATED CODE - DO NOT MODIFY BY HAND

part of 'ticket.dart';

// **************************************************************************
// JsonSerializableGenerator
// **************************************************************************

Ticket _$TicketFromJson(Map<String, dynamic> json) => Ticket(
      json['token'] as String,
      DateTime.parse(json['expires'] as String),
      json['host'] as String,
      json['port'] as int,
      json['user'] as String?,
    );

Map<String, dynamic> _$TicketToJson(Ticket instance) => <String, dynamic>{
      'token': instance.token,
      'expires': instance.expires.toIso8601String(),
      'host': instance.host,
      'port': instance.port,
      'user': instance.user,
    };
