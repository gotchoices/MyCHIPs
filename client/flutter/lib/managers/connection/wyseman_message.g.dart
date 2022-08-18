// GENERATED CODE - DO NOT MODIFY BY HAND

part of 'wyseman_message.dart';

// **************************************************************************
// JsonSerializableGenerator
// **************************************************************************

WysemanMessage _$WysemanMessageFromJson(Map<String, dynamic> json) =>
    WysemanMessage(
      json['ip'] as String,
      json['cookie'] as String,
      json['userAgent'] as String,
      json['date'] as String,
    );

Map<String, dynamic> _$WysemanMessageToJson(WysemanMessage instance) =>
    <String, dynamic>{
      'ip': instance.ip,
      'cookie': instance.cookie,
      'userAgent': instance.userAgent,
      'date': instance.date,
    };
