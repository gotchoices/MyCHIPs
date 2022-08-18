// GENERATED CODE - DO NOT MODIFY BY HAND

part of 'key.dart';

// **************************************************************************
// JsonSerializableGenerator
// **************************************************************************

Key _$KeyFromJson(Map<String, dynamic> json) => Key(
      json['host'] as String,
      json['port'] as int,
      json['user'] as String,
      json['privateKey'] as String,
    );

Map<String, dynamic> _$KeyToJson(Key instance) => <String, dynamic>{
      'host': instance.host,
      'port': instance.port,
      'user': instance.user,
      'privateKey': instance.privateKey,
    };
