import { ObjectId } from 'mongodb'

export interface PeerDoc extends Document, AccountData {
  _id?: ObjectId
}

export interface ActionDoc extends ActionData {
  _id?: ObjectId
  data?: AccountData
}

export interface AnalyticsDoc extends Document {
  _id?: ObjectId
}
