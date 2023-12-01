import React, { useEffect } from "react";
import { createNativeStackNavigator } from "@react-navigation/native-stack";
import { createBottomTabNavigator } from "@react-navigation/bottom-tabs";
import { View, Text } from "react-native";
import { useDispatch, useSelector } from "react-redux";

import useSocket from '../hooks/useSocket';
import { fetchAvatar, fetchPersonalAndCurrency, getPreferredLanguage, getFilter } from '../redux/profileSlice';
import { colors } from '../config/constants';

import Invite from "../screens/Invite";
import Home from "../screens/Home";
import Scanner from "../screens/Scanner";
import TallyPreview from "../screens/Tally/TallyPreview";
import EditOpenTally from "../screens/Tally/EditOpenTally";
import TallyReport from "../screens/Tally/TallyReport";
import Setting from "../screens/Setting";
import Profile from "../screens/Profile";
import ProfileEdit from "../screens/Profile/ProfileEdit";
import InviteProvider from "../components/InviteProvider";
import TradingVariables from "../screens/Tally/TradingVariables";
import CustomIcon from "../components/CustomIcon";

import ShareTally from "../screens/ShareTally";
import ChitHistory from "../screens/Tally/ChitHistory";
import ImportKeyScreen from "../screens/ImportKeyScreen";
import ChitDetail from "../screens/Tally/ChitDetail";
import TallyContract from "../screens/Tally/TallyContract";
import PaymentDetail from "../screens/Tally/PaymentDetail";
import FilterScreen from "../screens/Filter";
import DraftTally from "../screens/Tally/DraftTally";
import RequestDetail from "../screens/Tally/RequestDetail";
import TallyCertificate from "../screens/Tally/TallyCertificate";
import Receive from "../screens/Recieve";
import ReceiveShareTally from "../screens/ReceiveTallyShare";
import NotificationScreen from "../screens/Notification/NotificationScreen";
import TallyRequest from "../screens/Tally/TallyRequest";


const screenOptions = {
  headerTitleAlign: 'center',
  headerShadowVisible: false,
  headerTintColor: colors.gray300,
  headerTitleStyle: {
    color: colors.gray300,
    fontSize: 18,
    fontFamily: 'inter',
    fontWeight: '500',
  } 
}

const Tab = createBottomTabNavigator();

const HomeStack = createNativeStackNavigator();

function HomeStackScreen() {
  return (
    <HomeStack.Navigator>
      <HomeStack.Screen
        name="Home"
        component={Home}
        options={{ headerShown: false }}
      />
      <HomeStack.Screen
        name="DraftTally"
        component={DraftTally}
        options={{ title: "Customize New Certificate" }}
      />
      <HomeStack.Screen
        name="TallyRequest"
        component={TallyRequest}
        options={{ headerShown: false }}
      />
      <HomeStack.Screen
        name="TallyReport"
        component={TallyReport}
        options={{ headerShown: false }}
      />
      <HomeStack.Screen
        name="OpenTallyEdit"
        component={EditOpenTally}
        options={{ title: "Open Tally" }}
      />
      <HomeStack.Screen
        name="ChitHistory"
        component={ChitHistory}
        options={{ title: "Chit History" }}
      />
      <HomeStack.Screen
        name="ChitDetail"
        component={ChitDetail}
        options={{ title: "Chit Detail" }}
      />
      <HomeStack.Screen
        name="TradingVariables"
        component={TradingVariables}
        options={{ title: "Trading Variables" }}
      />
      <HomeStack.Screen
        name="PaymentDetail"
        component={PaymentDetail}
        options={{ title: "Payment Detail" }}
      />
      <HomeStack.Screen
        name="RequestDetail"
        component={RequestDetail}
        options={{ title: "Request Detail" }}
      />
        <HomeStack.Screen
        name="Notification"
        component={NotificationScreen}
        options={{ title: "Notification" }}
      />
      <InviteStack.Screen
        name="TallyCertificate"
        component={TallyCertificate}
        options={{ title: "Tally Certificate" }}
      />
    </HomeStack.Navigator>
  );
}


const InviteStack = createNativeStackNavigator();
function InviteStackScreen() {
  return (
    <InviteProvider >
      <InviteStack.Navigator screenOptions={screenOptions}>
        <InviteStack.Screen name="Invite" component={Invite} options={{ headerShown: false }} />
        <InviteStack.Screen
          name="FilterScreen"
          component={FilterScreen}
          options={{
            title: "Filters",
            headerShadowVisible: false,
          }}
        />
        <InviteStack.Screen
          name="TallyPreview"
          component={TallyPreview}
          options={{ title: "Tally Preview" }}
        />
        <InviteStack.Screen
          name="TallyShare"
          component={ShareTally}
          options={{ title: "Share Tally", headerShadowVisible: false }}
        />
        <InviteStack.Screen
          name="TallyContract"
          component={TallyContract}
          options={{ title: "Tally Contract" }}
        />
        <InviteStack.Screen
          name="TallyCertificate"
          component={TallyCertificate}
          options={{ title: "Tally Certificate" }}
        />
      </InviteStack.Navigator>
    </InviteProvider>
  );
}

const ReceiveStack = createNativeStackNavigator();
function ReceiveStackScreen() {
  return (
    <ReceiveStack.Navigator>
      <ReceiveStack.Screen name="Request" component={Receive} />
      <ReceiveStack.Screen name="ShareTally" component={ReceiveShareTally} />
    </ReceiveStack.Navigator>
  );
}

const SettingStack = createNativeStackNavigator();
function SettingStackScreen() {
  return (
    <SettingStack.Navigator>
      <SettingStack.Screen name="Setting" component={Setting} />
      <SettingStack.Screen
        name="Profile"
        component={Profile}
        options={{ title: "Profile" }}
      />
      <SettingStack.Screen
        name="ProfileEdit"
        component={ProfileEdit}
        options={{ title: "Edit Profile" }}
      />
      <SettingStack.Screen
        name="ImportKey"
        component={ImportKeyScreen}
        options={{ title: "Import Key" }}
      />
    </SettingStack.Navigator>
  );
}

const Navigator = () => {
  const { user } = useSelector((state) => state.currentUser);
  const user_ent = user?.curr_eid;
  const { wm } = useSocket();
  const dispatch = useDispatch();

  useEffect(() => {
    dispatch(fetchAvatar({ wm, user_ent }));
    dispatch(fetchPersonalAndCurrency({ wm, user_ent }));
    dispatch(getPreferredLanguage(wm));
    dispatch(getFilter());
  }, [wm, user_ent, fetchAvatar]);

  return (
    <Tab.Navigator
      screenOptions={{ headerShown: false, tabBarShowLabel: false }}
    >
      <Tab.Screen
        name="Tally"
        component={HomeStackScreen}
        options={{
          tabBarIcon: (props) => (
            <CustomIcon name="home" {...{ ...props, size: 24 }} />
          ),
        }}
      />

      <Tab.Screen
        name="Request"
        component={ReceiveStackScreen}
        options={{
          title: "Request",
          tabBarIcon: (props) => (
            <CustomIcon name="receive" {...{ ...props, size: 26 }} />
          ),
        }}
      />

      <Tab.Screen
        name="Scan"
        component={Scanner}
        options={{
          unmountOnBlur: true,
          tabBarIcon: (props) => (
            <CustomIcon name="scan" {...{ ...props, size: 23 }} />
          ),
        }}
      />

      <Tab.Screen
        name="InviteScreen"
        component={InviteStackScreen}
        options={{
          tabBarTestID: "inviteBtn",
          tabBarIcon: (props) => (
            <CustomIcon name="invite" {...{ ...props, size: 26 }} />
          ),
        }}
      />

      <Tab.Screen
        name="Settings"
        component={SettingStackScreen}
        options={{
          tabBarIcon: (props) => (
            <CustomIcon name="settings" {...{ ...props, size: 25 }} />
          ),
        }}
      />
    </Tab.Navigator>
  );
};

export default Navigator;
