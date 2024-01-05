import { Alert } from "react-native";
import React, { useEffect } from "react";
import { useDispatch, useSelector } from "react-redux";
import { createBottomTabNavigator } from "@react-navigation/bottom-tabs";
import { createNativeStackNavigator } from "@react-navigation/native-stack";

import useSocket from "../hooks/useSocket";
import {
  getFilter,
  fetchAvatar,
  getTallyListFilter,
  getPreferredLanguage,
  fetchPersonalAndCurrency,
  setShowCreateSignatureModal,
} from "../redux/profileSlice";
import { colors } from "../config/constants";

import Home from "../screens/Home";
import Invite from "../screens/Invite";
import Scanner from "../screens/Scanner";
import Setting from "../screens/Setting";
import Profile from "../screens/Profile";
import Receive from "../screens/Recieve";
import FilterScreen from "../screens/Filter";
import ShareTally from "../screens/ShareTally";
import CustomIcon from "../components/CustomIcon";
import ChitDetail from "../screens/Tally/ChitDetail";
import DraftTally from "../screens/Tally/DraftTally";
import TallyReport from "../screens/Tally/TallyReport";
import ChitHistory from "../screens/Tally/ChitHistory";
import TallyPreview from "../screens/Tally/TallyPreview";
import ProfileEdit from "../screens/Profile/ProfileEdit";
import ImportKeyScreen from "../screens/ImportKeyScreen";
import TallyRequest from "../screens/Tally/TallyRequest";
import PendingChits from "../screens/Tally/PendingChits";
import InviteProvider from "../components/InviteProvider";
import EditOpenTally from "../screens/Tally/EditOpenTally";
import TallyContract from "../screens/Tally/TallyContract";
import PaymentDetail from "../screens/Tally/PaymentDetail";
import RequestDetail from "../screens/Tally/RequestDetail";
import RequestShare from "../screens/Recieve/RequestShare";
import FilterTallyScreen from '../screens/Tally/FilterTallyList'
import TradingVariables from "../screens/Tally/TradingVariables";
import TallyCertificate from "../screens/Tally/TallyCertificate";
import PendingChitDetail from "../screens/Tally/PendingChits/Detail";
import NotificationScreen from "../screens/Notification/NotificationScreen";
import { GenerateKeysAlertModal } from '../components/GenerateKeyAlertModal';

const screenOptions = {
  headerTitleAlign: "center",
  headerShadowVisible: false,
  headerTintColor: colors.gray300,
  headerTitleStyle: {
    color: colors.gray300,
    fontSize: 18,
    fontFamily: "inter",
    fontWeight: "500",
  },
};

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
      <HomeStack.Screen
        name="TallyPreview"
        component={TallyPreview}
        options={{ title: "Tally Preview" }}
      />
      <InviteStack.Screen
        name="TallyCertificate"
        component={TallyCertificate}
        options={{ title: "Tally Certificate" }}
      />
      <HomeStack.Screen
        name="PendingChits"
        component={PendingChits}
        options={{ headerShown: false }}
      />
      <HomeStack.Screen
        name="PendingChitDetail"
        component={PendingChitDetail}
        options={{ headerShown: false }}
      />
      <HomeStack.Screen
        name="FilterTallyScreen"
        component={FilterTallyScreen}
        options={{ headerShown: true, headerTitle: 'Filters' }}
      />
    </HomeStack.Navigator>
  );
}

const InviteStack = createNativeStackNavigator();
function InviteStackScreen() {
  return (
    <InviteProvider>
      <InviteStack.Navigator screenOptions={screenOptions}>
        <InviteStack.Screen
          name="Invite"
          component={Invite}
          options={{ headerShown: false }}
        />
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
      <ReceiveStack.Screen name="RequestShare" component={RequestShare} />
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
  const { showCreateSignatureModal } = useSelector((state) => state.profile);
  const user_ent = user?.curr_eid;
  const { wm } = useSocket();
  const dispatch = useDispatch();

  useEffect(() => {
    dispatch(fetchAvatar({ wm, user_ent }));
    dispatch(fetchPersonalAndCurrency({ wm, user_ent }));
    dispatch(getPreferredLanguage(wm));
    dispatch(getFilter());
    dispatch(getTallyListFilter())
  }, [wm, user_ent, fetchAvatar]);

  const onDismissSignatureModal = () => {
    dispatch(setShowCreateSignatureModal(false))
  }

  const onKeySaved = () => {
    dispatch(setShowCreateSignatureModal(false))
    Alert.alert(
      "Success",
      "Key is generated successfully now you can accept tally."
    );
  }

  return (
    <>
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
          name="RequestScreen"
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
      <GenerateKeysAlertModal
        visible={showCreateSignatureModal}
        onDismiss={onDismissSignatureModal}
        onKeySaved={onKeySaved}
        onError={(err) => {
          Alert.alert("Error", err);
        }}
      />
    </>
  );
};

export default Navigator;
