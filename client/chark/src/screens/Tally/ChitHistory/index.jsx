import React, { useEffect, useState } from "react";
import { useSelector } from 'react-redux';
import { StyleSheet, FlatList, View, Text, ActivityIndicator, TouchableOpacity, RefreshControl } from "react-native";
import Icon from 'react-native-vector-icons/FontAwesome';

import useSocket from "../../../hooks/useSocket";
import { fetchChitHistory } from "../../../services/tally";
import { round, unitsToChips, unitsToFormattedChips } from "../../../utils/common";
import ChitHistoryHeader from "./ChitHistoryHeader";
import { colors, dateFormats } from "../../../config/constants";
import ChipValue from "../../../components/ChipValue";
import { formatDate } from "../../../utils/format-date";
import useMessageText from '../../../hooks/useMessageText';
import useTitle from '../../../hooks/useTitle';
import { 
  FilterSecondIcon
} from "../../../components/SvgAssets/SvgAssets";
import FieldFilterSelector from "../../../components/FieldFilterSelector";

const ChitHistory = (props) => {
  const { tally_uuid, digest } = props.route?.params ?? {};
  const { wm } = useSocket();
  const [loading, setLoading] = useState(true);
  const [chits, setChits] = useState(undefined);
  const [sortAscending, setSortAscending] = useState(false);
  const [statusFilter, setStatusFilter] = useState({
    values: ['good'], // Default to showing only 'good' status chits
    whereClause: "status = 'good'"
  });
  
  const [typeFilter, setTypeFilter] = useState({
    values: ['lift', 'tran'], // Default to showing only transaction chit types, not settings
    whereClause: "chit_type IN ('lift','tran')"
  });
  const { imagesByDigest } = useSelector((state) => state.avatar);
  const avatar = imagesByDigest?.[digest];
  const { messageText } = useMessageText();
  const chitMeText = messageText?.chits_v_me;

  useTitle(props.navigation, chitMeText?.msg?.chits?.title)
  
  // Component for the filter bar above the chit list
  const ChitFilterBar = () => {
    const { messageText } = useMessageText();
    const chitMeText = messageText?.chits_v_me?.col;
    
    // Handle status filter change
    const handleStatusFilterChange = (selectedValues, whereClause) => {
      setStatusFilter({
        values: selectedValues,
        whereClause
      });
    };
    
    // Handle chit type filter change
    const handleTypeFilterChange = (selectedValues, whereClause) => {
      setTypeFilter({
        values: selectedValues,
        whereClause
      });
    };
    
    // Get status options from the message text
    const getStatusOptions = () => {
      const statuses = chitMeText?.status?.values || [];
      return statuses.map(status => ({
        value: status.value,
        title: status.title || status.value
      }));
    };
    
    // Get chit type options from the message text
    const getTypeOptions = () => {
      const types = chitMeText?.chit_type?.values || [];
      return types.map(type => ({
        value: type.value,
        title: type.title || type.value
      }));
      // Include all chit types, including 'set'
    };
    
    return (
      <View style={styles.filterBarContainer}>
        {/* Date sort toggle */}
        <View style={styles.filterSection}>
          <TouchableOpacity 
            style={styles.filterButton}
            onPress={() => setSortAscending(!sortAscending)}
          >
            <Icon 
              name={sortAscending ? "sort-amount-asc" : "sort-amount-desc"} 
              size={14} 
              color="#636363" 
            />
            <Text style={styles.filterText}>
              {chitMeText?.crt_date?.title}
            </Text>
          </TouchableOpacity>
        </View>
        
        {/* Status filter using FieldFilterSelector */}
        <View style={styles.filterSection}>
          <FieldFilterSelector
            fieldName="status"
            screenId="chitHistory"
            options={getStatusOptions()}
            initialSelected={statusFilter.values}
            buttonLabel={chitMeText?.status?.title}
            onFilterChange={handleStatusFilterChange}
          />
        </View>
        
        {/* Chit Type filter using FieldFilterSelector */}
        <View style={styles.filterSection}>
          <FieldFilterSelector
            fieldName="chit_type"
            screenId="chitHistory"
            options={getTypeOptions()}
            initialSelected={typeFilter.values}
            buttonLabel={chitMeText?.chit_type?.title}
            onFilterChange={handleTypeFilterChange}
          />
        </View>
      </View>
    );
  };

  useEffect(() => {
    _fetchChitHistory();
  }, [tally_uuid])
  
  // When sort or filters change, reprocess data
  useEffect(() => {
    if (chits) {
      processChits(chits);
    }
  }, [sortAscending, statusFilter.values, typeFilter.values])

  const _fetchChitHistory = () => {
    setLoading(true);
    fetchChitHistory(
      wm,
      {
        fields: [
          'part_cuid', 'chit_ent', 'chit_idx', 'chit_uuid', 'chit_seq', 'chit_type', 'issuer', 'net', 
          'crt_date', 'chit_date', 'reference', 'memo', 'status', 'state', 'chain_idx', 'action'
        ],
        where: [
          `tally_uuid = ${tally_uuid}`,
          // We'll apply filter criteria in our processChits function
        ],
        order: [
          {
            field: 'action',
            asc: false,
          },
          {
            field: 'crt_date',
            asc: sortAscending, // Use the current sort direction
          },
        ]
      }
    ).then(data => {
      if (data?.length) {
        // Store the raw data and process it
        processChits(data);
      } else {
        setChits([]);
        setLoading(false);
      }
    }).catch(ex => {
      console.log("EXCEPTION ==> ", ex);
      setLoading(false);
    });
  }
  
  // Process chits for display based on current filters
  const processChits = (rawChits) => {
    if (!rawChits || rawChits.length === 0) {
      setChits([]);
      setLoading(false);
      return;
    }
    
    // Apply both status and type filters
    const filteredChits = rawChits.filter(chit => {
      // Status filter
      const statusMatch = statusFilter.values.length === 0 || 
                          statusFilter.values.includes(chit.status);
      
      // Type filter
      const typeMatch = typeFilter.values.length === 0 || 
                        typeFilter.values.includes(chit.chit_type);
      
      // Both filters must match
      return statusMatch && typeMatch;
    });
    
    // Sort by date if needed
    const sortedChits = [...filteredChits].sort((a, b) => {
      const dateA = new Date(a.crt_date).getTime();
      const dateB = new Date(b.crt_date).getTime();
      
      if (sortAscending) {
        return dateA - dateB; // Oldest first
      } else {
        return dateB - dateA; // Newest first
      }
    });
    
    // Calculate running balance based on sort direction
    let runningBalance = 0;
    let chitsWithRunningBalance;
    
    if (sortAscending) {
      // For chronological (oldest first) - start at zero and build up
      chitsWithRunningBalance = sortedChits.map((item) => {
        runningBalance += item.net;
        return { ...item, runningBalance };
      });
    } else {
      // For reverse chronological (newest first) - start with total and work backwards
      // First calculate the total net value of all chits
      const totalNet = sortedChits.reduce((sum, item) => sum + item.net, 0);
      runningBalance = totalNet;
      
      // Then assign running balances starting from the total and subtracting each chit's contribution
      chitsWithRunningBalance = sortedChits.map((item, index) => {
        // For the first item (newest), runningBalance is the total
        // For subsequent items, subtract the prior item's net from the running balance
        if (index > 0) {
          runningBalance -= sortedChits[index-1].net;
        }
        return { ...item, runningBalance };
      });
    }
    
    // Update the state
    setChits(chitsWithRunningBalance);
    setLoading(false);
  }

  const onChipClick = (item, index) => {
    props.navigation.navigate('ChitDetail', {
      chit_uuid: item.chit_uuid,
      chit_ent: item.chit_ent,
      chit_idx: item.chit_idx,
      chit_seq: item.chit_seq,
    });
  }

  const ChitItem = ({ item, index }) => {
    const formattedDate = formatDate({ date: item.chit_date, format: dateFormats.dateTime });
    
    // Get chit type for display
    const chitType = item.chit_type || 'lift';
    const chitTypeText = chitMeText?.col?.chit_type?.values?.find(v => v.value === chitType)?.title || chitType;
    
    // Check if reference and memo have content
    const hasReference = item.reference && 
                         item.reference !== 'null' && 
                         item.reference !== '{}' &&
                         JSON.stringify(item.reference) !== '{}';
                         
    const hasMemo = item.memo && item.memo.trim() !== '';
    
    // ChipValue component now handles currency conversion internally
    // No need to calculate conversion values here

    return (
      <TouchableOpacity
        style={styles.chitItem}
        onPress={() => { onChipClick(item, index) }}
      >
        {/* Transaction type (smaller font, left justified) */}
        <Text style={styles.transactionTypeText}>
          {chitTypeText}
        </Text>
        
        {/* Main row: Date, Amount, Total */}
        <View style={styles.mainRow}>
          {/* Date (indented) */}
          <Text style={styles.dateText}>{formattedDate}</Text>
          
          {/* Chit amount (center) */}
          <View style={styles.amountContainer}>
            <ChipValue 
              units={item?.net ?? 0}
              size="small"
              showIcon={true}
              iconSize={{width: 10, height: 10}}
            />
          </View>
          
          {/* Running balance (right) */}
          <View style={styles.balanceContainer}>
            <ChipValue 
              units={item?.runningBalance ?? 0}
              size="small"
              showIcon={false}
            />
          </View>
        </View>
        
        {/* Memo and reference (if they exist) */}
        {(hasMemo || hasReference) && (
          <View style={styles.detailsContainer}>
            {hasMemo && (
              <Text style={styles.memoText} numberOfLines={2} ellipsizeMode="tail">
                {item.memo}
              </Text>
            )}
            
            {hasReference && (
              <Text style={styles.referenceText} numberOfLines={1} ellipsizeMode="tail">
                {typeof item.reference === 'string' ? item.reference : JSON.stringify(item.reference)}
              </Text>
            )}
          </View>
        )}
      </TouchableOpacity>
    );
  }

  const ItemSeparator = () => {
    return <View style={styles.spacer} />
  }

  if (loading) {
    return <View style={[styles.container, { justifyContent: "center", alignItems: 'center' }]}>
      <ActivityIndicator />
    </View>
  }

  return <View style={styles.container}>
    <FlatList
      refreshControl={
        <RefreshControl
          refreshing={loading}
          onRefresh={_fetchChitHistory}
        />
      }
      ListHeaderComponent={
        <>
          <ChitHistoryHeader
            args={{
              ...props.route?.params,
              wm,
              avatar,
            }}
          />
          <ChitFilterBar />
        </>
      }
      contentContainerStyle={styles.contentContainer}
      data={chits}
      renderItem={ChitItem}
      keyExtractor={(item, index) => `${item.chit_uuid}${index}`}
      ItemSeparatorComponent={<ItemSeparator />}
      refreshing={loading}
      onRefresh={_fetchChitHistory}
    />
  </View>
}

const styles = StyleSheet.create({
  container: {
    flex: 1
  },
  contentContainer: {
    padding: 16
  },
  filterBarContainer: {
    flexDirection: 'row',
    flexWrap: 'wrap',
    justifyContent: 'flex-start',
    paddingHorizontal: 8,
    paddingVertical: 8,
    marginBottom: 8,
    backgroundColor: colors.white,
    borderRadius: 8,
  },
  filterSection: {
    alignItems: 'flex-start',
    marginRight: 8,
    marginBottom: 4,
  },
  filterButton: {
    borderWidth: 1,
    height: 30,
    borderColor: colors.white100,
    backgroundColor: colors.white200,
    flexDirection: 'row',
    borderRadius: 20,
    paddingHorizontal: 12,
    paddingVertical: 3,
    justifyContent: 'center',
    alignItems: 'center',
  },
  filterText: {
    fontSize: 12,
    color: '#636363',
    marginStart: 4,
    fontFamily: 'inter',
  },
  chitItem: {
    backgroundColor: 'white',
    padding: 8,
    paddingBottom: 6,
    borderRadius: 8,
    overflow: 'hidden'
  },
  transactionTypeText: {
    fontSize: 10,
    color: colors.gray500,
    marginBottom: 2,
    fontStyle: 'italic'
  },
  mainRow: {
    flexDirection: 'row',
    justifyContent: 'space-between',
    alignItems: 'center',
    marginLeft: 6,
    marginRight: 2
  },
  dateText: {
    fontSize: 12,
    fontWeight: '500',
    color: colors.gray700,
    flex: 1
  },
  amountContainer: {
    alignItems: 'center',
    flex: 1,
    justifyContent: 'center',
    paddingHorizontal: 2
  },
  balanceContainer: {
    alignItems: 'flex-end',
    justifyContent: 'flex-end',
    minWidth: 80,
    marginLeft: 5
  },
  detailsContainer: {
    marginTop: 4,
    marginLeft: 12,
    marginRight: 6
  },
  memoText: {
    fontSize: 13,
    color: colors.black100,
    marginBottom: 3
  },
  referenceText: {
    fontSize: 11,
    color: colors.gray500,
    marginBottom: 2,
    fontStyle: 'italic'
  },
  row: {
    flexDirection: 'row',
    justifyContent: 'center',
    alignItems: 'center'
  },
  title: {
    fontSize: 14,
    fontWeight: 'bold',
    color: '#14396C'
  },
  body: {
    fontSize: 14,
    color: 'black',
  },
  spacer: {
    // Reduced spacing between items by 50%
    height: 6,
  },
  label: {
    color: colors.gray500,
    fontSize: 12,
  }
});

export default ChitHistory;
