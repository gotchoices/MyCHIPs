module.exports = [
  ['p1000', 'p1001', 1, 'color=pink'],['p1001', 'p1002', 1, 'color=pink'],['p1002', 'p1003', 1, 'color=pink'],
  ['p1100', 'p1101', 1, 'color=pink'],['p1101', 'p1102', 1, 'color=pink'],['p1102', 'p1103', 1, 'color=pink'],
  ['p1200', 'p1201', 1, 'color=pink'],['p1201', 'p1202', 1, 'color=pink'],['p1202', 'p1203', 1, 'color=pink'],

  ['p1000', 'p1101', 1, 'color=pink'],['p1100', 'p1201', 1, 'color=pink'],
  ['p1001', 'p1102', 1, 'color=pink'],['p1101', 'p1202', 1, 'color=pink'],
  ['p1002', 'p1103', 1, 'color=pink'],['p1102', 'p1203', 1, 'color=pink'],
//  ['p1003', 'p1103', 1, 'color=pink'],['p1103', 'p1203', 1, 'color=pink'],
  
  ['p1003', 'p1002', 5, 'color=blue'],
  ['p1002', 'p1103', 6, 'color=blue'],
  ['p1103', 'p1203', 7, 'color=blue'],
  ['p1203', 'p1102', 8, 'color=blue'],
  ['p1102', 'p1101', 9, 'color=blue'],
  ['p1101', 'p1001', 10, 'color=blue'],
  ['p1001', 'p1000', 11, 'color=blue'],
  ['p1000', 'p1100', 12, 'color=blue'],
  ['p1100', 'p1201', 13, 'color=blue'],
  ['p1201', 'p1200', 14, 'color=blue'],
]
