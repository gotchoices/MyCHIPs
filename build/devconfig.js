#!/usr/bin/env node
//Configure environment for development mode docker
const path = require('path')
const fs = require('fs')

const devDir='/usr/local/devel'		//inside container context
const debugLevel='debug'

const mychipsDir = path.resolve(__dirname, '..')
const mychipsDirName = path.basename(mychipsDir)
const localDir = path.resolve(__dirname, '../local')
const envFile = path.join(localDir, 'compose-dev.env')
//const devDir = path.resolve(mychipsDir, '..')

if (!fs.existsSync(localDir))
  fs.mkdirSync(localDir)

const settings = `MYCHIPS_ROOTNAME=${mychipsDirName}
MYCHIPS_DEVDIR=${devDir}
MYCHIPS_DEBUG=${debugLevel}
`

fs.writeFileSync(envFile, settings)
