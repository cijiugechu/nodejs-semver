const semver = require('semver')

const versions = ['2.1.0']
const range = '>=1.0.0 <2.0.0'

console.log(semver.maxSatisfying(versions, range))