const semver = require('semver')

const versions = ['1.2.3', '1.2.2', '1.2.4']
const range = '~1.2.3'

console.log(semver.minSatisfying(versions, range))