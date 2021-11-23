const actions = require("./actions.js")

module.exports = {
    createAction(type, agentData, mongoDB, parameters) {
        var action;

        if (type === "makeNewTally") {
            action = actions.MakeNewTally(agentData, mongoDB.collection("actions"), parameters)
        }
        // Add more types here...

        return action;
    }
}