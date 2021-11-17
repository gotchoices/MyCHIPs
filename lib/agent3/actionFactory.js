const Action = require("./action.js")

module.exports = {
    createAction(type) {
        var action;

        if (type === "findTradingPartner") {
            action = new Action({type: "findTradingPartner"}); //Object is placeholder for functions or other config stuff
        }
        // Add more types here...

        return action;
    }
}