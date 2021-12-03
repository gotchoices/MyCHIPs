import Agent from "./agents";

export function createAgent(type, params) {
    var agent;

    if (type === "Consumer") {
        agent = new Agent.Consumer(params, worldDBManager, myChipsDBManager,
            checkForPeer, remoteCall, getAgentInfo, logger);
    }
    // Add other types here

    return agent;
}

export function createDefaultAgent() {
    return new Agent.DefaultAgent();
}

export function createCustomAgent(config) {
    return new Agent(config);
}