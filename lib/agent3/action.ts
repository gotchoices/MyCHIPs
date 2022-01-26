import Agent from "./agent";

interface Action {
    agent: Agent;
    //TODO we need to type these
    parameters: any;
    checkForPeer: any;
    remoteCall: any;

    run(): void
}

export default Action