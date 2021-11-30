import Web3 from 'web3'

import { address, privateKey, url } from "./config"
const web3 = new Web3(url)

function sleep(ms: number) {
    return new Promise(resolve => setTimeout(resolve, ms));
}

async function main() {
    // Wait for Geth to be online
    while (true) {
        var info: String;
        try {
            info = await web3.eth.getNodeInfo()
            console.log("Geth online: ", info)
            break
        } catch (err) {
            if (err instanceof Error) {
                console.log("Geth not available: ", err.message)
            } else {
                console.log("Geth not available: ", err)
            }
            await sleep(1000)
            continue
        }
    }

    // Transfer funds to our account
    const coinbase = await web3.eth.getCoinbase();
    await web3.eth.sendTransaction({
                                   from: coinbase,
                                   to: address,
                                   value: web3.utils.toWei("1", "ether")
    })
}

main()
