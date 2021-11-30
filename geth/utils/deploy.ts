import Web3 from 'web3'
import contract from "./Migrations.json"
import { AbiItem } from "web3-utils";

const bytecode = contract.bytecode
const abi = contract.abi as AbiItem[]
const privateKey = "96056e9ee8751520722534bf43f18026447dce015ad0217cf182e85d0d81589d"
const address = "0xecfe4b91b3f094496610fb0a947f5b44b212173f"
const url = "http://geth:8545"
const web3 = new Web3(url)

const deploy = async() => {
  const contractInfo = new web3.eth.Contract(abi)
  const txObject = contractInfo.deploy({
    data: bytecode
  })
  const txReceipt = await web3.eth.accounts.signTransaction({
    from: address,
    data: txObject.encodeABI(),
    gas: 8000000,
  }, privateKey)

  if (txReceipt.rawTransaction) {
    web3.eth.transactionConfirmationBlocks = 0
    let res = await web3.eth.sendSignedTransaction(
      txReceipt.rawTransaction
    ).catch(console.log);
    console.log(res)
  }
}

deploy()
