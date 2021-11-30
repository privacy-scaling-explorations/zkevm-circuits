import Web3 from 'web3'
import contract from "../build/contracts/Migrations.json"
import { AbiItem } from "web3-utils"
import { address, privateKey, url } from "../config"
import fs from 'fs'

const bytecode = contract.bytecode
const abi = contract.abi as AbiItem[]
const web3 = new Web3(url)

interface Receipt {
  rawTransaction: string;
}

const deploy = async() => {
  const contractInfo = new web3.eth.Contract(abi)
  const txObject = contractInfo.deploy({
    data: bytecode
  })
  const txReceipt = <Receipt> await web3.eth.accounts.signTransaction({
    from: address,
    data: txObject.encodeABI(),
    gas: 8000000,
  }, privateKey)

  web3.eth.transactionConfirmationBlocks = 0
  let res = await web3.eth.sendSignedTransaction(
    txReceipt.rawTransaction
  );
  console.log("Contract deployed: ", res)
  return res
}

async function main() {
  console.log("Deploying Migrations contract...")
  const receipt = await deploy()

  const data = JSON.stringify({
    deployMigrationsReceipt: receipt,
  }, null, 4)

  // Write ouput to disk.  Write first to a tmp file so that when the final
  // file is found it's complete
  fs.writeFileSync('./output/output.tmp.json', data, 'utf8')
  fs.renameSync('./output/output.tmp.json', './output/output.json')
}

main()
