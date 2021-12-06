import Web3 from 'web3'
import { AbiItem } from "web3-utils"
import { address, privateKey, url } from "../config"
import path from 'path'
import fs from 'fs'
const solc =  require('solc')

const contractFolder = "../contracts";
const web3 = new Web3(url)

interface Receipt {
  rawTransaction: string;
}

const deploy = async(contractName: string) => {
  const contractPath = path.resolve(__dirname, contractFolder, contractName)
  const contract = fs.readFileSync(contractPath, 'utf8')
  var input = {
    language: 'Solidity',
    sources: {
      target: {
        content: contract
      }
    },
    settings: {
      outputSelection: {
        '*': {
          '*': ['*']
        }
      }
    }
  };
  var output = JSON.parse(solc.compile(JSON.stringify(input)))
  const {abi, evm} = output.contracts.target.Greeter
  const contractInfo = new web3.eth.Contract(abi as AbiItem[])
  const object = {
    data: evm.bytecode.object,
    arguments: [5],
  }
  const txObject = contractInfo.deploy(object)
  const txReceipt = <Receipt> await web3.eth.accounts.signTransaction({
    from: address,
    data: txObject.encodeABI(),
    gas: 8000000,
  }, privateKey)

  web3.eth.transactionConfirmationBlocks = 0
  let res = await web3.eth.sendSignedTransaction(
    txReceipt.rawTransaction
  );
  return res
}

async function main() {
  const contractName = `${process.argv[2]}.sol`
  console.log(`Deploying ${contractName}...`)
  const receipt = await deploy(contractName)
  console.log("Contract deployed: ", receipt)

  const data = JSON.stringify({
    deployMigrationsReceipt: receipt,
  }, null, 4)

  // Write ouput to disk.  Write first to a tmp file so that when the final
  // file is found it's complete
  fs.writeFileSync('./output/output.tmp.json', data, 'utf8')
  fs.renameSync('./output/output.tmp.json', './output/output.json')
}

main()
