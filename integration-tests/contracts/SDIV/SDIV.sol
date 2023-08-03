// SPDX-License-Identifier: MIT
 
pragma solidity >=0.7.0 <0.9.0;
 
contract CheckSdiv {
    struct Len {
        uint256 l;
    }
 
    function checkBatchYul(Len calldata l) external returns (uint256 r) {
        assembly {
            let input := calldataload(4)
            let len := div(input, 100)
            // let a := 83
            let b := 77
            for {
                let i := 0
            } lt(i, len) {
                i := add(i, 1)
            } {
                r := sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,sdiv(b,r))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            }
        }
    }
}