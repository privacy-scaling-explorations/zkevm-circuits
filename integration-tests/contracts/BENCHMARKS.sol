// SPDX-License-Identifier: MIT
 
pragma solidity >=0.7.0 <0.9.0;
 
contract Benchmarks {
    struct Len {
        uint32 l;
    }
 
    function checkMload(Len calldata l) external returns (uint32 r) {
        assembly {
            let input := calldataload(4)
            let len := div(input, 100)
            let b := 77
            for {
                let i := 0
            } lt(i, len) {
                i := add(i, 1)
            } {
                r := mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(mload(0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            }
        }
    }

    function checkSdiv(Len calldata l) external returns (uint32 r) {
        assembly {
            let input := calldataload(4)
            let len := div(input, 100)
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

    function checkKeccak256(Len calldata l) external returns (uint32 r) {
        assembly {
            let input := calldataload(4)
            let len := div(input, 100)
            let b := 77
            for {
                let i := 0
            } lt(i, len) {
                i := add(i, 1)
            } {
                mstore(0, keccak256(0, 65536)) // 32768
            }
            r := mload(0)
        }
    }

    function checkExtCodeSize(address[] calldata addresses) external returns (uint256 length) {
        uint256 ptr = 68;
        uint256 len = addresses.length/100;
        uint8 inc = 32;
        for (uint256 i=0; i<len; i++) {
            assembly {
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
                length := extcodesize(calldataload(ptr))
                ptr := add(ptr, inc)
            }
        }
        return length;
    }
}
