// SPDX-License-Identifier: Unlicense
pragma solidity ^0.8.0;

contract SimpleStorage {
    constructor() {
        set(0xcafe, 0xbabe);
    }
    function get(uint k) view public returns (uint) {
       uint v;
       assembly {
           v := sload(k)
       }
       return v;
    }
    function set(uint k, uint v) public {
       assembly {
           sstore(k,v)
       }
    }
}