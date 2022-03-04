package main

/*
   #include <stdlib.h>
*/
import "C"
import (
	"encoding/json"
	"fmt"
	"main/gethutil"
	"unsafe"
)

// TODO: Add proper error handling.  For example, return an int, where 0 means
// ok, and !=0 means error.
//export CreateTrace
func CreateTrace(configStr *C.char) *C.char {
	var config gethutil.TraceConfig
	err := json.Unmarshal([]byte(C.GoString(configStr)), &config)
	if err != nil {
		return C.CString(fmt.Sprintf("Failed to unmarshal config, err: %v", err))
	}

	executionResult, err := gethutil.TraceTx(config)
	if err != nil {
		return C.CString(fmt.Sprintf("Failed to trace tx, err: %v", err))
	}

	bytes, err := json.MarshalIndent(executionResult, "", "  ")
	if err != nil {
		return C.CString(fmt.Sprintf("Failed to marshal ExecutionResult, err: %v", err))
	}

	return C.CString(string(bytes))
}

//export FreeString
func FreeString(str *C.char) {
	C.free(unsafe.Pointer(str))
}

func main() {}
