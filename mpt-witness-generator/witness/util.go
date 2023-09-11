package witness

import (
	"encoding/json"
	"fmt"
	"log"
	"os"
	"path/filepath"
	"strconv"
)

func check(err error) {
	if err != nil {
		log.Fatal(err)
	}
}

func MatrixToJson(rows [][]byte) string {
	// Had some problems with json.Marshal, so I just prepare json manually.
	json := "["
	for i := 0; i < len(rows); i++ {
		json += listToJson(rows[i])
		if i != len(rows)-1 {
			json += ","
		}
	}
	json += "]"

	return json
}

func listToJson(row []byte) string {
	json := "["
	for j := 0; j < len(row); j++ {
		json += strconv.Itoa(int(row[j]))
		if j != len(row)-1 {
			json += ","
		}
	}
	json += "]"

	return json
}

func StoreNodes(testName string, nodes []Node) {
	name := testName + ".json"
	path := "../generated_witnesses/" + name

	// Create the directories if they do not exist yet
	err := os.MkdirAll(filepath.Dir(path), 0755)
	if err != nil {
		log.Fatal(err)
	}

	f, err := os.Create(path)
	check(err)
	defer f.Close()
	b, err := json.Marshal(nodes)
	if err != nil {
		fmt.Println(err)
	}

	_, err = f.WriteString(string(b))
	check(err)
}
