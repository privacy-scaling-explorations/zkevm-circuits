package witness

import (
	"encoding/json"
	"fmt"
	"log"
	"os"
	"path/filepath"
)

func check(err error) {
	if err != nil {
		log.Fatal(err)
	}
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
	b, err := json.MarshalIndent(nodes, "", "    ")
	if err != nil {
		fmt.Println(err)
	}

	_, err = f.WriteString(string(b))
	check(err)
}
