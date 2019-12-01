package main

import "encoding/base64"
import "fmt"
import "time"
import "strings"

// From https://github.com/kostya/benchmarks/blob/master/base64/test.go

func main() {
        //STR_SIZE := 10000000
        STR_SIZE := 1000000
	TRIES := 100

	str2 := ""
	bytes := []byte(strings.Repeat("a", STR_SIZE))

	coder := base64.StdEncoding

	t := time.Now()
	s := 0

	for i := 0; i < TRIES; i += 1 {
		str2 = coder.EncodeToString(bytes)
		s += len(str2)
	}
	fmt.Printf("encode: %d, %.4f\n", s, time.Since(t).Seconds())
}
