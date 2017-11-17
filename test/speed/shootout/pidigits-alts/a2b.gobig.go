package main

import "os"
import "fmt"
import "strconv"
import big "math/gobig"

// a2b benchmark, forcibly using the pure-Go implementation
// of big integers. See also a2b.big.go

func main() {
  n := 1000
  iters := 0

  x := big.NewInt(1)
  y := big.NewInt(2)
  t := big.NewInt(0)

  if len(os.Args) > 1 {
    n, _ = strconv.Atoi(os.Args[1])
  }

  for x.BitLen() < n {
    t.Add(x, y)
    y.Add(t, y)
    x =  t
    iters++
  }

  fmt.Printf("%d\n", iters)
}
