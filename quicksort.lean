import PfsProgs25.Unit13.QuickSort

def main (args: List String) : IO Unit := do
  let n := args.head? |>.bind String.toNat? |>.getD 100000
  let m := args[1]? |>.bind String.toNat? |>.getD (n * 10)

  let mut l := #[]
  for _ in [0:n] do
    l := l.push (← IO.rand 0 m)
  IO.println s!"Sorting random list (naive) of size {n} with max value {m}"
  let l' := l.toList
  let start ← IO.monoMsNow
  let sorted := quickSort l'
  let done ← IO.monoMsNow
  IO.println s!"Time for sorting: {done - start}ms"
  IO.println s!"Done: got {sorted.length} elements. First 10: {sorted.take 10}"
  return ()
