let verbosity = ref 0

let cpThreshold = ref 0

let memoThreshold = ref 0

let outfile = ref stdout

let printFlag n = !verbosity >= n

let filter_strat = ref 1

let use_isa_sym = ref 0

let genCex = ref false

let cexBound = ref 10

let doGenCex n = !genCex == n

let belowCPThresholdInternal n = n < !cpThreshold

let belowMemoThreshold n = n < !memoThreshold

let isFilterStrat n = (n = !filter_strat)

let useISASym n = (!use_isa_sym = n)

let printf x y = Printf.fprintf !outfile "%s" y; x

let printfFlush x y = Printf.fprintf !outfile "%s" y; flush !outfile; x

let lastUpdateCheck = ref (Sys.time())

let printTimestamp x y = Printf.fprintf !outfile "\nTIMESTAMP,%s,%f\n" y (Sys.time()); x

let lowerThanBound n = n < !cexBound

let timeForStatusUpdate _ =
  if printFlag 3
  then true
  else
  let t = Sys.time() in
  if t -. !lastUpdateCheck > 5.0
  then (lastUpdateCheck := t; true)
  else false
