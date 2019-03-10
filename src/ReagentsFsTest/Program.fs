open System
open System.Threading
open System.Diagnostics

open ReagentsFs

let verify b =
  if not b then failwith "Failed"

let stressTest () =
  let atoms = Array.init 8 (fun _ -> CASN.atom 0)
  let n = Environment.ProcessorCount
  printfn "ProcessorCount = %d" n
  if not Runtime.GCSettings.IsServerGC then
    printfn "Not using server GC!"
  let nLive = ref n
  use startBarrier = new Barrier (!nLive)
  let nAttempts = ref 0L
  let nSuccesses = ref 0L
  let totalTime = ref (TimeSpan 0L)
  for i=1 to !nLive do
    let t = Thread (fun () ->
      let mutable nS = 0L
      let mutable nA = 0L
      let rnd = System.Random ()
      let casn = CASN.alloc 3
      startBarrier.SignalAndWait ()
      let watch = Stopwatch ()
      watch.Start ()
      while nS < 4000000L do
        let i = rnd.Next atoms.Length
        let mutable j = i
        while j = i do
          j <- rnd.Next atoms.Length
        let mutable k = i
        while k = i || k = j do
          k <- rnd.Next atoms.Length
        let iVal = CASN.load atoms.[i]
        let jVal = CASN.load atoms.[j]
        let kVal = CASN.load atoms.[k]
        CASN.op casn 0 atoms.[i] (jVal - 2) iVal
        CASN.op casn 1 atoms.[j] (kVal + 1) jVal
        CASN.op casn 2 atoms.[k] (iVal + 1) kVal
        if CASN.casn casn then
          nS <- nS + 1L
        nA <- nA + 1L
        if 0L = (nA &&& 0xFFFFFL) then
          printf "."
      printf "(%d)" i
      Interlocked.Add (nAttempts, nA) |> ignore
      Interlocked.Add (nSuccesses, nS) |> ignore
      let took = watch.Elapsed
      lock nLive <| fun () ->
        totalTime := !totalTime + took
        nLive := !nLive - 1
        Monitor.PulseAll nLive)
    t.Start()
  lock nLive <| fun () ->
    while !nLive <> 0 do
      Monitor.Wait nLive |> ignore
  let sum = atoms |> Array.sumBy CASN.load
  printfn "tot = %d, suc = %d, t = %A, suc / sec / thread = %f"
    (!nAttempts)
    (!nSuccesses)
    (!totalTime)
    (float (!nSuccesses) / (!totalTime).TotalSeconds)
  verify (sum = 0)

[<EntryPoint>]
let main argv =
  stressTest ()

  printfn "Big success!"
  0
