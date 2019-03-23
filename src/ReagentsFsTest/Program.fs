open System
open System.Threading
open System.Diagnostics

open ReagentsFs

let verifyEq actual expected =
  if actual <> expected then failwithf "%A <> %A" actual expected

let nAtoms = 8
let nOps = 4000000L

module TestCASN =
  open CASN
  let stress () =
    let atoms = Array.init nAtoms (fun _ -> atom 0)
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
        let desc = alloc 2
        startBarrier.SignalAndWait ()
        let watch = Stopwatch ()
        watch.Start ()
        while nS < nOps do
          let i = rnd.Next atoms.Length
          let mutable j = i
          while j = i do
            j <- rnd.Next atoms.Length
          //let mutable k = i
          //while k = i || k = j do
          //  k <- rnd.Next atoms.Length
          let iVal = load atoms.[i]
          let jVal = load atoms.[j]
          //let kVal = load atoms.[k]
          op desc 0 atoms.[i] (jVal - 1) iVal
          op desc 1 atoms.[j] (iVal + 1) jVal
          //op desc 2 atoms.[k] (iVal + 1) kVal
          if casn desc then
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
    let sum = atoms |> Array.sumBy load
    printfn "tot = %d, suc = %d, t = %A, suc / sec / thread = %f"
      (!nAttempts)
      (!nSuccesses)
      (!totalTime)
      (float (!nSuccesses) / (!totalTime).TotalSeconds)
    verifyEq sum 0

module TestAtomic =
  open Atomic

  let smoke () =
    let xA = atom 1
    let yA = atom 2
    let d = alloc ()
    atomically d (load yA >> update (fun (x, y) -> (y+1, x-1)) xA >> store yA) ()
    verifyEq (atomically d (load xA) ()) 3
    verifyEq (atomically d (load yA) ()) 0

  let stress () =
    let atoms = Array.init nAtoms (fun _ -> atom 0)
    let n = Environment.ProcessorCount
    printfn "ProcessorCount = %d" n
    if not Runtime.GCSettings.IsServerGC then
      printfn "Not using server GC!"
    let nLive = ref n
    use startBarrier = new Barrier (!nLive)
    let nSuccesses = ref 0L
    let totalTime = ref (TimeSpan 0L)
    for i=1 to !nLive do
      let t = Thread (fun () ->
        let mutable nS = 0L
        let mutable nA = 0L
        let rnd = System.Random ()
        let desc = alloc ()
        startBarrier.SignalAndWait ()
        let watch = Stopwatch ()
        watch.Start ()
        while nS < nOps do
          let i = rnd.Next atoms.Length
          let mutable j = i
          while j = i do
            j <- rnd.Next atoms.Length
          atomically
            desc
            (load atoms.[i] >>
             update (fun (x, y) -> (y-1, x+1)) atoms.[j] >>
             store atoms.[i])
            ()
          nS <- nS + 1L
          if 0L = (nS &&& 0xFFFFFL) then
            printf "."
        printf "(%d)" i
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
    let sum = atoms |> Array.sumBy (fun a -> atomically (alloc ()) (load a) ())
    printfn "suc = %d, t = %A, suc / sec / thread = %f"
      (!nSuccesses)
      (!totalTime)
      (float (!nSuccesses) / (!totalTime).TotalSeconds)
    verifyEq sum 0

[<EntryPoint>]
let main argv =
  TestAtomic.smoke ()
  TestAtomic.stress ()

  //TestCASN.stress ()

  printfn "Big success!"
  0
