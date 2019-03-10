namespace ReagentsFs

module CASN =
  open System
  open System.Threading
  open System.Collections.Generic

  let inline internal inc (x: byref<int>) = Interlocked.Increment (&x)
  let inline internal dec (x: byref<int>) = Interlocked.Decrement (&x)
  let inline internal same (x: obj) (y: obj) = LanguagePrimitives.PhysicalEquality x y
  let inline internal casi (x: byref<int>, y: _, z: _) = Interlocked.CompareExchange (&x, y, z)
  let inline internal cas (x: byref<obj>, y: _, z: _) = Interlocked.CompareExchange (&x, y, z)

  let mutable internal ids = 0

  type [<AllowNullLiteral>] Atom =
    val internal id : int
    val mutable internal content : obj
    new content = { id = inc (&ids) ; content = content }

  type Atom<'a> (value: 'a) =
    inherit Atom (box value)

  type [<Struct>] Op =
    {
      mutable atom: Atom
      mutable after: obj
      mutable before: obj
    }

  type CASN =
    {
      mutable status: int
      mutable helpers: int
      ops: array<Op>
    }

  let [<Literal>] internal Failure = -1
  let [<Literal>] internal Acquire = 0
  let [<Literal>] internal Success = 1

  let rec internal proceed (casn: CASN) =
    let status = Volatile.Read (&casn.status)
    if Acquire = status then
      acquire casn 0
    else
      let success = Acquire < status
      for i=0 to casn.ops.Length-1 do
        let op = &casn.ops.[i]
        let desired = if success then op.after else op.before
        cas (&op.atom.content, desired, casn) |> ignore
      success

  and internal acquire (casn: CASN) i =
    if i < casn.ops.Length then
      let op = &casn.ops.[i]
      let before = op.before
      let atom = op.atom
      if 0 <> Volatile.Read (&casn.status) then
        proceed casn
      else
        let was = cas (&atom.content, casn, before)
        if same was before then
          if Volatile.Read (&casn.status) < Acquire then
            cas (&atom.content, before, casn) |> ignore
            proceed casn
          else
            acquire casn (i+1)
        elif same was casn then
          acquire casn (i+1)
        else
          match was with
            | :? CASN as that ->
              help (&atom.content) that
              acquire casn i
            | _ ->
              casi (&casn.status, Failure, Acquire) |> ignore
              proceed casn
    else
      casi (&casn.status, Success, Acquire) |> ignore
      proceed casn

  and internal help (from: byref<obj>) casn =
    inc (&casn.helpers) |> ignore
    if same (Volatile.Read (&from)) casn then
      proceed casn |> ignore
    dec (&casn.helpers) |> ignore

  let rec internal op' (atom: Atom<'a>) (expected: 'a) =
    match Volatile.Read (&atom.content) with
      | :? CASN as that -> help (&atom.content) that ; op' atom expected
      | before -> if unbox<'a> before = expected then before else null

  let op (casn: CASN) i (atom: Atom<'a>) (desired: 'a) (expected: 'a) =
    let before = op' atom expected
    let op = &casn.ops.[i]
    op.atom <- atom
    op.before <- before
    op.after <- box desired

  let alloc n = { status = Acquire; helpers = 0; ops = Array.zeroCreate n }

  let internal sort (ops: array<Op>) =
    for i=1 to ops.Length-1 do
      let mutable j = i
      let op = ops.[i]
      while 0 < j && op.atom.id < ops.[j-1].atom.id do
        ops.[j] <- ops.[j-1]
        j <- j-1
      if j <> i then ops.[j] <- op

  let casn (casn: CASN) =
    sort casn.ops
    Volatile.Write (&casn.status, Acquire)
    let result = proceed casn
    while 0 <> Volatile.Read (&casn.helpers) do
      Thread.Yield () |> ignore
    result

  // ---------------------------------------------------------------------------

  let atom (value: 'a) = Atom<'a> value

  let rec load (atom: Atom<'a>) : 'a =
    match Volatile.Read (&atom.content) with
      | :? CASN as that -> help (&atom.content) that ; load atom
      | content -> unbox<'a> content

  let rec internal store' (atom: Atom<'a>) after =
    match Volatile.Read (&atom.content) with
      | :? CASN as that -> help (&atom.content) that ; store' atom after
      | before ->
        let was = cas (&atom.content, after, before)
        if not (same was before) then
          store' atom after

  let store (atom: Atom<'a>) (value: 'a) = store' atom (box value)
