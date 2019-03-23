namespace ReagentsFs

module Atomic =
  open System
  open System.Threading
  open System.Collections.Generic

  let inline inc (x: byref<int>) = Interlocked.Increment (&x)
  let inline dec (x: byref<int>) = Interlocked.Decrement (&x)
  let inline same (x: obj) (y: obj) = LanguagePrimitives.PhysicalEquality x y
  let inline casi (x: byref<int>, y: _, z: _) = Interlocked.CompareExchange (&x, y, z)
  let inline cas (x: byref<obj>, y: _, z: _) = Interlocked.CompareExchange (&x, y, z)
  let inline casa (x: byref<obj[]>, y: _, z: _) = Interlocked.CompareExchange (&x, y, z)

  let mutable ids = 0

  type Atom =
    val id: int
    val mutable content: obj
    new content = { id = inc (&ids) ; content = content }

  type Atom<'a> (value: 'a) =
    inherit Atom (box value)

  type Descriptor =
    {
      mutable helpers: int
      mutable allAtoms: Atom[]
      mutable uniqAtoms: Atom[]
      mutable uniqAtomsCount: int
      mutable indices: int[]
      mutable values: obj[]
      mutable input: obj
      mutable op: Op
    }

  and [<AbstractClass>] Op () =
    abstract member Attempt: Descriptor -> unit

  let atom (v: 'v) = Atom<'v> v

  let [<Literal>] Acquire = 0
  let [<Literal>] Attempt = 1

  let alloc () =
    {
      helpers = 0
      allAtoms = [||]
      uniqAtoms = [||]
      uniqAtomsCount = 0
      indices = [||]
      values = [||]
      input = null
      op = Unchecked.defaultof<_>
    }

  type [<AbstractClass>] Op<'a, 'b> () =
    inherit Op ()
    abstract member Atoms: Descriptor * int -> int
    abstract member Attempt: Descriptor * obj[] * 'a * byref<'b> * int -> int

  let inline attempt (this: Op<'a, 'b>) (d: Descriptor) =
    let before = Volatile.Read (&d.values)
    let n = d.uniqAtomsCount
    if same d before.[n] then
      let mutable b = Unchecked.defaultof<'b>
      let vs = Array.zeroCreate (n + 1)
      for i=0 to n - 1 do
        vs.[i] <- before.[i]
      if same before (Volatile.Read (&d.values)) then
        this.Attempt (d, vs, unbox<'a> d.input, &b, 0) |> ignore
        vs.[n] <- box b
        Interlocked.CompareExchange (&d.values, vs, before) |> ignore

  let inline addAtom (d: Descriptor) i r =
    if d.allAtoms.Length <= i then
      let allAtoms = Array.zeroCreate (i + 1)
      for j=0 to i-1 do
        allAtoms.[j] <- d.allAtoms.[j]
      d.allAtoms <- allAtoms
    d.allAtoms.[i] <- r
    i + 1

  let inline access (d: Descriptor) (vs: obj[]) i : byref<obj> =
    &vs.[d.indices.[i]]

  let load (aAtom: Atom<'a>) : Op<_, 'a> =
    {new Op<_, 'a> () with
      member this.Atoms (d, i) = addAtom d i aAtom
      member this.Attempt (d, vs, _, aR, i) =
        aR <- unbox<'a> (access d vs i)
        i + 1
      member this.Attempt d = attempt this d}

  let store (aAtom: Atom<'a>) : Op<'a, unit> =
    {new Op<'a, unit> () with
      member this.Atoms (d, i) = addAtom d i aAtom
      member this.Attempt (d, vs, a, _, i) =
        let aR = &access d vs i
        aR <- box<'a> a
        i + 1
      member this.Attempt d = attempt this d}

  let update (aab: 'a * 'b -> 'a * 'c) (aAtom: Atom<'a>) : Op<'b, 'c> =
    {new Op<'b, 'c> () with
      member this.Atoms (d, i) = addAtom d i aAtom
      member this.Attempt (d, vs, b, cR, i) =
        let aR = &access d vs i
        let (a, c) = aab (unbox<'a> aR, b)
        aR <- box<'a> a
        cR <- c
        i + 1
      member this.Attempt d = attempt this d}

  let (>>) (ab: Op<'a, 'b>) (bc: Op<'b, 'c>) : Op<'a, 'c> =
    {new Op<'a, 'c> () with
      member this.Atoms (d, i) = bc.Atoms (d, ab.Atoms (d, i))
      member this.Attempt (d, vs, a, c, i) =
        let mutable b = Unchecked.defaultof<'b>
        let i = ab.Attempt (d, vs, a, &b, i)
        if 0 <= i then bc.Attempt (d, vs, b, &c, i) else i
      member this.Attempt d = attempt this d}

  let rec proceed (d: Descriptor) =
    let n = d.uniqAtomsCount
    let mutable vs = Volatile.Read (&d.values)
    if not (same d vs.[n]) then
      let uniqAtoms = d.uniqAtoms
      for i = 0 to n - 1 do
        cas (&uniqAtoms.[i].content, vs.[i], d) |> ignore
    elif same d vs.[n-1] then
      let mutable i = 0
      let uniqAtoms = d.uniqAtoms
      while i < n && same d vs.[n-1] do
        if same d vs.[i] then
          let atom = uniqAtoms.[i]
          let wasBefore = Volatile.Read (&atom.content)
          match wasBefore with
            | :? Descriptor as other ->
              if same d other then
                while same d <| Volatile.Read (&vs.[i]) do
                  Thread.Yield () |> ignore
                i <- i + 1
              else
                help other (&atom.content)
            | _ ->
              let vs' = Volatile.Read (&d.values)
              if same vs' vs then
                let wasAfter = cas (&atom.content, d, wasBefore)
                if same wasAfter wasBefore then
                  Volatile.Write (&vs.[i], wasAfter)
                  i <- i + 1
                elif same wasAfter d then
                  while same d <| Volatile.Read (&vs.[i]) do
                    Thread.Yield () |> ignore
                  i <- i + 1
              else
                vs <- vs'
        else
          i <- i + 1
      proceed d
    else
      d.op.Attempt d
      proceed d

  and help (d: Descriptor) (from: byref<obj>) =
    inc (&d.helpers) |> ignore
    if same (Volatile.Read (&from)) d then
      proceed d
    dec (&d.helpers) |> ignore

  let inline prepare (d: Descriptor) (ab: Op<'a, 'b>) (a: 'a) =
    d.input <- box a
    d.op <- ab :> Op

    let allAtomsCount = ab.Atoms (d, 0)

    if d.uniqAtoms.Length < allAtomsCount then
      d.uniqAtoms <- Array.zeroCreate allAtomsCount
      d.indices <- Array.zeroCreate allAtomsCount
      d.values <- Array.zeroCreate (allAtomsCount + 1)

    d.uniqAtomsCount <- 0
    for i = 0 to allAtomsCount - 1 do
      let ref = d.allAtoms.[i]
      let mutable j = 0
      while j < d.uniqAtomsCount && d.uniqAtoms.[j].id < ref.id do
        j <- j + 1
      if j = d.uniqAtomsCount || not (same d.uniqAtoms.[j] ref) then
        for k = d.uniqAtomsCount downto j + 1 do
          d.uniqAtoms.[k] <- d.uniqAtoms.[k-1]
        d.uniqAtoms.[j] <- ref
        d.uniqAtomsCount <- d.uniqAtomsCount + 1

    for i = 0 to allAtomsCount - 1 do
      let ref = d.allAtoms.[i]
      let mutable j = 0
      while not (same d.uniqAtoms.[j] ref) do
        j <- j + 1
      d.indices.[i] <- j

    for i = 0 to d.uniqAtomsCount do
      d.values.[i] <- d :> obj

  let inline waitFree (d: Descriptor) =
    while 0 <> Volatile.Read (&d.helpers) do
      Thread.Yield () |> ignore

  let atomically (d: Descriptor) (ab: Op<'a, 'b>) (a: 'a) : 'b =
    prepare d ab a
    proceed d
    let result = unbox<'b> d.values.[d.uniqAtomsCount]
    waitFree d
    result

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
