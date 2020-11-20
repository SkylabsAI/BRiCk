# Thread-local-state modalities
The main theory to work with TLS is in
[modalities.v](modalities.v).
This theory provides general modalities that work as guards on assertions in
order to preserve soundness. Normally they are invisible (implicit) if you only
work "thread-locally", in the sense that you only work on a single and not
switching between ECs, PDs, or CPUs. When your work involve "cross-thread"
operations, then these modalities will show up. As already mentioned in one of
our meetings, weak-memory means more restricted use of invariants---the same
applies for any other kind of thread-local state. For example:
- if you're sending resources across EC, you'll probably have to deal with
  resource restrictions for cross-EC.
- if you're sending resources across PD, you'll probably have to deal with
  resource restrictions for cross-EC/PD.
- if you're sending resources across CPUs, you'll probably have to deal with all
  of the resource restrictions.

## The restriction
The restriction is simply: you can only send resource `P : mpred` across a
thread-local state `K` (`K ∈ PowerSet({EC, PD, TLB, View}`) only if `P` is
independent or *objective* w.r.t `K`. Intuitively, such objectivity of `P` means
that `∀ (i j : ti), i ≠_K j → P i ≡ P j`, i.e. `P i` and `P j` are the same if
`i` and `j` only differ in `K`.

Some examples of objectivity:
* a ghost own `own γ a` is objective w.r.t the whole `ti`
* `byte_at` is objective w.r.t `{EC, PD, TLB}`, but not `View`
* A non-objective `P` w.r.t `K` can be made objective by `explicitly
  quantifying` the concrete value `k : K` for `P`, so that `P` is no longer tie
  to some implicit local state. This is the key mechanism to transfer
  non-objective resources across TLS (see more below).

## The modalities
The main modalities are:
- explicit quantification: `monPred_exactly_at`, with notation `@(L,k) P`
- objective-with `monPred_objectively_with`, with notation `<obj>_L P`, and the
  related typeclass `ObjectiveWith L P`
- full objective `monPred_objectively`, with notation `<obj> P`, and the related
  typeclass `Objective P`.
- observation `monPred_atleast`, with notation `⊒{L} k`.

Many of these modalities mentioned the "monotone lens" `L : MLens I J`
(tentative notation, `I -ML> J`, which is basically a lens from `I` to `J` that
preserves monotonicity which is needed by `monPred`. In this situation we will
have `L` simply as a projection from `ti` to some subset of `ti`. This allows us
to have some separation and can work on each type of TLS more modularly.

Intutively:
- `@(L,k) P` says that `P` holds at the TLS where the `L` component is `k`,
  while the other components are taken from the current implicit TLS. More
  specificly `@(L_PD,pd) P` says that `P` holds at the PD `pd`, and at the other
  components of the current "thread".
- This means that `@(L_PD,pd) P` ignores the PD component of the current thread,
  and therefore we have `ObjectiveWith L_PD (@(L_PD,pd) P)`. In general we have
  `ObjectiveWith L ((@L, k) P)`.
- `<obj>_L P` *objectifies* `P`, in the sense that it asserts the ownership of
  `P` at any value `k` of the component `L`, while the other components are
  taken from the current implicit TLS. Naturally `ObjectiveWith L (<obj>_L P)`.
- In a sense, we can look at `<obj>_L` as a `∀`, and `@(L,k)` as a `∃`.
- Using `monPred_exactly_at` and `monPred_objectively_with`, we can iteratively
  turn a resource `P` to full objectivity. A fully objective `P` means that `P`
  is independently with the current implicit TLS, either because the contents of
  `P` do not use some thread-local information, or because the thread-local
  information used are already made explicit. In this case, we have `Objective
  P`.
- `<obj> P` simplify fully objectifies `P`. Naturally `Objective (<obj> P)`.
- `⊒{L} j`, where `L : MLens I J` and `j : J`, says that the current component
  `J` is at least `j`. For example `⊒{L_PD} pd` says that the current PD is
  `pd`.

To turn `P` fully objective:
- We have rules like `ObjectiveWith L.r P -> ObjectiveWith L (@(L.l, k) P)`,
  where `L : I -ML> (K * H), L.l : I -ML> K, L.r : I -ML> H`. The rule says that
  if `P` is already objective w.r.t `L.r`, `@(L.l, k)` makes `P` objective
  w.r.t. `L.l`, so in combination `@(L.l, k) P` is object w.r.t the whole `L`.
- We have `ObjectiveWith L_id P <-> Objective P`, where `L_id` is the identity
  lens of type `MLens I I` (`I -ML> I`).
- For example, we have `ObjectiveWith L_PD_EC_TLB byte_at`, so we have
  `ObjectiveWith L_id (@(View, V) byte_at))`, and therefore `Objective (@(View,
  V) byte_at)`.

## Putting fully objective resources in an invariant
The restriction above is realized in the restriction in the invariant. Generally
we have the following rules:
* `inv_alloc : |> <obj> P ={E}=> inv N P`
* `inv_access : inv N P |-- |={E,E\N)> |> <obj> P ** (|> <obj> P ={E\N,E}=*
  emp)`.

Instead, we can derive the rules with almost the same old API, but assuming
`Objective P` :
* `inv_alloc' : Objective P -> |> P ={E}=> inv N P`
* `inv_access' : Objective P -> inv N P |-- |={E,E\N)> |> P ** (|> P ={E\N,E}=*
  emp)`.

The latter can help reduce efforts in porting existing proofs to the new setup.
I have implemented some preliminary instances so that the side condition
`Objective P` can be discharged easily. But that is not complete and not well
tested yet.

Also, currently the rules `inv_alloc/access` are still used somewhere. The
proposal is to fully adopt the one with the side condition. There is a related
issue cpp2v#663, where we would shadow Iris's `inv/cinv` with our versions with
the side condition `Objective P`.

Currently, `own` is already shadowed, because its interface is the same (`own`
is fully objective). However, the theory of `own` is not lifted yet to `mpred`.