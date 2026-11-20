import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs

open MulAction

/- English proof (translation)
Establish `h1 : ∀ i, ∑ᶠ p, wi i p = ∑ᶠ o ∈ F i '' S i, w o`. Introduce `i`. Rewrite using `[finsum_mem_image (hinj i), finsum_mem_def]`. Use `congr 1`. Use function extensionality and compare the values at `p`.

Distinguish the cases in `hp : p ∈ S i`. Rewrite using `[Set.indicator_of_mem hp, (hF i p hp).2]`. Rewrite using `[Set.indicator_of_notMem hp, hwi i p hp]`. Establish `hsub : ∀ i, F i '' S i ⊆ B`. Introduce and unpack `i _ ⟨p, hp, rfl⟩`.

Conclude with `(hF i p hp).1`. Establish `hI : {i | (S i).Nonempty}.Finite`. Set `g : {i | (S i).Nonempty} → B` to `fun i => ⟨F i.1 i.2.some, (hF _ _ i.2.some_mem).1⟩`. Establish `hg : Function.Injective g` using `fun i j h => Subtype.ext (hij _ _ _ i.2.some_mem _ j.2.some_mem (congrArg Subtype.val h))`. Use `haveI := hB.to_subtype`.

Conclude with `Set.finite_coe_iff.1 (Finite.of_injective g hg)`. Establish `hU : B = ⋃ i ∈ {i | (S i).Nonempty}, F i '' S i`. Use extensionality with `o`. Simplify using `only [Set.mem_iUnion]`. Prove the components needed by the constructor for the conclusion.

Introduce `ho`. Take `⟨i, p, hp, rfl⟩` from `hs o ho`. Conclude with `⟨i, ⟨p, hp⟩, p, hp, rfl⟩`. Introduce and unpack `⟨i, _, ho⟩`. Conclude with `hsub i ho`.

Establish `h2 : ∑ᶠ o, w o = ∑ᶠ o ∈ B, w o`. Rewrite using `[finsum_mem_def]`. Use `congr 1`. Use function extensionality and compare the values at `o`. Distinguish the cases in `ho : o ∈ B`.

Rewrite using `[Set.indicator_of_mem ho]`. Rewrite using `[Set.indicator_of_notMem ho, hw o ho]`. Rewrite using `[h2, hU, finsum_mem_biUnion _ hI (fun i _ => hB.subset (hsub i)), finsum_mem_def]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Distinguish the cases in `hi : i ∈ {i | (S i).Nonempty}`. Rewrite using `[Set.indicator_of_mem hi, h1]`. Rewrite using `[Set.indicator_of_notMem hi, h1]`. Establish `: S i = ∅` using `Set.not_nonempty_iff_eq_empty.1 hi`. Rewrite using `[this, Set.image_empty, finsum_mem_empty]`.

Introduce `i _ j _ hne`. Use `Set.disjoint_left.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨p, hp, rfl⟩ ⟨q, hq, h⟩`. Conclude with `hne (hij i j p hp q hq h.symm)`.
-/
private theorem fib_abs {O I : Type} {P : I → Type} (F : ∀ i, P i → O) (S : ∀ i, Set (P i)) (B : Set O) (hB : B.Finite)
    (w : O → ℂ) (wi : ∀ i, P i → ℂ) (hw : ∀ o, o ∉ B → w o = 0) (hwi : ∀ i p, p ∉ S i → wi i p = 0)
    (hF : ∀ i, ∀ p ∈ S i, F i p ∈ B ∧ wi i p = w (F i p)) (hs : ∀ o ∈ B, ∃ i, ∃ p ∈ S i, F i p = o)
    (hij : ∀ i j, ∀ p ∈ S i, ∀ q ∈ S j, F i p = F j q → i = j) (hinj : ∀ i, Set.InjOn (F i) (S i)) :
    ∑ᶠ o, w o = ∑ᶠ i, ∑ᶠ p, wi i p := by
  classical
  have h1 : ∀ i, ∑ᶠ p, wi i p = ∑ᶠ o ∈ F i '' S i, w o := by
    intro i
    rw [finsum_mem_image (hinj i), finsum_mem_def]
    congr 1
    funext p
    by_cases hp : p ∈ S i
    · rw [Set.indicator_of_mem hp, (hF i p hp).2]
    · rw [Set.indicator_of_notMem hp, hwi i p hp]
  have hsub : ∀ i, F i '' S i ⊆ B := by
    rintro i _ ⟨p, hp, rfl⟩
    exact (hF i p hp).1
  have hI : {i | (S i).Nonempty}.Finite := by
    let g : {i | (S i).Nonempty} → B := fun i => ⟨F i.1 i.2.some, (hF _ _ i.2.some_mem).1⟩
    have hg : Function.Injective g := fun i j h =>
      Subtype.ext (hij _ _ _ i.2.some_mem _ j.2.some_mem (congrArg Subtype.val h))
    haveI := hB.to_subtype
    exact Set.finite_coe_iff.1 (Finite.of_injective g hg)
  have hU : B = ⋃ i ∈ {i | (S i).Nonempty}, F i '' S i := by
    ext o
    simp only [Set.mem_iUnion]
    constructor
    · intro ho
      obtain ⟨i, p, hp, rfl⟩ := hs o ho
      exact ⟨i, ⟨p, hp⟩, p, hp, rfl⟩
    · rintro ⟨i, _, ho⟩
      exact hsub i ho
  have h2 : ∑ᶠ o, w o = ∑ᶠ o ∈ B, w o := by
    rw [finsum_mem_def]
    congr 1
    funext o
    by_cases ho : o ∈ B
    · rw [Set.indicator_of_mem ho]
    · rw [Set.indicator_of_notMem ho, hw o ho]
  rw [h2, hU, finsum_mem_biUnion _ hI (fun i _ => hB.subset (hsub i)), finsum_mem_def]
  · congr 1
    funext i
    by_cases hi : i ∈ {i | (S i).Nonempty}
    · rw [Set.indicator_of_mem hi, h1]
    · rw [Set.indicator_of_notMem hi, h1]
      have : S i = ∅ := Set.not_nonempty_iff_eq_empty.1 hi
      rw [this, Set.image_empty, finsum_mem_empty]
  · intro i _ j _ hne
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, h⟩
    exact hne (hij i j p hp q hq h.symm)

/- English proof (translation)
Establish `h0 : H₀.map (MulAut.conj h).toMonoidHom = H₀`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `hn.conj_mem y hy h`.

Introduce `hz`. Use `⟨h⁻¹ * z * h, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using hn.conj_mem z hz h⁻¹`. Simplify using `[mul_assoc]`. Rewrite using `[stabilizer_smul_eq_stabilizer_map_conj]`.

Use `conv_lhs => rw [← h0]`. Conclude with `Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj h).injective`.
-/
private theorem rel_smul {H X : Type} [Group H] [MulAction H X] (H₀ : Subgroup H) (hn : H₀.Normal) (h : H) (x : X) :
    H₀.relIndex (stabilizer H (h • x)) = H₀.relIndex (stabilizer H x) := by
  have h0 : H₀.map (MulAut.conj h).toMonoidHom = H₀ := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hn.conj_mem y hy h
    · intro hz
      refine ⟨h⁻¹ * z * h, ?_, ?_⟩
      · simpa using hn.conj_mem z hz h⁻¹
      · simp [mul_assoc]
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  conv_lhs => rw [← h0]
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj h).injective

/- English proof (translation)
Establish `: (Quotient.mk (orbitRel H X) x).out ∈ orbit H x` using `orbitRel_apply.1 (Quotient.exact (Quotient.out_eq (Quotient.mk (orbitRel H X) x)))`. Take `⟨h, hh⟩` from `this`. Conclude with `⟨h, hh.symm⟩`.
-/
private theorem out_mk {H X : Type} [Group H] [MulAction H X] (x : X) :
    ∃ h : H, (Quotient.mk (orbitRel H X) x).out = h • x := by
  have : (Quotient.mk (orbitRel H X) x).out ∈ orbit H x :=
    orbitRel_apply.1 (Quotient.exact (Quotient.out_eq (Quotient.mk (orbitRel H X) x)))
  obtain ⟨h, hh⟩ := this
  exact ⟨h, hh.symm⟩

/- English proof (translation)
The claim follows from `Quotient.sound (orbitRel_apply.2 ⟨h, rfl⟩)`.
-/
private theorem mk_smul {H X : Type} [Group H] [MulAction H X] (h : H) (x : X) :
    Quotient.mk (orbitRel H X) (h • x) = Quotient.mk (orbitRel H X) x :=
  Quotient.sound (orbitRel_apply.2 ⟨h, rfl⟩)

/- English proof (translation)
Introduce `H X I _ _ H₀ k Hi Yi _ _ φ e ki hn hk hT he hinj hki hke hs hu`. Unfold `UpperTheory.V.Z.Sym.gq`. Establish `hex : ∀ x x' : X, Quotient.mk (orbitRel H X) x' = Quotient.mk (orbitRel H X) x → ∃ h : H, h • x = x'` using `fun x x' h => orbitRel_apply.1 (Quotient.exact h)`. Use `fib_abs (fun i (p : orbitRel.Quotient (Hi i) (Yi i)) => (Quotient.mk (orbitRel H X) (e i p.out) : orbitRel.Quotient H X)) (fun i => {p | ki i p.out ≠ 0}) {o | k o.out ≠ 0} ?_ _ _ ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Take `⟨T, hT⟩` from `hT`.

Use `(T.finite_toSet.image (Quotient.mk (orbitRel H X))).subset fun o ho => ?_` and prove the remaining obligations. Take `⟨h, s, hs, ho⟩` from `hT _ ho`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[← mk_smul h s, ← ho]`. Conclude with `Quotient.out_eq o`.

Introduce `o ho`. Establish `: k o.out = 0` using `not_not.1 ho`. Rewrite using `[this, zero_div]`. Introduce `i p hp`. Establish `: ki i p.out = 0` using `not_not.1 hp`.

Rewrite using `[this, zero_div]`. Introduce `i p hp`. Establish `hp' : ki i p.out ≠ 0` using `hp`. Take `⟨h, hh⟩` from `out_mk (H := H) (e i p.out)`. Establish `hv : k (Quotient.mk (orbitRel H X) (e i p.out)).out = ki i p.out` using `by rw [hh, hk, hke i _ hp']`.

Use `⟨fun h0 => hp' (hv ▸ h0), ?_⟩` and prove the remaining obligations. Establish `hst : (stabilizer (Hi i) p.out).map (φ i) = stabilizer H (e i p.out)`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, rfl⟩`.

Rewrite using `[mem_stabilizer_iff, ← he, mem_stabilizer_iff.1 ha]`. Introduce `hg`. Take `⟨_, a, rfl⟩` from `hu i i _ _ g hp' hp' hg`. Use `⟨a, hinj i ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[he]`.

Conclude with `hg`. Use `show _ = k (Quotient.mk (orbitRel H X) (e i p.out)).out / (H₀.relIndex (stabilizer H (Quotient.mk (orbitRel H X) (e i p.out)).out) : ℂ)`. Rewrite using `[hv, hh, rel_smul H₀ hn, Subgroup.relIndex_comap, hst]`. Introduce `o ho`. Take `⟨i, y, h, hy, hx⟩` from `hs _ ho`.

Take `⟨a, ha⟩` from `out_mk (H := Hi i) y`. Use `⟨i, Quotient.mk (orbitRel (Hi i) (Yi i)) y, ?_, ?_⟩` and prove the remaining obligations. Use `show ki i (Quotient.mk (orbitRel (Hi i) (Yi i)) y).out ≠ 0`. Rewrite using `[ha, hki]` and apply the resulting hypothesis. Use `show Quotient.mk (orbitRel H X) (e i (Quotient.mk (orbitRel (Hi i) (Yi i)) y).out) = o`.

Rewrite using `[ha, he, mk_smul, ← mk_smul h, ← hx]`. Conclude with `Quotient.out_eq o`. Introduce `i j p hp q hq hpq`. Take `⟨h, hh⟩` from `hex _ _ hpq.symm`. Conclude with `(hu i j _ _ h hp hq hh).1`.

Introduce `i p hp q hq hpq`. Take `⟨h, hh⟩` from `hex _ _ (Eq.symm hpq)`. Take `⟨_, a, rfl⟩` from `hu i i _ _ h hp hq hh`. Rewrite `hh` using `[← he]`. Establish `h3` using `hinj i hh`.

Rewrite using `[← Quotient.out_eq p, ← Quotient.out_eq q, ← h3]`. Conclude with `(mk_smul a _).symm`.
-/
theorem UpperTheory.orbitalFiber_decomposition :
    UpperTheory.V.Z.Sym.Glob.Fib.Decomp := by
  intro H X I _ _ H₀ k Hi Yi _ _ φ e ki hn hk hT he hinj hki hke hs hu
  unfold UpperTheory.V.Z.Sym.gq
  have hex : ∀ x x' : X, Quotient.mk (orbitRel H X) x' = Quotient.mk (orbitRel H X) x → ∃ h : H, h • x = x' :=
    fun x x' h => orbitRel_apply.1 (Quotient.exact h)
  refine fib_abs (fun i (p : orbitRel.Quotient (Hi i) (Yi i)) => (Quotient.mk (orbitRel H X) (e i p.out) : orbitRel.Quotient H X))
    (fun i => {p | ki i p.out ≠ 0}) {o | k o.out ≠ 0} ?_ _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · obtain ⟨T, hT⟩ := hT
    refine (T.finite_toSet.image (Quotient.mk (orbitRel H X))).subset fun o ho => ?_
    obtain ⟨h, s, hs, ho⟩ := hT _ ho
    refine ⟨s, hs, ?_⟩
    rw [← mk_smul h s, ← ho]
    exact Quotient.out_eq o
  · intro o ho
    have : k o.out = 0 := not_not.1 ho
    rw [this, zero_div]
  · intro i p hp
    have : ki i p.out = 0 := not_not.1 hp
    rw [this, zero_div]
  · intro i p hp
    have hp' : ki i p.out ≠ 0 := hp
    obtain ⟨h, hh⟩ := out_mk (H := H) (e i p.out)
    have hv : k (Quotient.mk (orbitRel H X) (e i p.out)).out = ki i p.out := by rw [hh, hk, hke i _ hp']
    refine ⟨fun h0 => hp' (hv ▸ h0), ?_⟩
    have hst : (stabilizer (Hi i) p.out).map (φ i) = stabilizer H (e i p.out) := by
      ext g
      constructor
      · rintro ⟨a, ha, rfl⟩
        rw [mem_stabilizer_iff, ← he, mem_stabilizer_iff.1 ha]
      · intro hg
        obtain ⟨_, a, rfl⟩ := hu i i _ _ g hp' hp' hg
        refine ⟨a, hinj i ?_, rfl⟩
        rw [he]
        exact hg
    show _ = k (Quotient.mk (orbitRel H X) (e i p.out)).out /
      (H₀.relIndex (stabilizer H (Quotient.mk (orbitRel H X) (e i p.out)).out) : ℂ)
    rw [hv, hh, rel_smul H₀ hn, Subgroup.relIndex_comap, hst]
  · intro o ho
    obtain ⟨i, y, h, hy, hx⟩ := hs _ ho
    obtain ⟨a, ha⟩ := out_mk (H := Hi i) y
    refine ⟨i, Quotient.mk (orbitRel (Hi i) (Yi i)) y, ?_, ?_⟩
    · show ki i (Quotient.mk (orbitRel (Hi i) (Yi i)) y).out ≠ 0
      rwa [ha, hki]
    · show Quotient.mk (orbitRel H X) (e i (Quotient.mk (orbitRel (Hi i) (Yi i)) y).out) = o
      rw [ha, he, mk_smul, ← mk_smul h, ← hx]
      exact Quotient.out_eq o
  · intro i j p hp q hq hpq
    obtain ⟨h, hh⟩ := hex _ _ hpq.symm
    exact (hu i j _ _ h hp hq hh).1
  · intro i p hp q hq hpq
    obtain ⟨h, hh⟩ := hex _ _ (Eq.symm hpq)
    obtain ⟨_, a, rfl⟩ := hu i i _ _ h hp hq hh
    rw [← he] at hh
    have h3 := hinj i hh
    rw [← Quotient.out_eq p, ← Quotient.out_eq q, ← h3]
    exact (mk_smul a _).symm
