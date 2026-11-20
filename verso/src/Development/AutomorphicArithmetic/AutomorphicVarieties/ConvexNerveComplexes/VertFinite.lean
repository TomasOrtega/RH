import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed

open Set UpperTheory.V.ConeExtensionAcyclic

/- English proof (translation)
Introduce `E Y _ _ q hq K hK hKp`. Use `choose S hSf hSU using fun x (hx : x ∈ K) => hq x (hKp hx)`. Take `⟨t, ht⟩` from `hK.elim_nhds_subcover' (fun x hx => {h' : E | ∀ y ∉ S x hx, 1 < q y h'}) (fun x hx => hSU x hx)`. Establish `hfin : (⋃ x ∈ (t : Set K), S x.1 x.2).Finite` using `t.finite_toSet.biUnion fun x _ => hSf x.1 x.2`. Use `Set.Finite.of_finite_image (f := fun v : E => {y : Y | q y v = 1}) ?_ ?_` and prove the remaining obligations.

Use `hfin.finite_subsets.subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, ⟨hvK, hvV⟩, rfl⟩`. Establish `hv` using `ht hvK`. Simplify using `only [Set.mem_iUnion] at hv`. Take `⟨x, hxt, hvx⟩` from `hv`.

Use `show {y : Y | q y v = 1} ⊆ _`. Introduce `y hy`. Simplify using `only [Set.mem_iUnion, Finset.mem_coe]`. Use `⟨x, hxt, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hyS`.

Establish `h1` using `(hvx : ∀ y ∉ S x.1 x.2, 1 < q y v) y hyS`. Simplify using `only [Set.mem_setOf_eq] at hy`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce and unpack `v ⟨_, hvV⟩ w ⟨_, hwV⟩ hvw`. Establish `key : w - v = 0`.

Use `hvV.2 (w - v) fun y hy => ?_` and prove the remaining obligations. Establish `hy' : y ∈ {y : Y | q y w = 1}`. Establish `e : {y : Y | q y v = 1} = {y : Y | q y w = 1}` using `hvw`. Rewrite using `[← e]`. Conclude with `hy`.

Simplify using `only [Set.mem_setOf_eq] at hy'`. Simplify using `[map_sub, hy, hy']`. Conclude with `(sub_eq_zero.1 key).symm`.
-/
theorem UpperTheory.V.ConeExtensionAcyclic.vert_finite :
    ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : Y → E →L[ℝ] ℝ}, LocFin q → ∀ K : Set E, IsCompact K → K ⊆ poly q → {h | h ∈ K ∧ IsVert q h}.Finite := by
  intro E Y _ _ q hq K hK hKp
  choose S hSf hSU using fun x (hx : x ∈ K) => hq x (hKp hx)
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x hx => {h' : E | ∀ y ∉ S x hx, 1 < q y h'})
    (fun x hx => hSU x hx)
  have hfin : (⋃ x ∈ (t : Set K), S x.1 x.2).Finite :=
    t.finite_toSet.biUnion fun x _ => hSf x.1 x.2
  refine Set.Finite.of_finite_image (f := fun v : E => {y : Y | q y v = 1}) ?_ ?_
  · refine hfin.finite_subsets.subset ?_
    rintro _ ⟨v, ⟨hvK, hvV⟩, rfl⟩
    have hv := ht hvK
    simp only [Set.mem_iUnion] at hv
    obtain ⟨x, hxt, hvx⟩ := hv
    show {y : Y | q y v = 1} ⊆ _
    intro y hy
    simp only [Set.mem_iUnion, Finset.mem_coe]
    refine ⟨x, hxt, ?_⟩
    by_contra hyS
    have h1 := (hvx : ∀ y ∉ S x.1 x.2, 1 < q y v) y hyS
    simp only [Set.mem_setOf_eq] at hy
    linarith
  · rintro v ⟨_, hvV⟩ w ⟨_, hwV⟩ hvw
    have key : w - v = 0 := by
      refine hvV.2 (w - v) fun y hy => ?_
      have hy' : y ∈ {y : Y | q y w = 1} := by
        have e : {y : Y | q y v = 1} = {y : Y | q y w = 1} := hvw
        rw [← e]
        exact hy
      simp only [Set.mem_setOf_eq] at hy'
      simp [map_sub, hy, hy']
    exact (sub_eq_zero.1 key).symm
