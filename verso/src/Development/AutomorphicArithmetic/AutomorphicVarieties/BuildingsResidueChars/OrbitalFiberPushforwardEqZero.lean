import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs

open MulAction

/- English proof (translation)
Introduce `H Y _ _ H₀ k hidx htriv hk hfin`. Establish `hout : ∀ (o : orbitRel.Quotient H Y) (y : Y), (Quotient.mk (orbitRel H Y) y : orbitRel.Quotient H Y) = o ↔ y ∈ orbit H o.out`. Introduce `o y`. Rewrite using `[← orbitRel_apply, ← Quotient.eq (r := orbitRel H Y), Quotient.out_eq]`. Establish `hkeq : ∀ (x y : Y), y ∈ orbit H x → k y = k x`.

Introduce and unpack `x y ⟨h, rfl⟩`. Conclude with `hk h x`. Use `set S : Finset Y := hfin.toFinset with hS`. Establish `hmem : ∀ y, y ∈ S ↔ k y ≠ 0`. Introduce `y`.

Simplify using `[hS]`. Set `q : Y → orbitRel.Quotient H Y` to `fun y => Quotient.mk (orbitRel H Y) y`. Establish `h1 : ∑ᶠ y, k y = ∑ y ∈ S, k y` using `finsum_eq_sum k hfin`. Establish `h2 : UpperTheory.V.Z.Sym.gq H₀ k = ∑ o ∈ S.image q, k o.out / (H₀.relIndex (stabilizer H o.out) : ℂ)`. Unfold `UpperTheory.V.Z.Sym.gq`.

Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `o ho`. Establish `hne : k o.out ≠ 0`. Introduce `h0`. Conclude with `ho (by simp [h0])`.

Simplify using `only [Finset.coe_image]`. Conclude with `⟨o.out, by simpa [hmem] using hne, Quotient.out_eq o⟩`. Rewrite using `[h1, h2, ← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image q) (g := q) (fun y hy => Finset.mem_image_of_mem q hy), Finset.sum_div]`. Use `Finset.sum_congr rfl fun o ho => ?_` and prove the remaining obligations. Take `⟨y₀, hy₀, hy₀o⟩` from `Finset.mem_image.mp ho`.

Establish `hne : k o.out ≠ 0`. Rewrite using `[← hkeq o.out y₀ ((hout o y₀).mp hy₀o)]`. Conclude with `(hmem y₀).mp hy₀`. Establish `hset : ((S.filter fun y => q y = o : Finset Y) : Set Y) = orbit H o.out`. Use extensionality with `y`.

Simplify using `only [Finset.coe_filter, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => (hout o y).mp h.2`. Introduce `h`. Conclude with `⟨(hmem y).mpr (by rw [hkeq _ _ h]; exact hne), (hout o y).mpr h⟩`.

Establish `hcard : (S.filter fun y => q y = o).card = (stabilizer H o.out).index`. Rewrite using `[index_stabilizer, ← hset, Set.ncard_coe_finset]`. Establish `hle : H₀ ≤ stabilizer H o.out` using `fun z hz => htriv z hz _`. Establish `hmul` using `Subgroup.relIndex_mul_index hle`. Establish `hsum : ∑ y ∈ S with q y = o, k y = ((stabilizer H o.out).index : ℂ) * k o.out`.

Rewrite using `[Finset.sum_congr rfl (g := fun _ => k o.out), Finset.sum_const, hcard, nsmul_eq_mul]`. Introduce `y hy`. Conclude with `hkeq _ _ ((hout o y).mp (Finset.mem_filter.mp hy).2)`. Rewrite `hidx` using `[← hmul]`. Establish `ha : ((H₀.relIndex (stabilizer H o.out) : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (left_ne_zero_of_mul hidx)`.

Establish `hb : (((stabilizer H o.out).index : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (right_ne_zero_of_mul hidx)`. Rewrite using `[hsum, ← hmul, Nat.cast_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem UpperTheory.orbitalFiber_pushforward_eq_zero :
    UpperTheory.V.Z.Sym.Glob.Fib.PushZero := by
  intro H Y _ _ H₀ k hidx htriv hk hfin
  classical
  have hout : ∀ (o : orbitRel.Quotient H Y) (y : Y),
      (Quotient.mk (orbitRel H Y) y : orbitRel.Quotient H Y) = o ↔ y ∈ orbit H o.out := by
    intro o y
    rw [← orbitRel_apply, ← Quotient.eq (r := orbitRel H Y), Quotient.out_eq]
  have hkeq : ∀ (x y : Y), y ∈ orbit H x → k y = k x := by
    rintro x y ⟨h, rfl⟩
    exact hk h x
  set S : Finset Y := hfin.toFinset with hS
  have hmem : ∀ y, y ∈ S ↔ k y ≠ 0 := by
    intro y; simp [hS]
  let q : Y → orbitRel.Quotient H Y := fun y => Quotient.mk (orbitRel H Y) y
  have h1 : ∑ᶠ y, k y = ∑ y ∈ S, k y := finsum_eq_sum k hfin
  have h2 : UpperTheory.V.Z.Sym.gq H₀ k =
      ∑ o ∈ S.image q, k o.out / (H₀.relIndex (stabilizer H o.out) : ℂ) := by
    unfold UpperTheory.V.Z.Sym.gq
    apply finsum_eq_sum_of_support_subset
    intro o ho
    have hne : k o.out ≠ 0 := by
      intro h0
      exact ho (by simp [h0])
    simp only [Finset.coe_image]
    exact ⟨o.out, by simpa [hmem] using hne, Quotient.out_eq o⟩
  rw [h1, h2, ← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image q) (g := q)
    (fun y hy => Finset.mem_image_of_mem q hy), Finset.sum_div]
  refine Finset.sum_congr rfl fun o ho => ?_
  obtain ⟨y₀, hy₀, hy₀o⟩ := Finset.mem_image.mp ho
  have hne : k o.out ≠ 0 := by
    rw [← hkeq o.out y₀ ((hout o y₀).mp hy₀o)]
    exact (hmem y₀).mp hy₀
  have hset : ((S.filter fun y => q y = o : Finset Y) : Set Y) = orbit H o.out := by
    ext y
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    constructor
    · exact fun h => (hout o y).mp h.2
    · intro h
      exact ⟨(hmem y).mpr (by rw [hkeq _ _ h]; exact hne), (hout o y).mpr h⟩
  have hcard : (S.filter fun y => q y = o).card = (stabilizer H o.out).index := by
    rw [index_stabilizer, ← hset, Set.ncard_coe_finset]
  have hle : H₀ ≤ stabilizer H o.out := fun z hz => htriv z hz _
  have hmul := Subgroup.relIndex_mul_index hle
  have hsum : ∑ y ∈ S with q y = o, k y = ((stabilizer H o.out).index : ℂ) * k o.out := by
    rw [Finset.sum_congr rfl (g := fun _ => k o.out), Finset.sum_const, hcard, nsmul_eq_mul]
    intro y hy
    exact hkeq _ _ ((hout o y).mp (Finset.mem_filter.mp hy).2)
  rw [← hmul] at hidx
  have ha : ((H₀.relIndex (stabilizer H o.out) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (left_ne_zero_of_mul hidx)
  have hb : (((stabilizer H o.out).index : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (right_ne_zero_of_mul hidx)
  rw [hsum, ← hmul, Nat.cast_mul]
  field_simp
