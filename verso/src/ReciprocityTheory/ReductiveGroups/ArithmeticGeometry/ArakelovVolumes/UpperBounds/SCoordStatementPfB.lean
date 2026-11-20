import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.SCoB

open MvPolynomial

noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

/- English proof (translation)
Establish `hY : AlgebraicIndependent K (φK ∘ y)` using `hy.map' φK.toRingHom.injective`. Assume the negation of the conclusion as `hc`. Establish `h1 : AlgebraicIndependent K (fun o : Option ιB => o.elim (φK a) (φK ∘ y))` using `AlgebraicIndependent.option_iff.mpr ⟨hY, hc⟩`. Establish `h2 : AlgebraicIndependent K (fun o : Option ιB => o.elim a y)`. Use `AlgebraicIndependent.of_comp φK ?_` and prove the remaining obligations.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `funext o; cases o <;> rfl`. Conclude with `((AlgebraicIndependent.option_iff.mp h2).2) ha`.
-/
theorem isAlgebraic_map {ιB : Type} {y : ιB → Ω} (hy : AlgebraicIndependent K y) [Algebra K ℂ]
    (φK : Ω →ₐ[K] ℂ) {a : Ω} (ha : IsAlgebraic (Algebra.adjoin K (Set.range y)) a) :
    IsAlgebraic (Algebra.adjoin K (Set.range (φK ∘ y))) (φK a) := by
  have hY : AlgebraicIndependent K (φK ∘ y) := hy.map' φK.toRingHom.injective
  by_contra hc
  have h1 : AlgebraicIndependent K (fun o : Option ιB => o.elim (φK a) (φK ∘ y)) :=
    AlgebraicIndependent.option_iff.mpr ⟨hY, hc⟩
  have h2 : AlgebraicIndependent K (fun o : Option ιB => o.elim a y) := by
    refine AlgebraicIndependent.of_comp φK ?_
    convert h1 using 1
    funext o; cases o <;> rfl
  exact ((AlgebraicIndependent.option_iff.mp h2).2) ha

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `letI : Algebra K ℂ := σ.toAlgebra`. Establish `hcomm : ∀ k, φ (algebraMap K Ω k) = algebraMap K ℂ k` using `fun k => by`. Rewrite using `[RingHom.algebraMap_toAlgebra, ← hφ]`. Both sides reduce to the same expression. Set `φK : Ω →ₐ[K] ℂ` to `{ toRingHom := φ, commutes' := hcomm }`.

Establish `hφK : ∀ a, φK a = φ a` using `fun _ => rfl`. Set `T : R × Fin (N + 1) → ℂ` to `fun p => t p.1 p.2`. Establish `hT : AlgebraicIndependent K T`. Rewrite using `[AlgebraicIndependent, injective_iff_map_eq_zero]`. Introduce `Q hQ`.

Assume the negation of the conclusion as `h`. Conclude with `ht Q h (by simpa [aeval_def, RingHom.algebraMap_toAlgebra] using hQ)`. Set `Y : ιB → ℂ` to `φK ∘ y`. Set `S : R × {j // j ≠ j0} → ℂ` to `fun q => t q.1 q.2`. Set `Z : ιB ⊕ (R × {j // j ≠ j0}) → ℂ` to `Sum.elim Y S`.

Establish `hYZ : Algebra.adjoin K (Set.range Y) ≤ Algebra.adjoin K (Set.range Z)` using `Algebra.adjoin_mono (by rintro _ ⟨b, rfl⟩; exact ⟨Sum.inl b, rfl⟩)`. Set `M` to `AlgebraicIndependent.matroid K ℂ`. Establish `hsub : Set.range T ⊆ M.closure (Set.range Z)`. Rewrite using `[AlgebraicIndependent.matroid_closure_eq]`. Set `A'` to `Subalgebra.algebraicClosure (Algebra.adjoin K (Set.range Z)) ℂ`.

Establish `hin : ∀ q, S q ∈ A'` using `fun q => by`. Rewrite using `[Subalgebra.mem_algebraicClosure]`. Establish `hm : S q ∈ Algebra.adjoin K (Set.range Z)` using `Algebra.subset_adjoin ⟨Sum.inr q, rfl⟩`. Conclude with `isAlgebraic_algebraMap (⟨S q, hm⟩ : Algebra.adjoin K (Set.range Z))`. Establish `hu : ∀ j, φ (u j) ∈ A'` using `fun j => by`.

Rewrite using `[Subalgebra.mem_algebraicClosure]`. Establish `h1` using `isAlgebraic_map hy.1 φK (hy.isAlgebraic.isAlgebraic (u j))`. Conclude with `h1.tower_top_of_subalgebra_le hYZ`. Introduce and unpack `_ ⟨⟨i, j⟩, rfl⟩`. Use `show t i j ∈ A'`.

Distinguish the cases in `hj : j = j0`. Substitute `hj` using the available equality. Establish `h2` using `hrel i`. Rewrite `h2` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ j), hu0, map_one, mul_one]`. Establish `h3 : t i j = -∑ k ∈ Finset.univ.erase j, t i k * φ (u k)` using `eq_neg_of_add_eq_zero_left h2`.

Rewrite using `[h3]`. Use `A'.neg_mem (A'.sum_mem fun k hk => A'.mul_mem ?_ (hu k))` and prove the remaining obligations. Conclude with `hin (i, ⟨k, Finset.ne_of_mem_erase hk⟩)`. Conclude with `hin (i, ⟨j, hj⟩)`. Establish `hI : M.Indep (Set.range T)` using `AlgebraicIndependent.matroid_indep_iff.mpr hT.to_subtype_range`.

Establish `h0` using `hI.encard_le_eRk_of_subset hsub`. Rewrite `h0` using `[Matroid.eRk_closure_eq]`. Establish `h1` using `hT.injective.encard_range.trans h0`. Establish `h2` using `M.eRk_le_encard (Set.range Z)`. Set `rng` to `Finset.univ.image Z`.

Establish `hrng : Set.range Z = ↑rng` using `by simp [rng]`. Establish `h3 : (Set.range Z).encard = rng.card` using `by rw [hrng, Set.encard_coe_eq_coe_finsetCard]`. Establish `h4 : rng.card ≤ Fintype.card (ιB ⊕ R × {j // j ≠ j0})` using `Finset.card_image_le.trans (by simp)`. Establish `hcardT : ENat.card (R × Fin (N + 1)) = ((Fintype.card R * (N + 1) : ℕ) : ℕ∞)`. Simplify using `[ENat.card_eq_coe_fintype_card]`.

Establish `hcardZ : Fintype.card (ιB ⊕ R × {j // j ≠ j0}) = Fintype.card ιB + Fintype.card R * N`. Simplify using `[Fintype.card_sum, Fintype.card_prod]`. Establish `hRN : Fintype.card R * (N + 1) = Fintype.card R * N + Fintype.card R` using `by ring`. Establish `hle : Fintype.card R * (N + 1) ≤ rng.card`. Use `h1.trans (h2.trans h3.le)` as an intermediate fact.

Rewrite `this` using `[hcardT]`. Conclude with `this` after adjusting the coercions. Establish `heq : rng.card = Fintype.card (ιB ⊕ R × {j // j ≠ j0})` using `le_antisymm h4 (by rw [hcardZ]; omega)`. Establish `hinj : Function.Injective Z`. Use `Finset.card_image_iff.mp (heq.trans Finset.card_univ.symm)` as an intermediate fact.

Conclude with `fun a b hab => this (Finset.mem_coe.2 (Finset.mem_univ a)) (Finset.mem_coe.2 (Finset.mem_univ b)) hab`. Establish `hindZ : M.Indep (Set.range Z)`. Rewrite using `[Matroid.indep_iff_eRk_eq_encard_of_finite (Set.finite_range Z)]`. Use `le_antisymm h2 ?_` and prove the remaining obligations. Rewrite using `[h3]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `(show rng.card ≤ Fintype.card R * (N + 1) by rw [heq, hcardZ]; omega)` after adjusting the coercions. Use `_ = ENat.card (R × Fin (N + 1)) := hcardT.symm`. Use `_ ≤ _ := h1`. Establish `hZ : AlgebraicIndependent K Z` using `(algebraicIndependent_subtype_range hinj).mp (AlgebraicIndependent.matroid_indep_iff.mp hindZ)`.

Establish `hZ' : AlgebraicIndependent K (Sum.elim S Y)`. Use `hZ.comp (Equiv.sumComm _ _) (Equiv.injective _)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `funext a; cases a <;> rfl`. Establish `hS : AlgebraicIndependent (Algebra.adjoin K (Set.range Y)) S` using `(AlgebraicIndependent.sumElim_iff.mp hZ').2`.

Set `R0` to `Algebra.adjoin K (Set.range y)`. Establish `hmap : ∀ s : R0, (φK.comp R0.val) s ∈ Algebra.adjoin K (Set.range Y)`. Introduce `s`. Establish `h : φK (s : Ω) ∈ R0.map φK` using `Subalgebra.mem_map.mpr ⟨s, s.2, rfl⟩`. Rewrite `h` using `[AlgHom.map_adjoin, ← Set.range_comp]`.

Conclude with `h`. Set `ρ : R0 →ₐ[K] Algebra.adjoin K (Set.range Y)` to `(φK.comp R0.val).codRestrict _ hmap`. Use `letI : Algebra Ω ℂ := φ.toAlgebra`. Use `letI : Algebra R0 ℂ := (φ.comp (algebraMap R0 Ω)).toAlgebra`. Establish `hS0 : AlgebraicIndependent R0 S`.

Use `AlgebraicIndependent.of_ringHom_of_comp_eq (S := Algebra.adjoin K (Set.range Y)) (B := ℂ) ρ.toRingHom (RingHom.id ℂ) ?_ ?_ ?_` and prove the remaining obligations. Simplify using `using hS`. Introduce `a b h`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `φ.injective` to reduce the goal to its premises.

Conclude with `congrArg Subtype.val h`. Use extensionality with `s`. Both sides reduce to the same expression. Establish `hSΩ : AlgebraicIndependent Ω S`. Establish `htow : IsScalarTower R0 Ω ℂ` using `IsScalarTower.of_algebraMap_eq (fun _ => rfl)`.

Establish `halg` using `hy.isAlgebraic`. Conclude with `@AlgebraicIndependent.extendScalars _ R0 ℂ S Ω _ _ _ _ _ _ htow _ hS0 halg`. Introduce `p hp hev`. Apply `hp` to reduce the goal to its premises. Apply `hSΩ` to reduce the goal to its premises.

Simplify `hev` using `[aeval_def, RingHom.algebraMap_toAlgebra]`.
-/
theorem gen_indep {ιB R : Type} [Fintype ιB] [Fintype R] {N : ℕ} (σ : K →+* ℂ) (φ : Ω →+* ℂ)
    (hφ : φ.comp (algebraMap K Ω) = σ) {y : ιB → Ω} (hy : IsTranscendenceBasis K y)
    (j0 : Fin (N + 1)) (u : Fin (N + 1) → Ω) (hu0 : u j0 = 1) (t : R → Fin (N + 1) → ℂ)
    (ht : ∀ Q : MvPolynomial (R × Fin (N + 1)) K, Q ≠ 0 → eval₂ σ (fun p => t p.1 p.2) Q ≠ 0)
    (hrel : ∀ i, ∑ j, t i j * φ (u j) = 0) (hcard : Fintype.card ιB ≤ Fintype.card R) :
    ∀ p : MvPolynomial (R × {j // j ≠ j0}) Ω, p ≠ 0 → eval₂ φ (fun q => t q.1 q.2) p ≠ 0 := by
  classical
  letI : Algebra K ℂ := σ.toAlgebra
  have hcomm : ∀ k, φ (algebraMap K Ω k) = algebraMap K ℂ k := fun k => by
    rw [RingHom.algebraMap_toAlgebra, ← hφ]; rfl
  let φK : Ω →ₐ[K] ℂ := { toRingHom := φ, commutes' := hcomm }
  have hφK : ∀ a, φK a = φ a := fun _ => rfl
  let T : R × Fin (N + 1) → ℂ := fun p => t p.1 p.2
  have hT : AlgebraicIndependent K T := by
    rw [AlgebraicIndependent, injective_iff_map_eq_zero]
    intro Q hQ
    by_contra h
    exact ht Q h (by simpa [aeval_def, RingHom.algebraMap_toAlgebra] using hQ)
  let Y : ιB → ℂ := φK ∘ y
  let S : R × {j // j ≠ j0} → ℂ := fun q => t q.1 q.2
  let Z : ιB ⊕ (R × {j // j ≠ j0}) → ℂ := Sum.elim Y S
  have hYZ : Algebra.adjoin K (Set.range Y) ≤ Algebra.adjoin K (Set.range Z) :=
    Algebra.adjoin_mono (by rintro _ ⟨b, rfl⟩; exact ⟨Sum.inl b, rfl⟩)
  let M := AlgebraicIndependent.matroid K ℂ

  have hsub : Set.range T ⊆ M.closure (Set.range Z) := by
    rw [AlgebraicIndependent.matroid_closure_eq]
    let A' := Subalgebra.algebraicClosure (Algebra.adjoin K (Set.range Z)) ℂ
    have hin : ∀ q, S q ∈ A' := fun q => by
      rw [Subalgebra.mem_algebraicClosure]
      have hm : S q ∈ Algebra.adjoin K (Set.range Z) := Algebra.subset_adjoin ⟨Sum.inr q, rfl⟩
      exact isAlgebraic_algebraMap (⟨S q, hm⟩ : Algebra.adjoin K (Set.range Z))
    have hu : ∀ j, φ (u j) ∈ A' := fun j => by
      rw [Subalgebra.mem_algebraicClosure]
      have h1 := isAlgebraic_map hy.1 φK (hy.isAlgebraic.isAlgebraic (u j))
      exact h1.tower_top_of_subalgebra_le hYZ
    rintro _ ⟨⟨i, j⟩, rfl⟩
    show t i j ∈ A'
    by_cases hj : j = j0
    · subst hj
      have h2 := hrel i
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hu0, map_one, mul_one] at h2
      have h3 : t i j = -∑ k ∈ Finset.univ.erase j, t i k * φ (u k) := eq_neg_of_add_eq_zero_left h2
      rw [h3]
      refine A'.neg_mem (A'.sum_mem fun k hk => A'.mul_mem ?_ (hu k))
      exact hin (i, ⟨k, Finset.ne_of_mem_erase hk⟩)
    · exact hin (i, ⟨j, hj⟩)
  have hI : M.Indep (Set.range T) :=
    AlgebraicIndependent.matroid_indep_iff.mpr hT.to_subtype_range
  have h0 := hI.encard_le_eRk_of_subset hsub
  rw [Matroid.eRk_closure_eq] at h0
  have h1 := hT.injective.encard_range.trans h0
  have h2 := M.eRk_le_encard (Set.range Z)
  let rng := Finset.univ.image Z
  have hrng : Set.range Z = ↑rng := by simp [rng]
  have h3 : (Set.range Z).encard = rng.card := by rw [hrng, Set.encard_coe_eq_coe_finsetCard]
  have h4 : rng.card ≤ Fintype.card (ιB ⊕ R × {j // j ≠ j0}) :=
    Finset.card_image_le.trans (by simp)
  have hcardT : ENat.card (R × Fin (N + 1)) = ((Fintype.card R * (N + 1) : ℕ) : ℕ∞) := by
    simp [ENat.card_eq_coe_fintype_card]
  have hcardZ : Fintype.card (ιB ⊕ R × {j // j ≠ j0}) = Fintype.card ιB + Fintype.card R * N := by
    simp [Fintype.card_sum, Fintype.card_prod]
  have hRN : Fintype.card R * (N + 1) = Fintype.card R * N + Fintype.card R := by ring
  have hle : Fintype.card R * (N + 1) ≤ rng.card := by
    have := h1.trans (h2.trans h3.le)
    rw [hcardT] at this
    exact_mod_cast this
  have heq : rng.card = Fintype.card (ιB ⊕ R × {j // j ≠ j0}) :=
    le_antisymm h4 (by rw [hcardZ]; omega)
  have hinj : Function.Injective Z := by
    have := Finset.card_image_iff.mp (heq.trans Finset.card_univ.symm)
    exact fun a b hab => this (Finset.mem_coe.2 (Finset.mem_univ a)) (Finset.mem_coe.2 (Finset.mem_univ b)) hab
  have hindZ : M.Indep (Set.range Z) := by
    rw [Matroid.indep_iff_eRk_eq_encard_of_finite (Set.finite_range Z)]
    refine le_antisymm h2 ?_
    rw [h3]
    calc (rng.card : ℕ∞) ≤ ((Fintype.card R * (N + 1) : ℕ) : ℕ∞) := by
          exact_mod_cast (show rng.card ≤ Fintype.card R * (N + 1) by rw [heq, hcardZ]; omega)
      _ = ENat.card (R × Fin (N + 1)) := hcardT.symm
      _ ≤ _ := h1
  have hZ : AlgebraicIndependent K Z :=
    (algebraicIndependent_subtype_range hinj).mp (AlgebraicIndependent.matroid_indep_iff.mp hindZ)
  have hZ' : AlgebraicIndependent K (Sum.elim S Y) := by
    have := hZ.comp (Equiv.sumComm _ _) (Equiv.injective _)
    convert this using 1
    funext a; cases a <;> rfl
  have hS : AlgebraicIndependent (Algebra.adjoin K (Set.range Y)) S :=
    (AlgebraicIndependent.sumElim_iff.mp hZ').2
  let R0 := Algebra.adjoin K (Set.range y)
  have hmap : ∀ s : R0, (φK.comp R0.val) s ∈ Algebra.adjoin K (Set.range Y) := by
    intro s
    have h : φK (s : Ω) ∈ R0.map φK := Subalgebra.mem_map.mpr ⟨s, s.2, rfl⟩
    rw [AlgHom.map_adjoin, ← Set.range_comp] at h
    exact h
  let ρ : R0 →ₐ[K] Algebra.adjoin K (Set.range Y) := (φK.comp R0.val).codRestrict _ hmap
  letI : Algebra Ω ℂ := φ.toAlgebra
  letI : Algebra R0 ℂ := (φ.comp (algebraMap R0 Ω)).toAlgebra
  have hS0 : AlgebraicIndependent R0 S := by
    refine AlgebraicIndependent.of_ringHom_of_comp_eq (S := Algebra.adjoin K (Set.range Y)) (B := ℂ)
      ρ.toRingHom (RingHom.id ℂ) ?_ ?_ ?_
    · simpa using hS
    · intro a b h
      apply Subtype.ext
      apply φ.injective
      exact congrArg Subtype.val h
    · ext s; rfl
  have hSΩ : AlgebraicIndependent Ω S := by
    have htow : IsScalarTower R0 Ω ℂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have halg := hy.isAlgebraic
    exact @AlgebraicIndependent.extendScalars _ R0 ℂ S Ω _ _ _ _ _ _ htow _ hS0 halg
  intro p hp hev
  apply hp
  apply hSΩ
  simpa [aeval_def, RingHom.algebraMap_toAlgebra] using hev

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.SCoB
