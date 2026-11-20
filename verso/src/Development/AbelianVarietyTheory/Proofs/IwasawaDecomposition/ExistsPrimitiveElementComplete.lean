import Mathlib
open IsLocalRing Polynomial

namespace GlobalTheory

/- English proof (translation)
Use `letI := (ResidueField.map φ).toAlgebra`. Rewrite using `[aeval_def, eval₂_map, eval_map, hom_eval₂]`. Use `congr 1`.
-/
theorem residue_eval_map_eq_aeval {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R]
    [IsLocalRing R] (φ : A →+* R) [IsLocalHom φ] (P : A[X]) (x : R) :
    letI := (ResidueField.map φ).toAlgebra
    residue R ((P.map φ).eval x) = aeval (residue R x) (P.map (residue A)) := by
  letI := (ResidueField.map φ).toAlgebra
  rw [aeval_def, eval₂_map, eval_map, hom_eval₂]
  congr 1

/- English proof (translation)
Introduce `A R _ _ _ _ _ φ _ hfin hchar`. Use `letI := (ResidueField.map φ).toAlgebra`. Use `haveI : FiniteDimensional (ResidueField A) (ResidueField R) := hfin`. Use `haveI : Algebra.IsSeparable (ResidueField A) (ResidueField R) := inferInstance`. Take `⟨α, hα⟩` from `Field.exists_primitive_element (ResidueField A) (ResidueField R)`.

Establish `hint : IsIntegral (ResidueField A) α` using `Algebra.IsIntegral.isIntegral α`. Use `set p := minpoly (ResidueField A) α with hp`. Establish `hpm : p.Monic` using `minpoly.monic hint`. Establish `hlift : p ∈ lifts (residue A)` using `(lifts_iff_coeff_lifts p).2 fun n => residue_surjective (p.coeff n)`. Take `⟨q, hqmap, hqdeg, hqm⟩` from `lifts_and_degree_eq_and_monic hlift hpm`.

Establish `hqnat : q.natDegree = p.natDegree` using `natDegree_eq_of_degree_eq hqdeg`. Take `⟨θ₀, hθ₀⟩` from `residue_surjective (R := R) α`. Establish `hmon : (q.map φ).Monic` using `hqm.map φ`. Establish `h1 : (q.map φ).eval θ₀ ∈ maximalIdeal R`. Rewrite using `[← residue_eq_zero_iff, residue_eval_map_eq_aeval, hqmap, hθ₀]`.

Conclude with `minpoly.aeval _ _`. Establish `hder : ∀ x : R, residue R x = α → IsUnit ((q.derivative.map φ).eval x)`. Introduce `x hx`. Rewrite using `[← residue_ne_zero_iff_isUnit, residue_eval_map_eq_aeval, ← derivative_map, hqmap, hx]`. Establish `hsep : (minpoly (ResidueField A) α).Separable` using `Algebra.IsSeparable.isSeparable (ResidueField A) α`.

Conclude with `hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)`. Establish `h2 : IsUnit ((q.map φ).derivative.eval θ₀)`. Rewrite using `[derivative_map]`. Conclude with `hder θ₀ hθ₀`. Take `⟨θ, hroot, hθθ₀⟩` from `(IsAdicComplete.henselianRing R (maximalIdeal R)).is_henselian _ hmon θ₀ h1 (h2.map _)`.

Establish `hθ : residue R θ = α`. Rewrite using `[← hθ₀, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]`. Conclude with `hθθ₀`. Use `⟨θ, q, hqm, hroot, hder θ hθ, ?_, ?_⟩` and prove the remaining obligations. Introduce `r`.

Establish `hr : residue R r ∈ Algebra.adjoin (ResidueField A) {α}`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, IntermediateField.mem_toSubalgebra, hα]`. Conclude with `IntermediateField.mem_top`. Rewrite `hr` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨pb, hpb⟩` from `hr`.

Take `⟨P, hP⟩` from `map_surjective (residue A) residue_surjective pb`. Use `⟨P, ?_⟩` and prove the remaining obligations. Rewrite using `[← residue_eq_zero_iff, map_sub, residue_eval_map_eq_aeval, hP, hθ, sub_eq_zero]`. Conclude with `hpb.symm`. Introduce `P hdeg hmem i`.

Rewrite `hmem` using `[← residue_eq_zero_iff, residue_eval_map_eq_aeval, hθ]`. Establish `hz : P.map (residue A) = 0`. Assume the negation of the conclusion as `hne`. Use `minpoly.degree_le_of_ne_zero (ResidueField A) α hne hmem` as an intermediate fact. Establish `h3` using `natDegree_le_natDegree this`.

Establish `h4 : (P.map (residue A)).natDegree ≤ P.natDegree` using `natDegree_map_le`. Rewrite `h3` using `[← hp]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← residue_eq_zero_iff, ← coeff_map, hz, coeff_zero]`.
-/
theorem exists_hensel_generator_of_residue_finite : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (φ : A →+* R) [IsLocalHom φ], (ResidueField.map φ).Finite → CharZero (ResidueField A) → ∃ (θ : R) (q : Polynomial A), q.Monic ∧ (q.map φ).eval θ = 0 ∧ IsUnit ((q.derivative.map φ).eval θ) ∧ (∀ r : R, ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R) ∧ ∀ P : Polynomial A, P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R → ∀ i, P.coeff i ∈ maximalIdeal A := by
  intro A R _ _ _ _ _ φ _ hfin hchar
  letI := (ResidueField.map φ).toAlgebra
  haveI : FiniteDimensional (ResidueField A) (ResidueField R) := hfin
  haveI : Algebra.IsSeparable (ResidueField A) (ResidueField R) := inferInstance
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField A) (ResidueField R)
  have hint : IsIntegral (ResidueField A) α := Algebra.IsIntegral.isIntegral α
  set p := minpoly (ResidueField A) α with hp
  have hpm : p.Monic := minpoly.monic hint
  have hlift : p ∈ lifts (residue A) :=
    (lifts_iff_coeff_lifts p).2 fun n => residue_surjective (p.coeff n)
  obtain ⟨q, hqmap, hqdeg, hqm⟩ := lifts_and_degree_eq_and_monic hlift hpm
  have hqnat : q.natDegree = p.natDegree := natDegree_eq_of_degree_eq hqdeg
  obtain ⟨θ₀, hθ₀⟩ := residue_surjective (R := R) α
  have hmon : (q.map φ).Monic := hqm.map φ
  have h1 : (q.map φ).eval θ₀ ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, residue_eval_map_eq_aeval, hqmap, hθ₀]
    exact minpoly.aeval _ _
  have hder : ∀ x : R, residue R x = α → IsUnit ((q.derivative.map φ).eval x) := by
    intro x hx
    rw [← residue_ne_zero_iff_isUnit, residue_eval_map_eq_aeval, ← derivative_map, hqmap, hx]
    have hsep : (minpoly (ResidueField A) α).Separable :=
      Algebra.IsSeparable.isSeparable (ResidueField A) α
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)
  have h2 : IsUnit ((q.map φ).derivative.eval θ₀) := by
    rw [derivative_map]; exact hder θ₀ hθ₀
  obtain ⟨θ, hroot, hθθ₀⟩ :=
    (IsAdicComplete.henselianRing R (maximalIdeal R)).is_henselian _ hmon θ₀ h1 (h2.map _)
  have hθ : residue R θ = α := by
    rw [← hθ₀, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hθθ₀
  refine ⟨θ, q, hqm, hroot, hder θ hθ, ?_, ?_⟩
  · intro r
    have hr : residue R r ∈ Algebra.adjoin (ResidueField A) {α} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
        IntermediateField.mem_toSubalgebra, hα]
      exact IntermediateField.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hr
    obtain ⟨pb, hpb⟩ := hr
    obtain ⟨P, hP⟩ := map_surjective (residue A) residue_surjective pb
    refine ⟨P, ?_⟩
    rw [← residue_eq_zero_iff, map_sub, residue_eval_map_eq_aeval, hP, hθ, sub_eq_zero]
    exact hpb.symm
  · intro P hdeg hmem i
    rw [← residue_eq_zero_iff, residue_eval_map_eq_aeval, hθ] at hmem
    have hz : P.map (residue A) = 0 := by
      by_contra hne
      have := minpoly.degree_le_of_ne_zero (ResidueField A) α hne hmem
      have h3 := natDegree_le_natDegree this
      have h4 : (P.map (residue A)).natDegree ≤ P.natDegree := natDegree_map_le
      rw [← hp] at h3
      omega
    rw [← residue_eq_zero_iff, ← coeff_map, hz, coeff_zero]

end GlobalTheory
