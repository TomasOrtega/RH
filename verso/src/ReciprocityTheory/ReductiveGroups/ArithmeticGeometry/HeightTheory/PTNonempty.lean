import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField Cardinal

/- English proof (translation)
Take `⟨S, hS⟩` from `hfg`. Use `haveI : Countable (MvPolynomial (S : Set Ω) K) := by first`. Consider the case `infer_instance`. Consider the case `exact Cardinal.mk_le_aleph0_iff.mp (MvPolynomial.cardinal_mk_le_max.trans (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl))`. Consider the case `exact Cardinal.mk_le_aleph0_iff.mp (MvPolynomial.cardinalMk_le_max_lift.trans (max_le (max_le (Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0) (Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0)) le_rfl))`.

Consider the case `exact Cardinal.mk_le_aleph0_iff.mp (MvPolynomial.cardinalMk_le_max.trans (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl))`. Set `f : MvPolynomial (S : Set Ω) K × MvPolynomial (S : Set Ω) K → Ω` to `fun pq => MvPolynomial.aeval (fun x : (S : Set Ω) => (x : Ω)) pq.1 / MvPolynomial.aeval (fun x : (S : Set Ω) => (x : Ω)) pq.2`. Establish `hf : Function.Surjective f`. Introduce `x`. Establish `hx : x ∈ IntermediateField.adjoin K (S : Set Ω)`.

Rewrite using `[hS]`. Conclude with `IntermediateField.mem_top`. Take `⟨r, hr, t, ht, rfl⟩` from `(IntermediateField.mem_adjoin_iff_div).mp hx`. Rewrite `hr`, `ht` using `[Algebra.adjoin_eq_range]`. Take `⟨p, rfl⟩` from `hr`.

Take `⟨q, rfl⟩` from `ht`. Conclude with `⟨(p, q), rfl⟩`. Conclude with `hf.countable`.
-/
private lemma countable_of_intermediateField_fg {K Ω : Type} [Field K] [Countable K] [Field Ω] [Algebra K Ω]
    (hfg : (⊤ : IntermediateField K Ω).FG) : Countable Ω := by
  obtain ⟨S, hS⟩ := hfg
  haveI : Countable (MvPolynomial (S : Set Ω) K) := by
    first
    | infer_instance
    | exact Cardinal.mk_le_aleph0_iff.mp (MvPolynomial.cardinal_mk_le_max.trans
        (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl))
    | exact Cardinal.mk_le_aleph0_iff.mp (MvPolynomial.cardinalMk_le_max_lift.trans
        (max_le (max_le (Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0)
          (Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0)) le_rfl))
    | exact Cardinal.mk_le_aleph0_iff.mp (MvPolynomial.cardinalMk_le_max.trans
        (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl))
  let f : MvPolynomial (S : Set Ω) K × MvPolynomial (S : Set Ω) K → Ω := fun pq =>
    MvPolynomial.aeval (fun x : (S : Set Ω) => (x : Ω)) pq.1 /
      MvPolynomial.aeval (fun x : (S : Set Ω) => (x : Ω)) pq.2
  have hf : Function.Surjective f := by
    intro x
    have hx : x ∈ IntermediateField.adjoin K (S : Set Ω) := by
      rw [hS]; exact IntermediateField.mem_top
    obtain ⟨r, hr, t, ht, rfl⟩ := (IntermediateField.mem_adjoin_iff_div).mp hx
    rw [Algebra.adjoin_eq_range] at hr ht
    obtain ⟨p, rfl⟩ := hr
    obtain ⟨q, rfl⟩ := ht
    exact ⟨(p, q), rfl⟩
  exact hf.countable

/- English proof (translation)
Use `haveI hKc : Countable K := by first`. Consider the case `infer_instance`. Consider the case `exact (Module.finBasis ℚ K).equivFun.injective.countable`. Use `haveI hΩc : Countable Ω := countable_of_intermediateField_fg hfg`. Use `letI : Algebra K ℂ := sg.toAlgebra`.

Use `haveI : FaithfulSMul K ℂ := by first`. Consider the case `infer_instance`. Consider the case `exact (faithfulSMul_iff_algebraMap_injective K ℂ).mpr sg.injective`. Use `haveI : FaithfulSMul K Ω := by first`. Consider the case `infer_instance`.

Consider the case `exact (faithfulSMul_iff_algebraMap_injective K Ω).mpr (algebraMap K Ω).injective`. Take `⟨s, hs⟩` from `exists_isTranscendenceBasis K Ω`. Take `⟨t, ht⟩` from `exists_isTranscendenceBasis K ℂ`. Establish `hC : Cardinal.aleph0 < Cardinal.mk ℂ`. Rewrite using `[Cardinal.mk_complex]`.

Conclude with `Cardinal.aleph0_lt_continuum`. Establish `hKle : Cardinal.mk K ≤ Cardinal.aleph0` using `Cardinal.mk_le_aleph0`. Establish `htt : Cardinal.aleph0 < Cardinal.mk t` using `by first`. Consider the case `(by_contra hle`. Establish `h` using `IsAlgClosed.cardinal_le_max_transcendence_basis _ ht`.

Conclude with `absurd (h.trans (max_le (max_le hKle (not_lt.mp hle)) le_rfl)) (not_le.mpr hC))`. Consider the case `(have h := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht hKle hC`. Rewrite `h` using `[Cardinal.lift_inj]`. Rewrite `hC` using `[h]`. Conclude with `hC)`.

Establish `hst : Cardinal.mk s ≤ Cardinal.mk t` using `Cardinal.mk_le_aleph0.trans htt.le`. Take `⟨e⟩` from `(Cardinal.le_def _ _).mp hst`. Set `u : s → ℂ` to `fun i => ((e i : t) : ℂ)`. Establish `hu : AlgebraicIndependent K u` using `ht.1.comp e e.injective`. Set `E` to `hs.1.aevalEquiv.symm.trans hu.aevalEquiv`.

Set `φ : Algebra.adjoin K (Set.range (Subtype.val : s → Ω)) →ₐ[K] ℂ` to `(Algebra.adjoin K (Set.range u)).val.comp E.toAlgHom`. Establish `hφ : Function.Injective φ` using `Subtype.val_injective.comp E.injective`. Use `letI : Algebra (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) ℂ := φ.toRingHom.toAlgebra`. Use `haveI : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω := hs.isAlgebraic`. Apply the tactic sequence `try haveI : NoZeroSMulDivisors (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) ℂ := NoZeroSMulDivisors.of_algebraMap_injective hφ`.

Apply the tactic sequence `try haveI : FaithfulSMul (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) ℂ := (faithfulSMul_iff_algebraMap_injective _ ℂ).mpr hφ`. Apply the tactic sequence `try haveI : NoZeroSMulDivisors (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω := NoZeroSMulDivisors.of_algebraMap_injective Subtype.val_injective`. Apply the tactic sequence `try haveI : FaithfulSMul (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω := (faithfulSMul_iff_algebraMap_injective _ Ω).mpr Subtype.val_injective`. Set `g : Ω →ₐ[Algebra.adjoin K (Set.range (Subtype.val : s → Ω))] ℂ` to `IsAlgClosed.lift`. Use `⟨g.toRingHom, ?_⟩` and prove the remaining obligations.

Use extensionality with `k`. Establish `h1 : algebraMap K Ω k = algebraMap (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω (algebraMap K (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) k)` using `by first`. Consider the case `rfl`. Consider the case `exact IsScalarTower.algebraMap_apply _ _ _ k`. Use `show g (algebraMap K Ω k) = sg k`.

Rewrite using `[h1, g.commutes]`. Conclude with `φ.commutes k`.
-/
theorem exists_embedding_over {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (hfg : (⊤ : IntermediateField K Ω).FG) (sg : K →+* ℂ) :
    ∃ P : Ω →+* ℂ, P.comp (algebraMap K Ω) = sg := by
  haveI hKc : Countable K := by
    first
    | infer_instance
    | exact (Module.finBasis ℚ K).equivFun.injective.countable
  haveI hΩc : Countable Ω := countable_of_intermediateField_fg hfg
  letI : Algebra K ℂ := sg.toAlgebra
  haveI : FaithfulSMul K ℂ := by
    first
    | infer_instance
    | exact (faithfulSMul_iff_algebraMap_injective K ℂ).mpr sg.injective
  haveI : FaithfulSMul K Ω := by
    first
    | infer_instance
    | exact (faithfulSMul_iff_algebraMap_injective K Ω).mpr (algebraMap K Ω).injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K Ω
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K ℂ
  have hC : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  have hKle : Cardinal.mk K ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  have htt : Cardinal.aleph0 < Cardinal.mk t := by
    first
    | (by_contra hle
       have h := IsAlgClosed.cardinal_le_max_transcendence_basis _ ht
       exact absurd (h.trans (max_le (max_le hKle (not_lt.mp hle)) le_rfl)) (not_le.mpr hC))
    | (have h := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht hKle hC
       rw [Cardinal.lift_inj] at h
       rw [h] at hC
       exact hC)
  have hst : Cardinal.mk s ≤ Cardinal.mk t := Cardinal.mk_le_aleph0.trans htt.le
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hst
  let u : s → ℂ := fun i => ((e i : t) : ℂ)
  have hu : AlgebraicIndependent K u := ht.1.comp e e.injective
  let E := hs.1.aevalEquiv.symm.trans hu.aevalEquiv
  let φ : Algebra.adjoin K (Set.range (Subtype.val : s → Ω)) →ₐ[K] ℂ :=
    (Algebra.adjoin K (Set.range u)).val.comp E.toAlgHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp E.injective
  letI : Algebra (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) ℂ := φ.toRingHom.toAlgebra
  haveI : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω :=
    hs.isAlgebraic
  try haveI : NoZeroSMulDivisors (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) ℂ :=
    NoZeroSMulDivisors.of_algebraMap_injective hφ
  try haveI : FaithfulSMul (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) ℂ :=
    (faithfulSMul_iff_algebraMap_injective _ ℂ).mpr hφ
  try haveI : NoZeroSMulDivisors (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω :=
    NoZeroSMulDivisors.of_algebraMap_injective Subtype.val_injective
  try haveI : FaithfulSMul (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ Ω).mpr Subtype.val_injective
  let g : Ω →ₐ[Algebra.adjoin K (Set.range (Subtype.val : s → Ω))] ℂ := IsAlgClosed.lift
  refine ⟨g.toRingHom, ?_⟩
  ext k
  have h1 : algebraMap K Ω k = algebraMap (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) Ω
      (algebraMap K (Algebra.adjoin K (Set.range (Subtype.val : s → Ω))) k) := by
    first
    | rfl
    | exact IsScalarTower.algebraMap_apply _ _ _ k
  show g (algebraMap K Ω k) = sg k
  rw [h1, g.commutes]
  exact φ.commutes k

end ReciprocityTheory.ChartRestriction.G.T0
