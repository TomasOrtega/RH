import Mathlib
import Formalism.PeriodIntegrals.AdelicOrbitU

noncomputable section

namespace PIW.AdelicOrbitU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

section Field

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Evaluate the numerical expressions. A detailed English derivation is pending.
-/
theorem quad_exists_not_mem (h2 : Module.finrank F E = 2) :
    ∃ a : E, a ∉ (algebraMap F E).range := by
  by_contra h
  push_neg at h
  have htop : Submodule.span F ({1} : Set E) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨c, rfl⟩ := RingHom.mem_range.mp (h x)
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
  have hle : Module.finrank F (Submodule.span F ({1} : Set E)) = 1 :=
    finrank_span_singleton one_ne_zero
  rw [htop, finrank_top, h2] at hle
  norm_num at hle

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Reduce the conclusion to the remaining proof obligations.

Simplify to obtain the desired conclusion from the available facts. It suffices to derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private lemma linearIndependent_one_of_not_mem_range {a : E} (ha : a ∉ (algebraMap F E).range) :
    LinearIndependent F ![(1 : E), a] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    refine ⟨?_, rfl⟩
    simpa using hst
  · exfalso
    apply ha
    refine ⟨-(s / t), ?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    have h' : t • a = -(s • (1 : E)) := by
      linear_combination hst
    calc (-(s / t)) • (1 : E) = t⁻¹ • (-(s • (1 : E))) := by
          rw [smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
      _ = t⁻¹ • (t • a) := by rw [h']
      _ = a := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
private lemma exists_eq_add_mul_of_finrank_two_of_linearIndependent (h2 : Module.finrank F E = 2) {a : E}
    (hli : LinearIndependent F ![(1 : E), a]) (z : E) :
    ∃ p q : F, z = algebraMap F E p + algebraMap F E q * a := by
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hb : ⇑b = ![(1 : E), a] := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  refine ⟨b.repr z 0, b.repr z 1, ?_⟩
  conv_lhs => rw [← b.sum_repr z]
  rw [Fin.sum_univ_two, hb]
  simp [Algebra.smul_def]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. Separate the alternatives or extract the components of the hypothesis. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
private lemma exists_mul_self_eq_and_sigma_eq_sub_of_not_mem (h2 : Module.finrank F E = 2)
    (hfix : ∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range) {a : E}
    (ha : a ∉ (algebraMap F E).range) :
    ∃ s t : F, a * a = algebraMap F E t + algebraMap F E s * a ∧ σ a = algebraMap F E s - a := by
  obtain ⟨t, s, hts⟩ := exists_eq_add_mul_of_finrank_two_of_linearIndependent h2 (linearIndependent_one_of_not_mem_range ha) (a * a)
  refine ⟨s, t, hts, ?_⟩
  have hσ := congrArg σ hts
  simp only [map_mul, map_add, AlgHom.commutes] at hσ
  have hne : σ a ≠ a := fun h => ha ((hfix a).mp h)
  have key : (σ a - a) * (σ a + a - algebraMap F E s) = 0 := by
    linear_combination hσ - hts
  rcases mul_eq_zero.mp key with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · linear_combination h

/- English proof (translation)
Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_sigma_sigma (h2 : Module.finrank F E = 2)
    (hfix : ∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range) (a : E) : σ (σ a) = a := by
  by_cases ha : a ∈ (algebraMap F E).range
  · rw [(hfix a).mpr ha, (hfix a).mpr ha]
  · obtain ⟨s, t, -, hs⟩ := exists_mul_self_eq_and_sigma_eq_sub_of_not_mem σ h2 hfix ha
    rw [hs, map_sub, AlgHom.commutes, hs]
    ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Simplify to obtain the desired conclusion from the available facts. Substitute using the available equality. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem quad_li [CharZero F] {θ : E} (hθ0 : θ ≠ 0) (hσθ : σ θ = -θ) :
    LinearIndependent F ![(1 : E), θ] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h' : s • (1 : E) - t • θ = 0 := by
    have := congrArg σ hst
    simp only [map_add, map_smul, map_one, hσθ, smul_neg, map_zero] at this
    linear_combination this
  have h3 : t • θ + t • θ = 0 := by linear_combination hst - h'
  have ht : t = 0 := by
    have h4 : (2 * t) • θ = 0 := by rw [two_mul, add_smul]; exact h3
    rcases smul_eq_zero.mp h4 with h | h
    · simpa using h
    · exact absurd h hθ0
  subst ht
  refine ⟨?_, rfl⟩
  simpa using hst

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem quad_exists_theta [CharZero F] (h2 : Module.finrank F E = 2)
    (hfix : ∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range) :
    ∃ θ : E, θ ≠ 0 ∧ σ θ = -θ ∧ (∃ d : F, d ≠ 0 ∧ θ * θ = algebraMap F E d) ∧
      LinearIndependent F ![(1 : E), θ] := by
  obtain ⟨a, ha⟩ := quad_exists_not_mem h2
  obtain ⟨s, t, hts, hs⟩ := exists_mul_self_eq_and_sigma_eq_sub_of_not_mem σ h2 hfix ha
  have hσθ : σ (2 * a - algebraMap F E s) = -(2 * a - algebraMap F E s) := by
    simp only [map_sub, map_mul, map_ofNat, AlgHom.commutes, hs]
    ring
  have hθ0 : 2 * a - algebraMap F E s ≠ 0 := by
    intro h
    apply ha
    refine ⟨2⁻¹ * s, ?_⟩
    have e : algebraMap F E 2⁻¹ * 2 = 1 := by
      rw [← map_ofNat (algebraMap F E) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
    rw [map_mul]
    linear_combination (-(algebraMap F E 2⁻¹)) * h + a * e
  have hsq : (2 * a - algebraMap F E s) * (2 * a - algebraMap F E s) =
      algebraMap F E (4 * t + s ^ 2) := by
    rw [map_add, map_mul, map_pow, map_ofNat]
    linear_combination 4 * hts
  have hd0 : (4 * t + s ^ 2 : F) ≠ 0 := by
    intro hd
    apply hθ0
    have h0 : (2 * a - algebraMap F E s) * (2 * a - algebraMap F E s) = 0 := by
      rw [hsq, hd, map_zero]
    exact mul_self_eq_zero.mp h0
  exact ⟨_, hθ0, hσθ, ⟨4 * t + s ^ 2, hd0, hsq⟩, quad_li σ hθ0 hσθ⟩

def quadBasis (h2 : Module.finrank F E = 2) {θ : E} (hli : LinearIndependent F ![(1 : E), θ]) :
    Module.Basis (Fin 2) F E :=
  basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem quadBasis_coe (h2 : Module.finrank F E = 2) {θ : E} (hli : LinearIndependent F ![(1 : E), θ]) :
    ⇑(quadBasis h2 hli) = ![(1 : E), θ] := by
  first
  | exact coe_basisOfLinearIndependentOfCardEqFinrank hli _
  | (unfold quadBasis; exact coe_basisOfLinearIndependentOfCardEqFinrank hli _)
  | simp [quadBasis]

end Field

section Ring

variable {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
  (h2 : Module.finrank F E = 2) {θ : E} (hli : LinearIndependent F ![(1 : E), θ])
  (R : Type) [CommRing R] [Algebra F R]

def quadBasisR : Module.Basis (Fin 2) R (R ⊗[F] E) :=
  Algebra.TensorProduct.basis R (quadBasis h2 hli)

/- English proof (translation)
Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem quadBasisR_zero : quadBasisR h2 hli R 0 = (1 : R) ⊗ₜ[F] (1 : E) := by
  first
  | (unfold quadBasisR; rw [Algebra.TensorProduct.basis_apply, quadBasis_coe]; rfl)
  | simp [quadBasisR, quadBasis_coe]

/- English proof (translation)
Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem quadBasisR_one : quadBasisR h2 hli R 1 = (1 : R) ⊗ₜ[F] θ := by
  first
  | (unfold quadBasisR; rw [Algebra.TensorProduct.basis_apply, quadBasis_coe]; rfl)
  | simp [quadBasisR, quadBasis_coe]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem quad_coord_eq (a b : R) :
    ⇑((quadBasisR h2 hli R).repr (a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] θ)) = ![a, b] := by
  have e : a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] θ =
      a • quadBasisR h2 hli R 0 + b • quadBasisR h2 hli R 1 := by
    rw [quadBasisR_zero, quadBasisR_one, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, mul_one, mul_one]
  rw [e, map_add, map_smul, map_smul, Module.Basis.repr_self, Module.Basis.repr_self]
  funext i
  fin_cases i <;> simp

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem quad_coord_zero (a b : R) : (quadBasisR h2 hli R).repr (a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] θ) 0 = a := by
  have h := congrFun (quad_coord_eq h2 hli R a b) 0
  simpa using h

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem quad_coord_one (a b : R) : (quadBasisR h2 hli R).repr (a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] θ) 1 = b := by
  have h := congrFun (quad_coord_eq h2 hli R a b) 1
  simpa using h

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem quad_decomp (z : R ⊗[F] E) :
    z = ((quadBasisR h2 hli R).repr z 0) ⊗ₜ[F] (1 : E) + ((quadBasisR h2 hli R).repr z 1) ⊗ₜ[F] θ := by
  conv_lhs => rw [← (quadBasisR h2 hli R).sum_repr z]
  rw [Fin.sum_univ_two, quadBasisR_zero, quadBasisR_one, TensorProduct.smul_tmul',
    TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one, mul_one]

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
private lemma sigR_tmul_adelic_unitary_orbits (x : R) (y : E) : sigR R σ (x ⊗ₜ[F] y) = x ⊗ₜ[F] σ y := by
  first
  | rfl
  | simp [sigR]
  | (unfold sigR; simp)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem quad_sig (hσθ : σ θ = -θ) (a b : R) :
    sigR R σ (a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] θ) = a ⊗ₜ[F] (1 : E) + (-b) ⊗ₜ[F] θ := by
  rw [map_add, sigR_tmul_adelic_unitary_orbits, sigR_tmul_adelic_unitary_orbits, map_one, hσθ, TensorProduct.tmul_neg,
    TensorProduct.neg_tmul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem quad_tmul_algebraMap (x : R) (d : F) :
    x ⊗ₜ[F] (algebraMap F E d) = (algebraMap F R d * x) ⊗ₜ[F] (1 : E) := by
  rw [show algebraMap F E d = d • (1 : E) from Algebra.algebraMap_eq_smul_one d,
    ← TensorProduct.smul_tmul, Algebra.smul_def]

include h2 hli in

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_trace {d : F} (hd : θ * θ = algebraMap F E d) (a b : R) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] θ) = 2 * a := by
  have e1 : (a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] θ) * ((1 : R) ⊗ₜ[F] θ) =
      (algebraMap F R d * b) ⊗ₜ[F] (1 : E) + a ⊗ₜ[F] θ := by
    simp only [add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hd,
      quad_tmul_algebraMap]
    abel
  rw [Algebra.trace_eq_matrix_trace (quadBasisR h2 hli R), Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, quadBasisR_zero,
    quadBasisR_one, ← Algebra.TensorProduct.one_def, mul_one, e1, quad_coord_zero, quad_coord_one]
  ring

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.
-/
theorem quad_sig_sig (hσσ : ∀ a : E, σ (σ a) = a) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x y => rw [sigR_tmul_adelic_unitary_orbits, sigR_tmul_adelic_unitary_orbits, hσσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Ring

end PIW.AdelicOrbitU
