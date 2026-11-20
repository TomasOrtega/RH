import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.MemALImage

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolV

open Formalism.L2.SG.Pf.NcVal Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, pow_zero, VolOrdW.absV_one]`. Consider the case `succ n ih => rw [pow_succ, VolOrdW.absV_mul, ih, pow_succ]`.
-/
theorem absV_pow (x : Fv F v) (n : ℕ) : absV v (x ^ n) = absV v x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, VolOrdW.absV_one]
  | succ n ih => rw [pow_succ, VolOrdW.absV_mul, ih, pow_succ]

/- English proof (translation)
Use `haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.locallyCompact_Fv v`. Use `haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v`. Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩`. Use `haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _`.

Use `haveI : IsTopologicalAddGroup (Fv F v ⊗[F] E) := IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)`. Set `b` to `Module.finBasis (Fv F v) (Fv F v ⊗[F] E)`. Set `eR : (Fv F v ⊗[F] E) ≃L[Fv F v] (Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v)` to `{ b.equivFun with continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }`. Use `haveI : SecondCountableTopology (Fv F v ⊗[F] E) := eR.toHomeomorph.secondCountableTopology`. Use `haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩`.

Use `haveI : BorelSpace (ι → Fv F v ⊗[F] E) := Pi.borelSpace`. Set `e0 : (ι → Fv F v ⊗[F] E) ≃ₗ[Fv F v] (ι × Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v)` to `(LinearEquiv.piCongrRight fun _ : ι => b.equivFun).trans (LinearEquiv.curry (Fv F v) (Fv F v) ι (Fin _)).symm`. Set `eV : (ι → Fv F v ⊗[F] E) ≃L[Fv F v] (ι × Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v)` to `{ e0 with continuous_toFun := IsModuleTopology.continuous_of_linearMap e0.toLinearMap continuous_invFun := IsModuleTopology.continuous_of_linearMap e0.symm.toLinearMap }`. Establish `hLM` using `PI.NglqJacSplitW.linModulusV_of (PI.NglqJacSplitW.linModulus_of PI.NglqJacSplitW.diagonal_one_jacobian)`. Rewrite using `[hLM (Fv F v) (ι → Fv F v ⊗[F] E) (ι × Fin _) ⟨eV⟩ f hf μ inferInstance S hS, PI.UnitaryGroupMassFormula.LocJacTyp.BM.modF_Fv v _ hf]`.

Both sides reduce to the same expression.
-/
theorem meas_image (ι : Type) [Fintype ι] [DecidableEq ι] (μ : Measure (ι → Fv F v ⊗[F] E))
    [μ.IsAddHaarMeasure] (f : (ι → Fv F v ⊗[F] E) →ₗ[Fv F v] (ι → Fv F v ⊗[F] E))
    (hf : LinearMap.det f ≠ 0) (S : Set (ι → Fv F v ⊗[F] E)) (hS : MeasurableSet S) :
    μ (f '' S) = ENNReal.ofReal (absV v (LinearMap.det f)) * μ S := by
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.locallyCompact_Fv v
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
  haveI : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  let b := Module.finBasis (Fv F v) (Fv F v ⊗[F] E)
  let eR : (Fv F v ⊗[F] E) ≃L[Fv F v] (Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    { b.equivFun with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }
  haveI : SecondCountableTopology (Fv F v ⊗[F] E) := eR.toHomeomorph.secondCountableTopology
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (ι → Fv F v ⊗[F] E) := Pi.borelSpace
  let e0 : (ι → Fv F v ⊗[F] E) ≃ₗ[Fv F v]
      (ι × Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    (LinearEquiv.piCongrRight fun _ : ι => b.equivFun).trans
      (LinearEquiv.curry (Fv F v) (Fv F v) ι (Fin _)).symm
  let eV : (ι → Fv F v ⊗[F] E) ≃L[Fv F v]
      (ι × Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    { e0 with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e0.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e0.symm.toLinearMap }
  have hLM := PI.NglqJacSplitW.linModulusV_of
    (PI.NglqJacSplitW.linModulus_of PI.NglqJacSplitW.diagonal_one_jacobian)
  rw [hLM (Fv F v) (ι → Fv F v ⊗[F] E) (ι × Fin _) ⟨eV⟩ f hf μ inferInstance S hS,
    PI.UnitaryGroupMassFormula.LocJacTyp.BM.modF_Fv v _ hf]
  rfl

section Big

variable (r : ℕ)

def famL (g : Fv F v) (θ : Fv F v ⊗[F] E) (p : Fin (r + 1) × Fin (r + 1)) :
    (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E) :=
  if p.1 < p.2 then g • LinearMap.id else if p.1 = p.2 then aL v g θ else LinearMap.id

def bigL (g : Fv F v) (θ : Fv F v ⊗[F] E) :
    (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) :=
  LinearMap.pi fun p => (famL v r g θ p).comp (LinearMap.proj p)

/- English proof (translation)
Establish `hr : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2`. Rewrite using `[Module.finrank_baseChange]`. Conclude with `hfin`. Establish `hs : LinearMap.det (g • (LinearMap.id : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E))) = g ^ 2`. Rewrite using `[LinearMap.det_smul, LinearMap.det_id, hr, mul_one]`.

Establish `ha` using `det_aL v hfin g θ Δ hθ hΔ hΔ0`. Take `⟨i, j⟩` from `p`. Simplify using `only [Prod.swap_prod_mk]`. Break down `lt_trichotomy i j with h | h | h` into its components or cases. Establish `h1 : ¬ j < i` using `not_lt.2 h.le`.

Establish `h2 : j ≠ i` using `h.ne'`. Simplify using `only [famL, if_pos h, if_neg h1, if_neg h2, hs, LinearMap.det_id, mul_one]`. Substitute `h` using the available equality. Simplify using `only [famL, lt_irrefl, if_false, if_true, ha, sq]`. Establish `h1 : ¬ i < j` using `not_lt.2 h.le`.

Establish `h2 : i ≠ j` using `h.ne'`. Simplify using `only [famL, if_pos h, if_neg h1, if_neg h2, hs, LinearMap.det_id, one_mul]`.
-/
theorem det_famL_mul (hfin : Module.finrank F E = 2) (g : Fv F v) (θ Δ : Fv F v ⊗[F] E)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (hΔ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0)
    (hΔ0 : Δ ≠ 0) (p : Fin (r + 1) × Fin (r + 1)) :
    LinearMap.det (famL v r g θ p) * LinearMap.det (famL v r g θ p.swap) = g ^ 2 := by
  have hr : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange]; exact hfin
  have hs : LinearMap.det (g • (LinearMap.id : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E))) = g ^ 2 := by
    rw [LinearMap.det_smul, LinearMap.det_id, hr, mul_one]
  have ha := det_aL v hfin g θ Δ hθ hΔ hΔ0
  obtain ⟨i, j⟩ := p
  simp only [Prod.swap_prod_mk]
  rcases lt_trichotomy i j with h | h | h
  · have h1 : ¬ j < i := not_lt.2 h.le
    have h2 : j ≠ i := h.ne'
    simp only [famL, if_pos h, if_neg h1, if_neg h2, hs, LinearMap.det_id, mul_one]
  · subst h
    simp only [famL, lt_irrefl, if_false, if_true, ha, sq]
  · have h1 : ¬ i < j := not_lt.2 h.le
    have h2 : i ≠ j := h.ne'
    simp only [famL, if_pos h, if_neg h1, if_neg h2, hs, LinearMap.det_id, one_mul]

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Rewrite using `[bigL, LinearMap.det_pi, sq]`. Establish `e : ∏ p : Fin (r + 1) × Fin (r + 1), LinearMap.det (famL v r g θ p.swap) = ∏ p : Fin (r + 1) × Fin (r + 1), LinearMap.det (famL v r g θ p)` using `Fintype.prod_equiv (Equiv.prodComm _ _) _ _ (fun _ => rfl)`. Use `conv_lhs => arg 2`. Rewrite using `[← e]`.

Rewrite using `[← Finset.prod_mul_distrib]`. Simplify using `only [det_famL_mul v r hfin g θ Δ hθ hΔ hΔ0, Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]`.
-/
theorem det_bigL_sq (hfin : Module.finrank F E = 2) (g : Fv F v) (θ Δ : Fv F v ⊗[F] E)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (hΔ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0)
    (hΔ0 : Δ ≠ 0) : LinearMap.det (bigL v r g θ) ^ 2 = (g ^ 2) ^ ((r + 1) ^ 2) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rw [bigL, LinearMap.det_pi, sq]
  have e : ∏ p : Fin (r + 1) × Fin (r + 1), LinearMap.det (famL v r g θ p.swap) =
      ∏ p : Fin (r + 1) × Fin (r + 1), LinearMap.det (famL v r g θ p) :=
    Fintype.prod_equiv (Equiv.prodComm _ _) _ _ (fun _ => rfl)
  conv_lhs => arg 2; rw [← e]
  rw [← Finset.prod_mul_distrib]
  simp only [det_famL_mul v r hfin g θ Δ hθ hΔ hΔ0, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, sq]

/- English proof (translation)
Establish `hgv : (g : Fv F v) ≠ 0` using `VolTU.natCast_ne_zero v hg0`. Establish `h2` using `det_bigL_sq v r hfin (g : Fv F v) θ Δ hθ hΔ hΔ0`. Establish `hD : LinearMap.det (bigL v r (g : Fv F v) θ) ≠ 0`. Introduce `h`. Rewrite `h2` using `[h, zero_pow two_ne_zero]`.

Conclude with `(pow_ne_zero _ (pow_ne_zero _ hgv)) h2.symm`. Use `⟨hD, ?_⟩` and prove the remaining obligations. Establish `h3` using `congrArg (absV v) h2`. Rewrite `h3` using `[absV_pow, absV_pow, absV_pow, hg]`. Establish `hpos` using `(VolOrdW.absV_pos v hD).le`.

Establish `hgpos : (0 : ℝ) ≤ (g : ℝ)⁻¹ ^ ((r + 1) ^ 2)` using `by positivity`. Use `(pow_left_inj₀ hpos hgpos two_ne_zero).1 ?_` and prove the remaining obligations. Rewrite using `[h3, ← pow_mul, ← pow_mul, mul_comm]`.
-/
theorem absV_det_bigL (hfin : Module.finrank F E = 2) {g : ℕ} (hg0 : g ≠ 0)
    (hg : absV v (g : Fv F v) = (g : ℝ)⁻¹) (θ Δ : Fv F v ⊗[F] E)
    (hθ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) θ = 1) (hΔ : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) Δ = 0)
    (hΔ0 : Δ ≠ 0) :
    LinearMap.det (bigL v r (g : Fv F v) θ) ≠ 0 ∧
      absV v (LinearMap.det (bigL v r (g : Fv F v) θ)) = (g : ℝ)⁻¹ ^ ((r + 1) ^ 2) := by
  have hgv : (g : Fv F v) ≠ 0 := VolTU.natCast_ne_zero v hg0
  have h2 := det_bigL_sq v r hfin (g : Fv F v) θ Δ hθ hΔ hΔ0
  have hD : LinearMap.det (bigL v r (g : Fv F v) θ) ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at h2
    exact (pow_ne_zero _ (pow_ne_zero _ hgv)) h2.symm
  refine ⟨hD, ?_⟩
  have h3 := congrArg (absV v) h2
  rw [absV_pow, absV_pow, absV_pow, hg] at h3
  have hpos := (VolOrdW.absV_pos v hD).le
  have hgpos : (0 : ℝ) ≤ (g : ℝ)⁻¹ ^ ((r + 1) ^ 2) := by positivity
  refine (pow_left_inj₀ hpos hgpos two_ne_zero).1 ?_
  rw [h3, ← pow_mul, ← pow_mul, mul_comm]

end Big

end Formalism.L2.SG.Pf.NcVal.VolV
