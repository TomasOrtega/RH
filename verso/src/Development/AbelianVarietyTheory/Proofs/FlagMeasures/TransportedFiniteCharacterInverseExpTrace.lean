import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EmbeddingTraceSumAlt.NormUnitsOfCalculation
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.St.G

/- English proof (translation)
Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_eq_succ hc.deg2`. Establish `: Algebra.IsQuadraticExtension F E` using `⟨hc.deg2⟩`. Set `s : E ≃ₐ[F] E` to `AlgEquiv.ofAlgHom hc.sig hc.sig (by ext y; simp [Formalism.BasicNotions.CMData.sig]) (by ext y; simp [Formalism.BasicNotions.CMData.sig])`. Establish `hs : ∀ y, s y = star y` using `fun y => rfl`. Establish `hne : (1 : E ≃ₐ[F] E) ≠ s`.

Introduce `h`. Establish `hall : ∀ y : E, y ∈ (algebraMap F E).range` using `fun y => (hc.fixed y).1 (by`. Rewrite using `[← hs, ← h]`. Use the proof step `rfl)`. Establish `h1 : Module.finrank F E = 1`.

Apply `finrank_eq_one (1 : E) one_ne_zero` to reduce the goal to its premises. Introduce `w`. Take `⟨a, ha⟩` from `hall w`. Conclude with `⟨a, by rw [Algebra.smul_def, mul_one, ha]⟩`. Rewrite `h1` using `[hc.deg2]`.

Use linear arithmetic over natural numbers and integers. Establish `hcard : Fintype.card (E ≃ₐ[F] E) = 2`. Rewrite using `[← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hc.deg2]`. Establish `huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, s}`. Use `symm`.

Apply `Finset.eq_univ_of_card` to reduce the goal to its premises. Rewrite using `[Finset.card_pair hne, hcard]`. Rewrite using `[trace_eq_sum_automorphisms, huniv, Finset.sum_pair hne, hs]`. Both sides reduce to the same expression.
-/
theorem trace_cm_eq_add_star {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (x : E) :
    algebraMap F E (Algebra.trace F E x) = x + star x := by
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hc.deg2
  have : Algebra.IsQuadraticExtension F E := ⟨hc.deg2⟩
  classical
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom hc.sig hc.sig
    (by ext y; simp [Formalism.BasicNotions.CMData.sig]) (by ext y; simp [Formalism.BasicNotions.CMData.sig])
  have hs : ∀ y, s y = star y := fun y => rfl
  have hne : (1 : E ≃ₐ[F] E) ≠ s := by
    intro h
    have hall : ∀ y : E, y ∈ (algebraMap F E).range := fun y => (hc.fixed y).1 (by
      rw [← hs, ← h]; rfl)
    have h1 : Module.finrank F E = 1 := by
      apply finrank_eq_one (1 : E) one_ne_zero
      intro w
      obtain ⟨a, ha⟩ := hall w
      exact ⟨a, by rw [Algebra.smul_def, mul_one, ha]⟩
    rw [hc.deg2] at h1
    omega
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hc.deg2]
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, s} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne, hcard]
  rw [trace_eq_sum_automorphisms, huniv, Finset.sum_pair hne, hs]
  rfl

/- English proof (translation)
Use `I.cm.totReal` as an intermediate fact. Rewrite using `[show psiEinf I y = PI.ScPsiExists.psiEinf I y from rfl, PI.ScPsiExists.UnitaryGroupMassFormula.psiEinf_eq, PI.ScPsiExists.UnitaryGroupMassFormula.sHom_coe]`. Establish `h2 : ∀ v, I.φ v y + star (I.φ v y) = v.embedding (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed y)`. Introduce `v`. Rewrite using `[← I.φ_over, PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply, map_add, I.cm.cmUnram.2.1 (I.φ v) y]`.

Both sides reduce to the same expression. Establish `h3 : PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed y = Algebra.trace I.F I.E y`. Apply `(algebraMap I.F I.E).injective` to reduce the goal to its premises. Rewrite using `[PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply, trace_cm_eq_add_star I.cm]`. Rewrite using `[Finset.sum_congr rfl (fun v _ => h2 v), PI.ScPsiExists.UnitaryGroupMassFormula.sum_embedding_eq_trace, h3, Algebra.trace_trace]`.

Both sides reduce to the same expression.
-/
theorem psiEinf_eq_exp_trace (I : Formalism.MainNotions.S.AutInst) (y : I.E) :
    psiEinf I y = Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ I.E y : ℚ) : ℂ)) := by
  have := I.cm.totReal
  rw [show psiEinf I y = PI.ScPsiExists.psiEinf I y from rfl, PI.ScPsiExists.UnitaryGroupMassFormula.psiEinf_eq,
    PI.ScPsiExists.UnitaryGroupMassFormula.sHom_coe]
  have h2 : ∀ v, I.φ v y + star (I.φ v y) =
      v.embedding (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed y) := by
    intro v
    rw [← I.φ_over, PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply, map_add, I.cm.cmUnram.2.1 (I.φ v) y]
    rfl
  have h3 : PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed y = Algebra.trace I.F I.E y := by
    apply (algebraMap I.F I.E).injective
    rw [PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply, trace_cm_eq_add_star I.cm]
  rw [Finset.sum_congr rfl (fun v _ => h2 v), PI.ScPsiExists.UnitaryGroupMassFormula.sum_embedding_eq_trace, h3,
    Algebra.trace_trace]
  rfl

/- English proof (translation)
Introduce `D X ιA hA x`. Establish `h1 : ιA.symm (Formalism.UG.inclE (F` using `D.host.F) (Ad D.host.F) x) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm x) := by`. Rewrite using `[RingEquiv.symm_apply_eq, hA.1 (X.ιE.symm x), X.ιE.apply_symm_apply]`. Establish `htr : Algebra.trace ℚ D.host.E x = Algebra.trace ℚ X.B.I.E (X.ιE.symm x)` using `by conv_lhs => rw [← X.ιE.apply_symm_apply x]`. Conclude with `Algebra.trace_eq_of_algEquiv X.ιE.toRatAlgEquiv (X.ιE.symm x)`.

Rewrite using `[h1, htr, ← psiEinf_eq_exp_trace]`. Conclude with `X.psiEf_rat (X.ιE.symm x)`.
-/
theorem psiEf_transport_rat : ∀ (D : D7) (X : HidaSetting D) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA → ∀ x : D.host.E, X.psiEf (ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) x)) * Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E x : ℚ) : ℂ)) = 1 := by
  intro D X ιA hA x
  have h1 : ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) x) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm x) := by
    rw [RingEquiv.symm_apply_eq, hA.1 (X.ιE.symm x), X.ιE.apply_symm_apply]
  have htr : Algebra.trace ℚ D.host.E x = Algebra.trace ℚ X.B.I.E (X.ιE.symm x) := by
    conv_lhs => rw [← X.ιE.apply_symm_apply x]
    exact Algebra.trace_eq_of_algEquiv X.ιE.toRatAlgEquiv (X.ιE.symm x)
  rw [h1, htr, ← psiEinf_eq_exp_trace]
  exact X.psiEf_rat (X.ιE.symm x)

end GlobalTheory.St.G

end
