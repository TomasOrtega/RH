import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.Published.AutFin.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem finiteDimensional_coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (coeffSpan ρ) := by
  let T : Module.Dual ℂ (Module.End ℂ W) →ₗ[ℂ] (K → ℂ) :=
    LinearMap.pi fun k => LinearMap.applyₗ (ρ k)
  have : coeffSpan ρ ≤ LinearMap.range T := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨ℓ.comp (LinearMap.applyₗ w), rfl⟩
  exact Submodule.finiteDimensional_of_le this

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem isAtTau_unique (hθ : IsInfFam θ) {τ : D.what₂.Tau} {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} {x y : GA D V}
    (hx : IsAtTau θ V τ g x) (hy : IsAtTau θ V τ g y) : x = y := by
  refine ((GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V).2.2.1 x hx.1 y hy.1 fun τ' => ?_
  by_cases c : τ' = τ
  · subst c; rw [hx.2.1, hy.2.1]
  · rw [hx.2.2 _ c, hy.2.2 _ c]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.
-/
theorem kAt_mul (hθ : IsInfFam θ) (τ : D.what₂.Tau) {e : Fin V.rank → Bool}
    {P : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ)
    (k l : Formalism.REAL.KG e) : kAt θ V τ e P (k * l) = kAt θ V τ e P k * kAt θ V τ e P l := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hk := isAtTau_kAt θ V hθ τ hP h k
  have hl := isAtTau_kAt θ V hθ τ hP h l
  have hm := ((GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V).2.2.2.1
  refine isAtTau_unique θ V hθ (isAtTau_kAt θ V hθ τ hP h (k * l)) ⟨mul_mem hk.1 hl.1, ?_, fun τ' c => ?_⟩
  · rw [hm, hk.2.1, hl.2.1]
    have : Formalism.REAL.toMK (k * l) = Formalism.REAL.toMK k * Formalism.REAL.toMK l := rfl
    rw [this]
    calc P⁻¹ * Formalism.REAL.toMK k * P * (P⁻¹ * Formalism.REAL.toMK l * P)
        = P⁻¹ * Formalism.REAL.toMK k * (P * P⁻¹) * Formalism.REAL.toMK l * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [mul_nonsing_inv _ hd]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  · rw [hm, hk.2.2 _ c, hl.2.2 _ c, Matrix.mul_one]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem kAt_injective (hθ : IsInfFam θ) (τ : D.what₂.Tau) {e : Fin V.rank → Bool}
    {P : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ) :
    Function.Injective (kAt θ V τ e P) := by
  intro k l hkl
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hk := (isAtTau_kAt θ V hθ τ hP h k).2.1
  have hl := (isAtTau_kAt θ V hθ τ hP h l).2.1
  rw [hkl, hl] at hk
  have h2 : Formalism.REAL.toMK l = Formalism.REAL.toMK k := by
    have hPi : IsUnit P⁻¹ := isUnit_nonsing_inv_iff.2 hP
    exact hPi.mul_left_cancel (hP.mul_right_cancel hk)
  exact Subtype.ext (Subtype.ext (Units.ext h2.symm))

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Both sides reduce to the same expression.

Treat this case separately. Treat this case separately. Treat this case separately. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem hasTypeAt_trivial_iff (hθ : IsInfFam θ) (τ : D.what₂.Tau) {e : Fin V.rank → Bool}
    {P : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ)
    (φ : GA D V → ℂ) : HasTypeAt θ V τ e P (Representation.trivial ℂ (Formalism.REAL.KG e) ℂ) φ ↔
      ∀ x k, φ (x * kAt θ V τ e P k) = φ x := by
  have h1 : kAt θ V τ e P 1 = 1 := by
    have := kAt_mul θ V hθ τ hP h 1 1
    rw [mul_one] at this
    exact (mul_eq_left.1 this.symm)
  constructor
  · intro H x k
    have key : ∀ f ∈ coeffSpan (Representation.trivial ℂ (Formalism.REAL.KG e) ℂ), f k = f 1 := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem f hf => obtain ⟨ℓ, w, rfl⟩ := hf; rfl
      | zero => rfl
      | add f g _ _ a b => simp [a, b]
      | smul c f _ a => simp [a]
    have := key _ (H x)
    simpa [h1] using this
  · intro H x
    exact Submodule.subset_span ⟨LinearMap.id, φ x, funext fun k => H x k⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem hypotheses_met (D : D7) : ∃ (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (_ : IsInfFam θ)
    (ε : D.what₂.Tau → Fin (D.sp.Y 0).rank → Bool)
    (fr : D.what₂.Tau → Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ),
    IsFrameFam (D.sp.Y 0) ε fr ∧ IsOpen ((⊤ : Subgroup (GA D (D.sp.Y 0))) : Set (GA D (D.sp.Y 0))) ∧
    (∀ τ, IsContRep (Representation.trivial ℂ (Formalism.REAL.KG (ε τ)) ℂ)) ∧
    Submodule.span ℂ (forms θ (D.sp.Y 0) ⊤ ε fr (fun τ => Representation.trivial ℂ (Formalism.REAL.KG (ε τ)) ℂ)
      (fun _ _ => 0)) ≠ ⊥ := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  obtain ⟨ε, fr, h⟩ := exists_isFrameFam (D := D) (D.sp.Y 0) (D.sp.Y_sig 0)
  refine ⟨θ, hθ, ε, fr, h, isOpen_univ, fun _ => isContRep_trivial, fun hb => ?_⟩
  have := Submodule.subset_span (R := ℂ) (const_mem_forms θ (D.sp.Y 0) ⊤ ε fr 1)
  rw [hb] at this
  exact one_ne_zero (congrFun ((Submodule.mem_bot ℂ).1 this) 1)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem finite_of_rank_zero (hV : V.rank = 0) (S : Set (GA D V → ℂ)) :
    FiniteDimensional ℂ (Submodule.span ℂ S) := by
  have : IsEmpty (Fin V.rank) := by rw [hV]; infer_instance
  have : Subsingleton (GA D V) := ⟨fun a b => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩
  infer_instance

end GlobalTheory.Published.AutFin.Model

end
