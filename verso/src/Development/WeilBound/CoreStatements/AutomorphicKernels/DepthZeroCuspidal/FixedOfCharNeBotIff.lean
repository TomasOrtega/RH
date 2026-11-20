import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DZC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mem_fixed_iff' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {v : V} : v ∈ fixed ρ K ↔ ∀ u ∈ K, ρ u v = v := by
  show (∀ h : K, ρ (h : G) v = (((1 : K →* ℂˣ) h : ℂˣ) : ℂ) • v) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul, Subtype.forall]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem fixed_ne_bot_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (K : Subgroup G)
    (hf : fixed ρ K ≠ ⊥) : fixed σ K ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hf
  refine (Submodule.ne_bot_iff _).2 ⟨e v, mem_fixed_iff'.2 fun u hu => ?_, ?_⟩
  · have h1 : e (ρ u v) = σ u (e v) := LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' u) v
    rw [mem_fixed_iff'.1 hv u hu] at h1
    exact h1.symm
  · intro h0
    apply hv0
    have := congrArg e.symm h0
    rwa [Representation.Equiv.symm_apply_apply, map_zero] at this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem fixed_ofChar_ne_bot_iff {G : Type} [Group G] (ψ : G →* ℂˣ) (K : Subgroup G) :
    fixed (GlobalTheory.SmGL.ofChar ψ) K ≠ ⊥ ↔ ∀ u ∈ K, ψ u = 1 := by
  constructor
  · intro hf u hu
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hf
    have h1 := mem_fixed_iff'.1 hv u hu
    rw [GlobalTheory.SmGL.ofChar_apply] at h1
    have h2 : ((ψ u : ℂˣ) : ℂ) = 1 := by
      have h3 : (((ψ u : ℂˣ) : ℂ) - 1) * v = 0 := by rw [sub_mul, h1, one_mul, sub_self]
      exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hv0)
    exact Units.ext h2
  · intro H
    refine (Submodule.ne_bot_iff _).2 ⟨1, mem_fixed_iff'.2 fun u hu => ?_, one_ne_zero⟩
    rw [GlobalTheory.SmGL.ofChar_apply, H u hu]
    simp

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem val_lt_one_iff (x : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) x < 1 ↔ Valued.v x < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [← Valuation.vlt_one_iff, ← Valuation.vlt_one_iff]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ofChar_fixed_iff (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    fixed (IrrGL.ofChar χ hχ : IrrGL (w.adicCompletion E)).rep
        (KOne (w.adicCompletion E) (Fin (IrrGL.ofChar χ hχ : IrrGL (w.adicCompletion E)).1)) ≠ ⊥ ↔
      ∀ u : (w.adicCompletion E)ˣ, Valued.v ((u : w.adicCompletion E) - 1) < 1 → χ u = 1 := by
  let e : (IrrRep.det (Fin 1) χ hχ).ρ.Equiv (IrrRep.det (Fin 1) χ hχ).cl.rep.ρ := equivRep _
  have key : fixed (IrrGL.ofChar χ hχ : IrrGL (w.adicCompletion E)).rep
        (KOne (w.adicCompletion E) (Fin (IrrGL.ofChar χ hχ : IrrGL (w.adicCompletion E)).1)) ≠ ⊥ ↔
      fixed (GlobalTheory.SmGL.ofChar (detChar (Fin 1) χ)) (KOne (w.adicCompletion E) (Fin 1)) ≠ ⊥ :=
    ⟨fixed_ne_bot_of_equiv e.symm _, fixed_ne_bot_of_equiv e _⟩
  rw [key, fixed_ofChar_ne_bot_iff]
  constructor
  · intro H u hu
    obtain ⟨g, hg, hgv⟩ := GlobalTheory.StepData.exists_mem_KOne (k := w.adicCompletion E) (n := Fin 1)
      (M := Matrix.of fun _ _ => (u : w.adicCompletion E)) (fun i j => by
        rw [Subsingleton.elim j i, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.of_apply]
        exact (val_lt_one_iff _).2 hu)
    have hd : Matrix.GeneralLinearGroup.det g = u := by
      ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, Matrix.det_unique, Matrix.of_apply]
    have := H g hg
    rwa [detChar_apply, hd] at this
  · intro H g hg
    rw [detChar_apply]
    exact GlobalTheory.StepData.tame_det_of_mem_KOne (fun x hx => H x ((val_lt_one_iff _).1 hx)) hg

end PositivityTheory.LocalParametersCuspidal.DZC

end
