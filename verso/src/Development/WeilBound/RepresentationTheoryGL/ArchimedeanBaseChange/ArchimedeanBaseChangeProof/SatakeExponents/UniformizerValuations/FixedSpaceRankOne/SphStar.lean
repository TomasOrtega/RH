import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceIndicatorLevelLocalUnitaryStatement
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FixedSpaceRankOne.TraceMulOfFinrankOne
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FixedSpaceRankOne.SphOne
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SphStarU

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.EigA

open PositivityTheory.Rg.BcB.F.Eig (locOp lconv lstar LocAlg SphStarU)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `hsub : Function.support (fun q : UL n w ⧸ KL n w => f q.out • (ρ q.out ∘ₗ LinearMap.id)) ⊆ ↑S`. Introduce `q hq`. Use `Finset.mem_coe.2 (hS q fun h0 => ?_)` and prove the remaining obligations. Apply `Function.mem_support.1 hq` to reduce the goal to its premises. Simplify using `only [h0, zero_smul]`.

Rewrite using `[levOp, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul, finsum_eq_sum_of_support_subset _ hsub, LinearMap.sum_apply]`. Simplify using `only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply]`.
-/
theorem levOp_KL_apply {n : ℕ} {w : Pl E} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (UL n w) V) (f : UL n w → ℂ) (S : Finset (UL n w ⧸ KL n w))
    (hS : ∀ q : UL n w ⧸ KL n w, f q.out ≠ 0 → q ∈ S) (v : V) :
    levOp ρ (KL n w) (KL n w) f LinearMap.id v = ∑ q ∈ S, f q.out • ρ q.out v := by
  have hsub : Function.support (fun q : UL n w ⧸ KL n w => f q.out • (ρ q.out ∘ₗ LinearMap.id)) ⊆ ↑S := by
    intro q hq
    refine Finset.mem_coe.2 (hS q fun h0 => ?_)
    apply Function.mem_support.1 hq
    simp only [h0, zero_smul]
  rw [levOp, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul,
    finsum_eq_sum_of_support_subset _ hsub, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply]

/- English proof (translation)
Introduce `hLA E _ _ _ hE n w σ hU hrank h₁ h₂ hh₁ hh₂`. Establish `hlev : IsLevel (MonoidHom.id (UL n w)) (KL n w) (KL n w)` using `⟨GlobalTheory.CompanionTheory.IwLevels.isOpen_KL n w, le_rfl, fun k hk => hk⟩`. Establish `LA` using `fun f₁ f₂ (hf₁ : IsHecke (KL n w) f₁) (hf₂ : IsHecke (KL n w) f₂) => hLA E n w σ (KL n w) hlev f₁ f₂ hf₁ hf₂`. Take `⟨tr1, app1, hconv, hstar, hmul, -, -, -⟩` from `LA h₁ h₂ hh₁ hh₂`. Take `⟨tr2, -⟩` from `LA h₂ h₁ hh₂ hh₁`.

Take `⟨trc, -⟩` from `LA (lconv h₁ h₂) h₁ hconv hh₁`. Take `⟨trs, apps, -⟩` from `LA (lstar h₁) h₁ hstar hh₁`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[trc, hmul, trace_mul_of_finrank_one hrank, ← tr1, ← tr2]`. Take `⟨B, hBh, hBpos, hBinv⟩` from `hU haveI : Nontrivial (fixed σ.ρ (KL n w)) := Module.nontrivial_of_finrank_eq_succ hrank`.

Take `⟨v, hv0⟩` from `exists_ne (0 : fixed σ.ρ (KL n w))`. Establish `hvfix` using `mem_fixed_iff.1 v.2`. Set `φ : UL n w → ℂ` to `fun x => B (σ.ρ x v) v`. Establish `key : ∀ f, IsHecke (KL n w) f → twTr σ.ρ (KL n w) (KL n w) f LinearMap.id = LinearMap.trace ℂ _ (locOp σ (KL n w) f) → (∀ u : fixed σ.ρ (KL n w), (locOp σ (KL n w) f u).1 = levOp σ.ρ (KL n w) (KL n w) f LinearMap.id u.1) → twTr σ.ρ (KL n w) (KL n w) f LinearMap.id * B v v = ∑ᶠ q …`. Introduce `f hf htr happ`.

Establish `hfin` using `finite_support_quot (KL n w) (GlobalTheory.CompanionTheory.IwLevels.isOpen_KL n w) f hf.1`. Establish `hS : ∀ q : UL n w ⧸ KL n w, f q.out ≠ 0 → q ∈ hfin.toFinset` using `fun q hq => hfin.mem_toFinset.2 hq`. Establish `hline : locOp σ (KL n w) f v = twTr σ.ρ (KL n w) (KL n w) f LinearMap.id • v`. Rewrite using `[htr]`. Use `conv_lhs => rw [end_eq_trace_smul hrank (locOp σ (KL n w) f)]`.

Both sides reduce to the same expression. Establish `h1 : levOp σ.ρ (KL n w) (KL n w) f LinearMap.id v.1 = twTr σ.ρ (KL n w) (KL n w) f LinearMap.id • v.1`. Rewrite using `[← happ, hline]`. Both sides reduce to the same expression. Rewrite `h1` using `[levOp_KL_apply σ.ρ f hfin.toFinset hS]`.

Establish `h2` using `congrArg (fun x => B x v.1) h1`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h2`. Establish `hsub : Function.support (fun q : UL n w ⧸ KL n w => f q.out * φ q.out) ⊆ ↑hfin.toFinset`. Introduce `q hq`. Conclude with `Finset.mem_coe.2 (hS q (left_ne_zero_of_mul (Function.mem_support.1 hq)))`.

Rewrite using `[← h2, finsum_eq_sum_of_support_subset _ hsub]`. Establish `hφ : ∀ x, starRingEnd ℂ (φ x) = φ x⁻¹`. Introduce `x`. Use `show starRingEnd ℂ (B (σ.ρ x v) v) = B (σ.ρ x⁻¹ v) v`. Rewrite using `[← hBh, ← hBinv x⁻¹ (v : σ.V) (σ.ρ x v), ← Module.End.mul_apply (σ.ρ x⁻¹) (σ.ρ x), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`.

Establish `hφbi : ∀ k₁ ∈ KL n w, ∀ k₂ ∈ KL n w, ∀ x, φ (k₁ * x * k₂) = φ x`. Introduce `k₁ hk₁ k₂ hk₂ x`. Use `show B (σ.ρ (k₁ * x * k₂) v) v = B (σ.ρ x v) v`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hvfix k₂ hk₂, ← hBinv k₁⁻¹ (σ.ρ k₁ (σ.ρ x v)) (v : σ.V), hvfix _ ((KL n w).inv_mem hk₁), ← Module.End.mul_apply (σ.ρ k₁⁻¹) (σ.ρ k₁), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Set `F : UL n w → ℂ` to `fun x => starRingEnd ℂ (h₁ x) * φ x⁻¹`.

Establish `hF : ∀ k₁ ∈ KL n w, ∀ k₂ ∈ KL n w, ∀ x, F (k₁ * x * k₂) = F x`. Introduce `k₁ hk₁ k₂ hk₂ x`. Use `show starRingEnd ℂ (h₁ (k₁ * x * k₂)) * φ (k₁ * x * k₂)⁻¹ = starRingEnd ℂ (h₁ x) * φ x⁻¹`. Rewrite using `[(hh₁.2 k₂ hk₂ _).2, mul_assoc, (hh₁.2 k₁ hk₁ _).1, _root_.mul_inv_rev, _root_.mul_inv_rev, hφbi _ ((KL n w).inv_mem hk₂) _ ((KL n w).inv_mem hk₁)]`. Establish `eqL` using `key h₁ hh₁ tr1 app1`.

Establish `eqμ` using `key (lstar h₁) hstar trs apps`. Establish `hBvv : starRingEnd ℂ (B v v) = B v v` using `(hBh v v).symm`. Establish `hBne : B v v ≠ 0`. Introduce `h`. Use `hBpos (v : σ.V) (fun h0 => hv0 (Subtype.ext h0))` as an intermediate fact.

Rewrite `this` using `[h]`. Simplify using `at this`. Establish `hfin1` using `finite_support_quot (KL n w) (GlobalTheory.CompanionTheory.IwLevels.isOpen_KL n w) h₁ hh₁.1`. Establish `hsupp : (Function.support fun q : UL n w ⧸ KL n w => h₁ q.out * φ q.out).Finite` using `hfin1.subset fun q hq => left_ne_zero_of_mul (Function.mem_support.1 hq)`. Establish `eqc : starRingEnd ℂ (twTr σ.ρ (KL n w) (KL n w) h₁ LinearMap.id) * B v v = ∑ᶠ q : UL n w ⧸ KL n w, F q.out`.

Establish `h` using `congrArg (starRingEnd ℂ) eqL`. Rewrite `h` using `[map_mul, hBvv, map_finsum _ hsupp]`. Rewrite using `[h]`. Use `finsum_congr fun q => ?_` and prove the remaining obligations. Simplify using `only [map_mul, hφ, F]`.

Establish `eqμ' : twTr σ.ρ (KL n w) (KL n w) (lstar h₁) LinearMap.id * B v v = ∑ᶠ q : UL n w ⧸ KL n w, F (q.out)⁻¹`. Rewrite using `[eqμ]`. Use `finsum_congr fun q => ?_` and prove the remaining obligations. Simplify using `only [F, lstar, inv_inv]`. Take `⟨-, τ, hmulτ, hinvτ, hdcτ, hKτ⟩` from `gelPair_KL hE n w`.

Establish `heq` using `finsum_inv_eq τ hmulτ hinvτ hdcτ hKτ F hF`. Rewrite `heq` using `[← eqμ', ← eqc]`. Conclude with `mul_right_cancel₀ hBne heq`. Establish `h` using `(GlobalTheory.T.twistedTrace_indicator_level_localUnitary E n w (KL n w) hlev σ).2.2.1`. Rewrite using `[h, Subgroup.relIndex_self, hrank]`.

Simplify using the standard rewrite rules.
-/
theorem sphStar : LocAlg → SphStarU := by
  intro hLA E _ _ _ hE n w σ hU hrank h₁ h₂ hh₁ hh₂
  have hlev : IsLevel (MonoidHom.id (UL n w)) (KL n w) (KL n w) :=
    ⟨GlobalTheory.CompanionTheory.IwLevels.isOpen_KL n w, le_rfl, fun k hk => hk⟩
  have LA := fun f₁ f₂ (hf₁ : IsHecke (KL n w) f₁) (hf₂ : IsHecke (KL n w) f₂) =>
    hLA E n w σ (KL n w) hlev f₁ f₂ hf₁ hf₂
  obtain ⟨tr1, app1, hconv, hstar, hmul, -, -, -⟩ := LA h₁ h₂ hh₁ hh₂
  obtain ⟨tr2, -⟩ := LA h₂ h₁ hh₂ hh₁
  obtain ⟨trc, -⟩ := LA (lconv h₁ h₂) h₁ hconv hh₁
  obtain ⟨trs, apps, -⟩ := LA (lstar h₁) h₁ hstar hh₁
  refine ⟨?_, ?_, ?_⟩
  · rw [trc, hmul, trace_mul_of_finrank_one hrank, ← tr1, ← tr2]
  · obtain ⟨B, hBh, hBpos, hBinv⟩ := hU
    haveI : Nontrivial (fixed σ.ρ (KL n w)) := Module.nontrivial_of_finrank_eq_succ hrank
    obtain ⟨v, hv0⟩ := exists_ne (0 : fixed σ.ρ (KL n w))
    have hvfix := mem_fixed_iff.1 v.2
    let φ : UL n w → ℂ := fun x => B (σ.ρ x v) v
    have key : ∀ f, IsHecke (KL n w) f →
        twTr σ.ρ (KL n w) (KL n w) f LinearMap.id = LinearMap.trace ℂ _ (locOp σ (KL n w) f) →
        (∀ u : fixed σ.ρ (KL n w), (locOp σ (KL n w) f u).1 = levOp σ.ρ (KL n w) (KL n w) f LinearMap.id u.1) →
        twTr σ.ρ (KL n w) (KL n w) f LinearMap.id * B v v = ∑ᶠ q : UL n w ⧸ KL n w, f q.out * φ q.out := by
      intro f hf htr happ
      have hfin := finite_support_quot (KL n w) (GlobalTheory.CompanionTheory.IwLevels.isOpen_KL n w) f hf.1
      have hS : ∀ q : UL n w ⧸ KL n w, f q.out ≠ 0 → q ∈ hfin.toFinset := fun q hq => hfin.mem_toFinset.2 hq
      have hline : locOp σ (KL n w) f v = twTr σ.ρ (KL n w) (KL n w) f LinearMap.id • v := by
        rw [htr]
        conv_lhs => rw [end_eq_trace_smul hrank (locOp σ (KL n w) f)]
        rfl
      have h1 : levOp σ.ρ (KL n w) (KL n w) f LinearMap.id v.1 = twTr σ.ρ (KL n w) (KL n w) f LinearMap.id • v.1 := by
        rw [← happ, hline]
        rfl
      rw [levOp_KL_apply σ.ρ f hfin.toFinset hS] at h1
      have h2 := congrArg (fun x => B x v.1) h1
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h2
      have hsub : Function.support (fun q : UL n w ⧸ KL n w => f q.out * φ q.out) ⊆ ↑hfin.toFinset := by
        intro q hq
        exact Finset.mem_coe.2 (hS q (left_ne_zero_of_mul (Function.mem_support.1 hq)))
      rw [← h2, finsum_eq_sum_of_support_subset _ hsub]
    have hφ : ∀ x, starRingEnd ℂ (φ x) = φ x⁻¹ := by
      intro x
      show starRingEnd ℂ (B (σ.ρ x v) v) = B (σ.ρ x⁻¹ v) v
      rw [← hBh, ← hBinv x⁻¹ (v : σ.V) (σ.ρ x v), ← Module.End.mul_apply (σ.ρ x⁻¹) (σ.ρ x), ← map_mul,
        inv_mul_cancel, map_one, Module.End.one_apply]
    have hφbi : ∀ k₁ ∈ KL n w, ∀ k₂ ∈ KL n w, ∀ x, φ (k₁ * x * k₂) = φ x := by
      intro k₁ hk₁ k₂ hk₂ x
      show B (σ.ρ (k₁ * x * k₂) v) v = B (σ.ρ x v) v
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hvfix k₂ hk₂,
        ← hBinv k₁⁻¹ (σ.ρ k₁ (σ.ρ x v)) (v : σ.V), hvfix _ ((KL n w).inv_mem hk₁),
        ← Module.End.mul_apply (σ.ρ k₁⁻¹) (σ.ρ k₁), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    let F : UL n w → ℂ := fun x => starRingEnd ℂ (h₁ x) * φ x⁻¹
    have hF : ∀ k₁ ∈ KL n w, ∀ k₂ ∈ KL n w, ∀ x, F (k₁ * x * k₂) = F x := by
      intro k₁ hk₁ k₂ hk₂ x
      show starRingEnd ℂ (h₁ (k₁ * x * k₂)) * φ (k₁ * x * k₂)⁻¹ = starRingEnd ℂ (h₁ x) * φ x⁻¹
      rw [(hh₁.2 k₂ hk₂ _).2, mul_assoc, (hh₁.2 k₁ hk₁ _).1, _root_.mul_inv_rev, _root_.mul_inv_rev,
        hφbi _ ((KL n w).inv_mem hk₂) _ ((KL n w).inv_mem hk₁)]
    have eqL := key h₁ hh₁ tr1 app1
    have eqμ := key (lstar h₁) hstar trs apps
    have hBvv : starRingEnd ℂ (B v v) = B v v := (hBh v v).symm
    have hBne : B v v ≠ 0 := by
      intro h
      have := hBpos (v : σ.V) (fun h0 => hv0 (Subtype.ext h0))
      rw [h] at this
      simp at this
    have hfin1 := finite_support_quot (KL n w) (GlobalTheory.CompanionTheory.IwLevels.isOpen_KL n w) h₁ hh₁.1
    have hsupp : (Function.support fun q : UL n w ⧸ KL n w => h₁ q.out * φ q.out).Finite :=
      hfin1.subset fun q hq => left_ne_zero_of_mul (Function.mem_support.1 hq)
    have eqc : starRingEnd ℂ (twTr σ.ρ (KL n w) (KL n w) h₁ LinearMap.id) * B v v =
        ∑ᶠ q : UL n w ⧸ KL n w, F q.out := by
      have h := congrArg (starRingEnd ℂ) eqL
      rw [map_mul, hBvv, map_finsum _ hsupp] at h
      rw [h]
      refine finsum_congr fun q => ?_
      simp only [map_mul, hφ, F]
    have eqμ' : twTr σ.ρ (KL n w) (KL n w) (lstar h₁) LinearMap.id * B v v =
        ∑ᶠ q : UL n w ⧸ KL n w, F (q.out)⁻¹ := by
      rw [eqμ]
      refine finsum_congr fun q => ?_
      simp only [F, lstar, inv_inv]
    obtain ⟨-, τ, hmulτ, hinvτ, hdcτ, hKτ⟩ := gelPair_KL hE n w
    have heq := finsum_inv_eq τ hmulτ hinvτ hdcτ hKτ F hF
    rw [← eqμ', ← eqc] at heq
    exact mul_right_cancel₀ hBne heq
  · have h := (GlobalTheory.T.twistedTrace_indicator_level_localUnitary E n w (KL n w) hlev σ).2.2.1
    rw [h, Subgroup.relIndex_self, hrank]
    simp

end PositivityTheory.Rg.BcB.F.EigA

end
