import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DominantRootSums
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.KStableFiniteDimSmoothCompactRootStable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusWeightEigenAndRootShift

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.LowestVector

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in

/- English proof (translation)
Introduce `hKS k r ε mu R hDS Q E hQ hE`. Establish `hFV` using `(_root_.GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 ε mu R hDS Q hQ`. Unfold `_root_.PI.UpqRep.IsDS at hFV`. Take `⟨-, -, -, -, -, ⟨S, hS⟩, -⟩` from `hFV`. Unfold `_root_.PI.UpqRep.IsKTypeOf at hS`.

Take `⟨hSfd, hSK, -, ⟨v, hvS, hv0, hvw⟩, hhigh⟩` from `hS`. Establish `hlow : _root_.PI.UpqRep.lowK ε mu = _root_.Formalism.QuantumDeterminants.lowK ε mu` using `rfl`. Establish `hstab` using `_root_.GlobalTheory.CompactStable.kStable_smooth_and_stable hKS k r ε mu R hDS Q hQ S hSfd hSK`. Unfold `_root_.BranchingSupport.Rep.IsE at hE`. Use `set w0 : R.H := ((‖v‖⁻¹ : ℝ) : ℂ) • v with hw0def`.

Establish `hw0S : w0 ∈ S` using `S.smul_mem _ hvS`. Establish `hw0wt : _root_.PI.UpqRep.IsWtOn (_root_.PI.UpqRep.Kset ε) (fun g ↦ R.σ (Q⁻¹ * g * Q)) (_root_.PI.UpqRep.lowK ε mu) w0`. Unfold `_root_.PI.UpqRep.IsWtOn at hvw ⊢`. Introduce `θ hθ`. Rewrite using `[hw0def, ContinuousLinearMap.map_smul, hvw θ hθ, smul_comm]`.

Establish `hnorm : ‖w0‖ = 1`. Rewrite using `[hw0def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]`. Set `w : R.smSub` to `⟨w0, (hstab.1 w0 hw0S).2⟩`. Establish `htor` using `_root_.GlobalTheory.TorusWeight.torus_weight_action hKS k r ε mu R hDS Q E hQ hE (_root_.PI.UpqRep.lowK ε mu) w hw0wt`. Set `T : Submodule ℂ R.smSub` to `S.comap R.smSub.subtype`.

Establish `hT : _root_.Formalism.REAL.KStable ε E T`. Unfold `_root_.Formalism.REAL.KStable`. Introduce `a b hab x hx`. Use `show ((E a b x : R.smSub) : R.H) ∈ S`. Rewrite using `[hE]`.

Conclude with `hstab.2 a b hab x hx`. Establish `hTfd : FiniteDimensional ℂ T`. Set `f : T →ₗ[ℂ] S` to `LinearMap.codRestrict S (R.smSub.subtype.comp T.subtype) (fun x => x.2)`. Use `Module.Finite.of_injective f ?_` and prove the remaining obligations. Introduce `x y hxy`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hval` using `congrArg Subtype.val hxy`. Conclude with `hval`. Establish `hle : _root_.Formalism.REAL.kSpan ε E w ≤ T`.

Unfold `_root_.Formalism.REAL.kSpan`. Conclude with `sInf_le ⟨hw0S, hT⟩`. Use `⟨w, hnorm, (hstab.1 w0 hw0S).1, ?_, Submodule.finiteDimensional_of_le hle⟩` and prove the remaining obligations. Unfold `_root_.Formalism.REAL.KHighest`. Use `⟨htor.1, ?_⟩` and prove the remaining obligations.

Introduce `a b hab hεab`. Assume the negation of the conclusion as `hne`. Establish `hmem : ((E a b w : R.smSub) : R.H) ∈ S`. Rewrite using `[hE]`. Conclude with `hstab.2 a b hεab w0 hw0S`.

Establish `hne' : ((E a b w : R.smSub) : R.H) ≠ 0` using `fun h => hne (Submodule.coe_eq_zero.mp h)`. Conclude with `_root_.GlobalTheory.DominantRootSums.not_cDom_add_root _ ε (_root_.PI.UpqRep.lowK ε mu) a b hab (hhigh _ _ hmem hne' (htor.2 a b))`.
-/
theorem _root_.GlobalTheory.LowestVector.exists_lowest_vector : _root_.PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : _root_.BranchingSupport.Rep k r), R.IsDS ε mu → ∀ (Q : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), _root_.PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∃ w : R.smSub, ‖w‖ = 1 ∧ R.KFin (w : R.H) ∧ _root_.Formalism.REAL.KHighest ε E (_root_.Formalism.QuantumDeterminants.lowK ε mu) w ∧ FiniteDimensional ℂ (_root_.Formalism.REAL.kSpan ε E w) := by
  intro hKS k r ε mu R hDS Q E hQ hE
  have hFV := (_root_.GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 ε mu R hDS Q hQ
  unfold _root_.PI.UpqRep.IsDS at hFV
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hFV
  unfold _root_.PI.UpqRep.IsKTypeOf at hS
  obtain ⟨hSfd, hSK, -, ⟨v, hvS, hv0, hvw⟩, hhigh⟩ := hS
  have hlow : _root_.PI.UpqRep.lowK ε mu = _root_.Formalism.QuantumDeterminants.lowK ε mu := rfl
  have hstab := _root_.GlobalTheory.CompactStable.kStable_smooth_and_stable hKS k r ε mu R hDS Q hQ S hSfd hSK
  unfold _root_.BranchingSupport.Rep.IsE at hE
  set w0 : R.H := ((‖v‖⁻¹ : ℝ) : ℂ) • v with hw0def
  have hw0S : w0 ∈ S := S.smul_mem _ hvS
  have hw0wt : _root_.PI.UpqRep.IsWtOn (_root_.PI.UpqRep.Kset ε) (fun g ↦ R.σ (Q⁻¹ * g * Q)) (_root_.PI.UpqRep.lowK ε mu) w0 := by
    unfold _root_.PI.UpqRep.IsWtOn at hvw ⊢
    intro θ hθ
    rw [hw0def, ContinuousLinearMap.map_smul, hvw θ hθ, smul_comm]
  have hnorm : ‖w0‖ = 1 := by
    rw [hw0def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  let w : R.smSub := ⟨w0, (hstab.1 w0 hw0S).2⟩
  have htor := _root_.GlobalTheory.TorusWeight.torus_weight_action hKS k r ε mu R hDS Q E hQ hE (_root_.PI.UpqRep.lowK ε mu) w hw0wt
  let T : Submodule ℂ R.smSub := S.comap R.smSub.subtype
  have hT : _root_.Formalism.REAL.KStable ε E T := by
    unfold _root_.Formalism.REAL.KStable
    intro a b hab x hx
    show ((E a b x : R.smSub) : R.H) ∈ S
    rw [hE]
    exact hstab.2 a b hab x hx
  have hTfd : FiniteDimensional ℂ T := by
    let f : T →ₗ[ℂ] S :=
      LinearMap.codRestrict S (R.smSub.subtype.comp T.subtype) (fun x => x.2)
    refine Module.Finite.of_injective f ?_
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have hval := congrArg Subtype.val hxy
    exact hval
  have hle : _root_.Formalism.REAL.kSpan ε E w ≤ T := by
    unfold _root_.Formalism.REAL.kSpan
    exact sInf_le ⟨hw0S, hT⟩
  refine ⟨w, hnorm, (hstab.1 w0 hw0S).1, ?_, Submodule.finiteDimensional_of_le hle⟩
  unfold _root_.Formalism.REAL.KHighest
  refine ⟨htor.1, ?_⟩
  intro a b hab hεab
  by_contra hne
  have hmem : ((E a b w : R.smSub) : R.H) ∈ S := by
    rw [hE]
    exact hstab.2 a b hεab w0 hw0S
  have hne' : ((E a b w : R.smSub) : R.H) ≠ 0 := fun h => hne (Submodule.coe_eq_zero.mp h)
  exact _root_.GlobalTheory.DominantRootSums.not_cDom_add_root _ ε (_root_.PI.UpqRep.lowK ε mu) a b hab
    (hhigh _ _ hmem hne' (htor.2 a b))

end GlobalTheory.LowestVector
