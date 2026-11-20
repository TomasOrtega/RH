import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary ValuativeRel
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory.SplitWeil.FourierPi (box isCompact_box exists_box_subset)
open scoped Topology

noncomputable section

namespace GlobalTheory.KSp

/- English proof (translation)
Introduce `i _`. Assume the negation of the conclusion as `h`. Simplify using `only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, not_le] at h`. Establish `hw : v i ≠ 0`. Introduce and unpack `h0`.

Rewrite `h` using `[h0, map_zero]`. Conclude with `absurd h (not_lt_of_ge zero_le')`. Apply `ht` to reduce the goal to its premises. Establish `hu : (Pi.single i ((t₀ : F) / v i) : d → F) ∈ box d s`. Introduce `j _`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `only [Pi.single_eq_same, GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq]`. Establish `e : (t₀ : F) / v j = ((t₀ * s⁻¹ : Fˣ) : F) * s / v j`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Establish `hpos : 0 < valuation F (v j)`. Rewrite using `[zero_lt_iff]`. Conclude with `(map_ne_zero _).mpr hw`. Rewrite using `[e, map_div₀, map_mul, div_le_iff₀ hpos, mul_comm (valuation F (s : F))]`.

Conclude with `mul_le_mul' h.le le_rfl`. Simplify using `[Pi.single_eq_of_ne hj, GlobalTheory.SplitWeil.cball]`. Establish `h2` using `hv _ hu`. Rewrite `h2` using `[single_dotProduct, div_mul_cancel₀ _ hw]`. Then use the resulting hypothesis.
-/
theorem mem_box_of_forall_dot {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {d : Type} [Fintype d] [DecidableEq d] (ψ : AddChar F ℂ) {t₀ : Fˣ}
    (ht : ψ t₀ ≠ 1) (s : Fˣ) {v : d → F} (hv : ∀ u ∈ box d s, ψ (u ⬝ᵥ v) = 1) :
    v ∈ box d (t₀ * s⁻¹) := by
  intro i _
  by_contra h
  simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, not_le] at h
  have hw : v i ≠ 0 := by
    rintro h0
    rw [h0, map_zero] at h
    exact absurd h (not_lt_of_ge zero_le')
  apply ht
  have hu : (Pi.single i ((t₀ : F) / v i) : d → F) ∈ box d s := by
    intro j _
    by_cases hj : j = i
    · subst hj
      simp only [Pi.single_eq_same, GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq]
      have e : (t₀ : F) / v j = ((t₀ * s⁻¹ : Fˣ) : F) * s / v j := by
        push_cast
        field_simp
      have hpos : 0 < valuation F (v j) := by
        rw [zero_lt_iff]; exact (map_ne_zero _).mpr hw
      rw [e, map_div₀, map_mul, div_le_iff₀ hpos, mul_comm (valuation F (s : F))]
      exact mul_le_mul' h.le le_rfl
    · simp [Pi.single_eq_of_ne hj, GlobalTheory.SplitWeil.cball]
  have h2 := hv _ hu
  rwa [single_dotProduct, div_mul_cancel₀ _ hw] at h2

/- English proof (translation)
Introduce `F _ _ _ _ _ V _ _ _ _ _ ψ hψ hn h1 β hs hnd`. Use `haveI := GlobalTheory.WeilM.nonarch_field F`. Use `haveI := IsModuleTopology.toContinuousAdd F V`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `h1 (DFunLike.ext _ _ fun x => by rw [h x, AddChar.one_apply])`. Establish `ht0 : t ≠ 0`. Introduce and unpack `rfl`. Conclude with `ht (AddChar.map_zero_eq_one ψ)`.

Set `T : Fˣ` to `Units.mk0 t ht0`. Establish `hT : ψ (T : F) ≠ 1` using `ht`. Set `b` to `Module.finBasis F V`. Set `e₁ : V ≃ₗ[F] (Fin (Module.finrank F V) → F)` to `b.equivFun`. Set `f₂ : V →ₗ[F] (Fin (Module.finrank F V) → F)` to `LinearMap.pi fun i => β (b i)`.

Establish `hf₂ : Function.Injective f₂`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `y hy`. Apply `hnd y` to reduce the goal to its premises. Introduce `x`.

Rewrite using `[← b.sum_repr x, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, LinearMap.smul_apply, show β (b i) y = 0 from congrFun hy i, smul_zero]`. Establish `hbij : Function.Bijective f₂` using `⟨hf₂, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hf₂⟩`. Set `e₂ : V ≃ₗ[F] (Fin (Module.finrank F V) → F)` to `LinearEquiv.ofBijective f₂ hbij`.

Establish `key : ∀ u y, β (e₁.symm u) y = u ⬝ᵥ e₂ y`. Introduce `u y`. Simplify using `[e₁, e₂, f₂, Module.Basis.equivFun_symm_apply, map_sum, map_smul, dotProduct]`. Establish `cont : ∀ g : V ≃ₗ[F] (Fin (Module.finrank F V) → F), Continuous g ∧ Continuous g.symm` using `fun g => ⟨IsModuleTopology.continuous_of_linearMap g.toLinearMap, IsModuleTopology.continuous_of_linearMap g.symm.toLinearMap⟩`. Establish `ann : ∀ (s : Fˣ) y, (∀ u ∈ box (Fin (Module.finrank F V)) s, ψ (β (e₁.symm u) y) = 1) → e₂ y ∈ box (Fin (Module.finrank F V)) (T * s⁻¹)`.

Introduce `s y h`. Conclude with `mem_box_of_forall_dot ψ hT s fun u hu => by rw [← key]; exact h u hu`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x x' y`. Rewrite using `[map_add, LinearMap.add_apply, AddChar.map_add_eq_mul]`.

Introduce `x y`. Rewrite using `[hs]`. Introduce `x y`. Conclude with `hn _`. Conclude with `(GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ).comp_continuous (IsModuleTopology.continuous_bilinear_of_finite_left β)`.

Introduce `U hU`. Establish `hU' : e₂.symm ⁻¹' U ∈ 𝓝 (0 : Fin (Module.finrank F V) → F)` using `(cont e₂).2.continuousAt.preimage_mem_nhds (by simpa using hU)`. Take `⟨r, hr⟩` from `exists_box_subset hU'`. Use `⟨e₁.symm '' box (Fin (Module.finrank F V)) (T * r⁻¹), (isCompact_box _).image (cont e₁).2, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h2` using `ann (T * r⁻¹) y fun u hu => hy _ ⟨u, hu, rfl⟩`.

Rewrite `h2` using `[show T * (T * r⁻¹)⁻¹ = r by rw [_root_.mul_inv_rev, inv_inv, mul_comm r, mul_inv_cancel_left]]`. Simplify using `using hr h2`. Introduce `U hU`. Establish `hU' : e₁.symm ⁻¹' U ∈ 𝓝 (0 : Fin (Module.finrank F V) → F)` using `(cont e₁).2.continuousAt.preimage_mem_nhds (by simpa using hU)`. Take `⟨s, hs'⟩` from `exists_box_subset hU'`.

Conclude with `⟨e₂.symm '' box (Fin (Module.finrank F V)) (T * s⁻¹), (isCompact_box _).image (cont e₂).2, fun y hy => ⟨e₂ y, ann s y fun u hu => hy _ (hs' hu), by simp⟩⟩`.
-/
theorem isPair_addChar_form : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [TopologicalSpace V] [IsModuleTopology F V] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (β : V →ₗ[F] V →ₗ[F] F), (∀ x y, β x y = β y x) → (∀ y, (∀ x, β x y = 0) → y = 0) → IsPair fun x y => ψ (β x y) := by
  intro F _ _ _ _ _ V _ _ _ _ _ ψ hψ hn h1 β hs hnd
  haveI := GlobalTheory.WeilM.nonarch_field F
  haveI := IsModuleTopology.toContinuousAdd F V
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact h1 (DFunLike.ext _ _ fun x => by rw [h x, AddChar.one_apply])
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (AddChar.map_zero_eq_one ψ)
  let T : Fˣ := Units.mk0 t ht0
  have hT : ψ (T : F) ≠ 1 := ht
  let b := Module.finBasis F V
  let e₁ : V ≃ₗ[F] (Fin (Module.finrank F V) → F) := b.equivFun
  let f₂ : V →ₗ[F] (Fin (Module.finrank F V) → F) := LinearMap.pi fun i => β (b i)
  have hf₂ : Function.Injective f₂ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hnd y
    intro x
    rw [← b.sum_repr x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, LinearMap.smul_apply, show β (b i) y = 0 from congrFun hy i, smul_zero]
  have hbij : Function.Bijective f₂ :=
    ⟨hf₂, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hf₂⟩
  let e₂ : V ≃ₗ[F] (Fin (Module.finrank F V) → F) := LinearEquiv.ofBijective f₂ hbij
  have key : ∀ u y, β (e₁.symm u) y = u ⬝ᵥ e₂ y := by
    intro u y
    simp [e₁, e₂, f₂, Module.Basis.equivFun_symm_apply, map_sum, map_smul, dotProduct]
  have cont : ∀ g : V ≃ₗ[F] (Fin (Module.finrank F V) → F), Continuous g ∧ Continuous g.symm := fun g =>
    ⟨IsModuleTopology.continuous_of_linearMap g.toLinearMap,
      IsModuleTopology.continuous_of_linearMap g.symm.toLinearMap⟩
  have ann : ∀ (s : Fˣ) y, (∀ u ∈ box (Fin (Module.finrank F V)) s, ψ (β (e₁.symm u) y) = 1) →
      e₂ y ∈ box (Fin (Module.finrank F V)) (T * s⁻¹) := by
    intro s y h
    exact mem_box_of_forall_dot ψ hT s fun u hu => by rw [← key]; exact h u hu
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x x' y
    rw [map_add, LinearMap.add_apply, AddChar.map_add_eq_mul]
  · intro x y
    rw [hs]
  · intro x y
    exact hn _
  · exact (GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ).comp_continuous
      (IsModuleTopology.continuous_bilinear_of_finite_left β)
  · intro U hU
    have hU' : e₂.symm ⁻¹' U ∈ 𝓝 (0 : Fin (Module.finrank F V) → F) :=
      (cont e₂).2.continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨r, hr⟩ := exists_box_subset hU'
    refine ⟨e₁.symm '' box (Fin (Module.finrank F V)) (T * r⁻¹), (isCompact_box _).image (cont e₁).2,
      fun y hy => ?_⟩
    have h2 := ann (T * r⁻¹) y fun u hu => hy _ ⟨u, hu, rfl⟩
    rw [show T * (T * r⁻¹)⁻¹ = r by rw [_root_.mul_inv_rev, inv_inv, mul_comm r, mul_inv_cancel_left]] at h2
    simpa using hr h2
  · intro U hU
    have hU' : e₁.symm ⁻¹' U ∈ 𝓝 (0 : Fin (Module.finrank F V) → F) :=
      (cont e₁).2.continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨s, hs'⟩ := exists_box_subset hU'
    exact ⟨e₂.symm '' box (Fin (Module.finrank F V)) (T * s⁻¹), (isCompact_box _).image (cont e₂).2,
      fun y hy => ⟨e₂ y, ann s y fun u hu => hy _ (hs' hu), by simp⟩⟩

end GlobalTheory.KSp

end
