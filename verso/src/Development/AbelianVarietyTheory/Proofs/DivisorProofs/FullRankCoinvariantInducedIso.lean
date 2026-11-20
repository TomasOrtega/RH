import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableFullRankZetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankZetaSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankZetaKernelStatement

noncomputable section

open MeasureTheory GlobalTheory.SplitFlip
open scoped Topology Matrix

namespace GlobalTheory.FullRankCoinv

/- English proof (translation)
Introduce `k _ _ _ _ n d Ψ hΨ`. Establish `h1 : ∀ᶠ u in 𝓝 (1 : GL (Fin d) k), ∀ X ∈ tsupport Ψ, Ψ (X * u.val) = Ψ X`. Use `IsCompact.eventually_forall_of_forall_eventually hΨ.2 fun y _ => ?_` and prove the remaining obligations. Establish `h2 : IsLocallyConstant fun q : GL (Fin d) k × Matrix (Fin n) (Fin d) k => (Ψ (q.2 * q.1.val), Ψ q.2)` using `(hΨ.1.comp_continuous (by fun_prop)).prodMk (hΨ.1.comp_continuous continuous_snd)`. Use `filter_upwards [h2.eventually_eq (1, y)] with q hq`.

Simplify using `only [Prod.mk.injEq, Units.val_one, Matrix.mul_one] at hq`. Rewrite using `[hq.1, hq.2]`. Establish `h3 : ∀ᶠ u in 𝓝 (1 : GL (Fin d) k), ∀ X ∈ tsupport Ψ, Ψ (X * (u⁻¹).val) = Ψ X`. Establish `ht : Filter.Tendsto (fun u : GL (Fin d) k => u⁻¹) (𝓝 1) (𝓝 1)`. Simplify using `using (continuous_inv.tendsto (1 : GL (Fin d) k))`.

Conclude with `ht.eventually h1`. Use `⟨_, h1.and h3, fun u hu X => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hX : X ∈ tsupport Ψ`. Conclude with `hu.1 X hX`. Distinguish the cases in `hX' : X * u.val ∈ tsupport Ψ`.

Use `hu.2 _ hX'` as an intermediate fact. Rewrite `this` using `[Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]`. Conclude with `this.symm`. Rewrite using `[image_eq_zero_of_notMem_tsupport hX, image_eq_zero_of_notMem_tsupport hX']`.
-/
theorem sb_right_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (Ψ : Matrix (Fin n) (Fin d) k → ℂ), Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) →
    ∃ U ∈ nhds (1 : GL (Fin d) k), ∀ u ∈ U, ∀ X : Matrix (Fin n) (Fin d) k, Ψ (X * u.val) = Ψ X := by
  intro k _ _ _ _ n d Ψ hΨ
  have h1 : ∀ᶠ u in 𝓝 (1 : GL (Fin d) k), ∀ X ∈ tsupport Ψ, Ψ (X * u.val) = Ψ X := by
    refine IsCompact.eventually_forall_of_forall_eventually hΨ.2 fun y _ => ?_
    have h2 : IsLocallyConstant fun q : GL (Fin d) k × Matrix (Fin n) (Fin d) k => (Ψ (q.2 * q.1.val), Ψ q.2) :=
      (hΨ.1.comp_continuous (by fun_prop)).prodMk (hΨ.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (1, y)] with q hq
    simp only [Prod.mk.injEq, Units.val_one, Matrix.mul_one] at hq
    rw [hq.1, hq.2]
  have h3 : ∀ᶠ u in 𝓝 (1 : GL (Fin d) k), ∀ X ∈ tsupport Ψ, Ψ (X * (u⁻¹).val) = Ψ X := by
    have ht : Filter.Tendsto (fun u : GL (Fin d) k => u⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv.tendsto (1 : GL (Fin d) k))
    exact ht.eventually h1
  refine ⟨_, h1.and h3, fun u hu X => ?_⟩
  by_cases hX : X ∈ tsupport Ψ
  · exact hu.1 X hX
  by_cases hX' : X * u.val ∈ tsupport Ψ
  · have := hu.2 _ hX'
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hX, image_eq_zero_of_notMem_tsupport hX']

/- English proof (translation)
Introduce `k _ _ _ _ n d ν hnd hν`. Use `letI : MeasurableSpace k := borel k`. Use `haveI : BorelSpace k := ⟨rfl⟩`. Set `Z₀ : fullRk k n d →ₗ[ℂ] (GL (Fin d) k → ℂ)` to `{ toFun := fun Ψ h => smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ.1 (Y0 k n d * h.val) map_add' := fun Ψ Φ => by`. Use function extensionality and compare the values at `h`.

Simplify using `only [smallF, Submodule.coe_add, Pi.add_apply]`. Rewrite using `[← integral_add (GlobalTheory.T.integrable_full_rank_zeta k n d ν hν Ψ.1 Ψ.2 _) (GlobalTheory.T.integrable_full_rank_zeta k n d ν hν Φ.1 Φ.2 _)]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Expand and normalize the polynomial expressions, which then agree.

Use the proof step `map_smul' := fun c Ψ => by`. Use function extensionality and compare the values at `h`. Simplify using `only [smallF, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]`. Rewrite using `[← integral_const_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `g`. Use `ring }`. Take `⟨Z, hZ⟩` from `LinearMap.exists_extend Z₀`. Establish `hZΨ : ∀ Ψ (hΨ : Ψ ∈ fullRk k n d), Z Ψ = fun h => smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (Y0 k n d * h.val)` using `fun Ψ hΨ => LinearMap.congr_fun hZ ⟨Ψ, hΨ⟩`. Use `⟨Z, fun Ψ hΨ => ?_, fun f hf => ?_, fun Ψ hΨ h0 => ?_, fun Ψ hΨ h₀ => ?_⟩` and prove the remaining obligations.

Rewrite using `[hZΨ Ψ hΨ]`. Use `⟨?_, fun b h D hD => ?_⟩` and prove the remaining obligations. Take `⟨U, hU, hinv⟩` from `sb_right_invariant k n d Ψ hΨ.1`. Use `⟨U, hU, fun h u hu => ?_⟩` and prove the remaining obligations. Simplify using `only [smallF]`.

Use `congr 1`. Use function extensionality and compare the values at `g`. Rewrite using `[Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv u hu, Matrix.mul_assoc]`. Establish `e1 : Y0 k n d * (b * h).val = D.val * (Y0 k n d * h.val)`. Rewrite using `[Units.val_mul, ← Matrix.mul_assoc, hD, Matrix.mul_assoc]`.

Establish `key` using `smallF_mul_left (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ D (Y0 k n d * h.val)`. Simplify using `only [Fintype.card_fin] at key`. Use `show smallF _ ν Ψ (Y0 k n d * (b * h).val) = _`. Rewrite using `[e1]`. Use `beta_reduce`.

Rewrite using `[← key, Units.val_inv_eq_inv_val, neg_div, apow_neg]`. Establish `h1 : (ν (gdet D) : ℂ) ≠ 0` using `Units.ne_zero _`. Establish `h2` using `apow_ne_zero (gdet D) ((d : ℂ) / 2)`. Clear the denominators using the available nonvanishing facts. Take `⟨Ψ, hΨ, hf'⟩` from `GlobalTheory.T.full_rank_zeta_surjective k n d ν hnd hν f hf`.

Conclude with `⟨Ψ, hΨ, by rw [hZΨ Ψ hΨ]; funext h; exact hf' h⟩`. Use `GlobalTheory.T.full_rank_zeta_kernel k n d ν hnd hν Ψ hΨ fun h => ?_` and prove the remaining obligations. Use `congrFun h0 h` as an intermediate fact. Rewrite `this` using `[hZΨ Ψ hΨ]`. Then use the resulting hypothesis. Establish `hmem : (fun Y => Ψ (Y * h₀.1)) ∈ fullRk k n d`.

Set `e : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k` to `{ toFun := fun X => X * h₀.1 invFun := fun X => X * (h₀⁻¹).1 left_inv := fun X => by simp [Matrix.mul_assoc] right_inv := fun X => by simp [Matrix.mul_assoc] continuous_toFun := by fun_prop continuous_invFun := by fun_prop }`. Use `⟨⟨hΨ.1.1.comp_continuous e.continuous, hΨ.1.2.comp_homeomorph e⟩, fun Y hY => hΨ.2 _ ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units h₀)]` and apply the resulting hypothesis. Rewrite using `[hZΨ _ hmem, hZΨ _ hΨ]`. Use function extensionality and compare the values at `h`.

Simplify using `only [smallF, Units.val_mul, Matrix.mul_assoc]`.
-/
theorem fibre_coinvariants : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∃ Z : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] (GL (Fin d) k → ℂ),
      (∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ ∈ GlobalTheory.FullRankCoinv.indSp k n d ν) ∧
      (∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν, ∃ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ = f) ∧
      (∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ = 0 → Ψ ∈ GlobalTheory.FullRankCoinv.augRk n d ν) ∧
      ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ h₀ : GL (Fin d) k,
        Z (fun Y => Ψ (Y * h₀.1)) = fun h => Z Ψ (h * h₀) := by
  intro k _ _ _ _ n d ν hnd hν
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  let Z₀ : fullRk k n d →ₗ[ℂ] (GL (Fin d) k → ℂ) :=
    { toFun := fun Ψ h => smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ.1 (Y0 k n d * h.val)
      map_add' := fun Ψ Φ => by
        funext h
        simp only [smallF, Submodule.coe_add, Pi.add_apply]
        rw [← integral_add (GlobalTheory.T.integrable_full_rank_zeta k n d ν hν Ψ.1 Ψ.2 _) (GlobalTheory.T.integrable_full_rank_zeta k n d ν hν Φ.1 Φ.2 _)]
        congr 1; funext g; ring
      map_smul' := fun c Ψ => by
        funext h
        simp only [smallF, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; funext g; ring }
  obtain ⟨Z, hZ⟩ := LinearMap.exists_extend Z₀
  have hZΨ : ∀ Ψ (hΨ : Ψ ∈ fullRk k n d),
      Z Ψ = fun h => smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ (Y0 k n d * h.val) :=
    fun Ψ hΨ => LinearMap.congr_fun hZ ⟨Ψ, hΨ⟩
  refine ⟨Z, fun Ψ hΨ => ?_, fun f hf => ?_, fun Ψ hΨ h0 => ?_, fun Ψ hΨ h₀ => ?_⟩
  · rw [hZΨ Ψ hΨ]
    refine ⟨?_, fun b h D hD => ?_⟩
    · obtain ⟨U, hU, hinv⟩ := sb_right_invariant k n d Ψ hΨ.1
      refine ⟨U, hU, fun h u hu => ?_⟩
      simp only [smallF]
      congr 1; funext g
      rw [Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv u hu, Matrix.mul_assoc]
    · have e1 : Y0 k n d * (b * h).val = D.val * (Y0 k n d * h.val) := by
        rw [Units.val_mul, ← Matrix.mul_assoc, hD, Matrix.mul_assoc]
      have key := smallF_mul_left (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ D (Y0 k n d * h.val)
      simp only [Fintype.card_fin] at key
      show smallF _ ν Ψ (Y0 k n d * (b * h).val) = _
      rw [e1]
      beta_reduce
      rw [← key, Units.val_inv_eq_inv_val, neg_div, apow_neg]
      have h1 : (ν (gdet D) : ℂ) ≠ 0 := Units.ne_zero _
      have h2 := apow_ne_zero (gdet D) ((d : ℂ) / 2)
      field_simp
  · obtain ⟨Ψ, hΨ, hf'⟩ := GlobalTheory.T.full_rank_zeta_surjective k n d ν hnd hν f hf
    exact ⟨Ψ, hΨ, by rw [hZΨ Ψ hΨ]; funext h; exact hf' h⟩
  · refine GlobalTheory.T.full_rank_zeta_kernel k n d ν hnd hν Ψ hΨ fun h => ?_
    have := congrFun h0 h
    rwa [hZΨ Ψ hΨ] at this
  · have hmem : (fun Y => Ψ (Y * h₀.1)) ∈ fullRk k n d := by
      let e : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k :=
        { toFun := fun X => X * h₀.1
          invFun := fun X => X * (h₀⁻¹).1
          left_inv := fun X => by simp [Matrix.mul_assoc]
          right_inv := fun X => by simp [Matrix.mul_assoc]
          continuous_toFun := by fun_prop
          continuous_invFun := by fun_prop }
      refine ⟨⟨hΨ.1.1.comp_continuous e.continuous, hΨ.1.2.comp_homeomorph e⟩, fun Y hY => hΨ.2 _ ?_⟩
      rwa [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units h₀)]
    rw [hZΨ _ hmem, hZΨ _ hΨ]
    funext h
    simp only [smallF, Units.val_mul, Matrix.mul_assoc]

end GlobalTheory.FullRankCoinv
