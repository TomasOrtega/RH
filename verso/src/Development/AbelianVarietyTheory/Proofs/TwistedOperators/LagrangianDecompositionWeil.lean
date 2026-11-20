import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatTransverseLagrangiaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterConductorExists
open ValuativeRel

noncomputable section
namespace GlobalTheory.SvNAnyChar

/- English proof (translation)
Introduce `k _ _ _ _ _ _ κ _ n d ψ0 hψ hne wT wM hT hM hTM hsurj`. Take `⟨c, hc0, hc⟩` from `GlobalTheory.CondRescale.exists_rescale_conductor_integers ψ0 hψ hne`. Set `ψ1 : AddChar k ℂ` to `ψ0.compAddMonoidHom (AddMonoidHom.mulLeft c)`. Establish `hψ1 : ∀ t, ψ1 t = ψ0 (c * t)` using `fun t => rfl`. Establish `hψ1c : Continuous ψ1`.

Establish `e : (ψ1 : k → ℂ) = fun t => ψ0 (c * t)` using `funext hψ1`. Rewrite using `[e]`. Conclude with `hψ.comp (continuous_const.mul continuous_id)`. Establish `hcond : ∀ x : k, (∀ y ∈ 𝒪[k], ψ1 (x * y) = 1) ↔ x ∈ 𝒪[k]` using `fun x => by`. Simplify using `only [hψ1]`.

Conclude with `hc x`. Set `S : (κ → k) × (κ → k) →+ (κ → k) × (κ → k)` to `AddMonoidHom.prodMap (AddMonoidHom.id _) (DistribMulAction.toAddMonoidHom _ c⁻¹)`. Establish `hS : ∀ w, S w = (w.1, c⁻¹ • w.2)` using `fun w => rfl`. Set `mc : Matrix (Fin n) (Fin d) k →+ Matrix (Fin n) (Fin d) k` to `DistribMulAction.toAddMonoidHom _ c`. Set `wT'` to `S.comp wT`.

Set `wM'` to `(S.comp wM).comp mc`. Establish `hT' : ∀ Y, wT' Y = ((wT Y).1, c⁻¹ • (wT Y).2)` using `fun Y => rfl`. Establish `hM' : ∀ z, wM' z = ((wM (c • z)).1, c⁻¹ • (wM (c • z)).2)` using `fun z => rfl`. Establish `hschr : ∀ w (φ : (κ → k) → ℂ), GlobalTheory.WeilM.schr ψ0 w φ = GlobalTheory.WeilM.schr ψ1 (S w) φ`. Introduce `w φ`.

Use function extensionality and compare the values at `x`. Simplify using `only [GlobalTheory.WeilM.schr, hS, hψ1, dotProduct_smul, smul_eq_mul]`. Use `congr 2`. Clear the denominators using the available nonvanishing facts. Take `⟨ι, hbij, htr, hmul⟩` from `GlobalTheory.T.stoneVonNeumann_schwartzBruhat_transverseLagrangians ψ1 hψ1c hcond wT' wM' (fun Y Y' => by`.

Establish `e` using `hT Y Y'`. Simplify using `only [hT', dotProduct_smul, smul_eq_mul]`. Rewrite using `[← mul_sub, e, mul_zero])`. Use the proof step `(fun z z' => by`. Establish `e` using `hM (c • z) (c • z')`.

Simplify using `only [hM', dotProduct_smul, smul_eq_mul]`. Rewrite using `[← mul_sub, e, mul_zero])`. Use the proof step `(fun Y z => by`. Establish `e` using `hTM Y (c • z)`. Simplify using `only [hT', hM', dotProduct_smul, smul_eq_mul]`.

Rewrite using `[← mul_sub, e, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.smul_apply, smul_eq_mul]`.

Use the proof step `field_simp)`. Use the proof step `(fun w => by`. Take `⟨Y, z, h⟩` from `hsurj (w.1, c • w.2)`. Use `⟨Y, c⁻¹ • z, ?_⟩` and prove the remaining obligations. Use `show S (wT Y) + S (wM (c • c⁻¹ • z)) = w`.

Rewrite using `[smul_smul, mul_inv_cancel₀ hc0, one_smul, ← map_add, h, hS]`. Simplify using `[smul_smul, inv_mul_cancel₀ hc0])`. Use `⟨ι, hbij, fun Y φ hφ => ?_, fun z φ hφ => ?_⟩` and prove the remaining obligations. Rewrite using `[hschr]`. Conclude with `htr Y φ hφ`.

Establish `e : S (wM z) = wM' (c⁻¹ • z)` using `by show S (wM z) = S (wM (c • c⁻¹ • z))`. Rewrite using `[smul_smul, mul_inv_cancel₀ hc0, one_smul]`. Rewrite using `[hschr, e, hmul _ φ hφ]`. Use function extensionality and compare the values at `Y'`. Use `congr 1`.

Rewrite using `[hψ1]`. Use `congr 1`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.smul_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem main : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [Invertible (2 : k)] {κ : Type} [Fintype κ] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (wT wM : Matrix (Fin n) (Fin d) k →+ (κ → k) × (κ → k)),
    (∀ Y Y', (wT Y).1 ⬝ᵥ (wT Y').2 - (wT Y').1 ⬝ᵥ (wT Y).2 = 0) →
    (∀ z z', (wM z).1 ⬝ᵥ (wM z').2 - (wM z').1 ⬝ᵥ (wM z).2 = 0) →
    (∀ Y z, (wT Y).1 ⬝ᵥ (wM z).2 - (wM z).1 ⬝ᵥ (wT Y).2 = ∑ i, ∑ j, Y i j * z i j) →
    (∀ w, ∃ Y z, wT Y + wM z = w) →
    ∃ ι : ((κ → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ),
      Set.BijOn ι (GlobalTheory.WeilM.SB (κ → k) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) : Set _) ∧
      (∀ Y, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wT Y) φ) = fun Y' => ι φ (Y' + Y)) ∧
      (∀ z, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), ι (GlobalTheory.WeilM.schr ψ0 (wM z) φ) = fun Y' => ψ0 (∑ i, ∑ j, Y' i j * z i j) * ι φ Y') := by
  intro k _ _ _ _ _ _ κ _ n d ψ0 hψ hne wT wM hT hM hTM hsurj
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.CondRescale.exists_rescale_conductor_integers ψ0 hψ hne
  let ψ1 : AddChar k ℂ := ψ0.compAddMonoidHom (AddMonoidHom.mulLeft c)
  have hψ1 : ∀ t, ψ1 t = ψ0 (c * t) := fun t => rfl
  have hψ1c : Continuous ψ1 := by
    have e : (ψ1 : k → ℂ) = fun t => ψ0 (c * t) := funext hψ1
    rw [e]; exact hψ.comp (continuous_const.mul continuous_id)
  have hcond : ∀ x : k, (∀ y ∈ 𝒪[k], ψ1 (x * y) = 1) ↔ x ∈ 𝒪[k] := fun x => by
    simp only [hψ1]; exact hc x
  let S : (κ → k) × (κ → k) →+ (κ → k) × (κ → k) :=
    AddMonoidHom.prodMap (AddMonoidHom.id _) (DistribMulAction.toAddMonoidHom _ c⁻¹)
  have hS : ∀ w, S w = (w.1, c⁻¹ • w.2) := fun w => rfl
  let mc : Matrix (Fin n) (Fin d) k →+ Matrix (Fin n) (Fin d) k := DistribMulAction.toAddMonoidHom _ c
  let wT' := S.comp wT
  let wM' := (S.comp wM).comp mc
  have hT' : ∀ Y, wT' Y = ((wT Y).1, c⁻¹ • (wT Y).2) := fun Y => rfl
  have hM' : ∀ z, wM' z = ((wM (c • z)).1, c⁻¹ • (wM (c • z)).2) := fun z => rfl
  have hschr : ∀ w (φ : (κ → k) → ℂ), GlobalTheory.WeilM.schr ψ0 w φ = GlobalTheory.WeilM.schr ψ1 (S w) φ := by
    intro w φ; funext x
    simp only [GlobalTheory.WeilM.schr, hS, hψ1, dotProduct_smul, smul_eq_mul]
    congr 2
    field_simp
  obtain ⟨ι, hbij, htr, hmul⟩ := GlobalTheory.T.stoneVonNeumann_schwartzBruhat_transverseLagrangians ψ1 hψ1c hcond wT' wM'
    (fun Y Y' => by
      have e := hT Y Y'
      simp only [hT', dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, e, mul_zero])
    (fun z z' => by
      have e := hM (c • z) (c • z')
      simp only [hM', dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, e, mul_zero])
    (fun Y z => by
      have e := hTM Y (c • z)
      simp only [hT', hM', dotProduct_smul, smul_eq_mul]
      rw [← mul_sub, e, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.smul_apply, smul_eq_mul]
      field_simp)
    (fun w => by
      obtain ⟨Y, z, h⟩ := hsurj (w.1, c • w.2)
      refine ⟨Y, c⁻¹ • z, ?_⟩
      show S (wT Y) + S (wM (c • c⁻¹ • z)) = w
      rw [smul_smul, mul_inv_cancel₀ hc0, one_smul, ← map_add, h, hS]
      simp [smul_smul, inv_mul_cancel₀ hc0])
  refine ⟨ι, hbij, fun Y φ hφ => ?_, fun z φ hφ => ?_⟩
  · rw [hschr]; exact htr Y φ hφ
  · have e : S (wM z) = wM' (c⁻¹ • z) := by
      show S (wM z) = S (wM (c • c⁻¹ • z))
      rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
    rw [hschr, e, hmul _ φ hφ]
    funext Y'
    congr 1
    rw [hψ1]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.smul_apply, smul_eq_mul]
    field_simp

end GlobalTheory.SvNAnyChar
