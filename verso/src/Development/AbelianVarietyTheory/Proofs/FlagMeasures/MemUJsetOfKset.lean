import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.RealPlaceAnalysis.FinalF

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory
namespace LowKProj

section General
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Introduce `x hx`. Take `⟨hidem, -, hrange⟩` from `hE`. Rewrite `hx` using `[← hrange]`. Take `⟨y, rfl⟩` from `hx`. Express the relevant statement in the definitionally equal form `E (E y) = E y`.

Rewrite using `[← ContinuousLinearMap.comp_apply, hidem]`.
-/
theorem fix_of_mem {E : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S) :
    ∀ x ∈ S, E x = x := by
  intro x hx
  obtain ⟨hidem, -, hrange⟩ := hE
  rw [← hrange] at hx
  obtain ⟨y, rfl⟩ := hx
  change E (E y) = E y
  rw [← ContinuousLinearMap.comp_apply, hidem]

/- English proof (translation)
Rewrite using `[← hE.2.2]`. Conclude with `⟨x, rfl⟩`.
-/
theorem apply_mem {E : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S) (x : H) :
    E x ∈ S := by
  rw [← hE.2.2]
  exact ⟨x, rfl⟩

/- English proof (translation)
Take `⟨hidem, hsym, -⟩` from `hE`. Use `ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_` and prove the remaining obligations. Establish `hEE : E (E x) = E x` using `by rw [← ContinuousLinearMap.comp_apply, hidem]`. Establish `hsq : ‖E x‖ ^ 2 ≤ ‖x‖ * ‖E x‖`. Rewrite using `[← inner_self_eq_norm_sq (𝕜 := ℂ), hsym, hEE]`.

Conclude with `re_inner_le_norm x (E x)`. Establish `h0 : 0 ≤ ‖x‖` using `norm_nonneg x`. Establish `h1 : 0 ≤ ‖E x‖` using `norm_nonneg (E x)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_le_one {E : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S) :
    ‖E‖ ≤ 1 := by
  obtain ⟨hidem, hsym, -⟩ := hE
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  have hEE : E (E x) = E x := by rw [← ContinuousLinearMap.comp_apply, hidem]
  have hsq : ‖E x‖ ^ 2 ≤ ‖x‖ * ‖E x‖ := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hsym, hEE]
    exact re_inner_le_norm x (E x)
  have h0 : 0 ≤ ‖x‖ := norm_nonneg x
  have h1 : 0 ≤ ‖E x‖ := norm_nonneg (E x)
  nlinarith

/- English proof (translation)
Establish `: CompleteSpace S` using `FiniteDimensional.complete ℂ S`. Use `⟨S.starProjection, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `S.isIdempotentElem_starProjection`. Conclude with `S.inner_starProjection_left_eq_right`. Conclude with `S.range_starProjection`.
-/
theorem exists_proj (S : Submodule ℂ H) [FiniteDimensional ℂ S] :
    ∃ E : H →L[ℂ] H, IsOrthProjOnto E S := by
  have : CompleteSpace S := FiniteDimensional.complete ℂ S
  refine ⟨S.starProjection, ?_, ?_, ?_⟩
  · exact S.isIdempotentElem_starProjection
  · exact S.inner_starProjection_left_eq_right
  · exact S.range_starProjection

/- English proof (translation)
Establish `hfix` using `fix_of_mem hE`. Establish `hmem` using `apply_mem hE`. Establish `hsym` using `hE.2.1`. Use extensionality with `x`. Simplify using `only [ContinuousLinearMap.comp_apply]`.

Use `ext_inner_right ℂ fun y => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem comm_of_stable {E A B : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S)
    (hAB : ∀ x y, ⟪A x, y⟫_ℂ = ⟪x, B y⟫_ℂ) (hA : ∀ v ∈ S, A v ∈ S) (hB : ∀ v ∈ S, B v ∈ S) :
    E ∘L A = A ∘L E := by
  have hfix := fix_of_mem hE
  have hmem := apply_mem hE
  have hsym := hE.2.1
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  refine ext_inner_right ℂ fun y => ?_

  calc ⟪E (A x), y⟫_ℂ = ⟪A x, E y⟫_ℂ := hsym _ _
    _ = ⟪x, B (E y)⟫_ℂ := hAB _ _
    _ = ⟪x, E (B (E y))⟫_ℂ := by rw [hfix _ (hB _ (hmem y))]
    _ = ⟪E x, B (E y)⟫_ℂ := (hsym _ _).symm
    _ = ⟪A (E x), E y⟫_ℂ := (hAB _ _).symm
    _ = ⟪E (A (E x)), y⟫_ℂ := (hsym _ _).symm
    _ = ⟪A (E x), y⟫_ℂ := by rw [hfix _ (hA _ (hmem x))]

end General

/- English proof (translation)
Take `⟨hu, hc⟩` from `hk`. Establish `h2 : star k * k = 1` using `(Matrix.mem_unitaryGroup_iff').1 hu`. Use `show kᴴ * Jm ε * k = Jm ε`. Rewrite using `[← Matrix.star_eq_conjTranspose, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, h2, Matrix.one_mul]`.
-/
theorem mem_UJset_of_Kset {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) : k ∈ UJset ε := by
  obtain ⟨hu, hc⟩ := hk
  have h2 : star k * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hu
  show kᴴ * Jm ε * k = Jm ε
  rw [← Matrix.star_eq_conjTranspose, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, h2, Matrix.one_mul]

/- English proof (translation)
Take `⟨hu, hc⟩` from `hk`. Establish `h1 : k * star k = 1` using `(Matrix.mem_unitaryGroup_iff).1 hu`. Establish `h2 : star k * k = 1` using `(Matrix.mem_unitaryGroup_iff').1 hu`. Use `⟨(Matrix.mem_unitaryGroup_iff).2 (by rw [star_star]; exact h2), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma star_mem_Kset {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) : star k ∈ Kset ε := by
  obtain ⟨hu, hc⟩ := hk
  have h1 : k * star k = 1 := (Matrix.mem_unitaryGroup_iff).1 hu
  have h2 : star k * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hu
  refine ⟨(Matrix.mem_unitaryGroup_iff).2 (by rw [star_star]; exact h2), ?_⟩
  calc star k * Jm ε = star k * Jm ε * (k * star k) := by rw [h1, Matrix.mul_one]
    _ = star k * (Jm ε * k) * star k := by simp only [Matrix.mul_assoc]
    _ = star k * (k * Jm ε) * star k := by rw [hc]
    _ = (star k * k) * Jm ε * star k := by simp only [Matrix.mul_assoc]
    _ = Jm ε * star k := by rw [h2, Matrix.one_mul]

/- English proof (translation)
Take `⟨⟨h1, hmul⟩, hiso, -⟩` from `hσ`. Establish `hkU` using `mem_UJset_of_Kset hk`. Establish `hsU` using `mem_UJset_of_Kset (star_mem_Kset hk)`. Establish `hks : k * star k = 1` using `(Matrix.mem_unitaryGroup_iff).1 hk.1`. Set `L : H →ₗᵢ[ℂ] H` to `⟨(σ k : H →ₗ[ℂ] H), fun v => hiso k hkU v⟩`.

Establish `hy : σ k (σ (star k) y) = y`. Rewrite using `[← ContinuousLinearMap.comp_apply, ← hmul k hkU (star k) hsU, hks, h1]`. Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation. Express the relevant statement in the definitionally equal form `⟪σ k x, y⟫_ℂ = ⟪σ k x, σ k (σ (star k) y)⟫_ℂ`.

Rewrite using `[hy]`. Use `_ = ⟪x, σ (star k) y⟫_ℂ := L.inner_map_map _ _`.
-/
theorem inner_adj {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (x y : H) :
    ⟪σ k x, y⟫_ℂ = ⟪x, σ (star k) y⟫_ℂ := by
  obtain ⟨⟨h1, hmul⟩, hiso, -⟩ := hσ
  have hkU := mem_UJset_of_Kset hk
  have hsU := mem_UJset_of_Kset (star_mem_Kset hk)
  have hks : k * star k = 1 := (Matrix.mem_unitaryGroup_iff).1 hk.1

  let L : H →ₗᵢ[ℂ] H := ⟨(σ k : H →ₗ[ℂ] H), fun v => hiso k hkU v⟩
  have hy : σ k (σ (star k) y) = y := by
    rw [← ContinuousLinearMap.comp_apply, ← hmul k hkU (star k) hsU, hks, h1]
    rfl
  calc ⟪σ k x, y⟫_ℂ = ⟪L x, L (σ (star k) y)⟫_ℂ := by
        change ⟪σ k x, y⟫_ℂ = ⟪σ k x, σ k (σ (star k) y)⟫_ℂ
        rw [hy]
    _ = ⟪x, σ (star k) y⟫_ℂ := L.inner_map_map _ _

/- English proof (translation)
Introduce `g hg v hv`. Establish `hle : lowKSub ε lam σ ≤ (lowKSub ε lam σ).comap (σ g : H →ₗ[ℂ] H)` using `sSup_le fun S hS w hw => le_sSup hS (hS.2.1 g hg w hw)`. Conclude with `hle hv`.
-/
theorem lowKSub_stable {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsKStableOn ε σ (lowKSub ε lam σ) := by
  intro g hg v hv

  have hle : lowKSub ε lam σ ≤ (lowKSub ε lam σ).comap (σ g : H →ₗ[ℂ] H) :=
    sSup_le fun S hS w hw => le_sSup hS (hS.2.1 g hg w hw)
  exact hle hv

/- English proof (translation)
Introduce `n ε lam H _ _ _ σ hDS`. Take `⟨-, -, hrep, -, -, ⟨S, hS⟩, -⟩` from `hDS`. Use `⟨?_, lowKSub_stable ε lam σ, fun _ => exists_proj _, ?_⟩` and prove the remaining obligations. Take `⟨v, hvS, hv0, hwt⟩` from `hS.2.2.2.1`. Establish `hn : (‖v‖ : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.2 hv0`.

Use `⟨((‖v‖ : ℂ)⁻¹) • v, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_smul, norm_inv, Complex.norm_real, norm_norm]`. Conclude with `inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)`. Establish `hle : S ≤ lowKSub ε lam σ` using `le_sSup (show S ∈ {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S} from hS)`. Conclude with `Submodule.smul_mem _ _ (hle hvS)`.

Introduce `θ hθ`. Rewrite using `[map_smul, hwt θ hθ, smul_comm]`. Introduce `E hE`. Use `⟨norm_le_one hE, fix_of_mem hE, fun k hk => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `comm_of_stable hE (inner_adj hrep hk) (fun v hv => lowKSub_stable ε lam σ k hk v hv) (fun v hv => lowKSub_stable ε lam σ (star k) (star_mem_Kset hk) v hv)`.

Conclude with `ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by`. Rewrite using `[hrep.2.1 k (mem_UJset_of_Kset hk) x, one_mul]`.
-/
theorem lowK_projection : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → (∃ w, IsHighestUnit ε lam σ w) ∧ IsKStableOn ε σ (lowKSub ε lam σ) ∧ (FiniteDimensional ℂ (lowKSub ε lam σ) → ∃ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub ε lam σ)) ∧ ∀ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub ε lam σ) → ‖E‖ ≤ 1 ∧ (∀ x ∈ lowKSub ε lam σ, E x = x) ∧ ∀ k ∈ Kset ε, E ∘L σ k = σ k ∘L E ∧ ‖σ k‖ ≤ 1 := by
  intro n ε lam H _ _ _ σ hDS
  obtain ⟨-, -, hrep, -, -, ⟨S, hS⟩, -⟩ := hDS
  refine ⟨?_, lowKSub_stable ε lam σ, fun _ => exists_proj _, ?_⟩
  ·
    obtain ⟨v, hvS, hv0, hwt⟩ := hS.2.2.2.1
    have hn : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hv0
    refine ⟨((‖v‖ : ℂ)⁻¹) • v, ?_, ?_, ?_⟩
    · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)
    · have hle : S ≤ lowKSub ε lam σ :=
        le_sSup (show S ∈ {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S} from hS)
      exact Submodule.smul_mem _ _ (hle hvS)
    · intro θ hθ
      rw [map_smul, hwt θ hθ, smul_comm]
  · intro E hE
    refine ⟨norm_le_one hE, fix_of_mem hE, fun k hk => ⟨?_, ?_⟩⟩
    · exact comm_of_stable hE (inner_adj hrep hk) (fun v hv => lowKSub_stable ε lam σ k hk v hv)
        (fun v hv => lowKSub_stable ε lam σ (star k) (star_mem_Kset hk) v hv)
    · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
        rw [hrep.2.1 k (mem_UJset_of_Kset hk) x, one_mul]

end LowKProj
end GlobalTheory
