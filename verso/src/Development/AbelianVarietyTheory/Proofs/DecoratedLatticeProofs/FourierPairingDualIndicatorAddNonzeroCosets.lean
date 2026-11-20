import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField

noncomputable section

open MeasureTheory ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd Lifts InDual)

namespace GlobalTheory.FinPl.Comm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n]

open Classical in

/- English proof (translation)
Establish `h` using `integral_add_right_eq_self (μ := μ) (fun y => vecInd L y * (χ (e * (η ⬝ᵥ y)) : ℂ)) y₀`. Establish `e2 : ∀ y, vecInd L (y + y₀) * (χ (e * (η ⬝ᵥ (y + y₀))) : ℂ) = (χ (e * (η ⬝ᵥ y₀)) : ℂ) * (vecInd L y * (χ (e * (η ⬝ᵥ y)) : ℂ))` using `fun y => by`. Rewrite using `[dotProduct_add, mul_add, AddChar.map_add_eq_mul, Circle.coe_mul, vecInd, vecInd, if_congr (L.add_mem_iff_left hy₀) rfl rfl]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e2] at h`.

Rewrite `h` using `[integral_const_mul]`. Assume the negation of the conclusion as `h0`. Conclude with `hne (Circle.ext (by simpa using (mul_eq_right₀ h0).1 h))`.
-/
theorem integral_vecInd_eq_zero [MeasurableSpace k] [BorelSpace k] (χ : AddChar k Circle) (e : k)
    (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n → k)) (η : n → k) {y₀ : n → k}
    (hy₀ : y₀ ∈ L) (hne : χ (e * (η ⬝ᵥ y₀)) ≠ 1) :
    ∫ y, vecInd L y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ = 0 := by
  have h := integral_add_right_eq_self (μ := μ) (fun y => vecInd L y * (χ (e * (η ⬝ᵥ y)) : ℂ)) y₀
  have e2 : ∀ y, vecInd L (y + y₀) * (χ (e * (η ⬝ᵥ (y + y₀))) : ℂ) =
      (χ (e * (η ⬝ᵥ y₀)) : ℂ) * (vecInd L y * (χ (e * (η ⬝ᵥ y)) : ℂ)) := fun y => by
    rw [dotProduct_add, mul_add, AddChar.map_add_eq_mul, Circle.coe_mul, vecInd, vecInd,
      if_congr (L.add_mem_iff_left hy₀) rfl rfl]
    ring
  simp only [e2] at h
  rw [integral_const_mul] at h
  by_contra h0
  exact hne (Circle.ext (by simpa using (mul_eq_right₀ h0).1 h))

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, f x ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hf (LinearMap.ext h)`. Take `⟨y, rfl⟩` from `Red.mk_surjective L x`.

Take `⟨t, ht⟩` from `residue_surjective (R := 𝒪[k]) (b * (f (Red.mk L y))⁻¹)`. Take `⟨s, hs, hs'⟩` from `hF (t • y)`. Use `⟨_, (t • y).2, s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[hs', map_smul, ← Red.residue_smul, map_smul, ht, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hx, mul_one]`.
-/
theorem exists_lifts_value (L : Submodule 𝒪[k] (n → k)) {f : Module.Dual 𝓀[k] (Red L)} (hf : f ≠ 0)
    {F : n → k} (hF : Lifts L F f) (b : 𝓀[k]) :
    ∃ y₀ ∈ L, ∃ s : 𝒪[k], (s : k) = F ⬝ᵥ y₀ ∧ residue 𝒪[k] s = b := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (LinearMap.ext h)
  obtain ⟨y, rfl⟩ := Red.mk_surjective L x
  obtain ⟨t, ht⟩ := residue_surjective (R := 𝒪[k]) (b * (f (Red.mk L y))⁻¹)
  obtain ⟨s, hs, hs'⟩ := hF (t • y)
  refine ⟨_, (t • y).2, s, hs, ?_⟩
  rw [hs', map_smul, ← Red.residue_smul, map_smul, ht, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hx, mul_one]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, resChar χ hχ q a ≠ 1 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `resChar_ne_one hχ q (by ext a; rw [h a, AddChar.one_apply])`. Apply the tactic sequence `have hee : e * e = 1 := by rcases he with rfl | rfl <;> norm_num`.

Establish `heo : e ∈ 𝒪[k]`. Break down `he with rfl | rfl` into its components or cases. Conclude with `one_mem _`. Conclude with `neg_mem (one_mem _)`. Set `ε : 𝒪[k]` to `⟨e, heo⟩`.

Establish `hε : residue 𝒪[k] ε * residue 𝒪[k] ε = 1`. Rewrite using `[← map_mul, show ε * ε = 1 from Subtype.ext hee, map_one]`. Take `⟨y₀, hy₀, s, hs, hs'⟩` from `exists_lifts_value L hf hF (residue 𝒪[k] ε * a)`. Use `integral_vecInd_eq_zero χ e μ L η hy₀ fun h => ha ?_` and prove the remaining obligations. Establish `hl : e * ((η - q.inv • F) ⬝ᵥ y₀) ∈ 𝒪[k]` using `mul_mem heo (hη y₀ hy₀)`.

Establish `hsplit : e * (η ⬝ᵥ y₀) = q.inv * ((ε * s : 𝒪[k]) : k) + e * ((η - q.inv • F) ⬝ᵥ y₀)`. Rewrite using `[sub_dotProduct, smul_dotProduct, smul_eq_mul, Subring.coe_mul, hs]`. Express the relevant statement in the definitionally equal form `_ = _ * (e * _) + _`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[hsplit, AddChar.map_add_eq_mul, apply_int_eq_one hχ ⟨_, hl⟩, mul_one]`.

Rewrite using `[show a = residue 𝒪[k] (ε * s) by rw [map_mul, hs', ← mul_assoc, hε, one_mul], resChar_residue, h]`. Both sides reduce to the same expression.
-/
theorem integral_vecInd_coset [MeasurableSpace k] [BorelSpace k] (q : Unif k) (χ : AddChar k Circle)
    (hχ : HasConductor χ 1) (e : k) (he : e = 1 ∨ e = -1) (μ : Measure (n → k)) [μ.IsAddHaarMeasure]
    (L : Submodule 𝒪[k] (n → k)) {f : Module.Dual 𝓀[k] (Red L)} (hf : f ≠ 0) {F η : n → k}
    (hF : Lifts L F f) (hη : InDual L (η - q.inv • F)) :
    ∫ y, vecInd L y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, resChar χ hχ q a ≠ 1 := by
    by_contra h
    push Not at h
    exact resChar_ne_one hχ q (by ext a; rw [h a, AddChar.one_apply])
  have hee : e * e = 1 := by rcases he with rfl | rfl <;> norm_num
  have heo : e ∈ 𝒪[k] := by
    rcases he with rfl | rfl
    · exact one_mem _
    · exact neg_mem (one_mem _)
  let ε : 𝒪[k] := ⟨e, heo⟩
  have hε : residue 𝒪[k] ε * residue 𝒪[k] ε = 1 := by
    rw [← map_mul, show ε * ε = 1 from Subtype.ext hee, map_one]
  obtain ⟨y₀, hy₀, s, hs, hs'⟩ := exists_lifts_value L hf hF (residue 𝒪[k] ε * a)
  refine integral_vecInd_eq_zero χ e μ L η hy₀ fun h => ha ?_
  have hl : e * ((η - q.inv • F) ⬝ᵥ y₀) ∈ 𝒪[k] := mul_mem heo (hη y₀ hy₀)
  have hsplit : e * (η ⬝ᵥ y₀) = q.inv * ((ε * s : 𝒪[k]) : k) + e * ((η - q.inv • F) ⬝ᵥ y₀) := by
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, Subring.coe_mul, hs]
    change _ = _ * (e * _) + _
    ring
  rw [hsplit, AddChar.map_add_eq_mul, apply_int_eq_one hχ ⟨_, hl⟩, mul_one] at h
  rw [show a = residue 𝒪[k] (ε * s) by rw [map_mul, hs', ← mul_assoc, hε, one_mul], resChar_residue, h]
  rfl

end GlobalTheory.FinPl.Comm

namespace GlobalTheory.FinPl.Comm

/- English proof (translation)
Introduce `k _ _ _ _ _ _ n _ _ q χ hχ e he μ _ L _`. Unfold `fpair`. Use `congr 1`. Use function extensionality and compare the values at `η`. Rewrite using `[Pi.add_apply, mul_add, Finset.sum_apply, Finset.mul_sum, add_eq_left]`.

Use `Finset.sum_eq_zero fun Q hQ => ?_` and prove the remaining obligations. Establish `hL : Q.lat = L` using `mem_withLat.1 hQ`. Unfold `cosetInd`. Use `split_ifs with h`. Take `⟨F, hF, hD⟩` from `h`.

Establish `h0` using `integral_vecInd_coset q χ hχ e he μ Q.lat Q.red_ne hF hD`. Rewrite `h0` using `[hL]`. Rewrite using `[h0, zero_mul]`. Rewrite using `[mul_zero]`.
-/
theorem fpair_vecInd_dualInd_add_cosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n]
    (q : Unif k) (χ : AddChar k Circle), HasConductor χ 1 → ∀ (e : k), (e = 1 ∨ e = -1) →
    ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k],
    fpair χ e μ (vecInd L) (dualInd L + ∑ Q ∈ withLat L, cosetInd q Q.lat Q.red) =
      fpair χ e μ (vecInd L) (dualInd L) := by
  intro k _ _ _ _ _ _ n _ _ q χ hχ e he μ _ L _
  unfold fpair
  congr 1
  funext η
  rw [Pi.add_apply, mul_add, Finset.sum_apply, Finset.mul_sum, add_eq_left]
  refine Finset.sum_eq_zero fun Q hQ => ?_
  have hL : Q.lat = L := mem_withLat.1 hQ
  classical
  unfold cosetInd
  split_ifs with h
  · obtain ⟨F, hF, hD⟩ := h
    have h0 := integral_vecInd_coset q χ hχ e he μ Q.lat Q.red_ne hF hD
    rw [hL] at h0
    rw [h0, zero_mul]
  · rw [mul_zero]

end GlobalTheory.FinPl.Comm
