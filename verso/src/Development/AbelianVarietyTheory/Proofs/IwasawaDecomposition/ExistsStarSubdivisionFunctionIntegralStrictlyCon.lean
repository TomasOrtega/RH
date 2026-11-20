import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllEqOfInRCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthCommonDenominatorRankLeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformStrictnessAndFaceCutBoundsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthLeStrictnessGapOffCentresStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthLeOnCentreCellStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedGeneratorsStarSubdivisionConeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionEstimateOffCentreCellStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarKey

/- English proof (translation)
Introduce `E _ _ _ H q ψ w hdom hψ hcs`. Take `⟨D₀, hD₀, hint⟩` from `GlobalTheory.T.starDepth_common_denominator_rank_le E H q ψ w hψ hcs`. Take `⟨N₀, C₀, hdata⟩` from `GlobalTheory.T.exists_uniform_strictness_and_face_cut_bounds E H q ψ hdom hψ`. Take `⟨b, hgens⟩` from `GlobalTheory.T.exists_bounded_generators_star_subdivision_cone E H q ψ w hψ hcs`. Establish `hD₀r : (0 : ℝ) < D₀` using `by exact_mod_cast hD₀`.

Use `⟨N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1, D₀, by omega, hD₀, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `X _ _ _ _ hX β hβ hp`. Take `⟨n₁, hn₁⟩` from `(hψ X hX).integral β hβ hp`. Take `⟨n₂, hn₂⟩` from `hint X hX β hβ hp`. Use `⟨D₀ * (N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1) * n₁ + n₂, ?_⟩` and prove the remaining obligations.

Rewrite using `[starFun_evalZ, hn₁]`. Use `push_cast`. Take the linear combination `hn₂`. Introduce `X _ _ _ _ hX m γ hγ hnoc`. Take `⟨N, ℓ, hN, hNN, hsw, -⟩` from `hdata X hX m γ hγ`.

Establish `hgap` using `GlobalTheory.T.starDepth_le_strictnessGap_off_centres E H q ψ w hψ hcs X hX m γ N ℓ hγ hnoc hN hsw`. Establish `hnn : ∀ β : LinearMap.BilinForm ℤ X, 0 ≤ (starDepth H.bar ψ w).evalZ β` using `fun β => starDepth_eval_nonneg (fun a b => (β a b : ℝ))`. Use `set K := N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1 with hKdef`. Establish `hKN : (N : ℝ) + 1 ≤ K`. Establish `: N + 1 ≤ K` using `by rw [hKdef]; omega`.

Conclude with `this` after adjusting the coercions. Establish `hN0 : (0 : ℝ) ≤ N` using `Nat.cast_nonneg N`. Use `⟨N, ((D₀ * K : ℕ) : ℤ) • ℓ, hN, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩` and prove the remaining obligations. Establish `h0` using `hsw.1 i`. Establish `hps : (starDepth H.bar ψ w).evalZ (γ i) = 0` using `le_antisymm (by have := hgap (γ i) (hγ.mem i) (hγ.nonneg i); linarith) (hnn _)`.

Rewrite using `[starFun_evalZ, hps]`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul]`. Use `push_cast`. Rewrite using `[h0]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hg` using `hgap β hβ hp`. Establish `hf` using `hsw.2.1 β hβ hp`. Establish `hps` using `hnn β`. Rewrite using `[starFun_evalZ]`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul]`.

Use `push_cast`. Use `set P := (starDepth H.bar ψ w).evalZ β`. Use `set Ψ := ψ.evalZ β`. Use `set L : ℝ := (ℓ β : ℝ)`. Establish `k1 : (N : ℝ) * P ≤ K * (L - N * Ψ)` using `by nlinarith [mul_le_mul_of_nonneg_left hg hN0]`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left k1 hD₀r.le]`. Establish `hg` using `hgap β hβ hp`. Establish `hf` using `hsw.2.1 β hβ hp`. Establish `hps` using `hnn β`. Rewrite `he` using `[starFun_evalZ]`.

Simplify using `only [LinearMap.smul_apply, smul_eq_mul] at he`. Move the coercions through the operations in `at he`. Use `set P := (starDepth H.bar ψ w).evalZ β`. Use `set Ψ := ψ.evalZ β`. Use `set L : ℝ := (ℓ β : ℝ)`.

Establish `e1 : (N : ℝ) * P = K * (L - N * Ψ)`. Use `mul_left_cancel₀ hD₀r.ne' (show (D₀ : ℝ) * (N * P) = D₀ * (K * (L - N * Ψ)) by linear_combination he)` as an intermediate fact. Conclude with `this`. Establish `e2 : L - N * Ψ = 0` using `by nlinarith [mul_le_mul_of_nonneg_left hg hN0]`. Conclude with `hsw.2.2 β hβ hp (by linarith)`.

Introduce `X _ _ _ _ hX m γ hγ β₀ hβ₀ hp₀ hw₀ hin₀ m' s h hcut hpos`. Take `⟨N, ℓ, hN, hNN, hsw, hcuts⟩` from `hdata X hX m γ hγ`. Take `⟨h', hcut', hpos', hdom'⟩` from `hcuts m' s h hcut`. Establish `hp' : 0 < h' β₀` using `hpos' β₀ hin₀ hpos`. Take `⟨hin, hone, hzero, heq⟩` from `GlobalTheory.T.starDepth_le_on_centre_cell E H q ψ w hψ hcs X hX m γ hγ β₀ hβ₀ hp₀ hw₀ hin₀ m' s h' hcut' hp'`.

Use `set K := N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1 with hKdef`. Establish `hKb : N + N * C₀ + N ^ 2 * C₀ * b + 1 ≤ K`. Rewrite using `[hKdef]`. Establish `h1 : N * C₀ ≤ N₀ * C₀` using `Nat.mul_le_mul_right _ hNN`. Establish `h2 : N ^ 2 * C₀ * b ≤ N₀ ^ 2 * C₀ * b` using `Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hNN 2))`.

Use linear arithmetic over natural numbers and integers. Establish `hoff` using `GlobalTheory.T.star_subdivision_estimate_off_centre_cell E H q ψ w b hψ hcs X hX (hgens X hX) m γ N ℓ hγ hN hsw β₀ hβ₀ hp₀ hw₀ hin₀ m' s h' hcut' hp' C₀ hdom' K hKb`. Establish `hlinγ : ∀ β, InRCone γ β → (ℓ β : ℝ) = N * ψ.evalZ β` using `fun β hβ => StarKey.ell_eq_of_inRCone hγ.linear hsw hβ`. Establish `hcast : (((h' β₀).toNat : ℕ) : ℝ) = (h' β₀ : ℝ)`. Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg hp'.le]`.

Establish `hH0 : (0 : ℝ) < h' β₀` using `by exact_mod_cast hp'`. Establish `hN0 : (0 : ℝ) < N` using `by exact_mod_cast hN`. Use `⟨N * (h' β₀).toNat, (D₀ : ℤ) • (((K : ℤ) * h' β₀) • ℓ + (N : ℤ) • h'), by` and prove the remaining obligations. Establish `: 0 < (h' β₀).toNat` using `by omega`. Use the proof step `positivity, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩`.

Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `only [Fin.cons_zero]`. Rewrite using `[starFun_evalZ, hone]`. Establish `hl` using `hlinγ β₀ hin₀`. Simplify using `only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]`.

Use `push_cast`. Rewrite using `[hcast, hl]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Fin.cons_succ]`. Establish `hh : h' (γ (s j)) = 0` using `(hcut'.2 (s j)).2 ⟨j, rfl⟩`.

Rewrite using `[starFun_evalZ, hzero j]`. Simplify using `only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul, hh]`. Use `push_cast`. Rewrite using `[hcast, hsw.1 (s j)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[starFun_evalZ]`. Simplify using `only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]`. Use `push_cast`. Rewrite using `[hcast]`. Use `set P := (starDepth H.bar ψ w).evalZ β`.

Use `set Ψ := ψ.evalZ β`. Distinguish the cases in `hc : InRCone γ β`. Establish `hl` using `hlinγ β hc`. Establish `hi` using `hin β hβ hp hc`. Rewrite using `[hl]`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hi (mul_nonneg hD₀r.le hN0.le)]`. Establish `ho` using `hoff β hβ hp hc`. Use polynomial arithmetic with `[mul_lt_mul_of_pos_left ho hD₀r]`. Rewrite `he` using `[starFun_evalZ]`. Simplify using `only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul] at he`.

Move the coercions through the operations in `at he`. Rewrite `he` using `[hcast]`. Use `set P := (starDepth H.bar ψ w).evalZ β`. Use `set Ψ := ψ.evalZ β`. Distinguish the cases in `hc : InRCone γ β`.

Establish `hl` using `hlinγ β hc`. Rewrite `he` using `[hl]`. Use `heq β hβ hp hc ?_` and prove the remaining obligations. Establish `: ((D₀ : ℝ) * N) * ((h' β₀ : ℝ) * P) = ((D₀ : ℝ) * N) * (h' β : ℝ)` using `by linear_combination he`. Conclude with `mul_left_cancel₀ (mul_pos hD₀r hN0).ne' this`.

Establish `ho` using `hoff β hβ hp hc`. Use polynomial arithmetic with `[mul_lt_mul_of_pos_left ho hD₀r]`.
-/
theorem exists_starFun_strict : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∃ K D : ℕ, 0 < K ∧ 0 < D ∧ (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (starFun H.bar ψ w K D).evalZ β = n) ∧ (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsStrict H.bar (starFun H.bar ψ w K D) γ) ∧ (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → IsStrict H.bar (starFun H.bar ψ w K D) (Fin.cons β₀ fun j => γ (s j))) := by
  intro E _ _ _ H q ψ w hdom hψ hcs
  obtain ⟨D₀, hD₀, hint⟩ := GlobalTheory.T.starDepth_common_denominator_rank_le E H q ψ w hψ hcs
  obtain ⟨N₀, C₀, hdata⟩ := GlobalTheory.T.exists_uniform_strictness_and_face_cut_bounds E H q ψ hdom hψ
  obtain ⟨b, hgens⟩ := GlobalTheory.T.exists_bounded_generators_star_subdivision_cone E H q ψ w hψ hcs
  have hD₀r : (0 : ℝ) < D₀ := by exact_mod_cast hD₀
  refine ⟨N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1, D₀, by omega, hD₀, ?_, ?_, ?_⟩
  · intro X _ _ _ _ hX β hβ hp
    obtain ⟨n₁, hn₁⟩ := (hψ X hX).integral β hβ hp
    obtain ⟨n₂, hn₂⟩ := hint X hX β hβ hp
    refine ⟨D₀ * (N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1) * n₁ + n₂, ?_⟩
    rw [starFun_evalZ, hn₁]
    push_cast
    linear_combination hn₂
  · intro X _ _ _ _ hX m γ hγ hnoc
    obtain ⟨N, ℓ, hN, hNN, hsw, -⟩ := hdata X hX m γ hγ
    have hgap := GlobalTheory.T.starDepth_le_strictnessGap_off_centres E H q ψ w hψ hcs X hX m γ N ℓ hγ hnoc hN hsw
    have hnn : ∀ β : LinearMap.BilinForm ℤ X, 0 ≤ (starDepth H.bar ψ w).evalZ β := fun β =>
      starDepth_eval_nonneg (fun a b => (β a b : ℝ))
    set K := N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1 with hKdef
    have hKN : (N : ℝ) + 1 ≤ K := by
      have : N + 1 ≤ K := by rw [hKdef]; omega
      exact_mod_cast this
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    refine ⟨N, ((D₀ * K : ℕ) : ℤ) • ℓ, hN, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
    · have h0 := hsw.1 i
      have hps : (starDepth H.bar ψ w).evalZ (γ i) = 0 :=
        le_antisymm (by have := hgap (γ i) (hγ.mem i) (hγ.nonneg i); linarith) (hnn _)
      rw [starFun_evalZ, hps]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      push_cast
      rw [h0]; ring
    · have hg := hgap β hβ hp
      have hf := hsw.2.1 β hβ hp
      have hps := hnn β
      rw [starFun_evalZ]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      push_cast
      set P := (starDepth H.bar ψ w).evalZ β
      set Ψ := ψ.evalZ β
      set L : ℝ := (ℓ β : ℝ)
      have k1 : (N : ℝ) * P ≤ K * (L - N * Ψ) := by nlinarith [mul_le_mul_of_nonneg_left hg hN0]
      nlinarith [mul_le_mul_of_nonneg_left k1 hD₀r.le]
    · have hg := hgap β hβ hp
      have hf := hsw.2.1 β hβ hp
      have hps := hnn β
      rw [starFun_evalZ] at he
      simp only [LinearMap.smul_apply, smul_eq_mul] at he
      push_cast at he
      set P := (starDepth H.bar ψ w).evalZ β
      set Ψ := ψ.evalZ β
      set L : ℝ := (ℓ β : ℝ)
      have e1 : (N : ℝ) * P = K * (L - N * Ψ) := by
        have := mul_left_cancel₀ hD₀r.ne' (show (D₀ : ℝ) * (N * P) = D₀ * (K * (L - N * Ψ)) by linear_combination he)
        exact this
      have e2 : L - N * Ψ = 0 := by nlinarith [mul_le_mul_of_nonneg_left hg hN0]
      exact hsw.2.2 β hβ hp (by linarith)
  · intro X _ _ _ _ hX m γ hγ β₀ hβ₀ hp₀ hw₀ hin₀ m' s h hcut hpos
    obtain ⟨N, ℓ, hN, hNN, hsw, hcuts⟩ := hdata X hX m γ hγ
    obtain ⟨h', hcut', hpos', hdom'⟩ := hcuts m' s h hcut
    have hp' : 0 < h' β₀ := hpos' β₀ hin₀ hpos
    obtain ⟨hin, hone, hzero, heq⟩ :=
      GlobalTheory.T.starDepth_le_on_centre_cell E H q ψ w hψ hcs X hX m γ hγ β₀ hβ₀ hp₀ hw₀ hin₀ m' s h' hcut' hp'
    set K := N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1 with hKdef
    have hKb : N + N * C₀ + N ^ 2 * C₀ * b + 1 ≤ K := by
      rw [hKdef]
      have h1 : N * C₀ ≤ N₀ * C₀ := Nat.mul_le_mul_right _ hNN
      have h2 : N ^ 2 * C₀ * b ≤ N₀ ^ 2 * C₀ * b :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hNN 2))
      omega
    have hoff := GlobalTheory.T.star_subdivision_estimate_off_centre_cell E H q ψ w b hψ hcs X hX (hgens X hX) m γ N ℓ hγ hN hsw β₀ hβ₀ hp₀ hw₀ hin₀ m' s h'
      hcut' hp' C₀ hdom' K hKb
    have hlinγ : ∀ β, InRCone γ β → (ℓ β : ℝ) = N * ψ.evalZ β := fun β hβ => StarKey.ell_eq_of_inRCone hγ.linear hsw hβ
    have hcast : (((h' β₀).toNat : ℕ) : ℝ) = (h' β₀ : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hp'.le]
    have hH0 : (0 : ℝ) < h' β₀ := by exact_mod_cast hp'
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    refine ⟨N * (h' β₀).toNat, (D₀ : ℤ) • (((K : ℤ) * h' β₀) • ℓ + (N : ℤ) • h'), by
      have : 0 < (h' β₀).toNat := by omega
      positivity, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        rw [starFun_evalZ, hone]
        have hl := hlinγ β₀ hin₀
        simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
        push_cast
        rw [hcast, hl]; ring
      · simp only [Fin.cons_succ]
        have hh : h' (γ (s j)) = 0 := (hcut'.2 (s j)).2 ⟨j, rfl⟩
        rw [starFun_evalZ, hzero j]
        simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul, hh]
        push_cast
        rw [hcast, hsw.1 (s j)]; ring
    · rw [starFun_evalZ]
      simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
      push_cast
      rw [hcast]
      set P := (starDepth H.bar ψ w).evalZ β
      set Ψ := ψ.evalZ β
      by_cases hc : InRCone γ β
      · have hl := hlinγ β hc
        have hi := hin β hβ hp hc
        rw [hl]
        nlinarith [mul_le_mul_of_nonneg_left hi (mul_nonneg hD₀r.le hN0.le)]
      · have ho := hoff β hβ hp hc
        nlinarith [mul_lt_mul_of_pos_left ho hD₀r]
    · rw [starFun_evalZ] at he
      simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul] at he
      push_cast at he
      rw [hcast] at he
      set P := (starDepth H.bar ψ w).evalZ β
      set Ψ := ψ.evalZ β
      by_cases hc : InRCone γ β
      · have hl := hlinγ β hc
        rw [hl] at he
        refine heq β hβ hp hc ?_
        have : ((D₀ : ℝ) * N) * ((h' β₀ : ℝ) * P) = ((D₀ : ℝ) * N) * (h' β : ℝ) := by linear_combination he
        exact mul_left_cancel₀ (mul_pos hD₀r hN0).ne' this
      · have ho := hoff β hβ hp hc
        nlinarith [mul_lt_mul_of_pos_left ho hD₀r]

end GlobalTheory.PolFan.StarKey
