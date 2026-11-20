import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementArchimedeanMatrixForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetArchimedeanNormBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelDomainReduction

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `m h e`. Establish `h1` using `ratio_le_rbar t ⟨m, h⟩`.

Establish `h2 : ¬ m + 1 < r` using `by omega`. Simplify `h1` using `[ratio, h2]`. Consider the case `succ k ih`. Introduce `m h e`. Establish `hm : m + 1 < r` using `by omega`.

Establish `h1` using `ih (m + 1) hm (by omega)`. Establish `h2` using `ratio_le_rbar t ⟨m, h⟩`. Establish `h3 : t ⟨m, h⟩ / t ⟨m + 1, hm⟩ ≤ rbar t` using `by simpa [ratio, hm] using h2`. Establish `h4 : t ⟨m, h⟩ ≤ rbar t * t ⟨m + 1, hm⟩` using `(div_le_iff₀ (ht _)).1 h3`. Establish `h5 : 0 ≤ rbar t` using `zero_le_one.trans (one_le_rbar t)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem param_le_rbar_pow {r : ℕ} {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) :
    ∀ (k m : ℕ) (h : m < r), m + k + 1 = r → t ⟨m, h⟩ ≤ rbar t ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro m h e
    have h1 := ratio_le_rbar t ⟨m, h⟩
    have h2 : ¬ m + 1 < r := by omega
    simpa [ratio, h2] using h1
  | succ k ih =>
    intro m h e
    have hm : m + 1 < r := by omega
    have h1 := ih (m + 1) hm (by omega)
    have h2 := ratio_le_rbar t ⟨m, h⟩
    have h3 : t ⟨m, h⟩ / t ⟨m + 1, hm⟩ ≤ rbar t := by simpa [ratio, hm] using h2
    have h4 : t ⟨m, h⟩ ≤ rbar t * t ⟨m + 1, hm⟩ := (div_le_iff₀ (ht _)).1 h3
    have h5 : 0 ≤ rbar t := zero_le_one.trans (one_le_rbar t)
    calc t ⟨m, h⟩ ≤ rbar t * t ⟨m + 1, hm⟩ := h4
      _ ≤ rbar t * rbar t ^ (k + 1) := mul_le_mul_of_nonneg_left h1 h5
      _ = rbar t ^ (k + 1 + 1) := by ring

/- English proof (translation)
Establish `h1` using `param_le_rbar_pow ht (r - i.val - 1) i.val i.2 (by omega)`. Conclude with `h1.trans (pow_le_pow_right₀ (one_le_rbar t) (by omega))`.
-/
theorem param_le_rbar_pow_rank {r : ℕ} {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) (i : Fin r) : t i ≤ rbar t ^ r := by
  have h1 := param_le_rbar_pow ht (r - i.val - 1) i.val i.2 (by omega)
  exact h1.trans (pow_le_pow_right₀ (one_le_rbar t) (by omega))

/- English proof (translation)
Establish `h1 : ∏ i, t i ≤ rbar t ^ (r * r)`. Use `Finset.prod_le_prod (s := (Finset.univ : Finset (Fin r))) (fun i _ => (ht i).le) fun i _ => param_le_rbar_pow_rank ht i` as an intermediate fact. Simplify `this` using `[pow_mul]`. Establish `h2 : 1 ≤ rbar t ^ (r * r)` using `one_le_pow₀ (one_le_rbar t)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_add_prod_le_rbar_pow {r : ℕ} {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) :
    1 + ∏ i, t i ≤ 2 * rbar t ^ (r * r) := by
  have h1 : ∏ i, t i ≤ rbar t ^ (r * r) := by
    have := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin r))) (fun i _ => (ht i).le)
      fun i _ => param_le_rbar_pow_rank ht i
    simpa [pow_mul] using this
  have h2 : 1 ≤ rbar t ^ (r * r) := one_le_pow₀ (one_le_rbar t)
  linarith

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ n J hJ r X Y hW c hc`. Establish `hc' : 0 < min 1 c ^ r` using `pow_pos (lt_min one_pos hc) _`. Take `⟨Ch, Ah, hCh⟩` from `@GlobalTheory.TorusHeight.height_torus_le F E _ _ _ _ _ σ hσ n J r X Y _ hc'`. Use `⟨r * r * Ah, fun Ω Cm hΩ hCm => ?_⟩` and prove the remaining obligations. Establish `hcont : Continuous fun g : GAd σ J => (height σ J g : ℝ)` using `NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)`.

Take `⟨R₁, hR₁⟩` from `(hΩ.image hcont).bddAbove`. Take `⟨R₂, hR₂⟩` from `(hCm.image hcont).bddAbove`. Use `set R₁' := max R₁ 0 with hR₁'`. Use `set R₂' := max R₂ 0 with hR₂'`. Use `set Ch' := max Ch 0 with hCh'`.

Establish `hR₁0 : 0 ≤ R₁'` using `le_max_right _ _`. Establish `hR₂0 : 0 ≤ R₂'` using `le_max_right _ _`. Establish `hCh0 : 0 ≤ Ch'` using `le_max_right _ _`. Use `⟨R₁' * (Ch' * 2 ^ Ah) * R₂', by positivity, fun p hp t ht a ha k hk => ?_⟩` and prove the remaining obligations. Establish `h1 : (height σ J a : ℝ) ≤ Ch * (1 + ∏ i, t i) ^ Ah` using `hCh t (GlobalTheory.SiegelHt.cone_low hc ht) a ha.1 (@GlobalTheory.SiegelTorusMat.archMat_torus F E _ _ _ _ _ σ hσ n J hJ r X Y hW t (fun i => hc'.trans_le (GlobalTheory.SiegelHt.cone_low hc ht i)) a ha)`.

Establish `hprod0 : 0 ≤ 1 + ∏ i, t i` using `add_nonneg zero_le_one (Finset.prod_nonneg fun i _ => (ht.1 i).le)`. Establish `h2` using `one_add_prod_le_rbar_pow (r := r) ht.1`. Establish `h3 : (height σ J a : ℝ) ≤ Ch' * (2 * rbar t ^ (r * r)) ^ Ah` using `h1.trans (mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hprod0 h2 _) (pow_nonneg hprod0 _) hCh0)`. Establish `hpb : (height σ J p : ℝ) ≤ R₁'` using `(hR₁ ⟨p, hp, rfl⟩).trans (le_max_left _ _)`. Establish `hkb : (height σ J k : ℝ) ≤ R₂'` using `(hR₂ ⟨k, hk, rfl⟩).trans (le_max_left _ _)`.

Establish `h5 : (height σ J (p * a * k) : ℝ) ≤ (height σ J p : ℝ) * height σ J a * height σ J k`. Conclude with `(height_mul_le σ J _ _).trans (mul_le_mul' (height_mul_le σ J _ _) le_rfl)` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow, ← pow_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem height_le_rbar_pow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ c : ℝ, 0 < c → ∃ b : ℕ, ∀ Ω Cm : Set (GAd σ J), IsCompact Ω → IsCompact Cm → ∃ H : ℝ, 0 ≤ H ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ Cm, (height σ J (p * a * k) : ℝ) ≤ H * rbar t ^ b := by
  intro F E _ _ _ _ _ σ hσ n J hJ r X Y hW c hc
  have hc' : 0 < min 1 c ^ r := pow_pos (lt_min one_pos hc) _
  obtain ⟨Ch, Ah, hCh⟩ := @GlobalTheory.TorusHeight.height_torus_le F E _ _ _ _ _ σ hσ n J r X Y _ hc'
  refine ⟨r * r * Ah, fun Ω Cm hΩ hCm => ?_⟩
  have hcont : Continuous fun g : GAd σ J => (height σ J g : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)
  obtain ⟨R₁, hR₁⟩ := (hΩ.image hcont).bddAbove
  obtain ⟨R₂, hR₂⟩ := (hCm.image hcont).bddAbove
  set R₁' := max R₁ 0 with hR₁'
  set R₂' := max R₂ 0 with hR₂'
  set Ch' := max Ch 0 with hCh'
  have hR₁0 : 0 ≤ R₁' := le_max_right _ _
  have hR₂0 : 0 ≤ R₂' := le_max_right _ _
  have hCh0 : 0 ≤ Ch' := le_max_right _ _
  refine ⟨R₁' * (Ch' * 2 ^ Ah) * R₂', by positivity, fun p hp t ht a ha k hk => ?_⟩
  have h1 : (height σ J a : ℝ) ≤ Ch * (1 + ∏ i, t i) ^ Ah :=
    hCh t (GlobalTheory.SiegelHt.cone_low hc ht) a ha.1
      (@GlobalTheory.SiegelTorusMat.archMat_torus F E _ _ _ _ _ σ hσ n J hJ r X Y hW t
        (fun i => hc'.trans_le (GlobalTheory.SiegelHt.cone_low hc ht i)) a ha)
  have hprod0 : 0 ≤ 1 + ∏ i, t i := add_nonneg zero_le_one (Finset.prod_nonneg fun i _ => (ht.1 i).le)
  have h2 := one_add_prod_le_rbar_pow (r := r) ht.1
  have h3 : (height σ J a : ℝ) ≤ Ch' * (2 * rbar t ^ (r * r)) ^ Ah :=
    h1.trans (mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hprod0 h2 _) (pow_nonneg hprod0 _) hCh0)
  have hpb : (height σ J p : ℝ) ≤ R₁' := (hR₁ ⟨p, hp, rfl⟩).trans (le_max_left _ _)
  have hkb : (height σ J k : ℝ) ≤ R₂' := (hR₂ ⟨k, hk, rfl⟩).trans (le_max_left _ _)
  have h5 : (height σ J (p * a * k) : ℝ) ≤ (height σ J p : ℝ) * height σ J a * height σ J k := by
    exact_mod_cast (height_mul_le σ J _ _).trans (mul_le_mul' (height_mul_le σ J _ _) le_rfl)
  calc (height σ J (p * a * k) : ℝ) ≤ (height σ J p : ℝ) * height σ J a * height σ J k := h5
    _ ≤ R₁' * (Ch' * (2 * rbar t ^ (r * r)) ^ Ah) * R₂' :=
        mul_le_mul (mul_le_mul hpb h3 (NNReal.coe_nonneg _) hR₁0) hkb (NNReal.coe_nonneg _)
          (mul_nonneg hR₁0 ((NNReal.coe_nonneg _).trans h3))
    _ = R₁' * (Ch' * 2 ^ Ah) * R₂' * rbar t ^ (r * r * Ah) := by
      rw [mul_pow, ← pow_mul]; ring

end GlobalTheory.CompanionTheory.RapidDecay

end
