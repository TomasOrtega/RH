import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumDirectionIndepStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumQExpansionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumSlTwoSmulStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisForm

/- English proof (translation)
Rewrite using `[Finset.sum_range (fun r => φ (u + (r : ZMod L) * e))]`. Use `Fintype.sum_bijective (fun i : Fin L => u + ((i : ℕ) : ZMod L) * e) ?_ _ _ (fun _ => rfl)` and prove the remaining obligations. Rewrite using `[Fintype.bijective_iff_injective_and_card]`. Use `⟨?_, by simp [ZMod.card]⟩` and prove the remaining obligations. Introduce `i i' h`.

Simplify using `only [add_right_inj] at h`. Establish `h'` using `he.mul_right_cancel h`. Rewrite `h'` using `[ZMod.natCast_eq_natCast_iff']`. Use `ext`. Rewrite `h'` using `[Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt i'.2]`. Then use the resulting hypothesis.
-/
lemma sum_shift (L : ℕ) [NeZero L] (φ : ZMod L → ℂ) (u e : ZMod L) (he : IsUnit e) :
    ∑ r ∈ Finset.range L, φ (u + (r : ZMod L) * e) = ∑ y, φ y := by
  rw [Finset.sum_range (fun r => φ (u + (r : ZMod L) * e))]
  refine Fintype.sum_bijective (fun i : Fin L => u + ((i : ℕ) : ZMod L) * e) ?_ _ _ (fun _ => rfl)
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp [ZMod.card]⟩
  intro i i' h
  simp only [add_right_inj] at h
  have h' := he.mul_right_cancel h
  rw [ZMod.natCast_eq_natCast_iff'] at h'
  ext
  rwa [Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt i'.2] at h'

/- English proof (translation)
Use `sum_shift L φ 0 1 isUnit_one` as an intermediate fact. Simplify using `only [zero_add, mul_one] at this`. Rewrite using `[← this]`. Simplify using `[hat]`.
-/
lemma hat_zero (L : ℕ) [NeZero L] (φ : ZMod L → ℂ) : hat φ 0 = ∑ y, φ y := by
  have := sum_shift L φ 0 1 isUnit_one
  simp only [zero_add, mul_one] at this
  rw [← this]; simp [hat]

/- English proof (translation)
Establish `hp : Function.Periodic b (L₂ : ℤ)` using `hb`. Establish `hpz : ∀ y n : ℤ, b (y + n * L₂) = b y` using `fun y n => by simpa using hp.int_mul n y`. Use `⟨∑ i ∈ Finset.range L₂, ‖b i‖, fun x => ?_⟩` and prove the remaining obligations. Establish `h1` using `Int.emod_nonneg x (by omega : (L₂ : ℤ) ≠ 0)`. Establish `h2` using `Int.emod_lt_of_pos x (by omega : (0 : ℤ) < L₂)`.

Establish `e : b x = b (((x % L₂).toNat : ℕ) : ℤ)`. Rewrite using `[Int.toNat_of_nonneg h1, ← hpz (x % L₂) (x / L₂)]`. Use `congr 1`. Rewrite using `[Int.emod_def]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `Finset.single_le_sum (f := fun i : ℕ => ‖b i‖) (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))`.
-/
lemma bdd_of_periodic (L₂ : ℕ) (hL : 0 < L₂) (b : ℤ → ℂ) (hb : ∀ x, b (x + L₂) = b x) :
    ∃ C : ℝ, ∀ x, ‖b x‖ ≤ C := by
  have hp : Function.Periodic b (L₂ : ℤ) := hb
  have hpz : ∀ y n : ℤ, b (y + n * L₂) = b y := fun y n => by simpa using hp.int_mul n y
  refine ⟨∑ i ∈ Finset.range L₂, ‖b i‖, fun x => ?_⟩
  have h1 := Int.emod_nonneg x (by omega : (L₂ : ℤ) ≠ 0)
  have h2 := Int.emod_lt_of_pos x (by omega : (0 : ℤ) < L₂)
  have e : b x = b (((x % L₂).toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg h1, ← hpz (x % L₂) (x / L₂)]
    congr 1
    rw [Int.emod_def]; ring
  rw [e]
  exact Finset.single_le_sum (f := fun i : ℕ => ‖b i‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_range.mpr (by omega))

/- English proof (translation)
Establish `hp : Function.Periodic b (L₂ : ℤ)` using `hb`. Establish `hpz : ∀ y n : ℤ, b (y + n * L₂) = b y` using `fun y n => by simpa using hp.int_mul n y`. Establish `hL : (L₁ : ℤ) ≠ 0` using `by exact_mod_cast hL₁.ne'`. Establish `hcop : IsCoprime d ((L₁ * L₂ : ℕ) : ℤ)` using `⟨a, -(b' * k), by push_cast; linear_combination hdet⟩`. Take `⟨hφ, hbχ⟩` from `hχ d hcop`.

Establish `hcopa : IsCoprime (L₁ : ℤ) a` using `⟨-(b' * L₂ * k), d, by linear_combination hdet⟩`. Unfold `latF`. Distinguish the cases in `h : (L₁ : ℤ) ∣ x.1`. Take `⟨m, hm⟩` from `h`. Establish `h2 : (L₁ : ℤ) ∣ x.1 * a + x.2 * (L₁ * L₂ * k)` using `⟨m * a + x.2 * L₂ * k, by rw [hm]; ring⟩`.

Rewrite using `[if_pos ⟨m, hm⟩, if_pos h2]`. Establish `e1 : x.1 / L₁ = m` using `by rw [hm, Int.mul_ediv_cancel_left _ hL]`. Establish `e2 : (x.1 * a + x.2 * (L₁ * L₂ * k)) / L₁ = m * a + (x.2 * k) * L₂`. Rewrite using `[show x.1 * a + x.2 * (L₁ * L₂ * k) = L₁ * (m * a + (x.2 * k) * L₂) by rw [hm]; ring, Int.mul_ediv_cancel_left _ hL]`. Establish `e3 : (((x.1 * b' + x.2 * d : ℤ)) : ZMod L₁) = (x.2 : ZMod L₁) * (d : ZMod L₁)`.

Rewrite using `[hm]`. Use `push_cast`. Rewrite using `[ZMod.natCast_self]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, e3, hpz]`.

Establish `e4 : b m = χ₂ d * b (m * a)`. Rewrite using `[← hbχ, ← hpz m (m * b' * L₁ * k)]`. Use `congr 1`. Take the linear combination `(-m) * hdet`. Rewrite using `[e4, hφ (x.2 : ZMod L₁)]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ¬ (L₁ : ℤ) ∣ x.1 * a + x.2 * (L₁ * L₂ * k)`. Introduce `h2`. Apply `h` to reduce the goal to its premises. Establish `h3 : (L₁ : ℤ) ∣ x.2 * (L₁ * L₂ * k)` using `⟨x.2 * L₂ * k, by ring⟩`.

Conclude with `hcopa.dvd_of_dvd_mul_right ((dvd_add_left h3).mp h2)`. Rewrite using `[if_neg h, if_neg h2, mul_zero]`.
-/
lemma latF_trans (L₁ L₂ : ℕ) (hL₁ : 0 < L₁) (b χ₁ χ₂ : ℤ → ℂ) (φ : ZMod L₁ → ℂ)
    (hb : ∀ x, b (x + L₂) = b x)
    (hχ : ∀ d : ℤ, IsCoprime d (L₁ * L₂ : ℕ) → (∀ y, φ y = χ₁ d * φ (y * d)) ∧ ∀ x, b (x * d) = χ₂ d * b x)
    (a b' k d : ℤ) (hdet : a * d - b' * (L₁ * L₂ * k) = 1) (x : ℤ × ℤ) :
    latF L₁ b φ x = χ₁ d * χ₂ d * latF L₁ b φ (x.1 * a + x.2 * (L₁ * L₂ * k), x.1 * b' + x.2 * d) := by
  have hp : Function.Periodic b (L₂ : ℤ) := hb
  have hpz : ∀ y n : ℤ, b (y + n * L₂) = b y := fun y n => by simpa using hp.int_mul n y
  have hL : (L₁ : ℤ) ≠ 0 := by exact_mod_cast hL₁.ne'
  have hcop : IsCoprime d ((L₁ * L₂ : ℕ) : ℤ) := ⟨a, -(b' * k), by push_cast; linear_combination hdet⟩
  obtain ⟨hφ, hbχ⟩ := hχ d hcop
  have hcopa : IsCoprime (L₁ : ℤ) a := ⟨-(b' * L₂ * k), d, by linear_combination hdet⟩
  unfold latF
  by_cases h : (L₁ : ℤ) ∣ x.1
  · obtain ⟨m, hm⟩ := h
    have h2 : (L₁ : ℤ) ∣ x.1 * a + x.2 * (L₁ * L₂ * k) := ⟨m * a + x.2 * L₂ * k, by rw [hm]; ring⟩
    rw [if_pos ⟨m, hm⟩, if_pos h2]
    have e1 : x.1 / L₁ = m := by rw [hm, Int.mul_ediv_cancel_left _ hL]
    have e2 : (x.1 * a + x.2 * (L₁ * L₂ * k)) / L₁ = m * a + (x.2 * k) * L₂ := by
      rw [show x.1 * a + x.2 * (L₁ * L₂ * k) = L₁ * (m * a + (x.2 * k) * L₂) by rw [hm]; ring,
        Int.mul_ediv_cancel_left _ hL]
    have e3 : (((x.1 * b' + x.2 * d : ℤ)) : ZMod L₁) = (x.2 : ZMod L₁) * (d : ZMod L₁) := by
      rw [hm]; push_cast; rw [ZMod.natCast_self]; ring
    rw [e1, e2, e3, hpz]
    have e4 : b m = χ₂ d * b (m * a) := by
      rw [← hbχ, ← hpz m (m * b' * L₁ * k)]
      congr 1
      linear_combination (-m) * hdet
    rw [e4, hφ (x.2 : ZMod L₁)]; ring
  · have h2 : ¬ (L₁ : ℤ) ∣ x.1 * a + x.2 * (L₁ * L₂ * k) := by
      intro h2; apply h
      have h3 : (L₁ : ℤ) ∣ x.2 * (L₁ * L₂ * k) := ⟨x.2 * L₂ * k, by ring⟩
      exact hcopa.dvd_of_dvd_mul_right ((dvd_add_left h3).mp h2)
    rw [if_neg h, if_neg h2, mul_zero]

/- English proof (translation)
Use `haveI : NeZero L₁ := ⟨hL₁.ne'⟩`. Establish `hp : Function.Periodic b (L₂ : ℤ)` using `hb`. Establish `hpz : ∀ y n : ℤ, b (y + n * L₂) = b y` using `fun y n => by simpa using hp.int_mul n y`. Establish `hL : (L₁ : ℤ) ≠ 0` using `by exact_mod_cast hL₁.ne'`. Rewrite `hhat` using `[hat_zero]`.

Introduce `x`. Distinguish the cases in `h : (L₁ : ℤ) ∣ x.1`. Take `⟨m, hm⟩` from `h`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations.

Simplify using `only [latF, Prod.fst_sub, Prod.snd_sub, Prod.smul_mk, smul_eq_mul]`. Rewrite using `[if_pos ⟨m - r * L₂ * k, by rw [hm]; ring⟩, show x.1 - (r : ℤ) * (L₁ * L₂ * k) = L₁ * (m + (-(r * k)) * L₂) by rw [hm]; ring, Int.mul_ediv_cancel_left _ hL, hpz]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = 0 := by rw [← Finset.mul_sum, sum_shift L₁ φ _ _ hd.neg, hhat, mul_zero]`. Use `Finset.sum_eq_zero fun r _ => ?_` and prove the remaining obligations. Simplify using `only [latF, Prod.fst_sub, Prod.snd_sub, Prod.smul_mk, smul_eq_mul]`. Rewrite using `[if_neg]`. Introduce `h2`.

Apply `h` to reduce the goal to its premises. Establish `h3 : (L₁ : ℤ) ∣ (r : ℤ) * (L₁ * L₂ * k)` using `⟨r * L₂ * k, by ring⟩`. Simplify using `using dvd_add h2 h3`.
-/
lemma latF_kills (L₁ L₂ : ℕ) (hL₁ : 0 < L₁) (b : ℤ → ℂ) (φ : ZMod L₁ → ℂ)
    (hb : ∀ x, b (x + L₂) = b x) (hhat : hat φ 0 = 0) (k d : ℤ) (hd : IsUnit (d : ZMod L₁)) :
    Kills L₁ (L₁ * L₂ * k, d) (latF L₁ b φ) := by
  haveI : NeZero L₁ := ⟨hL₁.ne'⟩
  have hp : Function.Periodic b (L₂ : ℤ) := hb
  have hpz : ∀ y n : ℤ, b (y + n * L₂) = b y := fun y n => by simpa using hp.int_mul n y
  have hL : (L₁ : ℤ) ≠ 0 := by exact_mod_cast hL₁.ne'
  rw [hat_zero] at hhat
  intro x
  by_cases h : (L₁ : ℤ) ∣ x.1
  · obtain ⟨m, hm⟩ := h
    calc ∑ r ∈ Finset.range L₁, latF L₁ b φ (x - (r : ℤ) • ((L₁ : ℤ) * L₂ * k, d))
        = ∑ r ∈ Finset.range L₁, b m * φ ((x.2 : ZMod L₁) + (r : ZMod L₁) * (-(d : ZMod L₁))) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          simp only [latF, Prod.fst_sub, Prod.snd_sub, Prod.smul_mk, smul_eq_mul]
          rw [if_pos ⟨m - r * L₂ * k, by rw [hm]; ring⟩,
            show x.1 - (r : ℤ) * (L₁ * L₂ * k) = L₁ * (m + (-(r * k)) * L₂) by rw [hm]; ring,
            Int.mul_ediv_cancel_left _ hL, hpz]
          congr 2; push_cast; ring
      _ = 0 := by rw [← Finset.mul_sum, sum_shift L₁ φ _ _ hd.neg, hhat, mul_zero]
  · refine Finset.sum_eq_zero fun r _ => ?_
    simp only [latF, Prod.fst_sub, Prod.snd_sub, Prod.smul_mk, smul_eq_mul]
    rw [if_neg]
    intro h2; apply h
    have h3 : (L₁ : ℤ) ∣ (r : ℤ) * (L₁ * L₂ * k) := ⟨r * L₂ * k, by ring⟩
    simpa using dvd_add h2 h3

end GlobalTheory.EisForm

namespace GlobalTheory.EisForm

/- English proof (translation)
Introduce `j L₁ L₂ b χ₁ χ₂ φ hj hL₁ hL₂ hhat hb hχ hpar`. Use `haveI : NeZero L₁ := ⟨hL₁.ne'⟩`. Take `⟨Cb, hCb⟩` from `bdd_of_periodic L₂ hL₂ b hb`. Establish `hparity : ∀ x y : ℤ, b (-x) * φ (-(y : ZMod L₁)) = (-1) ^ j * (b x * φ y)`. Introduce `x y`.

Take `⟨hφ, hbb⟩` from `hχ (-1) ⟨-1, 0, by ring⟩`. Establish `h1` using `hφ (-(y : ZMod L₁))`. Establish `h2` using `hbb x`. Rewrite `h1` using `[show -(y : ZMod L₁) * ((-1 : ℤ) : ZMod L₁) = y by push_cast; ring]`. Rewrite `h2` using `[mul_neg_one]`.

Rewrite using `[h1, h2, ← hpar]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨c, hP, hq⟩` from `GlobalTheory.T.regularizedEisensteinLatticeSum_qExpansion j L₁ b φ hj hL₁ ⟨Cb, hCb⟩ hhat hparity`. Use `⟨c, ⟨hP, ?_⟩, hq⟩` and prove the remaining obligations. Use `set K : ℂ := 2 * (-2 * π * Complex.I / L₁) ^ j / (j - 1).factorial with hKdef`.

Establish `hK : K ≠ 0`. Establish `hL : (L₁ : ℂ) ≠ 0` using `by exact_mod_cast hL₁.ne'`. Simplify using `[hKdef, Real.pi_ne_zero, Complex.I_ne_zero, hL, Nat.factorial_ne_zero]`. Use `set Φ := latF L₁ b φ with hΦ`. Establish `hq' : ∀ τ, qs (eis j c (hat φ) b) τ = K⁻¹ * lat j 0 L₁ (0, 1) Φ τ` using `fun τ => by`.

Rewrite using `[hq τ, ← mul_assoc, inv_mul_cancel₀ hK, one_mul]`. Establish `hΦb : ∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C`. Establish `hC0 : 0 ≤ Cb` using `le_trans (norm_nonneg _) (hCb 0)`. Use `⟨Cb * ∑ y, ‖φ y‖, fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [hΦ, latF]`.

Use `split_ifs`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (hCb _) (Finset.single_le_sum (f := fun y => ‖φ y‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _)) (norm_nonneg _) hC0`. Simplify using `using mul_nonneg hC0 (Finset.sum_nonneg fun y _ => norm_nonneg (φ y))`. Introduce `γ hc τ`.

Take `⟨k, hk⟩` from `hc`. Move the coercions through the operations in `at hk`. Establish `hdet : γ 0 0 * γ 1 1 - γ 0 1 * ((L₁ : ℤ) * L₂ * k) = 1`. Use `γ.2` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`.

Rewrite using `[← hk]`. Conclude with `this`. Establish `hunit : IsUnit ((γ 1 1 : ℤ) : ZMod L₁)`. Use `isUnit_iff_exists_inv.mpr ⟨((γ 0 0 : ℤ) : ZMod L₁), ?_⟩` and prove the remaining obligations. Use `congrArg (fun z : ℤ => (z : ZMod L₁)) hdet` as an intermediate fact.

Move the coercions through the operations in `at this`. Rewrite `this` using `[ZMod.natCast_self]`. Take the linear combination `this`. Use `set χd := χ₁ (γ 1 1) * χ₂ (γ 1 1) with hχd`. Establish `htr : ∀ x : ℤ × ℤ, (fun y => χd * Φ y) (x.1 * γ 0 0 + x.2 * γ 1 0, x.1 * γ 0 1 + x.2 * γ 1 1) = Φ x`.

Introduce `x`. Use `latF_trans L₁ L₂ hL₁ b χ₁ χ₂ φ hb hχ (γ 0 0) (γ 0 1) k (γ 1 1) hdet x` as an intermediate fact. Rewrite `this` using `[← hk]`. Conclude with `this.symm`. Establish `hlin : ∀ w, lat j 0 L₁ w (fun y => χd * Φ y) τ = χd * lat j 0 L₁ w Φ τ`.

Introduce `w`. Unfold `lat`. Rewrite using `[← tsum_mul_left]`. Use `congr 1`. Use extensionality with `x`.

Expand and normalize the polynomial expressions, which then agree. Establish `hw : ((0 : ℤ) * γ 0 0 + 1 * γ 1 0, (0 : ℤ) * γ 0 1 + 1 * γ 1 1) = ((L₁ : ℤ) * L₂ * k, γ 1 1)`. Simplify using `[hk]`. Establish `hk1 : Kills L₁ ((L₁ : ℤ) * L₂ * k, γ 1 1) Φ` using `latF_kills L₁ L₂ hL₁ b φ hb hhat k (γ 1 1) hunit`. Establish `hk0 : Kills L₁ (0, 1) Φ`.

Simplify using `using latF_kills L₁ L₂ hL₁ b φ hb hhat 0 1 (by simp)`. Rewrite using `[hq', hq', GlobalTheory.T.regularizedEisensteinLatticeSum_slTwo_smul j L₁ (0, 1) Φ (fun y => χd * Φ y) γ τ htr, hlin]`. Simplify using `only [Prod.fst, Prod.snd]`. Rewrite using `[hw, GlobalTheory.T.regularizedEisensteinLatticeSum_direction_indep j L₁ _ (0, 1) Φ τ hj hL₁ hΦb hk1 hk0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eis_latF_mf : ∀ (j L₁ L₂ : ℕ) (b χ₁ χ₂ : ℤ → ℂ) (φ : ZMod L₁ → ℂ), 1 ≤ j → 0 < L₁ → 0 < L₂ → hat φ 0 = 0 →
    (∀ x, b (x + L₂) = b x) →
    (∀ d : ℤ, IsCoprime d (L₁ * L₂ : ℕ) → (∀ y, φ y = χ₁ d * φ (y * d)) ∧ ∀ x, b (x * d) = χ₂ d * b x) →
    χ₁ (-1) * χ₂ (-1) = (-1) ^ j →
    ∃ c : ℂ, MF j (L₁ * L₂) (fun d => χ₁ d * χ₂ d) (eis j c (hat φ) b) ∧
      ∀ τ : ℍ, lat j 0 L₁ (0, 1) (latF L₁ b φ) τ = 2 * (-2 * π * Complex.I / L₁) ^ j / (j - 1).factorial * qs (eis j c (hat φ) b) τ := by
  intro j L₁ L₂ b χ₁ χ₂ φ hj hL₁ hL₂ hhat hb hχ hpar
  haveI : NeZero L₁ := ⟨hL₁.ne'⟩
  obtain ⟨Cb, hCb⟩ := bdd_of_periodic L₂ hL₂ b hb
  have hparity : ∀ x y : ℤ, b (-x) * φ (-(y : ZMod L₁)) = (-1) ^ j * (b x * φ y) := by
    intro x y
    obtain ⟨hφ, hbb⟩ := hχ (-1) ⟨-1, 0, by ring⟩
    have h1 := hφ (-(y : ZMod L₁))
    have h2 := hbb x
    rw [show -(y : ZMod L₁) * ((-1 : ℤ) : ZMod L₁) = y by push_cast; ring] at h1
    rw [mul_neg_one] at h2
    rw [h1, h2, ← hpar]; ring
  obtain ⟨c, hP, hq⟩ := GlobalTheory.T.regularizedEisensteinLatticeSum_qExpansion j L₁ b φ hj hL₁ ⟨Cb, hCb⟩ hhat hparity
  refine ⟨c, ⟨hP, ?_⟩, hq⟩
  set K : ℂ := 2 * (-2 * π * Complex.I / L₁) ^ j / (j - 1).factorial with hKdef
  have hK : K ≠ 0 := by
    have hL : (L₁ : ℂ) ≠ 0 := by exact_mod_cast hL₁.ne'
    simp [hKdef, Real.pi_ne_zero, Complex.I_ne_zero, hL, Nat.factorial_ne_zero]
  set Φ := latF L₁ b φ with hΦ
  have hq' : ∀ τ, qs (eis j c (hat φ) b) τ = K⁻¹ * lat j 0 L₁ (0, 1) Φ τ := fun τ => by
    rw [hq τ, ← mul_assoc, inv_mul_cancel₀ hK, one_mul]
  have hΦb : ∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C := by
    have hC0 : 0 ≤ Cb := le_trans (norm_nonneg _) (hCb 0)
    refine ⟨Cb * ∑ y, ‖φ y‖, fun x => ?_⟩
    simp only [hΦ, latF]
    split_ifs
    · rw [norm_mul]
      exact mul_le_mul (hCb _) (Finset.single_le_sum (f := fun y => ‖φ y‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ _)) (norm_nonneg _) hC0
    · simpa using mul_nonneg hC0 (Finset.sum_nonneg fun y _ => norm_nonneg (φ y))
  intro γ hc τ
  obtain ⟨k, hk⟩ := hc
  push_cast at hk
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * ((L₁ : ℤ) * L₂ * k) = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    rw [← hk]; exact this
  have hunit : IsUnit ((γ 1 1 : ℤ) : ZMod L₁) := by
    refine isUnit_iff_exists_inv.mpr ⟨((γ 0 0 : ℤ) : ZMod L₁), ?_⟩
    have := congrArg (fun z : ℤ => (z : ZMod L₁)) hdet
    push_cast at this
    rw [ZMod.natCast_self] at this
    linear_combination this
  set χd := χ₁ (γ 1 1) * χ₂ (γ 1 1) with hχd
  have htr : ∀ x : ℤ × ℤ, (fun y => χd * Φ y) (x.1 * γ 0 0 + x.2 * γ 1 0, x.1 * γ 0 1 + x.2 * γ 1 1) = Φ x := by
    intro x
    have := latF_trans L₁ L₂ hL₁ b χ₁ χ₂ φ hb hχ (γ 0 0) (γ 0 1) k (γ 1 1) hdet x
    rw [← hk] at this
    exact this.symm
  have hlin : ∀ w, lat j 0 L₁ w (fun y => χd * Φ y) τ = χd * lat j 0 L₁ w Φ τ := by
    intro w
    unfold lat
    rw [← tsum_mul_left]
    congr 1; ext x; ring
  have hw : ((0 : ℤ) * γ 0 0 + 1 * γ 1 0, (0 : ℤ) * γ 0 1 + 1 * γ 1 1) = ((L₁ : ℤ) * L₂ * k, γ 1 1) := by
    simp [hk]
  have hk1 : Kills L₁ ((L₁ : ℤ) * L₂ * k, γ 1 1) Φ := latF_kills L₁ L₂ hL₁ b φ hb hhat k (γ 1 1) hunit
  have hk0 : Kills L₁ (0, 1) Φ := by
    simpa using latF_kills L₁ L₂ hL₁ b φ hb hhat 0 1 (by simp)
  rw [hq', hq', GlobalTheory.T.regularizedEisensteinLatticeSum_slTwo_smul j L₁ (0, 1) Φ (fun y => χd * Φ y) γ τ htr, hlin]
  simp only [Prod.fst, Prod.snd]
  rw [hw, GlobalTheory.T.regularizedEisensteinLatticeSum_direction_indep j L₁ _ (0, 1) Φ τ hj hL₁ hΦb hk1 hk0]
  ring

end GlobalTheory.EisForm
