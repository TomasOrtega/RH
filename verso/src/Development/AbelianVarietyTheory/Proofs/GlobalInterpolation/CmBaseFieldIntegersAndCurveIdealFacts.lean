import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomDict

open GlobalTheory.MomOne

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k : ℤ, t = 2 * k + 1 := by`. Break down `Int.even_or_odd' t with ⟨k, rfl | rfl⟩` into its components or cases. It suffices to derive a contradiction. Establish `: (2 * k) ^ 2 = 4 * (k * k)` using `by ring`. Rewrite `hD` using `[this]`.

Generalize the expression as in `k * k = m at hD`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨k, rfl⟩`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs2, hw⟩ : ∃ s : ℂ, s ^ 2 = -(d : ℂ) ∧ wK d = (1 + s) / 2 := by`. Use `⟨Complex.I * ((Real.sqrt d : ℝ) : ℂ), ?_, rfl⟩` and prove the remaining obligations.

Rewrite using `[mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hDc : (t : ℂ) ^ 2 - 4 * n = -(d : ℂ)` using `by exact_mod_cast hD`. Establish `hprod : (2 * β - t - s) * (2 * β - t + s) = 0`.

Take the linear combination `4 * hβ + hDc - hs2`. Establish `hkc : (t : ℂ) = 2 * k + 1` using `by exact_mod_cast hk`. Break down `mul_eq_zero.1 hprod with h | h` into its components or cases. Use `⟨k, Or.inl ?_⟩` and prove the remaining obligations. Rewrite using `[hw]`.

Take the linear combination `h / 2 + hkc / 2`. Use `⟨k + 1, Or.inr ?_⟩` and prove the remaining obligations. Rewrite using `[hw]`. Use `push_cast`. Take the linear combination `h / 2 + hkc / 2`.
-/
theorem root_eq (d : ℕ) (hd : d % 4 = 3) (t n : ℤ) (hD : t ^ 2 - 4 * n = -(d : ℤ)) (β : ℂ)
    (hβ : β ^ 2 = t * β - n) : ∃ k : ℤ, β = k + wK d ∨ β = k - wK d := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, t = 2 * k + 1 := by
    rcases Int.even_or_odd' t with ⟨k, rfl | rfl⟩
    · exfalso
      have : (2 * k) ^ 2 = 4 * (k * k) := by ring
      rw [this] at hD
      generalize k * k = m at hD
      omega
    · exact ⟨k, rfl⟩
  obtain ⟨s, hs2, hw⟩ : ∃ s : ℂ, s ^ 2 = -(d : ℂ) ∧ wK d = (1 + s) / 2 := by
    refine ⟨Complex.I * ((Real.sqrt d : ℝ) : ℂ), ?_, rfl⟩
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    push_cast; ring
  have hDc : (t : ℂ) ^ 2 - 4 * n = -(d : ℂ) := by exact_mod_cast hD
  have hprod : (2 * β - t - s) * (2 * β - t + s) = 0 := by
    linear_combination 4 * hβ + hDc - hs2
  have hkc : (t : ℂ) = 2 * k + 1 := by exact_mod_cast hk
  rcases mul_eq_zero.1 hprod with h | h
  · refine ⟨k, Or.inl ?_⟩
    rw [hw]; linear_combination h / 2 + hkc / 2
  · refine ⟨k + 1, Or.inr ?_⟩
    rw [hw]; push_cast; linear_combination h / 2 + hkc / 2

/- English proof (translation)
Break down `hβ with rfl | rfl` into its components or cases. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, v, rfl⟩; exact ⟨u - v * k, v, by push_cast; ring⟩`. Introduce and unpack `⟨x, y, rfl⟩; exact ⟨x + y * k, y, by push_cast; ring⟩`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, v, rfl⟩; exact ⟨u + v * k, -v, by push_cast; ring⟩`. Introduce and unpack `⟨x, y, rfl⟩; exact ⟨x + y * k, -y, by push_cast; ring⟩`.
-/
theorem inOK_iff_int_pair (d : ℕ) (β : ℂ) (k : ℤ) (hβ : β = k + wK d ∨ β = k - wK d) (z : ℂ) :
    InOK d z ↔ ∃ x y : ℤ, z = x + y * β := by
  rcases hβ with rfl | rfl
  · constructor
    · rintro ⟨u, v, rfl⟩; exact ⟨u - v * k, v, by push_cast; ring⟩
    · rintro ⟨x, y, rfl⟩; exact ⟨x + y * k, y, by push_cast; ring⟩
  · constructor
    · rintro ⟨u, v, rfl⟩; exact ⟨u + v * k, -v, by push_cast; ring⟩
    · rintro ⟨x, y, rfl⟩; exact ⟨x + y * k, -y, by push_cast; ring⟩

/- English proof (translation)
Take `⟨b, t, n, h0, hw, hdisc⟩` from `GlobalTheory.QuadraticZeta.exists_basis (K := D.host.K) (GlobalTheory.CurveLattice.finrank_hostK D)`. Rewrite `hdisc` using `[GlobalTheory.CurveLattice.discr_hostK D]`. Set `σ : 𝓞 D.host.K →+* ℂ` to `D.host.φ₀.comp ((algebraMap D.host.K D.host.E).comp (algebraMap (𝓞 D.host.K) D.host.K))`. Establish `hσ : ∀ x : 𝓞 D.host.K, σ x = D.host.φ₀ ((x : D.host.K) : D.host.E)` using `fun x => rfl`. Establish `hβ : σ (b 1) ^ 2 = t * σ (b 1) - n`.

Rewrite using `[← map_pow, hw]`. Simplify using the standard rewrite rules. Establish `hd4 : D.host.d % 4 = 3` using `by have := D.host.hyp.2.2.2.1; omega`. Take `⟨k, hk⟩` from `root_eq D.host.d hd4 t n hdisc.symm _ hβ`. Rewrite using `[inOK_iff_int_pair D.host.d _ k hk z]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, y, rfl⟩`. Conclude with `⟨x + y * b 1, by rw [← hσ]; simp⟩`. Introduce and unpack `⟨x, rfl⟩`. Use `⟨b.repr x 0, b.repr x 1, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hσ]`. Use `conv_lhs => rw [GlobalTheory.QuadraticZeta.eq_coord b h0 x]`. Simplify using the standard rewrite rules.
-/
theorem inOK_iff (D : D7) (z : ℂ) :
    InOK D.host.d z ↔ ∃ x : 𝓞 D.host.K, z = D.host.φ₀ ((x : D.host.K) : D.host.E) := by
  obtain ⟨b, t, n, h0, hw, hdisc⟩ := GlobalTheory.QuadraticZeta.exists_basis (K := D.host.K) (GlobalTheory.CurveLattice.finrank_hostK D)
  rw [GlobalTheory.CurveLattice.discr_hostK D] at hdisc
  let σ : 𝓞 D.host.K →+* ℂ := D.host.φ₀.comp ((algebraMap D.host.K D.host.E).comp (algebraMap (𝓞 D.host.K) D.host.K))
  have hσ : ∀ x : 𝓞 D.host.K, σ x = D.host.φ₀ ((x : D.host.K) : D.host.E) := fun x => rfl
  have hβ : σ (b 1) ^ 2 = t * σ (b 1) - n := by
    rw [← map_pow, hw]; simp
  have hd4 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
  obtain ⟨k, hk⟩ := root_eq D.host.d hd4 t n hdisc.symm _ hβ
  rw [inOK_iff_int_pair D.host.d _ k hk z]
  constructor
  · rintro ⟨x, y, rfl⟩
    exact ⟨x + y * b 1, by rw [← hσ]; simp⟩
  · rintro ⟨x, rfl⟩
    refine ⟨b.repr x 0, b.repr x 1, ?_⟩
    rw [← hσ]
    conv_lhs => rw [GlobalTheory.QuadraticZeta.eq_coord b h0 x]
    simp

end GlobalTheory.MomDict

namespace GlobalTheory.MomDict

/- English proof (translation)
Unfold `area`. Establish `: {a : ℝ | 0 < a ∧ ∃ w₁ ∈ (⊥ : AddSubgroup ℂ), ∃ w₂ ∈ (⊥ : AddSubgroup ℂ), a = |((starRingEnd ℂ) w₁ * w₂).im|} = ∅`. Use extensionality with `a`. Simplify using `only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]`. Introduce and unpack `ha ⟨w₁, h1, w₂, h2, rfl⟩`.

Rewrite `h1`, `h2` using `[AddSubgroup.mem_bot]`. Simplify using `[h1, h2] at ha`. Rewrite using `[this, Real.sInf_empty]`.
-/
theorem area_bot : area (⊥ : AddSubgroup ℂ) = 0 := by
  unfold area
  have : {a : ℝ | 0 < a ∧ ∃ w₁ ∈ (⊥ : AddSubgroup ℂ), ∃ w₂ ∈ (⊥ : AddSubgroup ℂ), a = |((starRingEnd ℂ) w₁ * w₂).im|} = ∅ := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ha ⟨w₁, h1, w₂, h2, rfl⟩
    rw [AddSubgroup.mem_bot] at h1 h2
    simp [h1, h2] at ha
  rw [this, Real.sInf_empty]

/- English proof (translation)
Use extensionality with `w`. Rewrite using `[GlobalTheory.CurveLattice.mem_lamOf, AddSubgroup.mem_bot]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, -, rfl⟩`. Simplify using the standard rewrite rules.

Introduce and unpack `rfl; exact ⟨0, cc.zero_mem, by simp⟩`.
-/
theorem lamOf_zero (D : D7) (cc : Ideal (𝓞 D.host.K)) : lamOf D cc 0 = ⊥ := by
  ext w
  rw [GlobalTheory.CurveLattice.mem_lamOf, AddSubgroup.mem_bot]
  constructor
  · rintro ⟨c, -, rfl⟩; simp
  · rintro rfl; exact ⟨0, cc.zero_mem, by simp⟩

/- English proof (translation)
Break down `eq_or_ne δ 0 with rfl | hδ` into its components or cases. Rewrite using `[lamOf_zero, area_bot]`. Simplify using the standard rewrite rules. Take `⟨a, τ, ha, hN, h⟩` from `GlobalTheory.CurveLattice.exists_tau D cc hcc`. Establish `hda : δ * a ≠ 0` using `mul_ne_zero hδ ha`.

Establish `hd : 0 < √(D.host.d : ℝ)` using `Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)`. Rewrite using `[GlobalTheory.CurveLattice.area_of_tau hda (h δ), hN, norm_mul, Complex.normSq_eq_norm_sq]`. Clear the denominators using the available nonvanishing facts.
-/
theorem area_lamOf (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hcc : cc ≠ ⊥) :
    area (lamOf D cc δ) = Complex.normSq δ * (Ideal.absNorm cc : ℝ) * Real.sqrt D.host.d / 2 := by
  rcases eq_or_ne δ 0 with rfl | hδ
  · rw [lamOf_zero, area_bot]; simp
  obtain ⟨a, τ, ha, hN, h⟩ := GlobalTheory.CurveLattice.exists_tau D cc hcc
  have hda : δ * a ≠ 0 := mul_ne_zero hδ ha
  have hd : 0 < √(D.host.d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  rw [GlobalTheory.CurveLattice.area_of_tau hda (h δ), hN, norm_mul, Complex.normSq_eq_norm_sq]
  field_simp

/- English proof (translation)
Introduce `D`. Use `⟨D.host.hyp.2.1, D.host.hyp.2.2.2.1, inOK_iff D, fun x => D.host.conjE_apply _ _, fun cc δ hcc => ⟨area_lamOf D cc δ hcc, fun z => GlobalTheory.CurveLattice.mem_lamOf D cc δ z⟩⟩` and prove the remaining obligations.
-/
theorem main : ∀ (D : D7), D.host.d.Prime ∧ D.host.d % 16 = 7 ∧ (∀ z : ℂ, GlobalTheory.MomOne.InOK D.host.d z ↔ ∃ x : 𝓞 D.host.K, z = D.host.φ₀ ((x : D.host.K) : D.host.E)) ∧ (∀ x : D.host.K, D.host.φ₀ (D.host.conj (x : D.host.E)) = (starRingEnd ℂ) (D.host.φ₀ (x : D.host.E))) ∧ ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → area (lamOf D cc δ) = Complex.normSq δ * (Ideal.absNorm cc : ℝ) * Real.sqrt D.host.d / 2 ∧ ∀ z : ℂ, z ∈ lamOf D cc δ ↔ ∃ x ∈ cc, z = δ * D.host.φ₀ ((x : D.host.K) : D.host.E) := by
  intro D
  refine ⟨D.host.hyp.2.1, D.host.hyp.2.2.2.1, inOK_iff D, fun x => D.host.conjE_apply _ _, fun cc δ hcc => ⟨area_lamOf D cc δ hcc, fun z => GlobalTheory.CurveLattice.mem_lamOf D cc δ z⟩⟩

end GlobalTheory.MomDict
