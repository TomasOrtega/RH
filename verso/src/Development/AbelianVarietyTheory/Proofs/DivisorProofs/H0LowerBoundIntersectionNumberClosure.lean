import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefRiemannRochAsymptotic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ClosureRR

/- English proof (translation)
Establish `hf : (0 : ℚ) < k.factorial` using `by exact_mod_cast k.factorial_pos`. Establish `hε : (0 : ℚ) < (T : ℚ) - q` using `sub_pos.2 hq`. Take `⟨N, hN⟩` from `exists_nat_ge ((C : ℚ) * k * 2 ^ (k - 1) / ((T : ℚ) - q))`. Use `⟨N + 1, fun l hl => ?_⟩` and prove the remaining obligations. Establish `hm : (1 : ℚ) ≤ l` using `by exact_mod_cast (show 1 ≤ l by omega)`.

Establish `hNl : (N : ℚ) ≤ l` using `by exact_mod_cast (show N ≤ l by omega)`. Establish `hB : (C : ℚ) * k * 2 ^ (k - 1) ≤ ((T : ℚ) - q) * l`. Use `(div_le_iff₀ hε).1 (hN.trans hNl)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `a` using `hC l`.

Rewrite `a` using `[abs_le]`. Establish `a' : (T : ℚ) * (l : ℚ) ^ k - (C : ℚ) * ((k : ℚ) * ((l : ℚ) + 1) ^ (k - 1)) ≤ (k.factorial : ℚ) * (h l : ℚ)`. Use `a.1` as an intermediate fact. Establish `e : ((T * (l : ℤ) ^ k - C * ((k : ℤ) * ((l : ℤ) + 1) ^ (k - 1)) : ℤ) : ℚ) ≤ (((k.factorial : ℤ) * (h l : ℤ) : ℤ) : ℚ)` using `Int.cast_le.2 (by linarith)`. Move the coercions through the operations in `at e`.

Conclude with `e`. Rewrite using `[div_le_iff₀ hf]`. Break down `k with _ | j` into its components or cases. Simplify using `only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, CharP.cast_eq_zero, zero_mul, mul_zero, sub_zero, one_mul] at a' ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using `only [Nat.add_sub_cancel] at a' hB`. Establish `h2 : ((l : ℚ) + 1) ^ j ≤ 2 ^ j * (l : ℚ) ^ j`. Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ (by positivity) (by linarith) j`. Establish `hl0 : (0 : ℚ) ≤ (l : ℚ) ^ j` using `by positivity`.

Establish `hCk : (0 : ℚ) ≤ (C : ℚ) * ((j + 1 : ℕ) : ℚ)` using `by positivity`. Establish `e1 : (C : ℚ) * (((j + 1 : ℕ) : ℚ) * ((l : ℚ) + 1) ^ j) ≤ (C : ℚ) * ((j + 1 : ℕ) : ℚ) * 2 ^ j * (l : ℚ) ^ j`. Use `mul_le_mul_of_nonneg_left h2 hCk` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `e2 : (C : ℚ) * ((j + 1 : ℕ) : ℚ) * 2 ^ j * (l : ℚ) ^ j ≤ ((T : ℚ) - q) * l * (l : ℚ) ^ j` using `mul_le_mul_of_nonneg_right hB hl0`.

Rewrite `a'`, the goal using `[pow_succ]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem eventually_le_of_abs_sub_le (k C : ℕ) (T : ℤ) (q : ℚ) (hq : q < T) (h : ℕ → ℕ)
    (hC : ∀ m : ℕ, |(k.factorial : ℤ) * (h m : ℤ) - T * (m : ℤ) ^ k| ≤
      C * ((k : ℤ) * ((m : ℤ) + 1) ^ (k - 1))) :
    ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → q * (l : ℚ) ^ k / k.factorial ≤ (h l : ℚ) := by
  have hf : (0 : ℚ) < k.factorial := by exact_mod_cast k.factorial_pos
  have hε : (0 : ℚ) < (T : ℚ) - q := sub_pos.2 hq
  obtain ⟨N, hN⟩ := exists_nat_ge ((C : ℚ) * k * 2 ^ (k - 1) / ((T : ℚ) - q))
  refine ⟨N + 1, fun l hl => ?_⟩
  have hm : (1 : ℚ) ≤ l := by exact_mod_cast (show 1 ≤ l by omega)
  have hNl : (N : ℚ) ≤ l := by exact_mod_cast (show N ≤ l by omega)
  have hB : (C : ℚ) * k * 2 ^ (k - 1) ≤ ((T : ℚ) - q) * l := by
    have := (div_le_iff₀ hε).1 (hN.trans hNl)
    linarith
  have a := hC l
  rw [abs_le] at a
  have a' : (T : ℚ) * (l : ℚ) ^ k - (C : ℚ) * ((k : ℚ) * ((l : ℚ) + 1) ^ (k - 1)) ≤
      (k.factorial : ℚ) * (h l : ℚ) := by
    have := a.1
    have e : ((T * (l : ℤ) ^ k - C * ((k : ℤ) * ((l : ℤ) + 1) ^ (k - 1)) : ℤ) : ℚ) ≤
        (((k.factorial : ℤ) * (h l : ℤ) : ℤ) : ℚ) := Int.cast_le.2 (by linarith)
    push_cast at e
    exact e
  rw [div_le_iff₀ hf]
  rcases k with _ | j
  · simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, CharP.cast_eq_zero, zero_mul,
      mul_zero, sub_zero, one_mul] at a' ⊢
    linarith
  · simp only [Nat.add_sub_cancel] at a' hB
    have h2 : ((l : ℚ) + 1) ^ j ≤ 2 ^ j * (l : ℚ) ^ j := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) j
    have hl0 : (0 : ℚ) ≤ (l : ℚ) ^ j := by positivity
    have hCk : (0 : ℚ) ≤ (C : ℚ) * ((j + 1 : ℕ) : ℚ) := by positivity
    have e1 : (C : ℚ) * (((j + 1 : ℕ) : ℚ) * ((l : ℚ) + 1) ^ j) ≤
        (C : ℚ) * ((j + 1 : ℕ) : ℚ) * 2 ^ j * (l : ℚ) ^ j := by
      have := mul_le_mul_of_nonneg_left h2 hCk
      nlinarith
    have e2 : (C : ℚ) * ((j + 1 : ℕ) : ℚ) * 2 ^ j * (l : ℚ) ^ j ≤ ((T : ℚ) - q) * l * (l : ℚ) ^ j :=
      mul_le_mul_of_nonneg_right hB hl0
    rw [pow_succ] at a' ⊢
    nlinarith

end GlobalTheory.ClosureRR

namespace GlobalTheory.ClosureRR

/- English proof (translation)
Introduce `X _ _ p hp A z k q hA`. Use `letI := algebraΓOfHom p`. Introduce `hdim hq`. Use `haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme := isIntegral_red isIrreducible_singleton.closure`. Use `letI := algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p)`.

Establish `hi : ∀ r : ℂ, (redι (Closeds.closure ({z} : Set X))).appTop (algebraMap ℂ Γ(X, ⊤) r) = algebraMap ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤) r` using `fun r => rfl`. Establish `hpq : IsProjOver (redι (Closeds.closure ({z} : Set X)) ≫ p)`. Take `⟨n, f, hf, hs⟩` from `hp`. Conclude with `⟨n, redι (Closeds.closure ({z} : Set X)) ≫ f, inferInstance, by rw [Category.assoc, hs]⟩`. Establish `hstr : strHom ℂ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme = redι (Closeds.closure ({z} : Set X)) ≫ p` using `strHom_eq fun _ => rfl`.

Establish `hD : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme = k` using `(topologicalKrullDim_red _).trans hdim`. Establish `hNef : IsNef ℂ ((toLB A).pull (redι (Closeds.closure ({z} : Set X))))` using `(IsAmpleLB.isNef (k := ℂ) hA).pull_of_isClosedImmersion _ hi`. Take `⟨C, hC⟩` from `NefRiemannRoch.abs_factorial_mul_sections_sub_top_le ℂ _ (hstr ▸ hpq) k hD.le _ hNef`. Establish `heq : interNumRed ℂ (Closeds.closure ({z} : Set X)) (fun _ : Fin k => toLB A) = topSelfIntersection ℂ ((toLB A).pull (redι (Closeds.closure ({z} : Set X)))) k` using `interNumOn_const_eq_topSelf hi (isLB_toLB A) k`. Establish `hH : ∀ l : ℕ, lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X)))) = lbH0 ℂ (lbPow ((toLB A).pull (redι (Closeds.closure ({z} : Set X)))) l)` using `fun l => lineBundleGlobalSectionsDim_congr_picardClass (pull_isLB (isLB_toLB _) _) (isLB_lbPow (pull_isLB (isLB_toLB A) _) l) (by rw [cls_lbPow (pull_isLB (isLB_toLB A) _), cls_pull (isLB_toLB _), cls_pull (isLB_toLB A), ← toPic_apply, ← toPic_apply, map_nsmul, map_nsmul])`.

Rewrite `hq` using `[heq]`. Take `⟨l₁, hl₁⟩` from `eventually_le_of_abs_sub_le k C _ q hq _ hC`. Conclude with `⟨l₁, fun l hl => by rw [hH l]; exact hl₁ l hl⟩`.
-/
theorem h0_ge_of_lt_interNumRed : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (A : CartierDiv X) (z : X) (k : ℕ) (q : ℚ),
  IsAmpleLB (toLB A) → letI := algebraΓOfHom p; topologicalKrullDim (closure ({z} : Set X)) = k →
  q < (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A : ℤ) →
  ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → q * (l : ℚ) ^ k / k.factorial ≤
    (letI := algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p);
      lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X)))) : ℚ) := by
  intro X _ _ p hp A z k q hA
  letI := algebraΓOfHom p
  intro hdim hq
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme :=
    isIntegral_red isIrreducible_singleton.closure
  letI := algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p)
  have hi : ∀ r : ℂ, (redι (Closeds.closure ({z} : Set X))).appTop (algebraMap ℂ Γ(X, ⊤) r) =
      algebraMap ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤) r :=
    fun r => rfl
  have hpq : IsProjOver (redι (Closeds.closure ({z} : Set X)) ≫ p) := by
    obtain ⟨n, f, hf, hs⟩ := hp
    exact ⟨n, redι (Closeds.closure ({z} : Set X)) ≫ f, inferInstance, by rw [Category.assoc, hs]⟩
  have hstr : strHom ℂ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme =
      redι (Closeds.closure ({z} : Set X)) ≫ p := strHom_eq fun _ => rfl
  have hD : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme = k :=
    (topologicalKrullDim_red _).trans hdim
  have hNef : IsNef ℂ ((toLB A).pull (redι (Closeds.closure ({z} : Set X)))) :=
    (IsAmpleLB.isNef (k := ℂ) hA).pull_of_isClosedImmersion _ hi
  obtain ⟨C, hC⟩ := NefRiemannRoch.abs_factorial_mul_sections_sub_top_le ℂ _ (hstr ▸ hpq) k hD.le _ hNef
  have heq : interNumRed ℂ (Closeds.closure ({z} : Set X)) (fun _ : Fin k => toLB A) =
      topSelfIntersection ℂ ((toLB A).pull (redι (Closeds.closure ({z} : Set X)))) k :=
    interNumOn_const_eq_topSelf hi (isLB_toLB A) k
  have hH : ∀ l : ℕ, lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X)))) =
      lbH0 ℂ (lbPow ((toLB A).pull (redι (Closeds.closure ({z} : Set X)))) l) := fun l =>
    lineBundleGlobalSectionsDim_congr_picardClass (pull_isLB (isLB_toLB _) _) (isLB_lbPow (pull_isLB (isLB_toLB A) _) l)
      (by rw [cls_lbPow (pull_isLB (isLB_toLB A) _), cls_pull (isLB_toLB _), cls_pull (isLB_toLB A),
        ← toPic_apply, ← toPic_apply, map_nsmul, map_nsmul])
  rw [heq] at hq
  obtain ⟨l₁, hl₁⟩ := eventually_le_of_abs_sub_le k C _ q hq _ hC
  exact ⟨l₁, fun l hl => by rw [hH l]; exact hl₁ l hl⟩

end GlobalTheory.ClosureRR
