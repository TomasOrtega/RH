import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp

section GapArith

variable {N : ℕ}

/- English proof (translation)
Unfold `gap`. Use `split_ifs`. Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem gap_add (v w : Fin N → ℤ) (k : ℕ) : gap (v + w) k = gap v k + gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.add_apply]
    ring
  · simp

/- English proof (translation)
Unfold `gap`. Use `split_ifs`. Simplify using `only [Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem gap_sub (v w : Fin N → ℤ) (k : ℕ) : gap (v - w) k = gap v k - gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.sub_apply]
    ring
  · simp

/- English proof (translation)
Unfold `gap`. Use `split_ifs`. Simplify using `only [Pi.smul_apply, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem gap_nsmul (n : ℕ) (v : Fin N → ℤ) (k : ℕ) : gap (n • v) k = n * gap v k := by
  unfold gap
  split_ifs
  · simp only [Pi.smul_apply, nsmul_eq_mul]
    ring
  · simp

end GapArith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

/- English proof (translation)
Unfold `FlagTan.kap gap`. Simplify using `only [dif_pos h]`. Apply the tactic sequence `split_ifs <;> push_cast <;> omega`.
-/
theorem gap_kap (τ : Psi H) {k : ℕ} (h : k + 1 < Dw.p + Dw.q) : gap (FlagTan.kap Dw τ) k =
    if k + 1 = Dw.p then 2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2 else -2 := by
  unfold FlagTan.kap gap
  simp only [dif_pos h]
  split_ifs <;> push_cast <;> omega

/- English proof (translation)
Rewrite using `[gap_kap τ h]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem gap_kap_le (τ : Psi H) {k : ℕ} (h : k + 1 < Dw.p + Dw.q) :
    gap (FlagTan.kap Dw τ) k ≤ 2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2 := by
  rw [gap_kap τ h]
  split_ifs <;> omega

/- English proof (translation)
Establish `h₁ : n * (g / n) ≤ g` using `by first`. Consider the case `exact Int.mul_ediv_self_le hn.ne'`. Consider the case `exact Int.mul_ediv_le hn g`. Consider the case `(have := Int.emod_def g n; have := Int.emod_nonneg g hn.ne'; linarith)`. Consider the case `(have := Int.ediv_mul_le g hn.ne'; linarith)`.

Consider the case `(have := Int.emod_add_mul_ediv g n; have := Int.emod_nonneg g hn.ne'; linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem div_le_sub_mul_div (g : ℤ) {n : ℤ} (hn : 0 < n) : g / n ≤ g - (n - 1) * (g / n) := by
  have h₁ : n * (g / n) ≤ g := by
    first
      | exact Int.mul_ediv_self_le hn.ne'
      | exact Int.mul_ediv_le hn g
      | (have := Int.emod_def g n; have := Int.emod_nonneg g hn.ne'; linarith)
      | (have := Int.ediv_mul_le g hn.ne'; linarith)
      | (have := Int.emod_add_mul_ediv g n; have := Int.emod_nonneg g hn.ne'; linarith)
  linarith

/- English proof (translation)
Introduce `E _ _ _ H Dw P hP la hla`. Establish `hD3 : (0 : ℤ) < (dimFlag Dw : ℤ) + 3` using `by positivity`. Establish `hmain : ∀ (τ : Psi H) (k : ℕ), k + 1 < Dw.p + Dw.q → (((dimFlag Dw + 1).choose 2 : ℕ) : ℤ) + 4 * ((Dw.p : ℤ) + Dw.q) + dimFlag Dw + 3 ≤ gap (P.ub τ) k ∧ gap (P.ub τ) k ≤ gap (P.u₁ τ) k - ((dimFlag Dw : ℤ) + 2) * gap (P.ub τ) k ∧ gap (P.u₁ τ) k ≤ gap (P.u₂ τ) k`. Introduce `τ k h`. Establish `hg` using `hP.gaps τ k h`.

Move the coercions through the operations in `at hg`. Rewrite using `[P.gap_ub τ h]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Apply `Int.le_ediv_of_mul_le hD3` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.

Use `div_le_sub_mul_div (gap (P.u₁ τ) k) hD3` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[show P.u₂ τ = P.u₁ τ + P.rem τ from rfl, gap_add]`. Combine the linear relations using `[(P.gap_rem τ k).1]`. Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hla`.

Apply the tactic sequence `rcases hla with rfl | rfl | rfl | rfl <;> constructor <;> intro τ k h <;>`. Take `⟨h₁, h₂, h₃⟩` from `hmain τ k h`. Establish `h₄` using `gap_kap_le τ h`. Move the coercions through the operations in `at h₄`. Establish `hC : (0 : ℤ) ≤ (((dimFlag Dw + 1).choose 2 : ℕ) : ℤ)` using `by positivity`.

Establish `hD : (0 : ℤ) ≤ (dimFlag Dw : ℤ)` using `by positivity`. Establish `hN : (2 : ℤ) ≤ (Dw.p : ℤ) + Dw.q` using `by omega`. Establish `hb : (0 : ℤ) ≤ ((dimFlag Dw : ℤ) + 2) * gap (P.ub τ) k`. Apply the tactic sequence `apply mul_nonneg <;> linarith`. Apply the tactic sequence `try simp only [Pi.sub_apply, Pi.smul_apply, gap_sub, gap_nsmul]`.

Apply the tactic sequence `try push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gaps_of_wtBig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (P : WtPar Dw), WtBig P → ∀ la ∈ [P.u₁, P.u₂, P.ub, P.u₁ - FlagTan.kap Dw - (dimFlag Dw + 2) • P.ub], GapGe 1 la ∧ GapGe (((dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap Dw) := by
  intro E _ _ _ H Dw P hP la hla
  have hD3 : (0 : ℤ) < (dimFlag Dw : ℤ) + 3 := by positivity
  have hmain : ∀ (τ : Psi H) (k : ℕ), k + 1 < Dw.p + Dw.q →
      (((dimFlag Dw + 1).choose 2 : ℕ) : ℤ) + 4 * ((Dw.p : ℤ) + Dw.q) + dimFlag Dw + 3 ≤ gap (P.ub τ) k ∧
      gap (P.ub τ) k ≤ gap (P.u₁ τ) k - ((dimFlag Dw : ℤ) + 2) * gap (P.ub τ) k ∧
      gap (P.u₁ τ) k ≤ gap (P.u₂ τ) k := by
    intro τ k h
    have hg := hP.gaps τ k h
    push_cast at hg
    rw [P.gap_ub τ h]
    refine ⟨?_, ?_, ?_⟩
    · apply Int.le_ediv_of_mul_le hD3
      linarith
    · have := div_le_sub_mul_div (gap (P.u₁ τ) k) hD3
      linarith
    · rw [show P.u₂ τ = P.u₁ τ + P.rem τ from rfl, gap_add]
      linarith [(P.gap_rem τ k).1]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hla
  rcases hla with rfl | rfl | rfl | rfl <;> constructor <;> intro τ k h <;>
  · obtain ⟨h₁, h₂, h₃⟩ := hmain τ k h
    have h₄ := gap_kap_le τ h
    push_cast at h₄
    have hC : (0 : ℤ) ≤ (((dimFlag Dw + 1).choose 2 : ℕ) : ℤ) := by positivity
    have hD : (0 : ℤ) ≤ (dimFlag Dw : ℤ) := by positivity
    have hN : (2 : ℤ) ≤ (Dw.p : ℤ) + Dw.q := by omega
    have hb : (0 : ℤ) ≤ ((dimFlag Dw : ℤ) + 2) * gap (P.ub τ) k := by
      apply mul_nonneg <;> linarith
    try simp only [Pi.sub_apply, Pi.smul_apply, gap_sub, gap_nsmul]
    try push_cast
    linarith

end GlobalTheory.HSApp
