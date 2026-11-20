import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftOfNonneg
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

/- English proof (translation)
Express the relevant statement in the definitionally equal form `‖ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y‖ * Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + b * ((P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y + 2 * u)) / 2) = _`. Rewrite using `[Pair.nu, mul_assoc, ← Real.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem nu_shiftA {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) (u : ℝ)
    (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    (shiftA P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(b * u)) := by
  change ‖ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y‖ *
      Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y +
        b * ((P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y + 2 * u)) / 2) = _
  rw [Pair.nu, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/- English proof (translation)
Use `⟨hf.1, fun σ y => ?_⟩` and prove the remaining obligations. Rewrite using `[nu_shiftA]`. Establish `h1 : Real.exp (-(b * u)) ≤ 1` using `Real.exp_le_one_iff.2 (by`. Establish `: (0 : ℝ) ≤ b` using `by exact_mod_cast hb`. Use the proof step `nlinarith)`.

Establish `h0 : 0 ≤ P.nu a b σ y f` using `by unfold Pair.nu; positivity`. Establish `h2 : R ≥ P.nu a b σ y f` using `hf.2 σ y`. Use polynomial arithmetic with `[Real.exp_pos (-(b * u))]`.
-/
theorem Bl_subset_shiftA {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) {u : ℝ}
    (hu : 0 ≤ u) (a b : ℤ) (hb : 0 ≤ b) {R : ℝ} {f : X.functionField} (hf : f ∈ P.Bl a b R) :
    f ∈ (shiftA P u).Bl a b R := by
  refine ⟨hf.1, fun σ y => ?_⟩
  rw [nu_shiftA]
  have h1 : Real.exp (-(b * u)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : (0 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith)
  have h0 : 0 ≤ P.nu a b σ y f := by unfold Pair.nu; positivity
  have h2 : R ≥ P.nu a b σ y f := hf.2 σ y
  nlinarith [Real.exp_pos (-(b * u))]

/- English proof (translation)
Introduce `k _ X _ p D hX P b s t u hu h`. Conclude with `{ ample := h.ample nef := GlobalTheory.NefShift.isNef_shift_nonneg k X p D hX P.A u hu h.nef pos := h.pos s_mem := Bl_subset_shiftA P hu 0 1 zero_le_one h.s_mem s_ne := h.s_ne t_mem := Bl_subset_shiftA P hu (-1) b (Int.natCast_nonneg b) h.t_mem t_ne := h.t_ne reg := h.reg }`.
-/
theorem good_shiftA : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (b : ℕ) (s t : X.functionField) (u : ℝ), 0 ≤ u → P.Good D b s t → (shiftA P u).Good D b s t := by
  intro k _ X _ p D hX P b s t u hu h
  exact
    { ample := h.ample
      nef := GlobalTheory.NefShift.isNef_shift_nonneg k X p D hX P.A u hu h.nef
      pos := h.pos
      s_mem := Bl_subset_shiftA P hu 0 1 zero_le_one h.s_mem
      s_ne := h.s_ne
      t_mem := Bl_subset_shiftA P hu (-1) b (Int.natCast_nonneg b) h.t_mem
      t_ne := h.t_ne
      reg := h.reg }

end GlobalTheory.HSNef
