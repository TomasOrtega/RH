import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsFactorialMulEulerCharTwistPowSubLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerCharH0H1BoundHigherStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfForallIsPsEff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

/- English proof (translation)
Introduce `k _ _ X _ hX d L hL F _ hF h0 hI hi`. Take `⟨C2, hC2⟩` from `GlobalTheory.T.abs_factorial_mul_eulerChar_twist_pow_sub_le k X hX (d+1) F hF L hL`. Take `⟨C1, hC1⟩` from `GlobalTheory.T.euler_char_h0_h1_bound_higher k X hX (d+1) L hL F hF (fun m => (d+1)*(m+1)^d) hi`. Use `⟨C1 + C2 + hdim k (twist F (lbPow L 0)) 1, fun m => ?_⟩` and prove the remaining obligations. Establish `he1 : 1 ≤ (d+1)*(m+1)^d` using `Nat.one_le_iff_ne_zero.mpr (by positivity)`.

Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Combine the equalities or inequalities in the displayed calculation. Establish `a1` using `hC1 m`. Establish `a2` using `hC2 m`. Rewrite `a1` using `[h0 m hm]`.

Simplify using `only [Nat.add_sub_cancel] at a2`. Establish `hfac : (1 : ℤ) ≤ ((d+1).factorial : ℤ)`. Conclude with `Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)` after adjusting the coercions. Establish `hImp : 0 ≤ interNum k F (fun _ : Fin (d + 1) => L) * (m : ℤ)^(d+1)` using `mul_nonneg hI (by positivity)`. Establish `hE : (((d+1)*(m+1)^d : ℕ) : ℤ) = ((d+1 : ℕ) : ℤ) * ((m : ℤ) + 1) ^ d` using `by push_cast; ring`.

Rewrite `a2` using `[← hE]`. Establish `hEpos : (1 : ℤ) ≤ (((d+1)*(m+1)^d : ℕ) : ℤ)` using `by exact_mod_cast he1`. It suffices to establish `h : (hdim k (twist F (lbPow L m)) 1 : ℤ) ≤ ((C1 + C2 + hdim k (twist F (lbPow L 0)) 1 : ℕ) : ℤ) * (((d+1)*(m+1)^d : ℕ) : ℤ) by`. Conclude with `h` after adjusting the coercions. Generalize the expression as in `(((d+1)*(m+1)^d : ℕ) : ℤ) = E at a1 a2 hEpos ⊢`.

Generalize the expression as in `chi k (twist F (lbPow L m)) = c at a1 a2`. Generalize the expression as in `interNum k F (fun _ : Fin (d + 1) => L) * (m : ℤ)^(d+1) = I at a2 hImp`. Generalize the expression as in `(((d+1).factorial : ℕ) : ℤ) = f at a2 hfac`. Generalize the expression as in `(hdim k (twist F (lbPow L m)) 1 : ℤ) = H at a1 ⊢`. Use `push_cast`.

Establish `hh0 : (0 : ℤ) ≤ (hdim k (twist F (lbPow L 0)) 1 : ℤ)` using `by positivity`. Generalize the expression as in `(hdim k (twist F (lbPow L 0)) 1 : ℤ) = h00 at hh0 ⊢`. Establish `hC1' : (0:ℤ) ≤ C1` using `by positivity`. Establish `hC2' : (0:ℤ) ≤ C2` using `by positivity`. Rewrite `a1`, `a2` using `[abs_le]`.

Simplify using `only [CharP.cast_eq_zero, sub_zero] at a1`. Establish `hc : -c ≤ (C2 : ℤ) * E`. Break down `le_or_gt 0 c with hc | hc` into its components or cases. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem GlobalTheory.noSection_H1_bound_riemann_roch : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → (∀ m : ℕ, 1 ≤ m → hdim k (twist F (lbPow L m)) 0 = 0) → 0 ≤ interNum k F (fun _ : Fin (d + 1) => L) → (∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d))) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) 1 ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ hX d L hL F _ hF h0 hI hi
  obtain ⟨C2, hC2⟩ := GlobalTheory.T.abs_factorial_mul_eulerChar_twist_pow_sub_le k X hX (d+1) F hF L hL
  obtain ⟨C1, hC1⟩ := GlobalTheory.T.euler_char_h0_h1_bound_higher k X hX (d+1) L hL F hF (fun m => (d+1)*(m+1)^d) hi
  refine ⟨C1 + C2 + hdim k (twist F (lbPow L 0)) 1, fun m => ?_⟩
  have he1 : 1 ≤ (d+1)*(m+1)^d := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · calc hdim k (twist F (lbPow L 0)) 1 ≤ hdim k (twist F (lbPow L 0)) 1 * ((d+1)*(0+1)^d) :=
          Nat.le_mul_of_pos_right _ he1
      _ ≤ (C1 + C2 + hdim k (twist F (lbPow L 0)) 1) * ((d+1)*(0+1)^d) :=
          Nat.mul_le_mul_right _ (by omega)
  · have a1 := hC1 m
    have a2 := hC2 m
    rw [h0 m hm] at a1
    simp only [Nat.add_sub_cancel] at a2
    have hfac : (1 : ℤ) ≤ ((d+1).factorial : ℤ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hImp : 0 ≤ interNum k F (fun _ : Fin (d + 1) => L) * (m : ℤ)^(d+1) := mul_nonneg hI (by positivity)
    have hE : (((d+1)*(m+1)^d : ℕ) : ℤ) = ((d+1 : ℕ) : ℤ) * ((m : ℤ) + 1) ^ d := by push_cast; ring
    rw [← hE] at a2
    have hEpos : (1 : ℤ) ≤ (((d+1)*(m+1)^d : ℕ) : ℤ) := by exact_mod_cast he1
    suffices h : (hdim k (twist F (lbPow L m)) 1 : ℤ) ≤
        ((C1 + C2 + hdim k (twist F (lbPow L 0)) 1 : ℕ) : ℤ) * (((d+1)*(m+1)^d : ℕ) : ℤ) by
      exact_mod_cast h
    generalize (((d+1)*(m+1)^d : ℕ) : ℤ) = E at a1 a2 hEpos ⊢
    generalize chi k (twist F (lbPow L m)) = c at a1 a2
    generalize interNum k F (fun _ : Fin (d + 1) => L) * (m : ℤ)^(d+1) = I at a2 hImp
    generalize (((d+1).factorial : ℕ) : ℤ) = f at a2 hfac
    generalize (hdim k (twist F (lbPow L m)) 1 : ℤ) = H at a1 ⊢
    push_cast
    have hh0 : (0 : ℤ) ≤ (hdim k (twist F (lbPow L 0)) 1 : ℤ) := by positivity
    generalize (hdim k (twist F (lbPow L 0)) 1 : ℤ) = h00 at hh0 ⊢
    have hC1' : (0:ℤ) ≤ C1 := by positivity
    have hC2' : (0:ℤ) ≤ C2 := by positivity
    rw [abs_le] at a1 a2
    simp only [CharP.cast_eq_zero, sub_zero] at a1
    have hc : -c ≤ (C2 : ℤ) * E := by
      rcases le_or_gt 0 c with hc | hc
      · nlinarith
      · nlinarith
    nlinarith
