import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Formalism.LocalToGlobal.LatticeGeometry.PluckerHadamard.WeylPolynomialAlgebra

noncomputable section

namespace RootFieldNumerics.TF

section A
open Finset MvPolynomial Formalism.L2.Geo Formalism.L2.Geo.WeylPolynomialAlgebra

/- English proof (translation)
Use `set n := a0n Ψ N j`. Use `set k := (idxS Ψ N j).card with hkdef`. Use `set D := Formalism.DegreeFormula.dimFl Ψ N with hDdef`. Establish `hD : D = n + k` using `dim_split j hj`. Use `set fib : Formalism.ShimuraLimitIdentity.Pol Ψ N := ∏ t ∈ idxS Ψ N j, ell t with hfib`.

Use `set K0 : ℝ := (D.factorial : ℝ) * (∏ t ∈ idxS Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1)) * (∏ t ∈ idxC Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1)) / (D.choose n : ℝ) with hK0`. Establish `hpos : ∀ s : Finset (Ψ × Fin N × Fin N), (∀ t ∈ s, t.2.1 < t.2.2) → 0 < ∏ t ∈ s, 1 / ((t.2.2 : ℝ) - t.2.1)`. Introduce `s hs`. Use `Finset.prod_pos (fun t ht => ?_)` and prove the remaining obligations. Establish `: (t.2.1 : ℝ) < t.2.2` using `by exact_mod_cast (hs t ht)`.

Conclude with `one_div_pos.mpr (by linarith)`. Establish `hK0pos : 0 < K0`. Establish `h1` using `hpos (idxS Ψ N j) (fun t ht => (Finset.mem_filter.mp ht).2.1)`. Establish `h2` using `hpos (idxC Ψ N j) (fun t ht => (Finset.mem_filter.mp ht).2.1)`. Establish `h3 : (0 : ℝ) < (D.choose n : ℝ)` using `by exact_mod_cast Nat.choose_pos (by omega)`.

Establish `h4 : (0 : ℝ) < (D.factorial : ℝ)` using `by exact_mod_cast Nat.factorial_pos D`. Check the signs of the components of the expression. Establish `hPhi : ∀ ν : Ψ → Fin N → ℝ, PhiL j n (Formalism.DegreeFormula.linRoot ν ^ k) = K0 * eval (fun x => ν x.1 x.2) fib`. Introduce `ν`. Establish `hw` using `weyl_coeff j ν n k hD hkdef.symm`.

Rewrite using `[PhiL_apply, eval_fib]`. Establish `hc : (D.choose n : ℝ) ≠ 0` using `by exact_mod_cast (Nat.choose_pos (by omega)).ne'`. Establish `e : ∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1) = (∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2)) * ∏ t ∈ idxS Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1)`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl (fun t _ => ?_)` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hw` using `[e]`. Rewrite using `[hK0]`. Clear the denominators using the available nonvanishing facts. Combine the linear relations using `[hw]`.

Establish `hApol : ∀ ν : Ψ → Fin N → ℝ, apolL fib (Formalism.DegreeFormula.linRoot ν ^ k) = (k.factorial : ℝ) * (-1) ^ k * eval (fun x => ν x.1 x.2) fib`. Introduce `ν`. Use `show apol fib _ = _`. Rewrite using `[linRoot_eq_smul, apol_pow fib k (fib_homog j), eval_fib, eval_fib]`. Establish `e : ∏ t ∈ idxS Ψ N j, (-ν t.1 t.2.1 - -ν t.1 t.2.2) = (-1) ^ k * ∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2)`.

Rewrite using `[hkdef, ← Finset.prod_const, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl (fun t _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.

Use `set c : ℝ := K0 * (-1) ^ k / (k.factorial : ℝ) with hc`. Establish `hkf : (k.factorial : ℝ) ≠ 0` using `by exact_mod_cast (Nat.factorial_pos k).ne'`. Establish `hagree : ∀ ν : Ψ → Fin N → ℝ, PhiL j n (Formalism.DegreeFormula.linRoot ν ^ k) = c * apolL fib (Formalism.DegreeFormula.linRoot ν ^ k)`. Introduce `ν`. Rewrite using `[hPhi, hApol, hc]`.

Establish `h1 : ((-1 : ℝ) ^ k) * (-1) ^ k = 1` using `by rw [← mul_pow]; norm_num`. Conclude with `mul_eq_sign_rearrange K0 _ _ _ hkf h1`. Establish `hpol` using `polarization (fun t => (ell t : Formalism.ShimuraLimitIdentity.Pol Ψ N)) (idxS Ψ N j)`. Establish `hsumS : ∀ S : Finset (Ψ × Fin N × Fin N), (∑ t ∈ S, (ell t : Formalism.ShimuraLimitIdentity.Pol Ψ N)) = Formalism.DegreeFormula.linRoot (∑ t ∈ S, nuT t)`. Introduce `S`.

Rewrite using `[linRoot_sum]`. Conclude with `Finset.sum_congr rfl (fun t _ => (linRoot_nuT t).symm)`. Establish `hcast : ∀ S : Finset (Ψ × Fin N × Fin N), ((-1 : Formalism.ShimuraLimitIdentity.Pol Ψ N) ^ ((idxS Ψ N j).card - S.card)) = C ((-1 : ℝ) ^ ((idxS Ψ N j).card - S.card))`. Introduce `S`. Rewrite using `[map_pow, map_neg, map_one]`.

Rewrite `hpol` using `[← hfib]`. Simplify using `only [hsumS, hcast] at hpol`. Rewrite using `[show (((idxS Ψ N j).card.factorial : ℕ) : Formalism.ShimuraLimitIdentity.Pol Ψ N) = C ((k.factorial : ℕ) : ℝ) by`. Rewrite `hpol` using `[map_natCast]]`. Establish `hP` using `congrArg (PhiL j n) hpol`.

Establish `hA` using `congrArg (apolL fib) hpol`. Rewrite `hP` using `[PhiL_C_mul, map_sum]`. Rewrite `hA` using `[apolL_C_mul, map_sum]`. Simplify using `only [PhiL_C_mul, apolL_C_mul, ← hkdef, hagree] at hP hA`. Establish `hmain : PhiL j n fib = c * apolL fib fib`.

Establish `e1 : ∑ S ∈ (idxS Ψ N j).powerset, (-1 : ℝ) ^ ((idxS Ψ N j).card - S.card) * (c * apolL fib (Formalism.DegreeFormula.linRoot (∑ t ∈ S, nuT t) ^ k)) = c * ∑ S ∈ (idxS Ψ N j).powerset, (-1 : ℝ) ^ ((idxS Ψ N j).card - S.card) * apolL fib (Formalism.DegreeFormula.linRoot (∑ t ∈ S, nuT …`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun S _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite `hP` using `[e1, ← hA]`.

Establish `: (k.factorial : ℝ) * PhiL j n fib = (k.factorial : ℝ) * (c * apolL fib fib)` using `by rw [hP]; ring`. Conclude with `mul_left_cancel₀ hkf this`. Establish `hapos : 0 < apolL fib fib` using `apol_self_pos fib (fib_ne_zero j)`. Rewrite using `[hmain, hc]`. Establish `h1 : ((-1 : ℝ) ^ k) * (-1) ^ k = 1` using `by rw [← mul_pow]; norm_num`.

Establish `h4 : (0 : ℝ) < (k.factorial : ℝ)` using `by exact_mod_cast Nat.factorial_pos k`. Establish `e : (-1 : ℝ) ^ k * (K0 * (-1) ^ k / (k.factorial : ℝ) * apolL fib fib) = ((-1 : ℝ) ^ k * (-1) ^ k) * (K0 / (k.factorial : ℝ) * apolL fib fib)` using `by ring`. Rewrite using `[e, h1]`. Check the signs of the components of the expression.
-/
theorem jPos (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (hj : j ≤ N) :
    0 < (-1) ^ (idxS Ψ N j).card * PhiL j (a0n Ψ N j) (∏ t ∈ idxS Ψ N j, ell t) := by
  set n := a0n Ψ N j
  set k := (idxS Ψ N j).card with hkdef
  set D := Formalism.DegreeFormula.dimFl Ψ N with hDdef
  have hD : D = n + k := dim_split j hj
  set fib : Formalism.ShimuraLimitIdentity.Pol Ψ N := ∏ t ∈ idxS Ψ N j, ell t with hfib

  set K0 : ℝ := (D.factorial : ℝ) * (∏ t ∈ idxS Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1)) *
    (∏ t ∈ idxC Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1)) / (D.choose n : ℝ) with hK0
  have hpos : ∀ s : Finset (Ψ × Fin N × Fin N), (∀ t ∈ s, t.2.1 < t.2.2) →
      0 < ∏ t ∈ s, 1 / ((t.2.2 : ℝ) - t.2.1) := by
    intro s hs
    refine Finset.prod_pos (fun t ht => ?_)
    have : (t.2.1 : ℝ) < t.2.2 := by exact_mod_cast (hs t ht)
    exact one_div_pos.mpr (by linarith)
  have hK0pos : 0 < K0 := by
    have h1 := hpos (idxS Ψ N j) (fun t ht => (Finset.mem_filter.mp ht).2.1)
    have h2 := hpos (idxC Ψ N j) (fun t ht => (Finset.mem_filter.mp ht).2.1)
    have h3 : (0 : ℝ) < (D.choose n : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
    have h4 : (0 : ℝ) < (D.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos D
    positivity

  have hPhi : ∀ ν : Ψ → Fin N → ℝ, PhiL j n (Formalism.DegreeFormula.linRoot ν ^ k) =
      K0 * eval (fun x => ν x.1 x.2) fib := by
    intro ν
    have hw := weyl_coeff j ν n k hD hkdef.symm
    rw [PhiL_apply, eval_fib]
    have hc : (D.choose n : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
    have e : ∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2) / ((t.2.2 : ℝ) - t.2.1) =
        (∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2)) * ∏ t ∈ idxS Ψ N j, 1 / ((t.2.2 : ℝ) - t.2.1) := by
      rw [← Finset.prod_mul_distrib]; refine Finset.prod_congr rfl (fun t _ => ?_); ring
    rw [e] at hw
    rw [hK0]
    field_simp
    linarith [hw]

  have hApol : ∀ ν : Ψ → Fin N → ℝ, apolL fib (Formalism.DegreeFormula.linRoot ν ^ k) =
      (k.factorial : ℝ) * (-1) ^ k * eval (fun x => ν x.1 x.2) fib := by
    intro ν
    show apol fib _ = _
    rw [linRoot_eq_smul, apol_pow fib k (fib_homog j), eval_fib, eval_fib]
    have e : ∏ t ∈ idxS Ψ N j, (-ν t.1 t.2.1 - -ν t.1 t.2.2) =
        (-1) ^ k * ∏ t ∈ idxS Ψ N j, (ν t.1 t.2.1 - ν t.1 t.2.2) := by
      rw [hkdef, ← Finset.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun t _ => ?_); ring
    rw [e]; ring

  set c : ℝ := K0 * (-1) ^ k / (k.factorial : ℝ) with hc
  have hkf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have hagree : ∀ ν : Ψ → Fin N → ℝ, PhiL j n (Formalism.DegreeFormula.linRoot ν ^ k) = c * apolL fib (Formalism.DegreeFormula.linRoot ν ^ k) := by
    intro ν
    rw [hPhi, hApol, hc]
    have h1 : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
    exact mul_eq_sign_rearrange K0 _ _ _ hkf h1

  have hpol := polarization (fun t => (ell t : Formalism.ShimuraLimitIdentity.Pol Ψ N)) (idxS Ψ N j)
  have hsumS : ∀ S : Finset (Ψ × Fin N × Fin N), (∑ t ∈ S, (ell t : Formalism.ShimuraLimitIdentity.Pol Ψ N)) =
      Formalism.DegreeFormula.linRoot (∑ t ∈ S, nuT t) := by
    intro S; rw [linRoot_sum]; exact Finset.sum_congr rfl (fun t _ => (linRoot_nuT t).symm)
  have hcast : ∀ S : Finset (Ψ × Fin N × Fin N), ((-1 : Formalism.ShimuraLimitIdentity.Pol Ψ N) ^ ((idxS Ψ N j).card - S.card)) =
      C ((-1 : ℝ) ^ ((idxS Ψ N j).card - S.card)) := by
    intro S; rw [map_pow, map_neg, map_one]
  rw [← hfib] at hpol
  simp only [hsumS, hcast] at hpol
  rw [show (((idxS Ψ N j).card.factorial : ℕ) : Formalism.ShimuraLimitIdentity.Pol Ψ N) = C ((k.factorial : ℕ) : ℝ) by
    rw [map_natCast]] at hpol
  have hP := congrArg (PhiL j n) hpol
  have hA := congrArg (apolL fib) hpol
  rw [PhiL_C_mul, map_sum] at hP
  rw [apolL_C_mul, map_sum] at hA
  simp only [PhiL_C_mul, apolL_C_mul, ← hkdef, hagree] at hP hA
  have hmain : PhiL j n fib = c * apolL fib fib := by
    have e1 : ∑ S ∈ (idxS Ψ N j).powerset, (-1 : ℝ) ^ ((idxS Ψ N j).card - S.card) *
        (c * apolL fib (Formalism.DegreeFormula.linRoot (∑ t ∈ S, nuT t) ^ k)) =
        c * ∑ S ∈ (idxS Ψ N j).powerset, (-1 : ℝ) ^ ((idxS Ψ N j).card - S.card) *
          apolL fib (Formalism.DegreeFormula.linRoot (∑ t ∈ S, nuT t) ^ k) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun S _ => ?_); ring
    rw [e1, ← hA] at hP
    have : (k.factorial : ℝ) * PhiL j n fib = (k.factorial : ℝ) * (c * apolL fib fib) := by rw [hP]; ring
    exact mul_left_cancel₀ hkf this
  have hapos : 0 < apolL fib fib := apol_self_pos fib (fib_ne_zero j)
  rw [hmain, hc]
  have h1 : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  have h4 : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have e : (-1 : ℝ) ^ k * (K0 * (-1) ^ k / (k.factorial : ℝ) * apolL fib fib) =
      ((-1 : ℝ) ^ k * (-1) ^ k) * (K0 / (k.factorial : ℝ) * apolL fib fib) := by ring
  rw [e, h1]
  positivity

end A

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
open Formalism.L2.Geo.WeylPolynomialAlgebra Formalism.L2.Geo.BlockVandermondeForms

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

/- English proof (translation)
Rewrite using `[map_pow, ← Finset.prod_const, ← Finset.prod_mul_distrib]`. Unfold `fibClass idxS ell`. Rewrite using `[Finset.prod_filter, Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.prod_filter]`.

Use `Finset.prod_congr rfl (fun ab _ => ?_)` and prove the remaining obligations. Use `split_ifs`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem fib_eq' (j : ℕ) :
    (fibClass j : RP Ψ N) = C ((-1 : ℝ) ^ (idxS Ψ N j).card) * ∏ t ∈ idxS Ψ N j, ell t := by
  rw [map_pow, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  unfold fibClass idxS ell
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl (fun τ _ => ?_)
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl (fun ab _ => ?_)
  split_ifs
  · simp
  · rfl

/- English proof (translation)
Rewrite using `[Formalism.L2.Geo.degFlL_apply]`. Both sides reduce to the same expression.
-/
theorem degFl_eq (F : RP Ψ N) : degFl F = Formalism.L2.Geo.degFlL Ψ N F := by
  rw [Formalism.L2.Geo.degFlL_apply]; rfl

/- English proof (translation)
Rewrite using `[degFl_eq, degFl_eq, degFlL_C_mul]`.
-/
theorem degFl_C_mul (a : ℝ) (F : RP Ψ N) : degFl (C a * F) = a * degFl F := by
  rw [degFl_eq, degFl_eq, degFlL_C_mul]

/- English proof (translation)
Unfold `muSmall`. Use `split_ifs`. Conclude with `⟨0, by rw [zero_mul, sub_eq_zero]; rfl⟩`. Use `⟨-1, ?_⟩` and prove the remaining obligations. Unfold `Formalism.L2.Geo.a0Mu Formalism.L2.Geo.smallBlock pkLow pk`.

Rewrite using `[← neg_add', neg_one_mul, ← Finset.sum_add_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Simplify using `only [pow_one, Finset.sum_filter, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Distinguish the cases in `h : (i : ℕ) < j`. Rewrite using `[if_pos h, if_neg (by omega), add_zero]`. Rewrite using `[if_neg h, if_pos (by omega), zero_add]`.
-/
theorem mu_sub (j : ℕ) : ∃ c : RP Ψ N, (muSmall j : RP Ψ N) - Formalism.L2.Geo.a0Mu j = c * ∑ τ, pk τ 1 := by
  unfold muSmall
  split_ifs
  · exact ⟨0, by rw [zero_mul, sub_eq_zero]; rfl⟩
  · refine ⟨-1, ?_⟩
    unfold Formalism.L2.Geo.a0Mu Formalism.L2.Geo.smallBlock pkLow pk
    rw [← neg_add', neg_one_mul, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    simp only [pow_one, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : (i : ℕ) < j
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]

/- English proof (translation)
Take `⟨c, hc⟩` from `mu_sub (Ψ := Ψ) (N := N) j`. Take `⟨d, hd⟩` from `sub_dvd_pow_sub_pow (muSmall j : RP Ψ N) (Formalism.L2.Geo.a0Mu j) n`. Establish `e : (muSmall j : RP Ψ N) ^ n * G = Formalism.L2.Geo.a0Mu j ^ n * G + ∑ τ, pk τ 1 * (c * d * G)`. Rewrite using `[← Finset.sum_mul]`. Rewrite `hd` using `[hc]`.

Take the linear combination `G * hd`. Rewrite using `[e, degFl_eq, degFl_eq, map_add, map_sum, Finset.sum_eq_zero, add_zero]`. Introduce `τ _`. Conclude with `Formalism.L2.Geo.flag_integral_kills_power_sums Ψ N τ 1 le_rfl _`.
-/
theorem deg_mu (j n : ℕ) (G : RP Ψ N) :
    degFl (muSmall j ^ n * G) = degFl (Formalism.L2.Geo.a0Mu j ^ n * G) := by
  obtain ⟨c, hc⟩ := mu_sub (Ψ := Ψ) (N := N) j
  obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (muSmall j : RP Ψ N) (Formalism.L2.Geo.a0Mu j) n
  have e : (muSmall j : RP Ψ N) ^ n * G = Formalism.L2.Geo.a0Mu j ^ n * G + ∑ τ, pk τ 1 * (c * d * G) := by
    rw [← Finset.sum_mul]
    rw [hc] at hd
    linear_combination G * hd
  rw [e, degFl_eq, degFl_eq, map_add, map_sum, Finset.sum_eq_zero, add_zero]
  intro τ _
  exact Formalism.L2.Geo.flag_integral_kills_power_sums Ψ N τ 1 le_rfl _

/- English proof (translation)
Unfold `testDeg`. Rewrite using `[deg_mu, fib_eq', mul_left_comm, degFl_C_mul, degFl_eq]`. Conclude with `jPos Ψ N j hj`.
-/
theorem testDeg_pos (j : ℕ) (hj : j ≤ N) : 0 < testDeg Ψ N j := by
  unfold testDeg
  rw [deg_mu, fib_eq', mul_left_comm, degFl_C_mul, degFl_eq]
  exact jPos Ψ N j hj

/- English proof (translation)
Unfold `fibClass`. Use `d_prod_zero _ _ _ (fun σ _ => d_prod_zero _ _ _ (fun ab hab => ?_))` and prove the remaining obligations. Establish `h` using `hS _ _ (Finset.mem_filter.mp hab).2.2`. Rewrite using `[map_sub, dS_X, dS_X]`. Simplify using `only [h, sub_self]`.
-/
theorem d_fib (τ : Ψ) (j : ℕ) (S : Finset (Fin N))
    (hS : ∀ a b : Fin N, ((a : ℕ) < j ↔ (b : ℕ) < j) → (a ∈ S ↔ b ∈ S)) :
    dS τ S (fibClass j : RP Ψ N) = 0 := by
  unfold fibClass
  refine d_prod_zero _ _ _ (fun σ _ => d_prod_zero _ _ _ (fun ab hab => ?_))
  have h := hS _ _ (Finset.mem_filter.mp hab).2.2
  rw [map_sub, dS_X, dS_X]
  simp only [h, sub_self]

/- English proof (translation)
Rewrite using `[map_sum, Finset.sum_eq_single τ]`. Rewrite using `[map_sum]`. Simplify using `only [dS_X, true_and]`. Rewrite using `[Finset.sum_boole, map_natCast]`. Introduce `σ _ hσ`.

Rewrite using `[map_sum]`. Simplify using `[dS_X, hσ]`. Simplify using the standard rewrite rules.
-/
theorem d_sum (τ : Ψ) (S T : Finset (Fin N)) :
    dS τ S (∑ σ : Ψ, ∑ i ∈ T, (X (σ, i) : RP Ψ N)) = C (((T.filter (· ∈ S)).card : ℕ) : ℝ) := by
  rw [map_sum, Finset.sum_eq_single τ]
  · rw [map_sum]
    simp only [dS_X, true_and]
    rw [Finset.sum_boole, map_natCast]
  · intro σ _ hσ
    rw [map_sum]
    simp [dS_X, hσ]
  · simp

/- English proof (translation)
Rewrite using `[← dS_apply]`. Unfold `testPoly testDeg`. Rewrite using `[Derivation.leibniz, Derivation.leibniz_pow, hc, d_fib τ j S hS, ← degFl_C_mul]`. Use `congr 1`. Simplify using `only [smul_zero, zero_add, smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel, map_mul, map_add, map_one, map_natCast]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deg_d_test (τ : Ψ) (j : ℕ) (S : Finset (Fin N)) (c : ℝ)
    (hS : ∀ a b : Fin N, ((a : ℕ) < j ↔ (b : ℕ) < j) → (a ∈ S ↔ b ∈ S))
    (hc : dS τ S (muSmall j : RP Ψ N) = C c) :
    degFl (∑ i ∈ S, pderiv (τ, i) (testPoly j : RP Ψ N)) = ((dimX Ψ N j : ℝ) + 1) * c * testDeg Ψ N j := by
  rw [← dS_apply]
  unfold testPoly testDeg
  rw [Derivation.leibniz, Derivation.leibniz_pow, hc, d_fib τ j S hS, ← degFl_C_mul]
  congr 1
  simp only [smul_zero, zero_add, smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel, map_mul, map_add, map_one,
    map_natCast]
  push_cast
  ring

/- English proof (translation)
Unfold `muSmall`. Use `split_ifs`. Conclude with `IsHomogeneous.sum _ _ _ (fun _ _ => IsHomogeneous.sum _ _ _ (fun _ _ => isHomogeneous_X ℝ _))`. Use `IsHomogeneous.neg (IsHomogeneous.sum _ _ _ (fun _ _ => IsHomogeneous.sum _ _ _ (fun _ _ => ?_)))` and prove the remaining obligations. Rewrite using `[pow_one]`.

Conclude with `isHomogeneous_X ℝ _`.
-/
theorem mu_homog' (j : ℕ) : (muSmall j : RP Ψ N).IsHomogeneous 1 := by
  unfold muSmall
  split_ifs
  · exact IsHomogeneous.sum _ _ _ (fun _ _ => IsHomogeneous.sum _ _ _ (fun _ _ => isHomogeneous_X ℝ _))
  · refine IsHomogeneous.neg (IsHomogeneous.sum _ _ _ (fun _ _ => IsHomogeneous.sum _ _ _ (fun _ _ => ?_)))
    rw [pow_one]; exact isHomogeneous_X ℝ _

/- English proof (translation)
Unfold `testPoly`. Rewrite using `[fib_eq']`. Establish `h` using `((mu_homog' (Ψ := Ψ) (N := N) j).pow (dimX Ψ N j + 1)).mul ((isHomogeneous_C _ ((-1 : ℝ) ^ (idxS Ψ N j).card)).mul (fib_homog (Ψ := Ψ) (N := N) j))`. Establish `hD : dimFl Ψ N = dimX Ψ N j + (idxS Ψ N j).card` using `dim_split j hj`. Establish `e : 1 * (dimX Ψ N j + 1) + (0 + (idxS Ψ N j).card) = dimFl Ψ N + 1` using `by omega`.

Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem test_homog (j : ℕ) (hj : j ≤ N) : (testPoly j : RP Ψ N).IsHomogeneous (dimFl Ψ N + 1) := by
  unfold testPoly
  rw [fib_eq']
  have h := ((mu_homog' (Ψ := Ψ) (N := N) j).pow (dimX Ψ N j + 1)).mul
    ((isHomogeneous_C _ ((-1 : ℝ) ^ (idxS Ψ N j).card)).mul (fib_homog (Ψ := Ψ) (N := N) j))
  have hD : dimFl Ψ N = dimX Ψ N j + (idxS Ψ N j).card := dim_split j hj
  have e : 1 * (dimX Ψ N j + 1) + (0 + (idxS Ψ N j).card) = dimFl Ψ N + 1 := by omega
  rwa [e] at h

end RootFieldNumerics.TF

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
open RootFieldNumerics.TF Formalism.L2.Geo.BlockVandermondeForms in
/- English proof (translation)
Introduce `Ψ _ _ N j _ hjN`. Establish `hlow : ∀ a b : Fin N, ((a : ℕ) < j ↔ (b : ℕ) < j) → (a ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j) ↔ b ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j))`. Introduce `a b h`. Simplify using `using h`. Establish `hall : ∀ a b : Fin N, ((a : ℕ) < j ↔ (b : ℕ) < j) → (a ∈ (Finset.univ : Finset (Fin N)) ↔ b ∈ (Finset.univ : Finset (Fin N)))`.

Introduce `a b _`. Simplify using the standard rewrite rules. Establish `c1 : (Finset.univ.filter (fun i : Fin N => (i : ℕ) < j)).card = j` using `card_top N j hjN.le`. Establish `c2 : (Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ))).card = N - j` using `card_smallBlock N j`. Use `⟨test_homog j hjN.le, testDeg_pos j hjN.le, fun h τ => ⟨?_, ?_⟩, fun h τ => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Unfold `Sh`. Rewrite using `[deg_d_test τ j _ 0 hlow]`. Expand and normalize the polynomial expressions, which then agree. Unfold `muSmall`. Rewrite using `[if_pos h, d_sum, Finset.filter_false_of_mem]`.

Simplify using the standard rewrite rules. Introduce `x hx`. Simplify using `using hx`. Unfold `Tot`. Rewrite using `[deg_d_test τ j _ ((N - j : ℕ) : ℝ) hall]`.

Unfold `muSmall`. Rewrite using `[if_pos h, d_sum, Finset.filter_true_of_mem (fun _ _ => Finset.mem_univ _), c2]`. Unfold `Sh`. Rewrite using `[deg_d_test τ j _ (-(j : ℝ)) hlow]`. Expand and normalize the polynomial expressions, which then agree.

Unfold `muSmall pkLow`. Simplify using `only [pow_one]`. Rewrite using `[if_neg h, map_neg, d_sum, Finset.filter_true_of_mem (fun _ hx => hx), c1, map_neg]`. Unfold `Tot`. Rewrite using `[deg_d_test τ j _ (-(j : ℝ)) hall]`.

Expand and normalize the polynomial expressions, which then agree. Unfold `muSmall pkLow`. Simplify using `only [pow_one]`. Rewrite using `[if_neg h, map_neg, d_sum, Finset.filter_true_of_mem (fun _ _ => Finset.mem_univ _), c1, map_neg]`.
-/
theorem RootFieldNumerics.test_polynomial_shift_values : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ), 1 ≤ j → j < N → (testPoly j : RP Ψ N).IsHomogeneous (dimFl Ψ N + 1) ∧ 0 < testDeg Ψ N j ∧ (N - j ≤ j → ∀ τ : Ψ, Sh j τ (testPoly j : RP Ψ N) = 0 ∧ Tot τ (testPoly j : RP Ψ N) = ((dimX Ψ N j : ℝ) + 1) * ((N - j : ℕ) : ℝ) * testDeg Ψ N j) ∧ (¬ N - j ≤ j → ∀ τ : Ψ, Sh j τ (testPoly j : RP Ψ N) = -(((dimX Ψ N j : ℝ) + 1) * j * testDeg Ψ N j) ∧ Tot τ (testPoly j : RP Ψ N) = -(((dimX Ψ N j : ℝ) + 1) * j * testDeg Ψ N j)) := by
  intro Ψ _ _ N j _ hjN
  have hlow : ∀ a b : Fin N, ((a : ℕ) < j ↔ (b : ℕ) < j) →
      (a ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j) ↔
        b ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j)) := by
    intro a b h; simpa using h
  have hall : ∀ a b : Fin N, ((a : ℕ) < j ↔ (b : ℕ) < j) →
      (a ∈ (Finset.univ : Finset (Fin N)) ↔ b ∈ (Finset.univ : Finset (Fin N))) := by
    intro a b _; simp
  have c1 : (Finset.univ.filter (fun i : Fin N => (i : ℕ) < j)).card = j := card_top N j hjN.le
  have c2 : (Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ))).card = N - j := card_smallBlock N j
  refine ⟨test_homog j hjN.le, testDeg_pos j hjN.le, fun h τ => ⟨?_, ?_⟩, fun h τ => ⟨?_, ?_⟩⟩
  · unfold Sh
    rw [deg_d_test τ j _ 0 hlow]
    · ring
    · unfold muSmall
      rw [if_pos h, d_sum, Finset.filter_false_of_mem]
      · simp
      · intro x hx; simpa using hx
  · unfold Tot
    rw [deg_d_test τ j _ ((N - j : ℕ) : ℝ) hall]
    unfold muSmall
    rw [if_pos h, d_sum, Finset.filter_true_of_mem (fun _ _ => Finset.mem_univ _), c2]
  · unfold Sh
    rw [deg_d_test τ j _ (-(j : ℝ)) hlow]
    · ring
    · unfold muSmall pkLow
      simp only [pow_one]
      rw [if_neg h, map_neg, d_sum, Finset.filter_true_of_mem (fun _ hx => hx), c1, map_neg]
  · unfold Tot
    rw [deg_d_test τ j _ (-(j : ℝ)) hall]
    · ring
    · unfold muSmall pkLow
      simp only [pow_one]
      rw [if_neg h, map_neg, d_sum, Finset.filter_true_of_mem (fun _ _ => Finset.mem_univ _), c1, map_neg]
