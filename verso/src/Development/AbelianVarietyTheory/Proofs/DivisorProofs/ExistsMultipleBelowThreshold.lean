import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CoefBound

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `h` using `CartierDiv.mult_add (0 : CartierDiv X) 0 z`. Rewrite `h` using `[add_zero]`. Rewrite using `[zero_nsmul]`.

Use `push_cast`. Use linear arithmetic over natural numbers and integers. Consider the case `succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cartierDivisor_mult_nsmul_eq_natCast_mul {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (D : CartierDiv X)
    (n : ℕ) (z : X) : (n • D).mult z = n * D.mult z := by
  induction n with
  | zero =>
    have h := CartierDiv.mult_add (0 : CartierDiv X) 0 z
    rw [add_zero] at h
    rw [zero_nsmul]; push_cast; omega
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

/- English proof (translation)
Introduce `Y _ _ _ R Fd m r a hr hR`. Establish `hfin` using `Fd.finite_support_mult`. Use `set S : ℕ := ∑ z ∈ hfin.toFinset, ((m : ℤ) * Fd.mult z).toNat with hS`. Use `⟨a + 1 + S, by omega, fun z => ?_⟩` and prove the remaining obligations. Establish `hF : (m : ℤ) * Fd.mult z < ((a + 1 + S : ℕ) : ℤ)`.

Distinguish the cases in `hz : Fd.mult z = 0`. Rewrite using `[hz]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Establish `hmem : z ∈ hfin.toFinset` using `by simpa using hz`.

Establish `h1 : ((m : ℤ) * Fd.mult z).toNat ≤ S` using `Finset.single_le_sum (f := fun z => ((m : ℤ) * Fd.mult z).toNat) (fun _ _ => Nat.zero_le _) hmem`. Establish `h2 : (m : ℤ) * Fd.mult z ≤ (((m : ℤ) * Fd.mult z).toNat : ℤ)` using `Int.self_le_toNat _`. Establish `h3 : ((((m : ℤ) * Fd.mult z).toNat : ℕ) : ℤ) ≤ (S : ℤ)` using `by exact_mod_cast h1`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[CartierDiv.mult_add, cartierDivisor_mult_nsmul_eq_natCast_mul, cartierDivisor_mult_nsmul_eq_natCast_mul]`. Use `set b : ℕ := a + 1 + S`. Establish `hRz : R.mult z ≤ (m : ℤ) - 1` using `by have := hR z; omega`. Establish `hrb : (0 : ℤ) ≤ ((r * b : ℕ) : ℤ)` using `by positivity`. Establish `key : ((r * b : ℕ) : ℤ) * R.mult z ≤ ((r * b : ℕ) : ℤ) * ((m : ℤ) - 1)` using `mul_le_mul_of_nonneg_left hRz hrb`.

Establish `hb : ((b : ℕ) : ℤ) ≤ ((r * b : ℕ) : ℤ)`. Establish `: b ≤ r * b` using `Nat.le_mul_of_pos_left b hr`. Conclude with `this` after adjusting the coercions. Establish `e : (((m * r * b : ℕ)) : ℤ) = ((r * b : ℕ) : ℤ) * (m : ℤ)` using `by push_cast; ring`. Rewrite using `[e]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem coef_lt_of_large : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y] (R Fd : CartierDiv Y) (m r a : ℕ), 0 < r → (∀ z, R.mult z < m) → ∃ b : ℕ, a ≤ b ∧ ∀ z, ((r * b) • R + m • Fd).mult z < (m * r * b : ℕ) := by
  intro Y _ _ _ R Fd m r a hr hR
  classical
  have hfin := Fd.finite_support_mult
  set S : ℕ := ∑ z ∈ hfin.toFinset, ((m : ℤ) * Fd.mult z).toNat with hS
  refine ⟨a + 1 + S, by omega, fun z => ?_⟩
  have hF : (m : ℤ) * Fd.mult z < ((a + 1 + S : ℕ) : ℤ) := by
    by_cases hz : Fd.mult z = 0
    · rw [hz]; push_cast; omega
    · have hmem : z ∈ hfin.toFinset := by simpa using hz
      have h1 : ((m : ℤ) * Fd.mult z).toNat ≤ S :=
        Finset.single_le_sum (f := fun z => ((m : ℤ) * Fd.mult z).toNat) (fun _ _ => Nat.zero_le _) hmem
      have h2 : (m : ℤ) * Fd.mult z ≤ (((m : ℤ) * Fd.mult z).toNat : ℤ) := Int.self_le_toNat _
      have h3 : ((((m : ℤ) * Fd.mult z).toNat : ℕ) : ℤ) ≤ (S : ℤ) := by exact_mod_cast h1
      push_cast; omega
  rw [CartierDiv.mult_add, cartierDivisor_mult_nsmul_eq_natCast_mul, cartierDivisor_mult_nsmul_eq_natCast_mul]
  set b : ℕ := a + 1 + S
  have hRz : R.mult z ≤ (m : ℤ) - 1 := by have := hR z; omega
  have hrb : (0 : ℤ) ≤ ((r * b : ℕ) : ℤ) := by positivity
  have key : ((r * b : ℕ) : ℤ) * R.mult z ≤ ((r * b : ℕ) : ℤ) * ((m : ℤ) - 1) :=
    mul_le_mul_of_nonneg_left hRz hrb
  have hb : ((b : ℕ) : ℤ) ≤ ((r * b : ℕ) : ℤ) := by
    have : b ≤ r * b := Nat.le_mul_of_pos_left b hr
    exact_mod_cast this
  have e : (((m * r * b : ℕ)) : ℤ) = ((r * b : ℕ) : ℤ) * (m : ℤ) := by push_cast; ring
  rw [e]
  nlinarith

end GlobalTheory.CoefBound
