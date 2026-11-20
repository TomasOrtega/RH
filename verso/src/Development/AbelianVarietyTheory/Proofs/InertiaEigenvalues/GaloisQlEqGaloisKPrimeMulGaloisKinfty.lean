import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowRamifiedUniformizerFieldZpowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMinpolyCoeffZeroPowOfPowEqNegStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeAdjoinCompatibleRootsOfFiniteKummerTowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankMulMinpolyNatDegreeLeOfPowEqNegStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisDecompOfDisjointStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.NgalDecomp

/- English proof (translation)
Introduce `l _ a e _ _ ϖ hea g`. Establish `hl` using `(Fact.out : l.Prime)`. Establish `hdvd : e ∣ l ^ a - 1` using `⟨1, by omega⟩`. Establish `hG` using `PiSys.isGalois_field a ϖ hdvd`. Establish `hK : FiniteDimensional ℚ_[l] (ϖ.field a).1` using `(ϖ.field a).2`.

Establish `hcop : Nat.Coprime l e`. Use `(Nat.Prime.coprime_iff_not_dvd hl).2 fun h => ?_` and prove the remaining obligations. Establish `h2 : l ∣ l ^ a` using `dvd_pow_self l (NeZero.ne a)`. Rewrite `h2` using `[← hea]`. Conclude with `hl.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h2))`.

Establish `hbot : (ϖ.field a).1 ⊓ ϖ.Kinf = ⊥` using `by set F := (ϖ.field a).1 ⊓ ϖ.Kinf with hF haveI : FiniteDimensional ℚ_[l] F := FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : F ≤ (ϖ.field a).1)).toLinearMap (IntermediateField.inclusion (inf_le_left : F ≤ (ϖ.field a).1)).toRingHom.injective`. Take `⟨n, hn⟩` from `GlobalTheory.T.le_adjoin_compatibleRoots_of_finite_kummerTower l e ϖ F inferInstance inf_le_right`. Establish `hN : 0 < l ^ n` using `pow_pos hl.pos n`. Establish `hx : (ϖ.seq n ^ e) ^ (l ^ n) = -(l : Om l)` using `by rw [← pow_mul, mul_comm]; exact ϖ.seq_pow_mul n`. Establish `hx0 : ϖ.seq n ^ e ≠ 0` using `pow_ne_zero _ (ϖ.seq_ne_zero n)`.

Establish `hint : IsIntegral F (ϖ.seq n ^ e)` using `(Algebra.IsIntegral.isIntegral (R := ℚ_[l]) (ϖ.seq n ^ e)).tower_top`. Establish `hc0 : (minpoly F (ϖ.seq n ^ e)).coeff 0 ≠ 0` using `minpoly.coeff_zero_ne_zero hint hx0`. Establish `hcF : (((minpoly F (ϖ.seq n ^ e)).coeff 0 : F) : Om l) ∈ F` using `((minpoly F (ϖ.seq n ^ e)).coeff 0).2`. Establish `hc : (((minpoly F (ϖ.seq n ^ e)).coeff 0 : F) : Om l) ≠ 0`. Simplify using `using hc0`.

Take `⟨j, hj⟩` from `GlobalTheory.T.norm_pow_ramifiedUniformizerField_zpow l a e ϖ _ (IntermediateField.mem_inf.1 hcF).1 hc`. Establish `h2` using `GlobalTheory.T.norm_minpoly_coeff_zero_pow_of_pow_eq_neg_prime l F (l ^ n) (ϖ.seq n ^ e) hN hx`. Establish `h4` using `GlobalTheory.T.finrank_mul_natDegree_minpoly_le_of_pow_eq_neg l F (l ^ n) (ϖ.seq n ^ e) hN hx hn`. Establish `hm : 0 < (minpoly F (ϖ.seq n ^ e)).natDegree` using `minpoly.natDegree_pos hint`. Use `set m := (minpoly F (ϖ.seq n ^ e)).natDegree with hmdef`.

Use `set c : Om l := (((minpoly F (ϖ.seq n ^ e)).coeff 0 : F) : Om l) with hcdef`. Establish `hl0 : (0 : ℝ) < l` using `by exact_mod_cast hl.pos`. Establish `hl1 : (l : ℝ) ≠ 1` using `by exact_mod_cast hl.one_lt.ne'`. Establish `key : (l : ℝ) ^ (j * ((l ^ n : ℕ) : ℤ)) = (l : ℝ) ^ (-((m * e : ℕ) : ℤ))`. Establish `e1 : ‖c‖ ^ (e * l ^ n) = ((l : ℝ) ^ j) ^ (l ^ n)` using `by rw [pow_mul, hj]`.

Establish `e2 : ‖c‖ ^ (e * l ^ n) = (((l : ℝ)⁻¹) ^ m) ^ e` using `by rw [mul_comm, pow_mul, h2]`. Rewrite using `[_root_.zpow_mul, zpow_natCast, ← e1, e2, _root_.zpow_neg, zpow_natCast, ← pow_mul, inv_pow]`. Establish `key2 : j * ((l ^ n : ℕ) : ℤ) = -((m * e : ℕ) : ℤ)` using `zpow_right_injective₀ hl0 hl1 key`. Establish `hdv : l ^ n ∣ m * e`. Establish `: ((l ^ n : ℕ) : ℤ) ∣ ((m * e : ℕ) : ℤ)` using `⟨-j, by linarith⟩`.

Conclude with `Int.natCast_dvd_natCast.1 this`. Establish `hdm : l ^ n ∣ m` using `(Nat.Coprime.pow_left n hcop).dvd_of_dvd_mul_right hdv`. Establish `hle : l ^ n ≤ m` using `Nat.le_of_dvd hm hdm`. Establish `hfr : Module.finrank ℚ_[l] F = 1`. Establish `hpos : 0 < Module.finrank ℚ_[l] F` using `Module.finrank_pos`.

Assume the negation of the conclusion as `hne`. Establish `: 2 * m ≤ Module.finrank ℚ_[l] F * m` using `Nat.mul_le_mul_right _ (by omega)`. Use linear arithmetic over natural numbers and integers. Conclude with `IntermediateField.finrank_eq_one_iff.1 hfr`. Conclude with `GlobalTheory.T.exists_mul_fixingSubgroup_of_inf_eq_bot l (ϖ.field a).1 ϖ.Kinf hK hG hbot g`.
-/
theorem galQ_eq_GK_mul_GKinf : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e), e + 1 = l ^ a → ∀ g : GQ l, ∃ h ∈ GK (ϖ.field a), ∃ k ∈ ϖ.GKinf, g = h * k := by
  intro l _ a e _ _ ϖ hea g
  have hl := (Fact.out : l.Prime)
  have hdvd : e ∣ l ^ a - 1 := ⟨1, by omega⟩
  have hG := PiSys.isGalois_field a ϖ hdvd
  have hK : FiniteDimensional ℚ_[l] (ϖ.field a).1 := (ϖ.field a).2
  have hcop : Nat.Coprime l e := by
    refine (Nat.Prime.coprime_iff_not_dvd hl).2 fun h => ?_
    have h2 : l ∣ l ^ a := dvd_pow_self l (NeZero.ne a)
    rw [← hea] at h2
    exact hl.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h2))
  have hbot : (ϖ.field a).1 ⊓ ϖ.Kinf = ⊥ := by
    set F := (ϖ.field a).1 ⊓ ϖ.Kinf with hF
    haveI : FiniteDimensional ℚ_[l] F := FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : F ≤ (ϖ.field a).1)).toLinearMap (IntermediateField.inclusion (inf_le_left : F ≤ (ϖ.field a).1)).toRingHom.injective
    obtain ⟨n, hn⟩ := GlobalTheory.T.le_adjoin_compatibleRoots_of_finite_kummerTower l e ϖ F inferInstance inf_le_right
    have hN : 0 < l ^ n := pow_pos hl.pos n
    have hx : (ϖ.seq n ^ e) ^ (l ^ n) = -(l : Om l) := by rw [← pow_mul, mul_comm]; exact ϖ.seq_pow_mul n
    have hx0 : ϖ.seq n ^ e ≠ 0 := pow_ne_zero _ (ϖ.seq_ne_zero n)
    have hint : IsIntegral F (ϖ.seq n ^ e) := (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) (ϖ.seq n ^ e)).tower_top
    have hc0 : (minpoly F (ϖ.seq n ^ e)).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx0
    have hcF : (((minpoly F (ϖ.seq n ^ e)).coeff 0 : F) : Om l) ∈ F := ((minpoly F (ϖ.seq n ^ e)).coeff 0).2
    have hc : (((minpoly F (ϖ.seq n ^ e)).coeff 0 : F) : Om l) ≠ 0 := by
      simpa using hc0
    obtain ⟨j, hj⟩ := GlobalTheory.T.norm_pow_ramifiedUniformizerField_zpow l a e ϖ _ (IntermediateField.mem_inf.1 hcF).1 hc
    have h2 := GlobalTheory.T.norm_minpoly_coeff_zero_pow_of_pow_eq_neg_prime l F (l ^ n) (ϖ.seq n ^ e) hN hx
    have h4 := GlobalTheory.T.finrank_mul_natDegree_minpoly_le_of_pow_eq_neg l F (l ^ n) (ϖ.seq n ^ e) hN hx hn
    have hm : 0 < (minpoly F (ϖ.seq n ^ e)).natDegree := minpoly.natDegree_pos hint
    set m := (minpoly F (ϖ.seq n ^ e)).natDegree with hmdef
    set c : Om l := (((minpoly F (ϖ.seq n ^ e)).coeff 0 : F) : Om l) with hcdef
    have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.pos
    have hl1 : (l : ℝ) ≠ 1 := by exact_mod_cast hl.one_lt.ne'
    have key : (l : ℝ) ^ (j * ((l ^ n : ℕ) : ℤ)) = (l : ℝ) ^ (-((m * e : ℕ) : ℤ)) := by
      have e1 : ‖c‖ ^ (e * l ^ n) = ((l : ℝ) ^ j) ^ (l ^ n) := by rw [pow_mul, hj]
      have e2 : ‖c‖ ^ (e * l ^ n) = (((l : ℝ)⁻¹) ^ m) ^ e := by rw [mul_comm, pow_mul, h2]
      rw [_root_.zpow_mul, zpow_natCast, ← e1, e2, _root_.zpow_neg, zpow_natCast, ← pow_mul, inv_pow]
    have key2 : j * ((l ^ n : ℕ) : ℤ) = -((m * e : ℕ) : ℤ) := zpow_right_injective₀ hl0 hl1 key
    have hdv : l ^ n ∣ m * e := by
      have : ((l ^ n : ℕ) : ℤ) ∣ ((m * e : ℕ) : ℤ) := ⟨-j, by linarith⟩
      exact Int.natCast_dvd_natCast.1 this
    have hdm : l ^ n ∣ m := (Nat.Coprime.pow_left n hcop).dvd_of_dvd_mul_right hdv
    have hle : l ^ n ≤ m := Nat.le_of_dvd hm hdm
    have hfr : Module.finrank ℚ_[l] F = 1 := by
      have hpos : 0 < Module.finrank ℚ_[l] F := Module.finrank_pos
      by_contra hne
      have : 2 * m ≤ Module.finrank ℚ_[l] F * m := Nat.mul_le_mul_right _ (by omega)
      omega
    exact IntermediateField.finrank_eq_one_iff.1 hfr
  exact GlobalTheory.T.exists_mul_fixingSubgroup_of_inf_eq_bot l (ϖ.field a).1 ϖ.Kinf hK hG hbot g

end GlobalTheory.NgalDecomp
