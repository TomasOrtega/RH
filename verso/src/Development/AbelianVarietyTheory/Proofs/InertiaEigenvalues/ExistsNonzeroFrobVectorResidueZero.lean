import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisPlusSeriesWithThetaResiduesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesLinearIndependentOfFirstTerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSortedNormalizedOrthBasisComplexPAdicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOrthogonalFamilyResidueZerosStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisPlusFrobeniusStableSubringInFilZero
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMonII

open GlobalTheory.PSer

/- English proof (translation)
Establish `hn0 : (n : ZMod l) ≠ 0` using `by rwa [Ne, ZMod.natCast_eq_zero_iff]`. Use `set m := ((n : ZMod l)⁻¹).val with hm`. Establish `hmnZ : ((m * n : ℕ) : ZMod l) = ((1 : ℕ) : ZMod l)`. Use `push_cast`. Rewrite using `[hm, ZMod.natCast_zmod_val, inv_mul_cancel₀ hn0]`.

Establish `hmn : ((m * n : ℕ) : Formalism.Per.Fl l) = 1`. Rewrite using `[← Nat.cast_one, CharP.natCast_eq_natCast (Formalism.Per.Fl l) l]`. Conclude with `(ZMod.natCast_eq_natCast_iff _ _ _).1 hmnZ`. Establish `hy : y = (m : Formalism.Per.Fl l) * (n • y)`. Rewrite using `[nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul, hmn, one_mul]`.

Establish `hmul : ∀ a b : Formalism.Per.Fl l, sh (a * b) = sh a * sh b`. Introduce `a b`. Simplify using `[sh, map_mul]`. Establish `hle : ∀ x : Formalism.Per.Fl l, ‖sh x‖ ≤ 1` using `fun x => (GlobalTheory.RingBasics.mem_OC _).1 (PreTilt.untilt x).2`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hmul, norm_mul]`. Use `_ ≤ 1 * ‖sh (n • y)‖ := mul_le_mul_of_nonneg_right (hle _) (norm_nonneg _)`. Use `_ = ‖sh (n • y)‖ := one_mul _`.
-/
theorem sh_le_sh_nsmul {l : ℕ} [Fact l.Prime] (y : Formalism.Per.Fl l) (n : ℕ) (hn : ¬ l ∣ n) :
    ‖sh y‖ ≤ ‖sh (n • y)‖ := by
  have hn0 : (n : ZMod l) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  set m := ((n : ZMod l)⁻¹).val with hm
  have hmnZ : ((m * n : ℕ) : ZMod l) = ((1 : ℕ) : ZMod l) := by
    push_cast
    rw [hm, ZMod.natCast_zmod_val, inv_mul_cancel₀ hn0]
  have hmn : ((m * n : ℕ) : Formalism.Per.Fl l) = 1 := by
    rw [← Nat.cast_one, CharP.natCast_eq_natCast (Formalism.Per.Fl l) l]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hmnZ
  have hy : y = (m : Formalism.Per.Fl l) * (n • y) := by
    rw [nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul, hmn, one_mul]
  have hmul : ∀ a b : Formalism.Per.Fl l, sh (a * b) = sh a * sh b := by
    intro a b; simp [sh, map_mul]
  have hle : ∀ x : Formalism.Per.Fl l, ‖sh x‖ ≤ 1 := fun x => (GlobalTheory.RingBasics.mem_OC _).1 (PreTilt.untilt x).2
  calc ‖sh y‖ = ‖sh (m : Formalism.Per.Fl l)‖ * ‖sh (n • y)‖ := by
        conv_lhs => rw [hy]
        rw [hmul, norm_mul]
    _ ≤ 1 * ‖sh (n • y)‖ := mul_le_mul_of_nonneg_right (hle _) (norm_nonneg _)
    _ = ‖sh (n • y)‖ := one_mul _

/- English proof (translation)
Rewrite using `[ev, ← AlgHom.coe_pow, AlgHom.commutes, AlgHom.commutes]`.
-/
theorem ev_algebraMap {l : ℕ} [Fact l.Prime] (P : LocPrime l) (m : ℕ) (q : ℚ_[l]) :
    ev P m (algebraMap ℚ_[l] P.R.B q) = algebraMap ℚ_[l] P.R.BdR q := by
  rw [ev, ← AlgHom.coe_pow, AlgHom.commutes, AlgHom.commutes]

end GlobalTheory.PMonII

namespace GlobalTheory.PMonII

open GlobalTheory.PSer

/- English proof (translation)
Introduce `l _ P AI T h hh lam hlam hind`. Take `⟨S, θ, hS, hker, hQ, hser⟩` from `GlobalTheory.T.exists_BcrisPlus_series_with_theta_residues l P AI T`. Take `⟨-, hPev, hPring, hPq, -, -⟩` from `GlobalTheory.PMon.CrisPlus.plus_props l P AI T`. Establish `hθq : ∀ (c : ℚ_[l]) (hm : algebraMap ℚ_[l] P.R.BdR c ∈ S), θ ⟨_, hm⟩ = algebraMap ℚ_[l] ℂ_[l] c`. Introduce `c hm`.

Take `⟨_, h'⟩` from `hQ c`. Conclude with `h'`. Establish `hqS : ∀ c : ℚ_[l], algebraMap ℚ_[l] P.R.BdR c ∈ S` using `fun c => (hS _).2 (q_mem_Fil P c)`. Establish `hlS : ∀ j, lam j ∈ S` using `fun j => (hS _).2 (hlam j)`. Set `μ : Fin h → ℂ_[l]` to `fun j => θ ⟨lam j, hlS j⟩`.

Establish `hμind : ∀ c : Fin h → ℚ_[l], ∑ j, algebraMap ℚ_[l] ℂ_[l] (c j) * μ j = 0 → c = 0`. Introduce `c hc`. Apply `hind c` to reduce the goal to its premises. Establish `hm : ∑ j, c j • lam j ∈ S` using `S.sum_mem fun j _ => by`. Rewrite using `[Algebra.smul_def]`.

Conclude with `S.mul_mem (hqS _) (hlS j)`. Establish `he : (⟨_, hm⟩ : S) = ∑ j, (⟨_, hqS (c j)⟩ : S) * ⟨lam j, hlS j⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[Algebra.smul_def]`. Establish `h0 : θ ⟨_, hm⟩ = 0`.

Rewrite using `[he, map_sum, ← hc]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hθq]`. Conclude with `(hker ⟨_, hm⟩).1 h0`. Take `⟨Pm, μ', hdet, hμ', hnorm, hanti, hlt, horth⟩` from `GlobalTheory.T.exists_sorted_normalized_orthBasis_complexPAdic l h μ hμind`.

Take `⟨y, j0, r, R, hr0, hr1, hR1, hyR, hyr, hy0, hzero⟩` from `GlobalTheory.T.exists_orthogonal_family_residue_zeros l h μ' hh hnorm hanti hlt horth`. Establish `hb : ∀ k : Fin h, ∃ b : P.R.B, Plus T b ∧ P.φB^[h] b = (l : P.R.B) * b ∧ ∀ j : ℕ, ∃ hm, θ ⟨ev P j b, hm⟩ = abelian₂ h j (y k)` using `fun k => hser h R (y k) hh hR1 (hyR k)`. Use `choose b hbP hbφ hbθ using hb`. Use `choose hbm hθb using hbθ`. Establish `hbne : b j0 ≠ 0`.

Introduce `h0`. Establish `hc` using `GlobalTheory.T.untiltFrobeniusSeries_linearIndependent_of_firstTerms l h 1 r (fun _ => y j0) hh hr0 hr1 (fun _ k => hyr k) ?_ (fun _ => 1) ?_`. Conclude with `one_ne_zero (congrFun hc 0)`. Introduce `n hn a`. Assume the negation of the conclusion as `hd`.

Establish `ha : a = 0` using `Subsingleton.elim _ _`. Substitute `ha` using the available equality. Establish `hle` using `sh_le_sh_nsmul (y j0 0) (n 0) hd`. Simplify using `only [Finset.univ_unique, Finset.sum_singleton] at hn`. Establish `: (default : Fin 1) = 0` using `rfl`.

Rewrite `hn` using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `j _`. Establish `e : (⟨ev P j (b j0), hbm j0 j⟩ : S) = 0` using `Subtype.ext (by`. Simplify using `only [h0, ZeroMemClass.coe_zero, ← evHom_apply, map_zero])`.

Establish `hL : abelian₂ h j (y j0) = 0` using `by rw [← hθb j0 j, e, map_zero]`. Simplify using `[hL]`. Set `a : Fin h → P.R.B` to `fun j => ∑ k, algebraMap ℚ_[l] P.R.B (Pm k j) * b k`. Establish `hplus0 : Plus T (0 : P.R.B)` using `by simpa using hPq 0`. Establish `hev : ∀ (i : ℕ) (j : Fin h), ev P i (a j) = ∑ k, algebraMap ℚ_[l] P.R.BdR (Pm k j) * ev P i (b k)`.

Introduce `i j`. Simplify using `only [a, ← evHom_apply, map_sum, map_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[evHom_apply, evHom_apply, ev_algebraMap]`. Use `⟨a, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `ha`. Apply `hbne` to reduce the goal to its premises. Establish `hinv : Pm * Pm⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet)`. Establish `key : ∑ j, algebraMap ℚ_[l] P.R.B (Pm⁻¹ j j0) * a j = b j0`. Simplify using `only [a, Finset.mul_sum, ← mul_assoc, ← map_mul]`.

Rewrite using `[Finset.sum_comm]`. Establish `: ∀ k, ∑ j, algebraMap ℚ_[l] P.R.B (Pm⁻¹ j j0 * Pm k j) * b k = algebraMap ℚ_[l] P.R.B ((Pm * Pm⁻¹) k j0) * b k`. Introduce `k`. Rewrite using `[← Finset.sum_mul, ← map_sum, Matrix.mul_apply]`. Simplify using `only [mul_comm]`.

Simplify using `only [this, hinv, Matrix.one_apply]`. Simplify using the standard rewrite rules. Rewrite using `[← key]`. Simplify using `[ha]`. Introduce `j`.

Use `Finset.sum_induction _ (Plus T) (fun x y hx hy => (hPring x y hx hy).1) hplus0 fun k _ => ?_` and prove the remaining obligations. Conclude with `(hPring _ _ (hPq _) (hbP k)).2`. Introduce `j`. Simplify using `only [a]`. Rewrite using `[← AlgHom.coe_pow, map_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, AlgHom.commutes, AlgHom.coe_pow, hbφ k]`. Expand and normalize the polynomial expressions, which then agree. Introduce `i`. Establish `hX : ∑ j, lam j * ev P i (a j) ∈ S` using `S.sum_mem fun j _ => S.mul_mem (hlS j) (by`.

Rewrite using `[hev]`. Conclude with `S.sum_mem fun k _ => S.mul_mem (hqS _) (hbm k i))`. Apply `(hker ⟨_, hX⟩).1` to reduce the goal to its premises. Establish `he : (⟨_, hX⟩ : S) = ∑ j, ∑ k, (⟨lam j, hlS j⟩ : S) * ((⟨_, hqS (Pm k j)⟩ : S) * ⟨_, hbm k i⟩)`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [hev, Finset.mul_sum]`. Simplify using the standard rewrite rules. Rewrite using `[he]`. Simplify using `only [map_sum, map_mul, hθq, hθb]`. Rewrite using `[Finset.sum_comm]`.

Rewrite using `[← hzero i]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hμ' k, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [μ]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exII : ExII := by
  intro l _ P AI T h hh lam hlam hind
  obtain ⟨S, θ, hS, hker, hQ, hser⟩ := GlobalTheory.T.exists_BcrisPlus_series_with_theta_residues l P AI T
  obtain ⟨-, hPev, hPring, hPq, -, -⟩ := GlobalTheory.PMon.CrisPlus.plus_props l P AI T
  have hθq : ∀ (c : ℚ_[l]) (hm : algebraMap ℚ_[l] P.R.BdR c ∈ S),
      θ ⟨_, hm⟩ = algebraMap ℚ_[l] ℂ_[l] c := by
    intro c hm; obtain ⟨_, h'⟩ := hQ c; exact h'
  have hqS : ∀ c : ℚ_[l], algebraMap ℚ_[l] P.R.BdR c ∈ S := fun c => (hS _).2 (q_mem_Fil P c)
  have hlS : ∀ j, lam j ∈ S := fun j => (hS _).2 (hlam j)
  let μ : Fin h → ℂ_[l] := fun j => θ ⟨lam j, hlS j⟩
  have hμind : ∀ c : Fin h → ℚ_[l], ∑ j, algebraMap ℚ_[l] ℂ_[l] (c j) * μ j = 0 → c = 0 := by
    intro c hc
    apply hind c
    have hm : ∑ j, c j • lam j ∈ S := S.sum_mem fun j _ => by
      rw [Algebra.smul_def]; exact S.mul_mem (hqS _) (hlS j)
    have he : (⟨_, hm⟩ : S) = ∑ j, (⟨_, hqS (c j)⟩ : S) * ⟨lam j, hlS j⟩ := by
      apply Subtype.ext; simp [Algebra.smul_def]
    have h0 : θ ⟨_, hm⟩ = 0 := by
      rw [he, map_sum, ← hc]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, hθq]
    exact (hker ⟨_, hm⟩).1 h0
  obtain ⟨Pm, μ', hdet, hμ', hnorm, hanti, hlt, horth⟩ := GlobalTheory.T.exists_sorted_normalized_orthBasis_complexPAdic l h μ hμind
  obtain ⟨y, j0, r, R, hr0, hr1, hR1, hyR, hyr, hy0, hzero⟩ :=
    GlobalTheory.T.exists_orthogonal_family_residue_zeros l h μ' hh hnorm hanti hlt horth
  have hb : ∀ k : Fin h, ∃ b : P.R.B, Plus T b ∧ P.φB^[h] b = (l : P.R.B) * b ∧
      ∀ j : ℕ, ∃ hm, θ ⟨ev P j b, hm⟩ = abelian₂ h j (y k) :=
    fun k => hser h R (y k) hh hR1 (hyR k)
  choose b hbP hbφ hbθ using hb
  choose hbm hθb using hbθ

  have hbne : b j0 ≠ 0 := by
    intro h0
    have hc := GlobalTheory.T.untiltFrobeniusSeries_linearIndependent_of_firstTerms l h 1 r (fun _ => y j0) hh hr0 hr1 (fun _ k => hyr k) ?_ (fun _ => 1) ?_
    · exact one_ne_zero (congrFun hc 0)
    · intro n hn a
      by_contra hd
      have ha : a = 0 := Subsingleton.elim _ _
      subst ha
      have hle := sh_le_sh_nsmul (y j0 0) (n 0) hd
      simp only [Finset.univ_unique, Finset.sum_singleton] at hn
      have : (default : Fin 1) = 0 := rfl
      rw [this] at hn
      linarith
    · intro j _
      have e : (⟨ev P j (b j0), hbm j0 j⟩ : S) = 0 := Subtype.ext (by
        simp only [h0, ZeroMemClass.coe_zero, ← evHom_apply, map_zero])
      have hL : abelian₂ h j (y j0) = 0 := by rw [← hθb j0 j, e, map_zero]
      simp [hL]
  let a : Fin h → P.R.B := fun j => ∑ k, algebraMap ℚ_[l] P.R.B (Pm k j) * b k
  have hplus0 : Plus T (0 : P.R.B) := by simpa using hPq 0
  have hev : ∀ (i : ℕ) (j : Fin h), ev P i (a j) = ∑ k, algebraMap ℚ_[l] P.R.BdR (Pm k j) * ev P i (b k) := by
    intro i j
    simp only [a, ← evHom_apply, map_sum, map_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [evHom_apply, evHom_apply, ev_algebraMap]
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  ·
    intro ha
    apply hbne
    have hinv : Pm * Pm⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet)
    have key : ∑ j, algebraMap ℚ_[l] P.R.B (Pm⁻¹ j j0) * a j = b j0 := by
      simp only [a, Finset.mul_sum, ← mul_assoc, ← map_mul]
      rw [Finset.sum_comm]
      have : ∀ k, ∑ j, algebraMap ℚ_[l] P.R.B (Pm⁻¹ j j0 * Pm k j) * b k =
          algebraMap ℚ_[l] P.R.B ((Pm * Pm⁻¹) k j0) * b k := by
        intro k
        rw [← Finset.sum_mul, ← map_sum, Matrix.mul_apply]
        simp only [mul_comm]
      simp only [this, hinv, Matrix.one_apply]
      simp
    rw [← key]
    simp [ha]
  · intro j
    refine Finset.sum_induction _ (Plus T) (fun x y hx hy => (hPring x y hx hy).1) hplus0 fun k _ => ?_
    exact (hPring _ _ (hPq _) (hbP k)).2
  · intro j
    simp only [a]
    rw [← AlgHom.coe_pow, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, AlgHom.commutes, AlgHom.coe_pow, hbφ k]
    ring
  · intro i
    have hX : ∑ j, lam j * ev P i (a j) ∈ S := S.sum_mem fun j _ => S.mul_mem (hlS j) (by
      rw [hev]; exact S.sum_mem fun k _ => S.mul_mem (hqS _) (hbm k i))
    apply (hker ⟨_, hX⟩).1
    have he : (⟨_, hX⟩ : S) = ∑ j, ∑ k, (⟨lam j, hlS j⟩ : S) * ((⟨_, hqS (Pm k j)⟩ : S) * ⟨_, hbm k i⟩) := by
      apply Subtype.ext
      simp only [hev, Finset.mul_sum]
      simp
    rw [he]
    simp only [map_sum, map_mul, hθq, hθb]
    rw [Finset.sum_comm]
    rw [← hzero i]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hμ' k, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [μ]
    ring

end GlobalTheory.PMonII
