import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.IntertwiningIsomorphisms.IsoIffIntertwiningHolds
import Formalism.LocalToGlobal.NormalizedHeckeFactors.PendTie
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelCharpoly.GaloisClause
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RegularIffNatDegreeAndExistsEllipticGLStatement

open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace ReciprocityTheory.Ty.Fin.GreenAll

section

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

open GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.CuspLabel in
/- English proof (translation)
Establish `hcard : Nat.card K = Fintype.card K` using `Nat.card_eq_fintype_card`. Establish `h` using `isCuspChar_character τ hs hc`. Take `⟨k, hreg, hchar⟩` from `GlobalTheory.CuspFormula.exists_regular K C.ι C.ι_inj d hd τ.character (GlobalTheory.CuspGL.isIrrChar_of_norm_one _ h.1) (GlobalTheory.CuspGL.isPrimitive_of_isCuspChar _ h)`. Establish `hq : 1 < Fintype.card K` using `Fintype.one_lt_card`. Establish `hqd : 1 < Fintype.card K ^ d` using `Nat.one_lt_pow (by omega) hq`.

Establish `hg1 : C.gen d ^ (Fintype.card K ^ d - 1) = 1` using `by rw [← C.gen_order d hd, pow_orderOf_eq_one]`. Establish `hfin : IsOfFinOrder (C.gen d)` using `isOfFinOrder_iff_pow_eq_one.2 ⟨_, by omega, hg1⟩`. Take `⟨x₀, hkx⟩ : ∃ x₀, C.gen d ^ k = x₀` from `⟨_, rfl⟩`. Establish `hx1 : x₀ ^ (Fintype.card K ^ d - 1) = 1` using `by rw [← hkx, ← pow_mul, mul_comm, pow_mul, hg1, one_pow]`. Establish `hx0 : x₀ ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hx1` using `[zero_pow (by omega)]`. Conclude with `zero_ne_one hx1`. Establish `hint : IsIntegral K x₀` using `Algebra.IsIntegral.isIntegral x₀`. Establish `hdeg : (minpoly K x₀).natDegree = d`.

Use `((GlobalTheory.T.regular_iff_natDegree_and_exists_elliptic_GL K d hd x₀ (by show x₀ ^ (Nat.card K ^ d - 1) = 1` and prove the remaining obligations. Rewrite using `[hcard]`. Conclude with `hx1)).1).1 fun e he hed hh => hreg e he hed ?_`. Rewrite `hh` using `[← hkx, ← pow_mul, hfin.pow_eq_pow_iff_modEq, C.gen_order d hd]`. Rewrite `hh`, the goal using `[hcard]`.

Conclude with `hh`. Establish `hmon` using `minpoly.monic hint`. Establish `hirr` using `minpoly.irreducible hint`. Establish `hx₀ : aeval x₀ (minpoly K x₀) = 0` using `minpoly.aeval K x₀`. Establish `hX : minpoly K x₀ ≠ X` using `fun hh => hx0 (by simpa [hh] using hx₀)`.

Establish `hroot : ∀ w : AlgebraicClosure K, aeval w (minpoly K x₀) = 0 → w ^ (Fintype.card K ^ d - 1) = 1` using `fun w hw => by rw [← hdeg]; exact root_pow_eq_one hmon hirr hX hw`. Establish `hminP : ∀ w : AlgebraicClosure K, aeval w (minpoly K x₀) = 0 → minpoly K w = minpoly K x₀` using `fun w hw => (minpoly.eq_of_irreducible_of_monic hirr hw hmon).symm`. Establish `hadd` using `(GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow K C.ι k).1`. Use `⟨minpoly K x₀, hmon, hirr, hX, by simpa using hdeg, ?_⟩` and prove the remaining obligations. Introduce `x hx γ hγ z hz m hm`.

Simplify using `only [Fintype.card_fin] at hm ⊢`. Establish `hQ : minpoly K z = Matrix.charpoly (γ : Matrix (Fin d) (Fin d) K)` using `(minpoly.eq_of_irreducible_of_monic hγ hz (Matrix.charpoly_monic _)).symm`. Establish `hQd : (minpoly K z).natDegree = d`. Rewrite using `[hQ, Matrix.charpoly_natDegree_eq_dim]`. Simplify using the standard rewrite rules.

Establish `hz1 : z ^ (Fintype.card K ^ d - 1) = 1`. Rewrite using `[← hm, ← pow_mul, mul_comm, pow_mul, hg1, one_pow]`. Establish `hval` using `GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible K (Fin d → K) _ hadd (Matrix.toLin' (γ : Matrix (Fin d) (Fin d) K)) (by rw [Matrix.charpoly_toLin']; exact hγ)`. Rewrite `hval` using `[Matrix.charpoly_toLin']`. Use `show τ.character γ = _`.

Rewrite using `[hchar, hval, ← hQ, rootSum_minpoly C.ι hd hz1 hQd k]`. Use `congr 1`. Establish `hxd : (minpoly K x).natDegree = d` using `by rw [hminP x hx, hdeg]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← map_pow, ← map_pow, ← hm, ← hkx]`. Use `congr 1`. Simplify using `only [← pow_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = GlobalTheory.CuspGL.rootSum C.ι m (minpoly K x₀) := (rootSum_minpoly C.ι hd hx1 hdeg m).symm`. Use `_ = GlobalTheory.CuspGL.rootSum C.ι m (minpoly K x) := by rw [hminP x hx]`. Use `_ = ∑ i ∈ Finset.range d, C.ι (x ^ Fintype.card K ^ i) ^ m := rootSum_minpoly C.ι hd (hroot x hx) hxd m`. Use `_ = ∑ i ∈ Finset.range d, C.ι x ^ (m * Fintype.card K ^ i) := by`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_pow, ← pow_mul, mul_comm (Fintype.card K ^ i) m]`.
-/
theorem exists_label (C : LabelConv K) {d : ℕ} (hd : 1 ≤ d) (τ : FDRep ℂ (GL (Fin d) K)) (hs : Simple τ)
    (hc : IsCuspidal K τ) : ∃ P, HasCuspLabel C τ P := by
  have hcard : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
  have h := isCuspChar_character τ hs hc
  obtain ⟨k, hreg, hchar⟩ := GlobalTheory.CuspFormula.exists_regular K C.ι C.ι_inj d hd τ.character
    (GlobalTheory.CuspGL.isIrrChar_of_norm_one _ h.1) (GlobalTheory.CuspGL.isPrimitive_of_isCuspChar _ h)
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hqd : 1 < Fintype.card K ^ d := Nat.one_lt_pow (by omega) hq
  have hg1 : C.gen d ^ (Fintype.card K ^ d - 1) = 1 := by rw [← C.gen_order d hd, pow_orderOf_eq_one]
  have hfin : IsOfFinOrder (C.gen d) := isOfFinOrder_iff_pow_eq_one.2 ⟨_, by omega, hg1⟩
  obtain ⟨x₀, hkx⟩ : ∃ x₀, C.gen d ^ k = x₀ := ⟨_, rfl⟩
  have hx1 : x₀ ^ (Fintype.card K ^ d - 1) = 1 := by rw [← hkx, ← pow_mul, mul_comm, pow_mul, hg1, one_pow]
  have hx0 : x₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hx1
    exact zero_ne_one hx1
  have hint : IsIntegral K x₀ := Algebra.IsIntegral.isIntegral x₀
  have hdeg : (minpoly K x₀).natDegree = d := by
    refine ((GlobalTheory.T.regular_iff_natDegree_and_exists_elliptic_GL K d hd x₀ (by
      show x₀ ^ (Nat.card K ^ d - 1) = 1
      rw [hcard]; exact hx1)).1).1 fun e he hed hh => hreg e he hed ?_
    rw [← hkx, ← pow_mul, hfin.pow_eq_pow_iff_modEq, C.gen_order d hd] at hh
    rw [hcard] at hh ⊢
    exact hh
  have hmon := minpoly.monic hint
  have hirr := minpoly.irreducible hint
  have hx₀ : aeval x₀ (minpoly K x₀) = 0 := minpoly.aeval K x₀
  have hX : minpoly K x₀ ≠ X := fun hh => hx0 (by simpa [hh] using hx₀)
  have hroot : ∀ w : AlgebraicClosure K, aeval w (minpoly K x₀) = 0 → w ^ (Fintype.card K ^ d - 1) = 1 :=
    fun w hw => by rw [← hdeg]; exact root_pow_eq_one hmon hirr hX hw
  have hminP : ∀ w : AlgebraicClosure K, aeval w (minpoly K x₀) = 0 → minpoly K w = minpoly K x₀ := fun w hw =>
    (minpoly.eq_of_irreducible_of_monic hirr hw hmon).symm
  have hadd := (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow K C.ι k).1
  refine ⟨minpoly K x₀, hmon, hirr, hX, by simpa using hdeg, ?_⟩
  intro x hx γ hγ z hz m hm
  simp only [Fintype.card_fin] at hm ⊢
  have hQ : minpoly K z = Matrix.charpoly (γ : Matrix (Fin d) (Fin d) K) :=
    (minpoly.eq_of_irreducible_of_monic hγ hz (Matrix.charpoly_monic _)).symm
  have hQd : (minpoly K z).natDegree = d := by
    rw [hQ, Matrix.charpoly_natDegree_eq_dim]; simp
  have hz1 : z ^ (Fintype.card K ^ d - 1) = 1 := by
    rw [← hm, ← pow_mul, mul_comm, pow_mul, hg1, one_pow]
  have hval := GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible K (Fin d → K) _ hadd
    (Matrix.toLin' (γ : Matrix (Fin d) (Fin d) K)) (by rw [Matrix.charpoly_toLin']; exact hγ)
  rw [Matrix.charpoly_toLin'] at hval
  show τ.character γ = _
  rw [hchar, hval, ← hQ, rootSum_minpoly C.ι hd hz1 hQd k]
  congr 1
  have hxd : (minpoly K x).natDegree = d := by rw [hminP x hx, hdeg]
  calc ∑ i ∈ Finset.range d, C.ι (z ^ Fintype.card K ^ i) ^ k
      = ∑ i ∈ Finset.range d, C.ι (x₀ ^ Fintype.card K ^ i) ^ m := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← map_pow, ← map_pow, ← hm, ← hkx]
        congr 1
        simp only [← pow_mul]
        congr 1
        ring
    _ = GlobalTheory.CuspGL.rootSum C.ι m (minpoly K x₀) := (rootSum_minpoly C.ι hd hx1 hdeg m).symm
    _ = GlobalTheory.CuspGL.rootSum C.ι m (minpoly K x) := by rw [hminP x hx]
    _ = ∑ i ∈ Finset.range d, C.ι (x ^ Fintype.card K ^ i) ^ m := rootSum_minpoly C.ι hd (hroot x hx) hxd m
    _ = ∑ i ∈ Finset.range d, C.ι x ^ (m * Fintype.card K ^ i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_pow, ← pow_mul, mul_comm (Fintype.card K ^ i) m]

open GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.CuspLabel in
/- English proof (translation)
Establish `hq : 1 < Fintype.card K` using `Fintype.one_lt_card`. Establish `hqd : 1 < Fintype.card K ^ d` using `Nat.one_lt_pow (by omega) hq`. Establish `hdeg : P.natDegree = d` using `by simpa using h.2.2.2.1`. Take `⟨x, hx⟩` from `IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) P (degree_pos_of_irreducible h.2.1).ne'`. Establish `hprim : IsPrimitiveRoot (C.gen d) (Fintype.card K ^ d - 1)`.

Rewrite using `[← C.gen_order d hd]`. Conclude with `IsPrimitiveRoot.orderOf _`. Use `haveI : NeZero (Fintype.card K ^ d - 1) := ⟨by omega⟩`. Establish `heq : τ.character = τ'.character`. Use `GlobalTheory.CuspGL.cuspElliptic_statement K d _ _ (isCuspChar_character τ hs hc) (isCuspChar_character τ' hs' hc') fun γ hγ => ?_` and prove the remaining obligations.

Take `⟨z, hz⟩` from `IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) _ (degree_pos_of_irreducible hγ).ne'`. Establish `hX : Matrix.charpoly (γ : Matrix (Fin d) (Fin d) K) ≠ X`. Introduce `hh`. Establish `h0` using `Matrix.det_eq_sign_charpoly_coeff (γ : Matrix (Fin d) (Fin d) K)`. Rewrite `h0` using `[hh, coeff_X_zero, mul_zero]`.

Conclude with `(Matrix.GeneralLinearGroup.det γ).ne_zero h0`. Establish `hz1` using `root_pow_eq_one (Matrix.charpoly_monic _) hγ hX hz`. Rewrite `hz1` using `[Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Take `⟨m, -, hm⟩` from `hprim.eq_pow_of_pow_eq_one hz1`. Establish `hm' : C.gen (Fintype.card (Fin d)) ^ m = z` using `by rw [Fintype.card_fin]; exact hm`.

Conclude with `(h.2.2.2.2 x hx γ hγ z hz m hm').trans (h'.2.2.2.2 x hx γ hγ z hz m hm').symm`. Assume the negation of the conclusion as `hn`. Establish `h1` using `zIdemOrthogonal_holds _ τ τ' hs hs' hn`. Establish `hz : zIdem τ = zIdem τ'`. Establish `hd1 : (Module.finrank ℂ τ : ℂ) = Module.finrank ℂ τ'`.

Rewrite using `[← FDRep.char_one, ← FDRep.char_one, heq]`. Unfold `zIdem`. Use `Finset.sum_congr rfl fun γ _ => ?_` and prove the remaining obligations. Rewrite using `[hd1]`. Conclude with `congrArg _ (congrArg _ (congrFun heq γ⁻¹))`.

Rewrite `h1` using `[← hz, (zIdemIdemCentral_holds _ τ hs).1]`. Establish `h2` using `GlobalTheory.T.central_idempotent_properties.2.2.1 _ τ τ hs hs ⟨Iso.refl _⟩`. Rewrite `h2` using `[h1, map_zero]`. Use `haveI : Nontrivial τ := (isIrr_of_simple τ).1`. Conclude with `zero_ne_one h2`.
-/
theorem iso_of_label (C : LabelConv K) {d : ℕ} (hd : 1 ≤ d) (τ τ' : FDRep ℂ (GL (Fin d) K)) (P : K[X])
    (hs : Simple τ) (hc : IsCuspidal K τ) (hs' : Simple τ') (hc' : IsCuspidal K τ')
    (h : HasCuspLabel C τ P) (h' : HasCuspLabel C τ' P) : Nonempty (τ ≅ τ') := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hqd : 1 < Fintype.card K ^ d := Nat.one_lt_pow (by omega) hq
  have hdeg : P.natDegree = d := by simpa using h.2.2.2.1
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) P (degree_pos_of_irreducible h.2.1).ne'
  have hprim : IsPrimitiveRoot (C.gen d) (Fintype.card K ^ d - 1) := by
    rw [← C.gen_order d hd]; exact IsPrimitiveRoot.orderOf _
  haveI : NeZero (Fintype.card K ^ d - 1) := ⟨by omega⟩
  have heq : τ.character = τ'.character := by
    refine GlobalTheory.CuspGL.cuspElliptic_statement K d _ _ (isCuspChar_character τ hs hc)
      (isCuspChar_character τ' hs' hc') fun γ hγ => ?_
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) _ (degree_pos_of_irreducible hγ).ne'
    have hX : Matrix.charpoly (γ : Matrix (Fin d) (Fin d) K) ≠ X := by
      intro hh
      have h0 := Matrix.det_eq_sign_charpoly_coeff (γ : Matrix (Fin d) (Fin d) K)
      rw [hh, coeff_X_zero, mul_zero] at h0
      exact (Matrix.GeneralLinearGroup.det γ).ne_zero h0
    have hz1 := root_pow_eq_one (Matrix.charpoly_monic _) hγ hX hz
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at hz1
    obtain ⟨m, -, hm⟩ := hprim.eq_pow_of_pow_eq_one hz1
    have hm' : C.gen (Fintype.card (Fin d)) ^ m = z := by rw [Fintype.card_fin]; exact hm
    exact (h.2.2.2.2 x hx γ hγ z hz m hm').trans (h'.2.2.2.2 x hx γ hγ z hz m hm').symm
  by_contra hn
  have h1 := zIdemOrthogonal_holds _ τ τ' hs hs' hn
  have hz : zIdem τ = zIdem τ' := by
    have hd1 : (Module.finrank ℂ τ : ℂ) = Module.finrank ℂ τ' := by
      rw [← FDRep.char_one, ← FDRep.char_one, heq]
    unfold zIdem
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [hd1]
    exact congrArg _ (congrArg _ (congrFun heq γ⁻¹))
  rw [← hz, (zIdemIdemCentral_holds _ τ hs).1] at h1
  have h2 := GlobalTheory.T.central_idempotent_properties.2.2.1 _ τ τ hs hs ⟨Iso.refl _⟩
  rw [h1, map_zero] at h2
  haveI : Nontrivial τ := (isIrr_of_simple τ).1
  exact zero_ne_one h2

/- English proof (translation)
Introduce `d hd` and use `⟨fun τ hs hc => ⟨(exists_label C hd τ hs hc).elim fun P hP => ⟨P, hP, fun Q hQ => GlobalTheory.T.cuspidal_label_unique K C _ τ Q P hQ hP⟩, GlobalTheory.CompanionTheory.TyFin.finrank_of_simple_cuspidal C.ι C.ι_inj hd τ hs hc⟩, GlobalTheory.T.exists_cuspidal_with_label K C d hd, fu …`.
-/
theorem cuspParam_all (C : LabelConv K) : CuspParam K C := fun d hd =>
  ⟨fun τ hs hc => ⟨(exists_label C hd τ hs hc).elim fun P hP =>
      ⟨P, hP, fun Q hQ => GlobalTheory.T.cuspidal_label_unique K C _ τ Q P hQ hP⟩,
      GlobalTheory.CompanionTheory.TyFin.finrank_of_simple_cuspidal C.ι C.ι_inj hd τ hs hc⟩,
    GlobalTheory.T.exists_cuspidal_with_label K C d hd, fun τ τ' P => iso_of_label C hd τ τ' P⟩

end

def greenLab {K : Type} [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) : LabelMap K C :=
  Formalism.L2.PT.greenO C (cuspParam_all C)

end ReciprocityTheory.Ty.Fin.GreenAll
