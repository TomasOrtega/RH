import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import GroundTheory.Brauer.Degree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCentralizerComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyEqOfSeparableCommutantCommStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.RegDeg

open Polynomial

/- English proof (translation)
Introduce `F C _ _ _ _ _ _ n hC c hsep hcomm`. Take `⟨k, hk0, hkC, ⟨e⟩⟩` from `GroundTheory.Brauer.exists_algEquiv_matrix_algebraicClosure F C`. Establish `hkn : k = n` using `Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (hkC.symm.trans hC)`. Substitute `hkn` using the available equality. Use `set K := AlgebraicClosure F`.

Use `set x : K ⊗[F] C := (1 : K) ⊗ₜ[F] c with hx`. Establish `hxi : IsIntegral K x` using `IsIntegral.of_finite K x`. Establish `hxr : x = Algebra.TensorProduct.includeRight c` using `rfl`. Establish `hdvd : minpoly K x ∣ (minpoly F c).map (algebraMap F K)`. Apply `minpoly.dvd` to reduce the goal to its premises.

Rewrite using `[aeval_map_algebraMap, hxr, aeval_algHom_apply, minpoly.aeval, map_zero]`. Establish `hge` using `GlobalTheory.CentSep.natDegree_minpoly_le_baseChange K c hxi`. Establish `hmap : (minpoly F c).map (algebraMap F K) ≠ 0` using `(Polynomial.map_ne_zero_iff (algebraMap F K).injective).mpr (minpoly.ne_zero (IsIntegral.of_finite F c))`. Establish `hle : (minpoly K x).natDegree ≤ (minpoly F c).natDegree`. Combine the equalities or inequalities in the displayed calculation.

Establish `hxsep : (minpoly K x).Separable` using `(hsep.map).of_dvd hdvd`. Set `S` to `Subalgebra.centralizer F ({c} : Set C)`. Use `letI : CommRing S := { (inferInstance : Ring S) with mul_comm := fun a b => Subtype.ext (by`. Establish `ha : Commute (a : C) c` using `((Subalgebra.mem_centralizer_iff F).mp a.2 c rfl).symm`. Establish `hb : Commute (b : C) c` using `((Subalgebra.mem_centralizer_iff F).mp b.2 c rfl).symm`.

Conclude with `(hcomm _ _ ha hb).eq) }`. Establish `hcent : ∀ y : C, y * c = c * y ↔ y ∈ Set.range (S.val)`. Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `⟨⟨y, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[Subalgebra.mem_centralizer_iff]`. Introduce `g hg`. Rewrite using `[Set.mem_singleton_iff.mp hg]`. Conclude with `h.symm`.

Introduce and unpack `⟨w, rfl⟩`. Conclude with `((Subalgebra.mem_centralizer_iff F).mp w.2 c rfl).symm`. Use `set N := e x with hN`. Establish `hmN : minpoly K N = minpoly K x` using `minpoly.algEquiv_eq e x`. Establish `hNcomm : ∀ A B : Matrix (Fin k) (Fin k) K, Commute A N → Commute B N → Commute A B`.

Introduce `A B hA hB`. Establish `hA' : e.symm A * x = x * e.symm A`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, e.apply_symm_apply]`. Conclude with `hA.eq`.

Establish `hB' : e.symm B * x = x * e.symm B`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, e.apply_symm_apply]`. Conclude with `hB.eq`. Establish `h` using `GlobalTheory.LKCentAf.commute_of_centralizer F K C S c S.val hcent _ _ hA' hB'`.

Establish `h2` using `congrArg e h`. Rewrite `h2` using `[map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply]`. Conclude with `h2`. Establish `hdegN` using `GlobalTheory.T.natDegree_minpoly_eq_of_separable_commutant_comm K k N (by rw [hmN]; exact hxsep) hNcomm`. Establish `hxk : (minpoly K x).natDegree = k` using `by rw [← hmN]; exact hdegN`.

Rewrite using `[← hxk]`. Conclude with `le_antisymm hge hle`.
-/
theorem natDegree_minpoly_eq : ∀ (F C : Type) [Field F] [Ring C] [Algebra F C] [Algebra.IsCentral F C]
    [IsSimpleRing C] [FiniteDimensional F C] (n : ℕ), Module.finrank F C = n ^ 2 → ∀ c : C,
    (minpoly F c).Separable → (∀ a b : C, Commute a c → Commute b c → Commute a b) →
    (minpoly F c).natDegree = n := by
  intro F C _ _ _ _ _ _ n hC c hsep hcomm
  obtain ⟨k, hk0, hkC, ⟨e⟩⟩ := GroundTheory.Brauer.exists_algEquiv_matrix_algebraicClosure F C
  have hkn : k = n := Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (hkC.symm.trans hC)
  subst hkn
  set K := AlgebraicClosure F
  set x : K ⊗[F] C := (1 : K) ⊗ₜ[F] c with hx
  have hxi : IsIntegral K x := IsIntegral.of_finite K x
  have hxr : x = Algebra.TensorProduct.includeRight c := rfl
  have hdvd : minpoly K x ∣ (minpoly F c).map (algebraMap F K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, hxr, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hge := GlobalTheory.CentSep.natDegree_minpoly_le_baseChange K c hxi
  have hmap : (minpoly F c).map (algebraMap F K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap F K).injective).mpr
      (minpoly.ne_zero (IsIntegral.of_finite F c))
  have hle : (minpoly K x).natDegree ≤ (minpoly F c).natDegree := by
    calc (minpoly K x).natDegree ≤ ((minpoly F c).map (algebraMap F K)).natDegree :=
          natDegree_le_of_dvd hdvd hmap
      _ = (minpoly F c).natDegree := natDegree_map _
  have hxsep : (minpoly K x).Separable := (hsep.map).of_dvd hdvd

  let S := Subalgebra.centralizer F ({c} : Set C)
  letI : CommRing S :=
    { (inferInstance : Ring S) with
      mul_comm := fun a b => Subtype.ext (by
        have ha : Commute (a : C) c := ((Subalgebra.mem_centralizer_iff F).mp a.2 c rfl).symm
        have hb : Commute (b : C) c := ((Subalgebra.mem_centralizer_iff F).mp b.2 c rfl).symm
        exact (hcomm _ _ ha hb).eq) }
  have hcent : ∀ y : C, y * c = c * y ↔ y ∈ Set.range (S.val) := by
    intro y
    constructor
    · intro h
      refine ⟨⟨y, ?_⟩, rfl⟩
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
      exact h.symm
    · rintro ⟨w, rfl⟩
      exact ((Subalgebra.mem_centralizer_iff F).mp w.2 c rfl).symm
  set N := e x with hN
  have hmN : minpoly K N = minpoly K x := minpoly.algEquiv_eq e x
  have hNcomm : ∀ A B : Matrix (Fin k) (Fin k) K, Commute A N → Commute B N → Commute A B := by
    intro A B hA hB
    have hA' : e.symm A * x = x * e.symm A := by
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hA.eq
    have hB' : e.symm B * x = x * e.symm B := by
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hB.eq
    have h := GlobalTheory.LKCentAf.commute_of_centralizer F K C S c S.val hcent _ _ hA' hB'
    have h2 := congrArg e h
    rw [map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply] at h2
    exact h2
  have hdegN := GlobalTheory.T.natDegree_minpoly_eq_of_separable_commutant_comm K k N (by rw [hmN]; exact hxsep) hNcomm
  have hxk : (minpoly K x).natDegree = k := by rw [← hmN]; exact hdegN
  rw [← hxk]
  exact le_antisymm hge hle

end GlobalTheory.RegDeg
