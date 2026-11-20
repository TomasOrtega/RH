import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.Geo

open MvPolynomial in

/- English proof (translation)
Distinguish the cases in `htop : I = ⊤`. Conclude with `⟨1, 0, one_pos, by simp [htop]⟩`. Use `haveI : Nontrivial (MvPolynomial σ K ⧸ I) := Ideal.Quotient.nontrivial_iff.2 htop`. Use `set B := Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)) with hB`. Use `haveI : Algebra.IsIntegral B (MvPolynomial σ K ⧸ I) := Algebra.IsIntegral.of_finite _ _`.

Take `⟨p, hp, hroot⟩` from `Algebra.IsIntegral.isIntegral (R := B) (Ideal.Quotient.mk I a)`. Establish `hq : (p * Polynomial.X).Monic` using `hp.mul Polynomial.monic_X`. Establish `hroot' : Polynomial.eval₂ (algebraMap B (MvPolynomial σ K ⧸ I)) (Ideal.Quotient.mk I a) (p * Polynomial.X) = 0`. Rewrite using `[Polynomial.eval₂_mul, hroot, zero_mul]`. Establish `hdeg : 0 < (p * Polynomial.X).natDegree`.

Rewrite using `[hp.natDegree_mul Polynomial.monic_X, Polynomial.natDegree_X]`. Use linear arithmetic over natural numbers and integers. Generalize the expression as in `p * Polynomial.X = q at hq hroot' hdeg`. Establish `hlift : ∀ l, ∃ c : MvPolynomial (Fin m) K, Ideal.Quotient.mk I (aeval y c) = ((q.coeff l : B) : MvPolynomial σ K ⧸ I)`. Introduce `l`.

Establish `hmem : ((q.coeff l : B) : MvPolynomial σ K ⧸ I) ∈ (aeval (fun k => Ideal.Quotient.mk I (y k)) : MvPolynomial (Fin m) K →ₐ[K] MvPolynomial σ K ⧸ I).range`. Rewrite using `[← Algebra.adjoin_range_eq_range_aeval]`. Conclude with `(q.coeff l).2`. Take `⟨c, hc⟩` from `hmem`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hc]`. Use `MvPolynomial.comp_aeval_apply (R := K) (B := MvPolynomial σ K ⧸ I) y (Ideal.Quotient.mkₐ K I) c` as an intermediate fact. Simplify using `using this`. Use `choose C hC using hlift`. Use `⟨q.natDegree, C, hdeg, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← hroot', Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, map_add, map_sum, add_comm]`. Use `congr 1`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hC, map_pow]`. Both sides reduce to the same expression.

Simplify using `[hq.coeff_natDegree]`.
-/
theorem exists_monic_relation {K σ : Type} [Field K] {m : ℕ} (I : Ideal (MvPolynomial σ K))
    (y : Fin m → MvPolynomial σ K)
    (hfin : Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial σ K ⧸ I))
    (a : MvPolynomial σ K) :
    ∃ (s : ℕ) (C : ℕ → MvPolynomial (Fin m) K), 0 < s ∧
      a ^ s + ∑ l ∈ Finset.range s, aeval y (C l) * a ^ l ∈ I := by
  by_cases htop : I = ⊤
  · exact ⟨1, 0, one_pos, by simp [htop]⟩
  haveI : Nontrivial (MvPolynomial σ K ⧸ I) := Ideal.Quotient.nontrivial_iff.2 htop
  set B := Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)) with hB
  haveI : Algebra.IsIntegral B (MvPolynomial σ K ⧸ I) := Algebra.IsIntegral.of_finite _ _
  obtain ⟨p, hp, hroot⟩ := Algebra.IsIntegral.isIntegral (R := B) (Ideal.Quotient.mk I a)
  have hq : (p * Polynomial.X).Monic := hp.mul Polynomial.monic_X
  have hroot' : Polynomial.eval₂ (algebraMap B (MvPolynomial σ K ⧸ I)) (Ideal.Quotient.mk I a)
      (p * Polynomial.X) = 0 := by
    rw [Polynomial.eval₂_mul, hroot, zero_mul]
  have hdeg : 0 < (p * Polynomial.X).natDegree := by
    rw [hp.natDegree_mul Polynomial.monic_X, Polynomial.natDegree_X]
    omega
  generalize p * Polynomial.X = q at hq hroot' hdeg
  have hlift : ∀ l, ∃ c : MvPolynomial (Fin m) K,
      Ideal.Quotient.mk I (aeval y c) = ((q.coeff l : B) : MvPolynomial σ K ⧸ I) := by
    intro l
    have hmem : ((q.coeff l : B) : MvPolynomial σ K ⧸ I) ∈
        (aeval (fun k => Ideal.Quotient.mk I (y k)) :
          MvPolynomial (Fin m) K →ₐ[K] MvPolynomial σ K ⧸ I).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact (q.coeff l).2
    obtain ⟨c, hc⟩ := hmem
    refine ⟨c, ?_⟩
    rw [← hc]
    have := MvPolynomial.comp_aeval_apply (R := K) (B := MvPolynomial σ K ⧸ I) y
      (Ideal.Quotient.mkₐ K I) c
    simpa using this
  choose C hC using hlift
  refine ⟨q.natDegree, C, hdeg, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← hroot', Polynomial.eval₂_eq_sum_range,
    Finset.sum_range_succ, map_add, map_sum, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, hC, map_pow]
    rfl
  · simp [hq.coeff_natDegree]

open MvPolynomial in

/- English proof (translation)
Establish `key : ∀ r', homogeneousComponent (e * r + t) (aeval y (homogeneousComponent r' C) * b) = if r' = r then aeval y (homogeneousComponent r C) * b else 0`. Introduce `r'`. Establish `h : (aeval y (homogeneousComponent r' C) * b).IsHomogeneous (e * r' + t)` using `((homogeneousComponent_isHomogeneous r' C).aeval y hy).mul hb`. Rewrite using `[homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 h)]`. Distinguish the cases in `hr : r' = r`.

Substitute `hr` using the available equality. Simplify using the standard rewrite rules. Establish `hne : e * r' + t ≠ e * r + t` using `fun h' => hr (Nat.eq_of_mul_eq_mul_left he (Nat.add_right_cancel h'))`. Rewrite using `[if_neg hne.symm, if_neg hr]`. Use `conv_lhs => rw [← sum_homogeneousComponent C]`.

Rewrite using `[map_sum, Finset.sum_mul, map_sum]`. Repeatedly rewrite using `[key]`. Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs with hmem`. Both sides reduce to the same expression.

Rewrite using `[homogeneousComponent_eq_zero _ _ (by simpa [Nat.lt_succ_iff] using hmem)]`. Simplify using the standard rewrite rules.
-/
theorem homogeneousComponent_aeval_mul {K σ : Type} [Field K] {m e : ℕ} (he : 0 < e)
    (y : Fin m → MvPolynomial σ K) (hy : ∀ k, (y k).IsHomogeneous e)
    (C : MvPolynomial (Fin m) K) (r t : ℕ) (b : MvPolynomial σ K) (hb : b.IsHomogeneous t) :
    homogeneousComponent (e * r + t) (aeval y C * b) = aeval y (homogeneousComponent r C) * b := by
  have key : ∀ r', homogeneousComponent (e * r + t) (aeval y (homogeneousComponent r' C) * b) =
      if r' = r then aeval y (homogeneousComponent r C) * b else 0 := by
    intro r'
    have h : (aeval y (homogeneousComponent r' C) * b).IsHomogeneous (e * r' + t) :=
      ((homogeneousComponent_isHomogeneous r' C).aeval y hy).mul hb
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 h)]
    by_cases hr : r' = r
    · subst hr
      simp
    · have hne : e * r' + t ≠ e * r + t := fun h' =>
        hr (Nat.eq_of_mul_eq_mul_left he (Nat.add_right_cancel h'))
      rw [if_neg hne.symm, if_neg hr]
  conv_lhs => rw [← sum_homogeneousComponent C]
  rw [map_sum, Finset.sum_mul, map_sum]
  simp_rw [key]
  rw [Finset.sum_ite_eq']
  split_ifs with hmem
  · rfl
  · rw [homogeneousComponent_eq_zero _ _ (by simpa [Nat.lt_succ_iff] using hmem)]
    simp

open MvPolynomial in

/- English proof (translation)
Take `⟨s, C, hs, hmem⟩` from `exists_monic_relation I y hfin a`. Use `⟨s, fun l => homogeneousComponent ((s - l) * w) (C l), hs, fun l => homogeneousComponent_isHomogeneous _ _, ?_⟩` and prove the remaining obligations. Establish `hcomp` using `hI _ hmem (e * w * s)`. Rewrite `hcomp` using `[map_add, map_sum]`. Use `hcomp using 2` and compare the differences between its conclusion and the goal.

Establish `h` using `ha.pow s`. Rewrite using `[homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 h)]`. Simplify using the standard rewrite rules. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Establish `hl' : l ≤ s` using `(Finset.mem_range.1 hl).le`.

Establish `hdeg : e * w * s = e * ((s - l) * w) + e * w * l`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hl'`. Simplify using `only [Nat.add_sub_cancel_left]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hdeg, homogeneousComponent_aeval_mul he y hy (C l) _ _ _ (ha.pow l)]`.
-/
theorem exists_hom_relation {K σ : Type} [Field K] {m : ℕ} (I : Ideal (MvPolynomial σ K))
    (hI : ∀ f ∈ I, ∀ n : ℕ, homogeneousComponent n f ∈ I) (e : ℕ) (he : 0 < e)
    (y : Fin m → MvPolynomial σ K) (hy : ∀ k, (y k).IsHomogeneous e)
    (hfin : Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial σ K ⧸ I))
    (w : ℕ) (a : MvPolynomial σ K) (ha : a.IsHomogeneous (e * w)) :
    ∃ (s : ℕ) (c : ℕ → MvPolynomial (Fin m) K), 0 < s ∧ (∀ l, (c l).IsHomogeneous ((s - l) * w)) ∧
      a ^ s + ∑ l ∈ Finset.range s, aeval y (c l) * a ^ l ∈ I := by
  obtain ⟨s, C, hs, hmem⟩ := exists_monic_relation I y hfin a
  refine ⟨s, fun l => homogeneousComponent ((s - l) * w) (C l), hs,
    fun l => homogeneousComponent_isHomogeneous _ _, ?_⟩
  have hcomp := hI _ hmem (e * w * s)
  rw [map_add, map_sum] at hcomp
  convert hcomp using 2
  · have h := ha.pow s
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 h)]
    simp
  · refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l ≤ s := (Finset.mem_range.1 hl).le
    have hdeg : e * w * s = e * ((s - l) * w) + e * w * l := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hl'
      simp only [Nat.add_sub_cancel_left]
      ring
    rw [hdeg, homogeneousComponent_aeval_mul he y hy (C l) _ _ _ (ha.pow l)]

end GlobalTheory.CompanionTheory.Geo
