import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedDefs

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
The claim follows from `monic_prod_of_monic _ _ fun x _ => monic_X_sub_C x`.
-/
theorem rootPoly_monic' {E : Type} [Field E] (xs : Finset E) : (rootPoly xs).Monic :=
  monic_prod_of_monic _ _ fun x _ => monic_X_sub_C x

/- English proof (translation)
Unfold `rootPoly`. Rewrite using `[← Finset.prod_union (Finset.disjoint_sdiff_inter xs ys).symm, Finset.union_comm, Finset.sdiff_union_inter]`.
-/
theorem rootPoly_inter_mul_sdiff {E : Type} [Field E] (xs ys : Finset E) :
    rootPoly (xs ∩ ys) * rootPoly (xs \ ys) = rootPoly xs := by
  unfold rootPoly
  rw [← Finset.prod_union (Finset.disjoint_sdiff_inter xs ys).symm, Finset.union_comm,
    Finset.sdiff_union_inter]

/- English proof (translation)
Unfold `rootPoly`. Use `IsCoprime.prod_left fun x hx => IsCoprime.prod_right fun y hy => ?_` and prove the remaining obligations. Use `isCoprime_X_sub_C_of_isUnit_sub ?_` and prove the remaining obligations. Establish `hne : x ≠ y` using `fun e => Finset.disjoint_left.1 h hx (e ▸ hy)`. Conclude with `(sub_ne_zero.2 hne).isUnit`.
-/
theorem rootPoly_isCoprime_of_disjoint {E : Type} [Field E] (xs ys : Finset E) (h : Disjoint xs ys) :
    IsCoprime (rootPoly xs) (rootPoly ys) := by
  unfold rootPoly
  refine IsCoprime.prod_left fun x hx => IsCoprime.prod_right fun y hy => ?_
  refine isCoprime_X_sub_C_of_isUnit_sub ?_
  have hne : x ≠ y := fun e => Finset.disjoint_left.1 h hx (e ▸ hy)
  exact (sub_ne_zero.2 hne).isUnit

/- English proof (translation)
Establish `: P ∈ Polynomial.lifts k.subtype`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`. Conclude with `⟨⟨_, h n⟩, rfl⟩`. Conclude with `this`.
-/
theorem exists_poly_map_subfield {E : Type} [Field E] [DecidableEq E] (k : Subfield E) (P : E[X])
    (h : ∀ i, P.coeff i ∈ k) : ∃ p : (k)[X], p.map k.subtype = P := by
  have : P ∈ Polynomial.lifts k.subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, h n⟩, rfl⟩
  exact this

/- English proof (translation)
Take `⟨p, hp⟩` from `exists_poly_map_subfield k _ hx`. Take `⟨q, hq⟩` from `exists_poly_map_subfield k _ hy`. Use `set R := rootPoly (xs ∩ ys) with hR`. Use `set g0 := EuclideanDomain.gcd p q with hg0`. Use `set g := g0.map k.subtype with hg`.

Establish `hgP : g ∣ rootPoly xs`. Rewrite using `[← hp]`. Conclude with `Polynomial.map_dvd _ (EuclideanDomain.gcd_dvd_left p q)`. Establish `hgQ : g ∣ rootPoly ys`. Rewrite using `[← hq]`.

Conclude with `Polynomial.map_dvd _ (EuclideanDomain.gcd_dvd_right p q)`. Establish `hA` using `rootPoly_inter_mul_sdiff xs ys`. Establish `hB` using `rootPoly_inter_mul_sdiff ys xs`. Rewrite `hB` using `[Finset.inter_comm ys xs]`. Establish `hdisj : Disjoint (xs \ ys) (ys \ xs)`.

Rewrite using `[Finset.disjoint_left]`. Introduce `a ha hb`. Conclude with `(Finset.mem_sdiff.1 hb).2 (Finset.mem_sdiff.1 ha).1`. Take `⟨u, v, huv⟩` from `rootPoly_isCoprime_of_disjoint _ _ hdisj`. Establish `hgR : g ∣ R`.

Establish `: R = u * rootPoly xs + v * rootPoly ys`. Rewrite using `[← hA, ← hB]`. Take the linear combination `(-R) * huv`. Rewrite using `[this]`. Conclude with `dvd_add (hgP.mul_left _) (hgQ.mul_left _)`.

Establish `hRg : R ∣ g`. Establish `e : g = EuclideanDomain.gcd (rootPoly xs) (rootPoly ys)`. Rewrite using `[← hp, ← hq, Polynomial.gcd_map]`. Rewrite using `[e]`. Conclude with `EuclideanDomain.dvd_gcd ⟨_, hA.symm⟩ ⟨_, hB.symm⟩`.

Establish `hRm : R.Monic` using `rootPoly_monic' _`. Establish `hg0' : g ≠ 0` using `fun e => hRm.ne_zero (by simpa [e] using hgR)`. Establish `hg00 : g0 ≠ 0` using `fun e => hg0' (by rw [hg, e, Polynomial.map_zero])`. Establish `hmon : (g0 * C g0.leadingCoeff⁻¹).Monic` using `monic_mul_leadingCoeff_inv hg00`. Establish `hmon' : ((g0 * C g0.leadingCoeff⁻¹).map k.subtype).Monic` using `hmon.map _`.

Establish `hassoc : Associated ((g0 * C g0.leadingCoeff⁻¹).map k.subtype) R`. Establish `h1 : Associated g R` using `associated_of_dvd_dvd hgR hRg`. Use `Associated.trans ?_ h1` and prove the remaining obligations. Rewrite using `[Polynomial.map_mul, Polynomial.map_C]`. Use `(associated_mul_unit_left g _ ?_).symm.symm` and prove the remaining obligations.

Use `Polynomial.isUnit_C.2 (IsUnit.mk0 _ ?_)` and prove the remaining obligations. Simplify using `using hg00`. Establish `heq` using `eq_of_monic_of_associated hmon' hRm hassoc`. Introduce `i`. Rewrite using `[← heq, Polynomial.coeff_map]`.

Conclude with `(((g0 * C g0.leadingCoeff⁻¹).coeff i)).2`.
-/
theorem rootPoly_inter_mem {E : Type} [Field E] (k : Subfield E) (xs ys : Finset E)
    (hx : ∀ i, (rootPoly xs).coeff i ∈ k) (hy : ∀ i, (rootPoly ys).coeff i ∈ k) :
    ∀ i, (rootPoly (xs ∩ ys)).coeff i ∈ k := by
  obtain ⟨p, hp⟩ := exists_poly_map_subfield k _ hx
  obtain ⟨q, hq⟩ := exists_poly_map_subfield k _ hy
  set R := rootPoly (xs ∩ ys) with hR
  set g0 := EuclideanDomain.gcd p q with hg0
  set g := g0.map k.subtype with hg
  have hgP : g ∣ rootPoly xs := by
    rw [← hp]; exact Polynomial.map_dvd _ (EuclideanDomain.gcd_dvd_left p q)
  have hgQ : g ∣ rootPoly ys := by
    rw [← hq]; exact Polynomial.map_dvd _ (EuclideanDomain.gcd_dvd_right p q)
  have hA := rootPoly_inter_mul_sdiff xs ys
  have hB := rootPoly_inter_mul_sdiff ys xs
  rw [Finset.inter_comm ys xs] at hB
  have hdisj : Disjoint (xs \ ys) (ys \ xs) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.1 hb).2 (Finset.mem_sdiff.1 ha).1
  obtain ⟨u, v, huv⟩ := rootPoly_isCoprime_of_disjoint _ _ hdisj
  have hgR : g ∣ R := by
    have : R = u * rootPoly xs + v * rootPoly ys := by
      rw [← hA, ← hB]
      linear_combination (-R) * huv
    rw [this]
    exact dvd_add (hgP.mul_left _) (hgQ.mul_left _)
  have hRg : R ∣ g := by
    have e : g = EuclideanDomain.gcd (rootPoly xs) (rootPoly ys) := by
      rw [← hp, ← hq, Polynomial.gcd_map]
    rw [e]
    exact EuclideanDomain.dvd_gcd ⟨_, hA.symm⟩ ⟨_, hB.symm⟩
  have hRm : R.Monic := rootPoly_monic' _
  have hg0' : g ≠ 0 := fun e => hRm.ne_zero (by simpa [e] using hgR)
  have hg00 : g0 ≠ 0 := fun e => hg0' (by rw [hg, e, Polynomial.map_zero])
  have hmon : (g0 * C g0.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hg00
  have hmon' : ((g0 * C g0.leadingCoeff⁻¹).map k.subtype).Monic := hmon.map _
  have hassoc : Associated ((g0 * C g0.leadingCoeff⁻¹).map k.subtype) R := by
    have h1 : Associated g R := associated_of_dvd_dvd hgR hRg
    refine Associated.trans ?_ h1
    rw [Polynomial.map_mul, Polynomial.map_C]
    refine (associated_mul_unit_left g _ ?_).symm.symm
    refine Polynomial.isUnit_C.2 (IsUnit.mk0 _ ?_)
    simpa using hg00
  have heq := eq_of_monic_of_associated hmon' hRm hassoc
  intro i
  rw [← heq, Polynomial.coeff_map]
  exact (((g0 * C g0.leadingCoeff⁻¹).coeff i)).2

end ReciprocityTheory.ChartRestriction.L1
