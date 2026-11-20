import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundleDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef.LeIff

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

/- English proof (translation)
Simplify using `[ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus]`.
-/
theorem nonzeroLocus_zero {M : LB X} : ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (0 : LB.Sec M) = ⊥ := by
  simp [ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus]

/- English proof (translation)
The claim follows from `mul_nonneg (norm_nonneg _) (Real.exp_pos _).le`.
-/
theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    0 ≤ P.nu a b σ y f :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

/- English proof (translation)
Assume the negation of the conclusion as `h`. Take `⟨i, hi⟩` from `exists_chart P.L.isLB (genericPoint X)`. Take `⟨j, hj⟩` from `exists_chart P.A.isLB (genericPoint X)`. Establish `hne : P.loc a b (e 0) i j ≠ 0`. Simplify using `only [Pair.loc]`.

Conclude with `mul_ne_zero (mul_ne_zero h (zpow_ne_zero _ (P.r i).ne_zero)) (zpow_ne_zero _ (P.r' j).ne_zero)`. Establish `hmem` using `(he 0 _ i j hi hj).2 (unitAt_genericPoint hne)`. Rewrite `hmem` using `[nonzeroLocus_zero]`. Simplify using `at hmem`.
-/
theorem dict_zero (P : Pair p) (a b : ℤ) {M : HermLB p} (e : M.B.Sec → X.functionField)
    (he : ∀ (u : M.B.Sec) (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j →
      (x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u ↔ UnitAt x (P.loc a b (e u) i j))) : e 0 = 0 := by
  by_contra h
  obtain ⟨i, hi⟩ := exists_chart P.L.isLB (genericPoint X)
  obtain ⟨j, hj⟩ := exists_chart P.A.isLB (genericPoint X)
  have hne : P.loc a b (e 0) i j ≠ 0 := by
    simp only [Pair.loc]
    exact mul_ne_zero (mul_ne_zero h (zpow_ne_zero _ (P.r i).ne_zero)) (zpow_ne_zero _ (P.r' j).ne_zero)
  have hmem := (he 0 _ i j hi hj).2 (unitAt_genericPoint hne)
  rw [nonzeroLocus_zero] at hmem
  simp at hmem

/- English proof (translation)
Take `⟨h1, h2, -⟩` from `Pair.rep_base k X p P`. Establish `h3 : P.Rep 0 (-1) P.A.dual`. Use `Pair.rep_dual k X p P 0 1 _ h2` as an intermediate fact. Rewrite `this` using `[neg_zero]`. Then use the resulting hypothesis. Use `Pair.rep_tens k X p P 1 0 0 (-1) _ _ h1 h3` as an intermediate fact.

Rewrite `this` using `[add_zero, zero_add]`. Then use the resulting hypothesis.
-/
theorem rep_diff (P : Pair p) : P.Rep 1 (-1) (P.L.tens P.A.dual) := by
  obtain ⟨h1, h2, -⟩ := Pair.rep_base k X p P
  have h3 : P.Rep 0 (-1) P.A.dual := by
    have := Pair.rep_dual k X p P 0 1 _ h2
    rwa [neg_zero] at this
  have := Pair.rep_tens k X p P 1 0 0 (-1) _ _ h1 h3
  rwa [add_zero, zero_add] at this

def scaleL (P : Pair p) (f : X.functionFieldˣ) : Pair p :=
  ⟨P.L, P.A, fun i => f * P.r i, P.r', fun i j h => by
    simp only [Units.val_mul]
    rw [P.hr i j h]
    ring, P.hr'⟩

/- English proof (translation)
Simplify using `only [Pair.loc, scaleL, Units.val_mul, zpow_one, one_mul]`.
-/
theorem scaleL_loc (P : Pair p) (f : X.functionFieldˣ) (i : P.L.B.ι) (j : P.A.B.ι) :
    (scaleL P f).loc 1 (-1) 1 i j = P.loc 1 (-1) f i j := by
  simp only [Pair.loc, scaleL, Units.val_mul, zpow_one, one_mul]

end GlobalTheory.HSNef.LeIff

open GlobalTheory.HSNef.LeIff in

/- English proof (translation)
Introduce `k _ X _ p A B`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨P, rfl, rfl, h1H, h1n⟩`. Take `⟨e, -, hrange, hnorm, hloc⟩` from `RepDict.rep_dict k X p P 1 (-1) _ (rep_diff P)`. Take `⟨u, hu⟩ : (1 : X.functionField) ∈ Set.range e` from `by rw [hrange]; exact h1H`.

Use `⟨u, fun σ y => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hnorm, hu]`. Establish `h0` using `nu_nonneg P 1 (-1) σ y 1`. Establish `h1` using `h1n σ y`. Use the polynomial consequences of the given equalities and inequalities.

Introduce and unpack `rfl`. Rewrite `hu` using `[dict_zero P 1 (-1) e hloc]`. Conclude with `zero_ne_one hu`. Introduce and unpack `⟨s, hs, hs0⟩`. Take `⟨P, hPL, hPA⟩` from `exists_pair A B`.

Substitute `hPL hPA` using the available equality. Take `⟨e, hinj, hrange, hnorm, hloc⟩` from `RepDict.rep_dict k X p P 1 (-1) _ (rep_diff P)`. Establish `hfH : e s ∈ P.H 1 (-1)`. Establish `: e s ∈ Set.range e` using `⟨s, rfl⟩`. Rewrite `this` using `[hrange]`.

Conclude with `this`. Establish `hf0 : e s ≠ 0` using `fun h => hs0 (hinj (h.trans (dict_zero P 1 (-1) e hloc).symm))`. Establish `hfn : ∀ σ (y : CxPts p σ), P.nu 1 (-1) σ y (e s) ≤ 1` using `fun σ y => by`. Establish `h` using `hnorm s σ y`. Establish `h'` using `hs σ y`.

Establish `h0` using `nu_nonneg P 1 (-1) σ y (e s)`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨scaleL P (Units.mk0 _ hf0), rfl, rfl, fun x i j hi hj => ?_, fun σ y => ?_⟩` and prove the remaining obligations. Rewrite using `[show (scaleL P (Units.mk0 _ hf0)).loc 1 (-1) 1 i j = P.loc 1 (-1) (e s) i j from scaleL_loc P (Units.mk0 _ hf0) i j]`. Conclude with `hfH x i j hi hj`.

Use `hfn σ y` as an intermediate fact. Simplify using `only [Pair.nu] at this ⊢`. Rewrite using `[show ∀ i j, (scaleL P (Units.mk0 _ hf0)).loc 1 (-1) 1 i j = P.loc 1 (-1) (e s) i j from scaleL_loc P (Units.mk0 _ hf0)]`. Conclude with `this`.
-/
theorem GlobalTheory.HSNef.le_iff_exists_smallSec : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ A B : HermLB p, Le B A ↔ ∃ s ∈ (A.tens B.dual).smallSec, s ≠ 0 := by
  intro k _ X _ p A B
  constructor
  · rintro ⟨P, rfl, rfl, h1H, h1n⟩
    obtain ⟨e, -, hrange, hnorm, hloc⟩ := RepDict.rep_dict k X p P 1 (-1) _ (rep_diff P)
    obtain ⟨u, hu⟩ : (1 : X.functionField) ∈ Set.range e := by rw [hrange]; exact h1H
    refine ⟨u, fun σ y => ?_, ?_⟩
    · rw [← hnorm, hu]
      have h0 := nu_nonneg P 1 (-1) σ y 1
      have h1 := h1n σ y
      nlinarith
    · rintro rfl
      rw [dict_zero P 1 (-1) e hloc] at hu
      exact zero_ne_one hu
  · rintro ⟨s, hs, hs0⟩
    obtain ⟨P, hPL, hPA⟩ := exists_pair A B
    subst hPL hPA
    obtain ⟨e, hinj, hrange, hnorm, hloc⟩ := RepDict.rep_dict k X p P 1 (-1) _ (rep_diff P)
    have hfH : e s ∈ P.H 1 (-1) := by
      have : e s ∈ Set.range e := ⟨s, rfl⟩
      rw [hrange] at this
      exact this
    have hf0 : e s ≠ 0 := fun h => hs0 (hinj (h.trans (dict_zero P 1 (-1) e hloc).symm))
    have hfn : ∀ σ (y : CxPts p σ), P.nu 1 (-1) σ y (e s) ≤ 1 := fun σ y => by
      have h := hnorm s σ y
      have h' := hs σ y
      have h0 := nu_nonneg P 1 (-1) σ y (e s)
      nlinarith
    refine ⟨scaleL P (Units.mk0 _ hf0), rfl, rfl, fun x i j hi hj => ?_, fun σ y => ?_⟩
    · rw [show (scaleL P (Units.mk0 _ hf0)).loc 1 (-1) 1 i j = P.loc 1 (-1) (e s) i j from
        scaleL_loc P (Units.mk0 _ hf0) i j]
      exact hfH x i j hi hj
    · have := hfn σ y
      simp only [Pair.nu] at this ⊢
      rw [show ∀ i j, (scaleL P (Units.mk0 _ hf0)).loc 1 (-1) 1 i j = P.loc 1 (-1) (e s) i j from
        scaleL_loc P (Units.mk0 _ hf0)]
      exact this
