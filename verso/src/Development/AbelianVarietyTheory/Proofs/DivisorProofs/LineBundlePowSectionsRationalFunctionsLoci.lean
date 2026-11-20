import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

/- English proof (translation)
Introduce `k _ X _ p P e`. Establish `hR : P.Rep ((e : ℤ) * 1) ((e : ℤ) * 0) (P.L.pow e)` using `GlobalTheory.VolBr.Pair.rep_pow k X p P 1 0 P.L e (GlobalTheory.VolBr.Pair.rep_base k X p P).1`. Rewrite `hR` using `[mul_one, mul_zero]`. Take `⟨g, -, hrange, -, hloc⟩` from `GlobalTheory.VolBr.RepDict.rep_dict k X p P (e : ℤ) 0 (P.L.pow e) hR`. Establish `hcov {B : LB X} (hB : B.IsLB) (x : X) : ∃ c, x ∈ B.U c` using `Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))`.

Establish `key : ∀ u : (lbPow P.L.B e).Sec, NV P e 0 (g u) = (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u : Set X)`. Introduce `u`. Use extensionality with `x`. Take `⟨i, hi⟩` from `hcov P.L.isLB x`. Take `⟨j, hj⟩` from `hcov P.A.isLB x`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `(hloc u x i j hi hj).2 (h i j hi hj)`. Introduce `h i' j' hi' hj'`. Conclude with `(hloc u x i' j' hi' hj').1 h`.

Use `⟨fun u => ⟨g u, ?_, key u⟩, fun f hf => ?_⟩` and prove the remaining obligations. Establish `: g u ∈ Set.range g` using `⟨u, rfl⟩`. Rewrite `this` using `[hrange]`. Conclude with `this`. Establish `: f ∈ Set.range g` using `by rw [hrange]; exact hf`.

Take `⟨u, rfl⟩` from `this`. Conclude with `⟨u, key u⟩`.
-/
theorem GlobalTheory.HSAmp.pow_sec_dict : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ e : ℕ, (∀ u : (lbPow P.L.B e).Sec, ∃ f ∈ P.H e 0, NV P e 0 f = ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u) ∧ ∀ f ∈ P.H e 0, ∃ u : (lbPow P.L.B e).Sec, NV P e 0 f = ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  intro k _ X _ p P e
  have hR : P.Rep ((e : ℤ) * 1) ((e : ℤ) * 0) (P.L.pow e) :=
    GlobalTheory.VolBr.Pair.rep_pow k X p P 1 0 P.L e (GlobalTheory.VolBr.Pair.rep_base k X p P).1
  rw [mul_one, mul_zero] at hR
  obtain ⟨g, -, hrange, -, hloc⟩ := GlobalTheory.VolBr.RepDict.rep_dict k X p P (e : ℤ) 0 (P.L.pow e) hR
  have hcov {B : LB X} (hB : B.IsLB) (x : X) : ∃ c, x ∈ B.U c :=
    Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))
  have key : ∀ u : (lbPow P.L.B e).Sec, NV P e 0 (g u) = (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u : Set X) := by
    intro u
    ext x
    obtain ⟨i, hi⟩ := hcov P.L.isLB x
    obtain ⟨j, hj⟩ := hcov P.A.isLB x
    constructor
    · intro h
      exact (hloc u x i j hi hj).2 (h i j hi hj)
    · intro h i' j' hi' hj'
      exact (hloc u x i' j' hi' hj').1 h
  refine ⟨fun u => ⟨g u, ?_, key u⟩, fun f hf => ?_⟩
  · have : g u ∈ Set.range g := ⟨u, rfl⟩
    rw [hrange] at this
    exact this
  · have : f ∈ Set.range g := by rw [hrange]; exact hf
    obtain ⟨u, rfl⟩ := this
    exact ⟨u, key u⟩
