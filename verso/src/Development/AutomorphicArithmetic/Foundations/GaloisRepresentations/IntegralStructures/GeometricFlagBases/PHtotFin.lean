import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

/- English proof (translation)
Set `S : Finset ℤ` to `Finset.Icc 0 N`. Establish `hall : ∀ x : DirectSum ℤ A, x ∈ ⨆ n ∈ S, LinearMap.range (DirectSum.lof K ℤ A n)`. Introduce `x`. Proceed by induction on `x using DirectSum.induction_on with`. Consider the case `zero => exact Submodule.zero_mem _`.

Consider the case `of i a`. Distinguish the cases in `hi : i ∈ S`. Conclude with `Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi ⟨a, rfl⟩)`. Establish `hout : i < 0 ∨ N < i`. Simplify using `only [S, Finset.mem_Icc, not_and_or, not_le] at hi`.

Conclude with `hi`. Use `haveI := hs i hout`. Rewrite using `[Subsingleton.elim a 0, map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y hx hy => exact Submodule.add_mem _ hx hy`.

Establish `htop : (⨆ n ∈ S, LinearMap.range (DirectSum.lof K ℤ A n)) = ⊤` using `eq_top_iff.2 (fun x _ => hall x)`. Use `Module.finite_def.2 ?_` and prove the remaining obligations. Rewrite using `[← htop]`. Use `Submodule.fg_biSup S _ (fun n _ => ?_)` and prove the remaining obligations. Rewrite using `[LinearMap.range_eq_map]`.

Conclude with `(Module.finite_def.1 (hf n)).map _`.
-/
private theorem finOfDeg {K : Type} [Field K] {A : ℤ → Type*} [∀ n, AddCommGroup (A n)]
    [∀ n, Module K (A n)] (hf : ∀ n, FiniteDimensional K (A n)) (N : ℤ)
    (hs : ∀ n, (n < 0 ∨ N < n) → Subsingleton (A n)) :
    FiniteDimensional K (DirectSum ℤ A) := by
  classical
  let S : Finset ℤ := Finset.Icc 0 N
  have hall : ∀ x : DirectSum ℤ A, x ∈ ⨆ n ∈ S, LinearMap.range (DirectSum.lof K ℤ A n) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => exact Submodule.zero_mem _
    | of i a =>
      by_cases hi : i ∈ S
      · exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi ⟨a, rfl⟩)
      · have hout : i < 0 ∨ N < i := by
          simp only [S, Finset.mem_Icc, not_and_or, not_le] at hi
          exact hi
        haveI := hs i hout
        rw [Subsingleton.elim a 0, map_zero]
        exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  have htop : (⨆ n ∈ S, LinearMap.range (DirectSum.lof K ℤ A n)) = ⊤ :=
    eq_top_iff.2 (fun x _ => hall x)
  refine Module.finite_def.2 ?_
  rw [← htop]
  refine Submodule.fg_biSup S _ (fun n _ => ?_)
  rw [LinearMap.range_eq_map]
  exact (Module.finite_def.1 (hf n)).map _

/- English proof (translation)
Introduce `h l _ k _ _ hl X p hp hproj`. Take `⟨hf, N, hN⟩` from `h l k hl p hp hproj`. Conclude with `finOfDeg hf N hN`.
-/
theorem UpperTheory.Gal.Int.Geo.htotFin_of :
    DegFin → HtotFin := by
  intro h l _ k _ _ hl X p hp hproj
  obtain ⟨hf, N, hN⟩ := h l k hl p hp hproj
  exact finOfDeg hf N hN
