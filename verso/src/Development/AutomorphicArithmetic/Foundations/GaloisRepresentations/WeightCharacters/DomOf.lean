import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Formalism.GradedWeylDivisibility.FinalC
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

/- English proof (translation)
Introduce `a κ f hf`. Establish `hf' : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ a a κ.natW` using `hf`. Use `clear hf`. Rewrite `hf'` using `[Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℂ a a κ.natW]`. Proceed by induction on `hf' using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨K, sz, hsz, I, hshape, rfl⟩` from `hx`. Introduce `m hm k`. Establish `h` using `(Formalism.GradedWeylDivisibility.bidetDominance ℂ a a K sz hsz I m hm).1 k`. Rewrite `h` using `[hshape]`.

Conclude with `h`. Consider the case `zero`. Introduce `m hm`. Simplify using `at hm`. Consider the case `add x y _ _ hx hy`.

Introduce `m hm k`. Break down `Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h` into its components or cases. Conclude with `hx m h k`. Conclude with `hy m h k`. Consider the case `smul c x _ hx`.

Introduce `m hm k`. Conclude with `hx m (MvPolynomial.support_smul hm) k`.
-/
theorem UpperTheory.Gal.Wt.dom_of :
    UpperTheory.Gal.Wt.Dom := by
  classical
  intro a κ f hf
  have hf' : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ a a κ.natW := hf
  clear hf
  rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℂ a a κ.natW] at hf'
  induction hf' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm k
    have h := (Formalism.GradedWeylDivisibility.bidetDominance ℂ a a K sz hsz I m hm).1 k
    rw [hshape] at h
    exact h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm k
    rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
    · exact hx m h k
    · exact hy m h k
  | smul c x _ hx =>
    intro m hm k
    exact hx m (MvPolynomial.support_smul hm) k
