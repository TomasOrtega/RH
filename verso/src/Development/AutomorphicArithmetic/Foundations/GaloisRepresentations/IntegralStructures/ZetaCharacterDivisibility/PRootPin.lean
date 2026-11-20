import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

/- English proof (translation)
Introduce `p s m hp hdeg hdvd hprod hgen`. Establish `hspl : p.Splits` using `IsAlgClosed.splits p`. Establish `hq : rootPol s ^ m ≠ 0`. Apply `pow_ne_zero` to reduce the goal to its premises. Conclude with `(monic_multiset_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)).ne_zero`.

Establish `hle : p.roots ≤ (rootPol s ^ m).roots` using `Polynomial.roots.le_of_dvd hq hdvd`. Establish `hroots : (rootPol s ^ m).roots = m • s`. Rewrite using `[Polynomial.roots_pow]`. Unfold `rootPol`. Rewrite using `[roots_multiset_prod_X_sub_C]`.

Establish `hcard : p.roots.card = s.card`. Rewrite using `[splits_iff_card_roots.mp hspl, hdeg]`. Establish `hmem : ∀ x ∈ p.roots, x ∈ s`. Introduce `x hx`. Use `Multiset.mem_of_le hle hx` as an intermediate fact.

Rewrite `this` using `[hroots, Multiset.mem_nsmul]`. Conclude with `this.2`. Establish `heq : p.roots = s` using `hgen _ hcard hmem hprod`. Rewrite using `[hspl.eq_prod_roots_of_monic hp, heq]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.Gal.Int.Div.rootPin_of :
    RootPin := by
  intro p s m hp hdeg hdvd hprod hgen
  have hspl : p.Splits := IsAlgClosed.splits p
  have hq : rootPol s ^ m ≠ 0 := by
    apply pow_ne_zero
    exact (monic_multiset_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)).ne_zero
  have hle : p.roots ≤ (rootPol s ^ m).roots := Polynomial.roots.le_of_dvd hq hdvd
  have hroots : (rootPol s ^ m).roots = m • s := by
    rw [Polynomial.roots_pow]
    unfold rootPol
    rw [roots_multiset_prod_X_sub_C]
  have hcard : p.roots.card = s.card := by
    rw [splits_iff_card_roots.mp hspl, hdeg]
  have hmem : ∀ x ∈ p.roots, x ∈ s := by
    intro x hx
    have := Multiset.mem_of_le hle hx
    rw [hroots, Multiset.mem_nsmul] at this
    exact this.2
  have heq : p.roots = s := hgen _ hcard hmem hprod
  rw [hspl.eq_prod_roots_of_monic hp, heq]
  rfl
