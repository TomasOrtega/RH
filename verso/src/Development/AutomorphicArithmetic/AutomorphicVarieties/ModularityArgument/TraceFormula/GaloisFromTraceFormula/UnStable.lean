import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

/- English proof (translation)
Establish `hk : ((-1 : ℂˣ) ^ k)⁻¹ = (-1 : ℂˣ) ^ k`. Rewrite using `[← inv_pow, inv_neg_one]`. Use `conv_rhs => rw [← h]`. Simplify using `only [UpperTheory.V.Z.Tf.GlobalTraceComparison.inv, Multiset.map_map]`. Use `Multiset.map_congr rfl fun x _ => ?_` and prove the remaining obligations.

Simplify using `only [Function.comp_apply, mul_inv, hk]`.
-/
private theorem inv_map_sign (B : Multiset ℂˣ) (k : ℕ) (h : inv B = B) :
    inv (B.map (· * (-1 : ℂˣ) ^ k)) = B.map (· * (-1 : ℂˣ) ^ k) := by
  have hk : ((-1 : ℂˣ) ^ k)⁻¹ = (-1 : ℂˣ) ^ k := by
    rw [← inv_pow, inv_neg_one]
  conv_rhs => rw [← h]
  simp only [UpperTheory.V.Z.Tf.GlobalTraceComparison.inv, Multiset.map_map]
  refine Multiset.map_congr rfl fun x _ => ?_
  simp only [Function.comp_apply, mul_inv, hk]

/- English proof (translation)
Introduce `E _ _ _ μ a b w B₁ B₂ hμ h₁ h₂`. Establish `hadd : ∀ X Y : Multiset ℂˣ, inv (X + Y) = inv X + inv Y` using `fun X Y => Multiset.map_add _ _ _`. Simplify using `only [un, hμ]`. Rewrite using `[hadd, inv_map_sign B₁ b h₁, inv_map_sign B₂ a h₂]`.
-/
theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.unStable :
    UnStable := by
  intro E _ _ _ μ a b w B₁ B₂ hμ h₁ h₂
  have hadd : ∀ X Y : Multiset ℂˣ, inv (X + Y) = inv X + inv Y := fun X Y => Multiset.map_add _ _ _
  simp only [un, hμ]
  rw [hadd, inv_map_sign B₁ b h₁, inv_map_sign B₂ a h₂]
