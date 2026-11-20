import Development.EtaleCohomology.EtaleSheaves.TwistGenerators

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitSecPf.Indep

def LeafPowLocal : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)), ∃ S : Sieve U,
  S ∈ Scheme.etaleTopology U ∧ ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g →
    ∃ a : (ZMod q)ˣ, (ξ.map (Scheme.Γ.map g.op).hom).1 = (ζ.map (Scheme.Γ.map g.op).hom).1 ^ (a : ZMod q).val

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem twGen_pow {q : ℕ} {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    twGen 0 ξ = twGen 0 ζ := by
  unfold twGen
  congr 1
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩)
  simp
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem LeafTwGenIndep_of (hL : LeafPowLocal) : LeafTwGenIndep := by
  intro q _ U ζ ξ
  obtain ⟨S, hS, hSa⟩ := hL q U ζ ξ
  refine LateralTheory.E.LeafOneSpecPf.sec_sep (ZMod q) (tw q 0) U S hS _ _ fun V g hg => ?_
  obtain ⟨a, ha⟩ := hSa V g hg
  rw [twGen_res, twGen_res]
  exact (twGen_pow _ _ a ha).symm

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LeafUnitSec_of (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hL : LeafPowLocal) :
    LateralTheory.E.LeafOneExistsPf.LeafUnitSec :=
  LateralTheory.E.LeafUnitSecPf.LeafUnitSec_of hP (LeafTwGenIndep_of hL)

end LateralTheory.E.LeafUnitSecPf.Indep
