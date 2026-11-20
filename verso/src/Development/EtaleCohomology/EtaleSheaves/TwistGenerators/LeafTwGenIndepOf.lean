import Development.EtaleCohomology.EtaleSheaves.TwistGenerators

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitSecPf.Indep

def LeafPowLocal : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)), ∃ S : Sieve U,
  S ∈ Scheme.etaleTopology U ∧ ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g →
    ∃ a : (ZMod q)ˣ, (ξ.map (Scheme.Γ.map g.op).hom).1 = (ζ.map (Scheme.Γ.map g.op).hom).1 ^ (a : ZMod q).val

/- English proof (translation)
Unfold `twGen`. Use `congr 1`. Use `(Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩)` and prove the remaining obligations. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem twGen_pow {q : ℕ} {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    twGen 0 ξ = twGen 0 ζ := by
  unfold twGen
  congr 1
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩)
  simp
  rfl

/- English proof (translation)
Introduce `q _ U ζ ξ`. Take `⟨S, hS, hSa⟩` from `hL q U ζ ξ`. Use `LateralTheory.E.LeafOneSpecPf.sec_sep (ZMod q) (tw q 0) U S hS _ _ fun V g hg => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `hSa V g hg`. Rewrite using `[twGen_res, twGen_res]`.

Conclude with `(twGen_pow _ _ a ha).symm`.
-/
theorem LeafTwGenIndep_of (hL : LeafPowLocal) : LeafTwGenIndep := by
  intro q _ U ζ ξ
  obtain ⟨S, hS, hSa⟩ := hL q U ζ ξ
  refine LateralTheory.E.LeafOneSpecPf.sec_sep (ZMod q) (tw q 0) U S hS _ _ fun V g hg => ?_
  obtain ⟨a, ha⟩ := hSa V g hg
  rw [twGen_res, twGen_res]
  exact (twGen_pow _ _ a ha).symm

/- English proof (translation)
The claim follows from `LateralTheory.E.LeafUnitSecPf.LeafUnitSec_of hP (LeafTwGenIndep_of hL)`.
-/
theorem LeafUnitSec_of (hP : LateralTheory.E.LeafOneSpecPf.LeafPrimCover) (hL : LeafPowLocal) :
    LateralTheory.E.LeafOneExistsPf.LeafUnitSec :=
  LateralTheory.E.LeafUnitSecPf.LeafUnitSec_of hP (LeafTwGenIndep_of hL)

end LateralTheory.E.LeafUnitSecPf.Indep
