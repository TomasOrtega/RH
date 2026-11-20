import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsKumCoc

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison.TwSec

open GlobalTheory.EtC

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (k ≫ g) y = Sec.res k (Sec.res g y) := by
  change (F.obj.map (k ≫ g).op).hom y = (F.obj.map k.op).hom ((F.obj.map g.op).hom y)
  rw [op_comp, Functor.map_comp]
  rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem loc_bind' {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (h' : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => P' W (k ≫ g)) : Loc U P' := by
  obtain ⟨S, hS, hP⟩ := h
  choose T hT hT' using fun (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g) => h' V g (hP V g hg)
  refine ⟨Sieve.bind S.arrows (fun V g hg => T V g hg),
    Scheme.etaleTopology.bind_covering hS (fun V g hg => hT V g hg), ?_⟩
  rintro W f ⟨V, k, g, hg, hk, rfl⟩
  exact hT' V g hg W k hk

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem tw_loc (hG : E.InGen) (Q : ℕ) [NeZero Q] (i : ℤ) (U : Scheme.{0}) (y : Sec (tw Q i) U) :
    Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim Q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ := by
  have hsurj : Presheaf.imageSieve (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF Q i)) y ∈ Scheme.etaleTopology U :=
    Presheaf.imageSieve_mem Scheme.etaleTopology _ (U := op U) y
  refine loc_bind' ⟨_, hsurj, fun V g hg => hg⟩ ?_
  rintro V g ⟨t, ht⟩
  by_cases hP : Nonempty (Prim Q Γ(V, ⊤))
  · obtain ⟨ζ₀⟩ := hP
    obtain ⟨S, hS, hS'⟩ := (hG Q i).1 V ζ₀ (Sec.res g y)
    refine ⟨S, hS, fun W k hk => Or.inr ?_⟩
    obtain ⟨c, hc⟩ := hS' W k hk
    exact ⟨ζ₀.map k.appTop.hom, c, (res_comp k g y).trans hc⟩
  · have : IsEmpty (Prim Q Γ(V, ⊤)) := not_nonempty_iff.mp hP
    have ht0 : t = 0 := by
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (twRel Q i Γ(V, ⊤))
        (show (Prim Q Γ(V, ⊤) →₀ ULift.{1} (ZMod Q)) ⧸ twRel Q i Γ(V, ⊤) from t)
      have hf : f = 0 := Finsupp.ext fun a => (IsEmpty.false a).elim
      rw [hf]
      exact Submodule.Quotient.mk_zero _
    have hy : Sec.res g y = 0 := by
      refine ht.symm.trans ?_
      rw [ht0]
      exact map_zero _
    refine ⟨⊤, Scheme.etaleTopology.top_mem V, fun W k _ => Or.inl ?_⟩
    rw [res_comp, hy]
    exact map_zero _

end CrystallineSemistableComparison.TwSec
