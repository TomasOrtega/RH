import Development.EtaleCohomology.CohomologicalPurity.LeafChartFactPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. A detailed English derivation is pending.
-/
theorem wincl_mono (d : ℕ) : Mono (Wincl d) := by
  have h : ∀ n, Mono ((Wincl d).app n) := by
    intro n
    have : ∀ U, Mono (((Wincl d).app n).app U) := by
      intro U
      rw [mono_iff_injective]
      intro F G hFG
      change (F : ComposableArrows (WVec d U.unop) _) ⋙ WVec.incl d U.unop = G ⋙ WVec.incl d U.unop at hFG
      exact CategoryTheory.Functor.hext (fun i => Subtype.ext (congrArg (fun K => K.obj i) hFG))
        (fun i j a => Functor.hcongr_hom hFG a)
    exact NatTrans.mono_of_mono_app _
  exact NatTrans.mono_of_mono_app _

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem wb_mono (d : ℕ) (R : Type) [CommRing R] : Mono (wb d R) := by
  have := wincl_mono d
  unfold wb; infer_instance

def LocCov {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) : Prop :=
  ∀ (n : SimplexCategoryᵒᵖ) (X : Scheme.{0}) (x : (E.obj n).obj (op X)), ∃ (ι : Type) (O : ι → X.Opens),
    iSup O = ⊤ ∧ ∀ i, (∃ y, (f.app n).app (op (O i : Scheme.{0})) y = (E.obj n).map (O i).ι.op x) ∨
      (∃ y, (g.app n).app (op (O i : Scheme.{0})) y = (E.obj n).map (O i).ι.op x)

def LeafCovLoc : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Mono f → Mono g →
  LocCov f g → Cover2 R f g

def LeafWLoc : Prop := ∀ (d : ℕ) (R : Type) [CommRing R], LocCov (wb d R) (pr d R).hom

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem LeafWCov_of (hG : LeafGeo) (hC : LeafCovLoc) (hW : LeafWLoc) : LeafWCov := by
  intro _ q _ d R _ _
  exact hC (ZMod q) (wb d R) (pr d R).hom (wb_mono d R) (hG.1 d R) (hW d R)

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
