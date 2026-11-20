import Development.EtaleCohomology.EtaleSheaves.LeafSpreadSeparatedPf
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsClosedImmersionDescendsToSubring

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafSpreadSeparatedPf

namespace LateralTheory.E.LeafClosedImmSpreadPf

/- English proof (translation)
Establish `e : BC f g (f ≫ g) rfl t ≫ pullback.snd g t = pullback.snd (f ≫ g) t`. Simplify using `only [BC, pullback.map, pullback.lift_snd, Category.comp_id]`. Use `IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback g t)` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `IsPullback.of_hasPullback (f ≫ g) t`.

Simplify using `only [BC, pullback.map, pullback.lift_fst]`.
-/
theorem bc_sq {X Y Z T : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (t : T ⟶ Z) :
    IsPullback (pullback.fst (f ≫ g) t) (BC f g (f ≫ g) rfl t) f (pullback.fst g t) := by
  have e : BC f g (f ≫ g) rfl t ≫ pullback.snd g t = pullback.snd (f ≫ g) t := by
    simp only [BC, pullback.map, pullback.lift_snd, Category.comp_id]
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback g t)
  · rw [e]; exact IsPullback.of_hasPullback (f ≫ g) t
  · simp only [BC, pullback.map, pullback.lift_fst]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toR_eq {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) :
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap R.toSubring.subtype : Sp Ω ⟶ Sp R) = toR R := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem incl_eq {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R S : Subalgebra k Ω} (h : R ≤ S)
    (h' : R.toSubring ≤ S.toSubring) :
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (Subring.inclusion h') : Sp S ⟶ Sp R) = incl h := rfl

/- English proof (translation)
Introduce `k _ Ω _ _ R hR X Y f g hg hfg hci`. Take `⟨hg1, hg2, hg3⟩` from `hg`. Take `⟨hp1, hp2, hp3⟩` from `hfg`. Use `hg1` as an intermediate fact. Use `hg2` as an intermediate fact.

Use `hg3` as an intermediate fact. Use `hp1` as an intermediate fact. Use `hp2` as an intermediate fact. Use `hp3` as an intermediate fact. Establish `: QuasiSeparated f` using `QuasiSeparated.of_comp f g`.

Establish `: QuasiCompact f` using `QuasiCompact.of_comp f g`. Establish `: LocallyOfFiniteType f` using `locallyOfFiniteType_of_comp f g`. Establish `hY : IsPullback (pullback.fst g (toR R)) (pullback.snd g (toR R)) (g : Y ⟶ Sp R.toSubring) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap R.toSubring.subtype)`. Rewrite using `[toR_eq]`. Conclude with `IsPullback.of_hasPullback g (toR R)`.

Establish `: QuasiCompact (g : Y ⟶ Sp R.toSubring)` using `hg2`. Take `⟨F, hF⟩` from `GlobalTheory.isClosedImmersion_descends_to_subring Ω R.toSubring X Y _ _ f g (BC f g (f ≫ g) rfl (toR R)) (pullback.fst _ _) (pullback.fst _ _) (pullback.snd _ _) hY (bc_sq f g _) hci`. Set `S : Subalgebra k Ω` to `R ⊔ Algebra.adjoin k (F : Set Ω)`. Establish `h : R ≤ S` using `le_sup_left`. Establish `h' : R.toSubring ≤ S.toSubring` using `fun x hx => h hx`.

Establish `hsub : (F : Set Ω) ⊆ S.toSubring` using `fun x hx => (le_sup_right : Algebra.adjoin k (F : Set Ω) ≤ S) (Algebra.subset_adjoin hx)`. Use `⟨S, h, hR.sup (Subalgebra.fg_adjoin_finset F), ?_⟩` and prove the remaining obligations. Establish `hY1 : IsPullback (pullback.fst g (incl h)) (pullback.snd g (incl h)) (g : Y ⟶ Sp R.toSubring) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (Subring.inclusion h'))`. Rewrite using `[incl_eq h h']`. Conclude with `IsPullback.of_hasPullback g (incl h)`.

Conclude with `hF S.toSubring h' hsub _ _ (BC f g (f ≫ g) rfl (incl h)) (pullback.fst _ _) (pullback.fst _ _) (pullback.snd _ _) hY1 (bc_sq f g _)`.
-/
theorem LeafClosedImmSpread_of : LeafClosedImmSpread := by
  intro k _ Ω _ _ R hR X Y f g hg hfg hci
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hp1, hp2, hp3⟩ := hfg
  have := hg1; have := hg2; have := hg3; have := hp1; have := hp2; have := hp3
  have : QuasiSeparated f := QuasiSeparated.of_comp f g
  have : QuasiCompact f := QuasiCompact.of_comp f g
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f g
  have hY : IsPullback (pullback.fst g (toR R)) (pullback.snd g (toR R)) (g : Y ⟶ Sp R.toSubring)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap R.toSubring.subtype) := by
    rw [toR_eq]; exact IsPullback.of_hasPullback g (toR R)
  have : QuasiCompact (g : Y ⟶ Sp R.toSubring) := hg2
  obtain ⟨F, hF⟩ := GlobalTheory.isClosedImmersion_descends_to_subring Ω R.toSubring X Y _ _ f g
    (BC f g (f ≫ g) rfl (toR R)) (pullback.fst _ _) (pullback.fst _ _) (pullback.snd _ _) hY (bc_sq f g _) hci
  let S : Subalgebra k Ω := R ⊔ Algebra.adjoin k (F : Set Ω)
  have h : R ≤ S := le_sup_left
  have h' : R.toSubring ≤ S.toSubring := fun x hx => h hx
  have hsub : (F : Set Ω) ⊆ S.toSubring := fun x hx =>
    (le_sup_right : Algebra.adjoin k (F : Set Ω) ≤ S) (Algebra.subset_adjoin hx)
  refine ⟨S, h, hR.sup (Subalgebra.fg_adjoin_finset F), ?_⟩
  have hY1 : IsPullback (pullback.fst g (incl h)) (pullback.snd g (incl h)) (g : Y ⟶ Sp R.toSubring)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (Subring.inclusion h')) := by
    rw [incl_eq h h']; exact IsPullback.of_hasPullback g (incl h)
  exact hF S.toSubring h' hsub _ _ (BC f g (f ≫ g) rfl (incl h)) (pullback.fst _ _) (pullback.fst _ _)
    (pullback.snd _ _) hY1 (bc_sq f g _)

end LateralTheory.E.LeafClosedImmSpreadPf

end
