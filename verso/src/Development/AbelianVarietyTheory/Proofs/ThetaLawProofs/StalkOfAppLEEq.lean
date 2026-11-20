import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyComp

/- English proof (translation)
Establish `hle : (L.pull F).U (fun _ => j) ⊓ L'.U k ≤ F ⁻¹ᵁ L.U j` using `fun _ hy => mem_pull.1 hy.1`. Establish `hy : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k` using `⟨mem_pull.2 hj, hk⟩`. Establish `e` using `congrArg (gs r z _) (h (fun _ => j) k hle)`. Use `(gs_appLE F _ _ hle r z hy _).symm.trans (e.trans ?_)` and prove the remaining obligations. Rewrite using `[gs_mul _ z _ hy, gs_res _ z _ hy]`.

Conclude with `congrArg (· * _) (gs_unit _ z _ hy _)`.
-/
theorem stalk_of_appLE_eq {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) (s : L.Sec)
    (s' : L'.Sec) (h : ∀ (j : (L.pull F).ι) (i : L'.ι) (hle : (L.pull F).U j ⊓ L'.U i ≤ F ⁻¹ᵁ L.U (j PUnit.unit)),
      (F.appLE _ _ hle).hom (s.f (j PUnit.unit)) =
        (show Γ(X', (L.pull F).U j ⊓ L'.U i) from (w.s (j, i)).val) * resG _ inf_le_right (s'.f i))
    {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι) (hj : F (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    gs (r ≫ F) z _ (s.f j) = (gw w r z j k).val * gs r z _ (s'.f k) := by
  have hle : (L.pull F).U (fun _ => j) ⊓ L'.U k ≤ F ⁻¹ᵁ L.U j := fun _ hy => mem_pull.1 hy.1
  have hy : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  have e := congrArg (gs r z _) (h (fun _ => j) k hle)
  refine (gs_appLE F _ _ hle r z hy _).symm.trans (e.trans ?_)
  rw [gs_mul _ z _ hy, gs_res _ z _ hy]
  exact congrArg (· * _) (gs_unit _ z _ hy _)

end GlobalTheory.KeyComp

namespace GlobalTheory

/- English proof (translation)
Introduce `R R' R'' _ _ _ x x' x'' f f' H H'`. Take `⟨φ, he, w, hg, F, hp, hw, hr, hs, hF, hε, hv⟩` from `H`. Take `⟨φ', he', w', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩` from `H'`. Establish `g` using `(isGen_iff w).1 hw`. Establish `g'` using `(isGen_iff w').1 hw'`.

Take `⟨w'', T⟩` from `exists_comp x'.P.isLB w w' g g' x.P.isLB x''.P.isLB`. Establish `he'' : eSec x''.P.A ≫ φ' ≫ φ = spMap (f'.comp f) ≫ eSec x.P.A`. Rewrite using `[← Category.assoc, he', Category.assoc, he, spMap_comp, Category.assoc]`. Use `⟨φ' ≫ φ, he'', w'', hg'.trans hg, F'.comp F, (hp'.comp hp).congr (spMap_comp f f').symm rfl, (isGen_iff w'').2 (T.pgen_comp x'.P.isLB g g'), ?_, ?_, fun a => ?_, ?_, fun i => ?_⟩` and prove the remaining obligations. Establish `r₀` using `(maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _ (rigPull_le φ (spMap f) he x.P.L) (fun _ => rfl)).1 hr`.

Establish `r₁` using `(maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _ (rigPull_le φ' (spMap f') he' x'.P.L) (fun _ => rfl)).1 hr'`. Establish `r₂` using `T.pmaps_comp x'.P.isLB (fun _ => he') r₀ r₁`. Rewrite `r₂` using `[← spMap_comp]`. Conclude with `(maps_iff w'' _ (fun _ => eSec x.P.A) _ x''.rig x.rig (spMap (f'.comp f)) _ (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' x.P.L) (fun _ => rfl)).2 r₂`. Use `KeyPow.appLE_eq_of_stalk w'' x.th x''.th fun z j k hj hk => ?_` and prove the remaining obligations.

Take `⟨i, hi⟩` from `exists_chart x'.P.isLB (φ' z)`. Establish `a` using `KeyComp.stalk_of_appLE_eq w x.th x'.th hs (𝟙 _ ≫ φ') z j i hj hi`. Establish `b` using `KeyComp.stalk_of_appLE_eq w' x'.th x''.th hs' (𝟙 _) z i k hi hk`. Rewrite using `[T _ (𝟙 _) z j i k hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]`. Rewrite using `[RingHom.comp_apply, hF, hF', RingHom.comp_apply]`.

Rewrite using `[RingHom.comp_apply, hε, hε']`. Rewrite using `[← Category.assoc, hv', Category.assoc, hv, spMap_comp, Category.assoc]`. Both sides reduce to the same expression.
-/
theorem keyPB_trans : ∀ (R R' R'' : Type) [CommRing R] [CommRing R'] [CommRing R''] (x : KeyIn R) (x' : KeyIn R') (x'' : KeyIn R'') (f : R →+* R') (f' : R' →+* R''), KeyPB x' x f → KeyPB x'' x' f' → KeyPB x'' x (f'.comp f) := by
  intro R R' R'' _ _ _ x x' x'' f f' H H'
  obtain ⟨φ, he, w, hg, F, hp, hw, hr, hs, hF, hε, hv⟩ := H
  obtain ⟨φ', he', w', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := H'
  have g := (isGen_iff w).1 hw
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp x'.P.isLB w w' g g' x.P.isLB x''.P.isLB
  have he'' : eSec x''.P.A ≫ φ' ≫ φ = spMap (f'.comp f) ≫ eSec x.P.A := by
    rw [← Category.assoc, he', Category.assoc, he, spMap_comp, Category.assoc]
  refine ⟨φ' ≫ φ, he'', w'', hg'.trans hg, F'.comp F, (hp'.comp hp).congr (spMap_comp f f').symm rfl,
    (isGen_iff w'').2 (T.pgen_comp x'.P.isLB g g'), ?_, ?_, fun a => ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _
      (rigPull_le φ (spMap f) he x.P.L) (fun _ => rfl)).1 hr
    have r₁ := (maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _
      (rigPull_le φ' (spMap f') he' x'.P.L) (fun _ => rfl)).1 hr'
    have r₂ := T.pmaps_comp x'.P.isLB (fun _ => he') r₀ r₁
    rw [← spMap_comp] at r₂
    exact (maps_iff w'' _ (fun _ => eSec x.P.A) _ x''.rig x.rig (spMap (f'.comp f)) _
      (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' x.P.L) (fun _ => rfl)).2 r₂
  · refine KeyPow.appLE_eq_of_stalk w'' x.th x''.th fun z j k hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart x'.P.isLB (φ' z)
    have a := KeyComp.stalk_of_appLE_eq w x.th x'.th hs (𝟙 _ ≫ φ') z j i hj hi
    have b := KeyComp.stalk_of_appLE_eq w' x'.th x''.th hs' (𝟙 _) z i k hi hk
    rw [T _ (𝟙 _) z j i k hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]
  · rw [RingHom.comp_apply, hF, hF', RingHom.comp_apply]
  · rw [RingHom.comp_apply, hε, hε']
  · rw [← Category.assoc, hv', Category.assoc, hv, spMap_comp, Category.assoc]
    rfl

end GlobalTheory
