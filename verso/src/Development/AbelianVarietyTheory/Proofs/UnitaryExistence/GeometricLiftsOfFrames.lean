import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.DeltaDatumCombinedCoefficient
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdmissibleFalseIffFirstInvariant
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.AdmissibleSmulIffOfCoprime
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelCoverCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation hiding zetaM
open GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient

attribute [local instance] Over.cartesianMonoidalCategory

section Calc

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {q : Y ⟶ X} {q' : Y' ⟶ X'} {pm : Y' ⟶ Y}

def PtOver (w : LB.Iso L' (L.pull F)) (pm : Y' ⟶ Y) (k : ℤ)
    (s' : LB.Sec (LB.LinComb L' (K := Fin 1) (fun _ => q') (fun _ => k)))
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => q) (fun _ => k))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (i : L.ι) (j : L'.ι), F (q' (r z)) ∈ L.U i → q' (r z) ∈ L'.U j →
    gs (r ≫ pm) z _ (s.f fun _ => i) = (gw w (r ≫ q') z i j ^ k).val * gs r z _ (s'.f fun _ => j)

/- English proof (translation)
Establish `e : q (pm y) = F (q' y)` using `by rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]`. Rewrite using `[← e]`. Conclude with `⟨fun hy => Set.mem_iInter.1 hy 0, fun hy => Set.mem_iInter.2 fun _ => hy⟩`.
-/
theorem mem_sq (h : pm ≫ q = q' ≫ F) (y : Y') (i : L.ι) :
    pm y ∈ LB.wchart L (fun _ : Fin 1 => q) (fun _ => i) ↔ F (q' y) ∈ L.U i := by
  have e : q (pm y) = F (q' y) := by rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
  rw [← e]
  exact ⟨fun hy => Set.mem_iInter.1 hy 0, fun hy => Set.mem_iInter.2 fun _ => hy⟩

/- English proof (translation)
Establish `key : ∀ (i : L.ι) (j : L'.ι) (W : Y'.Opens) (h₂ : W ≤ (LB.LinComb L' (K` using `Fin 1) (fun _ => q') (fun _ => k)).U fun _ => j) (h₃ : W ≤ q' ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => i, j)) (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z), r z ∈ W → gs r z W (((res h₃ (pullU q' _ (w.s (fun _ => i, j))) ^ k : Γ(Y', W)ˣ) : Γ(Y', W)) * (Y'.presheaf.map (homOfLE h₂).op).hom …`. Introduce `i j W h₂ h₃ Z r z hz`. Rewrite using `[gs_mul r z W hz, gs_res r z h₂ hz, gs_unit r z W hz, map_zpow, gm_res r z h₃ hz, gm_pull r q' z _ (h₃ hz)]`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion.

Introduce `H i j W h₁ h₂ h₃`. Use `fn_ext fun z hz => ?_` and prove the remaining obligations. Rewrite using `[key i j W h₂ h₃ _ _ z hz, gs_appLE pm _ W h₁ _ z hz]`. Conclude with `H _ (𝟙 _) z i j (mem_pull.1 (h₃ hz).1) (h₃ hz).2`. Introduce `H Z r z i j hi hj`.

Set `W : Y'.Opens` to `q' ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => i, j)`. Establish `hz : r z ∈ W` using `⟨mem_pull.2 hi, hj⟩`. Establish `h₁ : W ≤ pm ⁻¹ᵁ (LB.LinComb L (K` using `Fin 1) (fun _ => q) (fun _ => k)).U fun _ => i := fun y hy => (mem_sq h y i).2 (mem_pull.1 hy.1)`. Establish `h₂ : W ≤ (LB.LinComb L' (K` using `Fin 1) (fun _ => q') (fun _ => k)).U fun _ => j := fun y hy => Set.mem_iInter.2 fun _ => hy.2`. Rewrite using `[← key i j W h₂ le_rfl Z r z hz, ← H i j W h₁ h₂ le_rfl, gs_appLE pm _ W h₁ r z hz]`.
-/
theorem ptOver_iff_charts (h : pm ≫ q = q' ≫ F) (w : LB.Iso L' (L.pull F)) (k : ℤ)
    (s' : LB.Sec (LB.LinComb L' (K := Fin 1) (fun _ => q') (fun _ => k)))
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => q) (fun _ => k))) :
    PtOver w pm k s' s ↔ ∀ (i : L.ι) (j : L'.ι) (W : Y'.Opens)
      (h₁ : W ≤ pm ⁻¹ᵁ (LB.LinComb L (K := Fin 1) (fun _ => q) (fun _ => k)).U fun _ => i)
      (h₂ : W ≤ (LB.LinComb L' (K := Fin 1) (fun _ => q') (fun _ => k)).U fun _ => j)
      (h₃ : W ≤ q' ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => i, j)),
      (pm.appLE _ W h₁).hom (s.f fun _ => i) =
        ((res h₃ (pullU q' _ (w.s (fun _ => i, j))) ^ k : Γ(Y', W)ˣ) : Γ(Y', W)) *
          (Y'.presheaf.map (homOfLE h₂).op).hom (s'.f fun _ => j) := by
  have key : ∀ (i : L.ι) (j : L'.ι) (W : Y'.Opens)
      (h₂ : W ≤ (LB.LinComb L' (K := Fin 1) (fun _ => q') (fun _ => k)).U fun _ => j)
      (h₃ : W ≤ q' ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => i, j)) (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z), r z ∈ W →
      gs r z W (((res h₃ (pullU q' _ (w.s (fun _ => i, j))) ^ k : Γ(Y', W)ˣ) : Γ(Y', W)) *
          (Y'.presheaf.map (homOfLE h₂).op).hom (s'.f fun _ => j)) =
        (gw w (r ≫ q') z i j ^ k).val * gs r z _ (s'.f fun _ => j) := by
    intro i j W h₂ h₃ Z r z hz
    rw [gs_mul r z W hz, gs_res r z h₂ hz, gs_unit r z W hz, map_zpow, gm_res r z h₃ hz, gm_pull r q' z _ (h₃ hz)]
    rfl
  constructor
  · intro H i j W h₁ h₂ h₃
    refine fn_ext fun z hz => ?_
    rw [key i j W h₂ h₃ _ _ z hz, gs_appLE pm _ W h₁ _ z hz]
    exact H _ (𝟙 _) z i j (mem_pull.1 (h₃ hz).1) (h₃ hz).2
  · intro H Z r z i j hi hj
    let W : Y'.Opens := q' ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => i, j)
    have hz : r z ∈ W := ⟨mem_pull.2 hi, hj⟩
    have h₁ : W ≤ pm ⁻¹ᵁ (LB.LinComb L (K := Fin 1) (fun _ => q) (fun _ => k)).U fun _ => i :=
      fun y hy => (mem_sq h y i).2 (mem_pull.1 hy.1)
    have h₂ : W ≤ (LB.LinComb L' (K := Fin 1) (fun _ => q') (fun _ => k)).U fun _ => j :=
      fun y hy => Set.mem_iInter.2 fun _ => hy.2
    rw [← key i j W h₂ le_rfl Z r z hz, ← H i j W h₁ h₂ le_rfl, gs_appLE pm _ W h₁ r z hz]

/- English proof (translation)
The claim follows from `funext fun a => congrArg J (Subsingleton.elim _ _)`.
-/
theorem fin_one_eq {A : Type} (J : Fin 1 → A) : J = fun _ => J 0 := funext fun a => congrArg J (Subsingleton.elim _ _)

/- English proof (translation)
Establish `hm : r z ∈ LB.wchart (L.pull F) (fun _ : Fin 1 => q') (fun _ _ => i) ⊓ LB.wchart L' (fun _ : Fin 1 => q') (fun _ => j)` using `⟨Set.mem_iInter.2 fun _ => mem_pull.2 hi, Set.mem_iInter.2 fun _ => hj⟩`. Express the relevant statement in the definitionally equal form `gm r z _ (∏ _k : Fin 1, (res _ (pullU q' _ (w.s (fun _ => i, j)))) ^ (1 : ℤ)) = _`. Rewrite using `[Fin.prod_univ_one, zpow_one]`. Conclude with `(gm_res r z _ hm _).trans (gm_pull r q' z ((L.pull F).U (fun _ => i) ⊓ L'.U j) ⟨mem_pull.2 hi, hj⟩ _)`.
-/
theorem gs_secMaps (w : LB.Iso L' (L.pull F)) (i : L.ι) (j : L'.ι) {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z)
    (hi : F (q' (r z)) ∈ L.U i) (hj : q' (r z) ∈ L'.U j) :
    gm r z (LB.wchart (L.pull F) (fun _ : Fin 1 => q') (fun _ _ => i) ⊓ LB.wchart L' (fun _ : Fin 1 => q') (fun _ => j))
      ((LB.linCombIso w (K := Fin 1) (fun _ => q') (fun _ => 1)).s (fun _ _ => i, fun _ => j)) =
      gw w (r ≫ q') z i j := by
  have hm : r z ∈ LB.wchart (L.pull F) (fun _ : Fin 1 => q') (fun _ _ => i) ⊓
      LB.wchart L' (fun _ : Fin 1 => q') (fun _ => j) :=
    ⟨Set.mem_iInter.2 fun _ => mem_pull.2 hi, Set.mem_iInter.2 fun _ => hj⟩
  change gm r z _ (∏ _k : Fin 1, (res _ (pullU q' _ (w.s (fun _ => i, j)))) ^ (1 : ℤ)) = _
  rw [Fin.prod_univ_one, zpow_one]
  exact (gm_res r z _ hm _).trans
    (gm_pull r q' z ((L.pull F).U (fun _ => i) ⊓ L'.U j) ⟨mem_pull.2 hi, hj⟩ _)

/- English proof (translation)
Establish `le : ∀ J : Fin 1 → PUnit → L.ι, LB.wchart (L.pull F) (fun _ : Fin 1 => q') J ≤ pm ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => q) (fun _ => J 0 PUnit.unit)` using `fun J y hy => (mem_sq h y _).2 (mem_pull.1 (Set.mem_iInter.1 hy 0))`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Use `⟨⟨fun J => (pm.appLE _ _ (le J)).hom (s.f fun _ => J 0 PUnit.unit), fun J J' => fn_ext fun y hy => ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `a` using `le J hy.1`.

Establish `a'` using `le J' hy.2`. Use `(gs_res _ y _ hy _).trans ((gs_appLE pm _ _ _ _ y hy.1 _).trans ((gs_compat s _ y a a').trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans (congrArg Units.val ?_)) ((gs_res _ y _ hy _).trans (gs_appLE pm _ _ _ _ y hy.2 _)))))))` and prove the remaining obligations. Use `(gm_linComb (L.pull F) (fun _ : Fin 1 => q') (fun _ => 1) (𝟙 _) y J J' hy.1 hy.2).trans (Eq.trans ?_ (gm_linComb L (fun _ : Fin 1 => q) (fun _ => 1) (𝟙 _ ≫ pm) y _ _ a a').symm)` and prove the remaining obligations. Rewrite using `[Fin.prod_univ_one, Fin.prod_univ_one, Category.assoc, h, ← Category.assoc]`. Conclude with `congrArg (· ^ (1 : ℤ)) (gm_pull_g L F _ y _ _ (Set.mem_iInter.1 hy.1 0) (Set.mem_iInter.1 hy.2 0))`.

Introduce and unpack `⟨J, j⟩`. Take `⟨i, rfl⟩ : ∃ i, J = fun _ _ => i` from `⟨J 0 PUnit.unit, fin_one_eq J⟩`. Take `⟨j, rfl⟩ : ∃ j', j = fun _ => j'` from `⟨j 0, fin_one_eq j⟩`. Use `fn_ext fun y hy => ?_` and prove the remaining obligations. Establish `hi : F (q' y) ∈ L.U i` using `mem_pull.1 (Set.mem_iInter.1 hy.1 0)`.

Establish `hj : q' y ∈ L'.U j` using `Set.mem_iInter.1 hy.2 0`. Use `(gs_res _ y _ hy _).trans ((gs_appLE pm _ _ _ _ y hy.1 _).trans ((H _ (𝟙 _) y i j hi hj).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans (congrArg Units.val ?_)) (gs_res _ y _ hy _))))))` and prove the remaining obligations. Conclude with `(gs_secMaps w i j (𝟙 _) y hi hj).trans (zpow_one _).symm`. Introduce `i e`. Take `⟨i, rfl⟩ : ∃ i', i = fun _ => i'` from `⟨i 0, fin_one_eq i⟩`.

Both sides reduce to the same expression. Introduce and unpack `⟨t, h1, h2⟩ Z r z i j hi hj`. Establish `hm : r z ∈ LB.wchart (L.pull F) (fun _ : Fin 1 => q') (fun _ _ => i) ⊓ LB.wchart L' (fun _ : Fin 1 => q') (fun _ => j)` using `⟨Set.mem_iInter.2 fun _ => mem_pull.2 hi, Set.mem_iInter.2 fun _ => hj⟩`. Establish `e1` using `congrArg (gs r z _) (h2 (fun _ => i) (le fun _ _ => i))`. Establish `e2` using `congrArg (gs r z _) (h1 (fun _ _ => i, fun _ => j))`.

Use `(gs_appLE pm _ _ _ r z hm.1 _).symm.trans (e1.trans ((gs_res r z _ hm _).symm.trans (e2.trans ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ hm _).trans (congrArg Units.val ?_)) (gs_res r z _ hm _))))))` and prove the remaining obligations. Conclude with `(gs_secMaps w i j r z hi hj).trans (zpow_one _).symm`.
-/
theorem ptOver_iff_middle (h : pm ≫ q = q' ≫ F) (w : LB.Iso L' (L.pull F))
    (s' : LB.Sec (LB.LinComb L' (K := Fin 1) (fun _ => q') (fun _ => 1)))
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => q) (fun _ => 1))) :
    PtOver w pm 1 s' s ↔ ∃ t : LB.Sec (LB.LinComb (L.pull F) (K := Fin 1) (fun _ => q') (fun _ => 1)),
      SecMaps (LB.linCombIso w (K := Fin 1) (fun _ => q') (fun _ => 1)) s' t ∧
      ∀ (i : Fin 1 → L.ι) (e : (LB.LinComb (L.pull F) (K := Fin 1) (fun _ => q') (fun _ => 1)).U (fun _ _ => i 0) ≤
          pm ⁻¹ᵁ (LB.LinComb L (K := Fin 1) (fun _ => q) (fun _ => 1)).U i),
        (pm.appLE _ _ e).hom (s.f i) = t.f (fun _ _ => i 0) := by
  have le : ∀ J : Fin 1 → PUnit → L.ι, LB.wchart (L.pull F) (fun _ : Fin 1 => q') J ≤
      pm ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => q) (fun _ => J 0 PUnit.unit) :=
    fun J y hy => (mem_sq h y _).2 (mem_pull.1 (Set.mem_iInter.1 hy 0))
  constructor
  · intro H
    refine ⟨⟨fun J => (pm.appLE _ _ (le J)).hom (s.f fun _ => J 0 PUnit.unit), fun J J' => fn_ext fun y hy => ?_⟩,
      ?_, ?_⟩
    · have a := le J hy.1
      have a' := le J' hy.2
      refine (gs_res _ y _ hy _).trans ((gs_appLE pm _ _ _ _ y hy.1 _).trans ((gs_compat s _ y a a').trans
        (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans (congrArg Units.val ?_))
          ((gs_res _ y _ hy _).trans (gs_appLE pm _ _ _ _ y hy.2 _)))))))
      refine (gm_linComb (L.pull F) (fun _ : Fin 1 => q') (fun _ => 1) (𝟙 _) y J J' hy.1 hy.2).trans (Eq.trans ?_
        (gm_linComb L (fun _ : Fin 1 => q) (fun _ => 1) (𝟙 _ ≫ pm) y _ _ a a').symm)
      rw [Fin.prod_univ_one, Fin.prod_univ_one, Category.assoc, h, ← Category.assoc]
      exact congrArg (· ^ (1 : ℤ)) (gm_pull_g L F _ y _ _ (Set.mem_iInter.1 hy.1 0) (Set.mem_iInter.1 hy.2 0))
    · rintro ⟨J, j⟩
      obtain ⟨i, rfl⟩ : ∃ i, J = fun _ _ => i := ⟨J 0 PUnit.unit, fin_one_eq J⟩
      obtain ⟨j, rfl⟩ : ∃ j', j = fun _ => j' := ⟨j 0, fin_one_eq j⟩
      refine fn_ext fun y hy => ?_
      have hi : F (q' y) ∈ L.U i := mem_pull.1 (Set.mem_iInter.1 hy.1 0)
      have hj : q' y ∈ L'.U j := Set.mem_iInter.1 hy.2 0
      refine (gs_res _ y _ hy _).trans ((gs_appLE pm _ _ _ _ y hy.1 _).trans ((H _ (𝟙 _) y i j hi hj).trans
        (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans (congrArg Units.val ?_))
          (gs_res _ y _ hy _))))))
      exact (gs_secMaps w i j (𝟙 _) y hi hj).trans (zpow_one _).symm
    · intro i e
      obtain ⟨i, rfl⟩ : ∃ i', i = fun _ => i' := ⟨i 0, fin_one_eq i⟩
      rfl
  · rintro ⟨t, h1, h2⟩ Z r z i j hi hj
    have hm : r z ∈ LB.wchart (L.pull F) (fun _ : Fin 1 => q') (fun _ _ => i) ⊓
        LB.wchart L' (fun _ : Fin 1 => q') (fun _ => j) :=
      ⟨Set.mem_iInter.2 fun _ => mem_pull.2 hi, Set.mem_iInter.2 fun _ => hj⟩
    have e1 := congrArg (gs r z _) (h2 (fun _ => i) (le fun _ _ => i))
    have e2 := congrArg (gs r z _) (h1 (fun _ _ => i, fun _ => j))
    refine (gs_appLE pm _ _ _ r z hm.1 _).symm.trans (e1.trans ((gs_res r z _ hm _).symm.trans (e2.trans
      ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ hm _).trans (congrArg Units.val ?_))
        (gs_res r z _ hm _))))))
    exact (gs_secMaps w i j r z hi hj).trans (zpow_one _).symm

/- English proof (translation)
Substitute `hq` using the available equality. Introduce `Z r z i j hi hj`. Establish `e : (LB.LinComb L' (K` using `Fin 1) (fun _ => pn ≫ q') (fun _ => k)).U (fun _ => j) ≤ pn ⁻¹ᵁ (LB.LinComb L' (K := Fin 1) (fun _ => q') (fun _ => k)).U fun _ => j := fun y hy => Set.mem_iInter.2 fun a => Set.mem_iInter.1 hy a`. Rewrite using `[← hs _ e, gs_appLE pn _ _ e r z (Set.mem_iInter.2 fun _ => hj), ← Category.assoc, ← Category.assoc]`. Conclude with `H Z (r ≫ pn) z i j hi hj`.
-/
theorem PtOver.comp {Y'' : Scheme.{0}} {q'' : Y'' ⟶ X'} {pn : Y'' ⟶ Y'} (hq : pn ≫ q' = q'') {w : LB.Iso L' (L.pull F)}
    {k : ℤ} {s' : LB.Sec (LB.LinComb L' (K := Fin 1) (fun _ => q') (fun _ => k))}
    {s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => q) (fun _ => k))} (H : PtOver w pm k s' s)
    {s'' : LB.Sec (LB.LinComb L' (K := Fin 1) (fun _ => q'') (fun _ => k))}
    (hs : ∀ (j : Fin 1 → L'.ι) (e : (LB.LinComb L' (K := Fin 1) (fun _ => q'') (fun _ => k)).U j ≤
      pn ⁻¹ᵁ (LB.LinComb L' (K := Fin 1) (fun _ => q') (fun _ => k)).U j), (pn.appLE _ _ e).hom (s'.f j) = s''.f j) :
    PtOver w (pn ≫ pm) k s'' s := by
  subst hq
  intro Z r z i j hi hj
  have e : (LB.LinComb L' (K := Fin 1) (fun _ => pn ≫ q') (fun _ => k)).U (fun _ => j) ≤
      pn ⁻¹ᵁ (LB.LinComb L' (K := Fin 1) (fun _ => q') (fun _ => k)).U fun _ => j :=
    fun y hy => Set.mem_iInter.2 fun a => Set.mem_iInter.1 hy a
  rw [← hs _ e, gs_appLE pn _ _ e r z (Set.mem_iInter.2 fun _ => hj), ← Category.assoc, ← Category.assoc]
  exact H Z (r ≫ pn) z i j hi hj

end Calc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

section Half

/- English proof (translation)
Establish `h0 : l.M ≠ 0` using `by have := l.three_le; omega`. Establish `h2` using `l₂.prod`. Rewrite `h2` using `[hJ, hM, Ideal.map_mul, _root_.mul_mul_mul_comm, l.prod, Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton]`. Use `mul_left_cancel₀ ?_ h2` and prove the remaining obligations. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`.

Conclude with `h0` after adjusting the coercions.
-/
theorem mul_conj_eq {l₂ : Level H} {p : ℕ} {J : Ideal (𝓞 E)} (hM : l₂.M = l.M * p) (hJ : l₂.Mb = l.Mb * J) :
    J * J.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(p : 𝓞 E)} := by
  have h0 : l.M ≠ 0 := by have := l.three_le; omega
  have h2 := l₂.prod
  rw [hJ, hM, Ideal.map_mul, _root_.mul_mul_mul_comm, l.prod, Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton] at h2
  refine mul_left_cancel₀ ?_ h2
  rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  exact_mod_cast h0

/- English proof (translation)
Establish `h1 : Ideal.span {(p : 𝓞 E)} ≤ J` using `mul_conj_eq hM hJ ▸ Ideal.mul_le_left`. Use `le_antisymm (sup_le (hJ ▸ Ideal.mul_le_right) h1) fun x hx => ?_` and prove the remaining obligations. Take `⟨u, v, huv⟩` from `Nat.isCoprime_iff_coprime.2 hp`. Establish `hMm : (l.M : 𝓞 E) ∈ l.Mb` using `(Ideal.mul_le_inf (level_mem_mul l)).1`. Establish `e : x = (l.M : 𝓞 E) * ((v : 𝓞 E) * x) + ((u : 𝓞 E) * x) * p`.

Establish `: (u : 𝓞 E) * p + v * l.M = 1` using `by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) huv`. Take the linear combination `(-x) * this`. Rewrite using `[e]`. Conclude with `Submodule.add_mem_sup (hJ ▸ Ideal.mul_mem_mul hMm (J.mul_mem_left _ hx)) (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))`.
-/
theorem half_eq {l₂ : Level H} {p : ℕ} {J : Ideal (𝓞 E)} (hM : l₂.M = l.M * p) (hp : p.Coprime l.M)
    (hJ : l₂.Mb = l.Mb * J) : l₂.Mb ⊔ Ideal.span {(p : 𝓞 E)} = J := by
  have h1 : Ideal.span {(p : 𝓞 E)} ≤ J := mul_conj_eq hM hJ ▸ Ideal.mul_le_left
  refine le_antisymm (sup_le (hJ ▸ Ideal.mul_le_right) h1) fun x hx => ?_
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hp
  have hMm : (l.M : 𝓞 E) ∈ l.Mb := (Ideal.mul_le_inf (level_mem_mul l)).1
  have e : x = (l.M : 𝓞 E) * ((v : 𝓞 E) * x) + ((u : 𝓞 E) * x) * p := by
    have : (u : 𝓞 E) * p + v * l.M = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) huv
    linear_combination (-x) * this
  rw [e]
  exact Submodule.add_mem_sup (hJ ▸ Ideal.mul_mem_mul hMm (J.mul_mem_left _ hx))
    (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

/- English proof (translation)
The claim follows from `a.coprime.coprime_dvd_right (Nat.dvd_lcm_left _ _)`.
-/
theorem coprime_M (a : IsAuxiliarySplitSquarefreeLevel l) : a.p.Coprime l.M := a.coprime.coprime_dvd_right (Nat.dvd_lcm_left _ _)

/- English proof (translation)
Take `⟨J, hJ⟩` from `Ideal.dvd_iff_le.2 a.dvd.2.1`. Rewrite using `[show a.named = J from half_eq a.M_eq (coprime_M a) hJ, hJ]`.
-/
theorem Mb_eq (a : IsAuxiliarySplitSquarefreeLevel l) : a.l₂.Mb = l.Mb * a.named := by
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 a.dvd.2.1
  rw [show a.named = J from half_eq a.M_eq (coprime_M a) hJ, hJ]

/- English proof (translation)
The claim follows from `eq_top_iff.2 (a.l₂.coprime.ge.trans (sup_le_sup le_sup_left (Ideal.map_mono le_sup_left)))`.
-/
theorem named_sup (a : IsAuxiliarySplitSquarefreeLevel l) : a.named ⊔ a.named.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ :=
  eq_top_iff.2 (a.l₂.coprime.ge.trans (sup_le_sup le_sup_left (Ideal.map_mono le_sup_left)))

end Half

variable {Xo : Moduli D l} {c : Coeff l}

abbrev coverDat {a : IsAuxiliarySplitSquarefreeLevel l} (C : Cover Xo c a) (n : ℕ) (nab₂ : NabV C.Xo₂ C.c₂) (f : Rul C.Xo₂ C.c₂)
    (φ : (Fin n → LevQ D a.l₂) → c.F) : DeltaDat Xo c n where
  pd := a.p
  I := a.named
  l₂ := a.l₂
  Xo₂ := C.Xo₂
  c₂ := C.c₂
  hF := C.field_eq.symm
  r := C.r
  m := C.m
  nab₂ := nab₂
  cδ := f
  φδ := φ

def LevelClauses {n : ℕ} (d : DeltaDat Xo c n) : Prop :=
  l.Dvd d.l₂ ∧ d.l₂.M = l.M * d.pd ∧ Nat.Coprime d.pd l.M ∧ d.l₂.Mb = l.Mb * d.I ∧
    d.I ⊔ d.I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧ d.EtaOK

def ExtraClauses {n : ℕ} (d : DeltaDat Xo c n) : Prop :=
  (d.pd.Prime ∨ d.pd = 1) ∧ Nat.Coprime d.pd l.A ∧ d.l₂.A = l.A ∧
    ∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ spMap (IntermediateField.inclusion h).toRingHom

/- English proof (translation)
The claim follows from `GlobalTheory.iso_eq_of_maps_along_section (S := Xo₂.X) (exists_chart Xo₂.univ.t.PP.isLB) (fun y => (exists_chart Xo.univ.t.PP.isLB (m.φ y)).elim fun _ hj => ⟨fun _ => _, mem_pull.2 hj⟩) Xo₂.univ.t.G.hom (eSec Xo₂.univ.t.G) (Over.w η[Xo₂.univ.t.G]) (GlobalTheory.globalFns_holds _ …`.
-/
theorem rigid_unique {l₂ : Level H} {Xo₂ : Moduli D l₂} {r : Xo₂.X ⟶ Xo.X} (m : SABMap Xo₂.univ.t Xo.univ.t r)
    {w w' : LB.Iso Xo₂.univ.t.PP.L (Xo.univ.t.PP.L.pull m.φ)} (g : w.IsGen) (g' : w'.IsGen)
    (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec Xo₂.univ.t.G) (fun _ => 1)) Xo₂.univ.t.PP.rig
      (m.cm.rigPull Xo.univ.t.PP.L Xo.univ.t.PP.rig))
    (h' : LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec Xo₂.univ.t.G) (fun _ => 1)) Xo₂.univ.t.PP.rig
      (m.cm.rigPull Xo.univ.t.PP.L Xo.univ.t.PP.rig)) : w = w' :=
  GlobalTheory.iso_eq_of_maps_along_section (S := Xo₂.X) (exists_chart Xo₂.univ.t.PP.isLB)
    (fun y => (exists_chart Xo.univ.t.PP.isLB (m.φ y)).elim fun _ hj => ⟨fun _ => _, mem_pull.2 hj⟩)
    Xo₂.univ.t.G.hom (eSec Xo₂.univ.t.G) (Over.w η[Xo₂.univ.t.G])
    (GlobalTheory.globalFns_holds _ _ ⟨Xo₂.univ.t.semi.comm, Xo₂.univ.t.semi.smooth, Xo₂.univ.proper,
      Xo₂.univ.t.semi.geomConnected⟩).2 g g' h h'

section Cover

variable {a : IsAuxiliarySplitSquarefreeLevel l} (C : Cover Xo c a) (n : ℕ) (nab₂ : NabV C.Xo₂ C.c₂) (f : Rul C.Xo₂ C.c₂)
  (φ : (Fin n → LevQ D a.l₂) → c.F)

/- English proof (translation)
Rewrite using `[a.A_eq, Nat.div_self l.A_pos]`.
-/
theorem div_A (a : IsAuxiliarySplitSquarefreeLevel l) : a.l₂.A / l.A = 1 := by rw [a.A_eq, Nat.div_self l.A_pos]

/- English proof (translation)
Assemble the required witnesses or components as `⟨a.dvd, a.M_eq, coprime_M a, Mb_eq a, named_sup a, C.level.2.1, fun x => by change (C.Xo₂.univ.etaA x ^ (a.l₂.A / l.A)).left ≫ C.m.φ = _ rw [div_A, pow_one] exact C.level.2.2 x⟩`.
-/
theorem levelClauses_coverDat : LevelClauses (coverDat C n nab₂ f φ) :=
  ⟨a.dvd, a.M_eq, coprime_M a, Mb_eq a, named_sup a, C.level.2.1, fun x => by
    change (C.Xo₂.univ.etaA x ^ (a.l₂.A / l.A)).left ≫ C.m.φ = _
    rw [div_A, pow_one]
    exact C.level.2.2 x⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨a.prime_or_one, a.coprime.coprime_dvd_right (Nat.dvd_lcm_right _ _), a.A_eq, fun _ => C.level.1⟩`.
-/
theorem extraClauses_coverDat : ExtraClauses (coverDat C n nab₂ f φ) :=
  ⟨a.prime_or_one, a.coprime.coprime_dvd_right (Nat.dvd_lcm_right _ _), a.A_eq, fun _ => C.level.1⟩

/- English proof (translation)
The claim follows from `Spec.map_id _`.
-/
theorem spMap_id (S : Type) [CommRing S] : spMap (RingHom.id S) = 𝟙 _ := Spec.map_id _

/- English proof (translation)
Establish `: dualMap (RingHom.id S) = RingHom.id _` using `RingHom.ext fun z => TrivSqZeroExt.inl_fst_add_inr_snd_eq z`. Rewrite using `[this]`. Conclude with `Spec.map_id _`.
-/
theorem spMap_dual_id (S : Type) [CommRing S] : spMap (dualMap (RingHom.id S)) = 𝟙 _ := by
  have : dualMap (RingHom.id S) = RingHom.id _ := RingHom.ext fun z => TrivSqZeroExt.inl_fst_add_inr_snd_eq z
  rw [this]; exact Spec.map_id _

/- English proof (translation)
Unfold `Cover.LiesOver Cover.IsGroupMap`. Rewrite using `[spMap_id, spMap_dual_id]`. Simplify using `only [Category.id_comp, Category.comp_id]`. Use `and_congr ⟨fun h x => (RingHom.congr_fun h x).symm, fun h => RingHom.ext fun x => (h x).symm⟩ (and_congr Iff.rfl (and_congr Iff.rfl ?_))` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨pm, ⟨h1, h2⟩, h3⟩`. Take `⟨t, t1, t2⟩` from `(ptOver_iff_middle h1 C.w y₂.s y.s).1 ((ptOver_iff_charts h1 C.w 1 y₂.s y.s).2 h3)`. Conclude with `⟨C.w, pm, t, C.bundle.1, C.bundle.2.1, h1, h2, t1, t2⟩`. Introduce and unpack `⟨w, pm, t, g, hr, h1, h2, t1, t2⟩`. Take `rfl : w = C.w` from `rigid_unique C.m g C.bundle.1 hr C.bundle.2.1`.

Conclude with `⟨pm, ⟨h1, h2⟩, (ptOver_iff_charts h1 C.w 1 y₂.s y.s).1 ((ptOver_iff_middle h1 C.w y₂.s y.s).2 ⟨t, t1, t2⟩)⟩`.
-/
theorem liesOver_iff {S : Type} [CommRing S] [Algebra c.F S] [Algebra C.c₂.F S] (y₂ : FrPt C.Xo₂ C.c₂ S)
    (y : FrPt Xo c S) :
    C.LiesOver (RingHom.id S) y₂ y ↔
      (∀ x : c.F, algebraMap C.c₂.F S (C.incl x) = algebraMap c.F S x) ∧
        FrOver (coverDat C n nab₂ f φ) (k := S) y₂ y := by
  unfold Cover.LiesOver Cover.IsGroupMap
  rw [spMap_id, spMap_dual_id]
  simp only [Category.id_comp, Category.comp_id]
  refine and_congr ⟨fun h x => (RingHom.congr_fun h x).symm, fun h => RingHom.ext fun x => (h x).symm⟩
    (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  constructor
  · rintro ⟨pm, ⟨h1, h2⟩, h3⟩
    obtain ⟨t, t1, t2⟩ := (ptOver_iff_middle h1 C.w y₂.s y.s).1 ((ptOver_iff_charts h1 C.w 1 y₂.s y.s).2 h3)
    exact ⟨C.w, pm, t, C.bundle.1, C.bundle.2.1, h1, h2, t1, t2⟩
  · rintro ⟨w, pm, t, g, hr, h1, h2, t1, t2⟩
    obtain rfl : w = C.w := rigid_unique C.m g C.bundle.1 hr C.bundle.2.1
    exact ⟨pm, ⟨h1, h2⟩, (ptOver_iff_charts h1 C.w 1 y₂.s y.s).1 ((ptOver_iff_middle h1 C.w y₂.s y.s).2 ⟨t, t1, t2⟩)⟩

end Cover

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, h2, h3, h4, -, h6, h7⟩, h8, h9, h10, h11⟩`. Take `⟨pd, I, l₂, Xo₂, c₂, hF, r, m, nab₂, f, φ⟩` from `d`. Simplify using `only at h1 h2 h3 h4 h6 h7 h8 h9 h10 h11`. Set `a : IsAuxiliarySplitSquarefreeLevel l` to `⟨pd, h8, (Nat.Coprime.mul_right h3 h9).coprime_dvd_right (Nat.lcm_dvd_mul _ _), l₂, h1, h2, h10⟩`.

Take `⟨w, hw⟩` from `exists_bundleIso m`. Take `rfl : l₂.Mb ⊔ Ideal.span {(pd : 𝓞 E)} = I` from `half_eq h2 h3 h4`. Use `⟨a, ⟨Xo₂, c₂, hF.symm, r, m, w, ⟨h11 _, h6, fun x => ?_⟩, hw⟩, nab₂, f, φ, rfl⟩` and prove the remaining obligations. Use `h7 x` as an intermediate fact. Rewrite `this` using `[h10, Nat.div_self l.A_pos, pow_one]`. Then use the resulting hypothesis.

Introduce and unpack `⟨a, C, nab₂, f, φ, rfl⟩`. Conclude with `⟨levelClauses_coverDat C n nab₂ f φ, extraClauses_coverDat C n nab₂ f φ⟩`.
-/
theorem exists_cover_iff {n : ℕ} (d : DeltaDat Xo c n) :
    LevelClauses d ∧ ExtraClauses d ↔ ∃ (a : IsAuxiliarySplitSquarefreeLevel l) (C : Cover Xo c a) (nab₂ : NabV C.Xo₂ C.c₂)
      (f : Rul C.Xo₂ C.c₂) (φ : (Fin n → LevQ D a.l₂) → c.F), d = coverDat C n nab₂ f φ := by
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, -, h6, h7⟩, h8, h9, h10, h11⟩
    obtain ⟨pd, I, l₂, Xo₂, c₂, hF, r, m, nab₂, f, φ⟩ := d
    dsimp only at h1 h2 h3 h4 h6 h7 h8 h9 h10 h11
    let a : IsAuxiliarySplitSquarefreeLevel l := ⟨pd, h8, (Nat.Coprime.mul_right h3 h9).coprime_dvd_right (Nat.lcm_dvd_mul _ _), l₂, h1, h2, h10⟩
    obtain ⟨w, hw⟩ := exists_bundleIso m
    obtain rfl : l₂.Mb ⊔ Ideal.span {(pd : 𝓞 E)} = I := half_eq h2 h3 h4
    refine ⟨a, ⟨Xo₂, c₂, hF.symm, r, m, w, ⟨h11 _, h6, fun x => ?_⟩, hw⟩, nab₂, f, φ, rfl⟩
    have := h7 x
    rwa [h10, Nat.div_self l.A_pos, pow_one] at this
  · rintro ⟨a, C, nab₂, f, φ, rfl⟩
    exact ⟨levelClauses_coverDat C n nab₂ f φ, extraClauses_coverDat C n nab₂ f φ⟩

/- English proof (translation)
Introduce and unpack `⟨⟨p, a1, a2, l₂, a3, a4, a5⟩, ⟨Xo₂, c₂, hF, r, m, w, hl, hb⟩, nab₂, f, φ⟩ ⟨⟨p', a1', a2', l₂', a3', a4', a5'⟩, ⟨Xo₂', c₂', hF', r', m', w', hl', hb'⟩, nab₂', f', φ'⟩ h`. Simplify using `only [coverDat, DeltaDat.mk.injEq] at h`. Take `⟨rfl, -, rfl, h⟩` from `h`. Simplify using `only [heq_eq_eq] at h`. Take `⟨rfl, rfl, h⟩` from `h`.

Simplify using `only [heq_eq_eq] at h`. Take `⟨rfl, h⟩` from `h`. Simplify using `only [heq_eq_eq] at h`. Take `⟨rfl, h, rfl, rfl⟩` from `h`. Take `rfl : @nab₂ = @nab₂'` from `h`.

Take `rfl : w = w'` from `rigid_unique m hb.1 hb'.1 hb.2.1 hb'.2.1`. Both sides reduce to the same expression.
-/
theorem coverDat_injective (n : ℕ) : Function.Injective
    fun t : Σ (a : IsAuxiliarySplitSquarefreeLevel l) (C : Cover Xo c a), NabV C.Xo₂ C.c₂ × Rul C.Xo₂ C.c₂ × ((Fin n → LevQ D a.l₂) → c.F) =>
      coverDat t.2.1 n t.2.2.1 t.2.2.2.1 t.2.2.2.2 := by
  rintro ⟨⟨p, a1, a2, l₂, a3, a4, a5⟩, ⟨Xo₂, c₂, hF, r, m, w, hl, hb⟩, nab₂, f, φ⟩
    ⟨⟨p', a1', a2', l₂', a3', a4', a5'⟩, ⟨Xo₂', c₂', hF', r', m', w', hl', hb'⟩, nab₂', f', φ'⟩ h
  simp only [coverDat, DeltaDat.mk.injEq] at h
  obtain ⟨rfl, -, rfl, h⟩ := h
  simp only [heq_eq_eq] at h
  obtain ⟨rfl, rfl, h⟩ := h
  simp only [heq_eq_eq] at h
  obtain ⟨rfl, h⟩ := h
  simp only [heq_eq_eq] at h
  obtain ⟨rfl, h, rfl, rfl⟩ := h
  obtain rfl : @nab₂ = @nab₂' := h
  obtain rfl : w = w' := rigid_unique m hb.1 hb'.1 hb.2.1 hb'.2.1
  rfl

section Rule

def fnRule (g : Γ(Xo.XF c, ⊤)) : Rul Xo c := fun _ y => fnAt (basePt y) g

/- English proof (translation)
Establish `e` using `congrArg (fun k => k.hom (y.appTop.hom g)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ))`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at e`. Conclude with `e`.
-/
theorem fnAt_comp {X : Scheme.{0}} {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (y : Sp S ⟶ X) (g : Γ(X, ⊤)) :
    fnAt (spMap ψ ≫ y) g = ψ (fnAt y g) := by
  have e := congrArg (fun k => k.hom (y.appTop.hom g)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

/- English proof (translation)
Use `pullback.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, basePt, basePt, pullback.lift_fst, pullback.lift_fst, h.1]`. Rewrite using `[Category.assoc, basePt, basePt, pullback.lift_snd, pullback.lift_snd, GlobalTheory.Frames.FramedBaseChange.spMap_comp_spMap]`. Conclude with `congrArg spMap ψ.comp_algebraMap.symm`.
-/
theorem basePt_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {ψ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap ψ y z) : basePt z = spMap ψ.toRingHom ≫ basePt y := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, basePt, basePt, pullback.lift_fst, pullback.lift_fst, h.1]
  · rw [Category.assoc, basePt, basePt, pullback.lift_snd, pullback.lift_snd,
      GlobalTheory.Frames.FramedBaseChange.spMap_comp_spMap]
    exact congrArg spMap ψ.comp_algebraMap.symm

/- English proof (translation)
Use `⟨fun p q ψ y z h => ?_, fun p t y y' h => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `fnAt (basePt z) g = ψ (fnAt (basePt y) g)`. Rewrite using `[basePt_frMap h, fnAt_comp]`. Both sides reduce to the same expression. Establish `e : basePt y' = basePt y`.

Use `pullback.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[basePt, basePt, pullback.lift_fst, pullback.lift_fst, h.1]`. Rewrite using `[basePt, basePt, pullback.lift_snd, pullback.lift_snd]`. Apply the tactic sequence `have e' : wchar (ex D 0 0) t = 1 := Finset.prod_eq_one fun i _ => by cases i <;> exact pow_zero _`. Express the relevant statement in the definitionally equal form `fnAt (basePt y') g = _ * fnAt (basePt y) g`.

Rewrite using `[e, e', _root_.one_mul]`.
-/
theorem fnRule_mem (g : Γ(Xo.XF c, ⊤)) : fnRule g ∈ sec Xo c 0 0 := by
  refine ⟨fun p q ψ y z h => ?_, fun p t y y' h => ?_⟩
  · change fnAt (basePt z) g = ψ (fnAt (basePt y) g)
    rw [basePt_frMap h, fnAt_comp]
    rfl
  · have e : basePt y' = basePt y := by
      refine pullback.hom_ext ?_ ?_
      · rw [basePt, basePt, pullback.lift_fst, pullback.lift_fst, h.1]
      · rw [basePt, basePt, pullback.lift_snd, pullback.lift_snd]
    have e' : wchar (ex D 0 0) t = 1 := Finset.prod_eq_one fun i _ => by cases i <;> exact pow_zero _
    change fnAt (basePt y') g = _ * fnAt (basePt y) g
    rw [e, e', _root_.one_mul]

/- English proof (translation)
Establish `h` using `GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H D l Xo c S y`. Unfold `evR evalAt`. Rewrite using `[dif_pos h, basePt_frMap h.choose_spec.choose_spec.choose_spec, fnAt_comp]`. Both sides reduce to the same expression.
-/
theorem evR_fnRule (g : Γ(Xo.XF c, ⊤)) {S : Type} [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S) :
    evR Xo c (fnRule g) y = fnAt (basePt y) g := by
  have h := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H D l Xo c S y
  unfold evR evalAt
  rw [dif_pos h, basePt_frMap h.choose_spec.choose_spec.choose_spec, fnAt_comp]
  rfl

/- English proof (translation)
Rewrite using `[fnAt, map_one, map_one]`.
-/
theorem fnAt_one {X : Scheme.{0}} {S : Type} [CommRing S] (y : Sp S ⟶ X) : fnAt y (1 : Γ(X, ⊤)) = 1 := by
  rw [fnAt, map_one, map_one]

end Rule

section Law

variable {a : IsAuxiliarySplitSquarefreeLevel l} (C : Cover Xo c a)

def GeometricLifts : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra C.c₂.F k],
    algebraMap c.F k = (algebraMap C.c₂.F k).comp C.incl →
    ∀ y : FrPt Xo c k, ∃ y₂ : FrPt C.Xo₂ C.c₂ k, C.LiesOver (RingHom.id k) y₂ y

end Law

section Coefficients

open GlobalTheory.ShortDatumEq

variable {a : IsAuxiliarySplitSquarefreeLevel l}

variable {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab) {n : ℕ}

end Coefficients

/- English proof (translation)
Introduce `g g' h`. Use `fn_ext fun z _ => ?_` and prove the remaining obligations. Take `⟨p, j, y, ⟨hj, h1, h2⟩, z, rfl⟩` from `GlobalTheory.Frames.exists_openChart_testRing GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H D l Xo c z`. Establish `e : basePt y = j` using `pullback.hom_ext (by rw [basePt, pullback.lift_fst, h1]) (by rw [basePt, pullback.lift_snd, h2])`. Establish `e' : fnAt j g = fnAt j g'` using `e ▸ congrFun (congrFun h p) y`.

Establish `e'' : j.appTop.hom g = j.appTop.hom g'` using `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of p.R)).hom).1 e'`. Use `(ConcreteCategory.bijective_of_isIso (j.stalkMap z)).1 ?_` and prove the remaining obligations. Use `(gs_stalkMap j z ⊤ trivial g).symm.trans (Eq.trans ?_ (gs_stalkMap j z ⊤ trivial g'))` and prove the remaining obligations. Rewrite using `[gs_eq j z ⊤ trivial, gs_eq j z ⊤ trivial]`. Conclude with `congrArg _ e''`.
-/
theorem fnRule_injective : Function.Injective (fnRule (Xo := Xo) (c := c)) := by
  intro g g' h
  refine fn_ext fun z _ => ?_
  obtain ⟨p, j, y, ⟨hj, h1, h2⟩, z, rfl⟩ :=
    GlobalTheory.Frames.exists_openChart_testRing GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H D l Xo c z
  have e : basePt y = j := pullback.hom_ext (by rw [basePt, pullback.lift_fst, h1]) (by rw [basePt, pullback.lift_snd, h2])
  have e' : fnAt j g = fnAt j g' := e ▸ congrFun (congrFun h p) y
  have e'' : j.appTop.hom g = j.appTop.hom g' :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of p.R)).hom).1 e'
  refine (ConcreteCategory.bijective_of_isIso (j.stalkMap z)).1 ?_
  refine (gs_stalkMap j z ⊤ trivial g).symm.trans (Eq.trans ?_ (gs_stalkMap j z ⊤ trivial g'))
  rw [gs_eq j z ⊤ trivial, gs_eq j z ⊤ trivial]
  exact congrArg _ e''

section Datum

open GlobalTheory.ShortDatumEq

variable {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab) (n : ℕ)

abbrev toDat : DeltaDat Xo c n :=
  coverDat Δ.cov n Δ.nab₂ (fnRule Δ.fn) fun q => (IntermediateField.equivOfEq Δ.cov.field_eq).symm
    ((Nat.card (Fin n → NamedCl D Δ.a.l₂) : Δ.cov.c₂.F) * Δ.combinedCoeff 0 q)

variable {n}

/- English proof (translation)
Take `⟨s, t, hst⟩` from `Nat.isCoprime_iff_coprime.2 (coprime_M a)`. Use `⟨fun b => s • levRep (q b), fun b => t • levRep (q b), funext fun b => ?_⟩` and prove the remaining obligations. Rewrite using `[← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, mul_comm _ s, mul_comm _ t, hst, one_smul, mk_levRep]`.
-/
theorem exists_split (a : IsAuxiliarySplitSquarefreeLevel l) (q : Fin n → LevQ D a.l₂) :
    ∃ u₁ u₂ : Fin n → D.La, q = fun b => Submodule.Quotient.mk (a.p • u₁ b + l.M • u₂ b) := by
  obtain ⟨s, t, hst⟩ := Nat.isCoprime_iff_coprime.2 (coprime_M a)
  refine ⟨fun b => s • levRep (q b), fun b => t • levRep (q b), funext fun b => ?_⟩
  rw [← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, mul_comm _ s, mul_comm _ t, hst, one_smul,
    mk_levRep]

end Datum

def coverEquiv (Xo : Moduli D l) (c : Coeff l) (n : ℕ) :
    (Σ (a : IsAuxiliarySplitSquarefreeLevel l) (C : Cover Xo c a), NabV C.Xo₂ C.c₂ × Rul C.Xo₂ C.c₂ × ((Fin n → LevQ D a.l₂) → c.F)) ≃
      {d : DeltaDat Xo c n // LevelClauses d ∧ ExtraClauses d} :=
  Equiv.ofBijective
    (fun t => ⟨coverDat t.2.1 n t.2.2.1 t.2.2.2.1 t.2.2.2.2,
      levelClauses_coverDat _ _ _ _ _, extraClauses_coverDat _ _ _ _ _⟩)
    ⟨fun _ _ h => coverDat_injective n (congrArg Subtype.val h), fun d => by
      obtain ⟨a, C, nab₂, f, φ, h⟩ := (exists_cover_iff d.1).1 d.2
      exact ⟨⟨a, C, nab₂, f, φ⟩, Subtype.ext h.symm⟩⟩

end GlobalTheory.LevelCoverCompare
