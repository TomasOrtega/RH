import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.JetGeo

open ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums

section Val
variable {A : Type} [CommRing A] {X Y Z : Scheme.{0}}

/- English proof (translation)
Distinguish the cases in `hx : ⊤ ≤ x ⁻¹ᵁ (q ⁻¹ᵁ W)`. Rewrite using `[Scheme.Hom.app_eq_appLE]`. Conclude with `GlobalTheory.ZH.FormCount.valR_appLE x q W _ le_rfl f hx`. Establish `hx' : ¬ ⊤ ≤ (x ≫ q) ⁻¹ᵁ W` using `hx`. Unfold `valR`.

Rewrite using `[dif_neg hx, dif_neg hx']`.
-/
theorem valR_app (x : Sp A ⟶ Y) (q : Y ⟶ X) (W : X.Opens) (f : Γ(X, W)) :
    valR x (q ⁻¹ᵁ W) ((q.app W).hom f) = valR (x ≫ q) W f := by
  by_cases hx : ⊤ ≤ x ⁻¹ᵁ (q ⁻¹ᵁ W)
  · rw [Scheme.Hom.app_eq_appLE]
    exact GlobalTheory.ZH.FormCount.valR_appLE x q W _ le_rfl f hx
  · have hx' : ¬ ⊤ ≤ (x ≫ q) ⁻¹ᵁ W := hx
    unfold valR
    rw [dif_neg hx, dif_neg hx']

/- English proof (translation)
Distinguish the cases in `h : ⊤ ≤ x ⁻¹ᵁ V`. Conclude with `GlobalTheory.ZH.CrdCalc.valR_res x e h f`. Establish `h' : ¬ ⊤ ≤ x ⁻¹ᵁ U` using `fun hU => h (hU.trans (x.preimage_mono e'))`. Unfold `valR`. Rewrite using `[dif_neg h, dif_neg h']`.
-/
theorem valR_res' (x : Sp A ⟶ X) {U V : X.Opens} (e : V ≤ U) (e' : U ≤ V) (f : Γ(X, U)) :
    valR x V (resG X e f) = valR x U f := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ V
  · exact GlobalTheory.ZH.CrdCalc.valR_res x e h f
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ U := fun hU => h (hU.trans (x.preimage_mono e'))
    unfold valR
    rw [dif_neg h, dif_neg h']

/- English proof (translation)
Establish `e' : h ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => h ≫ φ k) j` using `fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k`. Establish `e : LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j` using `fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k`. Express the relevant statement in the definitionally equal form `valR x _ (resG Z e ((h.app _).hom (c.s j).val)) = _`. Rewrite using `[valR_res' x e e']`. Conclude with `valR_app x h _ _`.
-/
theorem valR_pullGen (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y) (x : Sp A ⟶ Z) (j : K → L.ι) :
    valR x (LB.wchart L (fun k => h ≫ φ k) j) ((LB.pullGen L φ ε c h).s j).val =
      valR (x ≫ h) (LB.wchart L φ j) (c.s j).val := by
  have e' : h ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => h ≫ φ k) j :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have e : LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  change valR x _ (resG Z e ((h.app _).hom (c.s j).val)) = _
  rw [valR_res' x e e']
  exact valR_app x h _ _

end Val

/- English proof (translation)
Use `d.ex_add 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `mul_eq_left.1 this.symm`.
-/
theorem ex_zero {B : NumB ℂ} {g : ℕ} (d : AB B g) : d.ex 0 = 1 := by
  have := d.ex_add 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [ex_zero]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, d.ex_add, ih]`.
-/
theorem ex_sum {B : NumB ℂ} {g : ℕ} (d : AB B g) {J : Type} (s : Finset J) (v : J → Fin g → ℂ) :
    d.ex (∑ i ∈ s, v i) = ∏ i ∈ s, d.ex (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ex_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, d.ex_add, ih]

section Pts
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

/- English proof (translation)
Use `show _ ≫ (psum D.P.A (x3 D.P.A) I.down).left = _`. Rewrite using `[← Over.comp_left, psum_eq_prod, comp_prod]`. Establish `h3 : ∀ i, lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z))) ≫ x3 D.P.A i = ν.eA (d.ex (![x, y, z] i))`. Apply the tactic sequence `intro i; fin_cases i <;> simp [x3]`. Repeatedly rewrite using `[h3, ← map_prod, ← ex_sum]`.
-/
theorem thφ_pt (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) (I : thK.{0}) :
    (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left ≫ thφ D.P.A (x3 D.P.A) I =
      (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left := by
  show _ ≫ (psum D.P.A (x3 D.P.A) I.down).left = _
  rw [← Over.comp_left, psum_eq_prod, comp_prod]
  have h3 : ∀ i, lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z))) ≫ x3 D.P.A i =
      ν.eA (d.ex (![x, y, z] i)) := by
    intro i; fin_cases i <;> simp [x3]
  simp_rw [h3, ← map_prod, ← ex_sum]

end Pts

/- English proof (translation)
Introduce `R _ _ D _ N g ν d gm ⟨o, ho, hp⟩ χ χ' x y hx hy`. Establish `hρ : redE ℂ ≫ (TE R ℂ).hom = (TF (R` using `R) ℂ).hom := by`. Establish `e : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ` using `by ext; simp`. Simplify using `only [TE, Over.mk_hom, redE, spMap]`. Rewrite using `[← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]`.

Set `ρ : TF (R` to `R) ℂ ⟶ TE R ℂ := Over.homMk (redE ℂ) hρ`. Set `P3 : (Fin g → ℂ) → (TF (R` to `R) ℂ ⟶ G3 D.P.A) := fun z => lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))`. Set `q : DegPre.BF D ℂ ⟶ G3 D.P.A` to `lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') (DegPre.prB D ℂ))`. Set `h` to `(lift (DegPre.cT D (TE R ℂ) χ) (lift (DegPre.cT D (TE R ℂ) χ') gm.b))`. Establish `hb : ρ ≫ gm.b = ν.eA (d.ex 0)`.

Rewrite using `[ex_zero, map_one]`. Use `ext1`. Use `show redE ℂ ≫ gm.b.left = _`. Rewrite using `[← hp.1, ho.1]`. Both sides reduce to the same expression.

Establish `hred : ρ ≫ h = P3 0`. Simplify using `only [h, P3, comp_lift, hb, DegPre.cT, comp_toUnit_assoc]`. Rewrite using `[show toUnit _ ≫ D.c χ = ν.eA (d.ex x) from hx.symm, show toUnit _ ≫ D.c χ' = ν.eA (d.ex y) from hy.symm]`. Establish `hq : lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R` using `R) ℂ) gm.b ≫ q = h := by`. Simplify using `only [q, h, comp_lift, comp_toUnit_assoc, DegPre.prB, lift_snd, DegPre.cT]`.

Establish `hpt : ∀ z, ptB ν d z ≫ q.left = (P3 z).left`. Introduce `z`. Rewrite using `[ptB, ← Over.comp_left]`. Use `congr 1`. Simplify using `only [q, P3, comp_lift, comp_toUnit_assoc, DegPre.prB, lift_snd]`.

Rewrite using `[show toUnit _ ≫ D.c χ = ν.eA (d.ex x) from hx.symm, show toUnit _ ≫ D.c χ' = ν.eA (d.ex y) from hy.symm]`. Establish `e3 : ∀ z I, (P3 z).left ≫ thφ D.P.A (x3 D.P.A) I = (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left` using `fun z I => thφ_pt ν d x y z I`. Set `j0 : thK.{0} → D.P.L.ι` to `fun I => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left`. Set `W0` to `LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j0`. Use `⟨q.left ⁻¹ᵁ W0, (q.left.app W0).hom (D.cub.t.s j0).val, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `hj : (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ h.left ≫ thφ D.P.A (x3 D.P.A) k)) = j0`. Use function extensionality and compare the values at `I`. Rewrite using `[Category.id_comp, ← Category.assoc, show redE ℂ ≫ h.left = (P3 0).left from congrArg Over.Hom.left hred, e3]`. Use `Eq.trans ?_ (valR_app _ q.left W0 _).symm` and prove the remaining obligations. Rewrite using `[← Over.comp_left, hq]`.

Unfold `vE DegPre.cubAtT`. Use `(valR_pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t h.left (𝟙 _) _).trans ?_` and prove the remaining obligations. Rewrite using `[Category.id_comp]`. Establish `key : ∀ j j' : thK.{0} → D.P.L.ι, j = j' → valR h.left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j) (D.cub.t.s j).val = valR h.left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j') (D.cub.t.s j').val`. Introduce and unpack `_ _ rfl`.

Both sides reduce to the same expression. Conclude with `key _ _ hj`. Introduce `p _`. Express the relevant statement in the definitionally equal form `(ptB ν d 0 ≫ q.left).base p ∈ W0`. Rewrite using `[hpt]`.

Use `Set.mem_iInter.2 fun I => ?_` and prove the remaining obligations. Use `ν.good ((P3 0).left ≫ thφ D.P.A (x3 D.P.A) I) (Set.mem_univ p)` as an intermediate fact. Rewrite `this` using `[e3]`. Express the relevant statement in the definitionally equal form `((P3 0).left ≫ thφ D.P.A (x3 D.P.A) I).base p ∈ D.P.L.U (j0 I)`. Rewrite using `[e3]`.

Conclude with `this`. Introduce `z hz`. Use `⟨fun I p _ => ?_, ?_⟩` and prove the remaining obligations. Establish `hm : (ptB ν d z ≫ q.left).base p ∈ W0` using `hz (Set.mem_univ p)`. Rewrite `hm` using `[hpt]`.

Use `LB.wchart_le D.P.L (thφ D.P.A (x3 D.P.A)) j0 I hm` as an intermediate fact. Rewrite using `[← e3 z I]`. Conclude with `this`. Express the relevant statement in the definitionally equal form `valR (ptB ν d z) _ _ = valR _ _ _`. Use `(valR_app (ptB ν d z) q.left W0 _).trans ?_` and prove the remaining obligations.

Rewrite using `[hpt]`.
-/
theorem jet_geo : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
    (ν : NumOf D ℂ N) (d : AB N.toNumB g) (gm : GtPt D (TE R ℂ)),
    (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) →
    ∀ (χ χ' : D.X) (x y : Fin g → ℂ),
    ν.eA (d.ex x) = DegPre.cF D ℂ χ → ν.eA (d.ex y) = DegPre.cF D ℂ χ' →
    ∃ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)),
      vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
        valR (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) gm.b).left U f ∧
      ⊤ ≤ ptB ν d 0 ⁻¹ᵁ U ∧
      ∀ z, ⊤ ≤ ptB ν d z ⁻¹ᵁ U →
        (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ
          D.P.L.U (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)) ∧
        valF (ptB ν d z) U f =
          valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left
            (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) (fun I : thK.{0} => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left))
            (D.cub.t.s (fun I : thK.{0} => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)).val := by
  intro R _ _ D _ N g ν d gm ⟨o, ho, hp⟩ χ χ' x y hx hy
  classical

  have hρ : redE ℂ ≫ (TE R ℂ).hom = (TF (R := R) ℂ).hom := by
    have e : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
      ext; simp
    simp only [TE, Over.mk_hom, redE, spMap]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e, CommRingCat.ofHom_id, Spec.map_id,
      Category.id_comp]
  let ρ : TF (R := R) ℂ ⟶ TE R ℂ := Over.homMk (redE ℂ) hρ
  let P3 : (Fin g → ℂ) → (TF (R := R) ℂ ⟶ G3 D.P.A) := fun z =>
    lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))
  let q : DegPre.BF D ℂ ⟶ G3 D.P.A :=
    lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') (DegPre.prB D ℂ))
  let h := (lift (DegPre.cT D (TE R ℂ) χ) (lift (DegPre.cT D (TE R ℂ) χ') gm.b))
  have hb : ρ ≫ gm.b = ν.eA (d.ex 0) := by
    rw [ex_zero, map_one]
    ext1
    show redE ℂ ≫ gm.b.left = _
    rw [← hp.1, ho.1]
    rfl
  have hred : ρ ≫ h = P3 0 := by
    simp only [h, P3, comp_lift, hb, DegPre.cT, comp_toUnit_assoc]
    rw [show toUnit _ ≫ D.c χ = ν.eA (d.ex x) from hx.symm, show toUnit _ ≫ D.c χ' = ν.eA (d.ex y) from hy.symm]
  have hq : lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) gm.b ≫ q = h := by
    simp only [q, h, comp_lift, comp_toUnit_assoc, DegPre.prB, lift_snd, DegPre.cT]
  have hpt : ∀ z, ptB ν d z ≫ q.left = (P3 z).left := by
    intro z
    rw [ptB, ← Over.comp_left]
    congr 1
    simp only [q, P3, comp_lift, comp_toUnit_assoc, DegPre.prB, lift_snd]
    rw [show toUnit _ ≫ D.c χ = ν.eA (d.ex x) from hx.symm, show toUnit _ ≫ D.c χ' = ν.eA (d.ex y) from hy.symm]
  have e3 : ∀ z I, (P3 z).left ≫ thφ D.P.A (x3 D.P.A) I = (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left :=
    fun z I => thφ_pt ν d x y z I
  let j0 : thK.{0} → D.P.L.ι := fun I => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left
  let W0 := LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j0
  refine ⟨q.left ⁻¹ᵁ W0, (q.left.app W0).hom (D.cub.t.s j0).val, ?_, ?_, ?_⟩
  ·
    have hj : (fun k => ν.J (redE ℂ ≫ 𝟙 _ ≫ h.left ≫ thφ D.P.A (x3 D.P.A) k)) = j0 := by
      funext I
      rw [Category.id_comp, ← Category.assoc, show redE ℂ ≫ h.left = (P3 0).left from congrArg Over.Hom.left hred,
        e3]
    refine Eq.trans ?_ (valR_app _ q.left W0 _).symm
    rw [← Over.comp_left, hq]
    unfold vE DegPre.cubAtT
    refine (valR_pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t h.left (𝟙 _) _).trans ?_
    rw [Category.id_comp]
    have key : ∀ j j' : thK.{0} → D.P.L.ι, j = j' → valR h.left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j)
        (D.cub.t.s j).val = valR h.left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j') (D.cub.t.s j').val := by
      rintro _ _ rfl; rfl
    exact key _ _ hj
  · intro p _
    change (ptB ν d 0 ≫ q.left).base p ∈ W0
    rw [hpt]
    refine Set.mem_iInter.2 fun I => ?_
    have := ν.good ((P3 0).left ≫ thφ D.P.A (x3 D.P.A) I) (Set.mem_univ p)
    rw [e3] at this
    change ((P3 0).left ≫ thφ D.P.A (x3 D.P.A) I).base p ∈ D.P.L.U (j0 I)
    rw [e3]
    exact this
  · intro z hz
    refine ⟨fun I p _ => ?_, ?_⟩
    · have hm : (ptB ν d z ≫ q.left).base p ∈ W0 := hz (Set.mem_univ p)
      rw [hpt] at hm
      have := LB.wchart_le D.P.L (thφ D.P.A (x3 D.P.A)) j0 I hm
      rw [← e3 z I]
      exact this
    · change valR (ptB ν d z) _ _ = valR _ _ _
      refine (valR_app (ptB ν d z) q.left W0 _).trans ?_
      rw [hpt]

end GlobalTheory.MBLow.JetGeo
