import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.PairProp

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf

open Semi

namespace ZeroLinearity

section SlopeTestRemainingChoices

variable {X Y Z W : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma map_rfl' {V : Y.Opens} (x : Γ(Y, V)) :
    (Y.presheaf.map (homOfLE (le_rfl : V ≤ V)).op).hom x = x := by
  simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma pullGen_s_val {φ : K → (Y ⟶ X)} {ε : K → ℤ} (c : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (j : K → L.ι) :
    ((LB.pullGen L φ ε c h).s j).val =
      (h.appLE (LB.wchart L φ j) (LB.wchart L (fun k => h ≫ φ k) j)
        (LBVal.wchart_pull_le L φ h j)).hom (c.s j).val := by
  rfl

/- English proof (translation)
Establish `hW : W ≤ U ⊓ V` using `le_inf h1 h2`. Establish `key : ∀ {P : Y.Opens} (hP : U ⊓ V ≤ P) (hQ : W ≤ P) (c : Γ(Y, P)ˣ), res hQ c = res hW (res hP c)`. Introduce `P hP hQ c`. Establish `e : Y.presheaf.map (homOfLE hQ).op = Y.presheaf.map (homOfLE hP).op ≫ Y.presheaf.map (homOfLE hW).op`. Rewrite using `[← Functor.map_comp]`.

Both sides reduce to the same expression. Use `ext`. Conclude with `congrArg (fun φ => φ.hom c.val) e`. Rewrite using `[key inf_le_left h1 a, key inf_le_right h2 b, h]`.
-/
lemma res_eq_of_res_eq' {U V W : Y.Opens} (a : Γ(Y, U)ˣ) (b : Γ(Y, V)ˣ) (h1 : W ≤ U) (h2 : W ≤ V)
    (h : res (inf_le_left : U ⊓ V ≤ U) a = res (inf_le_right : U ⊓ V ≤ V) b) :
    res h1 a = res h2 b := by
  have hW : W ≤ U ⊓ V := le_inf h1 h2
  have key : ∀ {P : Y.Opens} (hP : U ⊓ V ≤ P) (hQ : W ≤ P) (c : Γ(Y, P)ˣ),
      res hQ c = res hW (res hP c) := by
    intro P hP hQ c
    have e : Y.presheaf.map (homOfLE hQ).op =
        Y.presheaf.map (homOfLE hP).op ≫ Y.presheaf.map (homOfLE hW).op := by
      rw [← Functor.map_comp]
      rfl
    ext
    exact congrArg (fun φ => φ.hom c.val) e
  rw [key inf_le_left h1 a, key inf_le_right h2 b, h]

/- English proof (translation)
Introduce `j j' hj hj' hjj`. Conclude with `(res_eq_of_res_eq' _ _ _ _ (h j' j hj' hj fun k k' hk => (hjj k' k hk.symm).symm)).symm`.
-/
lemma corr_symm' {K' : Type} [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)}
    {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : LB.Gen.Corr L φ ε φ' ε' t t') : LB.Gen.Corr L φ' ε' φ ε t' t := by
  intro j j' hj hj' hjj
  exact (res_eq_of_res_eq' _ _ _ _
    (h j' j hj' hj fun k k' hk => (hjj k' k hk.symm).symm)).symm

/- English proof (translation)
The claim follows from `Units.ext (map_one _)`.
-/
private lemma res_one_lemma {U V : Y.Opens} (h : V ≤ U) : res h (1 : Γ(Y, U)ˣ) = 1 :=
  Units.ext (map_one _)

/- English proof (translation)
Establish `hC : LB.Coh L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim` using `fun k => k.elim`. Establish `h2 : (L.LinComb φ ε).U j ≤ (L.LinComb (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim).U PEmpty.elim` using `by delta LB.LinComb`. Simplify using `[LB.wchart]`. Establish `key` using `res_eq_of_res_eq' _ _ le_rfl h2 (h j PEmpty.elim hj hC fun _ k' _ => k'.elim)`. Express the relevant statement in the definitionally equal form `res _ (t.s j) = res _ 1 at key`.

Rewrite `key` using `[res_one_lemma]`. Establish `e : res (le_refl _) (t.s j) = t.s j` using `Units.ext (map_rfl' _)`. Rewrite using `[← e]`. Conclude with `key`.
-/
lemma corr_one_alt {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    (h : LB.Gen.Corr L φ ε PEmpty.elim PEmpty.elim t (LB.oneGen L)) (j : K → L.ι)
    (hj : LB.Coh L φ j) : t.s j = 1 := by
  have hC : LB.Coh L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun k => k.elim
  have h2 : (L.LinComb φ ε).U j ≤
      (L.LinComb (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim).U PEmpty.elim := by
    delta LB.LinComb
    simp [LB.wchart]
  have key := res_eq_of_res_eq' _ _ le_rfl h2 (h j PEmpty.elim hj hC fun _ k' _ => k'.elim)
  change res _ (t.s j) = res _ 1 at key
  rw [res_one_lemma] at key
  have e : res (le_refl _) (t.s j) = t.s j := Units.ext (map_rfl' _)
  rw [← e]
  exact key

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(f.appLE C B e ≫ W.presheaf.map (homOfLE hT).op).hom x = _`. Rewrite using `[Scheme.Hom.appLE_map]`.
-/
private lemma appLE_res_lemma_3 (f : W ⟶ Y) {C : Y.Opens} {B T : W.Opens} (e : B ≤ f ⁻¹ᵁ C)
    (hT : T ≤ B) (x : Γ(Y, C)) :
    (W.presheaf.map (homOfLE hT).op).hom ((f.appLE C B e).hom x) = (f.appLE C T (hT.trans e)).hom x := by
  change (f.appLE C B e ≫ W.presheaf.map (homOfLE hT).op).hom x = _
  rw [Scheme.Hom.appLE_map]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(g1.app C ≫ Z.presheaf.map (homOfLE e1).op ≫ g2.appLE D B e2 ≫ W.presheaf.map (homOfLE hT).op).hom x = _`. Rewrite using `[Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]`. Use `first`. Consider the case `rfl`. Consider the case `simp only [Scheme.Hom.appLE, Scheme.comp_app, Category.assoc]`.

Consider the case `simp only [Scheme.Hom.appLE, Scheme.Hom.comp_app, Category.assoc]`.
-/
private lemma appLE_appLE_lemma_2 {B T : W.Opens} {C : Y.Opens} {D : Z.Opens} (g1 : Z ⟶ Y)
    (g2 : W ⟶ Z) (e1 : D ≤ g1 ⁻¹ᵁ C) (e2 : B ≤ g2 ⁻¹ᵁ D) (hT : T ≤ B) (x : Γ(Y, C)) :
    (W.presheaf.map (homOfLE hT).op).hom ((g2.appLE D B e2).hom ((g1.appLE C D e1).hom x)) =
      ((g2 ≫ g1).appLE C T (hT.trans (e2.trans (g2.preimage_mono e1)))).hom x := by
  change (g1.app C ≫ Z.presheaf.map (homOfLE e1).op ≫ g2.appLE D B e2 ≫
    W.presheaf.map (homOfLE hT).op).hom x = _
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  first
  | rfl
  | simp only [Scheme.Hom.appLE, Scheme.comp_app, Category.assoc]
  | simp only [Scheme.Hom.appLE, Scheme.Hom.comp_app, Category.assoc]

/- English proof (translation)
Substitute `hg` using the available equality. Introduce `j j' _ _ hjj`. Take `rfl : j = j'` from `funext fun k => hjj k k (by simp)`. Use `ext`. Express the relevant statement in the definitionally equal form `(W.presheaf.map (homOfLE _).op).hom ((LB.pullGen L _ ε (LB.pullGen L φ ε c g1) g2).s j).val = (W.presheaf.map (homOfLE _).op).hom ((LB.pullGen L φ ε c (g2 ≫ g1)).s j).val`.

Rewrite using `[pullGen_s_val, pullGen_s_val, pullGen_s_val]`. Conclude with `(appLE_appLE_lemma_2 g1 g2 _ _ _ _).trans (appLE_res_lemma_3 (g2 ≫ g1) _ _ _).symm`.
-/
lemma corr_pull_comp {φ : K → (Y ⟶ X)} {ε : K → ℤ} (c : LB.Gen (LB.LinComb L φ ε)) (g1 : Z ⟶ Y)
    (g2 : W ⟶ Z) (g : W ⟶ Y) (hg : g2 ≫ g1 = g) :
    LB.Gen.Corr L _ ε _ ε (LB.pullGen L _ ε (LB.pullGen L φ ε c g1) g2) (LB.pullGen L φ ε c g) := by
  subst hg
  intro j j' _ _ hjj
  obtain rfl : j = j' := funext fun k => hjj k k (by simp)
  ext
  change (W.presheaf.map (homOfLE _).op).hom
      ((LB.pullGen L _ ε (LB.pullGen L φ ε c g1) g2).s j).val =
    (W.presheaf.map (homOfLE _).op).hom ((LB.pullGen L φ ε c (g2 ≫ g1)).s j).val
  rw [pullGen_s_val, pullGen_s_val, pullGen_s_val]
  exact (appLE_appLE_lemma_2 g1 g2 _ _ _ _).trans (appLE_res_lemma_3 (g2 ≫ g1) _ _ _).symm

/- English proof (translation)
Introduce `j j' _ _ _`. Use `delta LB.pullGen LB.oneGen`. Simplify using `only [map_one]`. Conclude with `(res_one_lemma _).trans (res_one_lemma _).symm`.
-/
lemma corr_pull_one (h : Z ⟶ Y) :
    LB.Gen.Corr L _ _ PEmpty.elim PEmpty.elim (LB.pullGen L (Y := Y) (K := PEmpty) PEmpty.elim
      PEmpty.elim (LB.oneGen L) h) (LB.oneGen L) := by
  intro j j' _ _ _
  delta LB.pullGen LB.oneGen
  simp only [map_one]
  exact (res_one_lemma _).trans (res_one_lemma _).symm

/- English proof (translation)
Establish `e2` using `congrArg Units.val (corr_one_alt L hC j hj)`. Rewrite `e2` using `[pullGen_s_val, Units.val_one]`. Conclude with `(appLE_res_lemma_3 h (LBVal.wchart_pull_le L φ h j) hV _).symm.trans ((congrArg (fun y => (Z.presheaf.map (homOfLE hV).op).hom y) e2).trans (map_one _))`.
-/
lemma appLE_one {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (hC : LB.Gen.Corr L _ ε PEmpty.elim PEmpty.elim (LB.pullGen L φ ε t h) (LB.oneGen L))
    (j : K → L.ι) (hj : LB.Coh L (fun k => h ≫ φ k) j) (V : Z.Opens)
    (hV : V ≤ LB.wchart L (fun k => h ≫ φ k) j) :
    (h.appLE (LB.wchart L φ j) V (hV.trans (LBVal.wchart_pull_le L φ h j))).hom (t.s j).val = 1 := by
  have e2 := congrArg Units.val (corr_one_alt L hC j hj)
  rw [pullGen_s_val, Units.val_one] at e2
  exact (appLE_res_lemma_3 h (LBVal.wchart_pull_le L φ h j) hV _).symm.trans
    ((congrArg (fun y => (Z.presheaf.map (homOfLE hV).op).hom y) e2).trans (map_one _))

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(Y.presheaf.map (homOfLE hUV).op ≫ f.appLE V W' hW).hom x.val = _`. Rewrite using `[Scheme.Hom.map_appLE]`.
-/
lemma appLE_res (f : Z ⟶ Y) {U V : Y.Opens} (hUV : V ≤ U) {W' : Z.Opens} (hW : W' ≤ f ⁻¹ᵁ V)
    (x : Γ(Y, U)ˣ) :
    (f.appLE V W' hW).hom (res hUV x).val =
      (f.appLE U W' (hW.trans (f.preimage_mono hUV))).hom x.val := by
  change (Y.presheaf.map (homOfLE hUV).op ≫ f.appLE V W' hW).hom x.val = _
  rw [Scheme.Hom.map_appLE]

/- English proof (translation)
Introduce `j j' hj _ _`. Establish `hj0 : LB.Coh L φ j` using `fun k₁ k₂ hk => hj k₁ k₂ (by simp only [hk])`. Establish `e` using `corr_one_alt L hC j hj0`. Use `delta LB.pullGen LB.oneGen`. Simplify using `only [e, map_one]`.

Conclude with `(res_one_lemma _).trans (res_one_lemma _).symm`.
-/
lemma corr_one_pull {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    (hC : LB.Gen.Corr L φ ε PEmpty.elim PEmpty.elim t (LB.oneGen L)) (h : Z ⟶ Y) :
    LB.Gen.Corr L _ ε PEmpty.elim PEmpty.elim (LB.pullGen L φ ε t h) (LB.oneGen L) := by
  intro j j' hj _ _
  have hj0 : LB.Coh L φ j := fun k₁ k₂ hk => hj k₁ k₂ (by simp only [hk])
  have e := corr_one_alt L hC j hj0
  delta LB.pullGen LB.oneGen
  simp only [e, map_one]
  exact (res_one_lemma _).trans (res_one_lemma _).symm

end SlopeTestRemainingChoices

section Z

variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (f g : B ⟶ B) [IsMonHom g]

abbrev zz : B ⟶ B ⊗ B := lift (𝟙 B) (toUnit B ≫ η[B])

/- English proof (translation)
Rewrite using `[zz, padd, ← Category.assoc, comp_lift]`. Simplify using `using MonObj.lift_comp_one_right f`.
-/
lemma zz_0 : zz B ≫ padd B (fst B B ≫ f) (snd B B) = f := by
  rw [zz, padd, ← Category.assoc, comp_lift]
  simpa using MonObj.lift_comp_one_right f

/- English proof (translation)
Simplify using `[zz]`.
-/
lemma zz_1 : zz B ≫ fst B B ≫ f = f := by
  simp [zz]

/- English proof (translation)
Simplify using `[zz]`.
-/
lemma zz_2 : zz B ≫ snd B B = toUnit B ≫ η[B] := by
  simp [zz]

/- English proof (translation)
Simplify using `[zz]`.
-/
lemma zz_5 : zz B ≫ snd B B ≫ g = toUnit B ≫ η[B] := by
  simp [zz]

/- English proof (translation)
Rewrite using `[zz, padd, ← Category.assoc, comp_lift]`. Simplify using `using MonObj.lift_comp_one_right (𝟙 B)`.
-/
lemma zz_3 : zz B ≫ padd B (fst B B) (snd B B ≫ g) = 𝟙 B := by
  rw [zz, padd, ← Category.assoc, comp_lift]
  simpa using MonObj.lift_comp_one_right (𝟙 B)

/- English proof (translation)
Simplify using `[zz]`.
-/
lemma zz_4 : zz B ≫ fst B B = 𝟙 B := by
  simp [zz]

/- English proof (translation)
Introduce `ψ`. Establish `h0 : (zz B).left ≫ (padd B (fst B B ≫ f) (snd B B)).left = f.left`. Rewrite using `[← Over.comp_left, zz_0]`. Establish `h1 : (zz B).left ≫ (fst B B ≫ f).left = f.left`. Rewrite using `[← Over.comp_left, zz_1]`.

Establish `h2 : (zz B).left ≫ (snd B B).left = (toUnit B ≫ η[B]).left`. Rewrite using `[← Over.comp_left, zz_2]`. Establish `h3 : (zz B).left ≫ (padd B (fst B B) (snd B B ≫ g)).left = Over.Hom.left (𝟙 B)`. Rewrite using `[← Over.comp_left, zz_3]`. Establish `h4 : (zz B).left ≫ (fst B B).left = Over.Hom.left (𝟙 B)`.

Rewrite using `[← Over.comp_left, zz_4]`. Establish `h5 : (zz B).left ≫ (snd B B ≫ g).left = (toUnit B ≫ η[B]).left`. Rewrite using `[← Over.comp_left, zz_5]`. Establish `e0 : (zz B).left ≫ rosatiφ B f g 0 = f.left` using `h0`. Establish `e1 : (zz B).left ≫ rosatiφ B f g 1 = f.left` using `h1`.

Establish `e2 : (zz B).left ≫ rosatiφ B f g 2 = (toUnit B ≫ η[B]).left` using `h2`. Establish `e3 : (zz B).left ≫ rosatiφ B f g 3 = Over.Hom.left (𝟙 B)` using `h3`. Establish `e4 : (zz B).left ≫ rosatiφ B f g 4 = Over.Hom.left (𝟙 B)` using `h4`. Establish `e5 : (zz B).left ≫ rosatiφ B f g 5 = (toUnit B ≫ η[B]).left` using `h5`. Rewrite using `[Fin.sum_univ_six]`.

Use `beta_reduce`. Use `erw [e0, e1, e2, e3, e4, e5]`. Apply the tactic sequence `by_cases hf : Over.Hom.left f = ψ <;> by_cases hu : (toUnit B ≫ η[B]).left = ψ <;>`. Apply the tactic sequence `by_cases hi : Over.Hom.left (𝟙 B) = ψ <;>`. Use `first`.

Consider the case `(simp only [hf, hu, hi, eq_self_iff_true, ↓reduceIte]; simp [rosatiε]; done)`. Consider the case `simp [hf, hu, hi, rosatiε]`.
-/
lemma zz_sameSum : LB.SameSum (Y := B.left) (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun k => (zz B).left ≫ rosatiφ B f g k) rosatiε := by
  intro ψ
  have h0 : (zz B).left ≫ (padd B (fst B B ≫ f) (snd B B)).left = f.left := by
    rw [← Over.comp_left, zz_0]
  have h1 : (zz B).left ≫ (fst B B ≫ f).left = f.left := by
    rw [← Over.comp_left, zz_1]
  have h2 : (zz B).left ≫ (snd B B).left = (toUnit B ≫ η[B]).left := by
    rw [← Over.comp_left, zz_2]
  have h3 : (zz B).left ≫ (padd B (fst B B) (snd B B ≫ g)).left = Over.Hom.left (𝟙 B) := by
    rw [← Over.comp_left, zz_3]
  have h4 : (zz B).left ≫ (fst B B).left = Over.Hom.left (𝟙 B) := by
    rw [← Over.comp_left, zz_4]
  have h5 : (zz B).left ≫ (snd B B ≫ g).left = (toUnit B ≫ η[B]).left := by
    rw [← Over.comp_left, zz_5]
  have e0 : (zz B).left ≫ rosatiφ B f g 0 = f.left := h0
  have e1 : (zz B).left ≫ rosatiφ B f g 1 = f.left := h1
  have e2 : (zz B).left ≫ rosatiφ B f g 2 = (toUnit B ≫ η[B]).left := h2
  have e3 : (zz B).left ≫ rosatiφ B f g 3 = Over.Hom.left (𝟙 B) := h3
  have e4 : (zz B).left ≫ rosatiφ B f g 4 = Over.Hom.left (𝟙 B) := h4
  have e5 : (zz B).left ≫ rosatiφ B f g 5 = (toUnit B ≫ η[B]).left := h5
  rw [Fin.sum_univ_six]
  beta_reduce
  erw [e0, e1, e2, e3, e4, e5]
  by_cases hf : Over.Hom.left f = ψ <;> by_cases hu : (toUnit B ≫ η[B]).left = ψ <;>
    by_cases hi : Over.Hom.left (𝟙 B) = ψ <;>
    first
    | (simp only [hf, hu, hi, eq_self_iff_true, ↓reduceIte]; simp [rosatiε]; done)
    | simp [hf, hu, hi, rosatiε]

end Z

section Unit

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιG : RingAct G O) (e : ℕ) (a : O)

/- English proof (translation)
Use `haveI := ιG.hom a`. Use `delta eSec`. Rewrite using `[← Over.comp_left, IsMonHom.one_hom]`.
-/
lemma eSec_h : eSec (thickObj R I e G) ≫ ((Over.pullback (thick R I e)).map (ιG.act a)).left =
    eSec (thickObj R I e G) := by
  haveI := ιG.hom a
  delta eSec
  rw [← Over.comp_left, IsMonHom.one_hom]

/- English proof (translation)
Use `(U.gt e).q_hom` as an intermediate fact. Use `ext1`. Establish `h1 : (η[thickObj R I e G] ≫ (U.gt e).q) = η[thickObj R I e D.toPre.P.A]` using `IsMonHom.one_hom _`. Establish `h2` using `congrArg Over.Hom.left h1`. Simplify using `only [GtCoord.pG, DegPre.prBe, Over.comp_left, Over.map_map_left, Over.homMk_left] at h2 ⊢`.

Rewrite using `[← Category.assoc, h2, Functor.obj.η_def]`. Simplify using `only [Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_fst]`. Establish `h3` using `Over.w (toUnit ((Over.map (thick R I e)).obj (𝟙_ _)))`. Establish `h4` using `Over.w (Functor.LaxMonoidal.ε (Over.pullback (thick R I e)))`. Establish `h5` using `pullback.condition (f := (𝟙_ (Over (Spec (CommRingCat.of R)))).hom) (g := thick R I e)`.

Simplify using `only [Over.map_obj_hom, Functor.id_obj, Over.pullback_obj_hom] at h3 h4 h5`. Establish `h5' : pullback.fst (𝟙_ (Over (Spec (CommRingCat.of R)))).hom (thick R I e) = pullback.snd (𝟙_ (Over (Spec (CommRingCat.of R)))).hom (thick R I e) ≫ thick R I e` using `(Category.comp_id _).symm.trans h5`. Establish `h3' : Over.Hom.left (toUnit ((Over.map (thick R I e)).obj (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))))) = thick R I e` using `(Category.comp_id _).symm.trans (h3.trans (Category.id_comp _))`. Establish `key : Over.Hom.left (Functor.LaxMonoidal.ε (Over.pullback (thick R I e))) ≫ pullback.fst (𝟙_ (Over (Spec (CommRingCat.of R)))).hom (thick R I e) = Over.Hom.left (toUnit ((Over.map (thick R I e)).obj (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))))))`. Rewrite using `[h5', ← Category.assoc, h4, h3']`.

Conclude with `Category.id_comp _`. Rewrite using `[← Category.assoc, key]`.
-/
lemma eSec_pG : (Over.map (thick R I e)).map η[thickObj R I e G] ≫ (U.gt e).pG =
    toUnit _ ≫ η[D.toPre.P.A] := by
  have := (U.gt e).q_hom
  ext1
  have h1 : (η[thickObj R I e G] ≫ (U.gt e).q) = η[thickObj R I e D.toPre.P.A] := IsMonHom.one_hom _
  have h2 := congrArg Over.Hom.left h1
  simp only [GtCoord.pG, DegPre.prBe, Over.comp_left, Over.map_map_left, Over.homMk_left] at h2 ⊢
  rw [← Category.assoc, h2, Functor.obj.η_def]
  simp only [Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_fst]
  have h3 := Over.w (toUnit ((Over.map (thick R I e)).obj (𝟙_ _)))
  have h4 := Over.w (Functor.LaxMonoidal.ε (Over.pullback (thick R I e)))
  have h5 := pullback.condition (f := (𝟙_ (Over (Spec (CommRingCat.of R)))).hom) (g := thick R I e)
  simp only [Over.map_obj_hom, Functor.id_obj, Over.pullback_obj_hom] at h3 h4 h5
  have h5' : pullback.fst (𝟙_ (Over (Spec (CommRingCat.of R)))).hom (thick R I e) =
      pullback.snd (𝟙_ (Over (Spec (CommRingCat.of R)))).hom (thick R I e) ≫ thick R I e :=
    (Category.comp_id _).symm.trans h5
  have h3' : Over.Hom.left (toUnit ((Over.map (thick R I e)).obj
      (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))))) = thick R I e :=
    (Category.comp_id _).symm.trans (h3.trans (Category.id_comp _))
  have key : Over.Hom.left (Functor.LaxMonoidal.ε (Over.pullback (thick R I e))) ≫
      pullback.fst (𝟙_ (Over (Spec (CommRingCat.of R)))).hom (thick R I e) =
      Over.Hom.left (toUnit ((Over.map (thick R I e)).obj
        (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))))) := by
    rw [h5', ← Category.assoc, h4, h3']
    exact Category.id_comp _
  rw [← Category.assoc, key]

/- English proof (translation)
Use `show ((Over.map (thick R I e)).map η[thickObj R I e G]).left ≫ _ = _`. Rewrite using `[← Over.comp_left, ← Over.comp_left]`. Use `congr 1`. Rewrite using `[comp_lift, eSec_pG, comp_lift, Category.comp_id, ← Category.assoc _ (toUnit D.toPre.P.A), toUnit_unique (_ ≫ toUnit D.toPre.P.A) (toUnit _)]`.
-/
lemma eSec_lift (χ : D.toPre.X) :
    eSec (thickObj R I e G) ≫ (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left =
      ((Over.map (thick R I e)).map η[thickObj R I e G] ≫ toUnit _ ≫ D.toPre.c χ).left ≫
        (zz D.toPre.P.A).left := by
  show ((Over.map (thick R I e)).map η[thickObj R I e G]).left ≫ _ = _
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  rw [comp_lift, eSec_pG, comp_lift, Category.comp_id, ← Category.assoc _ (toUnit D.toPre.P.A),
    toUnit_unique (_ ≫ toUnit D.toPre.P.A) (toUnit _)]

end Unit

end ZeroLinearity

open ZeroLinearity

section Main

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
  (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))

/- English proof (translation)
Establish `hL` using `D.toPre.P.isLB`. Establish `hg : IsMonHom (ιD.onB.act a)` using `ιD.onB.hom a`. Set `ψ : Fin 6 → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)` to `fun k => (zz D.toPre.P.A).left ≫ rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k`. Establish `hs` using `zz_sameSum D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)`. Set `canon` to `Canon.canonGen D.toPre.P.L (Y := D.toPre.P.A.left) (K := PEmpty) PEmpty.elim PEmpty.elim ψ rosatiε (fun k => k.elim) (LB.oneGen D.toPre.P.L)`.

Establish `hcan : canon.IsGen` using `Canon.canonGen_isGen hL _ _ _ _ hs _ _ (LB.isGen_oneGen D.toPre.P.L)`. Establish `hcc` using `Canon.canonGen_corr hL (Y := D.toPre.P.A.left) (K := PEmpty) PEmpty.elim PEmpty.elim ψ rosatiε (fun k => k.elim) (LB.oneGen D.toPre.P.L)`. Set `v` to `LB.pullGen D.toPre.P.L _ _ u (zz D.toPre.P.A).left`. Establish `hv : v.IsGen` using `LB.isGen_pullGen (L := D.toPre.P.L) _ _ _ hu _`. Take `⟨κ, hκ⟩` from `ratio_glue _ (linComb_cover _ hL ψ rosatiε) v canon hv hcan`.

Set `ηA` to `(η[D.toPre.P.A]).left`. Establish `hz : ηA ≫ (zz D.toPre.P.A).left = zero2 D.toPre.P.A`. Rewrite using `[← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc, toUnit_unique (η[D.toPre.P.A] ≫ toUnit D.toPre.P.A) (𝟙 _), Category.id_comp]`. Establish `hψz : ∀ k, ηA ≫ ψ k = zero2 D.toPre.P.A ≫ rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k` using `fun k => by`. Rewrite using `[← hz, Category.assoc]`.

Use `choose idx hidx using fun s : (𝟙_ (Over (Spec (CommRingCat.of R)))).left => idx_exists D.toPre.P.L hL s`. Set `js : (𝟙_ (Over (Spec (CommRingCat.of R)))).left → Fin 6 → D.toPre.P.L.ι` to `fun s k => idx s (ηA ≫ ψ k)`. Set `Us : (𝟙_ (Over (Spec (CommRingCat.of R)))).left → (𝟙_ (Over (Spec (CommRingCat.of R)))).left.Opens` to `fun s => LB.wchart D.toPre.P.L (fun k => ηA ≫ ψ k) (js s)`. Establish `hUs : ∀ s, s ∈ Us s` using `fun s => Set.mem_iInter.2 fun k => hidx s _`. Establish `hcov : ⨆ s, Us s = ⊤` using `top_unique fun s _ => TopologicalSpace.Opens.mem_iSup.2 ⟨s, hUs s⟩`.

Establish `key : ∀ s, res (fun _ _ => trivial : Us s ≤ ηA ⁻¹ᵁ ⊤) (pullU ηA ⊤ κ) = 1`. Introduce `s`. Establish `coh1 : LB.Coh D.toPre.P.L (fun k => ηA ≫ ψ k) (js s)` using `fun k1 k2 h => congrArg (idx s) h`. Establish `coh2 : LB.Coh D.toPre.P.L (fun k => zero2 D.toPre.P.A ≫ rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k) (js s)` using `fun k1 k2 h => congrArg (idx s) (((hψz k1).trans h).trans (hψz k2).symm)`. Establish `cross : ∀ k k', ηA ≫ ψ k = zero2 D.toPre.P.A ≫ rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k' → js s k = js s k'` using `fun k k' h => congrArg (idx s) (h.trans (hψz k').symm)`.

Establish `e` using `corr_pull_comp D.toPre.P.L u (zz D.toPre.P.A).left ηA (zero2 D.toPre.P.A) hz (js s) (js s) coh1 coh2 cross`. Establish `one` using `corr_one_alt D.toPre.P.L hu0 (js s) coh2`. Establish `h2 : Us s ≤ LB.wchart D.toPre.P.L (fun k => zero2 D.toPre.P.A ≫ rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k) (js s)` using `fun x hx => Set.mem_iInter.2 fun k => by`. Use `Set.mem_iInter.1 hx k` as an intermediate fact. Use `beta_reduce at this ⊢`.

Rewrite `this` using `[hψz k]`. Then use the resulting hypothesis. Establish `e'` using `res_eq_of_res_eq' _ _ (le_rfl : Us s ≤ Us s) h2 e`. Establish `e''` using `(Canon.res_refl _ _).symm.trans (e'.trans ((congrArg (res h2) one).trans (map_one _)))`. Establish `cohψ : LB.Coh D.toPre.P.L ψ (js s)` using `fun k1 k2 h => congrArg (idx s) (congrArg (ηA ≫ ·) h)`. Establish `cone` using `corr_one_alt D.toPre.P.L (corr_symm' D.toPre.P.L hcc) (js s) cohψ`.

Establish `hh : Us s ≤ ηA ⁻¹ᵁ LB.wchart D.toPre.P.L ψ (js s)` using `LBVal.wchart_pull_le _ ψ ηA (js s)`. Establish `e5 : v.s (js s) = res le_top κ` using `(hκ (js s)).trans ((congrArg (res le_top κ * ·) cone).trans (_root_.mul_one _))`. Establish `e4 : res hh (pullU ηA _ (v.s (js s))) = res (fun _ _ => trivial : Us s ≤ ηA ⁻¹ᵁ ⊤) (pullU ηA ⊤ κ)` using `(congrArg (fun x => res hh (pullU ηA _ x)) e5).trans (Canon.res_pullU_eq ηA le_top (fun _ _ => trivial) hh κ).symm`. Conclude with `e4.symm.trans e''`. Establish `hκe : ηA.appTop.hom κ.val = 1`.

Use `eq_local Us hcov _ _ fun s => ?_` and prove the remaining obligations. Conclude with `(congrArg Units.val (key s)).trans (map_one _).symm`. Take `⟨c, hc⟩` from `(hGF _ D.toPre.P.A D.toPre.P.isAb).2 κ.val`. Establish `hηA : ηA ≫ D.toPre.P.A.hom = 𝟙 _` using `Over.w η[D.toPre.P.A]`. Establish `hc1 : c = 1`.

Establish `m : (ηA ≫ D.toPre.P.A.hom).appTop.hom c = c` using `by rw [hηA]; rfl`. Rewrite `m` using `[Scheme.Hom.comp_appTop]`. Conclude with `m.symm.trans ((congrArg ηA.appTop.hom hc).trans hκe)`. Establish `hκ1 : κ = 1` using `Units.ext (hc.symm.trans (by rw [hc1, map_one]; rfl))`. Introduce `j j' hj hj' hm`.

Establish `h1 : v.s j = canon.s j` using `(hκ j).trans (by rw [hκ1, map_one, _root_.one_mul])`. Conclude with `(congrArg (res _) h1).trans ((corr_symm' D.toPre.P.L hcc) j j' hj hj' hm)`.
-/
theorem u_zero (hGF : GlobalFnsSt) (hu : u.IsGen)
    (hu0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (zero2 D.toPre.P.A))
      (LB.oneGen D.toPre.P.L)) :
    LB.Gen.Corr D.toPre.P.L _ _ _ _
      (LB.pullGen D.toPre.P.L _ _ u (lift (𝟙 D.toPre.P.A) (toUnit D.toPre.P.A ≫ η[D.toPre.P.A])).left)
      (LB.oneGen D.toPre.P.L) := by
  classical
  have hL := D.toPre.P.isLB
  have hg : IsMonHom (ιD.onB.act a) := ιD.onB.hom a
  let ψ : Fin 6 → (D.toPre.P.A.left ⟶ D.toPre.P.A.left) := fun k =>
    (zz D.toPre.P.A).left ≫ rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k
  have hs := zz_sameSum D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)
  let canon := Canon.canonGen D.toPre.P.L (Y := D.toPre.P.A.left) (K := PEmpty) PEmpty.elim
    PEmpty.elim ψ rosatiε (fun k => k.elim) (LB.oneGen D.toPre.P.L)
  have hcan : canon.IsGen :=
    Canon.canonGen_isGen hL _ _ _ _ hs _ _ (LB.isGen_oneGen D.toPre.P.L)
  have hcc := Canon.canonGen_corr hL (Y := D.toPre.P.A.left) (K := PEmpty) PEmpty.elim PEmpty.elim
    ψ rosatiε (fun k => k.elim) (LB.oneGen D.toPre.P.L)
  let v := LB.pullGen D.toPre.P.L _ _ u (zz D.toPre.P.A).left
  have hv : v.IsGen := LB.isGen_pullGen (L := D.toPre.P.L) _ _ _ hu _
  obtain ⟨κ, hκ⟩ := ratio_glue _ (linComb_cover _ hL ψ rosatiε) v canon hv hcan

  let ηA := (η[D.toPre.P.A]).left
  have hz : ηA ≫ (zz D.toPre.P.A).left = zero2 D.toPre.P.A := by
    rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc,
      toUnit_unique (η[D.toPre.P.A] ≫ toUnit D.toPre.P.A) (𝟙 _), Category.id_comp]
  have hψz : ∀ k, ηA ≫ ψ k = zero2 D.toPre.P.A ≫
      rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k := fun k => by
    rw [← hz, Category.assoc]
  choose idx hidx using fun s : (𝟙_ (Over (Spec (CommRingCat.of R)))).left =>
    idx_exists D.toPre.P.L hL s
  let js : (𝟙_ (Over (Spec (CommRingCat.of R)))).left → Fin 6 → D.toPre.P.L.ι :=
    fun s k => idx s (ηA ≫ ψ k)
  let Us : (𝟙_ (Over (Spec (CommRingCat.of R)))).left → (𝟙_ (Over (Spec (CommRingCat.of R)))).left.Opens :=
    fun s => LB.wchart D.toPre.P.L (fun k => ηA ≫ ψ k) (js s)
  have hUs : ∀ s, s ∈ Us s := fun s => Set.mem_iInter.2 fun k => hidx s _
  have hcov : ⨆ s, Us s = ⊤ :=
    top_unique fun s _ => TopologicalSpace.Opens.mem_iSup.2 ⟨s, hUs s⟩
  have key : ∀ s, res (fun _ _ => trivial : Us s ≤ ηA ⁻¹ᵁ ⊤) (pullU ηA ⊤ κ) = 1 := by
    intro s

    have coh1 : LB.Coh D.toPre.P.L (fun k => ηA ≫ ψ k) (js s) := fun k1 k2 h => congrArg (idx s) h
    have coh2 : LB.Coh D.toPre.P.L (fun k => zero2 D.toPre.P.A ≫
        rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k) (js s) :=
      fun k1 k2 h => congrArg (idx s) (((hψz k1).trans h).trans (hψz k2).symm)
    have cross : ∀ k k', ηA ≫ ψ k = zero2 D.toPre.P.A ≫
        rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k' → js s k = js s k' :=
      fun k k' h => congrArg (idx s) (h.trans (hψz k').symm)
    have e := corr_pull_comp D.toPre.P.L u (zz D.toPre.P.A).left ηA (zero2 D.toPre.P.A) hz
      (js s) (js s) coh1 coh2 cross
    have one := corr_one_alt D.toPre.P.L hu0 (js s) coh2
    have h2 : Us s ≤ LB.wchart D.toPre.P.L (fun k => zero2 D.toPre.P.A ≫
        rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k) (js s) :=
      fun x hx => Set.mem_iInter.2 fun k => by
        have := Set.mem_iInter.1 hx k
        beta_reduce at this ⊢
        rwa [hψz k] at this
    have e' := res_eq_of_res_eq' _ _ (le_rfl : Us s ≤ Us s) h2 e
    have e'' := (Canon.res_refl _ _).symm.trans (e'.trans ((congrArg (res h2) one).trans (map_one _)))

    have cohψ : LB.Coh D.toPre.P.L ψ (js s) := fun k1 k2 h => congrArg (idx s) (congrArg (ηA ≫ ·) h)
    have cone := corr_one_alt D.toPre.P.L (corr_symm' D.toPre.P.L hcc) (js s) cohψ

    have hh : Us s ≤ ηA ⁻¹ᵁ LB.wchart D.toPre.P.L ψ (js s) := LBVal.wchart_pull_le _ ψ ηA (js s)
    have e5 : v.s (js s) = res le_top κ :=
      (hκ (js s)).trans ((congrArg (res le_top κ * ·) cone).trans (_root_.mul_one _))
    have e4 : res hh (pullU ηA _ (v.s (js s))) = res (fun _ _ => trivial : Us s ≤ ηA ⁻¹ᵁ ⊤)
        (pullU ηA ⊤ κ) :=
      (congrArg (fun x => res hh (pullU ηA _ x)) e5).trans
        (Canon.res_pullU_eq ηA le_top (fun _ _ => trivial) hh κ).symm
    exact e4.symm.trans e''
  have hκe : ηA.appTop.hom κ.val = 1 := by
    refine eq_local Us hcov _ _ fun s => ?_
    exact (congrArg Units.val (key s)).trans (map_one _).symm

  obtain ⟨c, hc⟩ := (hGF _ D.toPre.P.A D.toPre.P.isAb).2 κ.val
  have hηA : ηA ≫ D.toPre.P.A.hom = 𝟙 _ := Over.w η[D.toPre.P.A]
  have hc1 : c = 1 := by
    have m : (ηA ≫ D.toPre.P.A.hom).appTop.hom c = c := by rw [hηA]; rfl
    rw [Scheme.Hom.comp_appTop] at m
    exact m.symm.trans ((congrArg ηA.appTop.hom hc).trans hκe)
  have hκ1 : κ = 1 := Units.ext (hc.symm.trans (by rw [hc1, map_one]; rfl))

  intro j j' hj hj' hm
  have h1 : v.s j = canon.s j := (hκ j).trans (by rw [hκ1, map_one, _root_.one_mul])
  exact (congrArg (res _) h1).trans ((corr_symm' D.toPre.P.L hcc) j j' hj hj' hm)

include hO in

/- English proof (translation)
Establish `hL` using `D.toPre.P.isLB`. Establish `hz0` using `u_zero ιD a u hGF hu hu0`. Establish `F1` using `eSec_h (I := I) ιG e a`. Establish `F2` using `eSec_lift U e χ`. Set `ε` to `eSec (thickObj R I e G)`.

Set `cS` to `((Over.map (thick R I e)).map η[thickObj R I e G] ≫ toUnit _ ≫ D.toPre.c χ).left`. Set `S'` to `(𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left`. Use `choose idx hidx using fun s : S' => idx_exists D.toPre.P.L hL s`. Set `jA : S' → Fin 4 ⊕ Fin 6 → D.toPre.P.L.ι` to `fun s k => idx s (ε ≫ φA U ιD e a χ k)`. Set `jB : S' → Fin 4 → D.toPre.P.L.ι` to `fun s k => idx s (ε ≫ φB U ιG e a χ k)`.

Set `Us : S' → S'.Opens` to `fun s => LB.wchart D.toPre.P.L (fun k => ε ≫ φB U ιG e a χ k) (jB s) ⊓ LB.wchart D.toPre.P.L (fun k => ε ≫ φA U ιD e a χ k) (jA s)`. Establish `hUs : ∀ s, s ∈ Us s` using `fun s => ⟨Set.mem_iInter.2 fun k => hidx s _, Set.mem_iInter.2 fun k => hidx s _⟩`. Establish `hcov : ⨆ s, Us s = ⊤` using `top_unique fun s _ => TopologicalSpace.Opens.mem_iSup.2 ⟨s, hUs s⟩`. Establish `key : ∀ s, (ε.appLE ⊤ (Us s) (fun _ _ => trivial)).hom ρ.val = 1`. Introduce `s`.

Establish `cA : LB.Coh D.toPre.P.L (φA U ιD e a χ) (jA s)` using `fun k1 k2 h => congrArg (idx s) (congrArg (ε ≫ ·) h)`. Establish `cB : LB.Coh D.toPre.P.L (φB U ιG e a χ) (jB s)` using `fun k1 k2 h => congrArg (idx s) (congrArg (ε ≫ ·) h)`. Establish `cross : ∀ k k', φB U ιG e a χ k = φA U ιD e a χ k' → jB s k = jA s k'` using `fun k k' h => congrArg (idx s) (congrArg (ε ≫ ·) h)`. Establish `P` using `hρ (jA s) (jB s) cA cB cross`. Establish `hU : Us s ≤ ε ⁻¹ᵁ (LB.wchart D.toPre.P.L (φB U ιG e a χ) (jB s) ⊓ LB.wchart D.toPre.P.L (φA U ιD e a χ) (jA s))` using `fun x hx => ⟨LBVal.wchart_pull_le _ _ ε _ hx.1, LBVal.wchart_pull_le _ _ ε _ hx.2⟩`.

Establish `P2` using `(congrArg (fun w => (ε.appLE _ (Us s) hU).hom (Units.val w)) P).trans (map_mul (ε.appLE _ (Us s) hU).hom _ _)`. Establish `P'` using `(appLE_res ε _ hU _).symm.trans (P2.trans (congrArg₂ (· * ·) (appLE_res ε _ hU ρ) (appLE_res ε _ hU _)))`. Establish `hB : Us s ≤ ε ⁻¹ᵁ LB.wchart D.toPre.P.L (φB U ιG e a χ) (jB s)` using `fun x hx => LBVal.wchart_pull_le _ _ ε _ hx.1`. Establish `hBO : ∀ k, ε ≫ φB U ιG e a χ k = ε ≫ D.toPre.Oφ (U.gt e).pG χ k` using `fun k => by show ε ≫ ((Over.pullback (thick R I e)).map (ιG.act a)).left ≫ _ = _`. Rewrite using `[← Category.assoc, F1]`.

Establish `R1 : (ε.appLE _ (Us s) hB).hom ((rhs U ιG e a χ).s (jB s)).val = 1`. Use `(congrArg (ε.appLE _ (Us s) hB).hom (pullGen_s_val D.toPre.P.L _ _ (jB s))).trans ?_` and prove the remaining obligations. Establish `cohB : LB.Coh D.toPre.P.L (fun k => ε ≫ D.toPre.Oφ (U.gt e).pG χ k) (jB s)` using `fun k1 k2 h => congrArg (idx s) (((hBO k1).trans h).trans (hBO k2).symm)`. Establish `hV : Us s ≤ LB.wchart D.toPre.P.L (fun k => ε ≫ D.toPre.Oφ (U.gt e).pG χ k) (jB s)` using `fun x hx => Set.mem_iInter.2 fun k => by`. Use `Set.mem_iInter.1 hx.1 k` as an intermediate fact.

Use `beta_reduce at this ⊢`. Rewrite `this` using `[hBO k]`. Then use the resulting hypothesis. Establish `m : ((Over.pullback (thick R I e)).map (ιG.act a)).left.appLE _ _ (LBVal.wchart_pull_le _ _ _ (jB s)) ≫ ε.appLE _ (Us s) hB = ε.appLE _ (Us s) (hV.trans (LBVal.wchart_pull_le _ _ ε (jB s)))`. Rewrite using `[Scheme.Hom.appLE_comp_appLE]`. Conclude with `Semi.TorusInj.appLE_of_eq F1 _`.

Rewrite using `[← appLE_one D.toPre.P.L ((U.gt e).t χ) ε ((U.gt e).t_unit χ) (jB s) cohB (Us s) hV, ← m]`. Both sides reduce to the same expression. Establish `hA : Us s ≤ ε ⁻¹ᵁ LB.wchart D.toPre.P.L (φA U ιD e a χ) (jA s)` using `fun x hx => LBVal.wchart_pull_le _ _ ε _ hx.2`. Establish `M` using `LBVal.mulGen_val D.toPre.P.L _ _ _ _ ((U.gt e).t (star a • χ)) (LB.pullGen D.toPre.P.L _ _ u (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left) (jA s) _ le_rfl`. Establish `L1` using `(congrArg (ε.appLE _ (Us s) hA).hom ((map_rfl' _).symm.trans M)).trans (map_mul (ε.appLE _ (Us s) hA).hom _ _)`.

Establish `coh1 : LB.Coh D.toPre.P.L (fun k => ε ≫ D.toPre.Oφ (U.gt e).pG (star a • χ) k) (jA s ∘ Sum.inl)` using `fun k1 k2 h => congrArg (idx s) h`. Establish `hV1 : Us s ≤ LB.wchart D.toPre.P.L (fun k => ε ≫ D.toPre.Oφ (U.gt e).pG (star a • χ) k) (jA s ∘ Sum.inl)` using `fun x hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.2 (Sum.inl k)`. Establish `T1` using `appLE_one D.toPre.P.L ((U.gt e).t (star a • χ)) ε ((U.gt e).t_unit _) (jA s ∘ Sum.inl) coh1 (Us s) hV1`. Establish `m1` using `congrArg (fun ψ => ψ.hom (((U.gt e).t (star a • χ)).s (jA s ∘ Sum.inl)).val) (Scheme.Hom.map_appLE ε hA (homOfLE (fun x hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (Sum.inl k) : LB.wchart D.toPre.P.L (φA U ιD e a χ) (jA s) ≤ _)).op)`. Establish `hF2k : ∀ k, ε ≫ φA U ιD e a χ (Sum.inr k) = cS ≫ ((zz D.toPre.P.A).left ≫ rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k)` using `fun k => by show ε ≫ (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left ≫ _ = _`.

Rewrite using `[← Category.assoc, F2, Category.assoc]`. Establish `coh2 : LB.Coh D.toPre.P.L (fun k => cS ≫ ((zz D.toPre.P.A).left ≫ rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k)) (jA s ∘ Sum.inr)` using `fun k1 k2 h => congrArg (idx s) (((hF2k k1).trans h).trans (hF2k k2).symm)`. Establish `hV2' : Us s ≤ LB.wchart D.toPre.P.L (fun k => cS ≫ ((zz D.toPre.P.A).left ≫ rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k)) (jA s ∘ Sum.inr)` using `fun x hx => Set.mem_iInter.2 fun k => by`. Use `Set.mem_iInter.1 hx.2 (Sum.inr k)` as an intermediate fact. Use `beta_reduce at this ⊢`.

Rewrite `this` using `[hF2k k]`. Then use the resulting hypothesis. Establish `T2` using `appLE_one D.toPre.P.L (LB.pullGen D.toPre.P.L _ _ u (zz D.toPre.P.A).left) cS (corr_one_pull D.toPre.P.L hz0 cS) (jA s ∘ Sum.inr) coh2 (Us s) hV2'`. Establish `hW2 : Us s ≤ ε ⁻¹ᵁ LB.wchart D.toPre.P.L (fun k => (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left ≫ rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k) (jA s ∘ Sum.inr)` using `fun x hx => LBVal.wchart_pull_le _ _ ε _ (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.2 (Sum.inr k))`. Establish `m2 : (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left.appLE _ _ (LBVal.wchart_pull_le _ _ _ (jA s ∘ Sum.inr)) ≫ ε.appLE _ (Us s) hW2 = (zz D.toPre.P.A).left.appLE _ _ (LBVal.wchart_pull_le _ _ _ (jA s ∘ Sum.inr)) ≫ cS.appLE _ (Us s) (hV2'.trans (LBVal.wchart_pull_le _ _ cS _))`. Rewrite using `[Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]`.

Conclude with `Semi.TorusInj.appLE_of_eq F2 _`. Establish `V2 : (ε.appLE _ (Us s) hW2).hom ((LB.pullGen D.toPre.P.L _ _ u (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left).s (jA s ∘ Sum.inr)).val = 1`. Use `(congrArg (ε.appLE _ (Us s) hW2).hom (pullGen_s_val D.toPre.P.L _ _ _)).trans ?_` and prove the remaining obligations. Use `(congrArg (fun ψ => ψ.hom (u.s (jA s ∘ Sum.inr)).val) m2).trans ?_` and prove the remaining obligations. Use `Eq.trans ?_ T2` and prove the remaining obligations.

Conclude with `congrArg (cS.appLE _ (Us s) _).hom (pullGen_s_val D.toPre.P.L _ _ _).symm`. Establish `m3` using `congrArg (fun ψ => ψ.hom ((LB.pullGen D.toPre.P.L _ _ u (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left).s (jA s ∘ Sum.inr)).val) (Scheme.Hom.map_appLE ε hA (homOfLE (fun x hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (Sum.inr k) : LB.wchart D.toPre.P.L (φA U ιD e a χ) (j …`. Establish `LHS1 : (ε.appLE _ (Us s) hA).hom ((lhs U ιD e a χ u).s (jA s)).val = 1` using `L1.trans ((congrArg₂ (· * ·) (m1.trans T1) (m3.trans V2)).trans (_root_.mul_one _))`. Conclude with `(_root_.mul_one _).symm.trans ((congrArg _ R1).symm.trans (P'.symm.trans LHS1))`. Use `eq_local Us hcov _ _ fun s => ?_` and prove the remaining obligations.

Conclude with `(key s).trans (map_one _).symm`.
-/
theorem rho_e (hGF : GlobalFnsSt) (hu : u.IsGen)
    (hu0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (zero2 D.toPre.P.A))
      (LB.oneGen D.toPre.P.L))
    (ρ : Γ((thickObj R I e G).left, ⊤)ˣ) (hρ : PairProp U ιD ιG e a χ u ρ) :
    (eSec (thickObj R I e G)).appTop.hom ρ.val = 1 := by
  classical
  have hL := D.toPre.P.isLB
  have hz0 := u_zero ιD a u hGF hu hu0
  have F1 := eSec_h (I := I) ιG e a
  have F2 := eSec_lift U e χ
  let ε := eSec (thickObj R I e G)
  let cS := ((Over.map (thick R I e)).map η[thickObj R I e G] ≫ toUnit _ ≫ D.toPre.c χ).left
  let S' := (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left
  choose idx hidx using fun s : S' => idx_exists D.toPre.P.L hL s
  let jA : S' → Fin 4 ⊕ Fin 6 → D.toPre.P.L.ι := fun s k => idx s (ε ≫ φA U ιD e a χ k)
  let jB : S' → Fin 4 → D.toPre.P.L.ι := fun s k => idx s (ε ≫ φB U ιG e a χ k)
  let Us : S' → S'.Opens := fun s =>
    LB.wchart D.toPre.P.L (fun k => ε ≫ φB U ιG e a χ k) (jB s) ⊓
      LB.wchart D.toPre.P.L (fun k => ε ≫ φA U ιD e a χ k) (jA s)
  have hUs : ∀ s, s ∈ Us s := fun s =>
    ⟨Set.mem_iInter.2 fun k => hidx s _, Set.mem_iInter.2 fun k => hidx s _⟩
  have hcov : ⨆ s, Us s = ⊤ :=
    top_unique fun s _ => TopologicalSpace.Opens.mem_iSup.2 ⟨s, hUs s⟩
  have key : ∀ s, (ε.appLE ⊤ (Us s) (fun _ _ => trivial)).hom ρ.val = 1 := by
    intro s
    have cA : LB.Coh D.toPre.P.L (φA U ιD e a χ) (jA s) :=
      fun k1 k2 h => congrArg (idx s) (congrArg (ε ≫ ·) h)
    have cB : LB.Coh D.toPre.P.L (φB U ιG e a χ) (jB s) :=
      fun k1 k2 h => congrArg (idx s) (congrArg (ε ≫ ·) h)
    have cross : ∀ k k', φB U ιG e a χ k = φA U ιD e a χ k' → jB s k = jA s k' :=
      fun k k' h => congrArg (idx s) (congrArg (ε ≫ ·) h)
    have P := hρ (jA s) (jB s) cA cB cross
    have hU : Us s ≤ ε ⁻¹ᵁ (LB.wchart D.toPre.P.L (φB U ιG e a χ) (jB s) ⊓
        LB.wchart D.toPre.P.L (φA U ιD e a χ) (jA s)) :=
      fun x hx => ⟨LBVal.wchart_pull_le _ _ ε _ hx.1, LBVal.wchart_pull_le _ _ ε _ hx.2⟩
    have P2 := (congrArg (fun w => (ε.appLE _ (Us s) hU).hom (Units.val w)) P).trans
      (map_mul (ε.appLE _ (Us s) hU).hom _ _)
    have P' := (appLE_res ε _ hU _).symm.trans (P2.trans
      (congrArg₂ (· * ·) (appLE_res ε _ hU ρ) (appLE_res ε _ hU _)))

    have hB : Us s ≤ ε ⁻¹ᵁ LB.wchart D.toPre.P.L (φB U ιG e a χ) (jB s) :=
      fun x hx => LBVal.wchart_pull_le _ _ ε _ hx.1
    have hBO : ∀ k, ε ≫ φB U ιG e a χ k = ε ≫ D.toPre.Oφ (U.gt e).pG χ k := fun k => by
      show ε ≫ ((Over.pullback (thick R I e)).map (ιG.act a)).left ≫ _ = _
      rw [← Category.assoc, F1]
    have R1 : (ε.appLE _ (Us s) hB).hom ((rhs U ιG e a χ).s (jB s)).val = 1 := by
      refine (congrArg (ε.appLE _ (Us s) hB).hom (pullGen_s_val D.toPre.P.L _ _ (jB s))).trans ?_
      have cohB : LB.Coh D.toPre.P.L (fun k => ε ≫ D.toPre.Oφ (U.gt e).pG χ k) (jB s) :=
        fun k1 k2 h => congrArg (idx s) (((hBO k1).trans h).trans (hBO k2).symm)
      have hV : Us s ≤ LB.wchart D.toPre.P.L (fun k => ε ≫ D.toPre.Oφ (U.gt e).pG χ k) (jB s) :=
        fun x hx => Set.mem_iInter.2 fun k => by
          have := Set.mem_iInter.1 hx.1 k
          beta_reduce at this ⊢
          rwa [hBO k] at this
      have m : ((Over.pullback (thick R I e)).map (ιG.act a)).left.appLE _ _
          (LBVal.wchart_pull_le _ _ _ (jB s)) ≫ ε.appLE _ (Us s) hB =
          ε.appLE _ (Us s) (hV.trans (LBVal.wchart_pull_le _ _ ε (jB s))) := by
        rw [Scheme.Hom.appLE_comp_appLE]
        exact Semi.TorusInj.appLE_of_eq F1 _
      rw [← appLE_one D.toPre.P.L ((U.gt e).t χ) ε ((U.gt e).t_unit χ) (jB s) cohB (Us s) hV, ← m]
      rfl

    have hA : Us s ≤ ε ⁻¹ᵁ LB.wchart D.toPre.P.L (φA U ιD e a χ) (jA s) :=
      fun x hx => LBVal.wchart_pull_le _ _ ε _ hx.2
    have M := LBVal.mulGen_val D.toPre.P.L _ _ _ _ ((U.gt e).t (star a • χ))
      (LB.pullGen D.toPre.P.L _ _ u (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left) (jA s) _ le_rfl
    have L1 := (congrArg (ε.appLE _ (Us s) hA).hom ((map_rfl' _).symm.trans M)).trans
      (map_mul (ε.appLE _ (Us s) hA).hom _ _)

    have coh1 : LB.Coh D.toPre.P.L (fun k => ε ≫ D.toPre.Oφ (U.gt e).pG (star a • χ) k)
        (jA s ∘ Sum.inl) := fun k1 k2 h => congrArg (idx s) h
    have hV1 : Us s ≤ LB.wchart D.toPre.P.L (fun k => ε ≫ D.toPre.Oφ (U.gt e).pG (star a • χ) k)
        (jA s ∘ Sum.inl) := fun x hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.2 (Sum.inl k)
    have T1 := appLE_one D.toPre.P.L ((U.gt e).t (star a • χ)) ε ((U.gt e).t_unit _) (jA s ∘ Sum.inl)
      coh1 (Us s) hV1
    have m1 := congrArg (fun ψ => ψ.hom (((U.gt e).t (star a • χ)).s (jA s ∘ Sum.inl)).val)
      (Scheme.Hom.map_appLE ε hA (homOfLE (fun x hx =>
        Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (Sum.inl k) :
          LB.wchart D.toPre.P.L (φA U ιD e a χ) (jA s) ≤ _)).op)

    have hF2k : ∀ k, ε ≫ φA U ιD e a χ (Sum.inr k) = cS ≫ ((zz D.toPre.P.A).left ≫
        rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k) := fun k => by
      show ε ≫ (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left ≫ _ = _
      rw [← Category.assoc, F2, Category.assoc]
    have coh2 : LB.Coh D.toPre.P.L (fun k => cS ≫ ((zz D.toPre.P.A).left ≫
        rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k)) (jA s ∘ Sum.inr) :=
      fun k1 k2 h => congrArg (idx s) (((hF2k k1).trans h).trans (hF2k k2).symm)
    have hV2' : Us s ≤ LB.wchart D.toPre.P.L (fun k => cS ≫ ((zz D.toPre.P.A).left ≫
        rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k)) (jA s ∘ Sum.inr) :=
      fun x hx => Set.mem_iInter.2 fun k => by
        have := Set.mem_iInter.1 hx.2 (Sum.inr k)
        beta_reduce at this ⊢
        rwa [hF2k k] at this
    have T2 := appLE_one D.toPre.P.L (LB.pullGen D.toPre.P.L _ _ u (zz D.toPre.P.A).left) cS
      (corr_one_pull D.toPre.P.L hz0 cS) (jA s ∘ Sum.inr) coh2 (Us s) hV2'
    have hW2 : Us s ≤ ε ⁻¹ᵁ LB.wchart D.toPre.P.L (fun k =>
        (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left ≫
          rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k) (jA s ∘ Sum.inr) :=
      fun x hx => LBVal.wchart_pull_le _ _ ε _ (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx.2 (Sum.inr k))
    have m2 : (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left.appLE _ _
        (LBVal.wchart_pull_le _ _ _ (jA s ∘ Sum.inr)) ≫ ε.appLE _ (Us s) hW2 =
        (zz D.toPre.P.A).left.appLE _ _ (LBVal.wchart_pull_le _ _ _ (jA s ∘ Sum.inr)) ≫
          cS.appLE _ (Us s) (hV2'.trans (LBVal.wchart_pull_le _ _ cS _)) := by
      rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      exact Semi.TorusInj.appLE_of_eq F2 _
    have V2 : (ε.appLE _ (Us s) hW2).hom ((LB.pullGen D.toPre.P.L _ _ u
        (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left).s (jA s ∘ Sum.inr)).val = 1 := by
      refine (congrArg (ε.appLE _ (Us s) hW2).hom (pullGen_s_val D.toPre.P.L _ _ _)).trans ?_
      refine (congrArg (fun ψ => ψ.hom (u.s (jA s ∘ Sum.inr)).val) m2).trans ?_
      refine Eq.trans ?_ T2
      exact congrArg (cS.appLE _ (Us s) _).hom (pullGen_s_val D.toPre.P.L _ _ _).symm
    have m3 := congrArg (fun ψ => ψ.hom ((LB.pullGen D.toPre.P.L _ _ u
        (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left).s (jA s ∘ Sum.inr)).val)
      (Scheme.Hom.map_appLE ε hA (homOfLE (fun x hx =>
        Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (Sum.inr k) :
          LB.wchart D.toPre.P.L (φA U ιD e a χ) (jA s) ≤ _)).op)
    have LHS1 : (ε.appLE _ (Us s) hA).hom ((lhs U ιD e a χ u).s (jA s)).val = 1 :=
      L1.trans ((congrArg₂ (· * ·) (m1.trans T1) (m3.trans V2)).trans (_root_.mul_one _))
    exact (_root_.mul_one _).symm.trans ((congrArg _ R1).symm.trans (P'.symm.trans LHS1))
  refine eq_local Us hcov _ _ fun s => ?_
  exact (key s).trans (map_one _).symm

end Main

end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
