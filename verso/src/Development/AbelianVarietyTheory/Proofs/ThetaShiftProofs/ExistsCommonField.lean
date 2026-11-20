import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcVarZpowInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

noncomputable section

namespace GlobalTheory.ArcTransport

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section General

variable {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]

/- English proof (translation)
Use `choose u hu using fun p q => exists_pw w φ' ε p q`. Establish `glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' φ' q)ˣ, ∀ (y : Y) p, y ∈ LB.wchart L (fun k => φ' k ≫ Φ) p → y ∈ LB.wchart L' φ' q → gm (𝟙 Y) y _ s = (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ Φ) p) (t.s p)`. Introduce `q`. Establish `hv : ∀ (y : Y) p, y ∈ LB.wchart L (fun k => φ' k ≫ Φ) p ⊓ LB.wchart L' φ' q → gm (𝟙 Y) y _ ((u p q)⁻¹ * res inf_le_left (t.s p)) = (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ Φ) p) (t.s p)` using `fun y p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹) (hu p q _ _ y hz))) (gm_res _ y _ hz _))`. Take `⟨s, hs⟩` from `glue_unit _ (fun p => LB.wchart L (fun k => φ' k ≫ Φ) p ⊓ LB.wchart L' φ' q) (fun _ => inf_le_right) (fun y hy => by choose p hp using fun k => exists_chart hL (Φ (φ' k y))`.

Conclude with `Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) (fun p => (u p q)⁻¹ * res inf_le_left (t.s p))`. Use the proof step `(fun p p' y hy => by`. Rewrite using `[hv y p hy.1, hv y p' hy.2, pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.2.1 hy.1.2 hy.1.2, trF_self hL' _ ε (𝟙 Y) y hy.1.2, gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, inv_one, _root_.mul_one, mul_inv, _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])`. Use `⟨s, fun y p h₁ h₂ => ?_⟩` and prove the remaining obligations. Establish `hz : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun k => φ' k ≫ Φ) p ⊓ LB.wchart L' φ' q` using `⟨h₁, h₂⟩`.

Conclude with `(gm_res _ y inf_le_right hz s).symm.trans ((congrArg (gm _ y _) (hs p)).trans (hv y p hz))`. Use `choose s hs using glue`. Use `⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun y p q h₁ h₂ => hs q y p h₁ h₂⟩` and prove the remaining obligations. Use `choose p hp using fun k => exists_chart hL (Φ (φ' k y))`. Establish `m : y ∈ LB.wchart L (fun k => φ' k ≫ Φ) p` using `Set.mem_iInter.2 hp`.

Use `(hs j y p m hj).trans (Eq.trans ?_ (congrArg _ (hs j' y p m hj')).symm)` and prove the remaining obligations. Rewrite using `[pw_trans hw φ' ε (𝟙 Y) y m m hj hj', trF_self hL _ ε (𝟙 Y) y m, _root_.one_mul, mul_inv, inv_inv, _root_.mul_assoc]`.
-/
theorem exists_down_val {w : LB.Iso L' (L.pull Φ)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ Φ) ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧ ∀ (y : Y) p q, y ∈ LB.wchart L (fun k => φ' k ≫ Φ) p →
      y ∈ LB.wchart L' φ' q → gm (𝟙 Y) y (LB.wchart L' φ' q) (a.s q) =
        (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ Φ) p) (t.s p) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' φ' q)ˣ, ∀ (y : Y) p,
      y ∈ LB.wchart L (fun k => φ' k ≫ Φ) p → y ∈ LB.wchart L' φ' q →
      gm (𝟙 Y) y _ s = (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ Φ) p) (t.s p) := by
    intro q
    have hv : ∀ (y : Y) p, y ∈ LB.wchart L (fun k => φ' k ≫ Φ) p ⊓ LB.wchart L' φ' q →
        gm (𝟙 Y) y _ ((u p q)⁻¹ * res inf_le_left (t.s p)) =
          (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ Φ) p) (t.s p) :=
      fun y p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹) (hu p q _ _ y hz)))
        (gm_res _ y _ hz _))
    obtain ⟨s, hs⟩ := glue_unit _ (fun p => LB.wchart L (fun k => φ' k ≫ Φ) p ⊓ LB.wchart L' φ' q) (fun _ => inf_le_right)
      (fun y hy => by
        choose p hp using fun k => exists_chart hL (Φ (φ' k y))
        exact Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) (fun p => (u p q)⁻¹ * res inf_le_left (t.s p))
      (fun p p' y hy => by
        rw [hv y p hy.1, hv y p' hy.2, pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.2.1 hy.1.2 hy.1.2,
          trF_self hL' _ ε (𝟙 Y) y hy.1.2, gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, inv_one, _root_.mul_one, mul_inv,
          _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun y p h₁ h₂ => ?_⟩
    have hz : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun k => φ' k ≫ Φ) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res _ y inf_le_right hz s).symm.trans ((congrArg (gm _ y _) (hs p)).trans (hv y p hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun y p q h₁ h₂ => hs q y p h₁ h₂⟩
  choose p hp using fun k => exists_chart hL (Φ (φ' k y))
  have m : y ∈ LB.wchart L (fun k => φ' k ≫ Φ) p := Set.mem_iInter.2 hp
  refine (hs j y p m hj).trans (Eq.trans ?_ (congrArg _ (hs j' y p m hj')).symm)
  rw [pw_trans hw φ' ε (𝟙 Y) y m m hj hj', trF_self hL _ ε (𝟙 Y) y m, _root_.one_mul, mul_inv, inv_inv, _root_.mul_assoc]

/- English proof (translation)
Use `choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)`. Conclude with `⟨I, hI⟩`.
-/
theorem exists_good' (hL : L.IsLB) (y : Y) : ∃ J, Good L y J := by
  choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
  exact ⟨I, hI⟩

variable {F : Type} [Field F]

def unitStk (y : Sp F) : Fˣ →* ((Sp F).presheaf.stalk y)ˣ := Units.map (toStk y).toMonoidHom

/- English proof (translation)
Establish `z : Sp F` using `(default : PrimeSpectrum F)`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Use `⟨H.1, fun y J J' hJ hJ' => ?_⟩` and prove the remaining obligations. Take `⟨hp, H⟩` from `(genRel_iff w t t₀ x y).1 H`.

Take `rfl : (fun k => pt k ≫ Φ) = pt₀` from `funext hp`. Use `H (fun k => J' (pt k)) (fun k => J (pt k ≫ Φ)) (fun k => hJ (pt k ≫ Φ)) (fun k => hJ' (pt k))` as an intermediate fact. Rewrite using `[vS, vS, val_of t _ y J' (fun k => J' (pt k)) (fun k => by rw [Category.id_comp]), val_of t₀ _ y J (fun k => J (pt k ≫ Φ)) (fun k => by rw [Category.id_comp])]`. Conclude with `Units.ext this`. Introduce and unpack `⟨hp, H⟩`.

Take `rfl : (fun k => pt k ≫ Φ) = pt₀` from `funext hp`. Use `(genRel_iff w t t₀ x z).2 ⟨hp, fun j j₀ h₀ h₁ => ?_⟩` and prove the remaining obligations. Take `⟨J, hJ⟩` from `exists_good' hL z`. Take `⟨J', hJ'⟩` from `exists_good' hL' z`. Establish `H'` using `H z J J' hJ hJ'`.

Rewrite `H'` using `[vS, vS, val_of t _ z J' (fun k => J' (pt k)) (fun k => by rw [Category.id_comp]), val_of t₀ _ z J (fun k => J (pt k ≫ Φ)) (fun k => by rw [Category.id_comp])]`. Establish `m₀ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart L (fun k => pt k ≫ Φ) j₀` using `Set.mem_iInter.2 h₀`. Establish `m₁ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart L' pt j` using `Set.mem_iInter.2 h₁`. Establish `n₀ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart L (fun k => pt k ≫ Φ) (fun k => J (pt k ≫ Φ))` using `Set.mem_iInter.2 fun k => hJ (pt k ≫ Φ)`. Establish `n₁ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart L' pt (fun k => J' (pt k))` using `Set.mem_iInter.2 fun k => hJ' (pt k)`.

Establish `a` using `pw_trans hw pt ε (𝟙 _) z m₀ n₀ m₁ n₁`. Simplify using `only [pw, Category.id_comp] at a`. Establish `key : (∏ k, Geo.Tor.gw w (pt k) z (j₀ k) (j k) ^ ε k) * gm (𝟙 _) z (LB.wchart L' pt j) (t.s j) = unitStk z x * gm (𝟙 _) z (LB.wchart L (fun k => pt k ≫ Φ) j₀) (t₀.s j₀)`. Rewrite using `[a, gen_trans ht (𝟙 _) z m₁ n₁, gen_trans ht₀ (𝟙 _) z m₀ n₀]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Establish `e'` using `congrArg Additive.ofMul H'`. Simplify using `only [ofMul_mul, ofMul_inv] at e' ⊢`. Take the linear combination `(norm := abel) e'`. Conclude with `congrArg Units.val key`.
-/
theorem genRel_val {w : LB.Iso L' (L.pull Φ)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {pt : K → (Sp F ⟶ X')}
    {pt₀ : K → (Sp F ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L' pt ε)} {t₀ : LB.Gen (LB.LinComb L pt₀ ε)}
    (ht : t.IsGen) (ht₀ : t₀.IsGen) (x : Fˣ) :
    GenRel w t t₀ (x : F) ↔ (∀ k, pt k ≫ Φ = pt₀ k) ∧ ∀ (y : Sp F) J J', Good L y J → Good L' y J' →
      (∏ k, Geo.Tor.gw w (pt k) y (J (pt k ≫ Φ)) (J' (pt k)) ^ ε k) * vS t y J' = unitStk y x * vS t₀ y J := by
  have z : Sp F := (default : PrimeSpectrum F)
  constructor
  · intro H
    refine ⟨H.1, fun y J J' hJ hJ' => ?_⟩
    obtain ⟨hp, H⟩ := (genRel_iff w t t₀ x y).1 H
    obtain rfl : (fun k => pt k ≫ Φ) = pt₀ := funext hp
    have := H (fun k => J' (pt k)) (fun k => J (pt k ≫ Φ)) (fun k => hJ (pt k ≫ Φ)) (fun k => hJ' (pt k))
    rw [vS, vS, val_of t _ y J' (fun k => J' (pt k)) (fun k => by rw [Category.id_comp]),
      val_of t₀ _ y J (fun k => J (pt k ≫ Φ)) (fun k => by rw [Category.id_comp])]
    exact Units.ext this
  · rintro ⟨hp, H⟩
    obtain rfl : (fun k => pt k ≫ Φ) = pt₀ := funext hp
    refine (genRel_iff w t t₀ x z).2 ⟨hp, fun j j₀ h₀ h₁ => ?_⟩
    obtain ⟨J, hJ⟩ := exists_good' hL z
    obtain ⟨J', hJ'⟩ := exists_good' hL' z
    have H' := H z J J' hJ hJ'
    rw [vS, vS, val_of t _ z J' (fun k => J' (pt k)) (fun k => by rw [Category.id_comp]),
      val_of t₀ _ z J (fun k => J (pt k ≫ Φ)) (fun k => by rw [Category.id_comp])] at H'
    have m₀ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart L (fun k => pt k ≫ Φ) j₀ := Set.mem_iInter.2 h₀
    have m₁ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart L' pt j := Set.mem_iInter.2 h₁
    have n₀ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart L (fun k => pt k ≫ Φ) (fun k => J (pt k ≫ Φ)) :=
      Set.mem_iInter.2 fun k => hJ (pt k ≫ Φ)
    have n₁ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart L' pt (fun k => J' (pt k)) :=
      Set.mem_iInter.2 fun k => hJ' (pt k)
    have a := pw_trans hw pt ε (𝟙 _) z m₀ n₀ m₁ n₁
    simp only [pw, Category.id_comp] at a
    have key : (∏ k, Geo.Tor.gw w (pt k) z (j₀ k) (j k) ^ ε k) * gm (𝟙 _) z (LB.wchart L' pt j) (t.s j) =
        unitStk z x * gm (𝟙 _) z (LB.wchart L (fun k => pt k ≫ Φ) j₀) (t₀.s j₀) := by
      rw [a, gen_trans ht (𝟙 _) z m₁ n₁, gen_trans ht₀ (𝟙 _) z m₀ n₀]
      apply Additive.ofMul.injective
      have e' := congrArg Additive.ofMul H'
      simp only [ofMul_mul, ofMul_inv] at e' ⊢
      linear_combination (norm := abel) e'
    exact congrArg Units.val key

def unitTop (x : Fˣ) : Γ(Sp F, ⊤)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom x

/- English proof (translation)
Use `(map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ y _ (hJ.mem pt (𝟙 _)) _).trans (Units.ext ?_)) rfl)` and prove the remaining obligations. Rewrite using `[gm_val _ y ⊤ trivial]`. Both sides reduce to the same expression.
-/
theorem vS_scale {pt : K → (Sp F ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L pt ε)) (x : Fˣ) {y : Sp F} {J}
    (hJ : Good L y J) : vS (scaleGen (unitTop x) t) y J = unitStk y x * vS t y J := by
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ y _ (hJ.mem pt (𝟙 _)) _).trans (Units.ext ?_)) rfl)
  rw [gm_val _ y ⊤ trivial]
  rfl

end General

section Pull

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {Φ : D'.P.A.left ⟶ D.P.A.left}

/- English proof (translation)
Take `⟨t, ht, hv⟩` from `exists_up hw D.P.isLB D'.P.isLB (φ' := thφ D'.P.A (x3 D'.P.A)) (ε := thε) D'.cub.t D'.cub.isGen`. Establish `hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 D'.P.A).left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' → val t r z J = (∏ I : thK.{0}, Geo.Tor.gw w (r ≫ thφ D'.P.A (x3 D'.P.A) I) z (J ((r ≫ thφ D'.P.A (x3 D'.P.A) I) ≫ Φ)) (J' (r ≫ thφ D'.P.A (x3 D'.P.A) I)) ^ thε I) * val (L` using `D'.P.L) (φ := thφ D'.P.A (x3 D'.P.A)) (ε := thε) D'.cub.t r z J' := fun Z r z J J' hJ hJ' => by`. Use `(hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl)` and prove the remaining obligations. Rewrite using `[Category.assoc]`. Set `e : 𝟙_ (Over (Sp R')) ⟶ G3 D'.P.A` to `lift 1 (lift 1 1)`.

Establish `sj : Function.Surjective ((snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom` using `surj_comp (surj_snd hG D'.P.isAb _) (surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2)`. Establish `he : e.left ≫ (snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _`. Rewrite using `[Over.w, Over.w]`. Conclude with `Over.w e`. Establish `key` using `gen_unique' D.P.isLB (φ := fun I => (cubeMapOf gp).F3 ≫ thφ D.P.A (x3 D.P.A) I) (ε := thε) (fun V _ k => Finset.prod_congr rfl fun I _ => congrArg (fun q => k q ^ thε I) ((cubeMapOf gp).psum_comm I.down)) _ e.left he sj (pullGen_isGen _ _ _ _ D.cub.isGen (cubeMapOf gp).F3) ht (fu …`.

Establish `C' : IsCub (cubV D'.cub y I')` using `isCub_cubV D'.cub hI'`. Establish `p` using `prod_cub (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) 1 1 (fun q => Geo.Tor.gw w q y (I (q ≫ Φ)) (I' q))`. Rewrite `p` using `[_root_.mul_one, _root_.mul_one]`. Use `Eq.trans ?_ ((hv' _ e.left y I I' hI hI').trans (congrArg₂ (· * ·) p (C'.face 1 1))).symm` and prove the remaining obligations. Establish `o : pushPt gp.1.w (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) = 1` using `map_one (pushHom gp _)`.

Establish `q : e.left ≫ (cubeMapOf gp).F3 = (lift (pushPt gp.1.w (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A)) (lift (pushPt gp.1.w 1) (pushPt gp.1.w 1))).left` using `hom_ext_triple _ fun i => by`. Rewrite using `[Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]`. Apply the tactic sequence `fin_cases i <;> simp [e, x3, pushPt, cubeMapOf]`. Use `(val_pull hI _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[q, o]`.

Use `((isCub_cubV D.cub (T := Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap f)) hI).face 1 1).trans ?_` and prove the remaining obligations. Use the proof step `simp) _ (lift x (lift x' y)).left z J hJ`. Conclude with `(val_pull hJ _ _ _).symm.trans (key.trans (hv' _ _ z J J' hJ hJ'))`.
-/
theorem cub_push (hG : GlobalFnsSt) (gp : IsGrpPullback D'.P.A D.P.A (spMap f) Φ)
    {w : LB.Iso D'.P.L (D.P.L.pull Φ)} (hw : PGen w) {T' : Over (Sp R')} {z : T'.left} {J J'}
    (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') (x x' y : T' ⟶ D'.P.A) :
    val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
        ((lift x (lift x' y)).left ≫ (cubeMapOf gp).F3) z J =
      (∏ I : thK.{0}, Geo.Tor.gw w ((lift x (lift x' y)).left ≫ thφ D'.P.A (x3 D'.P.A) I) z
        (J (((lift x (lift x' y)).left ≫ thφ D'.P.A (x3 D'.P.A) I) ≫ Φ))
        (J' ((lift x (lift x' y)).left ≫ thφ D'.P.A (x3 D'.P.A) I)) ^ thε I) * cubV D'.cub z J' x x' y := by
  obtain ⟨t, ht, hv⟩ := exists_up hw D.P.isLB D'.P.isLB (φ' := thφ D'.P.A (x3 D'.P.A))
    (ε := thε) D'.cub.t D'.cub.isGen
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 D'.P.A).left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val t r z J = (∏ I : thK.{0}, Geo.Tor.gw w (r ≫ thφ D'.P.A (x3 D'.P.A) I) z
        (J ((r ≫ thφ D'.P.A (x3 D'.P.A) I) ≫ Φ)) (J' (r ≫ thφ D'.P.A (x3 D'.P.A) I)) ^ thε I) *
        val (L := D'.P.L) (φ := thφ D'.P.A (x3 D'.P.A)) (ε := thε) D'.cub.t r z J' := fun Z r z J J' hJ hJ' => by
    refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl)
    rw [Category.assoc]
  let e : 𝟙_ (Over (Sp R')) ⟶ G3 D'.P.A := lift 1 (lift 1 1)
  have sj : Function.Surjective ((snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D'.P.isAb _) (surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2)
  have he : e.left ≫ (snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := gen_unique' D.P.isLB (φ := fun I => (cubeMapOf gp).F3 ≫ thφ D.P.A (x3 D.P.A) I) (ε := thε)
    (fun V _ k => Finset.prod_congr rfl fun I _ => congrArg (fun q => k q ^ thε I) ((cubeMapOf gp).psum_comm I.down))
    _ e.left he sj (pullGen_isGen _ _ _ _ D.cub.isGen (cubeMapOf gp).F3) ht (fun y I hI => by
      choose I' hI' using fun χ : (𝟙_ (Over (Sp R'))).left ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ y)
      have C' : IsCub (cubV D'.cub y I') := isCub_cubV D'.cub hI'
      have p := prod_cub (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) 1 1
        (fun q => Geo.Tor.gw w q y (I (q ≫ Φ)) (I' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine Eq.trans ?_ ((hv' _ e.left y I I' hI hI').trans (congrArg₂ (· * ·) p (C'.face 1 1))).symm
      have o : pushPt gp.1.w (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) = 1 := map_one (pushHom gp _)
      have q : e.left ≫ (cubeMapOf gp).F3 =
          (lift (pushPt gp.1.w (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A)) (lift (pushPt gp.1.w 1)
            (pushPt gp.1.w 1))).left := hom_ext_triple _ fun i => by
        rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
        fin_cases i <;> simp [e, x3, pushPt, cubeMapOf]
      refine (val_pull hI _ _ _).trans ?_
      rw [q, o]
      refine ((isCub_cubV D.cub (T := Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap f)) hI).face 1 1).trans ?_
      simp) _ (lift x (lift x' y)).left z J hJ
  exact (val_pull hJ _ _ _).symm.trans (key.trans (hv' _ _ z J J' hJ hJ'))

variable {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]

/- English proof (translation)
The claim follows from `(Category.assoc _ _ _).trans (((congrArg (jFK (R := R') F ≫ ·) (spMap_comp f _).symm).trans (spMap_comp _ _).symm).trans ((congrArg spMap (RingHom.ext fun r => (hF r).symm)).trans (spMap_comp _ _)))`.
-/
theorem base_comm (hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (f r))) :
    (TF (R := R') F).hom ≫ spMap f = (TF (R := R) F).hom :=
  (Category.assoc _ _ _).trans (((congrArg (jFK (R := R') F ≫ ·) (spMap_comp f _).symm).trans (spMap_comp _ _).symm).trans
      ((congrArg spMap (RingHom.ext fun r => (hF r).symm)).trans (spMap_comp _ _)))

def wVal (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (y : Sp F) (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι)
    (J' : (Sp F ⟶ D'.P.A.left) → D'.P.L.ι) (x : TF (R := R') F ⟶ D'.P.A) : ((Sp F).presheaf.stalk y)ˣ :=
  Geo.Tor.gw w x.left y (J (x.left ≫ Φ)) (J' x.left)

def GtRel (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (e : D.X ≃+ D'.X) (u : D.X → Fˣ) (g₀ : GtPtF D F) (g : GtPtF D' F) :
    Prop :=
  ∀ z, GenRel w (g.s (e z)) (g₀.s z) (u z : F)

variable (gp : IsGrpPullback D'.P.A D.P.A (spMap f) Φ) (hT : (TF (R := R') F).hom ≫ spMap f = (TF (R := R) F).hom)

def pushF (x : TF (R := R') F ⟶ D'.P.A) : TF (R := R) F ⟶ D.P.A :=
  Over.homMk (x.left ≫ Φ) ((Over.w (pushPt gp.1.w x)).trans hT)

/- English proof (translation)
The claim follows from `Over.OverMorphism.ext ((gp.2 _ x y _ _ rfl rfl).symm.trans (mul_left_congr hT (pushPt gp.1.w x) (pushPt gp.1.w y) (pushF gp hT x) (pushF gp hT y) rfl rfl))`.
-/
theorem pushF_mul (x y : TF (R := R') F ⟶ D'.P.A) : pushF gp hT (x * y) = pushF gp hT x * pushF gp hT y :=
  Over.OverMorphism.ext ((gp.2 _ x y _ _ rfl rfl).symm.trans
    (mul_left_congr hT (pushPt gp.1.w x) (pushPt gp.1.w y) (pushF gp hT x) (pushF gp hT y) rfl rfl))

/- English proof (translation)
The claim follows from `mul_eq_left.1 ((pushF_mul gp hT 1 1).symm.trans (congrArg (pushF gp hT) (_root_.mul_one 1)))`.
-/
theorem pushF_one : pushF gp hT 1 = 1 :=
  mul_eq_left.1 ((pushF_mul gp hT 1 1).symm.trans (congrArg (pushF gp hT) (_root_.mul_one 1)))

/- English proof (translation)
Introduce `x y h` and use `Over.OverMorphism.ext (gp.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))`.
-/
theorem pushF_injective : Function.Injective (pushF gp hT) := fun x y h =>
  Over.OverMorphism.ext (gp.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))

/- English proof (translation)
Introduce `b` and use `⟨Over.homMk (gp.1.lift b.left (TF (R := R') F).hom ((Over.w b).trans hT.symm)) (gp.1.lift_snd _ _ _), Over.OverMorphism.ext (gp.1.lift_fst _ _ _)⟩`.
-/
theorem pushF_surjective : Function.Surjective (pushF gp hT) := fun b =>
  ⟨Over.homMk (gp.1.lift b.left (TF (R := R') F).hom ((Over.w b).trans hT.symm)) (gp.1.lift_snd _ _ _),
    Over.OverMorphism.ext (gp.1.lift_fst _ _ _)⟩

variable {e : D.X ≃+ D'.X} (hc : ∀ y, (D'.c (e y)).left ≫ Φ = spMap f ≫ (D.c y).left)

include hc in
/- English proof (translation)
The claim follows from `Over.OverMorphism.ext (by show ((TF (R := R') F).hom ≫ (D'.c (e χ)).left) ≫ Φ = (TF (R := R) F).hom ≫ (D.c χ).left rw [Category.assoc, hc, ← Category.assoc] exact congrArg (· ≫ _) hT)`.
-/
theorem pushF_cP (χ : D.X) : pushF gp hT (cP D' _ (e χ)) = cP D _ χ := Over.OverMorphism.ext (by
    show ((TF (R := R') F).hom ≫ (D'.c (e χ)).left) ≫ Φ = (TF (R := R) F).hom ≫ (D.c χ).left
    rw [Category.assoc, hc, ← Category.assoc]
    exact congrArg (· ≫ _) hT)

include hc in
/- English proof (translation)
Use `fin_cases i`. Conclude with `congrArg (fun q => q.left) ((pushF_mul gp hT (cP D' _ (e χ)) b).trans (congrArg (· * pushF gp hT b) (pushF_cP gp hT hc χ)))`. Conclude with `congrArg (fun q => q.left) (pushF_cP gp hT hc χ)`. Both sides reduce to the same expression. Conclude with `congrArg (fun q => q.left) (pushF_one gp hT)`.
-/
theorem gtφ_push (b : TF (R := R') F ⟶ D'.P.A) (χ : D.X) (i : Fin 4) :
    DegPre.gtφ D' F b (e χ) i ≫ Φ = DegPre.gtφ D F (pushF gp hT b) χ i := by
  fin_cases i
  · exact congrArg (fun q => q.left) ((pushF_mul gp hT (cP D' _ (e χ)) b).trans
      (congrArg (· * pushF gp hT b) (pushF_cP gp hT hc χ)))
  · exact congrArg (fun q => q.left) (pushF_cP gp hT hc χ)
  · rfl
  · exact congrArg (fun q => q.left) (pushF_one gp hT)

variable {w : LB.Iso D'.P.L (D.P.L.pull Φ)} (hw : PGen w)

include hw in
/- English proof (translation)
Establish `e` using `cub_push hG gp hw (T' := TF (R := R') F) hJ hJ' a b c`. Establish `q : (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 = (lift (pushF gp hT a) (lift (pushF gp hT b) (pushF gp hT c))).left` using `hom_ext_triple _ fun i => by`. Rewrite using `[Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]`. Apply the tactic sequence `fin_cases i <;> simp [x3] <;> rfl`. Rewrite `e` using `[q]`.

Conclude with `e.trans (congrArg₂ (· * ·) (prod_cub a b c (fun q => Geo.Tor.gw w q y (J (q ≫ Φ)) (J' q))) rfl)`.
-/
theorem thS_push (hG : GlobalFnsSt) {y : Sp F} {J J'} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J')
    (a b c : TF (R := R') F ⟶ D'.P.A) :
    thS D y J (pushF gp hT a) (pushF gp hT b) (pushF gp hT c) =
      wVal w y J J' (a * b * c) * (wVal w y J J' (a * b))⁻¹ * (wVal w y J J' (a * c))⁻¹ * (wVal w y J J' (b * c))⁻¹ *
        wVal w y J J' a * wVal w y J J' b * wVal w y J J' c * (wVal w y J J' 1)⁻¹ * thS D' y J' a b c := by
  have e := cub_push hG gp hw (T' := TF (R := R') F) hJ hJ' a b c
  have q : (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 =
      (lift (pushF gp hT a) (lift (pushF gp hT b) (pushF gp hT c))).left := hom_ext_triple _ fun i => by
    rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;> simp [x3] <;> rfl
  rw [q] at e
  exact e.trans (congrArg₂ (· * ·) (prod_cub a b c (fun q => Geo.Tor.gw w q y (J (q ≫ Φ)) (J' q))) rfl)

include hc hw in
/- English proof (translation)
Establish `key` using `fun χ => genRel_val hw D.P.isLB D'.P.isLB (g.isGen (e χ)) (g₀.isGen χ) (u χ)`. Establish `pr` using `fun χ (y : Sp F) (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι) (J' : (Sp F ⟶ D'.P.A.left) → D'.P.L.ι) => prod_gt g.b (e χ) (fun q => Geo.Tor.gw w q y (J (q ≫ Φ)) (J' q))`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Conclude with `⟨Over.OverMorphism.ext ((H 0).1 2), fun χ y J J' hJ hJ' => (congrArg (fun q : ((Sp F).presheaf.stalk y)ˣ => q * vS (g.s (e χ)) y J') (pr χ y J J').symm).trans (((key χ).1 (H χ)).2 y J J' hJ hJ')⟩`.

Introduce and unpack `⟨hb, H⟩ χ`. Conclude with `(key χ).2 ⟨fun i => by rw [← hb]; exact gtφ_push gp hT hc _ _ i, fun y J J' hJ hJ' => (congrArg (fun q : ((Sp F).presheaf.stalk y)ˣ => q * vS (g.s (e χ)) y J') (pr χ y J J')).trans (H χ y J J' hJ hJ')⟩`.
-/
theorem gtRel_iff (u : D.X → Fˣ) (g₀ : GtPtF D F) (g : GtPtF D' F) :
    GtRel w e u g₀ g ↔ pushF gp hT g.b = g₀.b ∧ ∀ χ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' →
      (wVal w y J J' (cP D' _ (e χ) * g.b))⁻¹ * wVal w y J J' (cP D' _ (e χ)) * wVal w y J J' g.b *
        (wVal w y J J' 1)⁻¹ * vS (g.s (e χ)) y J' = unitStk y (u χ) * vS (g₀.s χ) y J := by
  have key := fun χ => genRel_val hw D.P.isLB D'.P.isLB (g.isGen (e χ)) (g₀.isGen χ) (u χ)
  have pr := fun χ (y : Sp F) (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι) (J' : (Sp F ⟶ D'.P.A.left) → D'.P.L.ι) =>
    prod_gt g.b (e χ) (fun q => Geo.Tor.gw w q y (J (q ≫ Φ)) (J' q))
  constructor
  · intro H
    exact ⟨Over.OverMorphism.ext ((H 0).1 2), fun χ y J J' hJ hJ' =>
      (congrArg (fun q : ((Sp F).presheaf.stalk y)ˣ => q * vS (g.s (e χ)) y J') (pr χ y J J').symm).trans (((key χ).1 (H χ)).2 y J J' hJ hJ')⟩
  · rintro ⟨hb, H⟩ χ
    exact (key χ).2 ⟨fun i => by rw [← hb]; exact gtφ_push gp hT hc _ _ i, fun y J J' hJ hJ' =>
      (congrArg (fun q : ((Sp F).presheaf.stalk y)ˣ => q * vS (g.s (e χ)) y J') (pr χ y J J')).trans (H χ y J J' hJ hJ')⟩

include gp hT hc hw in

/- English proof (translation)
Take `⟨b, hb⟩` from `pushF_surjective gp hT g₀.b`. Establish `u0 : u 0 = 1` using `mul_eq_left.1 ((hu 0 0).symm.trans (congrArg u (add_zero 0)))`. Establish `ex : ∀ χ, ∃ a : LB.Gen (LB.LinComb D'.P.L (DegPre.gtφ D' F b (e χ)) DegPre.gtε), a.IsGen ∧ ∀ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' → (wVal w y J J' (cP D' _ (e χ) * b))⁻¹ * wVal w y J J' (cP D' _ (e χ)) * wVal w y J J' b * (wVal w y J J' 1)⁻¹ * vS (F` using `F) a y J' = unitStk y (u χ) * vS (g₀.s χ) y J := by`. Introduce `χ`. Take `⟨t, ht, vt⟩` from `exists_gen D.P.isLB (φ' := fun i => DegPre.gtφ D' F b (e χ) i ≫ Φ) (ε' := DegPre.gtε) (fun U _ h => Finset.prod_congr rfl fun i _ => congrArg (fun q => h q ^ DegPre.gtε i) (by rw [← hb]; exact (gtφ_push gp hT hc b χ i).symm)) (scaleGen (unitTop (u χ)) (g₀.s χ)) (scaleGen_isGen _ …`.

Take `⟨a, ha, va⟩` from `exists_down_val hw D.P.isLB D'.P.isLB t ht`. Use `⟨a, ha, fun y J J' hJ hJ' => ?_⟩` and prove the remaining obligations. Establish `v₁ : vS a y J' = (pw (Y` using `Sp F) (Z := Sp F) w (DegPre.gtφ D' F b (e χ)) DegPre.gtε (𝟙 _) y (fun k => J (𝟙 _ ≫ DegPre.gtφ D' F b (e χ) k ≫ Φ)) (fun k => J' (𝟙 _ ≫ DegPre.gtφ D' F b (e χ) k)))⁻¹ * vS t y J := va y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))`. Establish `v₂ : vS t y J = unitStk y (u χ) * vS (g₀.s χ) y J` using `(vt _ _ y J hJ).trans (vS_scale _ _ hJ)`. Establish `v₃ : pw (Y` using `Sp F) (Z := Sp F) w (DegPre.gtφ D' F b (e χ)) DegPre.gtε (𝟙 _) y (fun k => J (𝟙 _ ≫ DegPre.gtφ D' F b (e χ) k ≫ Φ)) (fun k => J' (𝟙 _ ≫ DegPre.gtφ D' F b (e χ) k)) = (wVal w y J J' (cP D' _ (e χ) * b))⁻¹ * wVal w y J J' (cP D' _ (e χ)) * wVal w y J J' b * (wVal w y J J' 1)⁻¹ := b …`.

Use `Eq.trans ?_ (prod_gt b (e χ) (fun q => Geo.Tor.gw w q y (J (q ≫ Φ)) (J' q)))` and prove the remaining obligations. Simplify using `only [pw, Category.id_comp]`. Rewrite using `[v₁, v₂, ← v₃]`. Conclude with `mul_inv_cancel_left _ _`. Use `choose t ht vt using ex`.

Take `⟨g, hgb, hg⟩` from `exists_gt b (fun χ => t (e.symm χ)) (fun χ => ht _) (fun χ U _ h => Finset.prod_congr rfl fun i _ => congrArg (fun q => h q ^ DegPre.gtε i) (by rw [AddEquiv.apply_symm_apply])) (fun y J' hJ' => by`. Take `⟨J, hJ⟩` from `exists_good' D.P.isLB (Y := Sp F) y`. Establish `z : vS (g₀.s 0) y J = 1` using `(val_corr hJ g₀.s_zero _).trans (val_one _)`. Establish `v` using `vt 0 y J J' hJ hJ'`. Use `show vS (t (e.symm 0)) y J' = 1`.

Rewrite using `[map_zero e.symm]`. Rewrite `v` using `[z, u0, map_one, _root_.mul_one, show cP D' (TF (R := R') F) (e 0) = 1 by rw [map_zero, cPoint_zero], _root_.one_mul]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `e'` using `congrArg Additive.ofMul v`. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_one] at e' ⊢`.

Take the linear combination `(norm := abel) e') (fun χ χ' y J' hJ' => by`. Take `⟨J, hJ⟩` from `exists_good' D.P.isLB (Y := Sp F) y`. Take `⟨χ, rfl⟩` from `e.surjective χ`. Take `⟨χ', rfl⟩` from `e.surjective χ'`. Establish `e₀` using `gt_mul (𝟙 (TF (R := R) F)) hJ g₀ χ χ'`.

Rewrite `e₀` using `[Category.id_comp]`. Establish `e₁ : vS (g₀.s (χ + χ')) y J * thS D y J (cP D _ χ) (cP D _ χ') g₀.b = vS (g₀.s χ) y J * vS (g₀.s χ') y J` using `e₀`. Use `show vS (t (e.symm (e χ + e χ'))) y J' * thS D' y J' (cP D' _ (e χ)) (cP D' _ (e χ')) b = vS (t (e.symm (e χ))) y J' * vS (t (e.symm (e χ'))) y J'`. Rewrite using `[← map_add, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]`. Establish `c` using `thS_push gp hT hw hG hJ hJ' (cP D' _ (e χ)) (cP D' _ (e χ')) b`.

Rewrite `c` using `[pushF_cP gp hT hc, pushF_cP gp hT hc, hb]`. Rewrite `e₁` using `[c]`. Establish `v₁` using `vt χ y J J' hJ hJ'`. Establish `v₂` using `vt χ' y J J' hJ hJ'`. Establish `v₃` using `vt (χ + χ') y J J' hJ hJ'`.

Rewrite `v₃` using `[show cP D' (TF (R := R') F) (e (χ + χ')) = cP D' _ (e χ) * cP D' _ (e χ') by rw [map_add, cPoint_add], hu, map_mul]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `a₁` using `congrArg Additive.ofMul e₁`. Establish `b₁` using `congrArg Additive.ofMul v₁`. Establish `b₂` using `congrArg Additive.ofMul v₂`.

Establish `b₃` using `congrArg Additive.ofMul v₃`. Simplify using `only [ofMul_mul, ofMul_inv] at a₁ b₁ b₂ b₃ ⊢`. Take the linear combination `(norm := abel) a₁ - b₁ - b₂ + b₃)`. Use `⟨g, (gtRel_iff gp hT hc hw u g₀ g).2 ⟨by rw [hgb, hb], fun χ y J J' hJ hJ' => ?_⟩⟩` and prove the remaining obligations. Establish `v : vS (g.s (e χ)) y J' = vS (t (e.symm (e χ))) y J'` using `hg _ y J' hJ'`.

Rewrite using `[v, AddEquiv.symm_apply_apply, hgb]`. Conclude with `vt χ y J J' hJ hJ'`.
-/
theorem exists_gtRel (hG : GlobalFnsSt) (u : D.X → Fˣ) (hu : ∀ a b, u (a + b) = u a * u b) (g₀ : GtPtF D F) :
    ∃ g : GtPtF D' F, GtRel w e u g₀ g := by
  obtain ⟨b, hb⟩ := pushF_surjective gp hT g₀.b
  have u0 : u 0 = 1 := mul_eq_left.1 ((hu 0 0).symm.trans (congrArg u (add_zero 0)))
  have ex : ∀ χ, ∃ a : LB.Gen (LB.LinComb D'.P.L (DegPre.gtφ D' F b (e χ)) DegPre.gtε), a.IsGen ∧
      ∀ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' →
      (wVal w y J J' (cP D' _ (e χ) * b))⁻¹ * wVal w y J J' (cP D' _ (e χ)) * wVal w y J J' b *
        (wVal w y J J' 1)⁻¹ * vS (F := F) a y J' = unitStk y (u χ) * vS (g₀.s χ) y J := by
    intro χ
    obtain ⟨t, ht, vt⟩ := exists_gen D.P.isLB (φ' := fun i => DegPre.gtφ D' F b (e χ) i ≫ Φ) (ε' := DegPre.gtε)
      (fun U _ h => Finset.prod_congr rfl fun i _ => congrArg (fun q => h q ^ DegPre.gtε i)
        (by rw [← hb]; exact (gtφ_push gp hT hc b χ i).symm))
      (scaleGen (unitTop (u χ)) (g₀.s χ)) (scaleGen_isGen _ _ (g₀.isGen χ))
    obtain ⟨a, ha, va⟩ := exists_down_val hw D.P.isLB D'.P.isLB t ht
    refine ⟨a, ha, fun y J J' hJ hJ' => ?_⟩
    have v₁ : vS a y J' = (pw (Y := Sp F) (Z := Sp F) w (DegPre.gtφ D' F b (e χ)) DegPre.gtε (𝟙 _) y
        (fun k => J (𝟙 _ ≫ DegPre.gtφ D' F b (e χ) k ≫ Φ)) (fun k => J' (𝟙 _ ≫ DegPre.gtφ D' F b (e χ) k)))⁻¹ *
        vS t y J := va y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have v₂ : vS t y J = unitStk y (u χ) * vS (g₀.s χ) y J := (vt _ _ y J hJ).trans (vS_scale _ _ hJ)
    have v₃ : pw (Y := Sp F) (Z := Sp F) w (DegPre.gtφ D' F b (e χ)) DegPre.gtε (𝟙 _) y
        (fun k => J (𝟙 _ ≫ DegPre.gtφ D' F b (e χ) k ≫ Φ)) (fun k => J' (𝟙 _ ≫ DegPre.gtφ D' F b (e χ) k)) =
        (wVal w y J J' (cP D' _ (e χ) * b))⁻¹ * wVal w y J J' (cP D' _ (e χ)) * wVal w y J J' b *
          (wVal w y J J' 1)⁻¹ := by
      refine Eq.trans ?_ (prod_gt b (e χ) (fun q => Geo.Tor.gw w q y (J (q ≫ Φ)) (J' q)))
      simp only [pw, Category.id_comp]
    rw [v₁, v₂, ← v₃]
    exact mul_inv_cancel_left _ _
  choose t ht vt using ex
  obtain ⟨g, hgb, hg⟩ := exists_gt b (fun χ => t (e.symm χ)) (fun χ => ht _) (fun χ U _ h =>
      Finset.prod_congr rfl fun i _ => congrArg (fun q => h q ^ DegPre.gtε i)
        (by rw [AddEquiv.apply_symm_apply])) (fun y J' hJ' => by
      obtain ⟨J, hJ⟩ := exists_good' D.P.isLB (Y := Sp F) y
      have z : vS (g₀.s 0) y J = 1 := (val_corr hJ g₀.s_zero _).trans (val_one _)
      have v := vt 0 y J J' hJ hJ'
      show vS (t (e.symm 0)) y J' = 1
      rw [map_zero e.symm]
      rw [z, u0, map_one, _root_.mul_one, show cP D' (TF (R := R') F) (e 0) = 1 by rw [map_zero, cPoint_zero],
        _root_.one_mul] at v
      apply Additive.ofMul.injective
      have e' := congrArg Additive.ofMul v
      simp only [ofMul_mul, ofMul_inv, ofMul_one] at e' ⊢
      linear_combination (norm := abel) e') (fun χ χ' y J' hJ' => by
      obtain ⟨J, hJ⟩ := exists_good' D.P.isLB (Y := Sp F) y
      obtain ⟨χ, rfl⟩ := e.surjective χ
      obtain ⟨χ', rfl⟩ := e.surjective χ'
      have e₀ := gt_mul (𝟙 (TF (R := R) F)) hJ g₀ χ χ'
      rw [Category.id_comp] at e₀
      have e₁ : vS (g₀.s (χ + χ')) y J * thS D y J (cP D _ χ) (cP D _ χ') g₀.b = vS (g₀.s χ) y J * vS (g₀.s χ') y J := e₀
      show vS (t (e.symm (e χ + e χ'))) y J' * thS D' y J' (cP D' _ (e χ)) (cP D' _ (e χ')) b =
        vS (t (e.symm (e χ))) y J' * vS (t (e.symm (e χ'))) y J'
      rw [← map_add, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
      have c := thS_push gp hT hw hG hJ hJ' (cP D' _ (e χ)) (cP D' _ (e χ')) b
      rw [pushF_cP gp hT hc, pushF_cP gp hT hc, hb] at c
      rw [c] at e₁
      have v₁ := vt χ y J J' hJ hJ'
      have v₂ := vt χ' y J J' hJ hJ'
      have v₃ := vt (χ + χ') y J J' hJ hJ'
      rw [show cP D' (TF (R := R') F) (e (χ + χ')) = cP D' _ (e χ) * cP D' _ (e χ') by rw [map_add, cPoint_add], hu,
        map_mul] at v₃
      apply Additive.ofMul.injective
      have a₁ := congrArg Additive.ofMul e₁
      have b₁ := congrArg Additive.ofMul v₁
      have b₂ := congrArg Additive.ofMul v₂
      have b₃ := congrArg Additive.ofMul v₃
      simp only [ofMul_mul, ofMul_inv] at a₁ b₁ b₂ b₃ ⊢
      linear_combination (norm := abel) a₁ - b₁ - b₂ + b₃)
  refine ⟨g, (gtRel_iff gp hT hc hw u g₀ g).2 ⟨by rw [hgb, hb], fun χ y J J' hJ hJ' => ?_⟩⟩
  have v : vS (g.s (e χ)) y J' = vS (t (e.symm (e χ))) y J' := hg _ y J' hJ'
  rw [v, AddEquiv.symm_apply_apply, hgb]
  exact vt χ y J J' hJ hJ'

include gp hT hc hw in

/- English proof (translation)
Take `⟨b₁, v₁⟩` from `(gtRel_iff gp hT hc hw u g₀ g).1 h`. Take `⟨b₂, v₂⟩` from `(gtRel_iff gp hT hc hw u g₀ g').1 h'`. Establish `hb : g.b = g'.b` using `pushF_injective gp hT (b₁.trans b₂.symm)`. Take `⟨b, s, hs, s0, sm⟩` from `g`. Take `⟨b', s', hs', s0', sm'⟩` from `g'`.

Take `rfl : b = b'` from `hb`. Take `rfl : s = s'` from `funext fun χ => by`. Take `⟨χ, rfl⟩` from `e.surjective χ`. Establish `: (s (e χ)).s = (s' (e χ)).s` using `funext fun j => unit_ext fun y hy => by`. Take `⟨J, hJ⟩` from `exists_good' D.P.isLB (Y := Sp F) y`.

Take `⟨J', hJ'⟩` from `exists_good' D'.P.isLB (Y := Sp F) y`. Establish `v : vS (s (e χ)) y J' = vS (s' (e χ)) y J'` using `mul_left_cancel ((v₁ χ y J J' hJ hJ').trans (v₂ χ y J J' hJ hJ').symm)`. Conclude with `(gen_trans (hs _) (𝟙 _) y hy (hJ'.mem _ (𝟙 _))).trans ((congrArg _ v).trans (gen_trans (hs' _) (𝟙 _) y hy (hJ'.mem _ (𝟙 _))).symm)`. Consider the cases of `h₁ : s (e χ)`. Consider the cases of `h₂ : s' (e χ)`.

Rewrite `this` using `[h₁, h₂]`. Conclude with `congrArg _ this`. Both sides reduce to the same expression.
-/
theorem GtRel.unique {u : D.X → Fˣ} {g₀ : GtPtF D F} {g g' : GtPtF D' F} (h : GtRel w e u g₀ g)
    (h' : GtRel w e u g₀ g') : g = g' := by
  obtain ⟨b₁, v₁⟩ := (gtRel_iff gp hT hc hw u g₀ g).1 h
  obtain ⟨b₂, v₂⟩ := (gtRel_iff gp hT hc hw u g₀ g').1 h'
  have hb : g.b = g'.b := pushF_injective gp hT (b₁.trans b₂.symm)
  obtain ⟨b, s, hs, s0, sm⟩ := g
  obtain ⟨b', s', hs', s0', sm'⟩ := g'
  obtain rfl : b = b' := hb
  obtain rfl : s = s' := funext fun χ => by
    obtain ⟨χ, rfl⟩ := e.surjective χ
    have : (s (e χ)).s = (s' (e χ)).s := funext fun j => unit_ext fun y hy => by
      obtain ⟨J, hJ⟩ := exists_good' D.P.isLB (Y := Sp F) y
      obtain ⟨J', hJ'⟩ := exists_good' D'.P.isLB (Y := Sp F) y
      have v : vS (s (e χ)) y J' = vS (s' (e χ)) y J' :=
        mul_left_cancel ((v₁ χ y J J' hJ hJ').trans (v₂ χ y J J' hJ hJ').symm)
      exact (gen_trans (hs _) (𝟙 _) y hy (hJ'.mem _ (𝟙 _))).trans ((congrArg _ v).trans
        (gen_trans (hs' _) (𝟙 _) y hy (hJ'.mem _ (𝟙 _))).symm)
    cases h₁ : s (e χ)
    cases h₂ : s' (e χ)
    rw [h₁, h₂] at this
    exact congrArg _ this
  rfl

include gp hT hc hw in
/- English proof (translation)
Take `⟨b₁, v₁⟩` from `(gtRel_iff gp hT hc hw _ _ _).1 h`. Take `⟨b₂, v₂⟩` from `(gtRel_iff gp hT hc hw _ _ _).1 h'`. Take `⟨b₃, v₃⟩` from `(gtRel_iff gp hT hc hw _ _ _).1 h''`. Take `⟨b₀, v₀⟩` from `(isAdd_iff _ _ _).1 H`. Establish `hb : g''.b = g.b * g'.b` using `pushF_injective gp hT (by rw [pushF_mul, b₁, b₂, b₃, b₀])`.

Use `(isAdd_iff _ _ _).2 ⟨hb, fun χ y J' hJ' => ?_⟩` and prove the remaining obligations. Take `⟨J, hJ⟩` from `exists_good' D.P.isLB (Y := Sp F) y`. Take `⟨χ, rfl⟩` from `e.surjective χ`. Establish `e₁ : vS (g₀''.s χ) y J * thS D y J (cP D _ χ) g₀.b g₀'.b = vS (g₀.s χ) y J * vS (g₀'.s χ) y J` using `v₀ χ y J hJ`. Use `show vS (g''.s (e χ)) y J' * thS D' y J' (cP D' _ (e χ)) g.b g'.b = vS (g.s (e χ)) y J' * vS (g'.s (e χ)) y J'`.

Establish `c` using `thS_push gp hT hw hG hJ hJ' (cP D' _ (e χ)) g.b g'.b`. Rewrite `c` using `[pushF_cP gp hT hc, b₁, b₂, _root_.mul_assoc (cP D' _ (e χ)), ← hb]`. Rewrite `e₁` using `[c]`. Establish `w₃` using `v₃ χ y J J' hJ hJ'`. Rewrite `w₃` using `[hu, map_mul]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `a₁` using `congrArg Additive.ofMul e₁`. Establish `c₁` using `congrArg Additive.ofMul (v₁ χ y J J' hJ hJ')`. Establish `c₂` using `congrArg Additive.ofMul (v₂ χ y J J' hJ hJ')`. Establish `c₃` using `congrArg Additive.ofMul w₃`.

Simplify using `only [ofMul_mul, ofMul_inv] at a₁ c₁ c₂ c₃ ⊢`. Take the linear combination `(norm := abel) a₁ - c₁ - c₂ + c₃`.
-/
theorem GtRel.isAdd (hG : GlobalFnsSt) {u u' u'' : D.X → Fˣ} (hu : ∀ χ, u'' χ = u χ * u' χ) {g₀ g₀' g₀'' : GtPtF D F}
    {g g' g'' : GtPtF D' F} (h : GtRel w e u g₀ g) (h' : GtRel w e u' g₀' g') (h'' : GtRel w e u'' g₀'' g'')
    (H : g₀.IsAdd g₀' g₀'') : g.IsAdd g' g'' := by
  obtain ⟨b₁, v₁⟩ := (gtRel_iff gp hT hc hw _ _ _).1 h
  obtain ⟨b₂, v₂⟩ := (gtRel_iff gp hT hc hw _ _ _).1 h'
  obtain ⟨b₃, v₃⟩ := (gtRel_iff gp hT hc hw _ _ _).1 h''
  obtain ⟨b₀, v₀⟩ := (isAdd_iff _ _ _).1 H
  have hb : g''.b = g.b * g'.b := pushF_injective gp hT (by rw [pushF_mul, b₁, b₂, b₃, b₀])
  refine (isAdd_iff _ _ _).2 ⟨hb, fun χ y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB (Y := Sp F) y
  obtain ⟨χ, rfl⟩ := e.surjective χ
  have e₁ : vS (g₀''.s χ) y J * thS D y J (cP D _ χ) g₀.b g₀'.b = vS (g₀.s χ) y J * vS (g₀'.s χ) y J := v₀ χ y J hJ
  show vS (g''.s (e χ)) y J' * thS D' y J' (cP D' _ (e χ)) g.b g'.b = vS (g.s (e χ)) y J' * vS (g'.s (e χ)) y J'
  have c := thS_push gp hT hw hG hJ hJ' (cP D' _ (e χ)) g.b g'.b
  rw [pushF_cP gp hT hc, b₁, b₂, _root_.mul_assoc (cP D' _ (e χ)), ← hb] at c
  rw [c] at e₁
  have w₃ := v₃ χ y J J' hJ hJ'
  rw [hu, map_mul] at w₃
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁
  have c₁ := congrArg Additive.ofMul (v₁ χ y J J' hJ hJ')
  have c₂ := congrArg Additive.ofMul (v₂ χ y J J' hJ hJ')
  have c₃ := congrArg Additive.ofMul w₃
  simp only [ofMul_mul, ofMul_inv] at a₁ c₁ c₂ c₃ ⊢
  linear_combination (norm := abel) a₁ - c₁ - c₂ + c₃

include gp hT hc hw in

/- English proof (translation)
Take `⟨b₁, v₁⟩` from `(gtRel_iff gp hT hc hw _ _ _).1 h`. Establish `hb' : g.b = 1` using `pushF_injective gp hT (by rw [pushF_one, b₁, hb])`. Use `⟨hb', fun χ y J J' hJ hJ' => ?_⟩` and prove the remaining obligations. Establish `v` using `v₁ χ y J J' hJ hJ'`. Rewrite `v` using `[show cP D' (TF (R := R') F) (e χ) * g.b = cP D' _ (e χ) by rw [hb', _root_.mul_one], show wVal w y J J' g.b = wVal w y J J' 1 by rw [hb'], inv_mul_cancel, _root_.one_mul, mul_inv_cancel, _root_.one_mul]`.

Conclude with `v`.
-/
theorem GtRel.over_zero {u : D.X → Fˣ} {g₀ : GtPtF D F} {g : GtPtF D' F} (h : GtRel w e u g₀ g) (hb : g₀.b = 1) :
    g.b = 1 ∧ ∀ χ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' →
      vS (g.s (e χ)) y J' = unitStk y (u χ) * vS (g₀.s χ) y J := by
  obtain ⟨b₁, v₁⟩ := (gtRel_iff gp hT hc hw _ _ _).1 h
  have hb' : g.b = 1 := pushF_injective gp hT (by rw [pushF_one, b₁, hb])
  refine ⟨hb', fun χ y J J' hJ hJ' => ?_⟩
  have v := v₁ χ y J J' hJ hJ'
  rw [show cP D' (TF (R := R') F) (e χ) * g.b = cP D' _ (e χ) by rw [hb', _root_.mul_one],
    show wVal w y J J' g.b = wVal w y J J' 1 by rw [hb'], inv_mul_cancel, _root_.one_mul, mul_inv_cancel,
    _root_.one_mul] at v
  exact v

include gp hT hc hw in
/- English proof (translation)
Take `⟨z₁, z₂⟩` from `(isZero_iff _).1 H`. Take `⟨hb, hv⟩` from `h.over_zero gp hT hc hw z₁`. Use `(isZero_iff _).2 ⟨hb, fun χ y J' hJ' => ?_⟩` and prove the remaining obligations. Take `⟨J, hJ⟩` from `exists_good' D.P.isLB (Y := Sp F) y`. Take `⟨χ, rfl⟩` from `e.surjective χ`.

Establish `z₃ : vS (g₀.s χ) y J = 1` using `z₂ χ y J hJ`. Conclude with `(hv χ y J J' hJ hJ').trans (by rw [hu, map_one, z₃, _root_.mul_one])`.
-/
theorem GtRel.isZero {u : D.X → Fˣ} (hu : ∀ χ, u χ = 1) {g₀ : GtPtF D F} {g : GtPtF D' F} (h : GtRel w e u g₀ g)
    (H : g₀.IsZero) : g.IsZero := by
  obtain ⟨z₁, z₂⟩ := (isZero_iff _).1 H
  obtain ⟨hb, hv⟩ := h.over_zero gp hT hc hw z₁
  refine (isZero_iff _).2 ⟨hb, fun χ y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB (Y := Sp F) y
  obtain ⟨χ, rfl⟩ := e.surjective χ
  have z₃ : vS (g₀.s χ) y J = 1 := z₂ χ y J hJ
  exact (hv χ y J J' hJ hJ').trans (by rw [hu, map_one, z₃, _root_.mul_one])

include gp hT hc hw in

/- English proof (translation)
Take `⟨hb', hv⟩` from `h.over_zero gp hT hc hw hb`. Use `⟨hb', fun χ j hj hle => ?_⟩` and prove the remaining obligations. Take `⟨χ, rfl⟩` from `e.surjective χ`. Establish `y : Sp F` using `(default : PrimeSpectrum F)`. Establish `m : (𝟙 (Sp F) : Sp F ⟶ Sp F) y ∈ LB.wchart D'.P.L (DegPre.gtφ D' F g.b (e χ)) j` using `hle trivial`.

Take `⟨J, hJ⟩` from `exists_good' D.P.isLB (Y := Sp F) y`. Take `⟨J', hJ', e'⟩` from `exists_good D'.P.L D'.P.isLB (Z := Sp F) y _ j hj (Set.mem_iInter.1 m)`. Establish `m₀` using `hJ.mem (DegPre.gtφ D F g₀.b χ) (𝟙 _)`. Establish `t₀` using `ht χ (fun k => J (𝟙 _ ≫ DegPre.gtφ D F g₀.b χ k)) (fun a b h => congrArg (fun q => J (𝟙 _ ≫ q)) h) ((top_le_iff_mem (𝟙 (Sp F)) _ y).2 m₀)`. Rewrite using `[AddEquiv.symm_apply_apply, ← t₀]`.

Apply `(toStk y).injective` to reduce the goal to its premises. Rewrite using `[map_mul]`. Use `(toStk_valF (𝟙 (Sp F)) _ y m _).trans (Eq.trans ?_ (congrArg _ (toStk_valF (𝟙 (Sp F)) _ y m₀ _)).symm)` and prove the remaining obligations. Use `Eq.trans (congrArg Units.val ?_) (congrArg Units.val (hv χ y J J' hJ hJ'))` and prove the remaining obligations. Conclude with `(val_of (g.s (e χ)) (𝟙 _) y J' j (fun k => by rw [Category.id_comp]; exact e' k)).symm`.
-/
theorem GtRel.torus {u : D.X → Fˣ} {g₀ : GtPtF D F} {g : GtPtF D' F} (h : GtRel w e u g₀ g) {t : D.X → F}
    (hb : g₀.b = DegPre.zeroF D F)
    (ht : ∀ χ j, LB.Coh D.P.L (DegPre.gtφ D F g₀.b χ) j → ⊤ ≤ LB.wchart D.P.L (DegPre.gtφ D F g₀.b χ) j →
      valF (𝟙 (Sp F)) _ ((g₀.s χ).s j).val = t χ) :
    g.b = DegPre.zeroF D' F ∧ ∀ χ j, LB.Coh D'.P.L (DegPre.gtφ D' F g.b χ) j →
      ⊤ ≤ LB.wchart D'.P.L (DegPre.gtφ D' F g.b χ) j →
      valF (𝟙 (Sp F)) _ ((g.s χ).s j).val = u (e.symm χ) * t (e.symm χ) := by
  obtain ⟨hb', hv⟩ := h.over_zero gp hT hc hw hb
  refine ⟨hb', fun χ j hj hle => ?_⟩
  obtain ⟨χ, rfl⟩ := e.surjective χ
  have y : Sp F := (default : PrimeSpectrum F)
  have m : (𝟙 (Sp F) : Sp F ⟶ Sp F) y ∈ LB.wchart D'.P.L (DegPre.gtφ D' F g.b (e χ)) j := hle trivial
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB (Y := Sp F) y
  obtain ⟨J', hJ', e'⟩ := exists_good D'.P.L D'.P.isLB (Z := Sp F) y _ j hj (Set.mem_iInter.1 m)
  have m₀ := hJ.mem (DegPre.gtφ D F g₀.b χ) (𝟙 _)
  have t₀ := ht χ (fun k => J (𝟙 _ ≫ DegPre.gtφ D F g₀.b χ k)) (fun a b h => congrArg (fun q => J (𝟙 _ ≫ q)) h)
    ((top_le_iff_mem (𝟙 (Sp F)) _ y).2 m₀)
  rw [AddEquiv.symm_apply_apply, ← t₀]
  apply (toStk y).injective
  rw [map_mul]
  refine (toStk_valF (𝟙 (Sp F)) _ y m _).trans (Eq.trans ?_ (congrArg _ (toStk_valF (𝟙 (Sp F)) _ y m₀ _)).symm)
  refine Eq.trans (congrArg Units.val ?_) (congrArg Units.val (hv χ y J J' hJ hJ'))
  exact (val_of (g.s (e χ)) (𝟙 _) y J' j (fun k => by rw [Category.id_comp]; exact e' k)).symm

variable {he : eSec D'.P.A ≫ Φ = spMap f ≫ eSec D.P.A}
  (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
    (rigPullOf Φ (spMap f) he D.P.L D.rig))

include gp hT hr in
/- English proof (translation)
Establish `pm` using `(maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (spMap f) _ (rigPull_le Φ (spMap f) he D.P.L) (fun _ => rfl)).1 hr`. Establish `a₂ : (TF (R` using `R) F).hom ≫ eSec D.P.A = (1 : TF (R := R') F ⟶ D'.P.A).left ≫ Φ := congrArg (fun q => q.left) (pushF_one gp hT).symm`. Establish `e` using `pm _ (TF (R := R') F).hom y (fun _ => J ((1 : TF (R := R') F ⟶ D'.P.A).left ≫ Φ)) (fun _ => J' (1 : TF (R := R') F ⟶ D'.P.A).left) (fun _ => hJ _) (fun _ => hJ' _)`. Rewrite `e` using `[Fintype.prod_unique, zpow_one, hT]`. Establish `b₁ : (𝟙 _ ≫ jFK (R` using `R) F) ≫ (toUnit (TK R)).left = (TF (R := R) F).hom := by rw [Category.id_comp]; rfl`.

Establish `b₂ : (𝟙 _ ≫ jFK (R` using `R') F) ≫ (toUnit (TK R')).left = (TF (R := R') F).hom := by rw [Category.id_comp]; rfl`. Use `(val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))` and prove the remaining obligations. Rewrite using `[b₁, b₂]`. Conclude with `(val_of _ _ y J _ (fun _ => congrArg J a₂)).trans e`.
-/
theorem rig_val {y : Sp F} {J J'} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J') :
    vK D.rigK y J = wVal w y J J' 1 * vK D'.rigK y J' := by
  have pm := (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (spMap f) _
    (rigPull_le Φ (spMap f) he D.P.L) (fun _ => rfl)).1 hr
  have a₂ : (TF (R := R) F).hom ≫ eSec D.P.A = (1 : TF (R := R') F ⟶ D'.P.A).left ≫ Φ :=
    congrArg (fun q => q.left) (pushF_one gp hT).symm
  have e := pm _ (TF (R := R') F).hom y (fun _ => J ((1 : TF (R := R') F ⟶ D'.P.A).left ≫ Φ))
    (fun _ => J' (1 : TF (R := R') F ⟶ D'.P.A).left) (fun _ => hJ _) (fun _ => hJ' _)
  rw [Fintype.prod_unique, zpow_one, hT] at e
  have b₁ : (𝟙 _ ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left = (TF (R := R) F).hom := by rw [Category.id_comp]; rfl
  have b₂ : (𝟙 _ ≫ jFK (R := R') F) ≫ (toUnit (TK R')).left = (TF (R := R') F).hom := by rw [Category.id_comp]; rfl
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
  rw [b₁, b₂]
  exact (val_of _ _ y J _ (fun _ => congrArg J a₂)).trans e

/- English proof (translation)
The claim follows from `(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))`.
-/
theorem tau_val (D : DegPre R) (a b : D.X) {y : Sp F} {J} (hJ : Good D.P.L y J) : vK (D.tau a b) y J =
    vK (D.psi (a + b)) y J * (vK (D.psi a) y J)⁻¹ * (vK (D.psi b) y J)⁻¹ * (vK D.rigK y J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

include hw in
/- English proof (translation)
Establish `a₁ : jFK (R` using `R') F ≫ D'.xK (e χ) = (cP D' (TF (R := R') F) (e χ)).left := (Category.assoc _ _ _).symm`. Establish `H` using `((genRel_val hw D.P.isLB D'.P.isLB (pullGen_isGen _ _ _ _ (D'.psi_gen _) _) (pullGen_isGen _ _ _ _ (D.psi_gen _) _) v).1 hψ).2 y J J' hJ hJ'`. Rewrite `H` using `[Fintype.prod_unique, zpow_neg_one]`. Establish `b₁ : vS (LB.pullGen _ _ _ (D'.psi (e χ)) (jFK (R` using `R') F)) y J' = vK (D'.psi (e χ)) y J' := val_pull hJ' _ _ _`. Establish `b₂ : vS (LB.pullGen _ _ _ (D.psi χ) (jFK (R` using `R) F)) y J = vK (D.psi χ) y J := val_pull hJ _ _ _`.

Rewrite using `[← b₁, ← b₂, wVal, ← a₁]`. Conclude with `H`.
-/
theorem psi_val {v : Fˣ} {χ : D.X} (hψ : GenRel w (LB.pullGen _ _ _ (D'.psi (e χ)) (jFK (R := R') F))
    (LB.pullGen _ _ _ (D.psi χ) (jFK (R := R) F)) (v : F)) {y : Sp F} {J J'} (hJ : Good D.P.L y J)
    (hJ' : Good D'.P.L y J') :
    (wVal w y J J' (cP D' _ (e χ)))⁻¹ * vK (D'.psi (e χ)) y J' = unitStk y v * vK (D.psi χ) y J := by
  have a₁ : jFK (R := R') F ≫ D'.xK (e χ) = (cP D' (TF (R := R') F) (e χ)).left := (Category.assoc _ _ _).symm
  have H := ((genRel_val hw D.P.isLB D'.P.isLB (pullGen_isGen _ _ _ _ (D'.psi_gen _) _)
    (pullGen_isGen _ _ _ _ (D.psi_gen _) _) v).1 hψ).2 y J J' hJ hJ'
  rw [Fintype.prod_unique, zpow_neg_one] at H
  have b₁ : vS (LB.pullGen _ _ _ (D'.psi (e χ)) (jFK (R := R') F)) y J' = vK (D'.psi (e χ)) y J' := val_pull hJ' _ _ _
  have b₂ : vS (LB.pullGen _ _ _ (D.psi χ) (jFK (R := R) F)) y J = vK (D.psi χ) y J := val_pull hJ _ _ _
  rw [← b₁, ← b₂, wVal, ← a₁]
  exact H

include gp hT hc hw hr in

/- English proof (translation)
Take `⟨b₁, v₁⟩` from `(gtRel_iff gp hT hc hw _ _ _).1 h`. Take `⟨ιb, ιv⟩` from `(isIota_iff _ _).1 H`. Establish `hb : g.b = cP D' _ (e x)` using `pushF_injective gp hT (by rw [pushF_cP gp hT hc, b₁, ιb])`. Use `(isIota_iff _ _).2 ⟨hb, fun χ y J' hJ' => ?_⟩` and prove the remaining obligations. Take `⟨J, hJ⟩` from `exists_good' D.P.isLB (Y := Sp F) y`.

Take `⟨χ, rfl⟩` from `e.surjective χ`. Establish `ι₁ : vS (g₀.s χ) y J = vK (D.tau x χ) y J` using `ιv _ y J hJ`. Use `show vS (g.s (e χ)) y J' = vK (D'.tau (e x) (e χ)) y J'`. Establish `c₀` using `v₁ χ y J J' hJ hJ'`. Rewrite `c₀` using `[ι₁, tau_val D _ _ hJ, rig_val gp hT hr hJ hJ', show cP D' (TF (R := R') F) (e χ) * g.b = cP D' _ (e (x + χ)) by rw [hb, map_add, cPoint_add, mul_comm], show wVal w y J J' g.b = wVal w y J J' (cP D' _ (e x)) by rw [hb]]`.

Establish `c₃` using `psi_val hw (hψ (x + χ)) hJ hJ'`. Rewrite `c₃` using `[hu, map_mul, map_mul]`. Rewrite using `[tau_val D' _ _ hJ', ← map_add]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `a₀` using `congrArg Additive.ofMul c₀`.

Establish `a₁` using `congrArg Additive.ofMul (psi_val hw (hψ x) hJ hJ')`. Establish `a₂` using `congrArg Additive.ofMul (psi_val hw (hψ χ) hJ hJ')`. Establish `a₃` using `congrArg Additive.ofMul c₃`. Simplify using `only [ofMul_mul, ofMul_inv] at a₀ a₁ a₂ a₃ ⊢`. Take the linear combination `(norm := abel) a₀ + a₁ + a₂ - a₃`.
-/
theorem GtRel.isIota {u v : D.X → Fˣ} (hψ : ∀ χ, GenRel w (LB.pullGen _ _ _ (D'.psi (e χ)) (jFK (R := R') F))
    (LB.pullGen _ _ _ (D.psi χ) (jFK (R := R) F)) (v χ : F)) {x : D.X} (hu : ∀ χ, v (x + χ) = u χ * v x * v χ)
    {g₀ : GtPtF D F} {g : GtPtF D' F} (h : GtRel w e u g₀ g) (H : GtPtF.IsIota x g₀) : GtPtF.IsIota (e x) g := by
  obtain ⟨b₁, v₁⟩ := (gtRel_iff gp hT hc hw _ _ _).1 h
  obtain ⟨ιb, ιv⟩ := (isIota_iff _ _).1 H
  have hb : g.b = cP D' _ (e x) := pushF_injective gp hT (by rw [pushF_cP gp hT hc, b₁, ιb])
  refine (isIota_iff _ _).2 ⟨hb, fun χ y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB (Y := Sp F) y
  obtain ⟨χ, rfl⟩ := e.surjective χ
  have ι₁ : vS (g₀.s χ) y J = vK (D.tau x χ) y J := ιv _ y J hJ
  show vS (g.s (e χ)) y J' = vK (D'.tau (e x) (e χ)) y J'
  have c₀ := v₁ χ y J J' hJ hJ'
  rw [ι₁, tau_val D _ _ hJ, rig_val gp hT hr hJ hJ',
    show cP D' (TF (R := R') F) (e χ) * g.b = cP D' _ (e (x + χ)) by rw [hb, map_add, cPoint_add, mul_comm],
    show wVal w y J J' g.b = wVal w y J J' (cP D' _ (e x)) by rw [hb]] at c₀
  have c₃ := psi_val hw (hψ (x + χ)) hJ hJ'
  rw [hu, map_mul, map_mul] at c₃
  rw [tau_val D' _ _ hJ', ← map_add]
  apply Additive.ofMul.injective
  have a₀ := congrArg Additive.ofMul c₀
  have a₁ := congrArg Additive.ofMul (psi_val hw (hψ x) hJ hJ')
  have a₂ := congrArg Additive.ofMul (psi_val hw (hψ χ) hJ hJ')
  have a₃ := congrArg Additive.ofMul c₃
  simp only [ofMul_mul, ofMul_inv] at a₀ a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₀ + a₁ + a₂ - a₃

end Pull

section ThetaShiftProofs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {k : Type} [Field k] {bF : c.F →+* k} (a : ArcIn D l (RingHom.id c.F) k bF)
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left} (w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X)
  {F : Type} [Field F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F] (uF : F)

def IsTransport {n : ℕ} (q₀ : QkPt a.D₀ F n) (q : QkPt P.toPre F n) : Prop :=
  q.y = e q₀.y ∧ ∀ z, GenRel w (q.g.s (e z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / n))

/- English proof (translation)
The claim follows from `((Int.natCast_dvd_natCast.2 hn).mul_left 2).trans (a.be_dvd y z)`.
-/
theorem dvd_be {n : ℕ} (hn : n ∣ l.M') (y z : a.D₀.X) : (n : ℤ) ∣ a.be y z :=
  ((Int.natCast_dvd_natCast.2 hn).mul_left 2).trans (a.be_dvd y z)

/- English proof (translation)
Establish `h₁ : (2 : ℤ) ∣ a.be x x` using `(Dvd.intro _ rfl).trans (a.be_dvd x x)`. Establish `h₂ : (2 : ℤ) ∣ a.be χ χ` using `(Dvd.intro _ rfl).trans (a.be_dvd χ χ)`. Establish `h₃` using `a.be_symm χ x`. Simplify using `only [map_add, LinearMap.add_apply]`. Use linear arithmetic over natural numbers and integers.
-/
theorem be_half (x χ : a.D₀.X) : a.be (x + χ) (x + χ) / 2 = a.be x χ + a.be x x / 2 + a.be χ χ / 2 := by
  have h₁ : (2 : ℤ) ∣ a.be x x := (Dvd.intro _ rfl).trans (a.be_dvd x x)
  have h₂ : (2 : ℤ) ∣ a.be χ χ := (Dvd.intro _ rfl).trans (a.be_dvd χ χ)
  have h₃ := a.be_symm χ x
  simp only [map_add, LinearMap.add_apply]
  omega

variable {a w e uF}

/- English proof (translation)
Rewrite using `[hu]`. Conclude with `(_root_.map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 PowerSeries.X_ne_zero)`.
-/
theorem u_ne_zero (hu : uF = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X)) :
    uF ≠ 0 := by
  rw [hu]
  exact (_root_.map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 PowerSeries.X_ne_zero)

/- English proof (translation)
Simplify using `only [GtRel, Units.val_zpow_eq_zpow_val, Units.val_mk0]`. Conclude with `Iff.rfl`.
-/
theorem gtRel_zpow (h0 : uF ≠ 0) (m : a.D₀.X → ℤ) (g₀ : GtPtF a.D₀ F) (g : GtPtF P.toPre F) :
    GtRel w e.toAddEquiv (fun z => Units.mk0 uF h0 ^ m z) g₀ g ↔
      ∀ z, GenRel w (g.s (e z)) (g₀.s z) (uF ^ m z) := by
  simp only [GtRel, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  exact Iff.rfl

variable [IsAlgClosed F] {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A} (hW : WitData a P oP φ he w e)
  (hF : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
    algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x)))
  (hu : uF = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X))

include hW hF hu

/- English proof (translation)
Take `⟨gp, hw, hr, -, hc, hψ⟩` from `hW`. Use `GtRel.isIota gp (base_comm hF) (e := e.toAddEquiv) hc ((isGen_iff w).1 hw) hr (v := fun y => Units.mk0 uF (u_ne_zero hu) ^ (a.be y y / 2)) (fun χ => ?_) (fun χ => ?_) h hι` and prove the remaining obligations. Rewrite using `[Units.val_zpow_eq_zpow_val]`. Conclude with `hψ F uF hF hu χ`. Rewrite using `[be_half, zpow_add, zpow_add]`.
-/
theorem isIota_of_rel {x : a.D₀.X} {g₀ : GtPtF a.D₀ F} {g : GtPtF P.toPre F}
    (h : GtRel w e.toAddEquiv (fun z => Units.mk0 uF (u_ne_zero hu) ^ a.be x z) g₀ g) (hι : GtPtF.IsIota x g₀) :
    GtPtF.IsIota (e x) g := by
  obtain ⟨gp, hw, hr, -, hc, hψ⟩ := hW
  refine GtRel.isIota gp (base_comm hF) (e := e.toAddEquiv) hc ((isGen_iff w).1 hw) hr
    (v := fun y => Units.mk0 uF (u_ne_zero hu) ^ (a.be y y / 2)) (fun χ => ?_) (fun χ => ?_) h hι
  · rw [Units.val_zpow_eq_zpow_val]
    exact hψ F uF hF hu χ
  · rw [be_half, zpow_add, zpow_add]

/- English proof (translation)
Establish `hι'` using `fun x g₀ g => isIota_of_rel hW hF hu (x := x) (g₀ := g₀) (g := g)`. Take `⟨gp, hw, hr, -, hc, hψ⟩` from `hW`. Establish `hT` using `base_comm hF`. Establish `hw'` using `(isGen_iff w).1 hw`. Establish `ex : ∀ (i : ℕ) (g₀ : GtPtF a.D₀ F), ∃ g : GtPtF P.toPre F, GtRel w e.toAddEquiv (fun z => Units.mk0 uF (u_ne_zero hu) ^ ((i : ℤ) * (a.be q₀.y z / n))) g₀ g` using `fun i g₀ => exists_gtRel gp hT (e := e.toAddEquiv) hc hw' hG _ (fun x y => by`.

Rewrite using `[map_add, Int.add_ediv_of_dvd_left (dvd_be a hn _ _), mul_add, zpow_add]) g₀`. Use `choose dn hdn using ex`. Take `⟨h, ⟨gs, g₀, gst, gl⟩, hι⟩` from `q₀.eq`. Use `⟨⟨e q₀.y, dn 1 q₀.g, dn n h, ⟨fun i => dn i (gs i), ?_, fun i => ?_, congrArg (dn n) gl⟩, hι' _ h _ ?_ hι⟩, rfl, ?_⟩` and prove the remaining obligations. Conclude with `GtRel.isZero gp hT (e := e.toAddEquiv) hc hw' (fun χ => by simp) (hdn _ _) g₀`.

Use `GtRel.isAdd gp hT (e := e.toAddEquiv) hc hw' hG (fun χ => ?_) (hdn _ _) (hdn _ _) (hdn _ _) (gst i)` and prove the remaining obligations. Rewrite using `[← zpow_add, ← add_mul]`. Simplify using the standard rewrite rules. Use `hdn n h` as an intermediate fact. Simplify using `only [Int.mul_ediv_cancel' (dvd_be a hn _ _)] at this`.

Conclude with `this`. Use `hdn 1 q₀.g` as an intermediate fact. Simplify using `only [Nat.cast_one, _root_.one_mul] at this`. Conclude with `(gtRel_zpow (u_ne_zero hu) _ _ _).1 this`.
-/
theorem exists_transport (hG : GlobalFnsSt) {n : ℕ} (hn : n ∣ l.M') (q₀ : QkPt a.D₀ F n) :
    ∃ q : QkPt P.toPre F n, IsTransport a w e uF q₀ q := by
  have hι' := fun x g₀ g => isIota_of_rel hW hF hu (x := x) (g₀ := g₀) (g := g)
  obtain ⟨gp, hw, hr, -, hc, hψ⟩ := hW
  have hT := base_comm hF
  have hw' := (isGen_iff w).1 hw
  have ex : ∀ (i : ℕ) (g₀ : GtPtF a.D₀ F), ∃ g : GtPtF P.toPre F,
      GtRel w e.toAddEquiv (fun z => Units.mk0 uF (u_ne_zero hu) ^ ((i : ℤ) * (a.be q₀.y z / n))) g₀ g :=
    fun i g₀ => exists_gtRel gp hT (e := e.toAddEquiv) hc hw' hG _ (fun x y => by
      rw [map_add, Int.add_ediv_of_dvd_left (dvd_be a hn _ _), mul_add, zpow_add]) g₀
  choose dn hdn using ex
  obtain ⟨h, ⟨gs, g₀, gst, gl⟩, hι⟩ := q₀.eq
  refine ⟨⟨e q₀.y, dn 1 q₀.g, dn n h, ⟨fun i => dn i (gs i), ?_, fun i => ?_, congrArg (dn n) gl⟩, hι' _ h _ ?_ hι⟩,
    rfl, ?_⟩
  · exact GtRel.isZero gp hT (e := e.toAddEquiv) hc hw' (fun χ => by simp) (hdn _ _) g₀
  · refine GtRel.isAdd gp hT (e := e.toAddEquiv) hc hw' hG (fun χ => ?_) (hdn _ _) (hdn _ _) (hdn _ _) (gst i)
    rw [← zpow_add, ← add_mul]
    simp
  · have := hdn n h
    simp only [Int.mul_ediv_cancel' (dvd_be a hn _ _)] at this
    exact this
  · have := hdn 1 q₀.g
    simp only [Nat.cast_one, _root_.one_mul] at this
    exact (gtRel_zpow (u_ne_zero hu) _ _ _).1 this

omit [IsAlgClosed F] hW hF hu in

/- English proof (translation)
The claim follows from `(h.2 0).1 2`.
-/
theorem IsTransport.b_comp {n : ℕ} {q₀ : QkPt a.D₀ F n} {q : QkPt P.toPre F n} (h : IsTransport a w e uF q₀ q) :
    q.g.b.left ≫ φ = q₀.g.b.left := (h.2 0).1 2

/- English proof (translation)
Take `⟨gp, hw, -, -, hc, -⟩` from `hW`. Establish `hg : q.g = q'.g` using `GtRel.unique gp (base_comm hF) (e := e.toAddEquiv) hc ((isGen_iff w).1 hw) ((gtRel_zpow (u_ne_zero hu) _ _ _).2 h.2) ((gtRel_zpow (u_ne_zero hu) _ _ _).2 h'.2)`. Establish `hy : q.y = q'.y` using `h.1.trans h'.1.symm`. Take `⟨y, g, _⟩` from `q`. Take `⟨y', g', _⟩` from `q'`.

Take `rfl : y = y'` from `hy`. Take `rfl : g = g'` from `hg`. Both sides reduce to the same expression.
-/
theorem IsTransport.unique {n : ℕ} {q₀ : QkPt a.D₀ F n} {q q' : QkPt P.toPre F n} (h : IsTransport a w e uF q₀ q)
    (h' : IsTransport a w e uF q₀ q') : q = q' := by
  obtain ⟨gp, hw, -, -, hc, -⟩ := hW
  have hg : q.g = q'.g := GtRel.unique gp (base_comm hF) (e := e.toAddEquiv) hc ((isGen_iff w).1 hw)
    ((gtRel_zpow (u_ne_zero hu) _ _ _).2 h.2) ((gtRel_zpow (u_ne_zero hu) _ _ _).2 h'.2)
  have hy : q.y = q'.y := h.1.trans h'.1.symm
  obtain ⟨y, g, _⟩ := q
  obtain ⟨y', g', _⟩ := q'
  obtain rfl : y = y' := hy
  obtain rfl : g = g' := hg
  rfl

/- English proof (translation)
Establish `hι'` using `fun x g₀ g => isIota_of_rel hW hF hu (x := x) (g₀ := g₀) (g := g)`. Take `⟨gp, hw, hr, -, hc, hψ⟩` from `hW`. Establish `hT` using `base_comm hF`. Establish `hw'` using `(isGen_iff w).1 hw`. Take `⟨z, hy, g₀, hι, hadd⟩` from `H`.

Take `⟨g, hg⟩` from `exists_gtRel gp hT (e := e.toAddEquiv) hc hw' hG (fun χ => Units.mk0 uF (u_ne_zero hu) ^ a.be z χ) (fun x y => by rw [map_add, zpow_add]) g₀`. Use `⟨e z, by rw [h'.1, h.1, hy, map_add, map_nsmul], g, hι' z g₀ g hg hι, ?_⟩` and prove the remaining obligations. Use `GtRel.isAdd gp hT (e := e.toAddEquiv) hc hw' hG (fun χ => ?_) ((gtRel_zpow (u_ne_zero hu) _ _ _).2 h.2) hg ((gtRel_zpow (u_ne_zero hu) _ _ _).2 h'.2) hadd` and prove the remaining obligations. Rewrite using `[← zpow_add, hy, map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, Int.add_mul_ediv_left _ _ (Int.natCast_ne_zero.2 hn₀.ne')]`.
-/
theorem IsTransport.equiv (hG : GlobalFnsSt) {n : ℕ} (hn₀ : 0 < n) (hn : n ∣ l.M') {q₀ q₀' : QkPt a.D₀ F n}
    {q q' : QkPt P.toPre F n} (h : IsTransport a w e uF q₀ q) (h' : IsTransport a w e uF q₀' q')
    (H : QkPt.Equiv a.D₀ F q₀ q₀') : QkPt.Equiv P.toPre F q q' := by
  have hι' := fun x g₀ g => isIota_of_rel hW hF hu (x := x) (g₀ := g₀) (g := g)
  obtain ⟨gp, hw, hr, -, hc, hψ⟩ := hW
  have hT := base_comm hF
  have hw' := (isGen_iff w).1 hw
  obtain ⟨z, hy, g₀, hι, hadd⟩ := H
  obtain ⟨g, hg⟩ := exists_gtRel gp hT (e := e.toAddEquiv) hc hw' hG
    (fun χ => Units.mk0 uF (u_ne_zero hu) ^ a.be z χ) (fun x y => by rw [map_add, zpow_add]) g₀
  refine ⟨e z, by rw [h'.1, h.1, hy, map_add, map_nsmul], g, hι' z g₀ g hg hι, ?_⟩
  refine GtRel.isAdd gp hT (e := e.toAddEquiv) hc hw' hG (fun χ => ?_) ((gtRel_zpow (u_ne_zero hu) _ _ _).2 h.2) hg
    ((gtRel_zpow (u_ne_zero hu) _ _ _).2 h'.2) hadd
  rw [← zpow_add, hy, map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul,
    Int.add_mul_ediv_left _ _ (Int.natCast_ne_zero.2 hn₀.ne')]

/- English proof (translation)
Take `⟨gp, hw, -, -, hc, -⟩` from `hW`. Take `⟨h₁, h₂⟩` from `GtRel.torus gp (base_comm hF) (e := e.toAddEquiv) hc ((isGen_iff w).1 hw) ((gtRel_zpow (u_ne_zero hu) _ _ _).2 h.2) hb ht`. Use `⟨by rw [h.1, hy, map_zero], h₁, fun χ j hj hle => (h₂ χ j hj hle).trans ?_⟩` and prove the remaining obligations. Rewrite using `[hy, map_zero, LinearMap.zero_apply, Int.zero_ediv, zpow_zero, Units.val_one, _root_.one_mul]`. Both sides reduce to the same expression.
-/
theorem IsTransport.torus {n : ℕ} {q₀ : QkPt a.D₀ F n} {q : QkPt P.toPre F n} (h : IsTransport a w e uF q₀ q)
    (hy : q₀.y = 0) {t : a.D₀.X → F} (hb : q₀.g.b = DegPre.zeroF a.D₀ F)
    (ht : ∀ χ j, LB.Coh a.D₀.P.L (DegPre.gtφ a.D₀ F q₀.g.b χ) j →
      ⊤ ≤ LB.wchart a.D₀.P.L (DegPre.gtφ a.D₀ F q₀.g.b χ) j → valF (𝟙 (Sp F)) _ ((q₀.g.s χ).s j).val = t χ) :
    q.y = 0 ∧ q.g.b = DegPre.zeroF P.toPre F ∧ ∀ χ j, LB.Coh P.toPre.P.L (DegPre.gtφ P.toPre F q.g.b χ) j →
      ⊤ ≤ LB.wchart P.toPre.P.L (DegPre.gtφ P.toPre F q.g.b χ) j →
      valF (𝟙 (Sp F)) _ ((q.g.s χ).s j).val = t (e.symm χ) := by
  obtain ⟨gp, hw, -, -, hc, -⟩ := hW
  obtain ⟨h₁, h₂⟩ := GtRel.torus gp (base_comm hF) (e := e.toAddEquiv) hc ((isGen_iff w).1 hw)
    ((gtRel_zpow (u_ne_zero hu) _ _ _).2 h.2) hb ht
  refine ⟨by rw [h.1, hy, map_zero], h₁, fun χ j hj hle => (h₂ χ j hj hle).trans ?_⟩
  rw [hy, map_zero, LinearMap.zero_apply, Int.zero_ediv, zpow_zero, Units.val_one, _root_.one_mul]
  rfl

end ThetaShiftProofs

/- English proof (translation)
Assemble the required witnesses or components as `⟨exists_transport hW hF hu hG hn, fun _ _ h => h.b_comp, fun _ _ _ h h' => h.unique hW hF hu h', fun _ _ _ _ h h' H => h.equiv hW hF hu hG hn₀ hn h' H, fun _ _ _ h hy ht => h.torus hW hF hu hy ht.1 ht.2⟩`.
-/
theorem transport (hG : GlobalFnsSt) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) (hW : WitData a P oP φ he w e)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F] (uF : F)
    (hF : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x)))
    (hu : uF = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X))
    (n : ℕ) (hn₀ : 0 < n) (hn : n ∣ l.M') :
    (∀ q₀ : QkPt a.D₀ F n, ∃ q : QkPt P.toPre F n, IsTransport a w e uF q₀ q) ∧
    (∀ (q₀ : QkPt a.D₀ F n) (q : QkPt P.toPre F n), IsTransport a w e uF q₀ q → q.g.b.left ≫ φ = q₀.g.b.left) ∧
    (∀ (q₀ : QkPt a.D₀ F n) (q q' : QkPt P.toPre F n), IsTransport a w e uF q₀ q → IsTransport a w e uF q₀ q' →
      q = q') ∧
    (∀ (q₀ q₀' : QkPt a.D₀ F n) (q q' : QkPt P.toPre F n), IsTransport a w e uF q₀ q → IsTransport a w e uF q₀' q' →
      QkPt.Equiv a.D₀ F q₀ q₀' → QkPt.Equiv P.toPre F q q') ∧
    ∀ (q₀ : QkPt a.D₀ F n) (q : QkPt P.toPre F n) (t : a.D₀.X → F), IsTransport a w e uF q₀ q → q₀.y = 0 →
      (q₀.g.b = DegPre.zeroF a.D₀ F ∧ ∀ χ j, LB.Coh a.D₀.P.L (DegPre.gtφ a.D₀ F q₀.g.b χ) j →
        ⊤ ≤ LB.wchart a.D₀.P.L (DegPre.gtφ a.D₀ F q₀.g.b χ) j → valF (𝟙 (Sp F)) _ ((q₀.g.s χ).s j).val = t χ) →
      q.y = 0 ∧ q.g.b = DegPre.zeroF P.toPre F ∧ ∀ χ j, LB.Coh P.toPre.P.L (DegPre.gtφ P.toPre F q.g.b χ) j →
        ⊤ ≤ LB.wchart P.toPre.P.L (DegPre.gtφ P.toPre F q.g.b χ) j →
        valF (𝟙 (Sp F)) _ ((q.g.s χ).s j).val = t (e.symm χ) :=
  ⟨exists_transport hW hF hu hG hn, fun _ _ h => h.b_comp, fun _ _ _ h h' => h.unique hW hF hu h',
    fun _ _ _ _ h h' H => h.equiv hW hF hu hG hn₀ hn h' H, fun _ _ _ h hy ht => h.torus hW hF hu hy ht.1 ht.2⟩

section Witness

open GlobalTheory.ToricData GlobalTheory.HostModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
  (k : Type) [Field k] (bF : c.F →+* k)

def toricArc : DegData (PowerSeries k) (Ideal.span {PowerSeries.X}) :=
  arcData (X := 𝓞 E) k (arcIn c k bF).be (arcIn c k bF).be_symm (arcIn c k bF).be_pos (arcIn_be_even c k bF)

instance : Module (𝓞 E) (toricArc c k bF).toPre.X := inferInstanceAs (Module (𝓞 E) (𝓞 E))

def toricArcAct : letI := H.starRing; (toricArc c k bF).toPre.OAct (𝓞 E) :=
  letI := H.starRing
  arcOAct (X := 𝓞 E) k _ _ _ _ (𝓞 E) (arcIn c k bF).be_adj

def toricMap : (toricArc c k bF).toPre.P.A.left ⟶ (arcIn c k bF).D₀.P.A.left :=
  baseMap (X := 𝓞 E) (fun _ => 1) (PowerSeries.C (R := k)) (arcExp k (arcIn c k bF).be)

def toricIso : LB.Iso (toricArc c k bF).toPre.P.L ((arcIn c k bF).D₀.P.L.pull (toricMap c k bF)) :=
  baseIso (X := 𝓞 E) (fun _ => 1) (PowerSeries.C (R := k)) (arcExp k (arcIn c k bF).be)

def toricNeg : (arcIn c k bF).D₀.X ≃ₗ[𝓞 E] (toricArc c k bF).toPre.X := LinearEquiv.neg (𝓞 E) (M := 𝓞 E)

/- English proof (translation)
Set `F` to `AlgebraicClosure (FractionRing (PowerSeries k))`. Set `g : k →+* F` to `((algebraMap (FractionRing (PowerSeries k)) F).comp (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))).comp PowerSeries.C`. Conclude with `⟨F, inferInstance, inferInstance, inferInstance, (IsFractionRing.lift (K := FractionRing k) g.injective).toAlgebra, fun x => IsFractionRing.lift_algebraMap (K := FractionRing k) g.injective x⟩`.
-/
theorem exists_commonField : ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F)
    (_ : Algebra (FractionRing (PowerSeries k)) F) (_ : Algebra (FractionRing k) F),
    ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x)) := by
  let F := AlgebraicClosure (FractionRing (PowerSeries k))
  let g : k →+* F := ((algebraMap (FractionRing (PowerSeries k)) F).comp
    (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))).comp PowerSeries.C
  exact ⟨F, inferInstance, inferInstance, inferInstance,
    (IsFractionRing.lift (K := FractionRing k) g.injective).toAlgebra,
    fun x => IsFractionRing.lift_algebraMap (K := FractionRing k) g.injective x⟩

end Witness

end GlobalTheory.ArcTransport
