import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCompMonHom

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.HomTorChar

/- English proof (translation)
Use `(GlobalTheory.SplitTorus.eq_torusMap_iff t h).2 fun b => ?_` and prove the remaining obligations. Establish `e` using `congrArg Units.val (ht b)`. Establish `: (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial) (pullU t.left ⊤ (charUnit S X' b)) : Γ((splitTorus S X).left, ⊤)ˣ).val = t.left.appTop.hom (charUnit S X' b).val`. Rewrite using `[Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Both sides reduce to the same expression.

Rewrite `e` using `[this, GlobalTheory.SplitTorus.charUnit_val, GlobalTheory.SplitTorus.charUnit_val]`. Conclude with `e`.
-/
theorem eq_torusMap_of_torusHomOf {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' →+ X)
    (t : splitTorus S X ⟶ splitTorus S X') (ht : GlobalTheory.Mum.Two.TorusHomOf h t) : t = GlobalTheory.SplitTorus.torusMap S h := by
  refine (GlobalTheory.SplitTorus.eq_torusMap_iff t h).2 fun b => ?_
  have e := congrArg Units.val (ht b)
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' b)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' b).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [this, GlobalTheory.SplitTorus.charUnit_val, GlobalTheory.SplitTorus.charUnit_val] at e
  exact e

/- English proof (translation)
Introduce `R _ _ _ hR D' D A' A G' G _ _ _ _ hG' hG U' U p hpm ρ hon`. Establish `hr : ∀ x ∈ maximalIdeal R ^ (0 + 1), residue R x = 0` using `fun x hx => (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx)`. Establish `hp` using `isGrpPullback_pullback G (spMap (residue R))`. Establish `hp'` using `isGrpPullback_pullback G' (spMap (residue R))`. Establish `e : ((Over.pullback (spMap (residue R))).map p).left ≫ pullback.fst G.hom (spMap (residue R)) = pullback.fst G'.hom (spMap (residue R)) ≫ p.left` using `pullback.lift_fst _ _ _`.

Establish `hρ : GlobalTheory.TorusPart.gtTorus (U'.gt 0) hr hp' ≫ (Over.pullback (spMap (residue R))).map p = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hr hp`. Take `⟨t, ht, hi⟩` from `hon 0`. Establish `htm` using `eq_torusMap_of_torusHomOf ρ t ht`. Establish `k` using `GlobalTheory.TorusPart.isGrpPullback_thickLift hr hp`. Establish `k'` using `GlobalTheory.TorusPart.isGrpPullback_thickLift hr hp'`.

Establish `e' : ((Over.pullback (spMap (residue R))).map p).left ≫ GlobalTheory.TorusPart.thickLift hr hp = GlobalTheory.TorusPart.thickLift hr hp' ≫ ((Over.pullback (thick R (maximalIdeal R) 0)).map p).left`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, GlobalTheory.TorusPart.thickLift_fst, e, Category.assoc]`. Simplify using `only [GlobalTheory.TorusPart.thickLift, Over.pullback_map_left]`. Rewrite using `[pullback.lift_fst, pullback.lift_fst_assoc]`.

Establish `w` using `Over.w ((Over.pullback (spMap (residue R))).map p)`. Simplify using `only [GlobalTheory.TorusPart.thickLift]`. Rewrite using `[Category.assoc, pullback.lift_snd, Category.assoc, ← Category.assoc _ _ (GlobalTheory.TorusPart.thickPt 0 hr), w]`. Simplify using `only [Over.pullback_map_left]`. Rewrite using `[pullback.lift_snd, pullback.lift_snd]`.

Establish `hc` using `GlobalTheory.TorusPart.pullTorus_comp k' k _ _ e' (U'.gt 0).i`. Unfold `GlobalTheory.TorusPart.gtTorus`. Rewrite using `[← hc, hi, htm, GlobalTheory.TorusPart.pullTorus_torusMap_comp]`. Introduce `F _ _ i₁ i₂ hF k hk τ τ' q q' a a' hτ'k hττ' hqy hq hq'y hq' ha ha'`. Establish `hi : i₁ = i₂` using `Algebra.algebra_ext _ _ fun x => RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors R) (j := @algebraMap _ _ _ _ i₁) (k := @algebraMap _ _ _ _ i₂) (RingHom.ext hF)) x`.

Substitute `hi` using the available equality. Establish `hk1 : 1 ≤ k`. Break down `Nat.eq_zero_or_pos k with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using `at hk`.

Conclude with `h`. Take `⟨s, s1, s2, s3, s4⟩` from `GlobalTheory.ToricTorsionUnif.main R hR G hG D A U k hk1`. Take `⟨s', s1', s2', s3', s4'⟩` from `GlobalTheory.ToricTorsionUnif.main R hR G' hG' D' A' U' k hk1`. Set `ρm` to `AddMonoidHom.toMultiplicative ρ`. Establish `powc : ∀ {H : Type} [CommGroup H] (f : Multiplicative D'.toPre.X →* H), f ^ k = 1 → (f.comp ρm) ^ k = 1` using `fun f hf => MonoidHom.ext fun x => by`.

Rewrite using `[MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hf]`. Both sides reduce to the same expression. Establish `hτ : τ = τ'.comp ρm` using `MonoidHom.ext fun x => hττ' (Multiplicative.toAdd x)`. Establish `hτk : τ ^ k = 1`. Rewrite using `[hτ]`.

Conclude with `powc τ' hτ'k`. Set `c : R →+* F` to `(algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))`. Rewrite using `[s4 F c τ hτk q a rfl hqy hq ha, ← Category.assoc, s4' F c τ' hτ'k q' a' rfl hq'y hq' ha']`. Take `⟨O, hO, hloc⟩` from `IsLocalRing.exists_factor_valuationRing c`. Set `φ : R →+* O` to `c.codRestrict O.toSubring hO`.

Use `haveI : IsLocalHom φ := hloc`. Establish `hc : c = O.subtype.comp φ` using `rfl`. Take `⟨τO, hτO⟩` from `GlobalTheory.ToricTorsionCompare.units_of_pow_eq_one F O _ k hk1 τ' hτ'k`. Establish `hτOk : τO ^ k = 1`. Use `MonoidHom.ext fun x => Units.ext (Subtype.ext ?_)` and prove the remaining obligations.

Use `congrArg (fun f => ((f x : Fˣ) : F)) hτ'k` as an intermediate fact. Simplify using `only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one] at this ⊢`. Rewrite using `[SubmonoidClass.coe_pow, hτO, this]`. Both sides reduce to the same expression. Set `τR` to `τO.comp ρm`.

Establish `hτR : τR ^ k = 1` using `powc τO hτOk`. Establish `hkO : IsUnit (k : O)` using `by simpa using hk.map φ`. Establish `hxy : s O φ τR hτR = s' O φ τO hτOk ≫ p`. Use `GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) G hG.smooth O (spMap φ) k hkO _ _ ?_ (ResidueField O) (residue O) inferInstance ?_` and prove the remaining obligations. Rewrite using `[s1, ← GlobalTheory.Poinc.HomTor.pow_comp_monHom, s1', MonObj.one_comp]`.

Set `τ₀ : Multiplicative D'.toPre.X →* (ResidueField O)ˣ` to `(Units.map (residue O).toMonoidHom).comp τO`. Establish `h₀ : τ₀ ^ k = 1`. Rewrite using `[show τ₀ ^ k = (Units.map (residue O).toMonoidHom).comp (τO ^ k) by ext x; simp [τ₀]]`. Rewrite using `[hτOk]`. Use `ext`.

Simplify using the standard rewrite rules. Set `τ₁` to `τ₀.comp ρm`. Establish `h₁ : τ₁ ^ k = 1` using `powc τ₀ h₀`. Set `z : Over.mk (spMap (ResidueField.map φ)) ⟶ splitTorus (Sp (ResidueField R)) D'.toPre.X` to `(GlobalTheory.splitTorusPointsEquiv _ _ _).symm ((Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField O))).inv.hom.toMonoidHom).comp τ₀)`. Establish `hz : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ₀ (Multiplicative.ofAdd χ))` using `fun χ => by`.

Simplify using `only [GlobalTheory.UU.chV, z, MulEquiv.apply_symm_apply]`. Both sides reduce to the same expression. Establish `hz₁ : ∀ χ, GlobalTheory.UU.chV (z ≫ GlobalTheory.SplitTorus.torusMap _ ρ) χ = unitOn (τ₁ (Multiplicative.ofAdd χ))` using `fun χ => by`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_comp_torusMap, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.UU.chV_val, hz]`.

Both sides reduce to the same expression. Establish `hres : (residue O).comp φ = (ResidueField.map φ).comp (residue R)`. Use extensionality with `r`. Simplify using `[ResidueField.map_residue]`. Rewrite using `[Over.comp_left, ← Category.assoc, ← s2 O _ φ ((residue O).comp φ) (residue O) τR hτR τ₁ h₁ rfl (fun χ => rfl), ← s2' O _ φ ((residue O).comp φ) (residue O) τO hτOk τ₀ h₀ rfl (fun χ => rfl), s3 _ _ (residue R) hr _ (ResidueField.map φ) _ _ hp τ₁ h₁ _ hres hz₁, s3' _ _ (residue R) …`.

Simplify using `only [Over.comp_left, Category.assoc]`. Rewrite using `[s2 O F φ c O.subtype τR hτR τ hτk hc (fun χ => by simp [τR, hτ, hτO]), s2' O F φ c O.subtype τO hτOk τ' hτ'k hc (fun χ => by simp [hτO]), hxy, Over.comp_left, Category.assoc]`.
-/
theorem torMatch_of_onTorus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (p : G ⟶ G₀), IsMonHom p → ∀ h : D₀.toPre.X →+ D.toPre.X, GlobalTheory.Mum.Two.OnTorus U.toUnifPre U₀.toUnifPre p h → GlobalTheory.Poinc.Eq8.TorMatch U₀ U (RingHom.id R) p.left h := by
  intro R _ _ _ hR D' D A' A G' G _ _ _ _ hG' hG U' U p hpm ρ hon
  have hr : ∀ x ∈ maximalIdeal R ^ (0 + 1), residue R x = 0 := fun x hx =>
    (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx)
  have hp := isGrpPullback_pullback G (spMap (residue R))
  have hp' := isGrpPullback_pullback G' (spMap (residue R))
  have e : ((Over.pullback (spMap (residue R))).map p).left ≫ pullback.fst G.hom (spMap (residue R)) =
      pullback.fst G'.hom (spMap (residue R)) ≫ p.left := pullback.lift_fst _ _ _
  have hρ : GlobalTheory.TorusPart.gtTorus (U'.gt 0) hr hp' ≫ (Over.pullback (spMap (residue R))).map p =
      GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hr hp := by
    obtain ⟨t, ht, hi⟩ := hon 0
    have htm := eq_torusMap_of_torusHomOf ρ t ht
    have k := GlobalTheory.TorusPart.isGrpPullback_thickLift hr hp
    have k' := GlobalTheory.TorusPart.isGrpPullback_thickLift hr hp'
    have e' : ((Over.pullback (spMap (residue R))).map p).left ≫ GlobalTheory.TorusPart.thickLift hr hp =
        GlobalTheory.TorusPart.thickLift hr hp' ≫ ((Over.pullback (thick R (maximalIdeal R) 0)).map p).left := by
      apply pullback.hom_ext
      · rw [Category.assoc, GlobalTheory.TorusPart.thickLift_fst, e, Category.assoc]
        simp only [GlobalTheory.TorusPart.thickLift, Over.pullback_map_left]
        rw [pullback.lift_fst, pullback.lift_fst_assoc]
      · have w := Over.w ((Over.pullback (spMap (residue R))).map p)
        simp only [GlobalTheory.TorusPart.thickLift]
        rw [Category.assoc, pullback.lift_snd, Category.assoc, ← Category.assoc _ _ (GlobalTheory.TorusPart.thickPt 0 hr), w]
        simp only [Over.pullback_map_left]
        rw [pullback.lift_snd, pullback.lift_snd]
    have hc := GlobalTheory.TorusPart.pullTorus_comp k' k _ _ e' (U'.gt 0).i
    unfold GlobalTheory.TorusPart.gtTorus
    rw [← hc, hi, htm, GlobalTheory.TorusPart.pullTorus_torusMap_comp]
  intro F _ _ i₁ i₂ hF k hk τ τ' q q' a a' hτ'k hττ' hqy hq hq'y hq' ha ha'
  have hi : i₁ = i₂ := Algebra.algebra_ext _ _ fun x =>
    RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors R)
      (j := @algebraMap _ _ _ _ i₁) (k := @algebraMap _ _ _ _ i₂) (RingHom.ext hF)) x
  subst hi
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk
    · exact h
  obtain ⟨s, s1, s2, s3, s4⟩ := GlobalTheory.ToricTorsionUnif.main R hR G hG D A U k hk1
  obtain ⟨s', s1', s2', s3', s4'⟩ := GlobalTheory.ToricTorsionUnif.main R hR G' hG' D' A' U' k hk1
  let ρm := AddMonoidHom.toMultiplicative ρ
  have powc : ∀ {H : Type} [CommGroup H] (f : Multiplicative D'.toPre.X →* H), f ^ k = 1 → (f.comp ρm) ^ k = 1 :=
    fun f hf => MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hf]; rfl
  have hτ : τ = τ'.comp ρm := MonoidHom.ext fun x => hττ' (Multiplicative.toAdd x)
  have hτk : τ ^ k = 1 := by
    rw [hτ]; exact powc τ' hτ'k
  let c : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))
  rw [s4 F c τ hτk q a rfl hqy hq ha, ← Category.assoc, s4' F c τ' hτ'k q' a' rfl hq'y hq' ha']
  obtain ⟨O, hO, hloc⟩ := IsLocalRing.exists_factor_valuationRing c
  let φ : R →+* O := c.codRestrict O.toSubring hO
  haveI : IsLocalHom φ := hloc
  have hc : c = O.subtype.comp φ := rfl
  obtain ⟨τO, hτO⟩ := GlobalTheory.ToricTorsionCompare.units_of_pow_eq_one F O _ k hk1 τ' hτ'k
  have hτOk : τO ^ k = 1 := by
    refine MonoidHom.ext fun x => Units.ext (Subtype.ext ?_)
    have := congrArg (fun f => ((f x : Fˣ) : F)) hτ'k
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one] at this ⊢
    rw [SubmonoidClass.coe_pow, hτO, this]; rfl
  let τR := τO.comp ρm
  have hτR : τR ^ k = 1 := powc τO hτOk
  have hkO : IsUnit (k : O) := by simpa using hk.map φ
  have hxy : s O φ τR hτR = s' O φ τO hτOk ≫ p := by
    refine GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) G hG.smooth O (spMap φ) k hkO _ _ ?_
      (ResidueField O) (residue O) inferInstance ?_
    · rw [s1, ← GlobalTheory.Poinc.HomTor.pow_comp_monHom, s1', MonObj.one_comp]
    · let τ₀ : Multiplicative D'.toPre.X →* (ResidueField O)ˣ := (Units.map (residue O).toMonoidHom).comp τO
      have h₀ : τ₀ ^ k = 1 := by
        rw [show τ₀ ^ k = (Units.map (residue O).toMonoidHom).comp (τO ^ k) by ext x; simp [τ₀]]
        rw [hτOk]; ext; simp
      let τ₁ := τ₀.comp ρm
      have h₁ : τ₁ ^ k = 1 := powc τ₀ h₀
      let z : Over.mk (spMap (ResidueField.map φ)) ⟶ splitTorus (Sp (ResidueField R)) D'.toPre.X :=
        (GlobalTheory.splitTorusPointsEquiv _ _ _).symm
          ((Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField O))).inv.hom.toMonoidHom).comp τ₀)
      have hz : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ₀ (Multiplicative.ofAdd χ)) := fun χ => by
        simp only [GlobalTheory.UU.chV, z, MulEquiv.apply_symm_apply]; rfl
      have hz₁ : ∀ χ, GlobalTheory.UU.chV (z ≫ GlobalTheory.SplitTorus.torusMap _ ρ) χ = unitOn (τ₁ (Multiplicative.ofAdd χ)) :=
        fun χ => by
          apply Units.ext
          rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.SplitTorus.val_eq,
            GlobalTheory.SplitTorus.val_comp_torusMap, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val,
            ← GlobalTheory.UU.chV_val, hz]
          rfl
      have hres : (residue O).comp φ = (ResidueField.map φ).comp (residue R) := by
        ext r; simp [ResidueField.map_residue]
      rw [Over.comp_left, ← Category.assoc,
        ← s2 O _ φ ((residue O).comp φ) (residue O) τR hτR τ₁ h₁ rfl (fun χ => rfl),
        ← s2' O _ φ ((residue O).comp φ) (residue O) τO hτOk τ₀ h₀ rfl (fun χ => rfl),
        s3 _ _ (residue R) hr _ (ResidueField.map φ) _ _ hp τ₁ h₁ _ hres hz₁,
        s3' _ _ (residue R) hr _ (ResidueField.map φ) _ _ hp' τ₀ h₀ z hres hz,
        Category.assoc z, ← hρ, Category.assoc _ _ p.left, ← e]
      simp only [Over.comp_left, Category.assoc]
  rw [s2 O F φ c O.subtype τR hτR τ hτk hc (fun χ => by simp [τR, hτ, hτO]),
    s2' O F φ c O.subtype τO hτOk τ' hτ'k hc (fun χ => by simp [hτO]), hxy, Over.comp_left, Category.assoc]

end GlobalTheory.Poinc.HomTorChar

end
