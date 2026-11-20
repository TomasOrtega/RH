import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCommGroupSchemeEqOfPowEqOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricTorsionUniformisationEqRestrictCharacters
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.HomTor

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, pow_zero, MonObj.one_comp]`. Consider the case `succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]`.
-/
theorem pow_comp_monHom {S : Scheme.{0}} {G G' Z : Over S} [MonObj G] [MonObj G'] (φ : G ⟶ G')
    [IsMonHom φ] (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

/- English proof (translation)
Introduce `R _ _ _ hR G _ _ hG D A U G' _ _ hG' D' A' U' p hpm`. Establish `hr : ∀ x ∈ maximalIdeal R ^ (0 + 1), residue R x = 0` using `fun x hx => (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx)`. Establish `hp` using `isGrpPullback_pullback G (spMap (residue R))`. Establish `hp'` using `isGrpPullback_pullback G' (spMap (residue R))`. Establish `e : ((Over.pullback (spMap (residue R))).map p).left ≫ pullback.fst G.hom (spMap (residue R)) = pullback.fst G'.hom (spMap (residue R)) ≫ p.left` using `pullback.lift_fst _ _ _`.

Establish `hf₁ : IsMonHom ((Over.pullback (spMap (residue R))).map p)` using `Out.PullGtPf.isMonHom_of_grpPullback hp' hp p _ e`. Take `⟨ρ, hρ⟩` from `(GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt 0) hr hp).2 _ (GlobalTheory.TorusPart.gtTorus (U'.gt 0) hr hp' ≫ (Over.pullback (spMap (residue R))).map p) inferInstance`. Use `⟨ρ, ?_⟩` and prove the remaining obligations. Introduce `F _ _ i₁ i₂ hF k hk τ τ' q q' a a' hτ'k hττ' hqy hq hq'y hq' ha ha'`. Establish `hi : i₁ = i₂` using `Algebra.algebra_ext _ _ fun x => RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors R) (j := @algebraMap _ _ _ _ i₁) (k := @algebraMap _ _ _ _ i₂) (RingHom.ext hF)) x`.

Substitute `hi` using the available equality. Establish `hk1 : 1 ≤ k`. Break down `Nat.eq_zero_or_pos k with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using `at hk`.

Conclude with `h`. Take `⟨s, s1, s2, s3, s4⟩` from `GlobalTheory.ToricTorsionUnif.main R hR G hG D A U k hk1`. Take `⟨s', s1', s2', s3', s4'⟩` from `GlobalTheory.ToricTorsionUnif.main R hR G' hG' D' A' U' k hk1`. Set `ρm` to `AddMonoidHom.toMultiplicative ρ`. Establish `powc : ∀ {H : Type} [CommGroup H] (f : Multiplicative D'.toPre.X →* H), f ^ k = 1 → (f.comp ρm) ^ k = 1` using `fun f hf => MonoidHom.ext fun x => by`.

Rewrite using `[MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hf]`. Both sides reduce to the same expression. Establish `hτ : τ = τ'.comp ρm` using `MonoidHom.ext fun x => hττ' (Multiplicative.toAdd x)`. Establish `hτk : τ ^ k = 1`. Rewrite using `[hτ]`.

Conclude with `powc τ' hτ'k`. Set `c : R →+* F` to `(algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))`. Rewrite using `[s4 F c τ hτk q a rfl hqy hq ha, ← Category.assoc, s4' F c τ' hτ'k q' a' rfl hq'y hq' ha']`. Take `⟨O, hO, hloc⟩` from `IsLocalRing.exists_factor_valuationRing c`. Set `φ : R →+* O` to `c.codRestrict O.toSubring hO`.

Use `haveI : IsLocalHom φ := hloc`. Establish `hc : c = O.subtype.comp φ` using `rfl`. Take `⟨τO, hτO⟩` from `GlobalTheory.ToricTorsionCompare.units_of_pow_eq_one F O _ k hk1 τ' hτ'k`. Establish `hτOk : τO ^ k = 1`. Use `MonoidHom.ext fun x => Units.ext (Subtype.ext ?_)` and prove the remaining obligations.

Use `congrArg (fun f => ((f x : Fˣ) : F)) hτ'k` as an intermediate fact. Simplify using `only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one] at this ⊢`. Rewrite using `[SubmonoidClass.coe_pow, hτO, this]`. Both sides reduce to the same expression. Set `τR` to `τO.comp ρm`.

Establish `hτR : τR ^ k = 1` using `powc τO hτOk`. Establish `hkO : IsUnit (k : O)` using `by simpa using hk.map φ`. Establish `hxy : s O φ τR hτR = s' O φ τO hτOk ≫ p`. Use `GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) G hG.smooth O (spMap φ) k hkO _ _ ?_ (ResidueField O) (residue O) inferInstance ?_` and prove the remaining obligations. Rewrite using `[s1, ← pow_comp_monHom, s1', MonObj.one_comp]`.

Set `τ₀ : Multiplicative D'.toPre.X →* (ResidueField O)ˣ` to `(Units.map (residue O).toMonoidHom).comp τO`. Establish `h₀ : τ₀ ^ k = 1`. Rewrite using `[show τ₀ ^ k = (Units.map (residue O).toMonoidHom).comp (τO ^ k) by ext x; simp [τ₀]]`. Rewrite using `[hτOk]`. Use `ext`.

Simplify using the standard rewrite rules. Set `τ₁` to `τ₀.comp ρm`. Establish `h₁ : τ₁ ^ k = 1` using `powc τ₀ h₀`. Set `z : Over.mk (spMap (ResidueField.map φ)) ⟶ splitTorus (Sp (ResidueField R)) D'.toPre.X` to `(GlobalTheory.splitTorusPointsEquiv _ _ _).symm ((Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField O))).inv.hom.toMonoidHom).comp τ₀)`. Establish `hz : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ₀ (Multiplicative.ofAdd χ))` using `fun χ => by`.

Simplify using `only [GlobalTheory.UU.chV, z, MulEquiv.apply_symm_apply]`. Both sides reduce to the same expression. Establish `hz₁ : ∀ χ, GlobalTheory.UU.chV (z ≫ GlobalTheory.SplitTorus.torusMap _ ρ) χ = unitOn (τ₁ (Multiplicative.ofAdd χ))` using `fun χ => by`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_comp_torusMap, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.UU.chV_val, hz]`.

Both sides reduce to the same expression. Establish `hres : (residue O).comp φ = (ResidueField.map φ).comp (residue R)`. Use extensionality with `r`. Simplify using `[ResidueField.map_residue]`. Rewrite using `[Over.comp_left, ← Category.assoc, ← s2 O _ φ ((residue O).comp φ) (residue O) τR hτR τ₁ h₁ rfl (fun χ => rfl), ← s2' O _ φ ((residue O).comp φ) (residue O) τO hτOk τ₀ h₀ rfl (fun χ => rfl), s3 _ _ (residue R) hr _ (ResidueField.map φ) _ _ hp τ₁ h₁ _ hres hz₁, s3' _ _ (residue R) …`.

Simplify using `only [Over.comp_left, Category.assoc]`. Rewrite using `[s2 O F φ c O.subtype τR hτR τ hτk hc (fun χ => by simp [τR, hτ, hτO]), s2' O F φ c O.subtype τO hτOk τ' hτ'k hc (fun χ => by simp [hτO]), hxy, Over.comp_left, Category.assoc]`.
-/
theorem exists_torMatch : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (p : G' ⟶ G), IsMonHom p → ∃ ρ, TorMatch U U' (RingHom.id R) p.left ρ := by
  intro R _ _ _ hR G _ _ hG D A U G' _ _ hG' D' A' U' p hpm
  have hr : ∀ x ∈ maximalIdeal R ^ (0 + 1), residue R x = 0 := fun x hx =>
    (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx)
  have hp := isGrpPullback_pullback G (spMap (residue R))
  have hp' := isGrpPullback_pullback G' (spMap (residue R))
  have e : ((Over.pullback (spMap (residue R))).map p).left ≫ pullback.fst G.hom (spMap (residue R)) =
      pullback.fst G'.hom (spMap (residue R)) ≫ p.left := pullback.lift_fst _ _ _
  have hf₁ : IsMonHom ((Over.pullback (spMap (residue R))).map p) :=
    Out.PullGtPf.isMonHom_of_grpPullback hp' hp p _ e
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt 0) hr hp).2 _
    (GlobalTheory.TorusPart.gtTorus (U'.gt 0) hr hp' ≫ (Over.pullback (spMap (residue R))).map p) inferInstance
  refine ⟨ρ, ?_⟩
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
    · rw [s1, ← pow_comp_monHom, s1', MonObj.one_comp]
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

end GlobalTheory.Poinc.HomTor

end
