import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsAlgClosureFractionRingBijective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Simplify using `only [TFK, Over.mk_hom, jFK]`. Rewrite using `[← Spec.map_comp]`. Use `congr 1`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem spMap_comp_tfk {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]
    (em : Kb R →ₐ[FractionRing R] F) :
    spMap em.toRingHom ≫ (TFK (R := R) (Kb R)).hom = (TFK (R := R) F).hom := by
  simp only [TFK, Over.mk_hom, jFK]
  rw [← Spec.map_comp]
  congr 1
  ext x
  simp

/- English proof (translation)
Introduce `R _ _ _ hR D C j W _ _ _ T F _ _ _ _ em hF f hfi hf1 hf2`. Establish `: CharZero R` using `hR.2`. Establish `hN : 1 ≤ C.n ^ j` using `Nat.one_le_pow _ _ C.n_prime.pos`. Establish `hbij` using `qkPt_algClosure_bijective R D.toPre F em (C.n ^ j) hN`. Establish `hpull : ∀ p' : QkPt T.D'.toPre F (C.n ^ j), ∃ p₁ : QkPt D.toPre F (C.n ^ j), p'.y = T.hD.xe.symm p₁.y ∧ IsPullGtF T.φ T.hD F p₁.g p'.g` using `fun p' => qkPullExists GlobalTheory.globalFns_holds R W T.φ D.toPre T.D'.toPre T.hD F hF (C.n ^ j) p'`.

Establish `huniq : ∀ (p' : QkPt T.D'.toPre F (C.n ^ j)) (p₁ p₂ : QkPt D.toPre F (C.n ^ j)), p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → p'.y = T.hD.xe.symm p₂.y → IsPullGtF T.φ T.hD F p₂.g p'.g → p₁ = p₂` using `fun p' p₁ p₂ h₁ g₁ h₂ g₂ => GlobalTheory.TorusExt.qk_ext (T.hD.xe.symm.injective (h₁.symm.trans h₂)) (GlobalTheory.ArcPull.pullGt_unique' T.hD g₁ g₂)`. Use `choose P₁ hP₁ using hpull`. Use `choose P hP using fun p' => (hbij.2 (P₁ p')).exists`. Set `y : QkPt D.toPre (Kb R) (C.n ^ j) → (TFK (R` to `R) F ⟶ C.A.A) := fun p => Over.homMk (spMap em.toRingHom ≫ (C.lab j p).left) (by`. Rewrite using `[Category.assoc, Over.w, spMap_comp_tfk])`.

Set `g : QkPt D.toPre (Kb R) (C.n ^ j) → (TFK (R` to `R) F ⟶ TFK (R := R) F ⊗ C.A.A) := fun p => lift (𝟙 _) (y p)`. Establish `hg1 : ∀ p, (g p).left ≫ (fst (TFK (R` using `R) F) C.A.A).left = 𝟙 _ := fun p => by`. Rewrite using `[← Over.comp_left, lift_fst]`. Both sides reduce to the same expression. Establish `hg2 : ∀ p, (g p).left ≫ (snd (TFK (R` using `R) F) C.A.A).left = spMap em.toRingHom ≫ (C.lab j p).left := fun p => by`.

Rewrite using `[← Over.comp_left, lift_snd]`. Both sides reduce to the same expression. Establish `hfst : inv f ≫ (fst (TFK (R` using `W) F) T.A.A).left = (fst (TFK (R := R) F) C.A.A).left := by`. Rewrite using `[← hf1, IsIso.inv_hom_id_assoc]`. Set `lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R` to `W) F ⟶ T.A.A) := fun p' => Over.homMk ((g (P p')).left ≫ inv f ≫ (snd (TFK (R := W) F) T.A.A).left) (by`.

Rewrite using `[Category.assoc, Category.assoc, Over.w (snd (TFK (R := W) F) T.A.A), ← Over.w (fst (TFK (R := W) F) T.A.A), reassoc_of% hfst, reassoc_of% (hg1 (P p'))])`. Establish `heq : ∀ p', (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j (P p')).left ≫ C.α` using `fun p' => by`. Simplify using `only [lab', Over.homMk_left, Category.assoc]`. Rewrite using `[← hf2, IsIso.inv_hom_id_assoc, reassoc_of% (hg2 (P p'))]`. Use `⟨lab', fun p' => T.lab F em hF j (P p') (P₁ p') p' (lab' p') (hP p') (hP₁ p').1 (hP₁ p').2 (heq p'), ?_⟩` and prove the remaining obligations.

Introduce `p p₁ p' hE hy hgp`. Take `rfl : p₁ = P₁ p'` from `huniq p' p₁ (P₁ p') hy hgp (hP₁ p').1 (hP₁ p').2`. Take `rfl : p = P p'` from `(hbij.2 (P₁ p')).unique hE (hP p')`. Conclude with `heq p'`.
-/
theorem Trait.exists_lab_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∃ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ p', QkToAkU T.U.toUnifPre F (C.n ^ j) p' (lab' p')) ∧ ∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α := by
  intro R _ _ _ hR D C j W _ _ _ T F _ _ _ _ em hF f hfi hf1 hf2
  have : CharZero R := hR.2
  have hN : 1 ≤ C.n ^ j := Nat.one_le_pow _ _ C.n_prime.pos
  have hbij := qkPt_algClosure_bijective R D.toPre F em (C.n ^ j) hN
  have hpull : ∀ p' : QkPt T.D'.toPre F (C.n ^ j), ∃ p₁ : QkPt D.toPre F (C.n ^ j),
      p'.y = T.hD.xe.symm p₁.y ∧ IsPullGtF T.φ T.hD F p₁.g p'.g := fun p' =>
    qkPullExists GlobalTheory.globalFns_holds R W T.φ D.toPre T.D'.toPre T.hD F hF (C.n ^ j) p'
  have huniq : ∀ (p' : QkPt T.D'.toPre F (C.n ^ j)) (p₁ p₂ : QkPt D.toPre F (C.n ^ j)),
      p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g →
      p'.y = T.hD.xe.symm p₂.y → IsPullGtF T.φ T.hD F p₂.g p'.g → p₁ = p₂ :=
    fun p' p₁ p₂ h₁ g₁ h₂ g₂ => GlobalTheory.TorusExt.qk_ext (T.hD.xe.symm.injective (h₁.symm.trans h₂))
      (GlobalTheory.ArcPull.pullGt_unique' T.hD g₁ g₂)
  choose P₁ hP₁ using hpull
  choose P hP using fun p' => (hbij.2 (P₁ p')).exists

  let y : QkPt D.toPre (Kb R) (C.n ^ j) → (TFK (R := R) F ⟶ C.A.A) := fun p =>
    Over.homMk (spMap em.toRingHom ≫ (C.lab j p).left) (by
      rw [Category.assoc, Over.w, spMap_comp_tfk])
  let g : QkPt D.toPre (Kb R) (C.n ^ j) → (TFK (R := R) F ⟶ TFK (R := R) F ⊗ C.A.A) := fun p => lift (𝟙 _) (y p)
  have hg1 : ∀ p, (g p).left ≫ (fst (TFK (R := R) F) C.A.A).left = 𝟙 _ := fun p => by
    rw [← Over.comp_left, lift_fst]; rfl
  have hg2 : ∀ p, (g p).left ≫ (snd (TFK (R := R) F) C.A.A).left = spMap em.toRingHom ≫ (C.lab j p).left := fun p => by
    rw [← Over.comp_left, lift_snd]; rfl
  have hfst : inv f ≫ (fst (TFK (R := W) F) T.A.A).left = (fst (TFK (R := R) F) C.A.A).left := by
    rw [← hf1, IsIso.inv_hom_id_assoc]
  let lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A) := fun p' =>
    Over.homMk ((g (P p')).left ≫ inv f ≫ (snd (TFK (R := W) F) T.A.A).left) (by
      rw [Category.assoc, Category.assoc, Over.w (snd (TFK (R := W) F) T.A.A), ← Over.w (fst (TFK (R := W) F) T.A.A),
        reassoc_of% hfst, reassoc_of% (hg1 (P p'))])
  have heq : ∀ p', (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β =
      spMap em.toRingHom ≫ (C.lab j (P p')).left ≫ C.α := fun p' => by
    simp only [lab', Over.homMk_left, Category.assoc]
    rw [← hf2, IsIso.inv_hom_id_assoc, reassoc_of% (hg2 (P p'))]
  refine ⟨lab', fun p' => T.lab F em hF j (P p') (P₁ p') p' (lab' p') (hP p') (hP₁ p').1 (hP₁ p').2 (heq p'), ?_⟩
  intro p p₁ p' hE hy hgp
  obtain rfl : p₁ = P₁ p' := huniq p' p₁ (P₁ p') hy hgp (hP₁ p').1 (hP₁ p').2
  obtain rfl : p = P p' := (hbij.2 (P₁ p')).unique hE (hP p')
  exact heq p'

end GlobalTheory.Mum
