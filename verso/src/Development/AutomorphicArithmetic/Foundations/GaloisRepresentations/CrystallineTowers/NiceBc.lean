import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.Seam

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.
-/
private theorem fEt_of_isPullback {P Y Z' Z : Scheme.{0}} {v : P ⟶ Y} {s' : P ⟶ Z'} {s : Y ⟶ Z} {g : Z' ⟶ Z} {d : ℕ}
    (h : IsPullback v s' s g) (hs : FEt s d) : FEt s' d := by
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) h hs.1,
    MorphismProperty.of_isPullback (P := @Etale) h hs.2.1, ?_⟩
  intro K _ _ x
  rw [← hs.2.2 K (x ≫ g)]
  refine Nat.card_congr
    { toFun := fun y => ⟨y.1 ≫ v, by rw [Category.assoc, h.w, ← Category.assoc, y.2]⟩
      invFun := fun y => ⟨h.lift y.1 x (by rw [y.2]), h.lift_snd _ _ _⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro y
    apply Subtype.ext
    apply h.hom_ext
    · simp
    · simp [y.2]
  · intro y
    apply Subtype.ext
    simp

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem isPullback_sΩ {k : Type} [Field k] (H : HTower k) (K : Type) [Field K] [Algebra k K] (g : H.Γ) :
    IsPullback (pullback.fst (H.s g ≫ H.q) (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (H.sΩ K g) (H.s g)
      (pullback.fst H.q (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  have hfst : H.sΩ K g ≫ pullback.fst H.q (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.fst (H.s g ≫ H.q) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫ H.s g :=
    pullback.lift_fst _ _ _
  have hsnd : H.sΩ K g ≫ pullback.snd H.q (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.snd (H.s g ≫ H.q) (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    pullback.lift_snd _ _ _
  refine IsPullback.of_bot (v₂₁ := pullback.snd H.q (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (v₂₂ := H.q)
    (h₃₁ := Spec.map (CommRingCat.ofHom (algebraMap k K))) ?_ hfst.symm (IsPullback.of_hasPullback _ _)
  rw [hsnd]
  exact IsPullback.of_hasPullback _ _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Equip the data with the indicated structure. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem niceBc : NiceBc := by
  intro k K _ _ τ H hN
  obtain ⟨hsm, hproj, hfet⟩ := hN
  letI : Algebra k K := τ.toAlgebra
  unfold bcAlong
  refine ⟨?_, ?_, ?_⟩
  · haveI := hsm
    show Smooth (pullback.snd H.q (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    infer_instance
  · exact GlobalTheory.ProjSpace.isProjOver_pullback_snd (algebraMap k K) hproj
  · intro g
    obtain ⟨d, hd⟩ := hfet g
    exact ⟨d, fEt_of_isPullback (isPullback_sΩ H K g) hd⟩

end UpperTheory.Gal.Seam

end
