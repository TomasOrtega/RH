import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqZeroOfFpqc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

open GlobalTheory.CechPic GlobalTheory.BirigUniq in

/- English proof (translation)
Introduce `S A A' _ _ _ _ hA hA' ψ hm hfin het hsurj P Q hP hQ h1 h2 h3 h4 hiso`. Establish `hfl : Flat (Over.Hom.left ψ)` using `inferInstance`. Establish `hqc : QuasiCompact (Over.Hom.left ψ)` using `inferInstance`. Establish `hcls : ∀ {Y : Scheme} (F : Y ⟶ (G2 A').left), pull F (cls P hP - cls Q hQ) = cls (P.pull F) (pull_isLB hP F) - cls (Q.pull F) (pull_isLB hQ F)`. Introduce `Y F`.

Rewrite using `[map_sub]`. Both sides reduce to the same expression. Establish `hzero : ∀ {Y : Scheme} (F : Y ⟶ (G2 A').left), LBIso (P.pull F) (Q.pull F) → pull F (cls P hP - cls Q hQ) = 0`. Introduce `Y F h`. Rewrite using `[hcls, sub_eq_zero]`.

Conclude with `(cls_eq_iff _ _).mpr h`. Use `set d := cls P hP - cls Q hQ with hd`. Establish `hs1 : pull (Over.Hom.left (lift (1 : A' ⟶ A') (𝟙 A'))) d = 0`. Rewrite using `[hcls, sub_eq_zero, (cls_eq_zero_iff _).mpr h1, (cls_eq_zero_iff _).mpr h3]`. Establish `hs2 : pull (Over.Hom.left (lift (𝟙 A') (1 : A' ⟶ A'))) d = 0`.

Rewrite using `[hcls, sub_eq_zero, (cls_eq_zero_iff _).mpr h2, (cls_eq_zero_iff _).mpr h4]`. Establish `hsq : pull (Hecke.sq2 ψ) d = 0` using `hzero _ hiso`. Set `E : A' ⊗ A ⟶ A' ⊗ A'` to `lift (fst A' A) (snd A' A ≫ ψ)`. Set `W : A ⊗ A' ⟶ A' ⊗ A` to `lift (snd A A') (fst A A')`. Set `W' : A' ⊗ A ⟶ A ⊗ A'` to `lift (snd A' A) (fst A' A)`.

Establish `hf : pull (Over.Hom.left (W ≫ E)) d = 0`. Use `pic_eq_zero_of_fpqc A A' A hA ψ hfl hsurj hqc _ ?_ ?_` and prove the remaining obligations. Rewrite using `[← pull_comp_left]`. Establish `: lift (1 : A' ⟶ A) (𝟙 A') ≫ W ≫ E = lift (𝟙 A') (1 : A' ⟶ A')`. Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp [E, W, one_comp_monHom]`.

Rewrite using `[this, hs2]`. Rewrite using `[← pull_comp_left]`. Establish `: lift (fst A A) (snd A A ≫ ψ) ≫ W ≫ E = lift (snd A A) (fst A A) ≫ lift (fst A A ≫ ψ) (snd A A ≫ ψ)`. Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp [E, W]`. Rewrite using `[this, pull_comp_left]`.

Establish `h' : pull (Over.Hom.left (lift (fst A A ≫ ψ) (snd A A ≫ ψ))) d = 0` using `hsq`. Rewrite using `[h', map_zero]`. Establish `he : pull (Over.Hom.left E) d = 0`. Establish `: W' ≫ W ≫ E = E`. Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp [E, W, W']`.

Rewrite using `[← this, pull_comp_left, hf, map_zero]`. Establish `hd0 : d = 0` using `pic_eq_zero_of_fpqc A' A' A hA' ψ hfl hsurj hqc d hs1 he`. Rewrite `hd0` using `[hd, sub_eq_zero]`. Conclude with `(cls_eq_iff hP hQ).mp hd0`.
-/
theorem UpperTheory.Gal.G3.pPolUniq :
    PolUniq := by
  intro S A A' _ _ _ _ hA hA' ψ hm hfin het hsurj P Q hP hQ h1 h2 h3 h4 hiso
  have hfl : Flat (Over.Hom.left ψ) := inferInstance
  have hqc : QuasiCompact (Over.Hom.left ψ) := inferInstance
  have hcls : ∀ {Y : Scheme} (F : Y ⟶ (G2 A').left),
      pull F (cls P hP - cls Q hQ) = cls (P.pull F) (pull_isLB hP F) - cls (Q.pull F) (pull_isLB hQ F) := by
    intro Y F
    rw [map_sub]
    rfl
  have hzero : ∀ {Y : Scheme} (F : Y ⟶ (G2 A').left), LBIso (P.pull F) (Q.pull F) →
      pull F (cls P hP - cls Q hQ) = 0 := by
    intro Y F h
    rw [hcls, sub_eq_zero]
    exact (cls_eq_iff _ _).mpr h
  set d := cls P hP - cls Q hQ with hd
  have hs1 : pull (Over.Hom.left (lift (1 : A' ⟶ A') (𝟙 A'))) d = 0 := by
    rw [hcls, sub_eq_zero, (cls_eq_zero_iff _).mpr h1, (cls_eq_zero_iff _).mpr h3]
  have hs2 : pull (Over.Hom.left (lift (𝟙 A') (1 : A' ⟶ A'))) d = 0 := by
    rw [hcls, sub_eq_zero, (cls_eq_zero_iff _).mpr h2, (cls_eq_zero_iff _).mpr h4]
  have hsq : pull (Hecke.sq2 ψ) d = 0 := hzero _ hiso
  let E : A' ⊗ A ⟶ A' ⊗ A' := lift (fst A' A) (snd A' A ≫ ψ)
  let W : A ⊗ A' ⟶ A' ⊗ A := lift (snd A A') (fst A A')
  let W' : A' ⊗ A ⟶ A ⊗ A' := lift (snd A' A) (fst A' A)
  have hf : pull (Over.Hom.left (W ≫ E)) d = 0 := by
    refine pic_eq_zero_of_fpqc A A' A hA ψ hfl hsurj hqc _ ?_ ?_
    · rw [← pull_comp_left]
      have : lift (1 : A' ⟶ A) (𝟙 A') ≫ W ≫ E = lift (𝟙 A') (1 : A' ⟶ A') := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [E, W, one_comp_monHom]
      rw [this, hs2]
    · rw [← pull_comp_left]
      have : lift (fst A A) (snd A A ≫ ψ) ≫ W ≫ E
          = lift (snd A A) (fst A A) ≫ lift (fst A A ≫ ψ) (snd A A ≫ ψ) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [E, W]
      rw [this, pull_comp_left]
      have h' : pull (Over.Hom.left (lift (fst A A ≫ ψ) (snd A A ≫ ψ))) d = 0 := hsq
      rw [h', map_zero]
  have he : pull (Over.Hom.left E) d = 0 := by
    have : W' ≫ W ≫ E = E := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [E, W, W']
    rw [← this, pull_comp_left, hf, map_zero]
  have hd0 : d = 0 := pic_eq_zero_of_fpqc A' A' A hA' ψ hfl hsurj hqc d hs1 he
  rw [hd, sub_eq_zero] at hd0
  exact (cls_eq_iff hP hQ).mp hd0
