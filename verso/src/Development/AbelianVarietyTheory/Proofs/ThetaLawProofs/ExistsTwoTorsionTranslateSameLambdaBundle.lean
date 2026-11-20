import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.SameLam

open GlobalTheory.CechPic GlobalTheory.PrimitiveOverField

/- English proof (translation)
Take `⟨s⟩ : Nonempty (Sp K)` from `inferInstance`. Take `⟨U, hU, t, ht⟩` from `hs s`. Establish `hV : ∀ z : A.left, z ∈ A.hom ⁻¹ᵁ U` using `fun z => by show A.hom.base z ∈ U`. Rewrite using `[Subsingleton.elim (A.hom.base z) s]`. Conclude with `hU`.

Establish `hι : IsIso (A.hom ⁻¹ᵁ U).ι`. Rewrite using `[isIso_iff_isOpenImmersion_and_surjective]`. Use `⟨inferInstance, ⟨fun z => ?_⟩⟩` and prove the remaining obligations. Establish `hz : z ∈ Set.range (A.hom ⁻¹ᵁ U).ι.base`. Rewrite using `[Scheme.Opens.range_ι]`.

Conclude with `hV z`. Conclude with `hz`. Establish `hc` using `(cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨t, ht⟩`. Rewrite `hc` using `[cls_linComb hL]`. Simplify using `only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_comp] at hc`.

Establish `key : pull (A.hom ⁻¹ᵁ U).ι (pull (GrpObj.inv : A ⟶ A).left (cls L hL) - cls L hL) = 0`. Rewrite using `[map_sub, ← hc, sub_eq_add_neg]`. Establish `h2` using `congrArg (pull (inv (A.hom ⁻¹ᵁ U).ι)) key`. Rewrite `h2` using `[← pull_comp, IsIso.inv_hom_id, pull_id, map_zero]`. Conclude with `sub_eq_zero.1 h2`.
-/
theorem pull_inv_cls {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {L : LB A.left}
    (hL : L.IsLB) (hs : Out.Sym A L) : pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL := by
  obtain ⟨s⟩ : Nonempty (Sp K) := inferInstance
  obtain ⟨U, hU, t, ht⟩ := hs s
  have hV : ∀ z : A.left, z ∈ A.hom ⁻¹ᵁ U := fun z => by
    show A.hom.base z ∈ U
    rw [Subsingleton.elim (A.hom.base z) s]
    exact hU
  have hι : IsIso (A.hom ⁻¹ᵁ U).ι := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun z => ?_⟩⟩
    have hz : z ∈ Set.range (A.hom ⁻¹ᵁ U).ι.base := by
      rw [Scheme.Opens.range_ι]
      exact hV z
    exact hz
  have hc := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨t, ht⟩
  rw [cls_linComb hL] at hc
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul,
    neg_smul, pull_comp] at hc
  have key : pull (A.hom ⁻¹ᵁ U).ι (pull (GrpObj.inv : A ⟶ A).left (cls L hL) - cls L hL) = 0 := by
    rw [map_sub, ← hc, sub_eq_add_neg]
  have h2 := congrArg (pull (inv (A.hom ⁻¹ᵁ U).ι)) key
  rw [← pull_comp, IsIso.inv_hom_id, pull_id, map_zero] at h2
  exact sub_eq_zero.1 h2

/- English proof (translation)
Introduce `hLaws K _ _ P P' e he hLam`. Take `⟨φ₂, hsq, hiso⟩` from `hLam`. Establish `hw : φ₂ ≫ (P.A ⊗ P.A).hom = (P'.A ⊗ P'.A).hom`. Rewrite using `[← Over.w (fst P.A P.A), ← Category.assoc, hsq.1, Category.assoc, Over.w e.hom, Over.w (fst P'.A P'.A)]`. Establish `hf : Over.homMk φ₂ hw ≫ fst P.A P.A = fst P'.A P'.A ≫ e.hom`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `using hsq.1`. Establish `hs : Over.homMk φ₂ hw ≫ snd P.A P.A = snd P'.A P'.A ≫ e.hom`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `using hsq.2`.

Establish `hcube : ∀ Q : Out.PolAV (Sp K), (abelian₂ Q.A Q.L).IsLB` using `fun Q => LB.isLB_linComb Q.isLB _ _`. Establish `hLc : ∀ Q : Out.PolAV (Sp K), cls _ (hcube Q) = lam (cls Q.L Q.isLB) (fst Q.A Q.A) (snd Q.A Q.A)` using `fun Q => cls_cube_two Q.isLB _ _ (hcube Q)`. Establish `hcls` using `(cls_eq_iff (hcube P') (pull_isLB (hcube P) φ₂)).2 hiso`. Rewrite `hcls` using `[cls_pull (hcube P), hLc P', hLc P]`. Establish `hA : lam (cls P'.L P'.isLB) (fst P'.A P'.A) (snd P'.A P'.A) = lam (cls P.L P.isLB) (fst P'.A P'.A ≫ e.hom) (snd P'.A P'.A ≫ e.hom)`.

Rewrite using `[hcls, ← hf, ← hs]`. Conclude with `pull_lam (Over.homMk φ₂ hw) _ _ _`. Establish `hB : lam (pull e.inv.left (cls P'.L P'.isLB)) (fst P.A P.A) (snd P.A P.A) = lam (cls P.L P.isLB) (fst P.A P.A) (snd P.A P.A)`. Establish `h1` using `congrArg (pull (lift (fst P.A P.A ≫ e.inv) (snd P.A P.A ≫ e.inv)).left) hA`. Rewrite `h1` using `[pull_lam, pull_lam]`.

Simplify using `only [lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd, Category.assoc, Iso.inv_hom_id, Category.comp_id] at h1`. Rewrite using `[lam_pull e.inv]`. Conclude with `h1`. Establish `hO : (GlobalTheory.CechPic.tens (P'.L.pull e.inv.left) (GlobalTheory.CechPic.dual P.L)).IsLB` using `isLB_tens (pull_isLB P'.isLB _) (isLB_dual P.isLB)`. Establish `hOc : cls _ hO = pull e.inv.left (cls P'.L P'.isLB) + -cls P.L P.isLB`.

Rewrite using `[cls_tens (pull_isLB P'.isLB _) (isLB_dual P.isLB), cls_pull P'.isLB, cls_dual P.isLB]`. Establish `hLO : (abelian₂ P.A (GlobalTheory.CechPic.tens (P'.L.pull e.inv.left) (GlobalTheory.CechPic.dual P.L))).IsLB` using `LB.isLB_linComb hO _ _`. Establish `hz : cls _ hLO = 0`. Use `(cls_cube_two hO _ _ hLO).trans ?_` and prove the remaining obligations. Rewrite using `[hOc]`.

Use `Eq.trans ?_ (sub_eq_zero.2 hB)` and prove the remaining obligations. Simplify using `only [lam, map_add, map_neg]`. Normalize the expressions using the abelian group laws. Take `⟨u, hu⟩` from `(cls_eq_zero_iff hLO).1 hz`. Take `⟨y, hy⟩` from `GlobalTheory.PrimitiveOverField.exists_point_translate hLaws K P _ hO ⟨u, hu⟩`.

Establish `hyc` using `(cls_eq_iff hO (LB.isLB_linComb P.isLB _ _)).2 hy`. Rewrite `hyc` using `[hOc, cls_linComb P.isLB]`. Simplify using `only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, pull_id] at hyc`. Establish `hd : pull e.inv.left (cls P'.L P'.isLB) = pull (toUnit P.A ≫ y * 𝟙 P.A).left (cls P.L P.isLB)` using `add_right_cancel hyc`. Establish `hc' : cls P'.L P'.isLB = pull (e.hom ≫ (toUnit P.A ≫ y * 𝟙 P.A)).left (cls P.L P.isLB)`.

Rewrite using `[Over.comp_left, pull_comp, ← hd, ← pull_comp, ← Over.comp_left, e.hom_inv_id, Over.id_left, pull_id]`. Use `⟨y, ?_, (cls_eq_iff P'.isLB (pull_isLB P.isLB _)).1 (by rw [cls_pull P.isLB]; exact hc')⟩` and prove the remaining obligations. Establish `hTh : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen` using `GlobalTheory.Moduli.cube_of_isLB _ P P.L P.isLB`. Establish `hsymA` using `pull_inv_cls P.isLB P.sym`. Establish `hsymA'` using `pull_inv_cls P'.isLB P'.sym`.

Establish `hdι : pull (GrpObj.inv : P.A ⟶ P.A).left (pull e.inv.left (cls P'.L P'.isLB)) = pull e.inv.left (cls P'.L P'.isLB)`. Rewrite using `[← pull_comp, ← Over.comp_left, GrpObj.inv_hom, Over.comp_left, pull_comp, hsymA']`. Rewrite `hdι` using `[hd]`. Establish `hlc` using `GlobalTheory.PrimitiveOverField.lam_const (B := P.A) (cls P.L P.isLB) y (𝟙 P.A)`. Rewrite `hlc` using `[Over.id_left, pull_id]`.

Establish `hpa : pull (GrpObj.inv : P.A ⟶ P.A).left (lam (cls P.L P.isLB) (toUnit P.A ≫ y) (𝟙 P.A)) = lam (cls P.L P.isLB) (toUnit P.A ≫ y) (𝟙 P.A)`. Rewrite using `[hlc, map_sub, hdι, hsymA]`. Rewrite `hpa` using `[pull_lam, ← Category.assoc, toUnit_unique (GrpObj.inv ≫ toUnit P.A) (toUnit P.A), Category.comp_id]`. Establish `hneg : lam (cls P.L P.isLB) (toUnit P.A ≫ y) GrpObj.inv = -lam (cls P.L P.isLB) (toUnit P.A ≫ y) (𝟙 P.A)`. Rewrite using `[lam_comm, lam_comm _ _ (𝟙 P.A), eq_neg_iff_add_eq_zero, ← lam_mul_left P.isLB hTh, GrpObj.inv_eq_inv, inv_mul_cancel, lam_one_left]`.

Establish `h2a : lam (cls P.L P.isLB) (toUnit P.A ≫ y ^ 2) (𝟙 P.A) = 0`. Rewrite using `[MonObj.comp_pow, lam_pow_left P.isLB hTh, two_nsmul]`. Use `nth_rewrite 1 [← hpa]`. Rewrite using `[hneg, neg_add_cancel]`. Conclude with `GlobalTheory.PrimitiveOverField.eq_one_of_lam_eq_zero P.isLB P.ktriv _ h2a`.
-/
theorem exists_two_torsion_translate : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P P' : Out.PolAV (Sp K)) (e : P'.A ≅ P.A), IsMonHom e.hom → LamIs P'.A P'.L P.A (abelian₂ P.A P.L) e.hom.left → ∃ t : 𝟙_ (Over (Sp K)) ⟶ P.A, t ^ 2 = 1 ∧ LBIso P'.L (P.L.pull (e.hom ≫ ((toUnit P.A ≫ t) * 𝟙 P.A)).left) := by
  intro hLaws K _ _ P P' e he hLam
  obtain ⟨φ₂, hsq, hiso⟩ := hLam
  have hw : φ₂ ≫ (P.A ⊗ P.A).hom = (P'.A ⊗ P'.A).hom := by
    rw [← Over.w (fst P.A P.A), ← Category.assoc, hsq.1, Category.assoc, Over.w e.hom,
      Over.w (fst P'.A P'.A)]
  have hf : Over.homMk φ₂ hw ≫ fst P.A P.A = fst P'.A P'.A ≫ e.hom := by
    apply Over.OverMorphism.ext
    simpa using hsq.1
  have hs : Over.homMk φ₂ hw ≫ snd P.A P.A = snd P'.A P'.A ≫ e.hom := by
    apply Over.OverMorphism.ext
    simpa using hsq.2
  have hcube : ∀ Q : Out.PolAV (Sp K), (abelian₂ Q.A Q.L).IsLB := fun Q => LB.isLB_linComb Q.isLB _ _
  have hLc : ∀ Q : Out.PolAV (Sp K),
      cls _ (hcube Q) = lam (cls Q.L Q.isLB) (fst Q.A Q.A) (snd Q.A Q.A) :=
    fun Q => cls_cube_two Q.isLB _ _ (hcube Q)
  have hcls := (cls_eq_iff (hcube P') (pull_isLB (hcube P) φ₂)).2 hiso
  rw [cls_pull (hcube P), hLc P', hLc P] at hcls
  have hA : lam (cls P'.L P'.isLB) (fst P'.A P'.A) (snd P'.A P'.A) =
      lam (cls P.L P.isLB) (fst P'.A P'.A ≫ e.hom) (snd P'.A P'.A ≫ e.hom) := by
    rw [hcls, ← hf, ← hs]
    exact pull_lam (Over.homMk φ₂ hw) _ _ _
  have hB : lam (pull e.inv.left (cls P'.L P'.isLB)) (fst P.A P.A) (snd P.A P.A) =
      lam (cls P.L P.isLB) (fst P.A P.A) (snd P.A P.A) := by
    have h1 := congrArg (pull (lift (fst P.A P.A ≫ e.inv) (snd P.A P.A ≫ e.inv)).left) hA
    rw [pull_lam, pull_lam] at h1
    simp only [lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] at h1
    rw [lam_pull e.inv]
    exact h1
  have hO : (GlobalTheory.CechPic.tens (P'.L.pull e.inv.left) (GlobalTheory.CechPic.dual P.L)).IsLB :=
    isLB_tens (pull_isLB P'.isLB _) (isLB_dual P.isLB)
  have hOc : cls _ hO = pull e.inv.left (cls P'.L P'.isLB) + -cls P.L P.isLB := by
    rw [cls_tens (pull_isLB P'.isLB _) (isLB_dual P.isLB), cls_pull P'.isLB, cls_dual P.isLB]
  have hLO : (abelian₂ P.A (GlobalTheory.CechPic.tens (P'.L.pull e.inv.left) (GlobalTheory.CechPic.dual P.L))).IsLB :=
    LB.isLB_linComb hO _ _
  have hz : cls _ hLO = 0 := by
    refine (cls_cube_two hO _ _ hLO).trans ?_
    rw [hOc]
    refine Eq.trans ?_ (sub_eq_zero.2 hB)
    simp only [lam, map_add, map_neg]
    abel
  obtain ⟨u, hu⟩ := (cls_eq_zero_iff hLO).1 hz
  obtain ⟨y, hy⟩ := GlobalTheory.PrimitiveOverField.exists_point_translate hLaws K P _ hO ⟨u, hu⟩
  have hyc := (cls_eq_iff hO (LB.isLB_linComb P.isLB _ _)).2 hy
  rw [hOc, cls_linComb P.isLB] at hyc
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul,
    pull_id] at hyc
  have hd : pull e.inv.left (cls P'.L P'.isLB) =
      pull (toUnit P.A ≫ y * 𝟙 P.A).left (cls P.L P.isLB) := add_right_cancel hyc
  have hc' : cls P'.L P'.isLB = pull (e.hom ≫ (toUnit P.A ≫ y * 𝟙 P.A)).left (cls P.L P.isLB) := by
    rw [Over.comp_left, pull_comp, ← hd, ← pull_comp, ← Over.comp_left, e.hom_inv_id, Over.id_left,
      pull_id]
  refine ⟨y, ?_, (cls_eq_iff P'.isLB (pull_isLB P.isLB _)).1 (by rw [cls_pull P.isLB]; exact hc')⟩
  have hTh : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := GlobalTheory.Moduli.cube_of_isLB _ P P.L P.isLB
  have hsymA := pull_inv_cls P.isLB P.sym
  have hsymA' := pull_inv_cls P'.isLB P'.sym
  have hdι : pull (GrpObj.inv : P.A ⟶ P.A).left (pull e.inv.left (cls P'.L P'.isLB)) =
      pull e.inv.left (cls P'.L P'.isLB) := by
    rw [← pull_comp, ← Over.comp_left, GrpObj.inv_hom, Over.comp_left, pull_comp, hsymA']
  rw [hd] at hdι
  have hlc := GlobalTheory.PrimitiveOverField.lam_const (B := P.A) (cls P.L P.isLB) y (𝟙 P.A)
  rw [Over.id_left, pull_id] at hlc
  have hpa : pull (GrpObj.inv : P.A ⟶ P.A).left (lam (cls P.L P.isLB) (toUnit P.A ≫ y) (𝟙 P.A)) =
      lam (cls P.L P.isLB) (toUnit P.A ≫ y) (𝟙 P.A) := by
    rw [hlc, map_sub, hdι, hsymA]
  rw [pull_lam, ← Category.assoc, toUnit_unique (GrpObj.inv ≫ toUnit P.A) (toUnit P.A),
    Category.comp_id] at hpa
  have hneg : lam (cls P.L P.isLB) (toUnit P.A ≫ y) GrpObj.inv =
      -lam (cls P.L P.isLB) (toUnit P.A ≫ y) (𝟙 P.A) := by
    rw [lam_comm, lam_comm _ _ (𝟙 P.A), eq_neg_iff_add_eq_zero, ← lam_mul_left P.isLB hTh,
      GrpObj.inv_eq_inv, inv_mul_cancel, lam_one_left]
  have h2a : lam (cls P.L P.isLB) (toUnit P.A ≫ y ^ 2) (𝟙 P.A) = 0 := by
    rw [MonObj.comp_pow, lam_pow_left P.isLB hTh, two_nsmul]
    nth_rewrite 1 [← hpa]
    rw [hneg, neg_add_cancel]
  exact GlobalTheory.PrimitiveOverField.eq_one_of_lam_eq_zero P.isLB P.ktriv _ h2a

end GlobalTheory.SameLam
