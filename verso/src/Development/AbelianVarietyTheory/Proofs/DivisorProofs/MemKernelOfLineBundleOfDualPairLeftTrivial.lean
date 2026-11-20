import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbDual

/- English proof (translation)
Introduce `K _ _ A B _ _ P L hA _ hD hL T x hx`. Use `haveI := hA.comm`. Establish `hP : (abelian₂ A L).IsLB` using `LB.isLB_linComb hL _ _`. Establish `e : ∀ (Y : Over (Sp K)) (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b` using `fun Y a b ↦ by`. Rewrite using `[evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst, lift_snd]`.

Establish `hadd` using `GlobalTheory.CubeNoeth.isAdditive_of_triv_axes hA hA hP (by rw [triv_ev_iff hP, e, lam_one_left]) (by rw [triv_ev_iff hP, e, lam_one_right])`. Take `⟨φ, hφ, -⟩` from `hD.univ A (abelian₂ A L) hP hadd`. Establish `hc : cls _ hP = evc hD.isLB (fst A A) (snd A A ≫ φ)` using `(cls_eq_iff hP (pull_isLB hD.isLB _)).2 hφ`. Establish `hx0 : lam (cls L hL) (fst T A ≫ x) (snd T A) = 0`. Establish `e₁` using `congrArg (CechPic.pull (lift (fst T A) (snd T A ≫ φ)).left) ((triv_ev_iff hD.isLB _ _).1 hx)`.

Rewrite `e₁` using `[pull_evc, map_zero, lift_fst_assoc, lift_snd]`. Rewrite using `[← e, evc, hc, pull_evc, lift_fst, lift_snd_assoc]`. Conclude with `e₁`. Establish `hD' : (Out.translDiff A L x).IsLB` using `LB.isLB_linComb hL _ _`. Introduce `p`.

Take `⟨V, hV, hc'⟩` from `exists_pull_eq_zero (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) p`. Use `⟨V, hV, (cls_eq_zero_iff (pull_isLB hD' _)).1 ?_⟩` and prove the remaining obligations. Establish `e₁` using `pull_translDiff hL x hD' (fst T A) (snd T A)`. Rewrite `e₁` using `[lift_fst_snd, Over.id_left, pull_id]`. Establish `e₂ : cls _ hD' = CechPic.pull (fst T A).left (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL))`.

Rewrite using `[e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one, ← sub_eq_zero, ← hx0, lam]`. Normalize the expressions using the abelian group laws. Rewrite using `[cls_pull hD', e₂, ← pull_comp]`. Conclude with `pull_eq_zero_of_mem V (((fst T A).left ⁻¹ᵁ V).ι ≫ (fst T A).left) (fun z ↦ z.2) hc'`.
-/
theorem memKL_of_triv_ev_left : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left) (L : LB A.left), IsAbelianScheme A → IsAbelianScheme B → IsDual A B P → L.IsLB →
    ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → GlobalTheory.MemKL A L x := by
  intro K _ _ A B _ _ P L hA _ hD hL T x hx
  haveI := hA.comm
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have e : ∀ (Y : Over (Sp K)) (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b := fun Y a b ↦ by
    rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
      lift_snd]
  have hadd := GlobalTheory.CubeNoeth.isAdditive_of_triv_axes hA hA hP
    (by rw [triv_ev_iff hP, e, lam_one_left]) (by rw [triv_ev_iff hP, e, lam_one_right])
  obtain ⟨φ, hφ, -⟩ := hD.univ A (abelian₂ A L) hP hadd
  have hc : cls _ hP = evc hD.isLB (fst A A) (snd A A ≫ φ) :=
    (cls_eq_iff hP (pull_isLB hD.isLB _)).2 hφ
  have hx0 : lam (cls L hL) (fst T A ≫ x) (snd T A) = 0 := by
    have e₁ := congrArg (CechPic.pull (lift (fst T A) (snd T A ≫ φ)).left) ((triv_ev_iff hD.isLB _ _).1 hx)
    rw [pull_evc, map_zero, lift_fst_assoc, lift_snd] at e₁
    rw [← e, evc, hc, pull_evc, lift_fst, lift_snd_assoc]
    exact e₁
  have hD' : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc'⟩ := exists_pull_eq_zero
    (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD' _)).1 ?_⟩
  have e₁ := pull_translDiff hL x hD' (fst T A) (snd T A)
  rw [lift_fst_snd, Over.id_left, pull_id] at e₁
  have e₂ : cls _ hD' = CechPic.pull (fst T A).left
      (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) := by
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
      ← sub_eq_zero, ← hx0, lam]
    abel
  rw [cls_pull hD', e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T A).left ⁻¹ᵁ V).ι ≫ (fst T A).left) (fun z ↦ z.2) hc'

end GlobalTheory.AbDual
