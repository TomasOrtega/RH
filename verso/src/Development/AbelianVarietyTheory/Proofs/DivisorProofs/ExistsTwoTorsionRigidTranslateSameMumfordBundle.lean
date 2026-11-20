import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullEqZeroOfChart
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SymPrincipalTranslate
open GlobalTheory.CechPic

/- English proof (translation)
Take `⟨L, hL, rfl⟩` from `cls_surj c`. Establish `hc : f.base (IsLocalRing.closedPoint R) ∈ (⨆ i, L.U i : X.Opens)` using `by rw [hL.cover]; trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 hc`. Conclude with `GlobalTheory.KTrivOfLam.pull_eq_zero_of_chart hL f i fun y => ((IsLocalRing.specializes_closedPoint y).map f.continuous).mem_open (L.U i).isOpen hi`.
-/
theorem pull_local_eq_zero {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (f : Sp R ⟶ X) (c : Pic X) :
    pull f c = 0 := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have hc : f.base (IsLocalRing.closedPoint R) ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
  exact GlobalTheory.KTrivOfLam.pull_eq_zero_of_chart hL f i fun y =>
    ((IsLocalRing.specializes_closedPoint y).map f.continuous).mem_open (L.U i).isOpen hi

/- English proof (translation)
Rewrite using `[show cls (abelian₂ G (LB.div L M)) h = _ from cls_linComb (LB.isLB_div hL hM) _ _ h, show cls (abelian₂ G L) h₁ = _ from cls_linComb hL _ _ h₁, show cls (abelian₂ G M) h₂ = _ from cls_linComb hM _ _ h₂, cls_div hL hM, ← Finset.sum_sub_distrib]`. Simplify using `only [map_sub, smul_sub]`.
-/
theorem cls_lam_div {S : Scheme.{0}} {G : Over S} [GrpObj G] {L M : LB G.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : (abelian₂ G (LB.div L M)).IsLB) (h₁ : (abelian₂ G L).IsLB) (h₂ : (abelian₂ G M).IsLB) :
    cls _ h = cls _ h₁ - cls _ h₂ := by
  rw [show cls (abelian₂ G (LB.div L M)) h = _ from cls_linComb (LB.isLB_div hL hM) _ _ h,
    show cls (abelian₂ G L) h₁ = _ from cls_linComb hL _ _ h₁, show cls (abelian₂ G M) h₂ = _ from cls_linComb hM _ _ h₂,
    cls_div hL hM, ← Finset.sum_sub_distrib]
  simp only [map_sub, smul_sub]

/- English proof (translation)
Introduce `R _ _ _ P L' hL' _ hsym hlam`. Use `P.isAb.comm` as an intermediate fact. Establish `hO : (LB.div L' P.L).IsLB` using `LB.isLB_div hL' P.isLB`. Establish `hΛ' : (abelian₂ P.A L').IsLB` using `LB.isLB_linComb hL' _ _`. Establish `hΛ : (abelian₂ P.A P.L).IsLB` using `LB.isLB_linComb P.isLB _ _`.

Establish `hΛO : (abelian₂ P.A (LB.div L' P.L)).IsLB` using `LB.isLB_linComb hO _ _`. Establish `hu : ∃ u : LB.Gen (abelian₂ P.A (LB.div L' P.L)), u.IsGen`. Use `(cls_eq_zero_iff hΛO).1 ?_` and prove the remaining obligations. Rewrite using `[cls_lam_div hL' P.isLB hΛO hΛ' hΛ, sub_eq_zero]`. Conclude with `(cls_eq_iff hΛ' hΛ).2 hlam`.

Take `⟨x, hx⟩` from `GlobalTheory.LN.ega_holds.2.2.2 R P _ hO hu`. Set `τ : P.A ⟶ P.A` to `(toUnit P.A ≫ x) * 𝟙 P.A`. Establish `hτ : cls L' hL' = pull τ.left (cls P.L P.isLB)`. Establish `h1` using `(cls_eq_iff hO (LB.isLB_linComb P.isLB _ _)).2 hx`. Rewrite `h1` using `[cls_div hL' P.isLB hO, cls_linComb P.isLB]`.

Simplify using `only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul, neg_smul, pull_id] at h1`. Conclude with `sub_left_injective (h1.trans (sub_eq_add_neg _ _).symm)`. Establish `hR : (GlobalTheory.RigidTranslate.rigTransl P.L x).IsLB` using `LB.isLB_linComb P.isLB _ _`. Establish `hcR : cls _ hR = pull τ.left (cls P.L P.isLB)`. Establish `e : GlobalTheory.PolTranslate.transl x = τ` using `by rw [GlobalTheory.PolTranslate.transl, _root_.mul_comm]`.

Use `(cls_linComb P.isLB _ _ hR).trans ?_` and prove the remaining obligations. Simplify using `only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul, neg_smul]`. Rewrite using `[Over.comp_left, pull_comp, pull_local_eq_zero (R := R) x.left, map_zero, neg_zero, add_zero, e]`. Use `⟨x, ?_, (cls_eq_iff hL' hR).1 (hτ.trans hcR.symm)⟩` and prove the remaining obligations. Establish `hs : pull (GrpObj.inv : P.A ⟶ P.A).left (cls P.L P.isLB) = cls P.L P.isLB` using `GlobalTheory.RigSymSubring.cls_of_sym P.isLB P.sym`.

Establish `hs' : pull (GrpObj.inv : P.A ⟶ P.A).left (cls L' hL') = cls L' hL'` using `GlobalTheory.RigSymSubring.cls_of_sym hL' hsym`. Set `τ' : P.A ⟶ P.A` to `(toUnit P.A ≫ x⁻¹) * 𝟙 P.A`. Establish `e1 : (GrpObj.inv : P.A ⟶ P.A) ≫ τ = τ' ≫ GrpObj.inv`. Rewrite using `[← Hom.inv_def, MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, mul_inv, ← GrpObj.comp_inv, inv_inv, Hom.inv_def, Category.id_comp]`. Establish `e2 : τ ≫ τ' = 𝟙 P.A`.

Rewrite using `[MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, ← _root_.mul_assoc, ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, _root_.one_mul]`. Establish `e3 : τ ≫ τ = (toUnit P.A ≫ (x * x)) * 𝟙 P.A`. Rewrite using `[MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, ← _root_.mul_assoc, ← MonObj.comp_mul]`. Establish `h2 : pull ((toUnit P.A ≫ (x * x)) * 𝟙 P.A).left (cls P.L P.isLB) = cls P.L P.isLB`. Establish `k : pull τ'.left (cls P.L P.isLB) = pull τ.left (cls P.L P.isLB)`.

Use `hs'` as an intermediate fact. Rewrite `this` using `[hτ, ← pull_comp, ← Over.comp_left, e1, Over.comp_left, pull_comp, hs]`. Conclude with `this`. Establish `k2` using `congrArg (pull τ.left) k`. Rewrite `k2` using `[← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, e2, e3, Over.id_left, pull_id]`.

Conclude with `k2.symm`. Use `(P.ktriv R (𝟙 (Sp R)) (x * x) fun p => ⟨⊤, trivial, ?_⟩).trans Hom.one_def.symm` and prove the remaining obligations. Set `T : Over (Sp R)` to `Over.mk (𝟙 (Sp R))`. Establish `hTD : (translDiff P.A P.L (x * x)).IsLB` using `LB.isLB_linComb P.isLB _ _`. Use `(cls_eq_zero_iff (pull_isLB hTD _)).1 ?_` and prove the remaining obligations.

Rewrite using `[cls_pull hTD]`. It suffices to establish `h0 : cls _ hTD = 0 by rw [h0, map_zero]`. Establish `e₁ : cls _ hTD = pull (lift (fst T P.A ≫ (x * x)) (snd T P.A) ≫ μ[P.A]).left (cls P.L P.isLB) - pull (snd T P.A).left (cls P.L P.isLB)`. Use `(cls_linComb P.isLB _ _ hTD).trans ?_` and prove the remaining obligations. Simplify using `only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul, neg_smul]`.

Conclude with `(sub_eq_add_neg _ _).symm`. Establish `e₂ : lift (fst T P.A ≫ (x * x)) (snd T P.A) ≫ μ[P.A] = snd T P.A ≫ ((toUnit P.A ≫ (x * x)) * 𝟙 P.A)` using `by show (fst T P.A ≫ (x * x)) * snd T P.A = _`. Rewrite using `[MonObj.comp_mul (snd T P.A), ← Category.assoc (snd T P.A), comp_toUnit, Category.comp_id]`. Use `congr 1`. Rewrite using `[e₁, e₂, Over.comp_left, pull_comp, h2, sub_self]`.
-/
theorem exists_two_torsion_rigTransl : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) (L' : LB P.A.left), L'.IsLB → Rigidified P.A L' → Sym P.A L' → LBIso (abelian₂ P.A L') (abelian₂ P.A P.L) → ∃ x : 𝟙_ (Over (Sp R)) ⟶ P.A, x * x = 1 ∧ LBIso L' (GlobalTheory.RigidTranslate.rigTransl P.L x) := by
  intro R _ _ _ P L' hL' _ hsym hlam
  have := P.isAb.comm
  have hO : (LB.div L' P.L).IsLB := LB.isLB_div hL' P.isLB
  have hΛ' : (abelian₂ P.A L').IsLB := LB.isLB_linComb hL' _ _
  have hΛ : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  have hΛO : (abelian₂ P.A (LB.div L' P.L)).IsLB := LB.isLB_linComb hO _ _
  have hu : ∃ u : LB.Gen (abelian₂ P.A (LB.div L' P.L)), u.IsGen := by
    refine (cls_eq_zero_iff hΛO).1 ?_
    rw [cls_lam_div hL' P.isLB hΛO hΛ' hΛ, sub_eq_zero]
    exact (cls_eq_iff hΛ' hΛ).2 hlam
  obtain ⟨x, hx⟩ := GlobalTheory.LN.ega_holds.2.2.2 R P _ hO hu
  let τ : P.A ⟶ P.A := (toUnit P.A ≫ x) * 𝟙 P.A

  have hτ : cls L' hL' = pull τ.left (cls P.L P.isLB) := by
    have h1 := (cls_eq_iff hO (LB.isLB_linComb P.isLB _ _)).2 hx
    rw [cls_div hL' P.isLB hO, cls_linComb P.isLB] at h1
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul,
      neg_smul, pull_id] at h1
    exact sub_left_injective (h1.trans (sub_eq_add_neg _ _).symm)

  have hR : (GlobalTheory.RigidTranslate.rigTransl P.L x).IsLB := LB.isLB_linComb P.isLB _ _
  have hcR : cls _ hR = pull τ.left (cls P.L P.isLB) := by
    have e : GlobalTheory.PolTranslate.transl x = τ := by rw [GlobalTheory.PolTranslate.transl, _root_.mul_comm]
    refine (cls_linComb P.isLB _ _ hR).trans ?_
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul,
      neg_smul]
    rw [Over.comp_left, pull_comp, pull_local_eq_zero (R := R) x.left, map_zero, neg_zero, add_zero, e]
  refine ⟨x, ?_, (cls_eq_iff hL' hR).1 (hτ.trans hcR.symm)⟩

  have hs : pull (GrpObj.inv : P.A ⟶ P.A).left (cls P.L P.isLB) = cls P.L P.isLB :=
    GlobalTheory.RigSymSubring.cls_of_sym P.isLB P.sym
  have hs' : pull (GrpObj.inv : P.A ⟶ P.A).left (cls L' hL') = cls L' hL' :=
    GlobalTheory.RigSymSubring.cls_of_sym hL' hsym
  let τ' : P.A ⟶ P.A := (toUnit P.A ≫ x⁻¹) * 𝟙 P.A
  have e1 : (GrpObj.inv : P.A ⟶ P.A) ≫ τ = τ' ≫ GrpObj.inv := by
    rw [← Hom.inv_def, MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, mul_inv,
      ← GrpObj.comp_inv, inv_inv, Hom.inv_def, Category.id_comp]
  have e2 : τ ≫ τ' = 𝟙 P.A := by
    rw [MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, ← _root_.mul_assoc,
      ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, _root_.one_mul]
  have e3 : τ ≫ τ = (toUnit P.A ≫ (x * x)) * 𝟙 P.A := by
    rw [MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, ← _root_.mul_assoc,
      ← MonObj.comp_mul]
  have h2 : pull ((toUnit P.A ≫ (x * x)) * 𝟙 P.A).left (cls P.L P.isLB) = cls P.L P.isLB := by
    have k : pull τ'.left (cls P.L P.isLB) = pull τ.left (cls P.L P.isLB) := by
      have := hs'
      rw [hτ, ← pull_comp, ← Over.comp_left, e1, Over.comp_left, pull_comp, hs] at this
      exact this
    have k2 := congrArg (pull τ.left) k
    rw [← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, e2, e3, Over.id_left, pull_id] at k2
    exact k2.symm

  refine (P.ktriv R (𝟙 (Sp R)) (x * x) fun p => ⟨⊤, trivial, ?_⟩).trans Hom.one_def.symm
  let T : Over (Sp R) := Over.mk (𝟙 (Sp R))
  have hTD : (translDiff P.A P.L (x * x)).IsLB := LB.isLB_linComb P.isLB _ _
  refine (cls_eq_zero_iff (pull_isLB hTD _)).1 ?_
  rw [cls_pull hTD]
  suffices h0 : cls _ hTD = 0 by rw [h0, map_zero]
  have e₁ : cls _ hTD = pull (lift (fst T P.A ≫ (x * x)) (snd T P.A) ≫ μ[P.A]).left (cls P.L P.isLB) -
      pull (snd T P.A).left (cls P.L P.isLB) := by
    refine (cls_linComb P.isLB _ _ hTD).trans ?_
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul,
      neg_smul]
    exact (sub_eq_add_neg _ _).symm
  have e₂ : lift (fst T P.A ≫ (x * x)) (snd T P.A) ≫ μ[P.A] = snd T P.A ≫ ((toUnit P.A ≫ (x * x)) * 𝟙 P.A) := by
    show (fst T P.A ≫ (x * x)) * snd T P.A = _
    rw [MonObj.comp_mul (snd T P.A), ← Category.assoc (snd T P.A), comp_toUnit, Category.comp_id]
    congr 1
  rw [e₁, e₂, Over.comp_left, pull_comp, h2, sub_self]
end GlobalTheory.SymPrincipalTranslate
