import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.InBlock
import Formalism.LocalToGlobal.IndefiniteReal.CxPassRep

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

namespace PassRep3

open Formalism.IndefR.CxPass.PassRep

section Lev

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (I : In3 K G Pl0 I0 Ty T m)

/- English proof (translation)
Establish `hS` using `fun n (W : Submodule K (Fin n → K)) => Formalism.L2.DIV.subspace_image_spec K n W`. Take `⟨-, hmul⟩` from `Formalism.L2.DIV.group_action_matrix_hom K B.S G B.r`. Establish `hbot : lvlIdem (⊥ : Subgroup G) (1 : (⊥ : Subgroup G) →* Kˣ) = 1` using `Formalism.L2.DIV.level_idempotent_bot K G 1`. Establish `hu : B.zE ⟨Xs, P, ψ⟩ Z *ᵥ x ∈ B.Z0 ⟨Xs, P, ψ⟩ Z`. Rewrite using `[← (hS _ (B.Z0 ⟨Xs, P, ψ⟩ Z)).2]`.

Conclude with `⟨x, rfl⟩`. Establish `hw : B.vE ⟨Xs, P, ψ⟩ *ᵥ (B.zE ⟨Xs, P, ψ⟩ Z *ᵥ x) ∈ B.coord Z` using `hu`. Establish `hr1 : B.vE ⟨Xs, P, ψ⟩ *ᵥ (B.zE ⟨Xs, P, ψ⟩ Z *ᵥ x) ∈ LinearMap.range (B.S.gaMat B.r (idemOf Xs)).mulVecLin`. Establish `h0 : B.vE ⟨Xs, P, ψ⟩ *ᵥ (B.zE ⟨Xs, P, ψ⟩ Z *ᵥ x) ∈ LinearMap.range (B.S.gaMat B.r (goodAt Xs P ψ)).mulVecLin`. Rewrite using `[← (hS _ (LinearMap.range (B.S.gaMat B.r (goodAt Xs P ψ)).mulVecLin)).2]`.

Conclude with `⟨_, rfl⟩`. Take `⟨v, hv⟩` from `h0`. Use `⟨B.S.gaMat B.r (lvlIdem P ψ) *ᵥ v, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.mulVecLin_apply] at hv ⊢`. Rewrite using `[Matrix.mulVec_mulVec, ← hmul]`.

Conclude with `hv`. Choose the witnesses or unpack the hypotheses as in `⟨u1, hu1⟩ : ∃ u1, B.vE ⟨Xs, ⊥, 1⟩ *ᵥ u1 = B.vE ⟨Xs, P, ψ⟩ *ᵥ (B.zE ⟨Xs, P, ψ⟩ Z *ᵥ x) := by`. Establish `e : B.S.gaMat B.r (goodAt Xs ⊥ 1) = B.S.gaMat B.r (idemOf Xs)` using `by rw [goodAt, hbot, mul_one]`. Establish `h1 : B.vE ⟨Xs, P, ψ⟩ *ᵥ (B.zE ⟨Xs, P, ψ⟩ Z *ᵥ x) ∈ LinearMap.range (B.S.gaMat B.r (goodAt Xs ⊥ 1)).mulVecLin`. Rewrite using `[e]`.

Conclude with `hr1`. Rewrite `h1` using `[← (hS _ (LinearMap.range (B.S.gaMat B.r (goodAt Xs ⊥ 1)).mulVecLin)).2]`. Take `⟨u1, hu1⟩` from `h1`. Conclude with `⟨u1, hu1⟩`. Establish `hu1Z : u1 ∈ B.Z0 ⟨Xs, ⊥, 1⟩ Z` using `by show B.vE ⟨Xs, ⊥, 1⟩ *ᵥ u1 ∈ B.coord Z`.

Rewrite using `[hu1]`. Conclude with `hw`. Rewrite `hu1Z` using `[← (hS _ (B.Z0 ⟨Xs, ⊥, 1⟩ Z)).2]`. Take `⟨y, hy⟩` from `hu1Z`. Use `⟨y, ?_⟩` and prove the remaining obligations.

Establish `hy' : B.zE ⟨Xs, ⊥, 1⟩ Z *ᵥ y = u1` using `hy`. Establish `hin : B.vE ⟨Xs, ⊥, 1⟩ *ᵥ (B.zE ⟨Xs, ⊥, 1⟩ Z *ᵥ y) = B.vE ⟨Xs, P, ψ⟩ *ᵥ (B.zE ⟨Xs, P, ψ⟩ Z *ᵥ x)`. Rewrite using `[hy', hu1]`. Rewrite using `[BlockDat.toF_apply, BlockDat.toF_apply, hin]`.
-/
private lemma exists_toF_bot_eq_toF (B : BlockDat K G Pl0) (Xs : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ)
    (Z : Submodule K B.S.Forms) (x : Fin (B.dZ ⟨Xs, P, ψ⟩ Z) → K) :
    ∃ y : Fin (B.dZ ⟨Xs, ⊥, 1⟩ Z) → K, B.toF ⟨Xs, ⊥, 1⟩ Z y = B.toF ⟨Xs, P, ψ⟩ Z x := by
  classical
  have hS := fun n (W : Submodule K (Fin n → K)) => Formalism.L2.DIV.subspace_image_spec K n W
  obtain ⟨-, hmul⟩ := Formalism.L2.DIV.group_action_matrix_hom K B.S G B.r
  have hbot : lvlIdem (⊥ : Subgroup G) (1 : (⊥ : Subgroup G) →* Kˣ) = 1 := Formalism.L2.DIV.level_idempotent_bot K G 1
  have hu : B.zE ⟨Xs, P, ψ⟩ Z *ᵥ x ∈ B.Z0 ⟨Xs, P, ψ⟩ Z := by
    rw [← (hS _ (B.Z0 ⟨Xs, P, ψ⟩ Z)).2]
    exact ⟨x, rfl⟩
  have hw : B.vE ⟨Xs, P, ψ⟩ *ᵥ (B.zE ⟨Xs, P, ψ⟩ Z *ᵥ x) ∈ B.coord Z := hu
  have hr1 : B.vE ⟨Xs, P, ψ⟩ *ᵥ (B.zE ⟨Xs, P, ψ⟩ Z *ᵥ x) ∈
      LinearMap.range (B.S.gaMat B.r (idemOf Xs)).mulVecLin := by
    have h0 : B.vE ⟨Xs, P, ψ⟩ *ᵥ (B.zE ⟨Xs, P, ψ⟩ Z *ᵥ x) ∈
        LinearMap.range (B.S.gaMat B.r (goodAt Xs P ψ)).mulVecLin := by
      rw [← (hS _ (LinearMap.range (B.S.gaMat B.r (goodAt Xs P ψ)).mulVecLin)).2]
      exact ⟨_, rfl⟩
    obtain ⟨v, hv⟩ := h0
    refine ⟨B.S.gaMat B.r (lvlIdem P ψ) *ᵥ v, ?_⟩
    simp only [Matrix.mulVecLin_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, ← hmul]
    exact hv
  obtain ⟨u1, hu1⟩ : ∃ u1, B.vE ⟨Xs, ⊥, 1⟩ *ᵥ u1 = B.vE ⟨Xs, P, ψ⟩ *ᵥ (B.zE ⟨Xs, P, ψ⟩ Z *ᵥ x) := by
    have e : B.S.gaMat B.r (goodAt Xs ⊥ 1) = B.S.gaMat B.r (idemOf Xs) := by rw [goodAt, hbot, mul_one]
    have h1 : B.vE ⟨Xs, P, ψ⟩ *ᵥ (B.zE ⟨Xs, P, ψ⟩ Z *ᵥ x) ∈
        LinearMap.range (B.S.gaMat B.r (goodAt Xs ⊥ 1)).mulVecLin := by
      rw [e]
      exact hr1
    rw [← (hS _ (LinearMap.range (B.S.gaMat B.r (goodAt Xs ⊥ 1)).mulVecLin)).2] at h1
    obtain ⟨u1, hu1⟩ := h1
    exact ⟨u1, hu1⟩
  have hu1Z : u1 ∈ B.Z0 ⟨Xs, ⊥, 1⟩ Z := by
    show B.vE ⟨Xs, ⊥, 1⟩ *ᵥ u1 ∈ B.coord Z
    rw [hu1]
    exact hw
  rw [← (hS _ (B.Z0 ⟨Xs, ⊥, 1⟩ Z)).2] at hu1Z
  obtain ⟨y, hy⟩ := hu1Z
  refine ⟨y, ?_⟩
  have hy' : B.zE ⟨Xs, ⊥, 1⟩ Z *ᵥ y = u1 := hy
  have hin : B.vE ⟨Xs, ⊥, 1⟩ *ᵥ (B.zE ⟨Xs, ⊥, 1⟩ Z *ᵥ y) =
      B.vE ⟨Xs, P, ψ⟩ *ᵥ (B.zE ⟨Xs, P, ψ⟩ Z *ᵥ x) := by
    rw [hy', hu1]
  rw [BlockDat.toF_apply, BlockDat.toF_apply, hin]

/- English proof (translation)
Consider the cases of `b`. Conclude with `exists_toF_bot_eq_toF (I.A.fam.R t) I.A.fam.X I.P0 I.ψ0 (I.X.zs.Z t) x`. Conclude with `exists_toF_bot_eq_toF (I.A.fam.R t) I.A.fam.X I.P1 I.ψ1 (I.X.zs.Z t) x`.
-/
theorem sub_lvl (b : Bool) (t : I.A3.fam3.base3.Tup)
    (x : Fin ((lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).dQ t) → K) :
    ∃ y, I.cg.toR I.X.zs false t y = I.cr.toR I.X.zs b t x := by
  cases b
  · exact exists_toF_bot_eq_toF (I.A.fam.R t) I.A.fam.X I.P0 I.ψ0 (I.X.zs.Z t) x
  · exact exists_toF_bot_eq_toF (I.A.fam.R t) I.A.fam.X I.P1 I.ψ1 (I.X.zs.Z t) x

/- English proof (translation)
The claim follows from `funext fun i => σ.injective (congrFun h i)`.
-/
private lemma cpt_injective' (σ : K →+* ℂ) {n : ℕ} {x y : Fin n → K} (h : cpt σ x = cpt σ y) : x = y :=
  funext fun i => σ.injective (congrFun h i)

/- English proof (translation)
Establish `hg : ∀ x, ∃ y, I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding y) = I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x)`. Introduce `x`. Take `⟨y, hy⟩` from `PassRep3.sub_lvl I b t x`. Conclude with `⟨y, by rw [CxData.iC_cpt', CxData.iC_cpt', hy]⟩`. Establish `hR` using `PassRep.relK I.A3.fam3.base3.v0.embedding (I.X.iC I.cg false t) (I.X.iC I.cr b t) (h2g.2 t).1 hg`.

Use `⟨hR.2, fun x => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `PassRep3.sub_lvl I b t x`. Establish `h1 : I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding y) = I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding ((I.Jt b t).mulVec x))`. Rewrite using `[show I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding ((I.Jt b t).mulVec x)) = I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x) from hR.2 x, CxData.iC_cpt', CxData.iC_cpt', hy]`. Establish `h2` using `cpt_injective' _ ((h2g.2 t).1 h1)`.

Rewrite using `[← h2, hy]`.
-/
theorem jt_spec (h2g : PrincipalLevelBijectivity I.A3 I.X (P1 := I.P1) (ψ1 := I.ψ1) (Dc := I.Dc) (Sp := I.Sp) (Zsc := I.Zsc)) (b : Bool) (t : I.A3.fam3.base3.Tup) :
    (∀ x, I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding ((I.Jt b t).mulVec x)) =
      I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x)) ∧
    ∀ x, I.cg.toR I.X.zs false t ((I.Jt b t).mulVec x) = I.cr.toR I.X.zs b t x := by
  have hg : ∀ x, ∃ y, I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding y) =
      I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x) := by
    intro x
    obtain ⟨y, hy⟩ := PassRep3.sub_lvl I b t x
    exact ⟨y, by rw [CxData.iC_cpt', CxData.iC_cpt', hy]⟩
  have hR := PassRep.relK I.A3.fam3.base3.v0.embedding (I.X.iC I.cg false t) (I.X.iC I.cr b t) (h2g.2 t).1 hg
  refine ⟨hR.2, fun x => ?_⟩
  obtain ⟨y, hy⟩ := PassRep3.sub_lvl I b t x
  have h1 : I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding y) =
      I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding ((I.Jt b t).mulVec x)) := by
    rw [show I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding ((I.Jt b t).mulVec x)) =
      I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x) from hR.2 x, CxData.iC_cpt', CxData.iC_cpt', hy]
  have h2 := cpt_injective' _ ((h2g.2 t).1 h1)
  rw [← h2, hy]

/- English proof (translation)
Establish `hX` using `H.ok.ok2.irr`. Establish `hZ : ∀ f ∈ I.X.zs.Z I.A3.fam3.base3.μ0, (I.A.fam.R I.A3.fam3.base3.μ0).r g f ∈ I.X.zs.Z I.A3.fam3.base3.μ0` using `fun f hf => H.stable.1 _ (Sum.inr g) (Submodule.mem_map_of_mem hf)`. Conclude with `PassRep.toF_act (I.A.fam.R I.A3.fam3.base3.μ0) I.A.fam.X hX (I.X.zs.Z I.A3.fam3.base3.μ0) g hZ x`.
-/
theorem rho_y {s : ℕ} (H : I.Hyp s) (g : G) (x : Fin I.Sg.D → K) :
    ∃ y : Fin I.Sg.D → K, I.cg.toR I.X.zs false I.A3.fam3.base3.μ0 y =
      (I.A.fam.R I.A3.fam3.base3.μ0).r g (I.cg.toR I.X.zs false I.A3.fam3.base3.μ0 x) := by
  have hX := H.ok.ok2.irr
  have hZ : ∀ f ∈ I.X.zs.Z I.A3.fam3.base3.μ0,
      (I.A.fam.R I.A3.fam3.base3.μ0).r g f ∈ I.X.zs.Z I.A3.fam3.base3.μ0 := fun f hf =>
    H.stable.1 _ (Sum.inr g) (Submodule.mem_map_of_mem hf)
  exact PassRep.toF_act (I.A.fam.R I.A3.fam3.base3.μ0) I.A.fam.X hX (I.X.zs.Z I.A3.fam3.base3.μ0) g hZ x

/- English proof (translation)
Use `show I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding y) = I.gE g (I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x))`. Use `erw [CxData.iC_cpt', CxData.iC_cpt', hy]`. Conclude with `H.gequiv _ g _`.
-/
theorem iCg_of_y {s : ℕ} (H : I.Hyp s) (g : G) (x y : Fin I.Sg.D → K)
    (hy : I.cg.toR I.X.zs false I.A3.fam3.base3.μ0 y =
      (I.A.fam.R I.A3.fam3.base3.μ0).r g (I.cg.toR I.X.zs false I.A3.fam3.base3.μ0 x)) :
    I.iCg (cpt I.A3.fam3.base3.v0.embedding y) = I.gE g (I.iCg (cpt I.A3.fam3.base3.v0.embedding x)) := by
  show I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding y) =
    I.gE g (I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x))
  erw [CxData.iC_cpt', CxData.iC_cpt', hy]
  exact H.gequiv _ g _

/- English proof (translation)
Establish `hg : ∀ x : Fin I.Sg.D → K, ∃ y : Fin I.Sg.D → K, I.iCg (cpt I.A3.fam3.base3.v0.embedding y) = ((I.gE g).comp I.iCg) (cpt I.A3.fam3.base3.v0.embedding x)`. Introduce `x`. Take `⟨y, hy⟩` from `PassRep3.rho_y I H g x`. Conclude with `⟨y, PassRep3.iCg_of_y I H g x y hy⟩`. Conclude with `(PassRep.relK I.A3.fam3.base3.v0.embedding I.iCg ((I.gE g).comp I.iCg) H.h2g.1 hg).2 x`.
-/
theorem rho_spec {s : ℕ} (H : I.Hyp s) (g : G) (x : Fin I.Sg.D → K) :
    I.iCg (cpt I.A3.fam3.base3.v0.embedding ((I.ρf g).mulVec x)) =
      I.gE g (I.iCg (cpt I.A3.fam3.base3.v0.embedding x)) := by
  have hg : ∀ x : Fin I.Sg.D → K, ∃ y : Fin I.Sg.D → K, I.iCg (cpt I.A3.fam3.base3.v0.embedding y) =
      ((I.gE g).comp I.iCg) (cpt I.A3.fam3.base3.v0.embedding x) := by
    intro x
    obtain ⟨y, hy⟩ := PassRep3.rho_y I H g x
    exact ⟨y, PassRep3.iCg_of_y I H g x y hy⟩
  exact (PassRep.relK I.A3.fam3.base3.v0.embedding I.iCg ((I.gE g).comp I.iCg) H.h2g.1 hg).2 x

/- English proof (translation)
Take `⟨y, hy⟩` from `PassRep3.rho_y I H g x`. Establish `hyeq : y = (I.ρf g).mulVec x` using `cpt_injective' _ (H.h2g.1 ((PassRep3.iCg_of_y I H g x y hy).trans (PassRep3.rho_spec I H g x).symm))`. Substitute `hyeq` using the available equality. Establish `key : ∀ v : Fin I.Sg.D → K, cv (I.A.fam.R I.A3.fam3.base3.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) v = (I.A.fam.R I.A3.fam3.base3.μ0).S.basis.equivFun (I.cg.toR I.X.zs false I.A3.fam3.base3.μ0 v)`. Introduce `v`.

Use `show _ = (I.A.fam.R I.A3.fam3.base3.μ0).S.basis.equivFun ((I.A.fam.R I.A3.fam3.base3.μ0).toF ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) v)`. Use `erw [BlockDat.toF_apply, LinearEquiv.apply_symm_apply]`. Both sides reduce to the same expression. Rewrite using `[key, key, hy]`. Use `first`.

Consider the case `exact (LinearMap.toMatrix_mulVec_repr _ _ _ _).symm`. Consider the case `(simp only [Basis.equivFun_apply]; exact (LinearMap.toMatrix_mulVec_repr _ _ _ _).symm)`. Consider the case `(simp only [Basis.equivFun_apply, CSD.actMat]; exact (LinearMap.toMatrix_mulVec_repr _ _ _ _).symm)`.
-/
theorem rho_cv {s : ℕ} (H : I.Hyp s) (g : G) (x : Fin I.Sg.D → K) :
    cv (I.A.fam.R I.A3.fam3.base3.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) ((I.ρf g).mulVec x) =
      ((I.A.fam.R I.A3.fam3.base3.μ0).S.actMat (I.A.fam.R I.A3.fam3.base3.μ0).r g).mulVec
        (cv (I.A.fam.R I.A3.fam3.base3.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) x) := by
  obtain ⟨y, hy⟩ := PassRep3.rho_y I H g x
  have hyeq : y = (I.ρf g).mulVec x :=
    cpt_injective' _ (H.h2g.1 ((PassRep3.iCg_of_y I H g x y hy).trans (PassRep3.rho_spec I H g x).symm))
  subst hyeq
  have key : ∀ v : Fin I.Sg.D → K,
      cv (I.A.fam.R I.A3.fam3.base3.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) v =
      (I.A.fam.R I.A3.fam3.base3.μ0).S.basis.equivFun (I.cg.toR I.X.zs false I.A3.fam3.base3.μ0 v) := by
    intro v
    show _ = (I.A.fam.R I.A3.fam3.base3.μ0).S.basis.equivFun
      ((I.A.fam.R I.A3.fam3.base3.μ0).toF ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) v)
    erw [BlockDat.toF_apply, LinearEquiv.apply_symm_apply]
    rfl
  rw [key, key, hy]
  first
  | exact (LinearMap.toMatrix_mulVec_repr _ _ _ _).symm
  | (simp only [Basis.equivFun_apply]; exact (LinearMap.toMatrix_mulVec_repr _ _ _ _).symm)
  | (simp only [Basis.equivFun_apply, CSD.actMat]; exact (LinearMap.toMatrix_mulVec_repr _ _ _ _).symm)

/- English proof (translation)
Set `cvL : (Fin I.Sg.D → K) →ₗ[K] (Fin (I.A.fam.R I.A3.fam3.base3.μ0).S.dim → K)` to `((I.A.fam.R I.A3.fam3.base3.μ0).vE (⟨I.A.fam.X, ⊥, 1⟩ : Lvl K G)).mulVecLin ∘ₗ ((I.A.fam.R I.A3.fam3.base3.μ0).zE (⟨I.A.fam.X, ⊥, 1⟩ : Lvl K G) (I.X.zs.Z I.A3.fam3.base3.μ0)).mulVecLin`. Establish `hcv : ∀ v : Fin I.Sg.D → K, cv (I.A.fam.R I.A3.fam3.base3.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) v = cvL v` using `fun v => rfl`. Establish `e1 : I.epM P ψ *ᵥ y = ∑ h : P, (((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) • (I.ρf (h : G) *ᵥ y))`. Rewrite using `[← Matrix.toLin'_apply, In3.epM]`. Simplify using `only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, Matrix.toLin'_apply, Finset.smul_sum, smul_smul, map_inv]`.

Use `congr 1`. Apply the tactic sequence `all_goals first | rfl | exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)`. Establish `e2 : (I.A.fam.R I.A3.fam3.base3.μ0).S.gaMat (I.A.fam.R I.A3.fam3.base3.μ0).r (lvlIdem P ψ) *ᵥ cvL y = ∑ h : P, (((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) • ((I.A.fam.R I.A3.fam3.base3.μ0).S.actMat (I.A.fam.R I.A3.fam3.base3.μ0).r (h : G) *ᵥ cvL y))`. Rewrite using `[CSD.gaMat_lvlIdem, ← Matrix.toLin'_apply]`. Simplify using `only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, Matrix.toLin'_apply]`.

Rewrite using `[hcv, hcv, e1, e2, map_sum]`. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, ← hcv, ← hcv, PassRep3.rho_cv I H (h : G) y]`.
-/
theorem cv_epM {s : ℕ} (H : I.Hyp s) (P : Subgroup G) (ψ : P →* Kˣ) (y : Fin I.Sg.D → K) :
    cv (I.A.fam.R I.A3.fam3.base3.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) ((I.epM P ψ).mulVec y) =
      ((I.A.fam.R I.A3.fam3.base3.μ0).S.gaMat (I.A.fam.R I.A3.fam3.base3.μ0).r (lvlIdem P ψ)).mulVec
        (cv (I.A.fam.R I.A3.fam3.base3.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) y) := by
  classical
  let cvL : (Fin I.Sg.D → K) →ₗ[K] (Fin (I.A.fam.R I.A3.fam3.base3.μ0).S.dim → K) :=
    ((I.A.fam.R I.A3.fam3.base3.μ0).vE (⟨I.A.fam.X, ⊥, 1⟩ : Lvl K G)).mulVecLin ∘ₗ ((I.A.fam.R I.A3.fam3.base3.μ0).zE (⟨I.A.fam.X, ⊥, 1⟩ : Lvl K G) (I.X.zs.Z I.A3.fam3.base3.μ0)).mulVecLin
  have hcv : ∀ v : Fin I.Sg.D → K, cv (I.A.fam.R I.A3.fam3.base3.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) v = cvL v := fun v => rfl
  have e1 : I.epM P ψ *ᵥ y = ∑ h : P, (((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) • (I.ρf (h : G) *ᵥ y)) := by
    rw [← Matrix.toLin'_apply, In3.epM]
    simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, Matrix.toLin'_apply,
      Finset.smul_sum, smul_smul, map_inv]
    congr 1
    all_goals first | rfl | exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)
  have e2 : (I.A.fam.R I.A3.fam3.base3.μ0).S.gaMat (I.A.fam.R I.A3.fam3.base3.μ0).r (lvlIdem P ψ) *ᵥ cvL y =
      ∑ h : P, (((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) • ((I.A.fam.R I.A3.fam3.base3.μ0).S.actMat (I.A.fam.R I.A3.fam3.base3.μ0).r (h : G) *ᵥ cvL y)) := by
    rw [CSD.gaMat_lvlIdem, ← Matrix.toLin'_apply]
    simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, Matrix.toLin'_apply]
  rw [hcv, hcv, e1, e2, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_smul, ← hcv, ← hcv, PassRep3.rho_cv I H (h : G) y]

end Lev

end PassRep3

namespace In3

open Formalism.IndefR.CxPass.PassRep Formalism.IndefR.CxPass.PassRep3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (I : In3 K G Pl0 I0 Ty T m)

/- English proof (translation)
Establish `hg : ∀ x : Fin (I.Sb b).D → K, ∃ y : Fin I.Sg.D → K, I.iCg (cpt I.A3.fam3.base3.v0.embedding y) = I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x)`. Introduce `x`. Take `⟨y, hy⟩` from `PassRep3.sub_lvl I b I.A3.fam3.base3.μ0 x`. Use `⟨y, ?_⟩` and prove the remaining obligations. Use `show I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding y) = _`.

Use `erw [CxData.iC_cpt', CxData.iC_cpt', hy]`. Establish `hR` using `PassRep.relK I.A3.fam3.base3.v0.embedding I.iCg (I.X.iC I.cr b I.A3.fam3.base3.μ0) H.h2g.1 hg`. Use `⟨hR.2, fun x y hxy => ?_⟩` and prove the remaining obligations. Establish `h1 : I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x) = I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding y)` using `(hR.2 x).symm.trans ((congrArg (fun v => I.iCg (cpt I.A3.fam3.base3.v0.embedding v)) hxy).trans (hR.2 y))`. Conclude with `PassRep3.cpt_injective' _ ((H.h2 b).1 h1)`.
-/
private theorem iCg_cpt_Jm_mulVec_and_Jm_injective {s : ℕ} (H : I.Hyp s) (b : Bool) :
    (∀ x : Fin (I.Sb b).D → K, I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.Jm b *ᵥ x)) =
      I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x)) ∧ Function.Injective (I.Jm b).mulVec := by
  have hg : ∀ x : Fin (I.Sb b).D → K, ∃ y : Fin I.Sg.D → K, I.iCg (cpt I.A3.fam3.base3.v0.embedding y) =
      I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x) := by
    intro x
    obtain ⟨y, hy⟩ := PassRep3.sub_lvl I b I.A3.fam3.base3.μ0 x
    refine ⟨y, ?_⟩
    show I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding y) = _
    erw [CxData.iC_cpt', CxData.iC_cpt', hy]
  have hR := PassRep.relK I.A3.fam3.base3.v0.embedding I.iCg (I.X.iC I.cr b I.A3.fam3.base3.μ0) H.h2g.1 hg
  refine ⟨hR.2, fun x y hxy => ?_⟩
  have h1 : I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x) =
      I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding y) :=
    (hR.2 x).symm.trans ((congrArg (fun v => I.iCg (cpt I.A3.fam3.base3.v0.embedding v)) hxy).trans (hR.2 y))
  exact PassRep3.cpt_injective' _ ((H.h2 b).1 h1)

/- English proof (translation)
Introduce `s H b t`. Take `⟨h1, h2⟩` from `PassRep3.jt_spec I H.h2g b t`. Use `⟨h1, h2, fun x => ?_⟩` and prove the remaining obligations. Establish `e1 : I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.Jm b *ᵥ (I.X.rowMat I.cr b t *ᵥ x))) = I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x)` using `((iCg_cpt_Jm_mulVec_and_Jm_injective I H b).1 _).trans (PassRep.key_row' I.X I.cr b (fun t => ((H.h2 b).2.1 t).2) (H.ratMu b) t x)`. Establish `e2 : I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.X.rowMat I.cg false t *ᵥ (I.Jt b t *ᵥ x))) = I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x)` using `(PassRep.key_row' I.X I.cg false (fun t => (H.h2g.2 t).2) H.ratMug t _).trans (h1 x)`.

Conclude with `PassRep3.cpt_injective' _ (H.h2g.1 (e1.trans e2.symm))`.
-/
theorem pJt : I.PJt := by
  intro s H b t
  obtain ⟨h1, h2⟩ := PassRep3.jt_spec I H.h2g b t
  refine ⟨h1, h2, fun x => ?_⟩
  have e1 : I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.Jm b *ᵥ (I.X.rowMat I.cr b t *ᵥ x))) =
      I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x) :=
    ((iCg_cpt_Jm_mulVec_and_Jm_injective I H b).1 _).trans (PassRep.key_row' I.X I.cr b (fun t => ((H.h2 b).2.1 t).2) (H.ratMu b) t x)
  have e2 : I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.X.rowMat I.cg false t *ᵥ (I.Jt b t *ᵥ x))) =
      I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x) :=
    (PassRep.key_row' I.X I.cg false (fun t => (H.h2g.2 t).2) H.ratMug t _).trans (h1 x)
  exact PassRep3.cpt_injective' _ (H.h2g.1 (e1.trans e2.symm))

/- English proof (translation)
Introduce `s H`. Establish `hsp` using `fun g x => PassRep3.rho_spec I H g x`. Establish `hinj : ∀ M N : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K, (∀ x, I.iCg (cpt I.A3.fam3.base3.v0.embedding (M *ᵥ x)) = I.iCg (cpt I.A3.fam3.base3.v0.embedding (N *ᵥ x))) → M = N`. Introduce `M N h`. Establish `h' : ∀ x, M *ᵥ x = N *ᵥ x` using `fun x => PassRep3.cpt_injective' _ (H.h2g.1 (h x))`.

Conclude with `Matrix.toLin'.injective (LinearMap.ext h')`. Use `⟨hinj _ _ fun x => ?_, fun g h => hinj _ _ fun x => ?_, hsp⟩` and prove the remaining obligations. Use `erw [hsp, Matrix.one_mulVec, map_one]`. Both sides reduce to the same expression. Use `erw [hsp, ← Matrix.mulVec_mulVec, hsp, hsp, map_mul]`.

Both sides reduce to the same expression.
-/
theorem pRho : I.PRho := by
  intro s H
  have hsp := fun g x => PassRep3.rho_spec I H g x
  have hinj : ∀ M N : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K,
      (∀ x, I.iCg (cpt I.A3.fam3.base3.v0.embedding (M *ᵥ x)) = I.iCg (cpt I.A3.fam3.base3.v0.embedding (N *ᵥ x))) →
      M = N := by
    intro M N h
    have h' : ∀ x, M *ᵥ x = N *ᵥ x := fun x => PassRep3.cpt_injective' _ (H.h2g.1 (h x))
    exact Matrix.toLin'.injective (LinearMap.ext h')
  refine ⟨hinj _ _ fun x => ?_, fun g h => hinj _ _ fun x => ?_, hsp⟩
  · erw [hsp, Matrix.one_mulVec, map_one]
    rfl
  · erw [hsp, ← Matrix.mulVec_mulVec, hsp, hsp, map_mul]
    rfl

/- English proof (translation)
Introduce `s H b`. Conclude with `iCg_cpt_Jm_mulVec_and_Jm_injective I H b`.
-/
theorem pJ : I.PJ := by
  intro s H b
  exact iCg_cpt_Jm_mulVec_and_Jm_injective I H b

/- English proof (translation)
Introduce `s H b`. Establish `hX` using `H.ok.ok2.irr`. Establish `hJt : ∀ x, I.cg.toR I.X.zs false I.A3.fam3.base3.μ0 (I.Jm b *ᵥ x) = I.cr.toR I.X.zs b I.A3.fam3.base3.μ0 x`. Introduce `x`. Take `⟨y, hy⟩` from `PassRep3.sub_lvl I b I.A3.fam3.base3.μ0 x`.

Establish `h1 : I.iCg (cpt I.A3.fam3.base3.v0.embedding y) = I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.Jm b *ᵥ x))`. Rewrite using `[(iCg_cpt_Jm_mulVec_and_Jm_injective I H b).1 x]`. Use `show I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding y) = _`. Use `erw [CxData.iC_cpt', CxData.iC_cpt', hy]`. Establish `h2` using `PassRep3.cpt_injective' _ (H.h2g.1 h1)`.

Rewrite using `[← h2, hy]`. Establish `key : ∀ (ℓ : Lvl K G) (v : Fin ((I.A.fam.R I.A3.fam3.base3.μ0).dZ ℓ (I.X.zs.Z I.A3.fam3.base3.μ0)) → K), cv (I.A.fam.R I.A3.fam3.base3.μ0) ℓ (I.X.zs.Z I.A3.fam3.base3.μ0) v = (I.A.fam.R I.A3.fam3.base3.μ0).S.basis.equivFun ((I.A.fam.R I.A3.fam3.base3.μ0).toF ℓ (I.X.zs.Z I.A3.fam3 …`. Introduce `ℓ v`. Use `erw [BlockDat.toF_apply, LinearEquiv.apply_symm_apply]`. Both sides reduce to the same expression.

Consider the cases of `b`. Use `PassRep.range_eq_block (I.A.fam.R I.A3.fam3.base3.μ0) I.A.fam.X hX I.P0 I.ψ0 (I.X.zs.Z I.A3.fam3.base3.μ0) (I.Jm false) (fun x => ?_) (I.epM I.P0 I.ψ0) (fun y => PassRep3.cv_epM I H I.P0 I.ψ0 y)` and prove the remaining obligations. Rewrite using `[key, key]`. Conclude with `congrArg _ (hJt x)`. Use `PassRep.range_eq_block (I.A.fam.R I.A3.fam3.base3.μ0) I.A.fam.X hX I.P1 I.ψ1 (I.X.zs.Z I.A3.fam3.base3.μ0) (I.Jm true) (fun x => ?_) (I.epM I.P1 I.ψ1) (fun y => PassRep3.cv_epM I H I.P1 I.ψ1 y)` and prove the remaining obligations.

Rewrite using `[key, key]`. Conclude with `congrArg _ (hJt x)`.
-/
theorem pRange : I.PRange := by
  intro s H b
  have hX := H.ok.ok2.irr
  have hJt : ∀ x, I.cg.toR I.X.zs false I.A3.fam3.base3.μ0 (I.Jm b *ᵥ x) =
      I.cr.toR I.X.zs b I.A3.fam3.base3.μ0 x := by
    intro x
    obtain ⟨y, hy⟩ := PassRep3.sub_lvl I b I.A3.fam3.base3.μ0 x
    have h1 : I.iCg (cpt I.A3.fam3.base3.v0.embedding y) = I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.Jm b *ᵥ x)) := by
      rw [(iCg_cpt_Jm_mulVec_and_Jm_injective I H b).1 x]
      show I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding y) = _
      erw [CxData.iC_cpt', CxData.iC_cpt', hy]
    have h2 := PassRep3.cpt_injective' _ (H.h2g.1 h1)
    rw [← h2, hy]
  have key : ∀ (ℓ : Lvl K G) (v : Fin ((I.A.fam.R I.A3.fam3.base3.μ0).dZ ℓ (I.X.zs.Z I.A3.fam3.base3.μ0)) → K),
      cv (I.A.fam.R I.A3.fam3.base3.μ0) ℓ (I.X.zs.Z I.A3.fam3.base3.μ0) v =
        (I.A.fam.R I.A3.fam3.base3.μ0).S.basis.equivFun
          ((I.A.fam.R I.A3.fam3.base3.μ0).toF ℓ (I.X.zs.Z I.A3.fam3.base3.μ0) v) := by
    intro ℓ v
    erw [BlockDat.toF_apply, LinearEquiv.apply_symm_apply]
    rfl
  cases b
  · refine PassRep.range_eq_block (I.A.fam.R I.A3.fam3.base3.μ0) I.A.fam.X hX I.P0 I.ψ0 (I.X.zs.Z I.A3.fam3.base3.μ0) (I.Jm false) (fun x => ?_)
      (I.epM I.P0 I.ψ0) (fun y => PassRep3.cv_epM I H I.P0 I.ψ0 y)
    rw [key, key]
    exact congrArg _ (hJt x)
  · refine PassRep.range_eq_block (I.A.fam.R I.A3.fam3.base3.μ0) I.A.fam.X hX I.P1 I.ψ1 (I.X.zs.Z I.A3.fam3.base3.μ0) (I.Jm true) (fun x => ?_)
      (I.epM I.P1 I.ψ1) (fun y => PassRep3.cv_epM I H I.P1 I.ψ1 y)
    rw [key, key]
    exact congrArg _ (hJt x)

end In3

end Formalism.IndefR.CxPass
