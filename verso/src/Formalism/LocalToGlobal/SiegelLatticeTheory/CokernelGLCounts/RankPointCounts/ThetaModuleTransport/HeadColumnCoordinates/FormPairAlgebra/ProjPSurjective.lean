import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.BRawHeadColsRight

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

/- English proof (translation)
Express the relevant statement in the definitionally equal form `p.mkQ (∑ a, c a • v a) = ∑ a, c a • p.mkQ (v a)`. Rewrite using `[map_sum]`. Simplify using `only [LinearMap.map_smul]`.
-/
theorem mk_sum_smul (p : Submodule O (Fin (r + 1) → O)) (c : Fin (r + 1) → O)
    (v : Fin (r + 1) → Fin (r + 1) → O) :
    (Submodule.Quotient.mk (∑ a, c a • v a) : (Fin (r + 1) → O) ⧸ p) =
      ∑ a, c a • Submodule.Quotient.mk (v a) := by
  change p.mkQ (∑ a, c a • v a) = ∑ a, c a • p.mkQ (v a)
  rw [map_sum]
  simp only [LinearMap.map_smul]

/- English proof (translation)
Rewrite using `[← bLin_apply, map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul, bLin_apply, Subring.smul_def, smul_eq_mul]`.
-/
theorem bRaw_sum (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (y' : Fin (r + 1) → O)
    (c : Fin (r + 1) → O) (v : Fin (r + 1) → Fin (r + 1) → O) :
    bRaw O cj Z (∑ a, c a • v a) y' = ∑ a, (c a : E) * bRaw O cj Z (v a) y' := by
  rw [← bLin_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [LinearMap.map_smul, bLin_apply, Subring.smul_def, smul_eq_mul]

/- English proof (translation)
Rewrite using `[← bLin_apply, map_sub]`. Both sides reduce to the same expression.
-/
theorem bRaw_sub_left (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (y z y' : Fin (r + 1) → O) :
    bRaw O cj Z (y - z) y' = bRaw O cj Z y y' - bRaw O cj Z z y' := by
  rw [← bLin_apply, map_sub]; rfl

section Adj

variable {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}

def uLift (γ : MbMod Z₁ ≃ₗ[O] MbMod Z₂) (a : Fin (r + 1)) : Fin (r + 1) → O :=
  if a = Fin.last r then Pi.single (Fin.last r) 1
  else Classical.choose (Submodule.Quotient.mk_surjective _
    (γ.symm (Submodule.Quotient.mk (Pi.single a 1) : MbMod Z₂)))

/- English proof (translation)
Simplify using `[uLift]`.
-/
theorem uLift_last (γ : MbMod Z₁ ≃ₗ[O] MbMod Z₂) : uLift O γ (Fin.last r) = Pi.single (Fin.last r) 1 := by
  simp [uLift]

/- English proof (translation)
Unfold `uLift`. Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `he`. Rewrite using `[Classical.choose_spec (Submodule.Quotient.mk_surjective _ (γ.symm (Submodule.Quotient.mk (Pi.single a 1) : MbMod Z₂)))]`.

Conclude with `γ.apply_symm_apply _`.
-/
theorem uLift_spec (γ : MbMod Z₁ ≃ₗ[O] MbMod Z₂) (he : γ (eCl Z₁) = eCl Z₂) (a : Fin (r + 1)) :
    γ (Submodule.Quotient.mk (uLift O γ a)) = (Submodule.Quotient.mk (Pi.single a 1) : MbMod Z₂) := by
  unfold uLift
  split_ifs with h
  · subst h; exact he
  · rw [Classical.choose_spec (Submodule.Quotient.mk_surjective _
      (γ.symm (Submodule.Quotient.mk (Pi.single a 1) : MbMod Z₂)))]
    exact γ.apply_symm_apply _

/- English proof (translation)
Rewrite using `[mk_sum_smul, map_sum]`. Simplify using `only [map_smul, uLift_spec O γ he]`. Rewrite using `[← mk_sum_smul, sum_smul_single]`.
-/
theorem gam_sum (γ : MbMod Z₁ ≃ₗ[O] MbMod Z₂) (he : γ (eCl Z₁) = eCl Z₂) (c : Fin (r + 1) → O) :
    γ (Submodule.Quotient.mk (∑ a, c a • uLift O γ a)) = (Submodule.Quotient.mk c : MbMod Z₂) := by
  rw [mk_sum_smul, map_sum]
  simp only [map_smul, uLift_spec O γ he]
  rw [← mk_sum_smul, sum_smul_single]

def adjW (γ : MbMod Z₁ ≃ₗ[O] MbMod Z₂) (y' : Fin (r + 1) → O) (a : Fin (r + 1)) : E :=
  cj (bRaw O cj Z₁ (uLift O γ a) y')

def adjVal (γ : MbMod Z₁ ≃ₗ[O] MbMod Z₂) (y' : Fin (r + 1) → O) (b : Fin (r + 1)) : E :=
  ∑ a, cj ((Z₂.map O.subtype) a b) * adjW O cj γ y' a

/- English proof (translation)
Establish `hcol : γ (Submodule.Quotient.mk (∑ a, Z₂ a b • uLift O γ a)) = (Submodule.Quotient.mk (fun i => Z₂ i b) : MbMod Z₂)` using `gam_sum O γ he (fun a => Z₂ a b)`. Establish `hcls : ∃ c : O, (Submodule.Quotient.mk (fun i => Z₂ i b) : MbMod Z₂) = c • bCls Z₂`. Distinguish the cases in `hbl : b = Fin.last r`. Substitute `hbl` using the available equality. Conclude with `⟨1, by rw [one_smul]; rfl⟩`.

Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[zero_smul, Submodule.Quotient.mk_eq_zero]`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨b.castPred hbl, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Take `⟨c, hc⟩` from `hcls`. Establish `hmk : (Submodule.Quotient.mk (∑ a, Z₂ a b • uLift O γ a) : MbMod Z₁) = c • bCls Z₁`. Apply `γ.injective` to reduce the goal to its premises. Rewrite using `[hcol, hc, LinearEquiv.map_smul, hb]`. Establish `hmem` using `bRaw_mem_of_mk O cj hO Z₁ hu₁ hmk y'`.

Rewrite `hmem` using `[bRaw_sum]`. Establish `hval : adjVal O cj γ y' b = cj (∑ a, (Z₂ a b : E) * bRaw O cj Z₁ (uLift O γ a) y')`. Simplify using `[adjVal, adjW, map_sum, map_mul, Matrix.map_apply]`. Rewrite using `[hval]`. Conclude with `hO _ hmem`.
-/
theorem adjVal_mem (hO : ∀ x ∈ O, cj x ∈ O) (hu₁ : IsUnit (Z₁.map O.subtype).det)
    (γ : MbMod Z₁ ≃ₗ[O] MbMod Z₂) (hb : γ (bCls Z₁) = bCls Z₂) (he : γ (eCl Z₁) = eCl Z₂)
    (y' : Fin (r + 1) → O) (b : Fin (r + 1)) : adjVal O cj γ y' b ∈ O := by
  have hcol : γ (Submodule.Quotient.mk (∑ a, Z₂ a b • uLift O γ a)) =
      (Submodule.Quotient.mk (fun i => Z₂ i b) : MbMod Z₂) := gam_sum O γ he (fun a => Z₂ a b)
  have hcls : ∃ c : O, (Submodule.Quotient.mk (fun i => Z₂ i b) : MbMod Z₂) = c • bCls Z₂ := by
    by_cases hbl : b = Fin.last r
    · subst hbl
      exact ⟨1, by rw [one_smul]; rfl⟩
    · refine ⟨0, ?_⟩
      rw [zero_smul, Submodule.Quotient.mk_eq_zero]
      apply Submodule.subset_span
      refine ⟨b.castPred hbl, ?_⟩
      simp
  obtain ⟨c, hc⟩ := hcls
  have hmk : (Submodule.Quotient.mk (∑ a, Z₂ a b • uLift O γ a) : MbMod Z₁) = c • bCls Z₁ := by
    apply γ.injective
    rw [hcol, hc, LinearEquiv.map_smul, hb]
  have hmem := bRaw_mem_of_mk O cj hO Z₁ hu₁ hmk y'
  rw [bRaw_sum] at hmem
  have hval : adjVal O cj γ y' b = cj (∑ a, (Z₂ a b : E) * bRaw O cj Z₁ (uLift O γ a) y') := by
    simp [adjVal, adjW, map_sum, map_mul, Matrix.map_apply]
  rw [hval]
  exact hO _ hmem

def adjV (hO : ∀ x ∈ O, cj x ∈ O) (hu₁ : IsUnit (Z₁.map O.subtype).det)
    (γ : MbMod Z₁ ≃ₗ[O] MbMod Z₂) (hb : γ (bCls Z₁) = bCls Z₂) (he : γ (eCl Z₁) = eCl Z₂)
    (y' : Fin (r + 1) → O) : Fin (r + 1) → O :=
  fun b => ⟨adjVal O cj γ y' b, adjVal_mem O cj hO hu₁ γ hb he y' b⟩

variable (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O)
  (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)

include hcj hO hu₁ hu₂

/- English proof (translation)
Rewrite using `[lamS_cjT O cj Z₂ hu₂ _ (adjW O cj γ y') (fun b => rfl), adjW, uLift_last, cj_bRaw_single O cj hcj]`.
-/
theorem lamS_adjV (γ : MbMod Z₁ ≃ₗ[O] MbMod Z₂) (hb : γ (bCls Z₁) = bCls Z₂)
    (he : γ (eCl Z₁) = eCl Z₂) (y' : Fin (r + 1) → O) :
    lamS O cj Z₂ (adjV O cj hO hu₁ γ hb he y') = lamS O cj Z₁ y' := by
  rw [lamS_cjT O cj Z₂ hu₂ _ (adjW O cj γ y') (fun b => rfl), adjW, uLift_last,
    cj_bRaw_single O cj hcj]

/- English proof (translation)
Establish `h1 : bRaw O cj Z₂ y₂ (adjV O cj hO hu₁ γ hb he y') = bRaw O cj Z₁ (∑ a, y₂ a • uLift O γ a) y'`. Rewrite using `[bRaw_cjT O cj hcj Z₂ hu₂ _ _ (adjW O cj γ y') (fun b => rfl), bRaw_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[adjW, hcj, mul_comm]`. Establish `h2 : (Submodule.Quotient.mk (∑ a, y₂ a • uLift O γ a - y) : MbMod Z₁) = (0 : O) • bCls Z₁`.

Rewrite using `[zero_smul, Submodule.Quotient.mk_sub, sub_eq_zero]`. Apply `γ.injective` to reduce the goal to its premises. Rewrite using `[gam_sum O γ he, h]`. Rewrite using `[h1, ← bRaw_sub_left]`. Conclude with `bRaw_mem_of_mk O cj hO Z₁ hu₁ h2 y'`.
-/
theorem bRaw_adjV (γ : MbMod Z₁ ≃ₗ[O] MbMod Z₂) (hb : γ (bCls Z₁) = bCls Z₂)
    (he : γ (eCl Z₁) = eCl Z₂) {y y₂ : Fin (r + 1) → O}
    (h : γ (Submodule.Quotient.mk y) = Submodule.Quotient.mk y₂) (y' : Fin (r + 1) → O) :
    bRaw O cj Z₂ y₂ (adjV O cj hO hu₁ γ hb he y') - bRaw O cj Z₁ y y' ∈ O := by
  have h1 : bRaw O cj Z₂ y₂ (adjV O cj hO hu₁ γ hb he y') =
      bRaw O cj Z₁ (∑ a, y₂ a • uLift O γ a) y' := by
    rw [bRaw_cjT O cj hcj Z₂ hu₂ _ _ (adjW O cj γ y') (fun b => rfl), bRaw_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [adjW, hcj, mul_comm]
  have h2 : (Submodule.Quotient.mk (∑ a, y₂ a • uLift O γ a - y) : MbMod Z₁) = (0 : O) • bCls Z₁ := by
    rw [zero_smul, Submodule.Quotient.mk_sub, sub_eq_zero]
    apply γ.injective
    rw [gam_sum O γ he, h]
  rw [h1, ← bRaw_sub_left]
  exact bRaw_mem_of_mk O cj hO Z₁ hu₁ h2 y'

/- English proof (translation)
Establish `hsum : Z.mulVec w = ∑ a : Fin k, w a.castSucc • (fun i => Z i a.castSucc)`. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hw, mul_zero, add_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun a _ => mul_comm _ _`. Rewrite using `[hsum]`.

Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`.
-/
private theorem mulVec_mem_headCols_of_last_eq_zero {R : Type} [CommRing R] {k : ℕ}
    (Z : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (w : Fin (k + 1) → R) (hw : w (Fin.last k) = 0) :
    Z.mulVec w ∈ headCols Z := by
  have hsum : Z.mulVec w = ∑ a : Fin k, w a.castSucc • (fun i => Z i a.castSucc) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hw, mul_zero, add_zero,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  rw [hsum]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/- English proof (translation)
Establish `hw : ∀ a, adjW O cj γ y' a ∈ O` using `fun a => hO _ (bRaw_headCols_right O cj hcj hO Z₁ hu₁ _ hy)`. Set `w : Fin (r + 1) → O` to `fun a => ⟨adjW O cj γ y' a, hw a⟩`. Establish `hlast : w (Fin.last r) = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show adjW O cj γ y' (Fin.last r) = 0`.

Rewrite using `[adjW, uLift_last, cj_bRaw_single O cj hcj, lamS_headCols O cj hO Z₁ hu₁ hy]`. Establish `heq : adjV O cj hO hu₁ γ hb he y' = (cjT O cj hO Z₂).mulVec w`. Use function extensionality and compare the values at `b`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[cjT_mulVec_coe]`.

Both sides reduce to the same expression. Rewrite using `[heq]`. Conclude with `mulVec_mem_headCols_of_last_eq_zero (O := O) (cj := cj) (hcj := hcj) (hO := hO) (hu₁ := hu₁) (hu₂ := hu₂) (Z := cjT O cj hO Z₂) (w := w) (hw := hlast)`.
-/
theorem adjV_headCols (γ : MbMod Z₁ ≃ₗ[O] MbMod Z₂) (hb : γ (bCls Z₁) = bCls Z₂)
    (he : γ (eCl Z₁) = eCl Z₂) {y' : Fin (r + 1) → O} (hy : y' ∈ headCols (cjT O cj hO Z₁)) :
    adjV O cj hO hu₁ γ hb he y' ∈ headCols (cjT O cj hO Z₂) := by
  have hw : ∀ a, adjW O cj γ y' a ∈ O := fun a => hO _ (bRaw_headCols_right O cj hcj hO Z₁ hu₁ _ hy)
  let w : Fin (r + 1) → O := fun a => ⟨adjW O cj γ y' a, hw a⟩
  have hlast : w (Fin.last r) = 0 := by
    apply Subtype.ext
    show adjW O cj γ y' (Fin.last r) = 0
    rw [adjW, uLift_last, cj_bRaw_single O cj hcj, lamS_headCols O cj hO Z₁ hu₁ hy]
  have heq : adjV O cj hO hu₁ γ hb he y' = (cjT O cj hO Z₂).mulVec w := by
    funext b
    apply Subtype.ext
    rw [cjT_mulVec_coe]
    rfl
  rw [heq]
  exact mulVec_mem_headCols_of_last_eq_zero (O := O) (cj := cj) (hcj := hcj) (hO := hO) (hu₁ := hu₁) (hu₂ := hu₂)
    (Z := cjT O cj hO Z₂) (w := w) (hw := hlast)

def adjL (γ : MbMod Z₁ ≃ₗ[O] MbMod Z₂) (hb : γ (bCls Z₁) = bCls Z₂) (he : γ (eCl Z₁) = eCl Z₂) :
    (Fin (r + 1) → O) →ₗ[O] (Fin (r + 1) → O) where
  toFun := adjV O cj hO hu₁ γ hb he
  map_add' y' z' := by
    funext b
    apply Subtype.ext
    simp [adjV, adjVal, adjW, bRaw_add_right, map_add, mul_add, Finset.sum_add_distrib]
  map_smul' c y' := by
    funext b
    apply Subtype.ext
    simp [adjV, adjVal, adjW, bRaw_smul_right, map_mul, hcj, Finset.mul_sum, mul_left_comm]

def adjQ (γ : MbMod Z₁ ≃ₗ[O] MbMod Z₂) (hb : γ (bCls Z₁) = bCls Z₂) (he : γ (eCl Z₁) = eCl Z₂) :
    MbMod (cjT O cj hO Z₁) →ₗ[O] MbMod (cjT O cj hO Z₂) :=
  (headCols (cjT O cj hO Z₁)).liftQ
    ((headCols (cjT O cj hO Z₂)).mkQ ∘ₗ adjL O cj hcj hO hu₁ γ hb he)
    (fun y' hy => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact adjV_headCols O cj hcj hO hu₁ hu₂ γ hb he hy)

/- English proof (translation)
Use `set x := adjV O cj hO hu₁ γ hb he y' with hx`. Establish `hA1 : ∀ y : Fin (r + 1) → O, bRaw O cj Z₂ y x = bRaw O cj Z₁ (∑ a, y a • uLift O γ a) y'`. Introduce `y`. Rewrite using `[bRaw_cjT O cj hcj Z₂ hu₂ y _ (adjW O cj γ y') (fun b => rfl), bRaw_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[adjW, hcj, mul_comm]`. Establish `hB : ∀ a, (Submodule.Quotient.mk (∑ c, uLift O δ a c • uLift O γ c) : MbMod Z₁) = Submodule.Quotient.mk (Pi.single a 1)`. Introduce `a`. Rewrite using `[← hδ (Submodule.Quotient.mk _), gam_sum O γ he, uLift_spec O δ he' a]`. Establish `hC : ∀ a, ∃ n : Fin (r + 1) → O, (a = Fin.last r → n = 0) ∧ (∑ c, uLift O δ a c • uLift O γ c) = Pi.single a 1 + Z₁.mulVec n`.

Introduce `a`. Distinguish the cases in `ha : a = Fin.last r`. Substitute `ha` using the available equality. Use `⟨0, fun _ => rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_zero, add_zero, uLift_last]`.

Simplify using `[Pi.single_apply, uLift_last]`. Establish `hm : (∑ c, uLift O δ a c • uLift O γ c) - Pi.single a 1 ∈ headCols Z₁`. Rewrite using `[← Submodule.Quotient.eq]`. Conclude with `hB a`. Take `⟨n, -, hn⟩` from `mem_headCols hm`.

Conclude with `⟨n, fun h => absurd h ha, by rw [← hn]; abel⟩`. Use `choose n hn0 hn using hC`. Establish `hE : ∀ b, ∑ a, cj ((Z₁.map O.subtype) a b) * cj (bRaw O cj Z₁ (Pi.single a 1) y') = (y' b : E)`. Introduce `b`. Establish `hinv : (Z₁.map O.subtype)⁻¹ * (Z₁.map O.subtype) = 1` using `Matrix.nonsing_inv_mul _ hu₁`.

Establish `hcol : ∀ a j, ((Z₁.map O.subtype)⁻¹.mulVec fun i => (((Pi.single a (1 : O) : Fin (r + 1) → O) i : O) : E)) j = (Z₁.map O.subtype)⁻¹ j a`. Introduce `a j`. Rewrite using `[Matrix.mulVec, dotProduct, Finset.sum_eq_single a]`. Simplify using the standard rewrite rules. Introduce `i _ hi`.

Simplify using `[Pi.single_apply, hi]`. Simplify using the standard rewrite rules. Establish `hj : ∀ j, ∑ a, cj ((Z₁.map O.subtype) a b) * ((y' j : E) * cj ((Z₁.map O.subtype)⁻¹ j a)) = (y' j : E) * cj (((Z₁.map O.subtype)⁻¹ * (Z₁.map O.subtype)) j b)`. Introduce `j`. Rewrite using `[Matrix.mul_apply, map_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [bRaw, hcol, map_sum, map_mul, hcj]`. Simplify using `only [Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Simplify using `only [hj, hinv, Matrix.one_apply]`. Rewrite using `[Finset.sum_eq_single b]`. Simplify using the standard rewrite rules. Introduce `j _ hj'`.

Simplify using `[hj']`. Simplify using the standard rewrite rules. Set `m : Fin (r + 1) → O` to `fun a => ⟨cj (∑ j, cj (y' j : E) * (n a j : E)), hO _ (O.sum_mem fun j _ => O.mul_mem (hO _ (y' j).2) (n a j).2)⟩`. Establish `hmlast : m (Fin.last r) = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[m, hn0 (Fin.last r) rfl]`. Establish `hdiff : adjV O cj hO hu₂ δ hb' he' x - y' = (cjT O cj hO Z₁).mulVec m`. Use function extensionality and compare the values at `b`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Pi.sub_apply, AddSubgroupClass.coe_sub, cjT_mulVec_coe, ← hE b]`.

Use `show adjVal O cj δ x b - _ = _`. Rewrite using `[adjVal, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[adjW, hA1, hn a, bRaw_add_left, bRaw_mulVec O cj Z₁ hu₁, map_add]`. Simplify using `only [m]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Submodule.Quotient.eq, hdiff]`. Conclude with `mulVec_mem_headCols_of_last_eq_zero (O := O) (cj := cj) (hcj := hcj) (hO := hO) (hu₁ := hu₁) (hu₂ := hu₂) (Z := cjT O cj hO Z₁) (w := m) (hw := hmlast)`.
-/
theorem adjV_comp (γ : MbMod Z₁ ≃ₗ[O] MbMod Z₂) (hb : γ (bCls Z₁) = bCls Z₂)
    (he : γ (eCl Z₁) = eCl Z₂) (δ : MbMod Z₂ ≃ₗ[O] MbMod Z₁) (hb' : δ (bCls Z₂) = bCls Z₁)
    (he' : δ (eCl Z₂) = eCl Z₁) (hδ : ∀ m, δ (γ m) = m) (y' : Fin (r + 1) → O) :
    (Submodule.Quotient.mk (adjV O cj hO hu₂ δ hb' he' (adjV O cj hO hu₁ γ hb he y')) :
      MbMod (cjT O cj hO Z₁)) = Submodule.Quotient.mk y' := by
  set x := adjV O cj hO hu₁ γ hb he y' with hx
  have hA1 : ∀ y : Fin (r + 1) → O, bRaw O cj Z₂ y x = bRaw O cj Z₁ (∑ a, y a • uLift O γ a) y' := by
    intro y
    rw [bRaw_cjT O cj hcj Z₂ hu₂ y _ (adjW O cj γ y') (fun b => rfl), bRaw_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [adjW, hcj, mul_comm]
  have hB : ∀ a, (Submodule.Quotient.mk (∑ c, uLift O δ a c • uLift O γ c) : MbMod Z₁) =
      Submodule.Quotient.mk (Pi.single a 1) := by
    intro a
    rw [← hδ (Submodule.Quotient.mk _), gam_sum O γ he, uLift_spec O δ he' a]
  have hC : ∀ a, ∃ n : Fin (r + 1) → O, (a = Fin.last r → n = 0) ∧
      (∑ c, uLift O δ a c • uLift O γ c) = Pi.single a 1 + Z₁.mulVec n := by
    intro a
    by_cases ha : a = Fin.last r
    · subst ha
      refine ⟨0, fun _ => rfl, ?_⟩
      rw [Matrix.mulVec_zero, add_zero, uLift_last]
      simp [Pi.single_apply, uLift_last]
    · have hm : (∑ c, uLift O δ a c • uLift O γ c) - Pi.single a 1 ∈ headCols Z₁ := by
        rw [← Submodule.Quotient.eq]
        exact hB a
      obtain ⟨n, -, hn⟩ := mem_headCols hm
      exact ⟨n, fun h => absurd h ha, by rw [← hn]; abel⟩
  choose n hn0 hn using hC
  have hE : ∀ b, ∑ a, cj ((Z₁.map O.subtype) a b) * cj (bRaw O cj Z₁ (Pi.single a 1) y') = (y' b : E) := by
    intro b
    have hinv : (Z₁.map O.subtype)⁻¹ * (Z₁.map O.subtype) = 1 :=
      Matrix.nonsing_inv_mul _ hu₁
    have hcol : ∀ a j, ((Z₁.map O.subtype)⁻¹.mulVec fun i => (((Pi.single a (1 : O) : Fin (r + 1) → O) i : O) : E)) j =
        (Z₁.map O.subtype)⁻¹ j a := by
      intro a j
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single a]
      · simp
      · intro i _ hi
        simp [Pi.single_apply, hi]
      · simp
    have hj : ∀ j, ∑ a, cj ((Z₁.map O.subtype) a b) * ((y' j : E) * cj ((Z₁.map O.subtype)⁻¹ j a)) =
        (y' j : E) * cj (((Z₁.map O.subtype)⁻¹ * (Z₁.map O.subtype)) j b) := by
      intro j
      rw [Matrix.mul_apply, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul]
      ring
    simp only [bRaw, hcol, map_sum, map_mul, hcj]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [hj, hinv, Matrix.one_apply]
    rw [Finset.sum_eq_single b]
    · simp
    · intro j _ hj'
      simp [hj']
    · simp
  let m : Fin (r + 1) → O := fun a => ⟨cj (∑ j, cj (y' j : E) * (n a j : E)),
    hO _ (O.sum_mem fun j _ => O.mul_mem (hO _ (y' j).2) (n a j).2)⟩
  have hmlast : m (Fin.last r) = 0 := by
    apply Subtype.ext
    simp [m, hn0 (Fin.last r) rfl]
  have hdiff : adjV O cj hO hu₂ δ hb' he' x - y' = (cjT O cj hO Z₁).mulVec m := by
    funext b
    apply Subtype.ext
    rw [Pi.sub_apply, AddSubgroupClass.coe_sub, cjT_mulVec_coe, ← hE b]
    show adjVal O cj δ x b - _ = _
    rw [adjVal, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [adjW, hA1, hn a, bRaw_add_left, bRaw_mulVec O cj Z₁ hu₁, map_add]
    simp only [m]
    ring
  rw [Submodule.Quotient.eq, hdiff]
  exact mulVec_mem_headCols_of_last_eq_zero (O := O) (cj := cj) (hcj := hcj) (hO := hO) (hu₁ := hu₁) (hu₂ := hu₂)
    (Z := cjT O cj hO Z₁) (w := m) (hw := hmlast)

def adjEquiv (γ : MbMod Z₁ ≃ₗ[O] MbMod Z₂) (hb : γ (bCls Z₁) = bCls Z₂) (he : γ (eCl Z₁) = eCl Z₂) :
    MbMod (cjT O cj hO Z₁) ≃ₗ[O] MbMod (cjT O cj hO Z₂) :=
  have hb' : γ.symm (bCls Z₂) = bCls Z₁ := by rw [LinearEquiv.symm_apply_eq]; exact hb.symm
  have he' : γ.symm (eCl Z₂) = eCl Z₁ := by rw [LinearEquiv.symm_apply_eq]; exact he.symm
  LinearEquiv.ofLinear (adjQ O cj hcj hO hu₁ hu₂ γ hb he) (adjQ O cj hcj hO hu₂ hu₁ γ.symm hb' he')
    (by
      refine LinearMap.ext fun m => ?_
      obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ m
      exact adjV_comp O cj hcj hO hu₂ hu₁ γ.symm hb' he' γ hb he (fun m => γ.apply_symm_apply m) y')
    (by
      refine LinearMap.ext fun m => ?_
      obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ m
      exact adjV_comp O cj hcj hO hu₁ hu₂ γ hb he γ.symm hb' he' (fun m => γ.symm_apply_apply m) y')

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem adjEquiv_mk (γ : MbMod Z₁ ≃ₗ[O] MbMod Z₂) (hb : γ (bCls Z₁) = bCls Z₂)
    (he : γ (eCl Z₁) = eCl Z₂) (y' : Fin (r + 1) → O) :
    adjEquiv O cj hcj hO hu₁ hu₂ γ hb he (Submodule.Quotient.mk y') =
      Submodule.Quotient.mk (adjV O cj hO hu₁ γ hb he y') := rfl

/- English proof (translation)
Introduce and unpack `⟨γ, hb, he⟩`. Use `⟨⟨(γ, adjEquiv O cj hcj hO hu₁ hu₂ γ hb he), ⟨hb, he⟩, ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Introduce `y' y₂' h`. Rewrite `h` using `[adjEquiv_mk]`. Establish `hd : y₂' - adjV O cj hO hu₁ γ hb he y' ∈ headCols (cjT O cj hO Z₂)`.

Rewrite using `[← Submodule.Quotient.eq]`. Conclude with `h.symm`. Establish `h0` using `lamS_headCols O cj hO Z₂ hu₂ hd`. Rewrite `h0` using `[lamS_sub, sub_eq_zero]`. Rewrite using `[h0, lamS_adjV O cj hcj hO hu₁ hu₂ γ hb he]`.

Introduce `y y' y₂ y₂' h1 h2`. Rewrite `h2` using `[adjEquiv_mk]`. Establish `hd : y₂' - adjV O cj hO hu₁ γ hb he y' ∈ headCols (cjT O cj hO Z₂)`. Rewrite using `[← Submodule.Quotient.eq]`. Conclude with `h2.symm`.

Establish `hA` using `bRaw_headCols_right O cj hcj hO Z₂ hu₂ y₂ hd`. Establish `hB` using `bRaw_adjV O cj hcj hO hu₁ hu₂ γ hb he h1 y'`. Rewrite `hA` using `[bRaw_sub_right]`. Use `O.add_mem hA hB` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem projP_surjective : Function.Surjective (projP O cj hO Z₁ Z₂) := by
  rintro ⟨γ, hb, he⟩
  refine ⟨⟨(γ, adjEquiv O cj hcj hO hu₁ hu₂ γ hb he), ⟨hb, he⟩, ?_, ?_⟩, rfl⟩
  · intro y' y₂' h
    rw [adjEquiv_mk] at h
    have hd : y₂' - adjV O cj hO hu₁ γ hb he y' ∈ headCols (cjT O cj hO Z₂) := by
      rw [← Submodule.Quotient.eq]
      exact h.symm
    have h0 := lamS_headCols O cj hO Z₂ hu₂ hd
    rw [lamS_sub, sub_eq_zero] at h0
    rw [h0, lamS_adjV O cj hcj hO hu₁ hu₂ γ hb he]
  · intro y y' y₂ y₂' h1 h2
    rw [adjEquiv_mk] at h2
    have hd : y₂' - adjV O cj hO hu₁ γ hb he y' ∈ headCols (cjT O cj hO Z₂) := by
      rw [← Submodule.Quotient.eq]
      exact h2.symm
    have hA := bRaw_headCols_right O cj hcj hO Z₂ hu₂ y₂ hd
    have hB := bRaw_adjV O cj hcj hO hu₁ hu₂ γ hb he h1 y'
    rw [bRaw_sub_right] at hA
    have := O.add_mem hA hB
    rwa [sub_add_sub_cancel] at this

end Adj

def StepAdjG : Prop :=
  ∀ (E : Type) [CommRing E] (O : Subring E) (cj : E →+* E), (∀ x, cj (cj x) = x) →
    ∀ (hO : ∀ x ∈ O, cj x ∈ O) (r : ℕ) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O),
    IsUnit (Z₁.map O.subtype).det → IsUnit (Z₂.map O.subtype).det →
    Function.Surjective (projP O cj hO Z₁ Z₂)

/- English proof (translation)
Introduce `E _ O cj hcj hO r Z₁ Z₂ hu₁ hu₂`. Conclude with `projP_surjective O cj hcj hO hu₁ hu₂`.
-/
theorem stepAdjG : StepAdjG := by
  intro E _ O cj hcj hO r Z₁ Z₂ hu₁ hu₂
  exact projP_surjective O cj hcj hO hu₁ hu₂

/- English proof (translation)
Introduce `E _ O cj hcj hO r Z₁ Z₂ hu₁ hu₂ _ _`. Conclude with `stepAdjG E O cj hcj hO r Z₁ Z₂ hu₁ hu₂`.
-/
theorem stepAdj : StepAdj := by
  intro E _ O cj hcj hO r Z₁ Z₂ hu₁ hu₂ _ _
  exact stepAdjG E O cj hcj hO r Z₁ Z₂ hu₁ hu₂

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear
