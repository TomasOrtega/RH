import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarOIsAddHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEigenContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdQ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalLiftSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeBTripleHypothesisFormStatement
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.StdPairLoc
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

noncomputable section

namespace GlobalTheory.PlaneTransl

open Matrix GlobalTheory.IsoCoord GlobalTheory.PlaneBasis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}

/- English proof (translation)
Establish `hD : ((Cᵀ * J.map t) *ᵥ fun r => t (σ (z r))) i = (fun r => C r i) ⬝ᵥ (J.map t *ᵥ fun r => t (σ (z r)))`. Rewrite using `[← mulVec_mulVec]`. Both sides reduce to the same expression. Rewrite using `[hD, funext h, dot_form]`.
-/
theorem coef (t : E →ₐ[F] Fv F v) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (C : Matrix (Fin n) (Fin n) (Fv F v))
    (i : Fin n) (y z : Fin n → E) (h : ∀ r, C r i = t (y r)) :
    ((Cᵀ * J.map t) *ᵥ fun r => t (σ (z r))) i = t (form σ J y z) := by
  have hD : ((Cᵀ * J.map t) *ᵥ fun r => t (σ (z r))) i = (fun r => C r i) ⬝ᵥ (J.map t *ᵥ fun r => t (σ (z r))) := by
    rw [← mulVec_mulVec]; rfl
  rw [hD, funext h, dot_form]

/- English proof (translation)
Establish `hP' : IsUnit Pᵀ.det` using `by rwa [det_transpose]`. Rewrite using `[GlobalTheory.IsoCoord.vecMulVec_mulVec]`. Simplify using `only [transpose_mul, transpose_transpose, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]`. Rewrite using `[nonsing_inv_mul_cancel_left _ _ hP', mul_nonsing_inv _ hQ, Matrix.mul_one]`.
-/
theorem co_eq {R : Type} [Field R] {n d : ℕ} (P A : Matrix (Fin n) (Fin n) R) (Q C : Matrix (Fin d) (Fin d) R)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det) (p : Fin n → R) (q : Fin d → R) :
    -(A * vecMulVec p q * Cᵀ) = Pᵀ⁻¹ * (-vecMulVec ((Pᵀ * A) *ᵥ p) ((Qᵀ * C) *ᵥ q)) * Q⁻¹ := by
  have hP' : IsUnit Pᵀ.det := by rwa [det_transpose]
  rw [GlobalTheory.IsoCoord.vecMulVec_mulVec]
  simp only [transpose_mul, transpose_transpose, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  rw [nonsing_inv_mul_cancel_left _ _ hP', mul_nonsing_inv _ hQ, Matrix.mul_one]

variable {B : Base F E} {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b} {H : Plane E (b + 2) b}
    {H' : Plane E (a + (b + 2)) (a + b)}

/- English proof (translation)
Establish `hM : IsUnit ((basW t H')ᵀ * G.W.J.map t).det`. Rewrite using `[det_mul, det_transpose]`. Conclude with `hQ.mul (isUnit_iff_ne_zero.2 (det_map_ne_zero _ (det_ne_zero_skew hG.hW)))`. Take `⟨z, hz, h0, h1⟩` from `exists_vec_comps hB.cm v t 0 (-(((basW t H')ᵀ * G.W.J.map t)⁻¹ *ᵥ r))`. Use `⟨vecMulVec (incV F H.x) z, Or.inl ⟨z, rfl⟩, at_vecMulVec_right _ hz, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_vecMulVec, h0]`. Use extensionality with `i j`. Simplify using `[vecMulVec_apply]`. Rewrite using `[map_vecMulVec, h1, piW_incV, co_eq _ _ _ _ hP hQ]`. Rewrite using `[mulVec_neg, mulVec_mulVec, mul_nonsing_inv _ hM, one_mulVec]`.

Establish `hp : ∀ i, (((basV t H)ᵀ * G.V'.J.map t) *ᵥ fun i => (t.comp σ) (H.x i)) i = if i.1 = b + 1 then 1 else 0`. Introduce `i`. Express the relevant statement in the definitionally equal form `(((basV t H)ᵀ * G.V'.J.map t) *ᵥ fun i => t (σ (H.x i))) i = _`. Distinguish the cases in `i0 : i.1 = 0`. Rewrite using `[coef t _ _ i H.x _ (fun r => by simp [basV, i0]), hC.hH.xx, map_zero, if_neg (by omega)]`.

Distinguish the cases in `i1 : i.1 = b + 1`. Rewrite using `[coef t _ _ i H.y _ (fun r => by simp [basV, i1]), if_pos i1]`. Use `form_swap hB.cm 1 (fun i j => by rw [one_mul]; exact hG.hV'.herm i j) H.x H.y` as an intermediate fact. Rewrite `this` using `[hC.hH.xy, map_one, one_mul]`. Rewrite using `[← this, map_one]`.

Rewrite using `[coef t _ _ i (fun r => H.ι r ⟨i.1 - 1, by have := i.2; omega⟩) _ (fun r => by simp [basV, i0, i1]), (orth_col hC.hH _).1, map_zero, if_neg i1]`. Unfold `crdP crdQ`. Use `congr 2`. Use extensionality with `i j`. Rewrite using `[Matrix.neg_apply, vecMulVec_apply, hp i, Pi.neg_apply]`.

Distinguish the cases in `h0 : i.1 = 0`. Establish `h1 : i.1 ≠ b + 1` using `by omega`. Simplify using `[insS, h0]`. Distinguish the cases in `h1 : i.1 = b + 1`. Simplify using `[insS, h1]`.

Simplify using `[insS, h0, h1]`.
-/
theorem exists_row (hB : B.IsGood σ) (hG : G.IsGood B) (hC : CfgB B G G₁ H H') (t : E →ₐ[F] Fv F v)
    (hP : IsUnit (basV t H).det) (hQ : IsUnit (basW t H').det) (r : Fin (a + (b + 2)) → Fv F v) :
    ∃ u ∈ isoB H H', At (evFin F v) u ∧ u.map (piW t) = 0 ∧
      -(G.V'.J.map t * u.map (piW (t.comp σ)) * (G.W.J.map t)ᵀ) =
        crdP t H * insS (0 : Matrix (Fin b) (Fin (a + b)) (Fv F v)) r 0 0 * crdQ t H' := by
  have hM : IsUnit ((basW t H')ᵀ * G.W.J.map t).det := by
    rw [det_mul, det_transpose]
    exact hQ.mul (isUnit_iff_ne_zero.2 (det_map_ne_zero _ (det_ne_zero_skew hG.hW)))
  obtain ⟨z, hz, h0, h1⟩ := exists_vec_comps hB.cm v t 0 (-(((basW t H')ᵀ * G.W.J.map t)⁻¹ *ᵥ r))
  refine ⟨vecMulVec (incV F H.x) z, Or.inl ⟨z, rfl⟩, at_vecMulVec_right _ hz, ?_, ?_⟩
  · rw [map_vecMulVec, h0]; ext i j; simp [vecMulVec_apply]
  rw [map_vecMulVec, h1, piW_incV, co_eq _ _ _ _ hP hQ]
  rw [mulVec_neg, mulVec_mulVec, mul_nonsing_inv _ hM, one_mulVec]
  have hp : ∀ i, (((basV t H)ᵀ * G.V'.J.map t) *ᵥ fun i => (t.comp σ) (H.x i)) i =
      if i.1 = b + 1 then 1 else 0 := by
    intro i
    change (((basV t H)ᵀ * G.V'.J.map t) *ᵥ fun i => t (σ (H.x i))) i = _
    by_cases i0 : i.1 = 0
    · rw [coef t _ _ i H.x _ (fun r => by simp [basV, i0]), hC.hH.xx, map_zero, if_neg (by omega)]
    by_cases i1 : i.1 = b + 1
    · rw [coef t _ _ i H.y _ (fun r => by simp [basV, i1]), if_pos i1]
      have := form_swap hB.cm 1 (fun i j => by rw [one_mul]; exact hG.hV'.herm i j) H.x H.y
      rw [hC.hH.xy, map_one, one_mul] at this
      rw [← this, map_one]
    · rw [coef t _ _ i (fun r => H.ι r ⟨i.1 - 1, by have := i.2; omega⟩) _ (fun r => by simp [basV, i0, i1]),
        (orth_col hC.hH _).1, map_zero, if_neg i1]
  unfold crdP crdQ
  congr 2
  ext i j
  rw [Matrix.neg_apply, vecMulVec_apply, hp i, Pi.neg_apply]
  by_cases h0 : i.1 = 0
  · have h1 : i.1 ≠ b + 1 := by omega
    simp [insS, h0]
  · by_cases h1 : i.1 = b + 1
    · simp [insS, h1]
    · simp [insS, h0, h1]

/- English proof (translation)
Use `set N := G₁.V'.J.map t with hNdef`. Establish `hN : IsUnit N.det` using `isUnit_iff_ne_zero.2 (det_map_ne_zero _ (GlobalTheory.isUnit_det_of_isHerm F E σ B b G₁.V' _ _ hG₁.hV').ne_zero)`. Establish `herm : ∀ i j, σ (G.V'.J j i) = 1 * G.V'.J i j` using `fun i j => by rw [one_mul]; exact hG.hV'.herm i j`. Take `⟨y, hy, h0, h1⟩` from `exists_vec_comps hB.cm v t 0 (N⁻¹ *ᵥ c)`. Use `⟨vecMulVec (incM F H.ι *ᵥ y) (incV F H'.x), Or.inr ⟨y, rfl⟩, at_vecMulVec_left _ hy _, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_vecMulVec, piW_mulVec, h0, mulVec_zero]`. Use extensionality with `i j`. Simplify using `[vecMulVec_apply]`. Rewrite using `[map_vecMulVec, piW_mulVec, h1, piW_incV, co_eq _ _ _ _ hP hQ]`. Establish `hq : ∀ k, (((basW t H')ᵀ * G.W.J.map t) *ᵥ fun i => (t.comp σ) (H'.x i)) k = if k.1 = a + b + 1 then -1 else 0`.

Introduce `k`. Express the relevant statement in the definitionally equal form `(((basW t H')ᵀ * G.W.J.map t) *ᵥ fun i => t (σ (H'.x i))) k = _`. Distinguish the cases in `k0 : k.1 = a`. Rewrite using `[coef t _ _ k H'.x _ (fun r => by simp only [basW, dif_pos k0]), hC.hH'.xx, map_zero, if_neg (by omega)]`. Distinguish the cases in `k1 : k.1 = a + b + 1`.

Rewrite using `[coef t _ _ k H'.y _ (fun r => by simp only [basW, dif_neg k0, dif_pos k1]), if_pos k1]`. Use `form_swap hB.cm (-1) (fun i j => by rw [neg_one_mul]; exact hG.hW.skew i j) H'.x H'.y` as an intermediate fact. Rewrite `this` using `[hC.hH'.xy, map_one, neg_one_mul]`. Rewrite using `[show form σ G.W.J H'.y H'.x = -1 by rw [this, neg_neg], map_neg, map_one]`. Distinguish the cases in `k2 : k.1 < a`.

Rewrite using `[coef t _ _ k (fun r => H'.ι r ⟨k.1, by omega⟩) _ (fun r => by simp only [basW, dif_neg k0, dif_neg k1, dif_pos k2]), (orth_col hC.hH' _).1, map_zero, if_neg k1]`. Rewrite using `[coef t _ _ k (fun r => H'.ι r ⟨k.1 - 1, by have := k.2; omega⟩) _ (fun r => by simp only [basW, dif_neg k0, dif_neg k1, dif_neg k2]), (orth_col hC.hH' _).1, map_zero, if_neg k1]`. Establish `hE : ∀ i k, (((basV t H)ᵀ * G.V'.J.map t) * H.ι.map (t.comp σ)) i k = (((basV t H)ᵀ * G.V'.J.map t) *ᵥ fun r => t (σ (H.ι r k))) i` using `fun _ _ => rfl`. Establish `hp : ∀ i, (((basV t H)ᵀ * G.V'.J.map t) *ᵥ (H.ι.map (t.comp σ) *ᵥ (N⁻¹ *ᵥ c))) i = if h : i.1 = 0 ∨ i.1 = b + 1 then 0 else c ⟨i.1 - 1, by omega⟩`. Introduce `i`.

Rewrite using `[mulVec_mulVec]`. Express the relevant statement in the definitionally equal form `∑ k : Fin b, _ * _ = _`. Simplify using `only [hE]`. Use `split_ifs with hi`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations.

Break down `hi with i0 | i1` into its components or cases. Use `form_swap hB.cm 1 herm (fun r => H.ι r k) H.x` as an intermediate fact. Rewrite `this` using `[(orth_col hC.hH k).1, map_zero, one_mul]`. Rewrite using `[coef t _ _ i H.x (fun r => H.ι r k) (fun r => by simp [basV, i0]), ← this, map_zero, zero_mul]`. Use `form_swap hB.cm 1 herm (fun r => H.ι r k) H.y` as an intermediate fact.

Rewrite `this` using `[(orth_col hC.hH k).2, map_zero, one_mul]`. Rewrite using `[coef t _ _ i H.y (fun r => H.ι r k) (fun r => by simp [basV, i1]), ← this, map_zero, zero_mul]`. Establish `i0 : ¬ i.1 = 0` using `fun h => hi (Or.inl h)`. Establish `i1 : ¬ i.1 = b + 1` using `fun h => hi (Or.inr h)`. Establish `hmid : ∀ k, (((basV t H)ᵀ * G.V'.J.map t) *ᵥ fun r => t (σ (H.ι r k))) i = N ⟨i.1 - 1, by omega⟩ k`.

Introduce `k`. Rewrite using `[coef t _ _ i (fun r => H.ι r ⟨i.1 - 1, by omega⟩) (fun r => H.ι r k) (fun r => by simp [basV, i0, i1]), gram_form, hC.hH.gram]`. Both sides reduce to the same expression. Simplify using `only [hmid]`. Express the relevant statement in the definitionally equal form `(N *ᵥ (N⁻¹ *ᵥ c)) ⟨i.1 - 1, by omega⟩ = _`.

Rewrite using `[mulVec_mulVec, mul_nonsing_inv _ hN, one_mulVec]`. Unfold `crdP crdQ`. Use `congr 2`. Use extensionality with `i j`. Rewrite using `[Matrix.neg_apply, vecMulVec_apply, hp i, hq j]`.

Distinguish the cases in `h0 : i.1 = 0`. Simplify using `[insS, h0]`. Distinguish the cases in `h1 : i.1 = b + 1`. Simplify using `[insS, h1]`. Distinguish the cases in `hj : j.1 = a + b + 1`.

Establish `e1 : ¬ a + b + 1 < a` using `by omega`. Establish `e2 : a + b + 1 ≠ a` using `by omega`. Simplify using `[insS, h0, h1, hj, e1, e2]`. Simplify using `[insS, h0, h1, hj]`.
-/
theorem exists_mid (hB : B.IsGood σ) (hG : G.IsGood B) (hG₁ : G₁.IsGood B) (hC : CfgB B G G₁ H H')
    (t : E →ₐ[F] Fv F v) (hP : IsUnit (basV t H).det) (hQ : IsUnit (basW t H').det) (c : Fin b → Fv F v) :
    ∃ u ∈ isoB H H', At (evFin F v) u ∧ u.map (piW t) = 0 ∧
      -(G.V'.J.map t * u.map (piW (t.comp σ)) * (G.W.J.map t)ᵀ) =
        crdP t H * insS (0 : Matrix (Fin b) (Fin (a + b)) (Fv F v)) 0 c 0 * crdQ t H' := by
  set N := G₁.V'.J.map t with hNdef
  have hN : IsUnit N.det := isUnit_iff_ne_zero.2 (det_map_ne_zero _
      (GlobalTheory.isUnit_det_of_isHerm F E σ B b G₁.V' _ _ hG₁.hV').ne_zero)
  have herm : ∀ i j, σ (G.V'.J j i) = 1 * G.V'.J i j := fun i j => by rw [one_mul]; exact hG.hV'.herm i j
  obtain ⟨y, hy, h0, h1⟩ := exists_vec_comps hB.cm v t 0 (N⁻¹ *ᵥ c)
  refine ⟨vecMulVec (incM F H.ι *ᵥ y) (incV F H'.x), Or.inr ⟨y, rfl⟩, at_vecMulVec_left _ hy _, ?_, ?_⟩
  · rw [map_vecMulVec, piW_mulVec, h0, mulVec_zero]; ext i j; simp [vecMulVec_apply]
  rw [map_vecMulVec, piW_mulVec, h1, piW_incV, co_eq _ _ _ _ hP hQ]
  have hq : ∀ k, (((basW t H')ᵀ * G.W.J.map t) *ᵥ fun i => (t.comp σ) (H'.x i)) k =
      if k.1 = a + b + 1 then -1 else 0 := by
    intro k
    change (((basW t H')ᵀ * G.W.J.map t) *ᵥ fun i => t (σ (H'.x i))) k = _
    by_cases k0 : k.1 = a
    · rw [coef t _ _ k H'.x _ (fun r => by simp only [basW, dif_pos k0]), hC.hH'.xx, map_zero, if_neg (by omega)]
    by_cases k1 : k.1 = a + b + 1
    · rw [coef t _ _ k H'.y _ (fun r => by simp only [basW, dif_neg k0, dif_pos k1]), if_pos k1]
      have := form_swap hB.cm (-1) (fun i j => by rw [neg_one_mul]; exact hG.hW.skew i j) H'.x H'.y
      rw [hC.hH'.xy, map_one, neg_one_mul] at this
      rw [show form σ G.W.J H'.y H'.x = -1 by rw [this, neg_neg], map_neg, map_one]
    by_cases k2 : k.1 < a
    · rw [coef t _ _ k (fun r => H'.ι r ⟨k.1, by omega⟩) _
        (fun r => by simp only [basW, dif_neg k0, dif_neg k1, dif_pos k2]), (orth_col hC.hH' _).1, map_zero, if_neg k1]
    · rw [coef t _ _ k (fun r => H'.ι r ⟨k.1 - 1, by have := k.2; omega⟩) _
        (fun r => by simp only [basW, dif_neg k0, dif_neg k1, dif_neg k2]), (orth_col hC.hH' _).1, map_zero, if_neg k1]
  have hE : ∀ i k, (((basV t H)ᵀ * G.V'.J.map t) * H.ι.map (t.comp σ)) i k =
      (((basV t H)ᵀ * G.V'.J.map t) *ᵥ fun r => t (σ (H.ι r k))) i := fun _ _ => rfl
  have hp : ∀ i, (((basV t H)ᵀ * G.V'.J.map t) *ᵥ (H.ι.map (t.comp σ) *ᵥ (N⁻¹ *ᵥ c))) i =
      if h : i.1 = 0 ∨ i.1 = b + 1 then 0 else c ⟨i.1 - 1, by omega⟩ := by
    intro i
    rw [mulVec_mulVec]
    change ∑ k : Fin b, _ * _ = _
    simp only [hE]
    split_ifs with hi
    · refine Finset.sum_eq_zero fun k _ => ?_
      rcases hi with i0 | i1
      · have := form_swap hB.cm 1 herm (fun r => H.ι r k) H.x
        rw [(orth_col hC.hH k).1, map_zero, one_mul] at this
        rw [coef t _ _ i H.x (fun r => H.ι r k) (fun r => by simp [basV, i0]), ← this, map_zero, zero_mul]
      · have := form_swap hB.cm 1 herm (fun r => H.ι r k) H.y
        rw [(orth_col hC.hH k).2, map_zero, one_mul] at this
        rw [coef t _ _ i H.y (fun r => H.ι r k) (fun r => by simp [basV, i1]), ← this, map_zero, zero_mul]
    · have i0 : ¬ i.1 = 0 := fun h => hi (Or.inl h)
      have i1 : ¬ i.1 = b + 1 := fun h => hi (Or.inr h)
      have hmid : ∀ k, (((basV t H)ᵀ * G.V'.J.map t) *ᵥ fun r => t (σ (H.ι r k))) i =
          N ⟨i.1 - 1, by omega⟩ k := by
        intro k
        rw [coef t _ _ i (fun r => H.ι r ⟨i.1 - 1, by omega⟩) (fun r => H.ι r k) (fun r => by simp [basV, i0, i1]),
          gram_form, hC.hH.gram]
        rfl
      simp only [hmid]
      change (N *ᵥ (N⁻¹ *ᵥ c)) ⟨i.1 - 1, by omega⟩ = _
      rw [mulVec_mulVec, mul_nonsing_inv _ hN, one_mulVec]
  unfold crdP crdQ
  congr 2
  ext i j
  rw [Matrix.neg_apply, vecMulVec_apply, hp i, hq j]
  by_cases h0 : i.1 = 0
  · simp [insS, h0]
  · by_cases h1 : i.1 = b + 1
    · simp [insS, h1]
    · by_cases hj : j.1 = a + b + 1
      · have e1 : ¬ a + b + 1 < a := by omega
        have e2 : a + b + 1 ≠ a := by omega
        simp [insS, h0, h1, hj, e1, e2]
      · simp [insS, h0, h1, hj]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [insS, Matrix.add_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem insS_add {R : Type} [AddMonoid R] (r : Fin (a + (b + 2)) → R) (c : Fin b → R) :
    insS (0 : Matrix (Fin b) (Fin (a + b)) R) r c 0 =
      insS (0 : Matrix (Fin b) (Fin (a + b)) R) 0 c 0 + insS (0 : Matrix (Fin b) (Fin (a + b)) R) r 0 0 := by
  ext i j
  simp only [insS, Matrix.add_apply]
  split_ifs <;> simp

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ L _ _ hinv ι ι₁ hι _ r c φ hφ`. Take `⟨hP, hQ⟩` from `GlobalTheory.T.seesaw_type_b_triple_hypothesis_form B G G₁ H H' hC X om om' om₁ om₁' hT hT₁`. Take `⟨u₁, hu₁, a₁, z₁, e₁⟩` from `exists_row hT.base hT.geo hC B.τ₁ hP hQ r`. Take `⟨u₂, hu₂, a₂, z₂, e₂⟩` from `exists_mid hT.base hT.geo hT₁.geo hC B.τ₁ hP hQ c`. Establish `hL` using `hι`.

Unfold `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinBar at hL`. Simplify using `only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL`. Establish `hsb` using `fun w f hf => GlobalTheory.SchrSB.schr_mem_SB (κ := Fin (b + 2) × Fin (a + (b + 2))) B.ψ hT.base.std.1 B.v₁ w f hf`. Establish `s₁` using `hsb (GlobalTheory.LatVac.locCo G.M'.co B.v₁ u₁) φ hφ`. Establish `s₂` using `hsb (GlobalTheory.LatVac.locCo G.M'.co B.v₁ u₂) _ s₁`.

Use `⟨_, s₂, (hinv u₂ hu₂ a₂ _ s₁).trans (hinv u₁ hu₁ a₁ φ hφ), fun Z => ?_⟩` and prove the remaining obligations. Rewrite using `[hL.trans u₂ a₂ z₂ _ s₁ _ s₂ (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ B.v₁ u₂ a₂ _), hL.trans u₁ a₁ z₁ _ hφ _ s₁ (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ B.v₁ u₁ a₁ _)]`. Use `beta_reduce`. Rewrite using `[e₁, e₂, insS_add r c, Matrix.mul_add, Matrix.add_mul, add_assoc]`.
-/
theorem transl_inv : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (L : ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F B.v₁) → ℂ),
    (∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), L φ ∈ SB (Fin b × Fin (a + b) → Fv F B.v₁)) →
    (∀ z : Matrix (Fin b) (Fin (a + b)) (AE F E), At (evFin F B.v₁) z → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁),
      L (schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ (incM F H.ι * z * (incM F H'.ι)ᵀ)) φ) =
        schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G₁.M'.co B.v₁ z) (L φ)) →
    (∀ u ∈ isoB H H', At (evFin F B.v₁) u → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁),
      L (schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ u) φ) = L φ) →
    ∀ ι ι₁, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι → G₁.M'.IsLinBar B.ψ B.τ₁ 1 1 ι₁ →
    ∀ (r : Fin (a + (b + 2)) → Fv F B.v₁) (c : Fin b → Fv F B.v₁), ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), ∃ φ' ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), L φ' = L φ ∧
      ∀ Z, ι φ' Z = ι φ (Z + GlobalTheory.PlaneBasis.crdP B.τ₁ H * insS (0 : Matrix (Fin b) (Fin (a + b)) (Fv F B.v₁)) r c 0 * GlobalTheory.PlaneBasis.crdQ B.τ₁ H') := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ L _ _ hinv ι ι₁ hι _ r c φ hφ
  obtain ⟨hP, hQ⟩ := GlobalTheory.T.seesaw_type_b_triple_hypothesis_form B G G₁ H H' hC X om om' om₁ om₁' hT hT₁
  obtain ⟨u₁, hu₁, a₁, z₁, e₁⟩ := exists_row hT.base hT.geo hC B.τ₁ hP hQ r
  obtain ⟨u₂, hu₂, a₂, z₂, e₂⟩ := exists_mid hT.base hT.geo hT₁.geo hC B.τ₁ hP hQ c
  have hL := hι
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinBar at hL
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL
  have hsb := fun w f hf => GlobalTheory.SchrSB.schr_mem_SB (κ := Fin (b + 2) × Fin (a + (b + 2))) B.ψ hT.base.std.1 B.v₁ w f hf
  have s₁ := hsb (GlobalTheory.LatVac.locCo G.M'.co B.v₁ u₁) φ hφ
  have s₂ := hsb (GlobalTheory.LatVac.locCo G.M'.co B.v₁ u₂) _ s₁
  refine ⟨_, s₂, (hinv u₂ hu₂ a₂ _ s₁).trans (hinv u₁ hu₁ a₁ φ hφ), fun Z => ?_⟩
  rw [hL.trans u₂ a₂ z₂ _ s₁ _ s₂ (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ B.v₁ u₂ a₂ _),
    hL.trans u₁ a₁ z₁ _ hφ _ s₁ (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ B.v₁ u₁ a₁ _)]
  beta_reduce
  rw [e₁, e₂, insS_add r c, Matrix.mul_add, Matrix.add_mul, add_assoc]

end GlobalTheory.PlaneTransl

end
