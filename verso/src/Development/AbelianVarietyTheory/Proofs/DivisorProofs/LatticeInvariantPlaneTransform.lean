import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacGlueIndicator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneTransformRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRingEmbeddingRows
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneCo

noncomputable section

namespace GlobalTheory.ThK.PlaneCo.LatDec

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `h : incM F (Matrix.vecMulVec x y) = Matrix.vecMulVec (incV F x) (incV F y)`. Use extensionality with `i j`. Simplify using `[incM, incV, Matrix.vecMulVec_apply]`. Rewrite using `[map_smul, Matrix.smul_apply, h, coefLin_vecMulVec, map_mul, RingHom.map_mulVec, RingHom.map_mulVec]`. Both sides reduce to the same expression.
-/
theorem coefLin_pure {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) (a : AF F) (x : Fin n → E)
    (y : Fin d → E) (k : Fin n₁ ⊕ Fin 2) (l : Fin d₁ ⊕ Fin 2) :
    coefLin H H' (a • incM F (Matrix.vecMulVec x y)) k l =
      a • inclR (F := F) (AF F) ((planeCoef H *ᵥ x) k * (planeCoef H' *ᵥ y) l) := by
  have h : incM F (Matrix.vecMulVec x y) = Matrix.vecMulVec (incV F x) (incV F y) := by
    ext i j; simp [incM, incV, Matrix.vecMulVec_apply]
  rw [map_smul, Matrix.smul_apply, h, coefLin_vecMulVec, map_mul, RingHom.map_mulVec, RingHom.map_mulVec]
  rfl

/- English proof (translation)
Rewrite using `[Matrix.mulVec_smul, Pi.smul_apply, planeCoef_mulVec_x_ne H hk, smul_zero]`.
-/
theorem planeCoef_mulVec_smul_x_eq_zero_of_ne {n n₁ : ℕ} (H : Plane E n n₁) (s : E) {k : Fin n₁ ⊕ Fin 2} (hk : k ≠ .inr 0) :
    (planeCoef H *ᵥ (s • H.x)) k = 0 := by
  rw [Matrix.mulVec_smul, Pi.smul_apply, planeCoef_mulVec_x_ne H hk, smul_zero]

/- English proof (translation)
Use `planeCoef_mul_planeMat_ne H hk` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply]`. Establish `h : (planeCoef H *ᵥ H.y) k = 0` using `by simpa [Matrix.mulVec, dotProduct, planeMat] using this`. Rewrite using `[Matrix.mulVec_smul, Pi.smul_apply, h, smul_zero]`.
-/
theorem coef_y {n n₁ : ℕ} (H : Plane E n n₁) (s : E) {k : Fin n₁ ⊕ Fin 2} (hk : k ≠ .inr 1) :
    (planeCoef H *ᵥ (s • H.y)) k = 0 := by
  have := planeCoef_mul_planeMat_ne H hk
  rw [Matrix.mul_apply] at this
  have h : (planeCoef H *ᵥ H.y) k = 0 := by simpa [Matrix.mulVec, dotProduct, planeMat] using this
  rw [Matrix.mulVec_smul, Pi.smul_apply, h, smul_zero]

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec]`. Simplify using `[Matrix.mulVec, dotProduct, planeCoef_mul_ι_inr]`.
-/
theorem coef_ι {n n₁ : ℕ} (H : Plane E n n₁) (u : Fin n₁ → E) (t : Fin 2) :
    (planeCoef H *ᵥ (H.ι *ᵥ u)) (.inr t) = 0 := by
  rw [Matrix.mulVec_mulVec]
  simp [Matrix.mulVec, dotProduct, planeCoef_mul_ι_inr]

variable (σ : E →ₐ[F] E) {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (H : Plane E n n₁) (H' : Plane E d d₁)

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Simplify using `[planeT, hs]`. Use extensionality with `i j`. Simplify using `[planeT, hb]`.
-/
theorem planeT_of_sI (u : Matrix (Fin n) (Fin d) (AE F E)) (hs : ∀ k, sI H H' u k = 0)
    (hb : ∀ i j, coefLin H H' u (.inl i) (.inl j) = 0) :
    (planeT σ X W H H' u).1.1 = 0 ∧ (planeT σ X W H H' u).2 = 0 := by
  refine ⟨?_, ?_⟩
  · funext k; simp [planeT, hs]
  · ext i j; simp [planeT, hb]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Simplify using `[planeT, pairI, ht]`. Use extensionality with `i j`. Simplify using `[planeT, hb]`.
-/
theorem planeT_of_tI (u : Matrix (Fin n) (Fin d) (AE F E)) (ht : ∀ k, tI H H' u k = 0)
    (hb : ∀ i j, coefLin H H' u (.inl i) (.inl j) = 0) :
    (planeT σ X W H H' u).1.2 = 0 ∧ (planeT σ X W H H' u).2 = 0 := by
  refine ⟨?_, ?_⟩
  · funext k; simp [planeT, pairI, ht]
  · ext i j; simp [planeT, hb]

def Dec (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (v : Pl F) (γ : Matrix (Fin n) (Fin d) (AE F E)) : Prop :=
  (∃ a ∈ latAtV X W v, planeT σ X W H H' a = ((0, (planeT σ X W H H' γ).1.2), 0)) ∧
    (∃ b ∈ latAtV X W v, planeT σ X W H H' b = (((planeT σ X W H H' γ).1.1, 0), 0)) ∧
    (planeT σ X W H H' γ).2 ∈ latAtV X₁ W₁ v

variable {σ X W H H'} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {v : Pl F}

/- English proof (translation)
Use `⟨⟨0, zero_mem _, ?_⟩, ⟨0, zero_mem _, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero]`. Both sides reduce to the same expression. Rewrite using `[map_zero]`. Both sides reduce to the same expression.

Rewrite using `[map_zero]`. Conclude with `zero_mem _`.
-/
theorem Dec.zero : Dec σ X W H H' X₁ W₁ v 0 := by
  refine ⟨⟨0, zero_mem _, ?_⟩, ⟨0, zero_mem _, ?_⟩, ?_⟩
  · rw [map_zero]; rfl
  · rw [map_zero]; rfl
  · rw [map_zero]; exact zero_mem _

/- English proof (translation)
Take `⟨⟨a, ha, ea⟩, ⟨b, hb, eb⟩, hc⟩` from `h`. Take `⟨⟨a', ha', ea'⟩, ⟨b', hb', eb'⟩, hc'⟩` from `h'`. Use `⟨⟨a + a', add_mem ha ha', ?_⟩, ⟨b + b', add_mem hb hb', ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_add, ea, ea']`. Simplify using `only [Prod.mk_add_mk, add_zero, Prod.fst_add, Prod.snd_add]`.

Rewrite using `[map_add, map_add, eb, eb']`. Simplify using `only [Prod.mk_add_mk, add_zero, Prod.fst_add]`. Rewrite using `[map_add]`. Conclude with `add_mem hc hc'`.
-/
theorem Dec.add {γ δ : Matrix (Fin n) (Fin d) (AE F E)} (h : Dec σ X W H H' X₁ W₁ v γ)
    (h' : Dec σ X W H H' X₁ W₁ v δ) : Dec σ X W H H' X₁ W₁ v (γ + δ) := by
  obtain ⟨⟨a, ha, ea⟩, ⟨b, hb, eb⟩, hc⟩ := h
  obtain ⟨⟨a', ha', ea'⟩, ⟨b', hb', eb'⟩, hc'⟩ := h'
  refine ⟨⟨a + a', add_mem ha ha', ?_⟩, ⟨b + b', add_mem hb hb', ?_⟩, ?_⟩
  · rw [map_add, map_add, ea, ea']; simp only [Prod.mk_add_mk, add_zero, Prod.fst_add, Prod.snd_add]
  · rw [map_add, map_add, eb, eb']; simp only [Prod.mk_add_mk, add_zero, Prod.fst_add]
  · rw [map_add]; exact add_mem hc hc'

/- English proof (translation)
Take `⟨⟨a, ha, ea⟩, ⟨b, hb, eb⟩, hc⟩` from `h`. Use `⟨⟨-a, neg_mem ha, ?_⟩, ⟨-b, neg_mem hb, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_neg, map_neg, ea]`. Simplify using `only [Prod.neg_mk, neg_zero, Prod.fst_neg, Prod.snd_neg]`. Rewrite using `[map_neg, map_neg, eb]`.

Simplify using `only [Prod.neg_mk, neg_zero, Prod.fst_neg]`. Rewrite using `[map_neg]`. Conclude with `neg_mem hc`.
-/
theorem Dec.neg {γ : Matrix (Fin n) (Fin d) (AE F E)} (h : Dec σ X W H H' X₁ W₁ v γ) :
    Dec σ X W H H' X₁ W₁ v (-γ) := by
  obtain ⟨⟨a, ha, ea⟩, ⟨b, hb, eb⟩, hc⟩ := h
  refine ⟨⟨-a, neg_mem ha, ?_⟩, ⟨-b, neg_mem hb, ?_⟩, ?_⟩
  · rw [map_neg, map_neg, ea]; simp only [Prod.neg_mk, neg_zero, Prod.fst_neg, Prod.snd_neg]
  · rw [map_neg, map_neg, eb]; simp only [Prod.neg_mk, neg_zero, Prod.fst_neg]
  · rw [map_neg]; exact neg_mem hc

/- English proof (translation)
Use `⟨⟨γ, hγ, Prod.ext (Prod.ext h.1 rfl) h.2⟩, ⟨0, zero_mem _, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, h.1]`. Both sides reduce to the same expression. Rewrite using `[h.2]`. Conclude with `zero_mem _`.
-/
theorem Dec.of_I {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v)
    (h : (planeT σ X W H H' γ).1.1 = 0 ∧ (planeT σ X W H H' γ).2 = 0) : Dec σ X W H H' X₁ W₁ v γ := by
  refine ⟨⟨γ, hγ, Prod.ext (Prod.ext h.1 rfl) h.2⟩, ⟨0, zero_mem _, ?_⟩, ?_⟩
  · rw [map_zero, h.1]; rfl
  · rw [h.2]; exact zero_mem _

/- English proof (translation)
Use `⟨⟨0, zero_mem _, ?_⟩, ⟨γ, hγ, Prod.ext (Prod.ext rfl h.1) h.2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, h.1]`. Both sides reduce to the same expression. Rewrite using `[h.2]`. Conclude with `zero_mem _`.
-/
theorem Dec.of_S {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v)
    (h : (planeT σ X W H H' γ).1.2 = 0 ∧ (planeT σ X W H H' γ).2 = 0) : Dec σ X W H H' X₁ W₁ v γ := by
  refine ⟨⟨0, zero_mem _, ?_⟩, ⟨γ, hγ, Prod.ext (Prod.ext rfl h.1) h.2⟩, ?_⟩
  · rw [map_zero, h.1]; rfl
  · rw [h.2]; exact zero_mem _

/- English proof (translation)
Use `⟨⟨0, zero_mem _, ?_⟩, ⟨0, zero_mem _, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, h]`. Both sides reduce to the same expression. Rewrite using `[map_zero, h]`. Both sides reduce to the same expression.

Rewrite using `[h]`. Conclude with `hz`.
-/
theorem Dec.of_block {γ : Matrix (Fin n) (Fin d) (AE F E)} {z : Matrix (Fin n₁) (Fin d₁) (AE F E)}
    (hz : z ∈ latAtV X₁ W₁ v) (h : planeT σ X W H H' γ = ((0, 0), z)) : Dec σ X W H H' X₁ W₁ v γ := by
  refine ⟨⟨0, zero_mem _, ?_⟩, ⟨0, zero_mem _, ?_⟩, ?_⟩
  · rw [map_zero, h]; rfl
  · rw [map_zero, h]; rfl
  · rw [h]; exact hz

end GlobalTheory.ThK.PlaneCo.LatDec

namespace GlobalTheory.ThK.PlaneCo.LatDec

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' hB hX hW hH hH' v γ hγ`. Express the relevant statement in the definitionally equal form `Dec σ X W H H' X₁ W₁ v γ`. Proceed by induction on `hγ using AddSubgroup.closure_induction with`. Consider the case `zero => exact Dec.zero`. Consider the case `add _ _ _ _ h h' => exact h.add h'`.

Consider the case `neg _ _ h => exact h.neg`. Consider the case `mem z hz`. Take `⟨a, ha, ha', x, hx, y, hy, rfl⟩` from `hz`. Take `⟨p, t, u, hp, ht, hu, ex⟩` from `hH.split x hx`. Take `⟨p', t', u', hp', ht', hu', ey⟩` from `hH'.split y hy`.

Establish `hιu` using `(hH.low u).1 hu`. Establish `mem : ∀ x ∈ X.L, ∀ y ∈ W.L, a • incM F (Matrix.vecMulVec x y) ∈ latAtV X W v` using `fun x hx y hy => AddSubgroup.subset_closure ⟨a, ha, ha', x, hx, y, hy, rfl⟩`. Establish `key : a • incM F (Matrix.vecMulVec x y) = a • incM F (Matrix.vecMulVec (p • H.x) y) + a • incM F (Matrix.vecMulVec (t • H.y) y) + a • incM F (Matrix.vecMulVec (H.ι *ᵥ u) (p' • H'.x)) + a • incM F (Matrix.vecMulVec (H.ι *ᵥ u) (t' • H'.y)) + a • incM F (Matrix.vecMulVec (H.ι *ᵥ u) …`. Simplify using `only [← smul_add]`. Use `congr 1`.

Use extensionality with `i j`. Simplify using `only [incM, Matrix.map_apply, Matrix.add_apply, Matrix.vecMulVec_apply, ← map_add]`. Use `congr 1`. Establish `e1` using `congrFun ex i`. Establish `e2` using `congrFun ey j`.

Simplify using `only [Pi.add_apply] at e1 e2`. Rewrite using `[e1]`. Take the linear combination `(H.ι *ᵥ u) i * e2`. Rewrite using `[key]`. Use `Dec.add (Dec.add (Dec.add (Dec.add ?_ ?_) ?_) ?_) ?_` and prove the remaining obligations.

Use `Dec.of_I (mem _ hp _ hy) (planeT_of_sI σ X W H H' _ ?_ ?_)` and prove the remaining obligations. Apply the tactic sequence `rintro (k | k) <;> simp only [sI, posS, coefLin_pure] <;> rw [planeCoef_mulVec_smul_x_eq_zero_of_ne H p (by simp)] <;> simp`. Introduce `i j; rw [coefLin_pure, planeCoef_mulVec_smul_x_eq_zero_of_ne H p (by simp)]; simp`. Use `Dec.of_S (mem _ ht _ hy) (planeT_of_tI σ X W H H' _ ?_ ?_)` and prove the remaining obligations. Apply the tactic sequence `rintro (k | k) <;> simp only [tI, posT, coefLin_pure] <;> rw [coef_y H t (by simp)] <;> simp`.

Introduce `i j; rw [coefLin_pure, coef_y H t (by simp)]; simp`. Use `Dec.of_I (mem _ hιu _ hp') (planeT_of_sI σ X W H H' _ ?_ ?_)` and prove the remaining obligations. Apply the tactic sequence `rintro (k | k) <;> simp only [sI, posS, coefLin_pure]`. Rewrite using `[coef_ι]`. Simplify using the standard rewrite rules.

Rewrite using `[planeCoef_mulVec_smul_x_eq_zero_of_ne H' p' (by simp)]; simp`. Introduce `i j; rw [coefLin_pure, planeCoef_mulVec_smul_x_eq_zero_of_ne H' p' (by simp)]; simp`. Use `Dec.of_S (mem _ hιu _ ht') (planeT_of_tI σ X W H H' _ ?_ ?_)` and prove the remaining obligations. Apply the tactic sequence `rintro (k | k) <;> simp only [tI, posT, coefLin_pure]`. Rewrite using `[coef_ι]`.

Simplify using the standard rewrite rules. Rewrite using `[coef_y H' t' (by simp)]; simp`. Introduce `i j; rw [coefLin_pure, coef_y H' t' (by simp)]; simp`. Use `Dec.of_block (z := a • incM F (Matrix.vecMulVec u u')) (AddSubgroup.subset_closure ⟨a, ha, ha', u, hu, u', hu', rfl⟩) ?_` and prove the remaining obligations. Rewrite using `[← BlockRead.planeT_block σ B X W X₁ W₁ H H' hB hX hW hH hH']`.

Use `congr 1`. Establish `e : Matrix.vecMulVec (H.ι *ᵥ u) (H'.ι *ᵥ u') = H.ι * Matrix.vecMulVec u u' * H'.ιᵀ`. Rewrite using `[Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]`. Rewrite using `[e, Matrix.mul_smul, Matrix.smul_mul]`. Simplify using `only [incM, Matrix.map_mul, Matrix.transpose_map]`.
-/
theorem latAtV_dec : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (v : Pl F), ∀ γ ∈ latAtV X W v,
    (∃ a ∈ latAtV X W v, planeT σ X W H H' a = ((0, (planeT σ X W H H' γ).1.2), 0)) ∧
    (∃ b ∈ latAtV X W v, planeT σ X W H H' b = (((planeT σ X W H H' γ).1.1, 0), 0)) ∧
    (planeT σ X W H H' γ).2 ∈ latAtV X₁ W₁ v := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' hB hX hW hH hH' v γ hγ
  change Dec σ X W H H' X₁ W₁ v γ
  induction hγ using AddSubgroup.closure_induction with
  | zero => exact Dec.zero
  | add _ _ _ _ h h' => exact h.add h'
  | neg _ _ h => exact h.neg
  | mem z hz =>
    obtain ⟨a, ha, ha', x, hx, y, hy, rfl⟩ := hz
    obtain ⟨p, t, u, hp, ht, hu, ex⟩ := hH.split x hx
    obtain ⟨p', t', u', hp', ht', hu', ey⟩ := hH'.split y hy
    have hιu := (hH.low u).1 hu
    have mem : ∀ x ∈ X.L, ∀ y ∈ W.L, a • incM F (Matrix.vecMulVec x y) ∈ latAtV X W v :=
      fun x hx y hy => AddSubgroup.subset_closure ⟨a, ha, ha', x, hx, y, hy, rfl⟩
    have key : a • incM F (Matrix.vecMulVec x y) =
        a • incM F (Matrix.vecMulVec (p • H.x) y) + a • incM F (Matrix.vecMulVec (t • H.y) y) +
        a • incM F (Matrix.vecMulVec (H.ι *ᵥ u) (p' • H'.x)) + a • incM F (Matrix.vecMulVec (H.ι *ᵥ u) (t' • H'.y)) +
        a • incM F (Matrix.vecMulVec (H.ι *ᵥ u) (H'.ι *ᵥ u')) := by
      simp only [← smul_add]
      congr 1
      ext i j
      simp only [incM, Matrix.map_apply, Matrix.add_apply, Matrix.vecMulVec_apply, ← map_add]
      congr 1
      have e1 := congrFun ex i
      have e2 := congrFun ey j
      simp only [Pi.add_apply] at e1 e2
      rw [e1]
      linear_combination (H.ι *ᵥ u) i * e2
    rw [key]
    refine Dec.add (Dec.add (Dec.add (Dec.add ?_ ?_) ?_) ?_) ?_
    · refine Dec.of_I (mem _ hp _ hy) (planeT_of_sI σ X W H H' _ ?_ ?_)
      · rintro (k | k) <;> simp only [sI, posS, coefLin_pure] <;> rw [planeCoef_mulVec_smul_x_eq_zero_of_ne H p (by simp)] <;> simp
      · intro i j; rw [coefLin_pure, planeCoef_mulVec_smul_x_eq_zero_of_ne H p (by simp)]; simp
    · refine Dec.of_S (mem _ ht _ hy) (planeT_of_tI σ X W H H' _ ?_ ?_)
      · rintro (k | k) <;> simp only [tI, posT, coefLin_pure] <;> rw [coef_y H t (by simp)] <;> simp
      · intro i j; rw [coefLin_pure, coef_y H t (by simp)]; simp
    · refine Dec.of_I (mem _ hιu _ hp') (planeT_of_sI σ X W H H' _ ?_ ?_)
      · rintro (k | k) <;> simp only [sI, posS, coefLin_pure]
        · rw [coef_ι]; simp
        · rw [planeCoef_mulVec_smul_x_eq_zero_of_ne H' p' (by simp)]; simp
      · intro i j; rw [coefLin_pure, planeCoef_mulVec_smul_x_eq_zero_of_ne H' p' (by simp)]; simp
    · refine Dec.of_S (mem _ hιu _ ht') (planeT_of_tI σ X W H H' _ ?_ ?_)
      · rintro (k | k) <;> simp only [tI, posT, coefLin_pure]
        · rw [coef_ι]; simp
        · rw [coef_y H' t' (by simp)]; simp
      · intro i j; rw [coefLin_pure, coef_y H' t' (by simp)]; simp
    · refine Dec.of_block (z := a • incM F (Matrix.vecMulVec u u'))
        (AddSubgroup.subset_closure ⟨a, ha, ha', u, hu, u', hu', rfl⟩) ?_
      rw [← BlockRead.planeT_block σ B X W X₁ W₁ H H' hB hX hW hH hH']
      congr 1
      have e : Matrix.vecMulVec (H.ι *ᵥ u) (H'.ι *ᵥ u') = H.ι * Matrix.vecMulVec u u' * H'.ιᵀ := by
        rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
      rw [e, Matrix.mul_smul, Matrix.smul_mul]
      simp only [incM, Matrix.map_mul, Matrix.transpose_map]

end GlobalTheory.ThK.PlaneCo.LatDec
