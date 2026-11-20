import Mathlib

noncomputable section

open Matrix

namespace UpperTheory.V.Cu.IrrKey

variable {K : Type} [Field K]

def tn (g t : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![g 0 0 * t 0 0, g 0 0 * t 0 1, -(g 0 1 * t 0 1), g 0 1 * t 0 0;
    g 0 0 * t 1 0, g 0 0 * t 1 1, -(g 0 1 * t 1 1), g 0 1 * t 1 0;
    -(g 1 0 * t 1 0), -(g 1 0 * t 1 1), g 1 1 * t 1 1, -(g 1 1 * t 1 0);
    g 1 0 * t 0 0, g 1 0 * t 0 1, -(g 1 1 * t 0 1), g 1 1 * t 0 0]

def Pm : Matrix (Fin 4) (Fin 2) K := !![1, 0; 1, 0; 0, -1; 0, 1]
def Mm : Matrix (Fin 4) (Fin 2) K := !![1, 0; -1, 0; 0, 1; 0, 1]
def Qp : Matrix (Fin 2) (Fin 4) K := !![(2 : K)⁻¹, (2 : K)⁻¹, 0, 0; 0, 0, -(2 : K)⁻¹, (2 : K)⁻¹]
def Qm : Matrix (Fin 2) (Fin 4) K := !![(2 : K)⁻¹, -(2 : K)⁻¹, 0, 0; 0, 0, (2 : K)⁻¹, (2 : K)⁻¹]

/- English proof (translation)
Take `⟨h1, h2⟩` from `h`. Use extensionality with `k`. Apply the tactic sequence `fin_cases k <;> simp [tn, Pm, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h1, h2] <;> ring`.
-/
theorem tnP_on (X B : Matrix (Fin 2) (Fin 2) K) (h : B 1 1 = B 0 0 ∧ B 1 0 = B 0 1) (x : Fin 2 → K) :
    tn X B *ᵥ (Pm *ᵥ x) = (B 0 0 + B 0 1) • (Pm *ᵥ (X *ᵥ x)) := by
  obtain ⟨h1, h2⟩ := h
  ext k
  fin_cases k <;> simp [tn, Pm, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h1, h2] <;> ring

/- English proof (translation)
Take `⟨h1, h2⟩` from `h`. Use extensionality with `k`. Apply the tactic sequence `fin_cases k <;> simp [tn, Mm, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h1, h2] <;> ring`.
-/
theorem tnM_on (X B : Matrix (Fin 2) (Fin 2) K) (h : B 1 1 = B 0 0 ∧ B 1 0 = B 0 1) (x : Fin 2 → K) :
    tn X B *ᵥ (Mm *ᵥ x) = (B 0 0 - B 0 1) • (Mm *ᵥ (X *ᵥ x)) := by
  obtain ⟨h1, h2⟩ := h
  ext k
  fin_cases k <;> simp [tn, Mm, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h1, h2] <;> ring

/- English proof (translation)
Take `⟨h1, h2⟩` from `h`. Use extensionality with `k`. Apply the tactic sequence `fin_cases k <;> simp [tn, Pm, Mm, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h1, h2] <;> ring`.
-/
theorem tnP_off (X B : Matrix (Fin 2) (Fin 2) K) (h : B 1 1 = -B 0 0 ∧ B 1 0 = -B 0 1) (x : Fin 2 → K) :
    tn X B *ᵥ (Pm *ᵥ x) = (B 0 0 + B 0 1) • (Mm *ᵥ (X *ᵥ x)) := by
  obtain ⟨h1, h2⟩ := h
  ext k
  fin_cases k <;> simp [tn, Pm, Mm, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h1, h2] <;> ring

/- English proof (translation)
Take `⟨h1, h2⟩` from `h`. Use extensionality with `k`. Apply the tactic sequence `fin_cases k <;> simp [tn, Pm, Mm, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h1, h2] <;> ring`.
-/
theorem tnM_off (X B : Matrix (Fin 2) (Fin 2) K) (h : B 1 1 = -B 0 0 ∧ B 1 0 = -B 0 1) (x : Fin 2 → K) :
    tn X B *ᵥ (Mm *ᵥ x) = (B 0 0 - B 0 1) • (Pm *ᵥ (X *ᵥ x)) := by
  obtain ⟨h1, h2⟩ := h
  ext k
  fin_cases k <;> simp [tn, Pm, Mm, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h1, h2] <;> ring

/- English proof (translation)
Take `⟨h1, h2⟩` from `h`. Use extensionality with `k`. Apply the tactic sequence `fin_cases k <;> simp [tn, Qp, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h1, h2] <;> ring`.
-/
theorem Qp_tn (X B : Matrix (Fin 2) (Fin 2) K) (h : B 1 1 = B 0 0 ∧ B 1 0 = B 0 1) (v : Fin 4 → K) :
    Qp *ᵥ (tn X B *ᵥ v) = (B 0 0 + B 0 1) • (X *ᵥ (Qp *ᵥ v)) := by
  obtain ⟨h1, h2⟩ := h
  ext k
  fin_cases k <;> simp [tn, Qp, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h1, h2] <;> ring

/- English proof (translation)
Establish `h2' : (2 : K)⁻¹ + 2⁻¹ = 1` using `by rw [← two_mul, mul_inv_cancel₀ h2]`. Use extensionality with `k`. Apply the tactic sequence `fin_cases k <;> simp [Pm, Qp, Mm, Qm, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]`. Take the linear combination `(v 0) * h2'`. Take the linear combination `(v 1) * h2'`.

Take the linear combination `(v 2) * h2'`. Take the linear combination `(v 3) * h2'`.
-/
theorem dec (h2 : (2 : K) ≠ 0) (v : Fin 4 → K) : Pm *ᵥ (Qp *ᵥ v) + Mm *ᵥ (Qm *ᵥ v) = v := by
  have h2' : (2 : K)⁻¹ + 2⁻¹ = 1 := by rw [← two_mul, mul_inv_cancel₀ h2]
  ext k
  fin_cases k <;> simp [Pm, Qp, Mm, Qm, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · linear_combination (v 0) * h2'
  · linear_combination (v 1) * h2'
  · linear_combination (v 2) * h2'
  · linear_combination (v 3) * h2'

/- English proof (translation)
Establish `hdec : ∀ v : Fin 4 → K, Pm *ᵥ (Qp *ᵥ v) + Mm *ᵥ (Qm *ᵥ v) = v` using `dec h2`. Establish `aP : ∀ i ∈ On, ∀ x, tn (A i) (B i) *ᵥ (Pm *ᵥ x) = (B i 0 0 + B i 0 1) • (Pm *ᵥ (A i *ᵥ x))` using `fun i hi x => tnP_on (A i) (B i) (hon i hi) x`. Establish `aM : ∀ i ∈ On, ∀ x, tn (A i) (B i) *ᵥ (Mm *ᵥ x) = (B i 0 0 - B i 0 1) • (Mm *ᵥ (A i *ᵥ x))` using `fun i hi x => tnM_on (A i) (B i) (hon i hi) x`. Establish `aPt : ∀ x, tn (A t) (B t) *ᵥ (Pm *ᵥ x) = (B t 0 0 + B t 0 1) • (Mm *ᵥ (A t *ᵥ x))` using `fun x => tnP_off (A t) (B t) hoff x`. Establish `aMt : ∀ x, tn (A t) (B t) *ᵥ (Mm *ᵥ x) = (B t 0 0 - B t 0 1) • (Pm *ᵥ (A t *ᵥ x))` using `fun x => tnM_off (A t) (B t) hoff x`.

Establish `hdetBt : (B t).det = -((B t 0 0 + B t 0 1) * (B t 0 0 - B t 0 1))`. Rewrite using `[Matrix.det_fin_two, hoff.1, hoff.2]`. Expand and normalize the polynomial expressions, which then agree. Establish `kpt : B t 0 0 + B t 0 1 ≠ 0` using `fun h => hBt (by rw [hdetBt, h, zero_mul, neg_zero])`. Establish `kmt : B t 0 0 - B t 0 1 ≠ 0` using `fun h => hBt (by rw [hdetBt, h, mul_zero, neg_zero])`.

Establish `surjt : ∀ y, ∃ x, A t *ᵥ x = y` using `fun y => ⟨(A t)⁻¹ *ᵥ y, by rw [mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit hAt), one_mulVec]⟩`. Establish `unsc : ∀ (c : K) (w : Fin 4 → K), c ≠ 0 → c • w ∈ W → w ∈ W` using `fun c w hc h => by`. Use `W.smul_mem c⁻¹ h` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hc, one_smul]`. Then use the resulting hypothesis. Establish `hP` using `hirr (W.comap (Matrix.mulVecLin Pm)) (by`.

Introduce `i hi v hv`. Simplify using `only [Submodule.mem_comap, Matrix.mulVecLin_apply] at hv ⊢`. Use `hW i (Or.inl hi) _ hv` as an intermediate fact. Rewrite `this` using `[aP i hi]`. Conclude with `unsc _ _ (hkp i hi) this)`.

Establish `hM` using `hirr (W.comap (Matrix.mulVecLin Mm)) (by`. Introduce `i hi v hv`. Simplify using `only [Submodule.mem_comap, Matrix.mulVecLin_apply] at hv ⊢`. Use `hW i (Or.inl hi) _ hv` as an intermediate fact. Rewrite `this` using `[aM i hi]`.

Conclude with `unsc _ _ (hkm i hi) this)`. Establish `hI` using `hirr (W.map (Matrix.mulVecLin Qp)) (by`. Introduce `i hi x hx`. Take `⟨v, hv, rfl⟩` from `Submodule.mem_map.1 hx`. Use `Submodule.mem_map.2 ⟨(B i 0 0 + B i 0 1)⁻¹ • (tn (A i) (B i) *ᵥ v), W.smul_mem _ (hW i (Or.inl hi) v hv), ?_⟩` and prove the remaining obligations.

Simplify using `only [Matrix.mulVecLin_apply]`. Rewrite using `[mulVec_smul, Qp_tn (A i) (B i) (hon i hi), smul_smul, inv_mul_cancel₀ (hkp i hi), one_smul])`. Establish `memP : W.comap (Matrix.mulVecLin Pm) = ⊤ → ∀ x, Pm *ᵥ x ∈ W` using `fun h x => by`. Establish `: x ∈ W.comap (Matrix.mulVecLin Pm)` using `h ▸ Submodule.mem_top`. Simplify using `using this`.

Establish `memM : W.comap (Matrix.mulVecLin Mm) = ⊤ → ∀ x, Mm *ᵥ x ∈ W` using `fun h x => by`. Establish `: x ∈ W.comap (Matrix.mulVecLin Mm)` using `h ▸ Submodule.mem_top`. Simplify using `using this`. Break down `hP with hP | hP` into its components or cases. Use `swap`.

Use `right`. Rewrite using `[eq_top_iff]`. Introduce `v _`. Rewrite using `[← hdec v]`. Use `W.add_mem (memP hP _) ?_` and prove the remaining obligations.

Take `⟨x, hx⟩` from `surjt (Qm *ᵥ v)`. Establish `h1` using `hW t (Or.inr rfl) _ (memP hP x)`. Rewrite `h1` using `[aPt, hx]`. Conclude with `unsc _ _ kpt h1`. Break down `hM with hM | hM` into its components or cases.

Use `swap`. Use `right`. Rewrite using `[eq_top_iff]`. Introduce `v _`. Rewrite using `[← hdec v]`.

Use `W.add_mem ?_ (memM hM _)` and prove the remaining obligations. Take `⟨x, hx⟩` from `surjt (Qp *ᵥ v)`. Establish `h1` using `hW t (Or.inr rfl) _ (memM hM x)`. Rewrite `h1` using `[aMt, hx]`. Conclude with `unsc _ _ kmt h1`.

Establish `inj : ∀ x, Pm *ᵥ x ∈ W → x = 0` using `fun x hx => by`. Establish `: x ∈ W.comap (Matrix.mulVecLin Pm)` using `by simpa using hx`. Rewrite `this` using `[hP]`. Simplify using `using this`. Establish `injM : ∀ y, Mm *ᵥ y ∈ W → y = 0` using `fun y hy => by`.

Establish `: y ∈ W.comap (Matrix.mulVecLin Mm)` using `by simpa using hy`. Rewrite `this` using `[hM]`. Simplify using `using this`. Break down `hI with hI | hI` into its components or cases. Use `left`.

Rewrite using `[eq_bot_iff]`. Introduce `v hv`. Establish `h1 : Qp *ᵥ v = 0`. Establish `: Qp *ᵥ v ∈ W.map (Matrix.mulVecLin Qp)` using `Submodule.mem_map_of_mem hv`. Rewrite `this` using `[hI]`.

Simplify using `using this`. Establish `h3 : Mm *ᵥ (Qm *ᵥ v) ∈ W`. Establish `e` using `hdec v`. Rewrite `e` using `[h1, mulVec_zero, zero_add]`. Rewrite using `[e]`.

Conclude with `hv`. Establish `h4` using `injM _ h3`. Rewrite using `[Submodule.mem_bot, ← hdec v, h1, h4, mulVec_zero, mulVec_zero, add_zero]`. It suffices to derive a contradiction. Establish `hex : ∀ j : Fin 2, ∃ w ∈ W, Qp *ᵥ w = Pi.single j 1` using `fun j => by`.

Establish `: (Pi.single j (1 : K) : Fin 2 → K) ∈ W.map (Matrix.mulVecLin Qp)` using `hI ▸ Submodule.mem_top`. Take `⟨w, hw, e⟩` from `Submodule.mem_map.1 this`. Conclude with `⟨w, hw, e⟩`. Use `choose w hwW hwQ using hex`. Set `Wt : Matrix (Fin 4) (Fin 2) K` to `Matrix.of fun a j => w j a`.

Establish `hWt : ∀ x, Wt *ᵥ x ∈ W` using `fun x => by`. Establish `e : Wt *ᵥ x = x 0 • w 0 + x 1 • w 1`. Use extensionality with `a`. Simplify using `[Wt, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]`. Rewrite using `[e]`.

Conclude with `W.add_mem (W.smul_mem _ (hwW 0)) (W.smul_mem _ (hwW 1))`. Establish `hQW : ∀ x, Qp *ᵥ (Wt *ᵥ x) = x` using `fun x => by`. Establish `e : Wt *ᵥ x = x 0 • w 0 + x 1 • w 1`. Use extensionality with `a`. Simplify using `[Wt, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]`.

Rewrite using `[e, mulVec_add, mulVec_smul, mulVec_smul, hwQ, hwQ]`. Use extensionality with `k`. Apply the tactic sequence `fin_cases k <;> simp`. Establish `hG : ∀ x, Pm *ᵥ x + Mm *ᵥ (Qm *ᵥ (Wt *ᵥ x)) ∈ W` using `fun x => by`. Establish `e` using `hdec (Wt *ᵥ x)`.

Rewrite `e` using `[hQW]`. Rewrite using `[e]`. Conclude with `hWt x`. Establish `huniq : ∀ x y, Pm *ᵥ x + Mm *ᵥ y ∈ W → y = Qm *ᵥ (Wt *ᵥ x)` using `fun x y h => by`. Establish `h1` using `W.sub_mem h (hG x)`.

Rewrite `h1` using `[add_sub_add_left_eq_sub, ← mulVec_sub]`. Conclude with `sub_eq_zero.1 (injM _ h1)`. Take `⟨Φ, hΦ⟩ : ∃ Φ : Matrix (Fin 2) (Fin 2) K, ∀ x, Φ *ᵥ x = Qm *ᵥ (Wt *ᵥ x)` from `⟨Qm * Wt, fun x => (Matrix.mulVec_mulVec x Qm Wt).symm⟩`. Establish `hΦdet : Φ.det ≠ 0`. Introduce `hd`.

Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hd`. Rewrite `hv` using `[hΦ]`. Apply `hv0` to reduce the goal to its premises. Apply `inj` to reduce the goal to its premises. Use `hG v` as an intermediate fact.

Rewrite `this` using `[hv, mulVec_zero, add_zero]`. Then use the resulting hypothesis. Establish `hkp0` using `hkp u hu`. Establish `heq : ∀ x, ((B u 0 0 + B u 0 1)⁻¹ * (B u 0 0 - B u 0 1)) • (A u *ᵥ (Qm *ᵥ (Wt *ᵥ x))) = Qm *ᵥ (Wt *ᵥ (A u *ᵥ x))` using `fun x => by`. Establish `h1` using `hW u (Or.inl hu) _ (hG x)`. Rewrite `h1` using `[mulVec_add, aP u hu, aM u hu]`.

Establish `h2` using `W.smul_mem (B u 0 0 + B u 0 1)⁻¹ h1`. Rewrite `h2` using `[smul_add, smul_smul, inv_mul_cancel₀ hkp0, one_smul, smul_smul, ← mulVec_smul]`. Conclude with `(huniq _ _ h2)`. Establish `hmat : ((B u 0 0 + B u 0 1)⁻¹ * (B u 0 0 - B u 0 1)) • (A u * Φ) = Φ * A u`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises.

Rewrite using `[map_smul, Matrix.toLin'_mul, Matrix.toLin'_mul]`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Rewrite using `[LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, hΦ, hΦ, heq]`. Establish `hd` using `congrArg Matrix.det hmat`.

Rewrite `hd` using `[Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Fintype.card_fin]`. Establish `hc : ((B u 0 0 + B u 0 1)⁻¹ * (B u 0 0 - B u 0 1)) ^ 2 = 1`. Establish `hne0 : (A u).det * Φ.det ≠ 0` using `mul_ne_zero hAu hΦdet`. Use `mul_right_cancel₀ hne0 ?_` and prove the remaining obligations. Rewrite using `[hd, one_mul, mul_comm]`.

Apply `hne` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hc, mul_one]`. Use `_ = (B u 0 0 - B u 0 1) ^ 2 := by`. Rewrite using `[mul_pow, inv_pow, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hkp0), one_mul]`.
-/
theorem key {ι : Type} (h2 : (2 : K) ≠ 0) (On : Set ι) (A B : ι → Matrix (Fin 2) (Fin 2) K)
    (hon : ∀ i ∈ On, B i 1 1 = B i 0 0 ∧ B i 1 0 = B i 0 1)
    (hkp : ∀ i ∈ On, B i 0 0 + B i 0 1 ≠ 0) (hkm : ∀ i ∈ On, B i 0 0 - B i 0 1 ≠ 0)
    (hirr : ∀ V : Submodule K (Fin 2 → K), (∀ i ∈ On, ∀ v ∈ V, A i *ᵥ v ∈ V) → V = ⊥ ∨ V = ⊤)
    (t : ι) (hoff : B t 1 1 = -B t 0 0 ∧ B t 1 0 = -B t 0 1) (hBt : (B t).det ≠ 0) (hAt : (A t).det ≠ 0)
    (u : ι) (hu : u ∈ On) (hAu : (A u).det ≠ 0)
    (hne : (B u 0 0 + B u 0 1) ^ 2 ≠ (B u 0 0 - B u 0 1) ^ 2)
    (W : Submodule K (Fin 4 → K)) (hW : ∀ i, (i ∈ On ∨ i = t) → ∀ v ∈ W, tn (A i) (B i) *ᵥ v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  have hdec : ∀ v : Fin 4 → K, Pm *ᵥ (Qp *ᵥ v) + Mm *ᵥ (Qm *ᵥ v) = v := dec h2
  have aP : ∀ i ∈ On, ∀ x, tn (A i) (B i) *ᵥ (Pm *ᵥ x) = (B i 0 0 + B i 0 1) • (Pm *ᵥ (A i *ᵥ x)) :=
    fun i hi x => tnP_on (A i) (B i) (hon i hi) x
  have aM : ∀ i ∈ On, ∀ x, tn (A i) (B i) *ᵥ (Mm *ᵥ x) = (B i 0 0 - B i 0 1) • (Mm *ᵥ (A i *ᵥ x)) :=
    fun i hi x => tnM_on (A i) (B i) (hon i hi) x
  have aPt : ∀ x, tn (A t) (B t) *ᵥ (Pm *ᵥ x) = (B t 0 0 + B t 0 1) • (Mm *ᵥ (A t *ᵥ x)) :=
    fun x => tnP_off (A t) (B t) hoff x
  have aMt : ∀ x, tn (A t) (B t) *ᵥ (Mm *ᵥ x) = (B t 0 0 - B t 0 1) • (Pm *ᵥ (A t *ᵥ x)) :=
    fun x => tnM_off (A t) (B t) hoff x
  have hdetBt : (B t).det = -((B t 0 0 + B t 0 1) * (B t 0 0 - B t 0 1)) := by
    rw [Matrix.det_fin_two, hoff.1, hoff.2]; ring
  have kpt : B t 0 0 + B t 0 1 ≠ 0 := fun h => hBt (by rw [hdetBt, h, zero_mul, neg_zero])
  have kmt : B t 0 0 - B t 0 1 ≠ 0 := fun h => hBt (by rw [hdetBt, h, mul_zero, neg_zero])
  have surjt : ∀ y, ∃ x, A t *ᵥ x = y := fun y =>
    ⟨(A t)⁻¹ *ᵥ y, by rw [mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit hAt), one_mulVec]⟩
  have unsc : ∀ (c : K) (w : Fin 4 → K), c ≠ 0 → c • w ∈ W → w ∈ W := fun c w hc h => by
    have := W.smul_mem c⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have hP := hirr (W.comap (Matrix.mulVecLin Pm)) (by
    intro i hi v hv
    simp only [Submodule.mem_comap, Matrix.mulVecLin_apply] at hv ⊢
    have := hW i (Or.inl hi) _ hv
    rw [aP i hi] at this
    exact unsc _ _ (hkp i hi) this)
  have hM := hirr (W.comap (Matrix.mulVecLin Mm)) (by
    intro i hi v hv
    simp only [Submodule.mem_comap, Matrix.mulVecLin_apply] at hv ⊢
    have := hW i (Or.inl hi) _ hv
    rw [aM i hi] at this
    exact unsc _ _ (hkm i hi) this)
  have hI := hirr (W.map (Matrix.mulVecLin Qp)) (by
    intro i hi x hx
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hx
    refine Submodule.mem_map.2 ⟨(B i 0 0 + B i 0 1)⁻¹ • (tn (A i) (B i) *ᵥ v), W.smul_mem _ (hW i (Or.inl hi) v hv), ?_⟩
    simp only [Matrix.mulVecLin_apply]
    rw [mulVec_smul, Qp_tn (A i) (B i) (hon i hi), smul_smul, inv_mul_cancel₀ (hkp i hi), one_smul])
  have memP : W.comap (Matrix.mulVecLin Pm) = ⊤ → ∀ x, Pm *ᵥ x ∈ W := fun h x => by
    have : x ∈ W.comap (Matrix.mulVecLin Pm) := h ▸ Submodule.mem_top
    simpa using this
  have memM : W.comap (Matrix.mulVecLin Mm) = ⊤ → ∀ x, Mm *ᵥ x ∈ W := fun h x => by
    have : x ∈ W.comap (Matrix.mulVecLin Mm) := h ▸ Submodule.mem_top
    simpa using this
  rcases hP with hP | hP
  swap
  · right
    rw [eq_top_iff]
    intro v _
    rw [← hdec v]
    refine W.add_mem (memP hP _) ?_
    obtain ⟨x, hx⟩ := surjt (Qm *ᵥ v)
    have h1 := hW t (Or.inr rfl) _ (memP hP x)
    rw [aPt, hx] at h1
    exact unsc _ _ kpt h1
  rcases hM with hM | hM
  swap
  · right
    rw [eq_top_iff]
    intro v _
    rw [← hdec v]
    refine W.add_mem ?_ (memM hM _)
    obtain ⟨x, hx⟩ := surjt (Qp *ᵥ v)
    have h1 := hW t (Or.inr rfl) _ (memM hM x)
    rw [aMt, hx] at h1
    exact unsc _ _ kmt h1
  have inj : ∀ x, Pm *ᵥ x ∈ W → x = 0 := fun x hx => by
    have : x ∈ W.comap (Matrix.mulVecLin Pm) := by simpa using hx
    rw [hP] at this
    simpa using this
  have injM : ∀ y, Mm *ᵥ y ∈ W → y = 0 := fun y hy => by
    have : y ∈ W.comap (Matrix.mulVecLin Mm) := by simpa using hy
    rw [hM] at this
    simpa using this
  rcases hI with hI | hI
  · left
    rw [eq_bot_iff]
    intro v hv
    have h1 : Qp *ᵥ v = 0 := by
      have : Qp *ᵥ v ∈ W.map (Matrix.mulVecLin Qp) := Submodule.mem_map_of_mem hv
      rw [hI] at this
      simpa using this
    have h3 : Mm *ᵥ (Qm *ᵥ v) ∈ W := by
      have e := hdec v
      rw [h1, mulVec_zero, zero_add] at e
      rw [e]
      exact hv
    have h4 := injM _ h3
    rw [Submodule.mem_bot, ← hdec v, h1, h4, mulVec_zero, mulVec_zero, add_zero]
  · exfalso
    have hex : ∀ j : Fin 2, ∃ w ∈ W, Qp *ᵥ w = Pi.single j 1 := fun j => by
      have : (Pi.single j (1 : K) : Fin 2 → K) ∈ W.map (Matrix.mulVecLin Qp) := hI ▸ Submodule.mem_top
      obtain ⟨w, hw, e⟩ := Submodule.mem_map.1 this
      exact ⟨w, hw, e⟩
    choose w hwW hwQ using hex
    let Wt : Matrix (Fin 4) (Fin 2) K := Matrix.of fun a j => w j a
    have hWt : ∀ x, Wt *ᵥ x ∈ W := fun x => by
      have e : Wt *ᵥ x = x 0 • w 0 + x 1 • w 1 := by
        ext a
        simp [Wt, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
      rw [e]
      exact W.add_mem (W.smul_mem _ (hwW 0)) (W.smul_mem _ (hwW 1))
    have hQW : ∀ x, Qp *ᵥ (Wt *ᵥ x) = x := fun x => by
      have e : Wt *ᵥ x = x 0 • w 0 + x 1 • w 1 := by
        ext a
        simp [Wt, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
      rw [e, mulVec_add, mulVec_smul, mulVec_smul, hwQ, hwQ]
      ext k
      fin_cases k <;> simp
    have hG : ∀ x, Pm *ᵥ x + Mm *ᵥ (Qm *ᵥ (Wt *ᵥ x)) ∈ W := fun x => by
      have e := hdec (Wt *ᵥ x)
      rw [hQW] at e
      rw [e]
      exact hWt x
    have huniq : ∀ x y, Pm *ᵥ x + Mm *ᵥ y ∈ W → y = Qm *ᵥ (Wt *ᵥ x) := fun x y h => by
      have h1 := W.sub_mem h (hG x)
      rw [add_sub_add_left_eq_sub, ← mulVec_sub] at h1
      exact sub_eq_zero.1 (injM _ h1)
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : Matrix (Fin 2) (Fin 2) K, ∀ x, Φ *ᵥ x = Qm *ᵥ (Wt *ᵥ x) :=
      ⟨Qm * Wt, fun x => (Matrix.mulVec_mulVec x Qm Wt).symm⟩
    have hΦdet : Φ.det ≠ 0 := by
      intro hd
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
      rw [hΦ] at hv
      apply hv0
      apply inj
      have := hG v
      rwa [hv, mulVec_zero, add_zero] at this
    have hkp0 := hkp u hu
    have heq : ∀ x, ((B u 0 0 + B u 0 1)⁻¹ * (B u 0 0 - B u 0 1)) • (A u *ᵥ (Qm *ᵥ (Wt *ᵥ x))) =
        Qm *ᵥ (Wt *ᵥ (A u *ᵥ x)) := fun x => by
      have h1 := hW u (Or.inl hu) _ (hG x)
      rw [mulVec_add, aP u hu, aM u hu] at h1
      have h2 := W.smul_mem (B u 0 0 + B u 0 1)⁻¹ h1
      rw [smul_add, smul_smul, inv_mul_cancel₀ hkp0, one_smul, smul_smul, ← mulVec_smul] at h2
      exact (huniq _ _ h2)
    have hmat : ((B u 0 0 + B u 0 1)⁻¹ * (B u 0 0 - B u 0 1)) • (A u * Φ) = Φ * A u := by
      apply Matrix.toLin'.injective
      rw [map_smul, Matrix.toLin'_mul, Matrix.toLin'_mul]
      apply LinearMap.ext
      intro x
      rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
        Matrix.toLin'_apply, Matrix.toLin'_apply, hΦ, hΦ, heq]
    have hd := congrArg Matrix.det hmat
    rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Fintype.card_fin] at hd
    have hc : ((B u 0 0 + B u 0 1)⁻¹ * (B u 0 0 - B u 0 1)) ^ 2 = 1 := by
      have hne0 : (A u).det * Φ.det ≠ 0 := mul_ne_zero hAu hΦdet
      refine mul_right_cancel₀ hne0 ?_
      rw [hd, one_mul, mul_comm]
    apply hne
    calc (B u 0 0 + B u 0 1) ^ 2 = (B u 0 0 + B u 0 1) ^ 2 * ((B u 0 0 + B u 0 1)⁻¹ * (B u 0 0 - B u 0 1)) ^ 2 := by
          rw [hc, mul_one]
    _ = (B u 0 0 - B u 0 1) ^ 2 := by
          rw [mul_pow, inv_pow, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hkp0), one_mul]

end UpperTheory.V.Cu.IrrKey

end
