import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowEmbeddingMemIntegralOrthogonalGroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowIsometryEntriesInModelCoordinatesStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.LiftCorner

/- English proof (translation)
Establish `ha` using `a.isLt`. Establish `hj` using `j.isLt`. Simplify using `only [Hpk, eI, esI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
lemma hpk_eI (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) j = if j = esI k r a then 1 else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Rewrite using `[← hpk_eI]`. Simplify using `[herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply, apply_ite (starRingEnd ℂ), ite_mul]`.
-/
lemma herm_bvec (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) (x : ℂ) :
    herm (Hpk k r) (bvec j) (x • bvec (eI k r a)) = star x * (if j = esI k r a then 1 else 0) := by
  rw [← hpk_eI]
  simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply, apply_ite (starRingEnd ℂ), ite_mul]

/- English proof (translation)
Simplify using `[form, Matrix.mulVec_smul, dotProduct_smul]`.
-/
lemma form_smul_left {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (u v : Fin n → E) (x : E) : form σ J (x • u) v = x * form σ J u v := by
  simp [form, Matrix.mulVec_smul, dotProduct_smul]

/- English proof (translation)
Simplify using `[form, dotProduct, Finset.mul_sum, mul_assoc]`.
-/
lemma form_smul_right {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (u v : Fin n → E) (x : E) : form σ J u (x • v) = σ x * form σ J u v := by
  simp [form, dotProduct, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `only [form, pairM, cT, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]`. Conclude with `Finset.sum_comm`.
-/
lemma form_cols {E : Type} [Field E] (σ : E →+* E) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P : Matrix (Fin n) (Fin m) E) (x z : Fin m) :
    form σ J (fun i => P i z) (fun i => P i x) = pairM σ J P P x z := by
  simp only [form, pairM, cT, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ k r J Λ P f T A s hV p l hl`. Take `⟨⟨a, b⟩, hab⟩` from `p`. Establish `hab' : a.val < b.val` using `hab`. Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`.

Take `⟨-, -, -, -, hFr, -, hLat, -, -, hAd⟩` from `id hV`. Take `⟨c, hc, hlc⟩` from `hl`. Simplify using `only at hc hlc`. Set `e : Fin (2 * r + k + 1) → E` to `fun i => P i a.castSucc`. Set `y : Fin (2 * r + k + 1) → E` to `c • e`.

Establish `hiso : ∀ x z : Fin r, form (σ : E →+* E) J (fun i => P i z.castSucc) (fun i => P i x.castSucc) = 0`. Introduce `x z`. Rewrite using `[form_cols, hFr.2]`. Simplify using `[TF, Matrix.diagonal_apply, Fin.castSucc_ne_last]`. Establish `hd : ∀ j, dInv E j ≠ 0` using `fun j => pow_ne_zero _ (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot))`.

Establish `hG : rowE (σ : E →+* E) J (fun i => P i b.castSucc) y 0 ∈ GN (σ : E →+* E) J Λ P`. Use `GlobalTheory.T.rowE_mem_GN_of_form_add_trace_eq_zero F E σ k r J Λ P f T A s hV b y 0 ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `c' _ show form _ J (c • e) _ = 0`. Rewrite using `[form_smul_left, hiso, mul_zero]`. Use `show form _ J (c • e) (c • e) + 0 + (σ : E →+* E) 0 = 0`.

Rewrite using `[form_smul_left, form_smul_right, hiso]`. Simplify using the standard rewrite rules. Introduce `c' hc'`. Establish `hmem : c' * c ∈ dInv E (r - a.val)`. Use `FractionalIdeal.mul_mem_mul hc' hc` as an intermediate fact.

Rewrite `this` using `[mul_comm (dInv E (r - a.val)), ← mul_assoc, inv_mul_cancel₀ (hd _), one_mul]`. Then use the resulting hypothesis. Establish `hy : c' • y = (c' * c) • e`. Simplify using `only [y, smul_smul]`. Rewrite using `[hy]`. Apply `hLat` to reduce the goal to its premises.

Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨Fin.castAdd r a.castSucc, c' * c, ?_, ?_⟩` and prove the remaining obligations. Simplify `hmem` using `[id1, Fin.append_left]`. Use extensionality with `i`. Simplify using `[sideM, Fin.append_left, e]`.

Conclude with `(dInv E _ : Submodule (𝓞 E) E).zero_mem`. Establish `hAy : ∀ w : InfinitePlace E, (A w).mulVec (fun l => w.embedding (y l)) = (w.embedding c * (s a : ℂ)) • bvec (eI k r a)`. Introduce `w`. Establish `h1 : (fun l => w.embedding (y l)) = w.embedding c • fun l => w.embedding (P l a.castSucc)`. Use extensionality with `l`.

Simplify using `[y, e]`. Rewrite using `[h1, Matrix.mulVec_smul, (hAd w a).1, smul_smul]`. Establish `hent : ∀ w i j, gM A (rowE (σ : E →+* E) J (fun i => P i b.castSucc) y 0) w i j = (if i = j then 1 else 0) + (if i = eI k r a ∧ j = esI k r b then (s a : ℂ) * s b * w.embedding c else 0) - (if i = eI k r b ∧ j = esI k r a then (s b : ℂ) * star (w.embedding c * (s a : ℂ)) else 0)`. Introduce `w i j`. Rewrite using `[GlobalTheory.T.rowIsometry_entries_in_modelCoordinates F E σ k r J Λ P f T A s hV b y 0 w i j, hAy w, herm_bvec]`.

Simplify using `only [bvec, Pi.smul_apply, Pi.single_apply, smul_eq_mul, map_zero, mul_zero, add_zero, ite_and]`. Apply the tactic sequence `split_ifs <;> ring`. Use `⟨_, hG, fun w => ?_, fun β hβ _ w => ?_⟩` and prove the remaining obligations. Use `show gM A _ w (eI k r a) (esI k r b) = l w`. Rewrite using `[hent, hlc w]`.

Establish `h1 : eI k r a ≠ esI k r b` using `by simp [Fin.ext_iff, eI, esI]; omega`. Establish `h2 : eI k r a ≠ eI k r b` using `by simp [Fin.ext_iff, eI]; omega`. Simplify using `[h1, h2]`. Apply the tactic sequence `first | done | (push_cast; ring)`. Break down `β with p' | a' | p' | a'` into its components or cases.

Take `⟨⟨a', b'⟩, h'⟩` from `p'`. Establish `h'' : a'.val < b'.val` using `h'`. Use `show gM A _ w (eI k r a') (eI k r b') = 0`. Rewrite using `[hent]`. Simplify using `only [eI, esI, Fin.ext_iff]`.

Apply the tactic sequence `split_ifs <;> first | omega | simp`. Use `show (fun j' => gM A _ w (eI k r a') (wI k r j')) = (0 : Fin (k + 1) → ℂ)`. Use function extensionality and compare the values at `j'`. Use `j'.isLt` as an intermediate fact. Rewrite using `[hent]`.

Simplify using `only [eI, esI, wI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | omega | simp`. Take `⟨⟨a', b'⟩, h'⟩` from `p'`. Establish `h'' : a'.val < b'.val` using `h'`. Establish `hne : ¬ (a'.val = a.val ∧ b'.val = b.val)`.

Introduce and unpack `⟨e1, e2⟩`. Take `rfl` from `Fin.ext e1`. Take `rfl` from `Fin.ext e2`. Conclude with `hβ rfl`. Use `show gM A _ w (eI k r a') (esI k r b') = 0`.

Rewrite using `[hent]`. Simplify using `only [eI, esI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | omega | simp`. Use `show (gM A _ w (eI k r a') (esI k r a')).im = 0`. Rewrite using `[hent]`.

Simplify using `only [eI, esI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | omega | simp`.
-/
theorem lift_corner : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (p : UTr r) (l : InfinitePlace E → ℂ), l ∈ ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inr (.inl p))) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inr (.inl p))) → degB r β ≤ degB r (.inr (.inr (.inl p))) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV p l hl
  obtain ⟨⟨a, b⟩, hab⟩ := p
  have hab' : a.val < b.val := hab
  have ha := a.isLt
  have hb := b.isLt
  obtain ⟨-, -, -, -, hFr, -, hLat, -, -, hAd⟩ := id hV
  obtain ⟨c, hc, hlc⟩ := hl
  dsimp only at hc hlc
  let e : Fin (2 * r + k + 1) → E := fun i => P i a.castSucc
  let y : Fin (2 * r + k + 1) → E := c • e
  have hiso : ∀ x z : Fin r,
      form (σ : E →+* E) J (fun i => P i z.castSucc) (fun i => P i x.castSucc) = 0 := by
    intro x z
    rw [form_cols, hFr.2]
    simp [TF, Matrix.diagonal_apply, Fin.castSucc_ne_last]
  have hd : ∀ j, dInv E j ≠ 0 := fun j =>
    pow_ne_zero _ (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot))
  have hG : rowE (σ : E →+* E) J (fun i => P i b.castSucc) y 0 ∈ GN (σ : E →+* E) J Λ P := by
    refine GlobalTheory.T.rowE_mem_GN_of_form_add_trace_eq_zero F E σ k r J Λ P f T A s hV b y 0 ?_ ?_ ?_ ?_
    · intro c' _
      show form _ J (c • e) _ = 0
      rw [form_smul_left, hiso, mul_zero]
    · show form _ J (c • e) (c • e) + 0 + (σ : E →+* E) 0 = 0
      rw [form_smul_left, form_smul_right, hiso]
      simp
    · intro c' hc'
      have hmem : c' * c ∈ dInv E (r - a.val) := by
        have := FractionalIdeal.mul_mem_mul hc' hc
        rwa [mul_comm (dInv E (r - a.val)), ← mul_assoc, inv_mul_cancel₀ (hd _), one_mul] at this
      have hy : c' • y = (c' * c) • e := by
        simp only [y, smul_smul]
      rw [hy]
      apply hLat
      apply Submodule.subset_span
      refine ⟨Fin.castAdd r a.castSucc, c' * c, ?_, ?_⟩
      · simpa [id1, Fin.append_left] using hmem
      · ext i
        simp [sideM, Fin.append_left, e]
    · exact (dInv E _ : Submodule (𝓞 E) E).zero_mem
  have hAy : ∀ w : InfinitePlace E, (A w).mulVec (fun l => w.embedding (y l)) =
      (w.embedding c * (s a : ℂ)) • bvec (eI k r a) := by
    intro w
    have h1 : (fun l => w.embedding (y l)) = w.embedding c • fun l => w.embedding (P l a.castSucc) := by
      ext l
      simp [y, e]
    rw [h1, Matrix.mulVec_smul, (hAd w a).1, smul_smul]
  have hent : ∀ w i j, gM A (rowE (σ : E →+* E) J (fun i => P i b.castSucc) y 0) w i j =
      (if i = j then 1 else 0) +
        (if i = eI k r a ∧ j = esI k r b then (s a : ℂ) * s b * w.embedding c else 0) -
        (if i = eI k r b ∧ j = esI k r a then (s b : ℂ) * star (w.embedding c * (s a : ℂ)) else 0) := by
    intro w i j
    rw [GlobalTheory.T.rowIsometry_entries_in_modelCoordinates F E σ k r J Λ P f T A s hV b y 0 w i j, hAy w, herm_bvec]
    simp only [bvec, Pi.smul_apply, Pi.single_apply, smul_eq_mul, map_zero, mul_zero, add_zero, ite_and]
    split_ifs <;> ring
  refine ⟨_, hG, fun w => ?_, fun β hβ _ w => ?_⟩
  · show gM A _ w (eI k r a) (esI k r b) = l w
    rw [hent, hlc w]
    have h1 : eI k r a ≠ esI k r b := by simp [Fin.ext_iff, eI, esI]; omega
    have h2 : eI k r a ≠ eI k r b := by simp [Fin.ext_iff, eI]; omega
    simp [h1, h2]
    first | done | (push_cast; ring)
  · rcases β with p' | a' | p' | a'
    · obtain ⟨⟨a', b'⟩, h'⟩ := p'
      have h'' : a'.val < b'.val := h'
      show gM A _ w (eI k r a') (eI k r b') = 0
      rw [hent]
      simp only [eI, esI, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · show (fun j' => gM A _ w (eI k r a') (wI k r j')) = (0 : Fin (k + 1) → ℂ)
      funext j'
      have := j'.isLt
      rw [hent]
      simp only [eI, esI, wI, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · obtain ⟨⟨a', b'⟩, h'⟩ := p'
      have h'' : a'.val < b'.val := h'
      have hne : ¬ (a'.val = a.val ∧ b'.val = b.val) := by
        rintro ⟨e1, e2⟩
        obtain rfl := Fin.ext e1
        obtain rfl := Fin.ext e2
        exact hβ rfl
      show gM A _ w (eI k r a') (esI k r b') = 0
      rw [hent]
      simp only [eI, esI, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · show (gM A _ w (eI k r a') (esI k r a')).im = 0
      rw [hent]
      simp only [eI, esI, Fin.ext_iff]
      split_ifs <;> first | omega | simp

end GlobalTheory.SnMass.VolN.LiftCorner
