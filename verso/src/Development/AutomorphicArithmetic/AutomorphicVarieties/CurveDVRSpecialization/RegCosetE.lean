import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FullEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SepOfMinors
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExpSums
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiagonalEntries

open Matrix Polynomial

namespace UpperTheory.V.Pr

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.DiagonalizeTwoByTwo.diagE M α hα h`.
-/
private lemma diagE {κ : Type} [Field κ] (M : Matrix (Fin 2) (Fin 2) κ) (α : Fin 2 → κ)
    (hα : Function.Injective α) (h : M.charpoly = ∏ i, (X - C (α i))) :
    ∃ P : GL (Fin 2) κ, M * (P : Matrix (Fin 2) (Fin 2) κ) = (P : Matrix (Fin 2) (Fin 2) κ) * diagonal α :=
  _root_.UpperTheory.Reformulated.B.DiagonalizeTwoByTwo.diagE M α hα h

/- English proof (translation)
Introduce `W S hS hW`. Use `set A : Matrix (Fin n) (Fin n) κ := (P : Matrix (Fin n) (Fin n) κ) with hA`. Use `set B : Matrix (Fin n) (Fin n) κ := ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) with hB`. Establish `hAB : ∀ v, A *ᵥ (B *ᵥ v) = v` using `fun v => by rw [mulVec_mulVec, hA, hB, Units.mul_inv, one_mulVec]`. Establish `hBA : ∀ v, B *ᵥ (A *ᵥ v) = v` using `fun v => by rw [mulVec_mulVec, hA, hB, Units.inv_mul, one_mulVec]`.

Establish `hg : ∀ g v, gm ((MulAut.conj P⁻¹).toMonoidHom.comp r) g *ᵥ v = B *ᵥ (gm r g *ᵥ (A *ᵥ v))`. Introduce `g v`. Rewrite using `[mulVec_mulVec, mulVec_mulVec]`. Both sides reduce to the same expression. Establish `hm : ∀ v, v ∈ W.comap (Matrix.toLin' B) ↔ B *ᵥ v ∈ W` using `fun v => by`.

Rewrite using `[Submodule.mem_comap, toLin'_apply]`. Establish `key` using `h (W.comap (Matrix.toLin' B)) S hS (by`. Introduce `g`. Rewrite using `[hW g]`. Prove the components needed by the constructor for the conclusion.

Introduce `h1 v hv`. Use `h1 _ ((hm v).1 hv)` as an intermediate fact. Rewrite `this` using `[hg, hAB]`. Conclude with `(hm _).2 this`. Introduce `h1 v hv`.

Rewrite using `[hg, ← hm]`. Conclude with `h1 _ (by rw [hm, hBA]; exact hv))`. Break down `key with key | key` into its components or cases. Use `left`. Rewrite using `[eq_bot_iff]`.

Introduce `v hv`. Establish `: A *ᵥ v ∈ W.comap (Matrix.toLin' B)` using `by rw [hm, hBA]; exact hv`. Rewrite `this` using `[key, Submodule.mem_bot]`. Rewrite using `[Submodule.mem_bot, ← hBA v, this, mulVec_zero]`. Use `right`.

Rewrite using `[eq_top_iff]`. Introduce `v _`. Establish `: A *ᵥ v ∈ W.comap (Matrix.toLin' B)` using `by rw [key]; trivial`. Rewrite `this` using `[hm, hBA]`. Then use the resulting hypothesis.
-/
private lemma strongIrr_conjE {G κ : Type} [Group G] [Field κ] {n : ℕ} (r : G →* GL (Fin n) κ) (h : StrongIrr r)
    (P : GL (Fin n) κ) : StrongIrr ((MulAut.conj P⁻¹).toMonoidHom.comp r) := by
  intro W S hS hW
  set A : Matrix (Fin n) (Fin n) κ := (P : Matrix (Fin n) (Fin n) κ) with hA
  set B : Matrix (Fin n) (Fin n) κ := ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) with hB
  have hAB : ∀ v, A *ᵥ (B *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hA, hB, Units.mul_inv, one_mulVec]
  have hBA : ∀ v, B *ᵥ (A *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hA, hB, Units.inv_mul, one_mulVec]
  have hg : ∀ g v, gm ((MulAut.conj P⁻¹).toMonoidHom.comp r) g *ᵥ v = B *ᵥ (gm r g *ᵥ (A *ᵥ v)) := by
    intro g v
    rw [mulVec_mulVec, mulVec_mulVec]
    rfl
  have hm : ∀ v, v ∈ W.comap (Matrix.toLin' B) ↔ B *ᵥ v ∈ W := fun v => by
    rw [Submodule.mem_comap, toLin'_apply]
  have key := h (W.comap (Matrix.toLin' B)) S hS (by
    intro g
    rw [hW g]
    constructor
    · intro h1 v hv
      have := h1 _ ((hm v).1 hv)
      rw [hg, hAB] at this
      exact (hm _).2 this
    · intro h1 v hv
      rw [hg, ← hm]
      exact h1 _ (by rw [hm, hBA]; exact hv))
  rcases key with key | key
  · left
    rw [eq_bot_iff]
    intro v hv
    have : A *ᵥ v ∈ W.comap (Matrix.toLin' B) := by rw [hm, hBA]; exact hv
    rw [key, Submodule.mem_bot] at this
    rw [Submodule.mem_bot, ← hBA v, this, mulVec_zero]
  · right
    rw [eq_top_iff]
    intro v _
    have : A *ᵥ v ∈ W.comap (Matrix.toLin' B) := by rw [key]; trivial
    rwa [hm, hBA] at this

private def blkE {κ : Type} [Field κ] (M : Matrix (Fin 2) (Fin 2) κ) (w : κ) : Matrix (Fin 3) (Fin 3) κ :=
  !![M 0 0, M 0 1, 0; M 1 0, M 1 1, 0; 0, 0, w]

/- English proof (translation)
Simplify using `only [Matrix.charpoly, det_fin_three, det_fin_two]`. Simplify using `[blkE, charmatrix_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma charpoly_blkE {κ : Type} [Field κ] (M : Matrix (Fin 2) (Fin 2) κ) (w : κ) :
    (blkE M w).charpoly = M.charpoly * (X - C w) := by
  simp only [Matrix.charpoly, det_fin_three, det_fin_two]
  simp [blkE, charmatrix_apply]
  ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [diagonal_pow, mul_diagonal, blkE]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [h0, h1, h2]`.
-/
private lemma blkE_mul {κ : Type} [Field κ] (M : Matrix (Fin 2) (Fin 2) κ) (w : κ) (a : Fin 2 → κ) (c : κ) (m : ℕ)
    (d : Fin 3 → κ) (h0 : d 0 = a 0) (h1 : d 1 = a 1) (h2 : d 2 = c) :
    blkE M w * diagonal d ^ m = blkE (M * diagonal a ^ m) (w * c ^ m) := by
  ext i j
  simp only [diagonal_pow, mul_diagonal, blkE]
  fin_cases i <;> fin_cases j <;> simp [h0, h1, h2]

/- English proof (translation)
Introduce `h0`. Take `⟨v, hv, hv'⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Use `h (fun j => if hj : j ∈ S then v ⟨j, hj⟩ else 0) (by` as an intermediate fact. Introduce `i hi`. Establish `h1` using `congrFun hv' ⟨i, hi⟩`.

Simplify using `only [mulVec, dotProduct, submatrix_apply, Pi.zero_apply] at h1 ⊢`. Use `Eq.trans ?_ h1` and prove the remaining obligations. Rewrite using `[← Finset.sum_subset (Finset.subset_univ S) (by intro x _ hx; rw [dif_neg hx, mul_zero]), ← Finset.sum_coe_sort S]`. Conclude with `Finset.sum_congr rfl fun x _ => by rw [dif_pos x.2]) (by intro i hi; exact dif_neg hi)`. Apply `hv` to reduce the goal to its premises.

Use extensionality with `⟨j, hj⟩`. Establish `h3` using `congrFun this j`. Simplify using `only [dif_pos hj] at h3`. Conclude with `h3`.
-/
private lemma minor_neE {κ : Type} [Field κ] {n : ℕ} (Y : Matrix (Fin n) (Fin n) κ) (S : Finset (Fin n))
    (h : ∀ v : Fin n → κ, (∀ i ∈ S, (Y *ᵥ v) i = 0) → (∀ i, i ∉ S → v i = 0) → v = 0) :
    (Y.submatrix (Subtype.val : S → Fin n) Subtype.val).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv'⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have := h (fun j => if hj : j ∈ S then v ⟨j, hj⟩ else 0) (by
    intro i hi
    have h1 := congrFun hv' ⟨i, hi⟩
    simp only [mulVec, dotProduct, submatrix_apply, Pi.zero_apply] at h1 ⊢
    refine Eq.trans ?_ h1
    rw [← Finset.sum_subset (Finset.subset_univ S) (by intro x _ hx; rw [dif_neg hx, mul_zero]),
      ← Finset.sum_coe_sort S]
    exact Finset.sum_congr rfl fun x _ => by rw [dif_pos x.2]) (by intro i hi; exact dif_neg hi)
  apply hv
  ext ⟨j, hj⟩
  have h3 := congrFun this j
  simp only [dif_pos hj] at h3
  exact h3

/- English proof (translation)
Apply `minor_neE` to reduce the goal to its premises. Introduce `v ha hb`. Rewrite `hd` using `[det_fin_two]`. Establish `e0 : (blkE M w *ᵥ v) 0 = M 0 0 * v 0 + M 0 1 * v 1` using `by simp [blkE, mulVec, dotProduct, Fin.sum_univ_three]`. Establish `e1 : (blkE M w *ᵥ v) 1 = M 1 0 * v 0 + M 1 1 * v 1` using `by simp [blkE, mulVec, dotProduct, Fin.sum_univ_three]`.

Establish `e2 : (blkE M w *ᵥ v) 2 = w * v 2` using `by simp [blkE, mulVec, dotProduct, Fin.sum_univ_three]`. Establish `v2 : v 2 = 0`. Distinguish the cases in `h : (2 : Fin 3) ∈ S`. Use `ha _ h` as an intermediate fact. Rewrite `this` using `[e2]`.

Simplify `this` using `[hw]`. Conclude with `hb _ h`. Establish `v01 : v 0 = 0 ∧ v 1 = 0`. Apply the tactic sequence `by_cases k0 : (0 : Fin 3) ∈ S <;> by_cases k1 : (1 : Fin 3) ∈ S`. Establish `a0` using `ha _ k0`.

Establish `a1` using `ha _ k1`. Rewrite `a0` using `[e0]`. Rewrite `a1` using `[e1]`. Prove the components needed by the constructor for the conclusion. Apply `mul_left_cancel₀ hd` to reduce the goal to its premises.

Take the linear combination `M 1 1 * a0 - M 0 1 * a1`. Apply `mul_left_cancel₀ hd` to reduce the goal to its premises. Take the linear combination `M 0 0 * a1 - M 1 0 * a0`. Establish `a0` using `ha _ k0`. Establish `a1` using `hb _ k1`.

Rewrite `a0` using `[e0, a1]`. Conclude with `⟨by simpa [h0] using a0, a1⟩`. Establish `a0` using `hb _ k0`. Establish `a1` using `ha _ k1`. Rewrite `a1` using `[e1, a0]`.

Conclude with `⟨a0, by simpa [h1] using a1⟩`. Conclude with `⟨hb _ k0, hb _ k1⟩`. Use extensionality with `i`. Use `fin_cases i`. Conclude with `v01.1`.

Conclude with `v01.2`. Conclude with `v2`.
-/
private lemma minor_blkE {κ : Type} [Field κ] (M : Matrix (Fin 2) (Fin 2) κ) (w : κ) (h0 : M 0 0 ≠ 0) (h1 : M 1 1 ≠ 0)
    (hd : M.det ≠ 0) (hw : w ≠ 0) (S : Finset (Fin 3)) :
    ((blkE M w).submatrix (Subtype.val : S → Fin 3) Subtype.val).det ≠ 0 := by
  apply minor_neE
  intro v ha hb
  rw [det_fin_two] at hd
  have e0 : (blkE M w *ᵥ v) 0 = M 0 0 * v 0 + M 0 1 * v 1 := by simp [blkE, mulVec, dotProduct, Fin.sum_univ_three]
  have e1 : (blkE M w *ᵥ v) 1 = M 1 0 * v 0 + M 1 1 * v 1 := by simp [blkE, mulVec, dotProduct, Fin.sum_univ_three]
  have e2 : (blkE M w *ᵥ v) 2 = w * v 2 := by simp [blkE, mulVec, dotProduct, Fin.sum_univ_three]
  have v2 : v 2 = 0 := by
    by_cases h : (2 : Fin 3) ∈ S
    · have := ha _ h
      rw [e2] at this
      simpa [hw] using this
    · exact hb _ h
  have v01 : v 0 = 0 ∧ v 1 = 0 := by
    by_cases k0 : (0 : Fin 3) ∈ S <;> by_cases k1 : (1 : Fin 3) ∈ S
    · have a0 := ha _ k0
      have a1 := ha _ k1
      rw [e0] at a0
      rw [e1] at a1
      constructor
      · apply mul_left_cancel₀ hd
        linear_combination M 1 1 * a0 - M 0 1 * a1
      · apply mul_left_cancel₀ hd
        linear_combination M 0 0 * a1 - M 1 0 * a0
    · have a0 := ha _ k0
      have a1 := hb _ k1
      rw [e0, a1] at a0
      exact ⟨by simpa [h0] using a0, a1⟩
    · have a0 := hb _ k0
      have a1 := ha _ k1
      rw [e1, a0] at a1
      exact ⟨a0, by simpa [h1] using a1⟩
    · exact ⟨hb _ k0, hb _ k1⟩
  ext i
  fin_cases i
  · exact v01.1
  · exact v01.2
  · exact v2

/- English proof (translation)
Establish `hα2 : FreeRatios α`. Introduce `i j hij m hm`. Use `hα i.castSucc j.castSucc (by simpa using hij) m hm` as an intermediate fact. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simpa using this`. Take `⟨b, hb⟩` from `fullEx G κ 2 σ hσ u α hα2 hu`.

Take `⟨m, hm⟩` from `expSums κ (Fin 2) (Fin 2) (fun _ => α) (fun s i => (y : Matrix (Fin 2) (Fin 2) κ) s i * gm σ b i s) (fun _ => hα2) (by`. Introduce `s`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Establish `: ∀ i, (y : Matrix (Fin 2) (Fin 2) κ) s i = 0` using `fun i => (mul_eq_zero.1 (hc i)).resolve_right (hb i s).1`.

Conclude with `y.det_ne_zero (det_eq_zero_of_row_eq_zero s this))`. Establish `hpow : ∀ k : ℕ, gm σ (u ^ k) = diagonal (fun i => ((α i : κˣ) : κ)) ^ k`. Introduce `k`. Rewrite using `[← hu]`. Simplify using `[gm]`.

Establish `hmul : ∀ g g', gm σ (g * g') = gm σ g * gm σ g'`. Introduce `g g'`. Simplify using `[gm]`. Use `set M : Matrix (Fin 2) (Fin 2) κ := (y : Matrix (Fin 2) (Fin 2) κ) * gm σ (u ^ m * b) with hM`. Establish `hdiag : ∀ s, M s s ≠ 0`.

Introduce `s`. Establish `: M s s = ∑ i, (y : Matrix (Fin 2) (Fin 2) κ) s i * gm σ b i s * ((α i : κˣ) : κ) ^ m`. Rewrite using `[hM, hmul, hpow, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[diagonal_pow, diagonal_mul]`.

Simplify using `only [Pi.pow_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `hm s`. Establish `hdet : M.det ≠ 0`.

Use `(y * σ (u ^ m * b)).det_ne_zero` as an intermediate fact. Rewrite `this` using `[Units.val_mul]`. Then use the resulting hypothesis. Take `⟨k, hk⟩` from `sepOfMinors κ 3 le_rfl (blkE M ((z * ψ₀ (u ^ m * b) : κˣ) : κ)) _ hα (minor_blkE M _ (hdiag 0) (hdiag 1) hdet (Units.ne_zero _))`. Rewrite `hk` using `[blkE_mul M _ (fun i => ((α i : κˣ) : κ)) ((ψ₀ u : κˣ) : κ) k _ rfl rfl rfl, charpoly_blkE]`. Use `⟨u ^ m * b * u ^ k, ?_⟩` and prove the remaining obligations.

Rewrite using `[hmul, hpow, ← Matrix.mul_assoc, ← hM]`. Use `hk using 4` and compare the differences between its conclusion and the goal. Simplify using `[mul_assoc]`.
-/
private lemma diagCaseE (G κ : Type) [Group G] [Field κ] (σ : G →* GL (Fin 2) κ) (ψ₀ : G →* κˣ) (hσ : StrongIrr σ)
    (u : G) (α : Fin 2 → κˣ) (hα : FreeRatios ![α 0, α 1, ψ₀ u])
    (hu : gm σ u = diagonal (fun i => ((α i : κˣ) : κ))) (y : GL (Fin 2) κ) (z : κˣ) :
    ∃ h, (((y : Matrix (Fin 2) (Fin 2) κ) * gm σ h).charpoly * (X - C ((z * ψ₀ h : κˣ) : κ))).Separable := by
  have hα2 : FreeRatios α := by
    intro i j hij m hm
    have := hα i.castSucc j.castSucc (by simpa using hij) m hm
    fin_cases i <;> fin_cases j <;> simpa using this
  obtain ⟨b, hb⟩ := fullEx G κ 2 σ hσ u α hα2 hu
  obtain ⟨m, hm⟩ := expSums κ (Fin 2) (Fin 2) (fun _ => α)
    (fun s i => (y : Matrix (Fin 2) (Fin 2) κ) s i * gm σ b i s) (fun _ => hα2) (by
      intro s
      by_contra hc
      push Not at hc
      have : ∀ i, (y : Matrix (Fin 2) (Fin 2) κ) s i = 0 := fun i =>
        (mul_eq_zero.1 (hc i)).resolve_right (hb i s).1
      exact y.det_ne_zero (det_eq_zero_of_row_eq_zero s this))
  have hpow : ∀ k : ℕ, gm σ (u ^ k) = diagonal (fun i => ((α i : κˣ) : κ)) ^ k := by
    intro k
    rw [← hu]; simp [gm]
  have hmul : ∀ g g', gm σ (g * g') = gm σ g * gm σ g' := by
    intro g g'; simp [gm]
  set M : Matrix (Fin 2) (Fin 2) κ := (y : Matrix (Fin 2) (Fin 2) κ) * gm σ (u ^ m * b) with hM
  have hdiag : ∀ s, M s s ≠ 0 := by
    intro s
    have : M s s = ∑ i, (y : Matrix (Fin 2) (Fin 2) κ) s i * gm σ b i s * ((α i : κˣ) : κ) ^ m := by
      rw [hM, hmul, hpow, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [diagonal_pow, diagonal_mul]
      simp only [Pi.pow_apply]
      ring
    rw [this]; exact hm s
  have hdet : M.det ≠ 0 := by
    have := (y * σ (u ^ m * b)).det_ne_zero
    rwa [Units.val_mul] at this
  obtain ⟨k, hk⟩ := sepOfMinors κ 3 le_rfl (blkE M ((z * ψ₀ (u ^ m * b) : κˣ) : κ)) _ hα
    (minor_blkE M _ (hdiag 0) (hdiag 1) hdet (Units.ne_zero _))
  rw [blkE_mul M _ (fun i => ((α i : κˣ) : κ)) ((ψ₀ u : κˣ) : κ) k _ rfl rfl rfl, charpoly_blkE] at hk
  refine ⟨u ^ m * b * u ^ k, ?_⟩
  rw [hmul, hpow, ← Matrix.mul_assoc, ← hM]
  convert hk using 4
  simp [mul_assoc]

end UpperTheory.V.Pr

/- English proof (translation)
Introduce `G κ _ _ σ ψ₀ hσ u α hα hu y z`. Establish `hinj : Function.Injective (fun i => ((α i : κˣ) : κ))`. Introduce `i j hij`. Assume the negation of the conclusion as `hne`. Use `hα i.castSucc j.castSucc (by simpa using hne) 1 one_pos` as an intermediate fact.

Establish `h2 : α i = α j` using `Units.ext hij`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp_all`. Take `⟨P, hP⟩` from `diagE (gm σ u) _ hinj hu`. Take `⟨h, hh⟩` from `diagCaseE G κ _ ψ₀ (strongIrr_conjE σ hσ P) u α hα (by`. Simplify using `only [gm] at hP`.

Simplify using `[gm, Matrix.mul_assoc, hP]) (P⁻¹ * y * P) z`. Use `⟨h, ?_⟩` and prove the remaining obligations. Use `hh using 2` and compare the differences between its conclusion and the goal. Rewrite using `[← Matrix.charpoly_units_conj P⁻¹]`. Use `congr 1`.

Simplify using `[gm, Matrix.mul_assoc]`.
-/
theorem UpperTheory.V.Pr.regCosetE :
    UpperTheory.V.Pr.RegCosetE := by
  intro G κ _ _ σ ψ₀ hσ u α hα hu y z
  have hinj : Function.Injective (fun i => ((α i : κˣ) : κ)) := by
    intro i j hij
    by_contra hne
    have := hα i.castSucc j.castSucc (by simpa using hne) 1 one_pos
    have h2 : α i = α j := Units.ext hij
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨P, hP⟩ := diagE (gm σ u) _ hinj hu
  obtain ⟨h, hh⟩ := diagCaseE G κ _ ψ₀ (strongIrr_conjE σ hσ P) u α hα (by
    simp only [gm] at hP
    simp [gm, Matrix.mul_assoc, hP]) (P⁻¹ * y * P) z
  refine ⟨h, ?_⟩
  convert hh using 2
  rw [← Matrix.charpoly_units_conj P⁻¹]
  congr 1
  simp [gm, Matrix.mul_assoc]
