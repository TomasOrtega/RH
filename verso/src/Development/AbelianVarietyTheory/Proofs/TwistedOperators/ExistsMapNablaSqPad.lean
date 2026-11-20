import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenericDetPowMulHw
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open scoped Matrix

noncomputable section

namespace GlobalTheory.GLDuality

def dropCols (r m : ℕ) : MvPolynomial (Fin r × Fin r) ℂ →ₐ[ℂ] MvPolynomial (Fin r × Fin m) ℂ :=
  aeval fun v => if h : v.2.val < m then X (v.1, ⟨v.2.val, h⟩) else 0

/- English proof (translation)
Establish `: (dropCols r m).comp (rowAct ℂ g) = (rowAct ℂ g).comp (dropCols r m)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨a, s⟩`. Apply the tactic sequence `by_cases hs : s.val < m <;> simp [dropCols, rowAct, hs]`. Conclude with `DFunLike.congr_fun this f`.
-/
theorem dropCols_rowAct (r m : ℕ) (g : Matrix (Fin r) (Fin r) ℂ) (f : MvPolynomial (Fin r × Fin r) ℂ) :
    dropCols r m (rowAct ℂ g f) = rowAct ℂ g (dropCols r m f) := by
  have : (dropCols r m).comp (rowAct ℂ g) = (rowAct ℂ g).comp (dropCols r m) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    by_cases hs : s.val < m <;> simp [dropCols, rowAct, hs]
  exact DFunLike.congr_fun this f

/- English proof (translation)
Unfold `lpMinor`. Rewrite using `[AlgHom.map_det]`. Use `congr 1`. Use `ext1 p q`. Establish `hq : q.val < m` using `lt_of_lt_of_le q.2 hm`.

Simplify using `[dropCols, hq, Fin.castLE]`.
-/
theorem dropCols_lpMinor (r m s : ℕ) (hr : s ≤ r) (hm : s ≤ m) :
    dropCols r m (lpMinor ℂ s hr hr) = lpMinor ℂ s hr hm := by
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext1 p q
  have hq : q.val < m := lt_of_lt_of_le q.2 hm
  simp [dropCols, hq, Fin.castLE]

/- English proof (translation)
Unfold `hw`. Rewrite using `[map_prod]`. Use `symm`. Use `Finset.prod_of_injOn (Fin.castLE h) (Fin.castLE_injective h).injOn (fun _ _ => Finset.mem_univ _) ?_ ?_` and prove the remaining obligations. Introduce `s _ hs`.

Establish `hs' : ¬ s.val < m` using `fun hlt => hs ⟨⟨s.val, hlt⟩, by simp, rfl⟩`. Simplify using `[rowNu, hs']`. Introduce `s _`. Rewrite using `[map_pow]`. Establish `e : nuNext (rowNu (r` using `r) ν) (Fin.castLE h s) = nuNext ν s := by`.

Simplify using `only [nuNext, rowNu, Fin.val_castLE]`. Use `split_ifs with h1 h2 h3`. Both sides reduce to the same expression. Both sides reduce to the same expression. Use linear arithmetic over natural numbers and integers.

Both sides reduce to the same expression. Establish `e' : rowNu (r` using `r) ν (Fin.castLE h s) = ν s := by simp [rowNu]`. Rewrite using `[e, e']`. Use `congr 1`. Conclude with `(dropCols_lpMinor r m (s.val + 1) _ _).symm`.
-/
theorem dropCols_hw (r m : ℕ) (h : m ≤ r) (ν : Fin m → ℕ) :
    dropCols r m (hw ℂ (le_refl r) (rowNu ν)) = hw ℂ h ν := by
  unfold hw
  rw [map_prod]
  symm
  refine Finset.prod_of_injOn (Fin.castLE h) (Fin.castLE_injective h).injOn (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro s _ hs
    have hs' : ¬ s.val < m := fun hlt => hs ⟨⟨s.val, hlt⟩, by simp, rfl⟩
    simp [rowNu, hs']
  · intro s _
    rw [map_pow]
    have e : nuNext (rowNu (r := r) ν) (Fin.castLE h s) = nuNext ν s := by
      simp only [nuNext, rowNu, Fin.val_castLE]
      split_ifs with h1 h2 h3
      · rfl
      · rfl
      · omega
      · rfl
    have e' : rowNu (r := r) ν (Fin.castLE h s) = ν s := by simp [rowNu]
    rw [e, e']
    congr 1
    exact (dropCols_lpMinor r m (s.val + 1) _ _).symm

/- English proof (translation)
Unfold `DomWeight.detShift`. Use `split_ifs`. Conclude with `Nat.cast_nonneg _`. Conclude with `le_rfl`.
-/
theorem pad_detShift_nonneg {m : ℕ} (r : ℕ) (a : Part m) : 0 ≤ (pad r a).detShift := by
  unfold DomWeight.detShift
  split_ifs
  · exact Nat.cast_nonneg _
  · exact le_rfl

/- English proof (translation)
Establish `h0` using `pad_detShift_nonneg r a`. Establish `h1 : (pad r a).detShift ≤ (pad r a).w i`. Unfold `DomWeight.detShift`. Rewrite using `[dif_pos i.pos]`. Apply `(pad r a).anti` to reduce the goal to its premises.

Rewrite using `[Fin.le_def]`. Use `i.2` as an intermediate fact. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Establish `h2 : (pad r a).w i = (rowNu (r` using `r) a.1 i : ℕ) := rfl`.

Simplify using `only [DomWeight.natW]`. Use linear arithmetic over natural numbers and integers.
-/
theorem pad_natW_add {m : ℕ} (r : ℕ) (a : Part m) (i : Fin r) :
    (pad r a).natW i + (pad r a).detShift.toNat = rowNu a.1 i := by
  have h0 := pad_detShift_nonneg r a
  have h1 : (pad r a).detShift ≤ (pad r a).w i := by
    unfold DomWeight.detShift
    rw [dif_pos i.pos]
    apply (pad r a).anti
    rw [Fin.le_def]
    have := i.2
    simp only
    omega
  have h2 : (pad r a).w i = (rowNu (r := r) a.1 i : ℕ) := rfl
  simp only [DomWeight.natW]
  omega

/- English proof (translation)
Introduce `r m h a`. Take `⟨c, hc⟩` from `Int.eq_ofNat_of_zero_le (pad_detShift_nonneg r a)`. Set `j : nablaSq ℂ r (pad r a) →ₗ[ℂ] MvPolynomial (Fin r × Fin m) ℂ` to `(dropCols r m).toLinearMap ∘ₗ LinearMap.mulLeft ℂ (lpMinor ℂ r le_rfl le_rfl ^ c) ∘ₗ (nablaSq ℂ r (pad r a)).subtype`. Establish `hj : ∀ f, j f = dropCols r m (lpMinor ℂ r le_rfl le_rfl ^ c * f)` using `fun _ => rfl`. Use `⟨j, fun g f => ?_, fun f hf => ?_⟩` and prove the remaining obligations.

Rewrite using `[hj, hj, ← dropCols_rowAct, (genericDet_pow_mul r c (fun _ => 0)).2.1, sqRep_coe, sqAct, hc, mul_smul_comm, Matrix.det_transpose]`. Simplify using `[detPow]`. Rewrite using `[hj, hf, extremal, genericDet_pow_mul_hw, ← dropCols_hw r m h]`. Use `congr 2`. Use function extensionality and compare the values at `i`.

Use `pad_natW_add r a i` as an intermediate fact. Rewrite `this` using `[hc, Int.toNat_natCast]`. Then use the resulting hypothesis.
-/
theorem exists_map_nablaSq_pad : ∀ (r m : ℕ) (h : m ≤ r) (a : Part m), ∃ j : nablaSq ℂ r (pad r a) →ₗ[ℂ] MvPolynomial (Fin r × Fin m) ℂ, (∀ (g : GL (Fin r) ℂ) (f : nablaSq ℂ r (pad r a)), j (sqRep ℂ r (pad r a) g f) = rowAct ℂ (g : Matrix (Fin r) (Fin r) ℂ)ᵀ (j f)) ∧ ∀ f : nablaSq ℂ r (pad r a), (f : MvPolynomial (Fin r × Fin r) ℂ) = extremal ℂ r (pad r a) → j f = hw ℂ h a.1 := by
  intro r m h a
  obtain ⟨c, hc⟩ := Int.eq_ofNat_of_zero_le (pad_detShift_nonneg r a)
  let j : nablaSq ℂ r (pad r a) →ₗ[ℂ] MvPolynomial (Fin r × Fin m) ℂ :=
    (dropCols r m).toLinearMap ∘ₗ LinearMap.mulLeft ℂ (lpMinor ℂ r le_rfl le_rfl ^ c) ∘ₗ
      (nablaSq ℂ r (pad r a)).subtype
  have hj : ∀ f, j f = dropCols r m (lpMinor ℂ r le_rfl le_rfl ^ c * f) := fun _ => rfl
  refine ⟨j, fun g f => ?_, fun f hf => ?_⟩
  · rw [hj, hj, ← dropCols_rowAct, (genericDet_pow_mul r c (fun _ => 0)).2.1, sqRep_coe, sqAct, hc,
      mul_smul_comm, Matrix.det_transpose]
    simp [detPow]
  · rw [hj, hf, extremal, genericDet_pow_mul_hw, ← dropCols_hw r m h]
    congr 2
    funext i
    have := pad_natW_add r a i
    rwa [hc, Int.toNat_natCast] at this

end GlobalTheory.GLDuality
