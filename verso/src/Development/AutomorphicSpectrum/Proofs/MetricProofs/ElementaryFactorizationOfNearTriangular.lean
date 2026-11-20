import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Factor

/- English proof (translation)
Introduce `N j ca cb C hcb hblk hC hdet hlow`. Establish `hlt : ca < cb` using `by rw [Fin.lt_def]; omega`. Establish `hne : ca ≠ cb` using `ne_of_lt hlt`. Establish `hne' : cb ≠ ca` using `hne.symm`. Establish `hx : C ca ca = 0 → C cb ca ≠ 0`.

Introduce `ha hx`. Apply `hdet` to reduce the goal to its premises. Establish `hT : C.BlockTriangular id`. Introduce `r c hrc`. Distinguish the cases in `h : r = cb ∧ c = ca`.

Take `⟨rfl, rfl⟩` from `h`. Conclude with `hx`. Conclude with `hlow r c hrc h`. Rewrite using `[Matrix.det_of_upperTriangular hT]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ ca) ha`.

Use `set s : ℂ := if C ca ca = 0 then -(C cb ca)⁻¹ else 0 with hs`. Use `set C' : Matrix (Fin N) (Fin N) ℂ := Matrix.transvection ca cb (-s) * C with hC'`. Establish `hC'o : ∀ r c, r ≠ ca → C' r c = C r c` using `fun r c hr => Matrix.transvection_mul_apply_of_ne ca cb r c hr (-s) C`. Establish `hC'a : ∀ c, C' ca c = C ca c + -s * C cb c` using `fun c => Matrix.transvection_mul_apply_same ca cb c (-s) C`. Establish `hC'blk : IsBlockDiag j C'`.

Introduce `a b hab`. Distinguish the cases in `ha : a = ca`. Substitute `ha` using the available equality. Rewrite using `[hC'a, hC a b hab, hC cb b (by rw [← hblk]; exact hab)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hC'o a b ha, hC a b hab]`. Establish `hC'low : ∀ r c, c < r → ¬ (r = cb ∧ c = ca) → C' r c = 0`. Introduce `r c hrc h`. Distinguish the cases in `hr : r = ca`. Substitute `hr` using the available equality.

Establish `hcb' : c < cb` using `lt_trans hrc hlt`. Rewrite using `[hC'a, hlow _ c hrc (fun h' => hne h'.1), hlow cb c hcb' (fun h' => (ne_of_lt hrc) h'.2)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hC'o r c hr]`. Conclude with `hlow r c hrc h`.

Establish `hdiag : C' ca ca ≠ 0`. Rewrite using `[hC'a]`. Distinguish the cases in `ha : C ca ca = 0`. Establish `hx'` using `hx ha`. Rewrite using `[hs, if_pos ha, ha, neg_neg, inv_mul_cancel₀ hx']`.

Simplify using the standard rewrite rules. Rewrite using `[hs, if_neg ha]`. Simplify using `using ha`. Use `set t : ℂ := C' cb ca / C' ca ca with ht`. Use `set U : Matrix (Fin N) (Fin N) ℂ := Matrix.transvection cb ca (-t) * C' with hU`.

Establish `hUo : ∀ r c, r ≠ cb → U r c = C' r c` using `fun r c hr => Matrix.transvection_mul_apply_of_ne cb ca r c hr (-t) C'`. Establish `hUb : ∀ c, U cb c = C' cb c + -t * C' ca c` using `fun c => Matrix.transvection_mul_apply_same cb ca c (-t) C'`. Establish `hUtri : U.BlockTriangular id`. Introduce `r c hrc`. Express the relevant statement in the definitionally equal form `c < r at hrc`.

Distinguish the cases in `hr : r = cb`. Substitute `hr` using the available equality. Rewrite using `[hUb]`. Distinguish the cases in `hc : c = ca`. Substitute `hc` using the available equality.

Rewrite using `[ht, neg_mul, div_mul_cancel₀ _ hdiag]`. Expand and normalize the polynomial expressions, which then agree. Establish `hca : c < ca`. Rewrite `hrc`, the goal using `[Fin.lt_def]`. Establish `: (c : ℕ) ≠ ca` using `fun h => hc (Fin.ext h)`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hC'low _ c hrc (fun h => hc h.2), hC'low ca c hca (fun h => hne h.1)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hUo r c hr]`. Conclude with `hC'low r c hrc (fun h => hr h.1)`.

Establish `hdetU : U.det = C.det`. Rewrite using `[hU, hC', Matrix.det_mul, Matrix.det_mul, Matrix.det_transvection_of_ne _ _ hne', Matrix.det_transvection_of_ne _ _ hne, one_mul, one_mul]`. Use `⟨Matrix.transvection ca cb s, U, t, ?_, ?_, ?_, ?_, hUtri, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Rewrite using `[Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]`.

Establish `hab' : a ≠ b` using `fun h => hab (by rw [h])`. Rewrite using `[if_neg hab']`. Distinguish the cases in `h : ca = a ∧ cb = b`. Take `⟨rfl, rfl⟩` from `h`. Conclude with `absurd hblk hab`.

Rewrite using `[if_neg h]`. Simplify using the standard rewrite rules. Introduce `r c hrc`. Express the relevant statement in the definitionally equal form `c < r at hrc`. Rewrite using `[Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, if_neg (ne_of_gt hrc)]`.

Establish `h : ¬ (ca = r ∧ cb = c)`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `absurd (lt_trans hrc hlt) (lt_irrefl _)`. Rewrite using `[if_neg h]`. Simplify using the standard rewrite rules.

Rewrite using `[Matrix.det_transvection_of_ne _ _ hne]`. Conclude with `one_ne_zero`. Introduce `a b hab`. Distinguish the cases in `ha : a = cb`. Substitute `ha` using the available equality.

Rewrite using `[hUb, hC'blk _ b hab, hC'blk ca b (by rw [hblk]; exact hab)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hUo a b ha, hC'blk a b hab]`. Introduce `c`. Establish `hp : ∏ i, U i i ≠ 0`.

Rewrite using `[← Matrix.det_of_upperTriangular hUtri, hdetU]`. Conclude with `hdet`. Conclude with `Finset.prod_ne_zero_iff.mp hp c (Finset.mem_univ c)`. Express the relevant statement in the definitionally equal form `C = Matrix.transvection ca cb s * Matrix.transvection cb ca t * U`. Rewrite using `[hU, hC', Matrix.mul_assoc (Matrix.transvection ca cb s), ← Matrix.mul_assoc (Matrix.transvection cb ca t), Matrix.transvection_mul_transvection_same cb ca hne' t (-t), add_neg_cancel, Matrix.transvection_zero, Matrix.one_mul, ← Matrix.mul_assoc, Matrix.transvection_mul_transvect …`.
-/
theorem exists_upper_transvection_upper : ∀ (N j : ℕ) (ca cb : Fin N) (C : Matrix (Fin N) (Fin N) ℂ), (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → IsBlockDiag j C → C.det ≠ 0 → (∀ r c, c < r → ¬ (r = cb ∧ c = ca) → C r c = 0) → ∃ (B U : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), IsBlockDiag j B ∧ B.BlockTriangular id ∧ B.det ≠ 0 ∧ IsBlockDiag j U ∧ U.BlockTriangular id ∧ (∀ c, U c c ≠ 0) ∧ C = B * (1 + Matrix.single cb ca t) * U := by
  intro N j ca cb C hcb hblk hC hdet hlow
  have hlt : ca < cb := by rw [Fin.lt_def]; omega
  have hne : ca ≠ cb := ne_of_lt hlt
  have hne' : cb ≠ ca := hne.symm
  have hx : C ca ca = 0 → C cb ca ≠ 0 := by
    intro ha hx
    apply hdet
    have hT : C.BlockTriangular id := by
      intro r c hrc
      by_cases h : r = cb ∧ c = ca
      · obtain ⟨rfl, rfl⟩ := h
        exact hx
      · exact hlow r c hrc h
    rw [Matrix.det_of_upperTriangular hT]
    exact Finset.prod_eq_zero (Finset.mem_univ ca) ha
  set s : ℂ := if C ca ca = 0 then -(C cb ca)⁻¹ else 0 with hs
  set C' : Matrix (Fin N) (Fin N) ℂ := Matrix.transvection ca cb (-s) * C with hC'
  have hC'o : ∀ r c, r ≠ ca → C' r c = C r c := fun r c hr =>
    Matrix.transvection_mul_apply_of_ne ca cb r c hr (-s) C
  have hC'a : ∀ c, C' ca c = C ca c + -s * C cb c := fun c =>
    Matrix.transvection_mul_apply_same ca cb c (-s) C
  have hC'blk : IsBlockDiag j C' := by
    intro a b hab
    by_cases ha : a = ca
    · subst ha
      rw [hC'a, hC a b hab, hC cb b (by rw [← hblk]; exact hab)]
      ring
    · rw [hC'o a b ha, hC a b hab]
  have hC'low : ∀ r c, c < r → ¬ (r = cb ∧ c = ca) → C' r c = 0 := by
    intro r c hrc h
    by_cases hr : r = ca
    · subst hr
      have hcb' : c < cb := lt_trans hrc hlt
      rw [hC'a, hlow _ c hrc (fun h' => hne h'.1),
        hlow cb c hcb' (fun h' => (ne_of_lt hrc) h'.2)]
      ring
    · rw [hC'o r c hr]
      exact hlow r c hrc h
  have hdiag : C' ca ca ≠ 0 := by
    rw [hC'a]
    by_cases ha : C ca ca = 0
    · have hx' := hx ha
      rw [hs, if_pos ha, ha, neg_neg, inv_mul_cancel₀ hx']
      simp
    · rw [hs, if_neg ha]
      simpa using ha
  set t : ℂ := C' cb ca / C' ca ca with ht
  set U : Matrix (Fin N) (Fin N) ℂ := Matrix.transvection cb ca (-t) * C' with hU
  have hUo : ∀ r c, r ≠ cb → U r c = C' r c := fun r c hr =>
    Matrix.transvection_mul_apply_of_ne cb ca r c hr (-t) C'
  have hUb : ∀ c, U cb c = C' cb c + -t * C' ca c := fun c =>
    Matrix.transvection_mul_apply_same cb ca c (-t) C'
  have hUtri : U.BlockTriangular id := by
    intro r c hrc
    change c < r at hrc
    by_cases hr : r = cb
    · subst hr
      rw [hUb]
      by_cases hc : c = ca
      · subst hc
        rw [ht, neg_mul, div_mul_cancel₀ _ hdiag]
        ring
      · have hca : c < ca := by
          rw [Fin.lt_def] at hrc ⊢
          have : (c : ℕ) ≠ ca := fun h => hc (Fin.ext h)
          omega
        rw [hC'low _ c hrc (fun h => hc h.2), hC'low ca c hca (fun h => hne h.1)]
        ring
    · rw [hUo r c hr]
      exact hC'low r c hrc (fun h => hr h.1)
  have hdetU : U.det = C.det := by
    rw [hU, hC', Matrix.det_mul, Matrix.det_mul, Matrix.det_transvection_of_ne _ _ hne',
      Matrix.det_transvection_of_ne _ _ hne, one_mul, one_mul]
  refine ⟨Matrix.transvection ca cb s, U, t, ?_, ?_, ?_, ?_, hUtri, ?_, ?_⟩
  · intro a b hab
    rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have hab' : a ≠ b := fun h => hab (by rw [h])
    rw [if_neg hab']
    by_cases h : ca = a ∧ cb = b
    · obtain ⟨rfl, rfl⟩ := h
      exact absurd hblk hab
    · rw [if_neg h]
      simp
  · intro r c hrc
    change c < r at hrc
    rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
      if_neg (ne_of_gt hrc)]
    have h : ¬ (ca = r ∧ cb = c) := by
      rintro ⟨rfl, rfl⟩
      exact absurd (lt_trans hrc hlt) (lt_irrefl _)
    rw [if_neg h]
    simp
  · rw [Matrix.det_transvection_of_ne _ _ hne]
    exact one_ne_zero
  · intro a b hab
    by_cases ha : a = cb
    · subst ha
      rw [hUb, hC'blk _ b hab, hC'blk ca b (by rw [hblk]; exact hab)]
      ring
    · rw [hUo a b ha, hC'blk a b hab]
  · intro c
    have hp : ∏ i, U i i ≠ 0 := by
      rw [← Matrix.det_of_upperTriangular hUtri, hdetU]
      exact hdet
    exact Finset.prod_ne_zero_iff.mp hp c (Finset.mem_univ c)
  · change C = Matrix.transvection ca cb s * Matrix.transvection cb ca t * U
    rw [hU, hC', Matrix.mul_assoc (Matrix.transvection ca cb s), ← Matrix.mul_assoc (Matrix.transvection cb ca t),
      Matrix.transvection_mul_transvection_same cb ca hne' t (-t), add_neg_cancel, Matrix.transvection_zero, Matrix.one_mul,
      ← Matrix.mul_assoc, Matrix.transvection_mul_transvection_same ca cb hne s (-s), add_neg_cancel,
      Matrix.transvection_zero, Matrix.one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.Factor
