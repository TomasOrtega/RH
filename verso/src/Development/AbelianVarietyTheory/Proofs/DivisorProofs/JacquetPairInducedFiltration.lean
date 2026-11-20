import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusThreeBlockApply
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeMatrixCharacterLeviBlockExists
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

noncomputable section

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.IndJacBlock GlobalTheory.LeviBlockExponentLocal

namespace GlobalTheory.IndJacBlock

section Cells

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Rewrite using `[Pi.mul_apply, Pi.mul_apply, torus_three_block_apply]`. Use `ext1`. Simplify using `only [Units.val_mul, Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe]`. Conclude with `(Matrix.scalar_commute _ (fun r => Commute.all _ r) _).symm.eq`.
-/
theorem tor3_comm (d : ℕ) (p : kˣ × kˣ) (y : Levi k (fun j : Fin 3 => Fin (sz3 d j))) :
    y * tor3 k d p = tor3 k d p * y := by
  funext j
  rw [Pi.mul_apply, Pi.mul_apply, torus_three_block_apply]
  ext1
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).symm.eq

/- English proof (translation)
Introduce `j _`. Rewrite using `[torus_three_block_apply]`. Use `mem_parab.2 fun a b hab => ?_` and prove the remaining obligations. Establish `hne : a ≠ b` using `by rintro rfl; exact lt_irrefl _ hab`. Simplify using `[Matrix.GeneralLinearGroup.scalar, hne]`.
-/
theorem tor3_mem_relParab (d : ℕ) (p : kˣ × kˣ) {β : Type} {c : Fin 3 → β → Type} [LinearOrder β] [Fintype β]
    [∀ j r, Fintype (c j r)] [∀ j r, DecidableEq (c j r)]
    (g : ∀ j, (Σ r, c j r) ≃ Fin (sz3 d j)) : tor3 k d p ∈ relParab k g := by
  intro j _
  rw [torus_three_block_apply]
  refine mem_parab.2 fun a b hab => ?_
  have hne : a ≠ b := by rintro rfl; exact lt_irrefl _ hab
  simp [Matrix.GeneralLinearGroup.scalar, hne]

/- English proof (translation)
Use extensionality with `a a'`. Use `(leviProj_apply k (g j) ⟨tor3 k d p j, tor3_mem_relParab d p g j trivial⟩ r a a').trans ?_` and prove the remaining obligations. Use `show ((tor3 k d p j : GL (Fin (sz3 d j)) k) : Matrix (Fin (sz3 d j)) (Fin (sz3 d j)) k) _ _ = _`. Rewrite using `[torus_three_block_apply]`. Distinguish the cases in `h : a = a'`.

Substitute `h` using the available equality. Simplify using `[Matrix.GeneralLinearGroup.scalar]`. Establish `h' : g j ⟨r, a⟩ ≠ g j ⟨r, a'⟩` using `by simpa using h`. Simplify using `[Matrix.GeneralLinearGroup.scalar, h, h']`.
-/
theorem relProj_tor3 (d : ℕ) (p : kˣ × kˣ) {β : Type} {c : Fin 3 → β → Type} [LinearOrder β] [Fintype β]
    [∀ j r, Fintype (c j r)] [∀ j r, DecidableEq (c j r)]
    (g : ∀ j, (Σ r, c j r) ≃ Fin (sz3 d j)) (j : Fin 3) (r : β) :
    relProj k g ⟨tor3 k d p, tor3_mem_relParab d p g⟩ j r =
      Matrix.GeneralLinearGroup.scalar _ (torEntry k d p j) := by
  ext a a'
  refine (leviProj_apply k (g j) ⟨tor3 k d p j, tor3_mem_relParab d p g j trivial⟩ r a a').trans ?_
  show ((tor3 k d p j : GL (Fin (sz3 d j)) k) : Matrix (Fin (sz3 d j)) (Fin (sz3 d j)) k) _ _ = _
  rw [torus_three_block_apply]
  by_cases h : a = a'
  · subst h; simp [Matrix.GeneralLinearGroup.scalar]
  · have h' : g j ⟨r, a⟩ ≠ g j ⟨r, a'⟩ := by simpa using h
    simp [Matrix.GeneralLinearGroup.scalar, h, h']

/- English proof (translation)
Simplify using `[modExp, Finset.sum_filter, Fin.sum_univ_three]`.
-/
theorem modExp_three_zero (m : Fin 3 → Type) [∀ a, Fintype (m a)] :
    modExp m 0 = (Fintype.card (m 1) : ℤ) + Fintype.card (m 2) := by
  simp [modExp, Finset.sum_filter, Fin.sum_univ_three]

/- English proof (translation)
Simplify using `[modExp, Finset.sum_filter, Fin.sum_univ_three]`.
-/
theorem modExp_three_two (m : Fin 3 → Type) [∀ a, Fintype (m a)] :
    modExp m 2 = -((Fintype.card (m 0) : ℤ) + Fintype.card (m 1)) := by
  simp [modExp, Finset.sum_filter, Fin.sum_univ_three]

/- English proof (translation)
Break down `(by omega : n = 0 ∨ n = 1) with h0 | h1` into its components or cases. Simplify using `[h0]`. Rewrite using `[h h1, h1, absPow_neg]`. Simplify using the standard rewrite rules.
-/
theorem absPow_pow_inv {n : ℕ} (hn : n ≤ 1) {s t : ℂ} (h : n = 1 → t = -s) (x : kˣ) :
    (absPow k s (x ^ n))⁻¹ = absPow k t x ^ n := by
  rcases (by omega : n = 0 ∨ n = 1) with h0 | h1
  · simp [h0]
  · rw [h h1, h1, absPow_neg]; simp

/- English proof (translation)
Establish `hy` using `relProj_tor3 (k := k) d p g`. Use `set y := relProj k g ⟨tor3 k d p, tor3_mem_relParab d p g⟩ with hydef`. Apply the tactic sequence `have hdet : ∀ j i, Matrix.GeneralLinearGroup.det (y j i) = torEntry k d p j ^ bm.1 i j := by`. Introduce `j i`. Rewrite using `[hy, det_scalar', Fintype.card_fin]`.

Apply the tactic sequence `have t0 : torEntry k d p 0 = p.1 := by simp [torEntry]`. Apply the tactic sequence `have t1 : torEntry k d p 1 = 1 := by simp [torEntry]`. Apply the tactic sequence `have t2 : torEntry k d p 2 = p.2 := by simp [torEntry]`. Establish `hc0 : bm.1 0 0 + bm.1 1 0 = 1`. Use `bm.2.2 0` as an intermediate fact.

Simplify `this` using `[Fin.sum_univ_two, sz3]`. Establish `hc2 : bm.1 0 2 + bm.1 1 2 = 1`. Use `bm.2.2 2` as an intermediate fact. Simplify `this` using `[Fin.sum_univ_two, sz3]`. Establish `hrow : ∀ i, bm.1 i 0 + bm.1 i 1 + bm.1 i 2 = b i`.

Introduce `i`. Use `bm.2.1 i` as an intermediate fact. Simplify `this` using `[Fin.sum_univ_three]`. Establish `hle0 : ∀ i, bm.1 i 0 ≤ 1`. Apply the tactic sequence `intro i; fin_cases i <;> simp <;> omega`.

Establish `hle2 : ∀ i, bm.1 i 2 ≤ 1`. Apply the tactic sequence `intro i; fin_cases i <;> simp <;> omega`. Establish `hA : relDeltaHalf k (fun j i => Fin (bm.1 i j)) y = 1`. Rewrite using `[relDeltaHalf_apply]`. Use `Finset.prod_eq_one fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[deltaHalf_apply, Fin.prod_univ_two, hdet, hdet, modExp_two_zero, modExp_two_one]`. Simplify using `only [Fintype.card_fin]`. Apply the tactic sequence `have hj : bm.1 0 j + bm.1 1 j = 1 ∨ torEntry k d p j = 1 := by fin_cases j`. Conclude with `Or.inl hc0`. Conclude with `Or.inr t1`.

Conclude with `Or.inl hc2`. Break down `hj with hj | hj` into its components or cases. Apply the tactic sequence `rcases (by omega : (bm.1 0 j = 0 ∧ bm.1 1 j = 1) ∨ (bm.1 0 j = 1 ∧ bm.1 1 j = 0)) with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp [h0, h1]`. Simplify using `[hj]`. Establish `hB : ∀ i, (deltaHalf k (fun j => Fin (bm.1 i j)) (swapBlocks k (fun i j => Fin (bm.1 i j)) y i))⁻¹ = absPow k ((1 - (b i : ℂ)) / 2) p.1 ^ bm.1 i 0 * absPow k (((b i : ℂ) - 1) / 2) p.2 ^ bm.1 i 2`.

Introduce `i`. Rewrite using `[deltaHalf_apply, Fin.prod_univ_three]`. Apply the tactic sequence `have e : ∀ j, Matrix.GeneralLinearGroup.det (swapBlocks k (fun i j => Fin (bm.1 i j)) y i j) = torEntry k d p j ^ bm.1 i j := fun j => hdet j i`. Rewrite using `[e, e, e, t0, t1, t2, one_pow, map_one, mul_one, mul_inv, modExp_three_zero, modExp_three_two]`. Establish `hb` using `congrArg (Nat.cast : ℕ → ℂ) (hrow i)`.

Move the coercions through the operations in `at hb`. Simplify using `only [Fintype.card_fin]`. Use `congr 1`. Use `absPow_pow_inv (hle0 i) (fun h => ?_) _` and prove the remaining obligations. Rewrite `hb` using `[h]`.

Move the coercions through the operations in `at hb ⊢`. Rewrite using `[← hb]`. Expand and normalize the polynomial expressions, which then agree. Use `absPow_pow_inv (hle2 i) (fun h => ?_) _` and prove the remaining obligations. Rewrite `hb` using `[h]`.

Move the coercions through the operations in `at hb ⊢`. Rewrite using `[← hb]`. Expand and normalize the polynomial expressions, which then agree. Establish `hC : pairChar k b χ (relEmb k f (swapBlocks k (fun i j => Fin (bm.1 i j)) y)) = ∏ i, χ i p.1 ^ bm.1 i 0 * χ i p.2 ^ bm.1 i 2`. Simplify using `only [pairChar, MonoidHom.finsetProd_apply, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, detChar_apply]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `have e : ∀ j, Matrix.GeneralLinearGroup.det (swapBlocks k (fun i j => Fin (bm.1 i j)) y i j) = torEntry k d p j ^ bm.1 i j := fun j => hdet j i`. Rewrite using `[relEmb_apply, det_leviEmb, Fin.prod_univ_three, e, e, e, t0, t1, t2, one_pow, mul_one, map_mul, map_pow, map_pow]`. Unfold `cellScalar cellChar₂`. Use `congr 1`.

Rewrite using `[← hydef, hA, hC, relDeltaHalf_apply, ← Finset.prod_inv_distrib, Finset.prod_congr rfl fun i _ => hB i, Fin.prod_univ_two, Fin.prod_univ_two]`. Apply the tactic sequence `fin_cases r <;> fin_cases r' <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] at hr hr' ⊢`. Rewrite using `[hr, hr', show bm.1 1 0 = 0 by omega, show bm.1 1 2 = 0 by omega]; simp only [pow_one, pow_zero, one_mul, mul_one]; ext; push_cast; ring`. Rewrite using `[hr, hr', show bm.1 1 0 = 0 by omega, show bm.1 0 2 = 0 by omega]; simp only [pow_one, pow_zero, one_mul, mul_one]; ext; push_cast; ring`. Rewrite using `[hr, hr', show bm.1 0 0 = 0 by omega, show bm.1 1 2 = 0 by omega]; simp only [pow_one, pow_zero, one_mul, mul_one]; ext; push_cast; ring`.

Rewrite using `[hr, hr', show bm.1 0 0 = 0 by omega, show bm.1 0 2 = 0 by omega]; simp only [pow_one, pow_zero, one_mul, mul_one]; ext; push_cast; ring`.
-/
theorem cellScalar_tor3 (d : ℕ) (b : Fin 2 → ℕ) (χ : Fin 2 → kˣ →* ℂˣ) (p : kˣ × kˣ)
    (bm : SizeMatrix (fun j : Fin 2 => Fin (b j)) (fun j : Fin 3 => Fin (sz3 d j)))
    (f : ∀ r, (Σ j, Fin (bm.1 r j)) ≃ Fin (b r)) (g : ∀ j, (Σ r, Fin (bm.1 r j)) ≃ Fin (sz3 d j))
    (r r' : Fin 2) (hr : bm.1 r 0 = 1) (hr' : bm.1 r' 2 = 1) :
    ((cellScalar f g (pairChar k b χ) ⟨tor3 k d p, tor3_mem_relParab d p g⟩ : ℂˣ) : ℂ) = cellChar₂ k b χ r r' p := by
  have hy := relProj_tor3 (k := k) d p g
  set y := relProj k g ⟨tor3 k d p, tor3_mem_relParab d p g⟩ with hydef
  have hdet : ∀ j i, Matrix.GeneralLinearGroup.det (y j i) = torEntry k d p j ^ bm.1 i j := by
    intro j i
    rw [hy, det_scalar', Fintype.card_fin]
  have t0 : torEntry k d p 0 = p.1 := by simp [torEntry]
  have t1 : torEntry k d p 1 = 1 := by simp [torEntry]
  have t2 : torEntry k d p 2 = p.2 := by simp [torEntry]
  have hc0 : bm.1 0 0 + bm.1 1 0 = 1 := by
    have := bm.2.2 0
    simpa [Fin.sum_univ_two, sz3] using this
  have hc2 : bm.1 0 2 + bm.1 1 2 = 1 := by
    have := bm.2.2 2
    simpa [Fin.sum_univ_two, sz3] using this
  have hrow : ∀ i, bm.1 i 0 + bm.1 i 1 + bm.1 i 2 = b i := by
    intro i
    have := bm.2.1 i
    simpa [Fin.sum_univ_three] using this
  have hle0 : ∀ i, bm.1 i 0 ≤ 1 := by
    intro i; fin_cases i <;> simp <;> omega
  have hle2 : ∀ i, bm.1 i 2 ≤ 1 := by
    intro i; fin_cases i <;> simp <;> omega
  have hA : relDeltaHalf k (fun j i => Fin (bm.1 i j)) y = 1 := by
    rw [relDeltaHalf_apply]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [deltaHalf_apply, Fin.prod_univ_two, hdet, hdet, modExp_two_zero, modExp_two_one]
    simp only [Fintype.card_fin]
    have hj : bm.1 0 j + bm.1 1 j = 1 ∨ torEntry k d p j = 1 := by
      fin_cases j
      · exact Or.inl hc0
      · exact Or.inr t1
      · exact Or.inl hc2
    rcases hj with hj | hj
    · rcases (by omega : (bm.1 0 j = 0 ∧ bm.1 1 j = 1) ∨ (bm.1 0 j = 1 ∧ bm.1 1 j = 0)) with
        ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp [h0, h1]
    · simp [hj]
  have hB : ∀ i, (deltaHalf k (fun j => Fin (bm.1 i j)) (swapBlocks k (fun i j => Fin (bm.1 i j)) y i))⁻¹ =
      absPow k ((1 - (b i : ℂ)) / 2) p.1 ^ bm.1 i 0 * absPow k (((b i : ℂ) - 1) / 2) p.2 ^ bm.1 i 2 := by
    intro i
    rw [deltaHalf_apply, Fin.prod_univ_three]
    have e : ∀ j, Matrix.GeneralLinearGroup.det (swapBlocks k (fun i j => Fin (bm.1 i j)) y i j) =
        torEntry k d p j ^ bm.1 i j := fun j => hdet j i
    rw [e, e, e, t0, t1, t2, one_pow, map_one, mul_one, mul_inv, modExp_three_zero, modExp_three_two]
    have hb := congrArg (Nat.cast : ℕ → ℂ) (hrow i)
    push_cast at hb
    simp only [Fintype.card_fin]
    congr 1
    · refine absPow_pow_inv (hle0 i) (fun h => ?_) _
      rw [h] at hb; push_cast at hb ⊢; rw [← hb]; ring
    · refine absPow_pow_inv (hle2 i) (fun h => ?_) _
      rw [h] at hb; push_cast at hb ⊢; rw [← hb]; ring
  have hC : pairChar k b χ (relEmb k f (swapBlocks k (fun i j => Fin (bm.1 i j)) y)) =
      ∏ i, χ i p.1 ^ bm.1 i 0 * χ i p.2 ^ bm.1 i 2 := by
    simp only [pairChar, MonoidHom.finsetProd_apply, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, detChar_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    have e : ∀ j, Matrix.GeneralLinearGroup.det (swapBlocks k (fun i j => Fin (bm.1 i j)) y i j) =
        torEntry k d p j ^ bm.1 i j := fun j => hdet j i
    rw [relEmb_apply, det_leviEmb, Fin.prod_univ_three, e, e, e, t0, t1, t2, one_pow, mul_one, map_mul, map_pow,
      map_pow]
  unfold cellScalar cellChar₂
  congr 1
  rw [← hydef, hA, hC, relDeltaHalf_apply, ← Finset.prod_inv_distrib, Finset.prod_congr rfl fun i _ => hB i,
    Fin.prod_univ_two, Fin.prod_univ_two]
  fin_cases r <;> fin_cases r' <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] at hr hr' ⊢
  · rw [hr, hr', show bm.1 1 0 = 0 by omega, show bm.1 1 2 = 0 by omega]; simp only [pow_one, pow_zero, one_mul, mul_one]; ext; push_cast; ring
  · rw [hr, hr', show bm.1 1 0 = 0 by omega, show bm.1 0 2 = 0 by omega]; simp only [pow_one, pow_zero, one_mul, mul_one]; ext; push_cast; ring
  · rw [hr, hr', show bm.1 0 0 = 0 by omega, show bm.1 1 2 = 0 by omega]; simp only [pow_one, pow_zero, one_mul, mul_one]; ext; push_cast; ring
  · rw [hr, hr', show bm.1 0 0 = 0 by omega, show bm.1 0 2 = 0 by omega]; simp only [pow_one, pow_zero, one_mul, mul_one]; ext; push_cast; ring

/- English proof (translation)
Establish `hc0 : ∀ bm : SizeMatrix (fun j : Fin 2 => Fin (b j)) (fun j : Fin 3 => Fin (sz3 d j)), bm.1 0 0 + bm.1 1 0 = 1` using `fun bm => by`. Use `bm.2.2 0` as an intermediate fact. Simplify `this` using `[Fin.sum_univ_two, sz3]`. Establish `hc2 : ∀ bm : SizeMatrix (fun j : Fin 2 => Fin (b j)) (fun j : Fin 3 => Fin (sz3 d j)), bm.1 0 2 + bm.1 1 2 = 1` using `fun bm => by`. Use `bm.2.2 2` as an intermediate fact.

Simplify `this` using `[Fin.sum_univ_two, sz3]`. Establish `hrow : ∀ (bm : SizeMatrix (fun j : Fin 2 => Fin (b j)) (fun j : Fin 3 => Fin (sz3 d j))) i, bm.1 i 0 + bm.1 i 1 + bm.1 i 2 = b i` using `fun bm i => by`. Use `bm.2.1 i` as an intermediate fact. Simplify `this` using `[Fin.sum_univ_three]`. Use `⟨fun bm => if bm.1 0 0 = 1 then 0 else 1, fun bm => if bm.1 0 2 = 1 then 0 else 1, fun bm => ?_, fun bm => ?_, fun s t h h' => ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `have := hc0 bm dsimp only split_ifs with h <;> omega`. Apply the tactic sequence `have := hc2 bm dsimp only split_ifs with h <;> omega`. Establish `a1` using `hc0 s`. Establish `a2` using `hc0 t`. Establish `a3` using `hc2 s`.

Establish `a4` using `hc2 t`. Establish `a5` using `hrow s 0`. Establish `a6` using `hrow s 1`. Establish `a7` using `hrow t 0`. Establish `a8` using `hrow t 1`.

Apply the tactic sequence `have e0 : s.1 0 0 = t.1 0 0 := by dsimp only at h split_ifs at h <;> first | omega | exact absurd h (by decide)`. Apply the tactic sequence `have e2 : s.1 0 2 = t.1 0 2 := by dsimp only at h' split_ifs at h' <;> first | omega | exact absurd h' (by decide)`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;> omega`.
-/
theorem exists_rows (d : ℕ) (b : Fin 2 → ℕ) :
    ∃ (r : SizeMatrix (fun j : Fin 2 => Fin (b j)) (fun j : Fin 3 => Fin (sz3 d j)) → Fin 2)
      (r' : SizeMatrix (fun j : Fin 2 => Fin (b j)) (fun j : Fin 3 => Fin (sz3 d j)) → Fin 2),
      (∀ bm : SizeMatrix (fun j : Fin 2 => Fin (b j)) (fun j : Fin 3 => Fin (sz3 d j)), bm.1 (r bm) 0 = 1) ∧
      (∀ bm : SizeMatrix (fun j : Fin 2 => Fin (b j)) (fun j : Fin 3 => Fin (sz3 d j)), bm.1 (r' bm) 2 = 1) ∧
      ∀ s t, r s = r t → r' s = r' t → s = t := by
  have hc0 : ∀ bm : SizeMatrix (fun j : Fin 2 => Fin (b j)) (fun j : Fin 3 => Fin (sz3 d j)),
      bm.1 0 0 + bm.1 1 0 = 1 := fun bm => by
    have := bm.2.2 0
    simpa [Fin.sum_univ_two, sz3] using this
  have hc2 : ∀ bm : SizeMatrix (fun j : Fin 2 => Fin (b j)) (fun j : Fin 3 => Fin (sz3 d j)),
      bm.1 0 2 + bm.1 1 2 = 1 := fun bm => by
    have := bm.2.2 2
    simpa [Fin.sum_univ_two, sz3] using this
  have hrow : ∀ (bm : SizeMatrix (fun j : Fin 2 => Fin (b j)) (fun j : Fin 3 => Fin (sz3 d j))) i,
      bm.1 i 0 + bm.1 i 1 + bm.1 i 2 = b i := fun bm i => by
    have := bm.2.1 i
    simpa [Fin.sum_univ_three] using this
  refine ⟨fun bm => if bm.1 0 0 = 1 then 0 else 1, fun bm => if bm.1 0 2 = 1 then 0 else 1,
    fun bm => ?_, fun bm => ?_, fun s t h h' => ?_⟩
  · have := hc0 bm
    dsimp only
    split_ifs with h <;> omega
  · have := hc2 bm
    dsimp only
    split_ifs with h <;> omega
  · have a1 := hc0 s
    have a2 := hc0 t
    have a3 := hc2 s
    have a4 := hc2 t
    have a5 := hrow s 0
    have a6 := hrow s 1
    have a7 := hrow t 0
    have a8 := hrow t 1
    have e0 : s.1 0 0 = t.1 0 0 := by
      dsimp only at h
      split_ifs at h <;> first | omega | exact absurd h (by decide)
    have e2 : s.1 0 2 = t.1 0 2 := by
      dsimp only at h'
      split_ifs at h' <;> first | omega | exact absurd h' (by decide)
    apply Subtype.ext
    funext i j
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;> omega

end Cells

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `hG k _ _ _ _ d h2 b hb χ hsm`. Unfold `pairInd`. Take `⟨M, bb, hbb⟩` from `hG k (Fin 2) (Fin 3) (Fin d) (fun j => Fin (b j)) (fun j => Fin (sz3 d j)) (pairPlace b hb) (place3 h2)`. Establish `hchar : IsSmoothChar (pairChar k b χ)`. Unfold `pairChar`.

Use `Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) ?_ fun a _ => ?_` and prove the remaining obligations. Unfold `IsSmoothChar`. Simplify using the standard rewrite rules. Conclude with `(hsm a).detChar.comp _ (continuous_apply a)`. Take `⟨S, hmono, h0, htop, hS⟩` from `hbb ℂ (ofChar (pairChar k b χ)) ((isSmooth_ofChar_iff _).2 hchar)`.

Take `⟨r, r', hr, hr', hinj⟩` from `exists_rows d b`. Use `⟨M, fun t => (S t).toSubmodule, fun t => r (bb t), fun t => r' (bb t), fun s t hst => hmono hst, (congrArg Subrepresentation.toSubmodule h0).trans (toSubmodule_bot' _), (congrArg Subrepresentation.toSubmodule htop).trans (toSubmodule_top' _), fun s t h h' => bb.injective (hinj _ …` and prove the remaining obligations. Take `⟨f⟩` from `(bb t).nonempty_rows`. Take `⟨g⟩` from `(bb t).nonempty_cols`. Establish `φ` using `Classical.choice (hS t f g)`.

Rewrite using `[← cellScalar_tor3 d b χ p (bb t) f g _ _ (hr _) (hr' _)]`. Set `x : (S t.succ).toSubmodule ⧸ Submodule.comap (S t.succ).toSubmodule.subtype (S t.castSucc).toSubmodule` to `Submodule.Quotient.mk ⟨v, hv⟩`. Establish `hq : subQuot (S t.succ) (S t.castSucc) (tor3 k d p) x = ((cellScalar f g (pairChar k b χ) ⟨tor3 k d p, tor3_mem_relParab d p g⟩ : ℂˣ) : ℂ) • x`. Apply `φ.toLinearEquiv.injective` to reduce the goal to its premises. Establish `h1 : φ.toLinearEquiv (subQuot (S t.succ) (S t.castSucc) (tor3 k d p) x) = cellFunctor f g (ofChar (pairChar k b χ)) (tor3 k d p) (φ.toLinearEquiv x)` using `Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap (tor3 k d p) x`.

Use `h1.trans ((cellFunctor_ofChar_central f g _ _ (tor3_mem_relParab d p g) (tor3_comm d p) _).trans ?_)` and prove the remaining obligations. Conclude with `(φ.toLinearEquiv.map_smul _ _).symm`. Establish `h3` using `(Submodule.Quotient.eq _).1 (show (Submodule.Quotient.mk ((S t.succ).toRepresentation (tor3 k d p) ⟨v, hv⟩) : (S t.succ).toSubmodule ⧸ Submodule.comap (S t.succ).toSubmodule.subtype (S t.castSucc).toSubmodule) = Submodule.Quotient.mk (((cellScalar f g (pairChar k b χ) ⟨tor3 k d p …`. Conclude with `h3`.
-/
theorem jacquet_cells : GlobalTheory.Published.GeometricLemmaFiltration → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (d : ℕ) (h2 : 2 ≤ d) (b : Fin 2 → ℕ) (hb : b 0 + b 1 = d) (χ : Fin 2 → kˣ →* ℂˣ),
    (∀ j, IsSmoothChar (χ j)) →
    ∃ (M : ℕ) (S : Fin (M + 1) → Submodule ℂ (Jacquet (pairInd k b hb χ) (unipRad k (place3 h2))))
      (r r' : Fin M → Fin 2),
      Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last M) = ⊤ ∧ (∀ s t, r s = r t → r' s = r' t → s = t) ∧
      ∀ t, ∀ v ∈ S t.succ, ∀ p : kˣ × kˣ,
        jac (place3 h2) (pairInd k b hb χ) (tor3 k d p) v - cellChar₂ k b χ (r t) (r' t) p • v ∈ S t.castSucc := by
  intro hG k _ _ _ _ d h2 b hb χ hsm
  unfold pairInd
  obtain ⟨M, bb, hbb⟩ := hG k (Fin 2) (Fin 3) (Fin d) (fun j => Fin (b j))
    (fun j => Fin (sz3 d j)) (pairPlace b hb) (place3 h2)
  have hchar : IsSmoothChar (pairChar k b χ) := by
    unfold pairChar
    refine Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) ?_ fun a _ => ?_
    · unfold IsSmoothChar; simp
    · exact (hsm a).detChar.comp _ (continuous_apply a)
  obtain ⟨S, hmono, h0, htop, hS⟩ := hbb ℂ (ofChar (pairChar k b χ)) ((isSmooth_ofChar_iff _).2 hchar)
  obtain ⟨r, r', hr, hr', hinj⟩ := exists_rows d b
  refine ⟨M, fun t => (S t).toSubmodule, fun t => r (bb t), fun t => r' (bb t), fun s t hst => hmono hst,
    (congrArg Subrepresentation.toSubmodule h0).trans (toSubmodule_bot' _),
    (congrArg Subrepresentation.toSubmodule htop).trans (toSubmodule_top' _),
    fun s t h h' => bb.injective (hinj _ _ h h'), fun t v hv p => ?_⟩
  obtain ⟨f⟩ := (bb t).nonempty_rows
  obtain ⟨g⟩ := (bb t).nonempty_cols
  have φ := Classical.choice (hS t f g)
  rw [← cellScalar_tor3 d b χ p (bb t) f g _ _ (hr _) (hr' _)]
  let x : (S t.succ).toSubmodule ⧸ Submodule.comap (S t.succ).toSubmodule.subtype (S t.castSucc).toSubmodule :=
    Submodule.Quotient.mk ⟨v, hv⟩
  have hq : subQuot (S t.succ) (S t.castSucc) (tor3 k d p) x =
      ((cellScalar f g (pairChar k b χ) ⟨tor3 k d p, tor3_mem_relParab d p g⟩ : ℂˣ) : ℂ) • x := by
    apply φ.toLinearEquiv.injective
    have h1 : φ.toLinearEquiv (subQuot (S t.succ) (S t.castSucc) (tor3 k d p) x) =
        cellFunctor f g (ofChar (pairChar k b χ)) (tor3 k d p) (φ.toLinearEquiv x) :=
      Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap (tor3 k d p) x
    refine h1.trans ((cellFunctor_ofChar_central f g _ _ (tor3_mem_relParab d p g) (tor3_comm d p) _).trans ?_)
    exact (φ.toLinearEquiv.map_smul _ _).symm
  have h3 := (Submodule.Quotient.eq _).1 (show
    (Submodule.Quotient.mk ((S t.succ).toRepresentation (tor3 k d p) ⟨v, hv⟩) :
      (S t.succ).toSubmodule ⧸ Submodule.comap (S t.succ).toSubmodule.subtype (S t.castSucc).toSubmodule) =
      Submodule.Quotient.mk
        (((cellScalar f g (pairChar k b χ) ⟨tor3 k d p, tor3_mem_relParab d p g⟩ : ℂˣ) : ℂ) •
          (⟨v, hv⟩ : (S t.succ).toSubmodule)) from hq)
  exact h3

end GlobalTheory.IndJacBlock
