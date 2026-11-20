import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeIndicatorFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetOrderBoundedHeckeSupportStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockIntegralIffStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockInverseIntegralIffStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockDetOrderAddStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermHeckeFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIndicatorIntegralIndexStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIndexEqDiagonalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalLatticeIndexPowStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharacterBlockValueStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusHalfBlockValueStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeVectorLinearCombinationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatakeEigenvaluePairDecompositionStatement
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.mul_apply] exact (Ov E w).sum_mem fun l _ => (Ov E w).mul_mem (hM i l) (hN l j)`.
-/
theorem IsInt.mul {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r s t : Type} [Fintype s]
    {M : Matrix r s (w.adicCompletion E)} {N : Matrix s t (w.adicCompletion E)} (hM : IsInt w M) (hN : IsInt w N) :
    IsInt w (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact (Ov E w).sum_mem fun l _ => (Ov E w).mul_mem (hM i l) (hN l j)

/- English proof (translation)
Rewrite using `[GlobalTheory.T.hecke_indicator_formula E w n k ϖ hϖ hk]`. Use `if_congr ?_ rfl rfl` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.block_integral_iff E n a b h w m X, GlobalTheory.T.block_inverse_integral_iff E n a b h w ϖ m X, GlobalTheory.T.block_det_order_add E n a b h w m X]`. The claim follows by propositional logic.
-/
theorem tj_blk (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (ϖ : w.adicCompletion E)
    (hϖ : IsUnifV E w ϖ) (k : ℕ) (hk : k ≤ n) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    Tj ℂ n (Ov E w) ϖ k (blk h w m X) =
      if IsInt w m.1.val ∧ IsInt w m.2.val ∧ IsInt w (m.1.val * X) ∧ IsInt w (ϖ • (m.1⁻¹).val) ∧ IsInt w (ϖ • (m.2⁻¹).val) ∧
        IsInt w (ϖ • (X * (m.2⁻¹).val)) ∧ ordL m.1.val.det + ordL m.2.val.det = (k : ℤ) then 1 else 0 := by
  rw [GlobalTheory.T.hecke_indicator_formula E w n k ϖ hϖ hk]
  refine if_congr ?_ rfl rfl
  rw [GlobalTheory.T.block_integral_iff E n a b h w m X, GlobalTheory.T.block_inverse_integral_iff E n a b h w ϖ m X, GlobalTheory.T.block_det_order_add E n a b h w m X]
  tauto

/- English proof (translation)
Establish `hle : intSub a b w ≤ latM ϖ m` using `fun X hX => by`. Use `⟨i1.mul hX, ?_⟩` and prove the remaining obligations. Establish `e : ϖ • (X * (m.2⁻¹).val) = X * (ϖ • (m.2⁻¹).val)` using `(Matrix.mul_smul _ _ _).symm`. Rewrite using `[e]`. Conclude with `IsInt.mul hX j2`.

Use `GlobalTheory.T.lattice_indicator_integral_index E a b w (latM ϖ m) hle` as an intermediate fact. Rewrite `this` using `[GlobalTheory.T.lattice_index_eq_diagonal E a b w ϖ hϖ i j hi hj m t1 t2, GlobalTheory.T.diagonal_lattice_index_pow E a b w ϖ hϖ i j hi hj]`. Rewrite `this` using `[Nat.cast_pow]`. Establish `e2 : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) => if IsInt w (m.1.val * Multiplicative.toAdd X) ∧ IsInt w (ϖ • (Multiplicative.toAdd X * (m.2⁻¹).val)) then (1 : ℂ) else 0) = fun X => if Multiplicative.toAdd X ∈ latM ϖ m then (1 : ℂ) else 0`. Use function extensionality and compare the values at `fun X => if_congr Iff.rfl rfl rfl`.

Rewrite using `[e2]`. Conclude with `this`.
-/
theorem hint_lat (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (ϖ : w.adicCompletion E)
    (hϖ : IsUnifV E w ϖ) (i j : ℕ) (hi : i ≤ a) (hj : j ≤ b) (m : GLw a w × GLw b w)
    (i1 : IsInt w m.1.val) (j2 : IsInt w (ϖ • (m.2⁻¹).val))
    (t1 : Tj ℂ a (Ov E w) ϖ i m.1 ≠ 0) (t2 : Tj ℂ b (Ov E w) ϖ j m.2 ≠ 0) :
    hint (intMat a b w) (fun X => if IsInt w (m.1.val * Multiplicative.toAdd X) ∧
        IsInt w (ϖ • (Multiplicative.toAdd X * (m.2⁻¹).val)) then (1 : ℂ) else 0) = (qV E w : ℂ) ^ (i * (b - j)) := by
  have hle : intSub a b w ≤ latM ϖ m := fun X hX => by
    refine ⟨i1.mul hX, ?_⟩
    have e : ϖ • (X * (m.2⁻¹).val) = X * (ϖ • (m.2⁻¹).val) := (Matrix.mul_smul _ _ _).symm
    rw [e]
    exact IsInt.mul hX j2
  have := GlobalTheory.T.lattice_indicator_integral_index E a b w (latM ϖ m) hle
  rw [GlobalTheory.T.lattice_index_eq_diagonal E a b w ϖ hϖ i j hi hj m t1 t2, GlobalTheory.T.diagonal_lattice_index_pow E a b w ϖ hϖ i j hi hj] at this
  rw [Nat.cast_pow] at this
  have e2 : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      if IsInt w (m.1.val * Multiplicative.toAdd X) ∧ IsInt w (ϖ • (Multiplicative.toAdd X * (m.2⁻¹).val)) then (1 : ℂ) else 0) =
      fun X => if Multiplicative.toAdd X ∈ latM ϖ m then (1 : ℂ) else 0 :=
    funext fun X => if_congr Iff.rfl rfl rfl
  rw [e2]
  exact this

/- English proof (translation)
Establish `hq' : (q : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hq`. Rewrite using `[coef]`. Use `congr 1`. Rewrite using `[← Complex.cpow_natCast (q : ℂ), ← Complex.cpow_add _ _ hq']`. Use `congr 1`.

Move the coercions through the operations in `[Nat.cast_sub hj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coef_eq (q : ℕ) (hq : q ≠ 0) (c : ℂˣ) (a b i j : ℕ) (hj : j ≤ b) :
    (c : ℂ) ^ (i * b + j * a) * ((q : ℂ) ^ (-((i : ℂ) * b - (j : ℂ) * a) / 2) * (q : ℂ) ^ (i * (b - j))) = coef q c a b i j := by
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  rw [coef]
  congr 1
  rw [← Complex.cpow_natCast (q : ℂ), ← Complex.cpow_add _ _ hq']
  congr 1
  push_cast [Nat.cast_sub hj]
  ring

/- English proof (translation)
Unfold `hint`. Rewrite using `[finsum_zero, mul_zero]`.
-/
theorem hint_zero {H : Type} [Group H] (K : Subgroup H) : hint K (fun _ : H => (0 : ℂ)) = 0 := by
  unfold hint
  rw [finsum_zero, mul_zero]

set_option maxHeartbeats 1600000 in
/- English proof (translation)
Rewrite using `[GlobalTheory.T.constant_term_hecke_formula E n a b h w _ ϖ hw hϖ k m]`. Distinguish the cases in `hP : ∃ p ∈ pairs a b k, Tj ℂ a (Ov E w) ϖ p.1 m.1 ≠ 0 ∧ Tj ℂ b (Ov E w) ϖ p.2 m.2 ≠ 0`. Take `⟨⟨i, j⟩, hp, h1, h2⟩` from `hP`. Choose the witnesses or unpack the hypotheses as in `⟨hij, hi, hj⟩ : i + j = k ∧ i ≤ a ∧ j ≤ b := by`. Conclude with `mem_pairs.1 hp`.

Simplify using `only at h1 h2`. Establish `c1` using `GlobalTheory.T.hecke_indicator_formula E w a i ϖ hϖ hi m.1`. Establish `c2` using `GlobalTheory.T.hecke_indicator_formula E w b j ϖ hϖ hj m.2`. Rewrite `h1` using `[c1]`. Rewrite `h2` using `[c2]`.

Choose the witnesses or unpack the hypotheses as in `⟨i1, i2, i3⟩ : IsInt w m.1.val ∧ IsInt w (ϖ • (m.1⁻¹).val) ∧ ordL m.1.val.det = (i : ℤ) := by`. Assume the negation of the conclusion as `hc`. Conclude with `h1 (if_neg hc)`. Choose the witnesses or unpack the hypotheses as in `⟨j1, j2, j3⟩ : IsInt w m.2.val ∧ IsInt w (ϖ • (m.2⁻¹).val) ∧ ordL m.2.val.det = (j : ℤ) := by`. Assume the negation of the conclusion as `hc`.

Conclude with `h2 (if_neg hc)`. Establish `hfun : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) => Tj ℂ n (Ov E w) ϖ k (blk h w m (Multiplicative.toAdd X))) = fun X => if IsInt w (m.1.val * Multiplicative.toAdd X) ∧ IsInt w (ϖ • (Multiplicative.toAdd X * (m.2⁻¹).val)) then (1 : ℂ) else 0`. Use function extensionality and compare the values at `X`. Rewrite using `[tj_blk E n a b h w ϖ hϖ k hk m]`. Establish `e : ordL m.1.val.det + ordL m.2.val.det = (k : ℤ)` using `by rw [i3, j3, ← hij]; push_cast; rfl`.

Distinguish the cases in `hX : IsInt w (m.1.val * Multiplicative.toAdd X) ∧ IsInt w (ϖ • (Multiplicative.toAdd X * (m.2⁻¹).val))`. Rewrite using `[if_pos ⟨i1, j1, hX.1, i2, j2, hX.2, e⟩, if_pos hX]`. Rewrite using `[if_neg fun hc => hX ⟨hc.2.2.1, hc.2.2.2.2.2.1⟩, if_neg hX]`. Establish `u1 : Tj ℂ a (Ov E w) ϖ i m.1 = 1` using `by rw [c1, if_pos ⟨i1, i2, i3⟩]`. Establish `u2 : Tj ℂ b (Ov E w) ϖ j m.2 = 1` using `by rw [c2, if_pos ⟨j1, j2, j3⟩]`.

Establish `t1 : Tj ℂ a (Ov E w) ϖ i m.1 ≠ 0` using `by rw [u1]; exact one_ne_zero`. Establish `t2 : Tj ℂ b (Ov E w) ϖ j m.2 ≠ 0` using `by rw [u2]; exact one_ne_zero`. Rewrite using `[hfun, hint_lat E a b w ϖ hϖ i j hi hj m i1 j2 t1 t2, GlobalTheory.T.unramified_character_block_value E a b w c i j m i3 j3, GlobalTheory.T.modulus_half_block_value E a b w i j m i3 j3, coef_eq _ (qV_ne_zero w) c a b i j hj, Finset.sum_eq_single_of_mem (⟨i, j⟩ : ℕ × ℕ) hp]`. Simplify using `[u1, u2]`. Introduce and unpack `⟨i', j'⟩ hp' hne`.

Choose the witnesses or unpack the hypotheses as in `⟨hij', hi', hj'⟩ : i' + j' = k ∧ i' ≤ a ∧ j' ≤ b := by`. Conclude with `mem_pairs.1 hp'`. Establish `: i' ≠ i` using `fun e => hne (by subst e; congr; omega)`. Establish `u : Tj ℂ a (Ov E w) ϖ i' m.1 = 0`. Rewrite using `[GlobalTheory.T.hecke_indicator_formula E w a i' ϖ hϖ hi' m.1, if_neg]`.

Introduce and unpack `⟨-, -, e⟩`. Conclude with `this (by rw [i3] at e; exact_mod_cast e.symm)`. Simplify using `[u]`. Use `push_neg at hP`. Establish `hz : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) => Tj ℂ n (Ov E w) ϖ k (blk h w m (Multiplicative.toAdd X))) = fun _ => 0`.

Use function extensionality and compare the values at `X`. Rewrite using `[tj_blk E n a b h w ϖ hϖ k hk m, if_neg]`. Introduce and unpack `⟨i1, j1, -, i2, j2, -, e⟩`. Take `⟨i, hi, i3⟩` from `GlobalTheory.T.det_order_bounded_hecke_support E w a ϖ hϖ m.1 i1 i2`. Take `⟨j, hj, j3⟩` from `GlobalTheory.T.det_order_bounded_hecke_support E w b ϖ hϖ m.2 j1 j2`.

Establish `hp : (⟨i, j⟩ : ℕ × ℕ) ∈ pairs a b k`. Establish `: i + j = k` using `by rw [i3, j3] at e; exact_mod_cast e`. Conclude with `mem_pairs.2 ⟨this, hi, hj⟩`. Establish `t1 : Tj ℂ a (Ov E w) ϖ i m.1 ≠ 0`. Rewrite using `[GlobalTheory.T.hecke_indicator_formula E w a i ϖ hϖ hi m.1, if_pos ⟨i1, i2, i3⟩]`.

Conclude with `one_ne_zero`. Establish `t2 : Tj ℂ b (Ov E w) ϖ j m.2 ≠ 0`. Rewrite using `[GlobalTheory.T.hecke_indicator_formula E w b j ϖ hϖ hj m.2, if_pos ⟨j1, j2, j3⟩]`. Conclude with `one_ne_zero`. Conclude with `t2 (hP (i, j) hp t1)`.

Establish `hs : ∑ p ∈ pairs a b k, coef (qV E w) c a b p.1 p.2 * (Tj ℂ a (Ov E w) ϖ p.1 m.1 * Tj ℂ b (Ov E w) ϖ p.2 m.2) = 0`. Use `Finset.sum_eq_zero fun p hp => ?_` and prove the remaining obligations. Distinguish the cases in `t1 : Tj ℂ a (Ov E w) ϖ p.1 m.1 = 0`. Simplify using `[t1]`. Simplify using `[hP p hp t1]`.

Rewrite using `[hz, hs, hint_zero, mul_zero, mul_zero]`.
-/
theorem ct_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (c : ℂˣ)
    (ϖ : w.adicCompletion E) (hw : IsSplitAt w) (hϖ : IsUnifV E w ϖ) (k : ℕ) (hk : k ≤ n) (m : GLw a w × GLw b w) :
    ctT h w (GlobalTheory.SmGL.unrChar (w.adicCompletion E) c) ϖ k m =
      ∑ p ∈ pairs a b k, coef (qV E w) c a b p.1 p.2 * (Tj ℂ a (Ov E w) ϖ p.1 m.1 * Tj ℂ b (Ov E w) ϖ p.2 m.2) := by
  rw [GlobalTheory.T.constant_term_hecke_formula E n a b h w _ ϖ hw hϖ k m]
  by_cases hP : ∃ p ∈ pairs a b k, Tj ℂ a (Ov E w) ϖ p.1 m.1 ≠ 0 ∧ Tj ℂ b (Ov E w) ϖ p.2 m.2 ≠ 0
  · obtain ⟨⟨i, j⟩, hp, h1, h2⟩ := hP
    obtain ⟨hij, hi, hj⟩ : i + j = k ∧ i ≤ a ∧ j ≤ b := by
      exact mem_pairs.1 hp
    simp only at h1 h2
    have c1 := GlobalTheory.T.hecke_indicator_formula E w a i ϖ hϖ hi m.1
    have c2 := GlobalTheory.T.hecke_indicator_formula E w b j ϖ hϖ hj m.2
    rw [c1] at h1
    rw [c2] at h2
    obtain ⟨i1, i2, i3⟩ : IsInt w m.1.val ∧ IsInt w (ϖ • (m.1⁻¹).val) ∧ ordL m.1.val.det = (i : ℤ) := by
      by_contra hc; exact h1 (if_neg hc)
    obtain ⟨j1, j2, j3⟩ : IsInt w m.2.val ∧ IsInt w (ϖ • (m.2⁻¹).val) ∧ ordL m.2.val.det = (j : ℤ) := by
      by_contra hc; exact h2 (if_neg hc)
    have hfun : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        Tj ℂ n (Ov E w) ϖ k (blk h w m (Multiplicative.toAdd X))) =
        fun X => if IsInt w (m.1.val * Multiplicative.toAdd X) ∧
          IsInt w (ϖ • (Multiplicative.toAdd X * (m.2⁻¹).val)) then (1 : ℂ) else 0 := by
      funext X
      rw [tj_blk E n a b h w ϖ hϖ k hk m]
      have e : ordL m.1.val.det + ordL m.2.val.det = (k : ℤ) := by rw [i3, j3, ← hij]; push_cast; rfl
      by_cases hX : IsInt w (m.1.val * Multiplicative.toAdd X) ∧ IsInt w (ϖ • (Multiplicative.toAdd X * (m.2⁻¹).val))
      · rw [if_pos ⟨i1, j1, hX.1, i2, j2, hX.2, e⟩, if_pos hX]
      · rw [if_neg fun hc => hX ⟨hc.2.2.1, hc.2.2.2.2.2.1⟩, if_neg hX]
    have u1 : Tj ℂ a (Ov E w) ϖ i m.1 = 1 := by rw [c1, if_pos ⟨i1, i2, i3⟩]
    have u2 : Tj ℂ b (Ov E w) ϖ j m.2 = 1 := by rw [c2, if_pos ⟨j1, j2, j3⟩]
    have t1 : Tj ℂ a (Ov E w) ϖ i m.1 ≠ 0 := by rw [u1]; exact one_ne_zero
    have t2 : Tj ℂ b (Ov E w) ϖ j m.2 ≠ 0 := by rw [u2]; exact one_ne_zero
    rw [hfun, hint_lat E a b w ϖ hϖ i j hi hj m i1 j2 t1 t2, GlobalTheory.T.unramified_character_block_value E a b w c i j m i3 j3, GlobalTheory.T.modulus_half_block_value E a b w i j m i3 j3,
      coef_eq _ (qV_ne_zero w) c a b i j hj, Finset.sum_eq_single_of_mem (⟨i, j⟩ : ℕ × ℕ) hp]
    · simp [u1, u2]
    · rintro ⟨i', j'⟩ hp' hne
      obtain ⟨hij', hi', hj'⟩ : i' + j' = k ∧ i' ≤ a ∧ j' ≤ b := by
        exact mem_pairs.1 hp'
      have : i' ≠ i := fun e => hne (by subst e; congr; omega)
      have u : Tj ℂ a (Ov E w) ϖ i' m.1 = 0 := by
        rw [GlobalTheory.T.hecke_indicator_formula E w a i' ϖ hϖ hi' m.1, if_neg]
        rintro ⟨-, -, e⟩
        exact this (by rw [i3] at e; exact_mod_cast e.symm)
      simp [u]
  · push_neg at hP
    have hz : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        Tj ℂ n (Ov E w) ϖ k (blk h w m (Multiplicative.toAdd X))) = fun _ => 0 := by
      funext X
      rw [tj_blk E n a b h w ϖ hϖ k hk m, if_neg]
      rintro ⟨i1, j1, -, i2, j2, -, e⟩
      obtain ⟨i, hi, i3⟩ := GlobalTheory.T.det_order_bounded_hecke_support E w a ϖ hϖ m.1 i1 i2
      obtain ⟨j, hj, j3⟩ := GlobalTheory.T.det_order_bounded_hecke_support E w b ϖ hϖ m.2 j1 j2
      have hp : (⟨i, j⟩ : ℕ × ℕ) ∈ pairs a b k := by
        have : i + j = k := by rw [i3, j3] at e; exact_mod_cast e
        exact mem_pairs.2 ⟨this, hi, hj⟩
      have t1 : Tj ℂ a (Ov E w) ϖ i m.1 ≠ 0 := by
        rw [GlobalTheory.T.hecke_indicator_formula E w a i ϖ hϖ hi m.1, if_pos ⟨i1, i2, i3⟩]; exact one_ne_zero
      have t2 : Tj ℂ b (Ov E w) ϖ j m.2 ≠ 0 := by
        rw [GlobalTheory.T.hecke_indicator_formula E w b j ϖ hϖ hj m.2, if_pos ⟨j1, j2, j3⟩]; exact one_ne_zero
      exact t2 (hP (i, j) hp t1)
    have hs : ∑ p ∈ pairs a b k, coef (qV E w) c a b p.1 p.2 * (Tj ℂ a (Ov E w) ϖ p.1 m.1 * Tj ℂ b (Ov E w) ϖ p.2 m.2) = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      by_cases t1 : Tj ℂ a (Ov E w) ϖ p.1 m.1 = 0
      · simp [t1]
      · simp [hP p hp t1]
    rw [hz, hs, hint_zero, mul_zero, mul_zero]

/- English proof (translation)
Introduce `E _ _ _ n a b h w ν c V _ _ ρ x Ba Bb hw hν hs ϖ hϖ k hk`. Substitute `hν` using the available equality. Establish `hF : ctT h w (GlobalTheory.SmGL.unrChar (w.adicCompletion E) c) ϖ k = fun m => ∑ p ∈ pairs a b k, coef (qV E w) c a b p.1 p.2 * (Tj ℂ a (Ov E w) ϖ p.1 m.1 * Tj ℂ b (Ov E w) ϖ p.2 m.2)`. Use function extensionality and compare the values at `fun m => ct_eq E n a b h w c ϖ hw hϖ k hk m`. Rewrite using `[hF, GlobalTheory.T.hecke_vector_linear_combination E a b w ϖ hϖ, GlobalTheory.T.satake_eigenvalue_pair_decomposition _ n a b c Ba Bb (qV_ne_zero w) h hs.2.1 hs.2.2.1 k hk, Finset.sum_smul]`.

Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨-, hi, hj⟩ : p.1 + p.2 = k ∧ p.1 ≤ a ∧ p.2 ≤ b := by`. Conclude with `mem_pairs.1 hp`. Rewrite using `[hs.2.2.2 ϖ hϖ p.1 hi p.2 hj, smul_smul]`.
-/
theorem ctSat : CtSat := by
  intro E _ _ _ n a b h w ν c V _ _ ρ x Ba Bb hw hν hs ϖ hϖ k hk
  subst hν
  have hF : ctT h w (GlobalTheory.SmGL.unrChar (w.adicCompletion E) c) ϖ k = fun m =>
      ∑ p ∈ pairs a b k, coef (qV E w) c a b p.1 p.2 * (Tj ℂ a (Ov E w) ϖ p.1 m.1 * Tj ℂ b (Ov E w) ϖ p.2 m.2) :=
    funext fun m => ct_eq E n a b h w c ϖ hw hϖ k hk m
  rw [hF, GlobalTheory.T.hecke_vector_linear_combination E a b w ϖ hϖ, GlobalTheory.T.satake_eigenvalue_pair_decomposition _ n a b c Ba Bb (qV_ne_zero w) h hs.2.1 hs.2.2.1 k hk, Finset.sum_smul]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨-, hi, hj⟩ : p.1 + p.2 = k ∧ p.1 ≤ a ∧ p.2 ≤ b := by
    exact mem_pairs.1 hp
  rw [hs.2.2.2 ϖ hϖ p.1 hi p.2 hj, smul_smul]

end GlobalTheory.CompanionTheory.CtS
