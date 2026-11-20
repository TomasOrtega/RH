import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PCtSatDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetCoverMatrixValuationOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLevelsEqIntegralGLOfUnramified
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevOpParabEqLevOpCt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockLevelsTwistedConstantTermSplitPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSatEqOfIsCT

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Introduce `e` and use `by simp [IsUnifV, e] at hϖ`.
-/
theorem b_unif_ne_zero {w : Pl E} {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) : ϖ ≠ 0 := fun e => by
  simp [IsUnifV, e] at hϖ

/- English proof (translation)
Rewrite `h` using `[hϖ, ← WithZero.coe_pow, ← WithZero.coe_pow, WithZero.coe_inj, ← ofAdd_nsmul, ← ofAdd_nsmul]`. Use `Multiplicative.ofAdd.injective h` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem b_pow_inj {w : Pl E} {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) {i j : ℕ}
    (h : Valued.v ϖ ^ i = Valued.v ϖ ^ j) : i = j := by
  rw [hϖ, ← WithZero.coe_pow, ← WithZero.coe_pow, WithZero.coe_inj, ← ofAdd_nsmul, ← ofAdd_nsmul] at h
  have := Multiplicative.ofAdd.injective h
  simp at this
  omega

/- English proof (translation)
Take `⟨x, hx, y, hy, e⟩` from `Set.mem_of_indicator_ne_zero h`. Rewrite using `[e, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, GlobalTheory.GLintCover.det_v hx, GlobalTheory.GLintCover.det_v hy, GlobalTheory.SphGal.det_diagJ ϖ hi, map_pow, one_mul, mul_one]`.
-/
theorem b_val_det_of_Tj {m : ℕ} {w : Pl E} {ϖ : w.adicCompletion E} {g : GLw m w} {i : ℕ} (hi : i ≤ m)
    (h : Tj ℂ m (Ov E w) ϖ i g ≠ 0) :
    Valued.v (g : Matrix (Fin m) (Fin m) (w.adicCompletion E)).det = Valued.v ϖ ^ i := by
  obtain ⟨x, hx, y, hy, e⟩ := Set.mem_of_indicator_ne_zero h
  rw [e, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, GlobalTheory.GLintCover.det_v hx, GlobalTheory.GLintCover.det_v hy,
    GlobalTheory.SphGal.det_diagJ ϖ hi, map_pow, one_mul, mul_one]

/- English proof (translation)
The claim follows from `(Tj_mem_hecke hϖ j).1 ⟨_, inv_mem hκ⟩ ⟨_, hκ⟩ g`.
-/
theorem b_Tj_conj {m : ℕ} {w : Pl E} {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (j : ℕ) {κ : GLw m w}
    (hκ : κ ∈ KGL w m) (g : GLw m w) : Tj ℂ m (Ov E w) ϖ j (κ⁻¹ * g * κ) = Tj ℂ m (Ov E w) ϖ j g :=
  (Tj_mem_hecke hϖ j).1 ⟨_, inv_mem hκ⟩ ⟨_, hκ⟩ g

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `h` to reduce the goal to its premises. Unfold `avg`. Simplify using `[hc]`.
-/
theorem b_exists_of_avg_ne_zero {H : Type} [Group H] (u : H → ℂ) (h : avg u ≠ 0) : ∃ x, u x ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  unfold avg
  simp [hc]

/- English proof (translation)
Rewrite using `[Matrix.coe_units_inv, CtLevel.blk_val]`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]`. Simplify using `[Matrix.mul_assoc, Matrix.mul_neg]`. Conclude with `Matrix.submatrix_one_equiv (CtLevel.blkEq h).symm`.
-/
theorem b_blk_inv_val {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (((blk h w m X)⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.reindex (CtLevel.blkEq h) (CtLevel.blkEq h)
        (Matrix.fromBlocks ((m.1⁻¹ : GLw a w) : Matrix (Fin a) (Fin a) (w.adicCompletion E))
          (-(X * ((m.2⁻¹ : GLw b w) : Matrix (Fin b) (Fin b) (w.adicCompletion E)))) 0
          ((m.2⁻¹ : GLw b w) : Matrix (Fin b) (Fin b) (w.adicCompletion E))) := by
  rw [Matrix.coe_units_inv, CtLevel.blk_val]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [Matrix.mul_assoc, Matrix.mul_neg]
  exact Matrix.submatrix_one_equiv (CtLevel.blkEq h).symm

/- English proof (translation)
Rewrite using `[Units.val_mul, GlobalTheory.WeylGL.tor_val, Matrix.diagonal_mul, zpow_one]`.
-/
theorem b_tor_mul_apply {p : ℕ} {w : Pl E} {ϖ : w.adicCompletion E} (h0 : ϖ ≠ 0) (g : GL (Fin p) (w.adicCompletion E))
    (r s : Fin p) :
    (((GlobalTheory.WeylGL.tor h0 fun _ => (1 : ℤ)) * g : GL (Fin p) (w.adicCompletion E)) : Matrix (Fin p) (Fin p) _) r s =
      ϖ * (g : Matrix (Fin p) (Fin p) (w.adicCompletion E)) r s := by
  rw [Units.val_mul, GlobalTheory.WeylGL.tor_val, Matrix.diagonal_mul, zpow_one]

/- English proof (translation)
Use `⟨⟨fun r s => ?_, fun r s => ?_⟩, fun r s => ?_, fun r s => ?_⟩` and prove the remaining obligations. Use `h1 (CtLevel.blkEq h (Sum.inl r)) (CtLevel.blkEq h (Sum.inl s))` as an intermediate fact. Simplify `this` using `[CtLevel.blk_val, Matrix.reindex_apply]`. Use `h2 (CtLevel.blkEq h (Sum.inl r)) (CtLevel.blkEq h (Sum.inl s))` as an intermediate fact. Rewrite `this` using `[b_tor_mul_apply, b_blk_inv_val]`.

Rewrite using `[b_tor_mul_apply]`. Simplify `this` using `[Matrix.reindex_apply]`. Use `h1 (CtLevel.blkEq h (Sum.inr r)) (CtLevel.blkEq h (Sum.inr s))` as an intermediate fact. Simplify `this` using `[CtLevel.blk_val, Matrix.reindex_apply]`. Use `h2 (CtLevel.blkEq h (Sum.inr r)) (CtLevel.blkEq h (Sum.inr s))` as an intermediate fact.

Rewrite `this` using `[b_tor_mul_apply, b_blk_inv_val]`. Rewrite using `[b_tor_mul_apply]`. Simplify `this` using `[Matrix.reindex_apply]`.
-/
theorem b_int_blocks {n a b : ℕ} (h : a + b = n) (w : Pl E) {ϖ : w.adicCompletion E} (h0 : ϖ ≠ 0)
    (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E))
    (h1 : GlobalTheory.WeylGL.IntM (blk h w m X)) (h2 : GlobalTheory.WeylGL.IntM ((GlobalTheory.WeylGL.tor h0 fun _ => 1) * (blk h w m X)⁻¹)) :
    (GlobalTheory.WeylGL.IntM m.1 ∧ GlobalTheory.WeylGL.IntM ((GlobalTheory.WeylGL.tor h0 fun _ => 1) * m.1⁻¹)) ∧
      (GlobalTheory.WeylGL.IntM m.2 ∧ GlobalTheory.WeylGL.IntM ((GlobalTheory.WeylGL.tor h0 fun _ => 1) * m.2⁻¹)) := by
  refine ⟨⟨fun r s => ?_, fun r s => ?_⟩, fun r s => ?_, fun r s => ?_⟩
  · have := h1 (CtLevel.blkEq h (Sum.inl r)) (CtLevel.blkEq h (Sum.inl s))
    simpa [CtLevel.blk_val, Matrix.reindex_apply] using this
  · have := h2 (CtLevel.blkEq h (Sum.inl r)) (CtLevel.blkEq h (Sum.inl s))
    rw [b_tor_mul_apply, b_blk_inv_val] at this
    rw [b_tor_mul_apply]
    simpa [Matrix.reindex_apply] using this
  · have := h1 (CtLevel.blkEq h (Sum.inr r)) (CtLevel.blkEq h (Sum.inr s))
    simpa [CtLevel.blk_val, Matrix.reindex_apply] using this
  · have := h2 (CtLevel.blkEq h (Sum.inr r)) (CtLevel.blkEq h (Sum.inr s))
    rw [b_tor_mul_apply, b_blk_inv_val] at this
    rw [b_tor_mul_apply]
    simpa [Matrix.reindex_apply] using this

/- English proof (translation)
Rewrite using `[← hd]`. Unfold `dosetInd`. Rewrite using `[Set.indicator_of_mem (GlobalTheory.WeylGL.mem_doset.2 ⟨1, one_mem _, 1, one_mem _, by group⟩)]`. Simplify using the standard rewrite rules.
-/
theorem b_Tj_self {p : ℕ} {w : Pl E} {ϖ : w.adicCompletion E} {g : GLw p w} {i : ℕ}
    (hd : dosetInd ℂ (KGL w p) g = Tj ℂ p (Ov E w) ϖ i) : Tj ℂ p (Ov E w) ϖ i g ≠ 0 := by
  rw [← hd]
  unfold dosetInd
  rw [Set.indicator_of_mem (GlobalTheory.WeylGL.mem_doset.2 ⟨1, one_mem _, 1, one_mem _, by group⟩)]
  simp

/- English proof (translation)
Establish `h0` using `b_unif_ne_zero hϖ`. Unfold `ctT ctMu at hm`. Establish `hc` using `right_ne_zero_of_mul hm`. Unfold `ct at hc`. Take `⟨X, hX⟩` from `CtLevel.exists_ne_zero_of_hint_ne_zero _ _ (right_ne_zero_of_mul hc)`.

Take `⟨κ, hκ⟩` from `b_exists_of_avg_ne_zero _ hX`. Use `beta_reduce at hκ`. Rewrite `hκ` using `[SplitLevels.toSub_of_mem _ _ (SplitLevels.mem_UL_split hw _)]`. Establish `hT : Tj ℂ n (Ov E w) ϖ k (blk h w m (Multiplicative.toAdd X)) ≠ 0`. Rewrite using `[← b_Tj_conj hϖ k κ.2]`.

Conclude with `hκ`. Take `⟨i1, i2⟩` from `GlobalTheory.SatInd.intM_of_Tj h0 hϖ hT`. Take `⟨⟨a1, a2⟩, b1, b2⟩` from `b_int_blocks h w h0 m _ i1 i2`. Take `⟨i, hi, hdi⟩` from `GlobalTheory.SatInd.dosetInd_eq_Tj h0 hϖ a1 a2`. Take `⟨j, hj, hdj⟩` from `GlobalTheory.SatInd.dosetInd_eq_Tj h0 hϖ b1 b2`.

Establish `t1` using `b_Tj_self hdi`. Establish `t2` using `b_Tj_self hdj`. Establish `hdet : ((blk h w m (Multiplicative.toAdd X) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).det = (m.1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)).det * (m.2 : Matrix (Fin b) (Fin b) (w.adicCompletion E)).det`. Rewrite using `[CtLevel.blk_val, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]`. Establish `e` using `b_val_det_of_Tj hk hT`.

Rewrite `e` using `[hdet, map_mul, b_val_det_of_Tj hi t1, b_val_det_of_Tj hj t2, ← pow_add]`. Establish `hk'` using `b_pow_inj hϖ e`. Use `⟨(i, j), ?_, t1, t2⟩` and prove the remaining obligations. Simplify using `only [pairsK, Finset.mem_filter, Finset.mem_product, Finset.mem_range]`. Use linear arithmetic over natural numbers and integers.
-/
theorem ctT_supp {n a b : ℕ} (h : a + b = n) (w : Pl E) (hw : IsSplitAt w) (ν : (w.adicCompletion E)ˣ →* ℂˣ)
    {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (k : ℕ) (hk : k ≤ n) (m : GLw a w × GLw b w)
    (hm : ctT h w ν ϖ k m ≠ 0) :
    ∃ p ∈ pairsK a b k, Tj ℂ a (Ov E w) ϖ p.1 m.1 ≠ 0 ∧ Tj ℂ b (Ov E w) ϖ p.2 m.2 ≠ 0 := by
  have h0 := b_unif_ne_zero hϖ
  unfold ctT ctMu at hm
  have hc := right_ne_zero_of_mul hm
  unfold ct at hc
  obtain ⟨X, hX⟩ := CtLevel.exists_ne_zero_of_hint_ne_zero _ _ (right_ne_zero_of_mul hc)
  obtain ⟨κ, hκ⟩ := b_exists_of_avg_ne_zero _ hX
  beta_reduce at hκ
  rw [SplitLevels.toSub_of_mem _ _ (SplitLevels.mem_UL_split hw _)] at hκ
  have hT : Tj ℂ n (Ov E w) ϖ k (blk h w m (Multiplicative.toAdd X)) ≠ 0 := by
    rw [← b_Tj_conj hϖ k κ.2]; exact hκ
  obtain ⟨i1, i2⟩ := GlobalTheory.SatInd.intM_of_Tj h0 hϖ hT
  obtain ⟨⟨a1, a2⟩, b1, b2⟩ := b_int_blocks h w h0 m _ i1 i2
  obtain ⟨i, hi, hdi⟩ := GlobalTheory.SatInd.dosetInd_eq_Tj h0 hϖ a1 a2
  obtain ⟨j, hj, hdj⟩ := GlobalTheory.SatInd.dosetInd_eq_Tj h0 hϖ b1 b2
  have t1 := b_Tj_self hdi
  have t2 := b_Tj_self hdj
  have hdet : ((blk h w m (Multiplicative.toAdd X) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).det =
      (m.1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)).det * (m.2 : Matrix (Fin b) (Fin b) (w.adicCompletion E)).det := by
    rw [CtLevel.blk_val, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  have e := b_val_det_of_Tj hk hT
  rw [hdet, map_mul, b_val_det_of_Tj hi t1, b_val_det_of_Tj hj t2, ← pow_add] at e
  have hk' := b_pow_inj hϖ e
  refine ⟨(i, j), ?_, t1, t2⟩
  simp only [pairsK, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

/- English proof (translation)
Take `⟨a1, a2⟩` from `GlobalTheory.AdelicU.mem_GLint_iff.1 h1`. Take `⟨b1, b2⟩` from `GlobalTheory.AdelicU.mem_GLint_iff.1 h2`. Use `GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[CtLevel.dgM_val]`. Conclude with `CtLevel.blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ a1 b1 i j`.

Rewrite using `[← map_inv, CtLevel.dgM_val]`. Conclude with `CtLevel.blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ a2 b2 i j`.
-/
theorem b_dgM_mem {n a b : ℕ} (h : a + b = n) (w : Pl E) (κ : GLw a w × GLw b w) (h1 : κ.1 ∈ KGL w a)
    (h2 : κ.2 ∈ KGL w b) : CtLevel.dgM h w κ ∈ KGL w n := by
  obtain ⟨a1, a2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 h1
  obtain ⟨b1, b2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 h2
  refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [CtLevel.dgM_val]; exact CtLevel.blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ a1 b1 i j
  · rw [← map_inv, CtLevel.dgM_val]; exact CtLevel.blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ a2 b2 i j

end PositivityTheory.Rg.BcB.F.RS
