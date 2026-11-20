import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.OfSInvCoe

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.MomentRationality.Ht

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

abbrev gi (g : GL (Fin N) L) : Matrix (Fin N) (Fin N) L := ((g⁻¹ : GL (Fin N) L) : Matrix (Fin N) (Fin N) L)

/- English proof (translation)
Introduce `h`. Establish `h1` using `hc w`. Rewrite `h1` using `[h, zero_smul]`. Establish `h2 : (mt c w).det = 1` using `(c w).prop`. Use `haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩`.

Rewrite `h2` using `[h1, Matrix.det_zero]`. Conclude with `zero_ne_one h2`.
-/
theorem z_ne (hN : 1 ≤ N) {g : GL (Fin N) L} {z : InfinitePlace L → ℂ} {c : Sp L N}
    (hc : ∀ w, mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding) (w : InfinitePlace L) : z w ≠ 0 := by
  intro h
  have h1 := hc w
  rw [h, zero_smul] at h1
  have h2 : (mt c w).det = 1 := (c w).prop
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [h1, Matrix.det_zero] at h2
  exact zero_ne_one h2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem emb_toL (y : Lat L N) (w : InfinitePlace L) (a : Fin N) : w.embedding (toL y a) = toR y w a := rfl

/- English proof (translation)
Establish `hz` using `z_ne hN hc w`. Establish `hgg : (g : Matrix (Fin N) (Fin N) L) * gi g = 1` using `g.mul_inv`. Establish `hinv : mt c⁻¹ w * mt c w = 1` using `by show (((c w)⁻¹ : Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * (c w : Matrix (Fin N) (Fin N) ℂ) = 1`. Rewrite using `[← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]`. Establish `hx : toR y w = mt c w *ᵥ ((z w)⁻¹ • (fun a => w.embedding ((gi g *ᵥ toL y) a)))`.

Rewrite using `[hc w, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hz, one_smul]`. Use function extensionality and compare the values at `a`. Express the relevant statement in the definitionally equal form `toR y w a = ((g : Matrix (Fin N) (Fin N) L).map w.embedding *ᵥ (w.embedding ∘ (gi g *ᵥ toL y))) a`. Rewrite using `[← RingHom.map_mulVec, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec, emb_toL]`. Rewrite using `[hx, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]`.
-/
theorem cinv_vec (hN : 1 ≤ N) {g : GL (Fin N) L} {z : InfinitePlace L → ℂ} {c : Sp L N}
    (hc : ∀ w, mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding) (y : Lat L N) (w : InfinitePlace L) :
    mt c⁻¹ w *ᵥ toR y w = (z w)⁻¹ • (fun a => w.embedding ((gi g *ᵥ toL y) a)) := by
  have hz := z_ne hN hc w
  have hgg : (g : Matrix (Fin N) (Fin N) L) * gi g = 1 := g.mul_inv
  have hinv : mt c⁻¹ w * mt c w = 1 := by
    show (((c w)⁻¹ : Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * (c w : Matrix (Fin N) (Fin N) ℂ) = 1
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hx : toR y w = mt c w *ᵥ ((z w)⁻¹ • (fun a => w.embedding ((gi g *ᵥ toL y) a))) := by
    rw [hc w, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hz, one_smul]
    funext a
    change toR y w a = ((g : Matrix (Fin N) (Fin N) L).map w.embedding *ᵥ (w.embedding ∘ (gi g *ᵥ toL y))) a
    rw [← RingHom.map_mulVec, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec, emb_toL]
  rw [hx, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

/- English proof (translation)
Rewrite using `[hc w, transpose_smul, smul_mulVec, ← transpose_map]`. Use `congr 1`. Use extensionality with `a`. Use `RingHom.map_mulVec w.embedding (g : Matrix (Fin N) (Fin N) L)ᵀ (toL y) a` as an intermediate fact. Rewrite using `[this]`.

Both sides reduce to the same expression.
-/
theorem cT_vec {g : GL (Fin N) L} {z : InfinitePlace L → ℂ} {c : Sp L N}
    (hc : ∀ w, mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding) (y : Lat L N) (w : InfinitePlace L) :
    (mt c w)ᵀ *ᵥ toR y w = z w • (fun a => w.embedding (((g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y) a)) := by
  rw [hc w, transpose_smul, smul_mulVec, ← transpose_map]
  congr 1
  ext a
  have := RingHom.map_mulVec w.embedding (g : Matrix (Fin N) (Fin N) L)ᵀ (toL y) a
  rw [this]
  rfl

/- English proof (translation)
Introduce `h`. Apply `hy` to reduce the goal to its premises. Use function extensionality and compare the values at `a`. Establish `h1` using `congrFun h a`. Simplify `h1` using `[toL]`.
-/
theorem toL_ne {y : Lat L N} (hy : y ≠ 0) : toL y ≠ 0 := by
  intro h
  apply hy
  funext a
  have h1 := congrFun h a
  simpa [toL] using h1

/- English proof (translation)
Introduce `h`. Apply `toL_ne hy` to reduce the goal to its premises. Use `congrArg (fun v => (g : Matrix (Fin N) (Fin N) L) *ᵥ v) h` as an intermediate fact. Simplify `this` using `[mulVec_mulVec, Units.mul_inv, one_mulVec]`.
-/
theorem gi_ne (g : GL (Fin N) L) {y : Lat L N} (hy : y ≠ 0) : gi g *ᵥ toL y ≠ 0 := by
  intro h
  apply toL_ne hy
  have := congrArg (fun v => (g : Matrix (Fin N) (Fin N) L) *ᵥ v) h
  simpa [mulVec_mulVec, Units.mul_inv, one_mulVec] using this

/- English proof (translation)
Introduce `h`. Apply `toL_ne hy` to reduce the goal to its premises. Establish `h2 : (gi g)ᵀ * (g : Matrix (Fin N) (Fin N) L)ᵀ = 1`. Rewrite using `[← Matrix.transpose_mul, g.mul_inv, Matrix.transpose_one]`. Establish `h1 : (gi g)ᵀ *ᵥ ((g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y) = (gi g)ᵀ *ᵥ 0` using `by rw [h]`.

Rewrite `h1` using `[Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, Matrix.mulVec_zero]`. Then use the resulting hypothesis.
-/
theorem gT_ne (g : GL (Fin N) L) {y : Lat L N} (hy : y ≠ 0) : (g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y ≠ 0 := by
  intro h
  apply toL_ne hy
  have h2 : (gi g)ᵀ * (g : Matrix (Fin N) (Fin N) L)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, g.mul_inv, Matrix.transpose_one]
  have h1 : (gi g)ᵀ *ᵥ ((g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y) = (gi g)ᵀ *ᵥ 0 := by rw [h]
  rwa [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, Matrix.mulVec_zero] at h1

/- English proof (translation)
Simplify using `only [mulVec, dotProduct, Finset.mul_sum]`. Use `IsIntegral.sum _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc]`. Conclude with `(hd a j).mul (RingOfIntegers.isIntegral_coe (y j))`.
-/
theorem int_d {d : ℤ} {G : Matrix (Fin N) (Fin N) L} (hd : ∀ i j, IsIntegral ℤ ((d : L) * G i j)) (y : Lat L N)
    (a : Fin N) : IsIntegral ℤ ((d : L) * (G *ᵥ toL y) a) := by
  simp only [mulVec, dotProduct, Finset.mul_sum]
  refine IsIntegral.sum _ fun j _ => ?_
  rw [← mul_assoc]
  exact (hd a j).mul (RingOfIntegers.isIntegral_coe (y j))

/- English proof (translation)
Establish `hdR : (d : ℝ) ≠ 0` using `Int.cast_ne_zero.mpr hd`. Set `α : 𝓞 L` to `⟨(d : L) * β, hint⟩`. Establish `hαc : ((α : 𝓞 L) : L) = (d : L) * β` using `rfl`. Establish `hα0 : α ≠ 0`. Introduce `h`.

Establish `h1 : ((α : 𝓞 L) : L) = 0` using `by rw [h]; rfl`. Rewrite `h1` using `[hαc]`. Conclude with `mul_ne_zero (Int.cast_ne_zero.mpr hd) hβ h1`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : ∃ w : InfinitePlace L, 1 ≤ w ((α : 𝓞 L) : L) := by`. Assume the negation of the conclusion as `H`.

Use `push_neg at H`. Take `⟨w0⟩ : Nonempty (InfinitePlace L)` from `inferInstance`. Conclude with `absurd (InfinitePlace.one_le_of_lt_one hα0 (fun z _ => H z)) (not_le.mpr (H w0))`. Establish `hwα : w ((α : 𝓞 L) : L) = |(d : ℝ)| * ‖w.embedding β‖`. Rewrite using `[← InfinitePlace.norm_embedding_eq, hαc, map_mul, norm_mul, map_intCast, Complex.norm_intCast]`.

Establish `hd2 : (0 : ℝ) < (d : ℝ) ^ 2` using `by positivity`. Establish `h1 : 1 ≤ (d : ℝ) ^ 2 * ‖w.embedding β‖ ^ 2`. Establish `h2 : (1 : ℝ) ≤ (|(d : ℝ)| * ‖w.embedding β‖) ^ 2` using `one_le_pow₀ (hwα ▸ hw)`. Rewrite `h2` using `[mul_pow, sq_abs]`. Then use the resulting hypothesis. Establish `key : ((d : ℝ) ^ 2)⁻¹ ≤ ‖w.embedding β‖ ^ 2`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `key.trans (Finset.single_le_sum (f := fun v : InfinitePlace L => ‖v.embedding β‖ ^ 2) (fun v _ => sq_nonneg _) (Finset.mem_univ w))`.
-/
theorem sum_sq_ge (hL : IsTotallyComplex L) {d : ℤ} (hd : d ≠ 0) {β : L} (hβ : β ≠ 0)
    (hint : IsIntegral ℤ ((d : L) * β)) : ((d : ℝ) ^ 2)⁻¹ ≤ ∑ w : InfinitePlace L, ‖w.embedding β‖ ^ 2 := by
  have hdR : (d : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hd
  let α : 𝓞 L := ⟨(d : L) * β, hint⟩
  have hαc : ((α : 𝓞 L) : L) = (d : L) * β := rfl
  have hα0 : α ≠ 0 := by
    intro h
    have h1 : ((α : 𝓞 L) : L) = 0 := by rw [h]; rfl
    rw [hαc] at h1
    exact mul_ne_zero (Int.cast_ne_zero.mpr hd) hβ h1
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace L, 1 ≤ w ((α : 𝓞 L) : L) := by
    by_contra H
    push_neg at H
    obtain ⟨w0⟩ : Nonempty (InfinitePlace L) := inferInstance
    exact absurd (InfinitePlace.one_le_of_lt_one hα0 (fun z _ => H z)) (not_le.mpr (H w0))
  have hwα : w ((α : 𝓞 L) : L) = |(d : ℝ)| * ‖w.embedding β‖ := by
    rw [← InfinitePlace.norm_embedding_eq, hαc, map_mul, norm_mul, map_intCast, Complex.norm_intCast]
  have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  have h1 : 1 ≤ (d : ℝ) ^ 2 * ‖w.embedding β‖ ^ 2 := by
    have h2 : (1 : ℝ) ≤ (|(d : ℝ)| * ‖w.embedding β‖) ^ 2 := one_le_pow₀ (hwα ▸ hw)
    rwa [mul_pow, sq_abs] at h2
  have key : ((d : ℝ) ^ 2)⁻¹ ≤ ‖w.embedding β‖ ^ 2 := by
    calc ((d : ℝ) ^ 2)⁻¹ = ((d : ℝ) ^ 2)⁻¹ * 1 := (mul_one _).symm
      _ ≤ ((d : ℝ) ^ 2)⁻¹ * ((d : ℝ) ^ 2 * ‖w.embedding β‖ ^ 2) := by gcongr
      _ = ‖w.embedding β‖ ^ 2 := by field_simp
  exact key.trans (Finset.single_le_sum (f := fun v : InfinitePlace L => ‖v.embedding β‖ ^ 2)
    (fun v _ => sq_nonneg _) (Finset.mem_univ w))

end PositivityTheory.KB.MomentRationality.Ht
