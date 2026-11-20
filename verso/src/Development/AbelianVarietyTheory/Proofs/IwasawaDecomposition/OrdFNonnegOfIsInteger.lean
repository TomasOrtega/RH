import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.Chr.DetOrd

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Establish `ha : w.valuation L (a : L) ≠ 0` using `by simp`. Establish `hb : w.valuation L (b : L) ≠ 0` using `by simp`. Unfold `ordF`. Rewrite using `[Units.val_mul, map_mul, WithZero.log_mul ha hb]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ordF_mul' (w : HeightOneSpectrum (𝓞 L)) (a b : Lˣ) : ordF w (a * b) = ordF w a + ordF w b := by
  have ha : w.valuation L (a : L) ≠ 0 := by simp
  have hb : w.valuation L (b : L) ≠ 0 := by simp
  unfold ordF
  rw [Units.val_mul, map_mul, WithZero.log_mul ha hb]
  ring

/- English proof (translation)
Take `⟨r, hr⟩` from `h`. Establish `ha : w.valuation L (a : L) ≠ 0` using `by simp`. Establish `hle : w.valuation L (a : L) ≤ 1`. Rewrite using `[← hr]`. Conclude with `w.valuation_le_one r`.

Use `(WithZero.log_le_log ha one_ne_zero).2 hle` as an intermediate fact. Unfold `ordF`. Simplify using `using this`.
-/
theorem ordF_nonneg_of_isInteger (w : HeightOneSpectrum (𝓞 L)) (a : Lˣ)
    (h : IsLocalization.IsInteger (𝓞 L) (a : L)) : 0 ≤ ordF w a := by
  obtain ⟨r, hr⟩ := h
  have ha : w.valuation L (a : L) ≠ 0 := by simp
  have hle : w.valuation L (a : L) ≤ 1 := by
    rw [← hr]; exact w.valuation_le_one r
  have := (WithZero.log_le_log ha one_ne_zero).2 hle
  unfold ordF
  simpa using this

/- English proof (translation)
Use `((HeightOneSpectrum.Support.finite (𝓞 L) (a : L)).union (HeightOneSpectrum.Support.finite (𝓞 L) ((a⁻¹ : Lˣ) : L))).subset fun w hw => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Simplify using `only [Set.mem_union, not_or, HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hn`. Apply `hw` to reduce the goal to its premises. Establish `h0 : w.valuation L (a : L) ≠ 0` using `by simp`.

Establish `h1 : w.valuation L (a : L) = 1`. Use `le_antisymm hn.1 ?_` and prove the remaining obligations. Establish `h2` using `hn.2`. Rewrite `h2` using `[Units.val_inv_eq_inv_val, map_inv₀]`. Conclude with `(inv_le_one₀ (zero_lt_iff.2 h0)).1 h2`.

Simplify using `[ordF, h1]`.
-/
theorem ordF_finite (a : Lˣ) : {w : HeightOneSpectrum (𝓞 L) | ordF w a ≠ 0}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 L) (a : L)).union
    (HeightOneSpectrum.Support.finite (𝓞 L) ((a⁻¹ : Lˣ) : L))).subset fun w hw => ?_
  by_contra hn
  simp only [Set.mem_union, not_or, HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hn
  apply hw
  have h0 : w.valuation L (a : L) ≠ 0 := by simp
  have h1 : w.valuation L (a : L) = 1 := by
    refine le_antisymm hn.1 ?_
    have h2 := hn.2
    rw [Units.val_inv_eq_inv_val, map_inv₀] at h2
    exact (inv_le_one₀ (zero_lt_iff.2 h0)).1 h2
  simp [ordF, h1]

/- English proof (translation)
Take `⟨a, ha, hint⟩` from `Formalism.L2.LamCM.A2.exists_den M hM`. Use `⟨a ^ N, pow_mem ha N, fun b hb => ?_⟩` and prove the remaining obligations. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem d hd`. Take `⟨x, hx, rfl⟩` from `hd`.

Establish `: (a ^ N) • (Matrix.of x).det = (Matrix.of fun i j => a • x i j).det`. Rewrite using `[show (Matrix.of fun i j => a • x i j) = (algebraMap (𝓞 L) L a) • Matrix.of x by`. Use extensionality with `i j`. Simplify using `[Algebra.smul_def]]`. Rewrite using `[Matrix.det_smul, Fintype.card_fin, Algebra.smul_def, map_pow]`.

Rewrite using `[this]`. Conclude with `Formalism.L2.LamCM.A2.isInteger_det _ fun i j => hint _ (hx i) j`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `IsLocalization.isInteger_add hx hy`.

Consider the case `smul r x _ hx => rw [smul_comm]`. Conclude with `IsLocalization.isInteger_smul hx`.
-/
theorem isFractional_detSub {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L)) (hM : M.FG) :
    IsFractional (𝓞 L)⁰ (detSub M) := by
  obtain ⟨a, ha, hint⟩ := Formalism.L2.LamCM.A2.exists_den M hM
  refine ⟨a ^ N, pow_mem ha N, fun b hb => ?_⟩
  induction hb using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨x, hx, rfl⟩ := hd
    have : (a ^ N) • (Matrix.of x).det = (Matrix.of fun i j => a • x i j).det := by
      rw [show (Matrix.of fun i j => a • x i j) = (algebraMap (𝓞 L) L a) • Matrix.of x by
        ext i j; simp [Algebra.smul_def]]
      rw [Matrix.det_smul, Fintype.card_fin, Algebra.smul_def, map_pow]
    rw [this]
    exact Formalism.L2.LamCM.A2.isInteger_det _ fun i j => hint _ (hx i) j
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy => rw [smul_add]; exact IsLocalization.isInteger_add hx hy
  | smul r x _ hx => rw [smul_comm]; exact IsLocalization.isInteger_smul hx

/- English proof (translation)
Take `⟨a, ha, hint⟩` from `h`. Establish `ha0 : algebraMap (𝓞 L) L a ≠ 0`. Simplify using `using nonZeroDivisors.ne_zero ha`. Use `⟨Units.mk0 _ ha0, fun w k hk => ?_⟩` and prove the remaining obligations. Establish `h1` using `ordF_nonneg_of_isInteger w (Units.mk0 _ ha0 * k) (by`.

Use `hint _ hk` as an intermediate fact. Rewrite using `[Algebra.smul_def] at this)` and apply the resulting hypothesis. Rewrite `h1` using `[ordF_mul']`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_bound {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) :
    ∃ d : Lˣ, ∀ w : HeightOneSpectrum (𝓞 L), ∀ k : Lˣ, (k : L) ∈ A → -ordF w d ≤ ordF w k := by
  obtain ⟨a, ha, hint⟩ := h
  have ha0 : algebraMap (𝓞 L) L a ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero ha
  refine ⟨Units.mk0 _ ha0, fun w k hk => ?_⟩
  have h1 := ordF_nonneg_of_isInteger w (Units.mk0 _ ha0 * k) (by
    have := hint _ hk
    rwa [Algebra.smul_def] at this)
  rw [ordF_mul'] at h1
  linarith

/- English proof (translation)
Take `⟨d, hd⟩` from `exists_bound h`. Establish `hb : BddBelow {n | ∃ k : Lˣ, (k : L) ∈ A ∧ ordF w k = n}` using `⟨-ordF w d, by rintro n ⟨k, hk, rfl⟩; exact hd w k hk⟩`. Conclude with `⟨Int.csInf_mem ⟨_, k0, hk0, rfl⟩ hb, fun n hn => csInf_le hb hn⟩`.
-/
theorem isLeast_ordSub {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) (k0 : Lˣ) (hk0 : (k0 : L) ∈ A)
    (w : HeightOneSpectrum (𝓞 L)) :
    IsLeast {n | ∃ k : Lˣ, (k : L) ∈ A ∧ ordF w k = n} (ordSub w A) := by
  obtain ⟨d, hd⟩ := exists_bound h
  have hb : BddBelow {n | ∃ k : Lˣ, (k : L) ∈ A ∧ ordF w k = n} :=
    ⟨-ordF w d, by rintro n ⟨k, hk, rfl⟩; exact hd w k hk⟩
  exact ⟨Int.csInf_mem ⟨_, k0, hk0, rfl⟩ hb, fun n hn => csInf_le hb hn⟩

/- English proof (translation)
Take `⟨d, hd⟩` from `exists_bound h`. Use `((ordF_finite d).union (ordF_finite k0)).subset fun w hw => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Simplify using `only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hn`. Apply `hw` to reduce the goal to its premises.

Take `⟨⟨k, hk, e⟩, hl⟩` from `isLeast_ordSub h k0 hk0 w`. Establish `h1` using `hl ⟨k0, hk0, rfl⟩`. Establish `h2` using `hd w k hk`. Use linear arithmetic over natural numbers and integers.
-/
theorem ordSub_finite {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) (k0 : Lˣ) (hk0 : (k0 : L) ∈ A) :
    {w : HeightOneSpectrum (𝓞 L) | ordSub w A ≠ 0}.Finite := by
  obtain ⟨d, hd⟩ := exists_bound h
  refine ((ordF_finite d).union (ordF_finite k0)).subset fun w hw => ?_
  by_contra hn
  simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hn
  apply hw
  obtain ⟨⟨k, hk, e⟩, hl⟩ := isLeast_ordSub h k0 hk0 w
  have h1 := hl ⟨k0, hk0, rfl⟩
  have h2 := hd w k hk
  omega

/- English proof (translation)
Establish `: (Matrix.of fun i => γ.mulVec (x i)) = Matrix.of x * γ.transpose`. Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]`. Rewrite using `[this, Matrix.det_mul, Matrix.det_transpose, mul_comm]`.
-/
theorem det_of_mulVec {N : ℕ} (γ : Matrix (Fin N) (Fin N) L) (x : Fin N → Fin N → L) :
    (Matrix.of fun i => γ.mulVec (x i)).det = γ.det * (Matrix.of x).det := by
  have : (Matrix.of fun i => γ.mulVec (x i)) = Matrix.of x * γ.transpose := by
    ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [this, Matrix.det_mul, Matrix.det_transpose, mul_comm]

/- English proof (translation)
Unfold `detSub`. Rewrite using `[Submodule.map_span]`. Use `congr 1`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩ choose x hx e using fun i => Submodule.mem_map.1 (hy i)`. Use `⟨_, ⟨x, hx, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `: y = fun i => γ.mulVec (x i)` using `funext fun i => by`. Rewrite using `[← e i]`. Simplify using the standard rewrite rules.

Rewrite using `[this, det_of_mulVec]`. Both sides reduce to the same expression. Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, rfl⟩`. Use `⟨fun i => γ.mulVec (x i), fun i => Submodule.mem_map.2 ⟨x i, hx i, by simp⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[det_of_mulVec]`.

Both sides reduce to the same expression.
-/
theorem detSub_map {N : ℕ} (γ : Matrix (Fin N) (Fin N) L) (M : Submodule (𝓞 L) (Fin N → L)) :
    detSub (M.map ((Matrix.toLin' γ).restrictScalars (𝓞 L))) =
      (detSub M).map (LinearMap.mulLeft (𝓞 L) γ.det) := by
  unfold detSub
  rw [Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    choose x hx e using fun i => Submodule.mem_map.1 (hy i)
    refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
    have : y = fun i => γ.mulVec (x i) := funext fun i => by
      rw [← e i]; simp
    rw [this, det_of_mulVec]
    rfl
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨fun i => γ.mulVec (x i), fun i => Submodule.mem_map.2 ⟨x i, hx i, by simp⟩, ?_⟩
    rw [det_of_mulVec]
    rfl

/- English proof (translation)
Take `⟨⟨k, hk, e⟩, hl⟩` from `isLeast_ordSub h k0 hk0 w`. Use `IsLeast.csInf_eq ⟨⟨u * k, Submodule.mem_map.2 ⟨k, hk, rfl⟩, by rw [ordF_mul', e]⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `n ⟨k', hk', rfl⟩`. Take `⟨y, hy, ey⟩` from `Submodule.mem_map.1 hk'`. Establish `ey' : (u : L) * y = k'` using `ey`.

Establish `hy' : ((u⁻¹ * k' : Lˣ) : L) = y`. Rewrite using `[Units.val_mul, ← ey', Units.inv_mul_cancel_left]`. Establish `h1` using `hl ⟨u⁻¹ * k', hy' ▸ hy, rfl⟩`. Establish `h2 : ordF w k' = ordF w u + ordF w (u⁻¹ * k')`. Rewrite using `[← ordF_mul', mul_inv_cancel_left]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem ordSub_map_mul {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) (k0 : Lˣ) (hk0 : (k0 : L) ∈ A)
    (u : Lˣ) (w : HeightOneSpectrum (𝓞 L)) :
    ordSub w (A.map (LinearMap.mulLeft (𝓞 L) (u : L))) = ordF w u + ordSub w A := by
  obtain ⟨⟨k, hk, e⟩, hl⟩ := isLeast_ordSub h k0 hk0 w
  refine IsLeast.csInf_eq ⟨⟨u * k, Submodule.mem_map.2 ⟨k, hk, rfl⟩, by rw [ordF_mul', e]⟩, ?_⟩
  rintro n ⟨k', hk', rfl⟩
  obtain ⟨y, hy, ey⟩ := Submodule.mem_map.1 hk'
  have ey' : (u : L) * y = k' := ey
  have hy' : ((u⁻¹ * k' : Lˣ) : L) = y := by
    rw [Units.val_mul, ← ey', Units.inv_mul_cancel_left]
  have h1 := hl ⟨u⁻¹ * k', hy' ▸ hy, rfl⟩
  have h2 : ordF w k' = ordF w u + ordF w (u⁻¹ * k') := by
    rw [← ordF_mul', mul_inv_cancel_left]
  omega

end GlobalTheory.Mem.Chr.DetOrd

namespace GlobalTheory.Mem.Chr

open DetOrd

open Classical in

/- English proof (translation)
Introduce `L _ _ N M hfg hsp`. Establish `hf` using `isFractional_detSub M hfg`. Take `⟨x, hx, hd⟩` from `Formalism.L2.LamCM.A2.exists_det_ne M hsp`. Establish `hk : ((Units.mk0 _ hd : Lˣ) : L) ∈ detSub M` using `det_mem_detSub x hx`. Use `⟨ordSub_finite hf _ hk, isLeast_ordSub hf _ hk, fun γ u hu w => ?_⟩` and prove the remaining obligations.

Establish `e` using `detSub_map γ M`. Establish `hu' : γ.det = u` using `by convert hu`. Rewrite `e` using `[hu']`. Use `ordSub_map_mul hf _ hk u w` as an intermediate fact. Rewrite `this` using `[← e]`.

Use `this` and compare the differences between its conclusion and the goal.
-/
theorem ordSub_detSub_lattice :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (M : Submodule (𝓞 L) (Fin N → L)), M.FG → Submodule.span L (M : Set (Fin N → L)) = ⊤ → {w | ordSub w (detSub M) ≠ 0}.Finite ∧ (∀ w, IsLeast {n | ∃ k : Lˣ, (k : L) ∈ detSub M ∧ ordF w k = n} (ordSub w (detSub M))) ∧ ∀ (γ : Matrix (Fin N) (Fin N) L) (u : Lˣ), γ.det = u → ∀ w, ordSub w (detSub (M.map ((Matrix.toLin' γ).restrictScalars (𝓞 L)))) = ordF w u + ordSub w (detSub M) := by
  intro L _ _ N M hfg hsp
  have hf := isFractional_detSub M hfg
  obtain ⟨x, hx, hd⟩ := Formalism.L2.LamCM.A2.exists_det_ne M hsp
  have hk : ((Units.mk0 _ hd : Lˣ) : L) ∈ detSub M := det_mem_detSub x hx
  refine ⟨ordSub_finite hf _ hk, isLeast_ordSub hf _ hk, fun γ u hu w => ?_⟩
  have e := detSub_map γ M
  have hu' : γ.det = u := by convert hu
  rw [hu'] at e
  have := ordSub_map_mul hf _ hk u w
  rw [← e] at this
  convert this

end GlobalTheory.Mem.Chr
