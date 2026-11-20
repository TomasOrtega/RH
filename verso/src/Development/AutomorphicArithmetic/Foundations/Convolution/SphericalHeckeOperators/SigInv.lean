import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

section

variable {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] {n : ℕ}

/- English proof (translation)
The claim follows from `GroundTheory.LocalField.valuation_algEquiv_apply k E σ x`.
-/
private theorem val_sig (σ : E ≃ₐ[k] E) (x : E) :
    ValuativeRel.valuation E (σ x) = ValuativeRel.valuation E x :=
  GroundTheory.LocalField.valuation_algEquiv_apply k E σ x

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem sig_apply (σ : E ≃ₐ[k] E) (g : GL (Fin n) E) (i j : Fin n) :
    ((PositivityTheory.Rg.Tf.Loc.sigmaGL σ g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
      σ ((g : Matrix (Fin n) (Fin n) E) i j) := rfl

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Rewrite using `[sig_apply, sig_apply, AlgEquiv.symm_apply_apply]`.
-/
private theorem sig_symm (σ : E ≃ₐ[k] E) (g : GL (Fin n) E) :
    PositivityTheory.Rg.Tf.Loc.sigmaGL σ.symm (PositivityTheory.Rg.Tf.Loc.sigmaGL σ g) = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [sig_apply, sig_apply, AlgEquiv.symm_apply_apply]

/- English proof (translation)
Rewrite `hg`, the goal using `[mem_integralGL_iff]`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[sig_apply, Valuation.mem_integer_iff, val_sig]`. Conclude with `hg.1 i j`. Rewrite using `[← map_inv, sig_apply, Valuation.mem_integer_iff, val_sig]`.

Conclude with `hg.2 i j`.
-/
private theorem sig_mem_K (σ : E ≃ₐ[k] E) {g : GL (Fin n) E} (hg : g ∈ integralGL E n) :
    PositivityTheory.Rg.Tf.Loc.sigmaGL σ g ∈ integralGL E n := by
  rw [mem_integralGL_iff] at hg ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [sig_apply, Valuation.mem_integer_iff, val_sig]
    exact hg.1 i j
  · rw [← map_inv, sig_apply, Valuation.mem_integer_iff, val_sig]
    exact hg.2 i j

/- English proof (translation)
Rewrite `hg`, the goal using `[mem_iwahori_iff]`. Use `⟨fun i j => ?_, fun i j h => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[sig_apply, val_sig]`. Conclude with `hg.1 i j`. Rewrite using `[sig_apply, val_sig]`.

Conclude with `hg.2.1 i j h`. Rewrite using `[sig_apply, val_sig]`. Conclude with `hg.2.2 i`.
-/
private theorem sig_mem_I (σ : E ≃ₐ[k] E) {g : GL (Fin n) E} (hg : g ∈ iwahori E n) :
    PositivityTheory.Rg.Tf.Loc.sigmaGL σ g ∈ iwahori E n := by
  rw [mem_iwahori_iff] at hg ⊢
  refine ⟨fun i j => ?_, fun i j h => ?_, fun i => ?_⟩
  · rw [sig_apply, val_sig]
    exact hg.1 i j
  · rw [sig_apply, val_sig]
    exact hg.2.1 i j h
  · rw [sig_apply, val_sig]
    exact hg.2.2 i

/- English proof (translation)
Rewrite using `[mem_iwahori_iff]`. Use `⟨fun i j => ?_, fun i j h => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[coe_diagGL]`. Distinguish the cases in `e : i = j`. Substitute `e` using the available equality.

Rewrite using `[Matrix.diagonal_apply_eq, hd]`. Rewrite using `[Matrix.diagonal_apply_ne _ e, map_zero]`. Conclude with `zero_le'`. Rewrite using `[coe_diagGL, Matrix.diagonal_apply_ne _ h.ne', map_zero]`. Conclude with `zero_lt_one`.

Rewrite using `[coe_diagGL, Matrix.diagonal_apply_eq, hd]`.
-/
private theorem diag_mem_I {d : Fin n → Eˣ} (hd : ∀ i, ValuativeRel.valuation E (d i : E) = 1) :
    diagGL E n d ∈ iwahori E n := by
  rw [mem_iwahori_iff]
  refine ⟨fun i j => ?_, fun i j h => ?_, fun i => ?_⟩
  · rw [coe_diagGL]
    by_cases e : i = j
    · subst e
      rw [Matrix.diagonal_apply_eq, hd]
    · rw [Matrix.diagonal_apply_ne _ e, map_zero]
      exact zero_le'
  · rw [coe_diagGL, Matrix.diagonal_apply_ne _ h.ne', map_zero]
    exact zero_lt_one
  · rw [coe_diagGL, Matrix.diagonal_apply_eq, hd]

/- English proof (translation)
Establish `h0 : (GLnLocal.uniformizer E : E) ≠ 0` using `(uniformizerUnit E).ne_zero`. Establish `hs : σ (GLnLocal.uniformizer E : E) ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff σ σ.injective]` and apply the resulting hypothesis. Set `v : Eˣ` to `Units.mk0 (σ (GLnLocal.uniformizer E : E) / (GLnLocal.uniformizer E : E)) (div_ne_zero hs h0)`. Establish `hv : ValuativeRel.valuation E (v : E) = 1`.

Rewrite using `[Units.val_mk0, map_div₀, val_sig, div_self]`. Conclude with `(Valuation.ne_zero_iff _).2 h0`. Use `⟨diagGL E n fun i => v ^ a i, diag_mem_I fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_zpow_eq_zpow_val, map_zpow₀, hv, one_zpow]`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations.

Rewrite using `[sig_apply, Units.val_mul, coe_torusPow, coe_diagGL, Matrix.diagonal_mul_diagonal]`. Distinguish the cases in `e : i = j`. Substitute `e` using the available equality. Rewrite using `[Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, map_zpow₀, Units.val_zpow_eq_zpow_val, Units.val_mk0, div_zpow, mul_div_cancel₀ _ (zpow_ne_zero _ h0)]`. Rewrite using `[Matrix.diagonal_apply_ne _ e, Matrix.diagonal_apply_ne _ e, map_zero]`.
-/
private theorem sig_torusPow (σ : E ≃ₐ[k] E) (a : Fin n → ℤ) :
    ∃ u ∈ iwahori E n, PositivityTheory.Rg.Tf.Loc.sigmaGL σ (torusPow E n a) = torusPow E n a * u := by
  have h0 : (GLnLocal.uniformizer E : E) ≠ 0 := (uniformizerUnit E).ne_zero
  have hs : σ (GLnLocal.uniformizer E : E) ≠ 0 := by
    rwa [Ne, map_eq_zero_iff σ σ.injective]
  let v : Eˣ := Units.mk0 (σ (GLnLocal.uniformizer E : E) / (GLnLocal.uniformizer E : E)) (div_ne_zero hs h0)
  have hv : ValuativeRel.valuation E (v : E) = 1 := by
    rw [Units.val_mk0, map_div₀, val_sig, div_self]
    exact (Valuation.ne_zero_iff _).2 h0
  refine ⟨diagGL E n fun i => v ^ a i, diag_mem_I fun i => ?_, ?_⟩
  · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hv, one_zpow]
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [sig_apply, Units.val_mul, coe_torusPow, coe_diagGL, Matrix.diagonal_mul_diagonal]
    by_cases e : i = j
    · subst e
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, map_zpow₀, Units.val_zpow_eq_zpow_val,
        Units.val_mk0, div_zpow, mul_div_cancel₀ _ (zpow_ne_zero _ h0)]
    · rw [Matrix.diagonal_apply_ne _ e, Matrix.diagonal_apply_ne _ e, map_zero]

/- English proof (translation)
Take `⟨x, hx, y, hy, rfl⟩` from `h`. Take `⟨u, hu, e⟩` from `sig_torusPow σ a`. Use `⟨PositivityTheory.Rg.Tf.Loc.sigmaGL σ x, sig_mem_I σ hx, u * PositivityTheory.Rg.Tf.Loc.sigmaGL σ y, mul_mem hu (sig_mem_I σ hy), ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, e]`. Simplify using `only [mul_assoc]`.
-/
private theorem sig_mem_dco (σ : E ≃ₐ[k] E) (a : Fin n → ℤ) {g : GL (Fin n) E} (h : g ∈ dco E a) :
    PositivityTheory.Rg.Tf.Loc.sigmaGL σ g ∈ dco E a := by
  obtain ⟨x, hx, y, hy, rfl⟩ := h
  obtain ⟨u, hu, e⟩ := sig_torusPow σ a
  refine ⟨PositivityTheory.Rg.Tf.Loc.sigmaGL σ x, sig_mem_I σ hx, u * PositivityTheory.Rg.Tf.Loc.sigmaGL σ y,
    mul_mem hu (sig_mem_I σ hy), ?_⟩
  rw [map_mul, map_mul, e]
  simp only [mul_assoc]

end

/- English proof (translation)
Introduce `k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ n x`. Establish `hK : PositivityTheory.Rg.Tf.Loc.sigmaGL σ x ∈ integralGL E n ↔ x ∈ integralGL E n` using `⟨fun h => by simpa only [sig_symm] using sig_mem_K σ.symm h, sig_mem_K σ⟩`. Establish `hD : ∀ a : Fin n → ℤ, PositivityTheory.Rg.Tf.Loc.sigmaGL σ x ∈ dco E a ↔ x ∈ dco E a` using `fun a => ⟨fun h => by simpa only [sig_symm] using sig_mem_dco σ.symm a h, sig_mem_dco σ a⟩`. Use `⟨?_, fun a => ?_⟩` and prove the remaining obligations. Unfold `oneK`.

Distinguish the cases in `h : x ∈ integralGL E n`. Rewrite using `[Set.indicator_of_mem (SetLike.mem_coe.2 (hK.2 h)), Set.indicator_of_mem (SetLike.mem_coe.2 h)]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem (fun h' => h (hK.1 h')), Set.indicator_of_notMem h]`. Unfold `uFn`.

Distinguish the cases in `h : x ∈ dco E a`. Rewrite using `[Set.indicator_of_mem ((hD a).2 h), Set.indicator_of_mem h]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem (fun h' => h ((hD a).1 h')), Set.indicator_of_notMem h]`.
-/
theorem UpperTheory.ConvolutionTheory.H.sigInv :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E) (n : ℕ) (x : GL (Fin n) E),
      oneK E n (PositivityTheory.Rg.Tf.Loc.sigmaGL σ x) = oneK E n x ∧ ∀ a : Fin n → ℤ, uFn E a (PositivityTheory.Rg.Tf.Loc.sigmaGL σ x) = uFn E a x := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ n x
  have hK : PositivityTheory.Rg.Tf.Loc.sigmaGL σ x ∈ integralGL E n ↔ x ∈ integralGL E n :=
    ⟨fun h => by simpa only [sig_symm] using sig_mem_K σ.symm h, sig_mem_K σ⟩
  have hD : ∀ a : Fin n → ℤ, PositivityTheory.Rg.Tf.Loc.sigmaGL σ x ∈ dco E a ↔ x ∈ dco E a := fun a =>
    ⟨fun h => by simpa only [sig_symm] using sig_mem_dco σ.symm a h, sig_mem_dco σ a⟩
  refine ⟨?_, fun a => ?_⟩
  · unfold oneK
    by_cases h : x ∈ integralGL E n
    · rw [Set.indicator_of_mem (SetLike.mem_coe.2 (hK.2 h)), Set.indicator_of_mem (SetLike.mem_coe.2 h)]
      rfl
    · rw [Set.indicator_of_notMem (fun h' => h (hK.1 h')), Set.indicator_of_notMem h]
  · unfold uFn
    by_cases h : x ∈ dco E a
    · rw [Set.indicator_of_mem ((hD a).2 h), Set.indicator_of_mem h]
      rfl
    · rw [Set.indicator_of_notMem (fun h' => h ((hD a).1 h')), Set.indicator_of_notMem h]
