import Formalism.LocalToGlobal.Columns.QthPrincInv

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Conj

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq0 : (q : E) ≠ 0)

def QClose {m : ℕ} (W : Sp E m ≃ₗ[E] Sp E m) : Prop :=
  ∀ i j, P.valuation E ((((toGLm E m W : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1) i j) ≤ P.valuation E (q : E)

/- English proof (translation)
Introduce `i j`. Use `set A := ((toGLm E m h⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) with hAdef`. Use `set R := ((toGLm E m r : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) with hRdef`. Use `set B := ((toGLm E m h : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) with hBdef`. Establish `hmul : ((toGLm E m (h⁻¹ * r * h) : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) = A * R * B`.

Rewrite using `[map_mul, map_mul, Units.val_mul, Units.val_mul]`. Establish `hAB : A * B = 1`. Rewrite using `[hAdef, hBdef, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]`. Establish `key : A * R * B - 1 = A * (R - 1) * B`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAB]`.

Rewrite using `[hmul, key]`. Establish `h1` using `qth_conj_le P A (R - 1) B (b : ℤ) (a : ℤ) (N : ℤ) hb hr ha i j`. Use `h1.trans (le_trans ?_ he)` and prove the remaining obligations. Conclude with `WithZero.exp_le_exp.mpr (by omega)`.
-/
theorem qth_conj_close {m : ℕ} (h r : Sp E m ≃ₗ[E] Sp E m) (a b N e : ℕ)
    (ha : ∀ i j, P.valuation E (((toGLm E m h : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) i j) ≤ WithZero.exp (a : ℤ))
    (hb : ∀ i j, P.valuation E (((toGLm E m h⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) i j) ≤ WithZero.exp (b : ℤ))
    (hr : ∀ i j, P.valuation E ((((toGLm E m r : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1) i j) ≤ WithZero.exp (-(N : ℤ)))
    (he : WithZero.exp (-(e : ℤ)) ≤ P.valuation E (q : E)) (hN : a + b + e ≤ N) : QClose P q (h⁻¹ * r * h) := by
  intro i j
  set A := ((toGLm E m h⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) with hAdef
  set R := ((toGLm E m r : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) with hRdef
  set B := ((toGLm E m h : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) with hBdef
  have hmul : ((toGLm E m (h⁻¹ * r * h) : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) = A * R * B := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
  have hAB : A * B = 1 := by
    rw [hAdef, hBdef, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have key : A * R * B - 1 = A * (R - 1) * B := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAB]
  rw [hmul, key]
  have h1 := qth_conj_le P A (R - 1) B (b : ℤ) (a : ℤ) (N : ℤ) hb hr ha i j
  refine h1.trans (le_trans ?_ he)
  exact WithZero.exp_le_exp.mpr (by omega)

include hq0 in

/- English proof (translation)
Establish `hinv : ∀ x : Sp E (n + c), y⁻¹ (y x) = x` using `fun x => LinearEquiv.symm_apply_apply y x`. Establish `he : ∀ l : ℕ, (fun l : ℕ => if kj ≤ l ∧ l < n then (1 : ℤ) else 0) l = 0 ∨ (fun l : ℕ => if kj ≤ l ∧ l < n then (1 : ℤ) else 0) l = 1`. Introduce `l`. Simplify using `only`. Apply the tactic sequence `split_ifs <;> simp`.

Use `Subgroup.mem_inf.2 ⟨fun x => ⟨fun hx => ?_, fun hx => qth_close_std P q hq0 y hy hx⟩, fun x => ⟨fun hx => ?_, fun hx => qth_close_scl P q hq0 _ he y hy hx⟩⟩` and prove the remaining obligations. Use `qth_close_std P q hq0 y⁻¹ hy' hx` as an intermediate fact. Rewrite `this` using `[hinv]`. Then use the resulting hypothesis. Use `qth_close_scl P q hq0 _ he y⁻¹ hy' hx` as an intermediate fact. Rewrite `this` using `[hinv]`. Then use the resulting hypothesis.
-/
theorem qth_mem_JQ {n c : ℕ} (kj : ℕ) (y : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (hy : QClose P q y) (hy' : QClose P q y⁻¹) :
    y ∈ LocE.JQ P q kj n c := by
  have hinv : ∀ x : Sp E (n + c), y⁻¹ (y x) = x := fun x => LinearEquiv.symm_apply_apply y x
  have he : ∀ l : ℕ, (fun l : ℕ => if kj ≤ l ∧ l < n then (1 : ℤ) else 0) l = 0 ∨
      (fun l : ℕ => if kj ≤ l ∧ l < n then (1 : ℤ) else 0) l = 1 := by
    intro l
    simp only
    split_ifs <;> simp
  refine Subgroup.mem_inf.2 ⟨fun x => ⟨fun hx => ?_, fun hx => qth_close_std P q hq0 y hy hx⟩,
    fun x => ⟨fun hx => ?_, fun hx => qth_close_scl P q hq0 _ he y hy hx⟩⟩
  · have := qth_close_std P q hq0 y⁻¹ hy' hx
    rwa [hinv] at this
  · have := qth_close_scl P q hq0 _ he y⁻¹ hy' hx
    rwa [hinv] at this

include hq0 in

/- English proof (translation)
Use `set M := ((toGLm E m y : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) with hMdef`. Establish `hyij : P.valuation E ((M - 1) i j) ≤ P.valuation E (q : E)` using `hy i j`. Establish `hv0 : P.valuation E (q : E) ≠ 0` using `by simpa using hq0`. Establish `ha0 : P.valuation E ((1 : Matrix (Fin m) (Fin m) E) i j) ≤ 1`. Rewrite using `[Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hd : IntAt P ((M - 1) i j / (q : E))`. Rewrite using `[qth_intAt_iff, map_div₀, div_eq_mul_inv]`. Combine the equalities or inequalities in the displayed calculation. Establish `hsum : M i j = (1 : Matrix (Fin m) (Fin m) E) i j + (q : E) * ((M - 1) i j / (q : E))`.

Rewrite using `[mul_div_cancel₀ _ hq0, Matrix.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[qth_intAt_iff, show M i j = (1 : Matrix (Fin m) (Fin m) E) i j + (M - 1) i j by`. Rewrite using `[Matrix.sub_apply]`.

Use the proof step `ring]`. Conclude with `Valuation.map_add_le _ ha0 (hyij.trans (qth_vq_le P q))`. Rewrite using `[hsum]`. Conclude with `redP_add_natCast_mul hq hd`.
-/
theorem qth_red_entry (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) {m : ℕ} {y : Sp E m ≃ₗ[E] Sp E m} (hy : QClose P q y) (i j : Fin m) :
    IntAt P (((toGLm E m y : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) i j) ∧
      redP P (((toGLm E m y : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) i j) = redP P ((1 : Matrix (Fin m) (Fin m) E) i j) := by
  set M := ((toGLm E m y : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) with hMdef
  have hyij : P.valuation E ((M - 1) i j) ≤ P.valuation E (q : E) := hy i j
  have hv0 : P.valuation E (q : E) ≠ 0 := by simpa using hq0
  have ha0 : P.valuation E ((1 : Matrix (Fin m) (Fin m) E) i j) ≤ 1 := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  have hd : IntAt P ((M - 1) i j / (q : E)) := by
    rw [qth_intAt_iff, map_div₀, div_eq_mul_inv]
    calc P.valuation E ((M - 1) i j) * (P.valuation E (q : E))⁻¹
        ≤ P.valuation E (q : E) * (P.valuation E (q : E))⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hv0
  have hsum : M i j = (1 : Matrix (Fin m) (Fin m) E) i j + (q : E) * ((M - 1) i j / (q : E)) := by
    rw [mul_div_cancel₀ _ hq0, Matrix.sub_apply]
    ring
  refine ⟨?_, ?_⟩
  · rw [qth_intAt_iff, show M i j = (1 : Matrix (Fin m) (Fin m) E) i j + (M - 1) i j by
      rw [Matrix.sub_apply]; ring]
    exact Valuation.map_add_le _ ha0 (hyij.trans (qth_vq_le P q))
  · rw [hsum]
    exact redP_add_natCast_mul hq hd

end Conj

end Formalism.L2.Col
