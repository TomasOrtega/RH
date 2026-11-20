import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscOntoOfShape

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.discriminantNormShapes

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

/- English proof (translation)
Take `⟨y, i, hi, hyi⟩` from `h𝔭.exists_inv hb`. Establish `hnil : IsNilpotent (Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι i))`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hi) k`.

Take `⟨u, hu⟩` from `hnil.isUnit_one_sub`. Use `⟨↑u⁻¹ * Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι y), ?_⟩` and prove the remaining obligations. Establish `h : Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι y) * Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι b) = 1 - Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι i)`. Rewrite using `[← map_mul, ← map_mul, eq_sub_iff_add_eq, ← map_add, ← map_add, hyi, map_one, map_one]`. Rewrite using `[mul_assoc, h, ← hu, Units.inv_mul]`.
-/
theorem exists_inv_unit {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {b : 𝓞 F} (hb : b ∉ 𝔭) (k : ℕ) :
    ∃ g : 𝓞 K ⧸ extP K 𝔭 ^ k, g * Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι b) = 1 := by
  obtain ⟨y, i, hi, hyi⟩ := h𝔭.exists_inv hb

  have hnil : IsNilpotent (Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι i)) := by
    refine ⟨k, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hi) k
  obtain ⟨u, hu⟩ := hnil.isUnit_one_sub
  refine ⟨↑u⁻¹ * Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι y), ?_⟩
  have h : Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι y) * Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι b) = 1 - Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι i) := by
    rw [← map_mul, ← map_mul, eq_sub_iff_add_eq, ← map_add, ← map_add, hyi, map_one, map_one]
  rw [mul_assoc, h, ← hu, Units.inv_mul]

open Classical in

def gQ (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [Fact (IsFixF K F)] {m : ℕ} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ)
    (a : Fin m → 𝓞 F) : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  Matrix.diagonal fun j => if h : a j ∈ 𝔭 then 0 else (exists_inv_unit (K := K) h𝔭 h k).choose

/- English proof (translation)
Unfold `gQ eQ diagQ`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one, Matrix.diagonal_sub]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : a j ∈ 𝔭`.

Simplify using `[h]`. Rewrite using `[dif_neg h, if_neg h, sub_zero]`. Conclude with `(exists_inv_unit (K := K) h𝔭 h k).choose_spec`.
-/
theorem gQ_mul_diagQ {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (a : Fin m → 𝓞 F) :
    gQ K h𝔭 k a * diagQ K 𝔭 k a = 1 - eQ K 𝔭 k a := by
  unfold gQ eQ diagQ
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one, Matrix.diagonal_sub]
  congr 1
  funext j
  by_cases h : a j ∈ 𝔭
  · simp [h]
  · rw [dif_neg h, if_neg h, sub_zero]
    exact (exists_inv_unit (K := K) h𝔭 h k).choose_spec

/- English proof (translation)
Rewrite using `[Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `mul_comm _ _`.
-/
theorem diag_comm {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (d d' : n → R) :
    diagonal d * diagonal d' = diagonal d' * diagonal d := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

/- English proof (translation)
Introduce `K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk Y`. Take `⟨⟨P, hPY⟩, ⟨W, hW⟩⟩` from `Y.2`. Establish `hF : IsFixF K F` using `Fact.out`. Use `set H := diagQ K 𝔭 k a with hHdef`. Use `set E := eQ K 𝔭 k a with hEdef`.

Use `set G := gQ K h𝔭 k a with hGdef`. Use `set Y0 := Y.1 with hY0`. Establish `hGH : G * H = 1 - E` using `gQ_mul_diagQ h𝔭 k a`. Establish `hHE : H * E = E * H` using `diag_comm _ _`. Establish `hHG : H * G = G * H` using `diag_comm _ _`.

Establish `hEE : E * E = E` using `eQ_mul_self 𝔭 k a`. Establish `hE : Eᴴ = E` using `eQ_conjTranspose 𝔭 k a`. Establish `hEE' : ∀ M : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k), E * (E * M) = E * M` using `fun M => by rw [← Matrix.mul_assoc, hEE]`. Establish `hHh : Hᴴ = H` using `diagQ_conjTranspose 𝔭 k a`. Establish `hE0E : (1 - E) * E = 0` using `by rw [Matrix.sub_mul, Matrix.one_mul, hEE, sub_self]`.

Establish `hEE0 : E * (1 - E) = 0` using `by rw [Matrix.mul_sub, Matrix.mul_one, hEE, sub_self]`. Establish `hE0E0 : (1 - E) * (1 - E) = 1 - E` using `by rw [Matrix.sub_mul, Matrix.one_mul, hEE0, sub_zero]`. Establish `hE0h : (1 - E)ᴴ = 1 - E` using `by rw [conjTranspose_sub, conjTranspose_one, hE]`. Establish `hHE0 : H * (1 - E) = (1 - E) * H`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hHE]`.

Use `set ZA := (1 - Y0) * G with hZA`. Establish `hY1 : Y0 + ZA * H = Y0 * E + (1 - E)`. Rewrite using `[hZA, Matrix.mul_assoc, hGH]`. Simplify using `only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]`. Normalize the expressions using the abelian group laws.

Establish `hP1` using `hom_shift hPY ZA`. Establish `hW1` using `form_shift hPY hW ZA`. Rewrite `hP1`, `hW1` using `[hY1]`. Rewrite `hP1`, `hW1` using `[← hHdef]`. Use `set P1 := P + H * ZA with hP1def`.

Use `set W1 := W + Pᴴ * ZA + ZAᴴ * P + ZAᴴ * H * ZA with hW1def`. Use `set Y1 := Y0 * E + (1 - E) with hY1def`. Use `clear_value ZA P1 W1 Y1`. Establish `hY1E0 : Y1 * (1 - E) = 1 - E`. Rewrite using `[hY1def, Matrix.add_mul, Matrix.mul_assoc, hEE0, Matrix.mul_zero, zero_add, hE0E0]`.

Establish `hE0Y1 : (1 - E) * Y1ᴴ = 1 - E`. Use `congrArg conjTranspose hY1E0` as an intermediate fact. Rewrite `this` using `[conjTranspose_mul, hE0h]`. Then use the resulting hypothesis. Establish `hoff : (1 - E) * Y1 * E = (1 - E) * W1 * E * H`. Establish `h1 : (1 - E) * (Y1ᴴ * H * Y1 - H) * E = (1 - E) * H * Y1 * E`.

Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hE0Y1, Matrix.mul_assoc (1 - E) H E, hHE, ← Matrix.mul_assoc, hE0E, Matrix.zero_mul, sub_zero]`. Rewrite `h1` using `[hW1]`. Establish `h2 : G * ((1 - E) * H) = 1 - E` using `by rw [← hHE0, ← Matrix.mul_assoc, hGH, hE0E0]`. Combine the equalities or inequalities in the displayed calculation. Use `set ZB := -((1 - E) * W1 * E) with hZB`.

Establish `hY2 : Y1 + ZB * H = E * Y0 * E + (1 - E)`. Rewrite using `[hZB, Matrix.neg_mul, ← hoff, hY1def]`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hEE, hE0E, Matrix.zero_mul]`. Normalize the expressions using the abelian group laws. Establish `hP2` using `hom_shift hP1 ZB`.

Establish `hW2` using `form_shift hP1 hW1 ZB`. Rewrite `hP2`, `hW2` using `[hY2]`. Rewrite `hP2`, `hW2` using `[← hHdef]`. Use `set P2 := P1 + H * ZB with hP2def`. Use `set W2 := W1 + P1ᴴ * ZB + ZBᴴ * P1 + ZBᴴ * H * ZB with hW2def`.

Use `set Y2 := E * Y0 * E + (1 - E) with hY2def`. Use `clear_value ZB P2 W2 Y2`. Establish `hY2E0 : (1 - E) * Y2 = 1 - E`. Rewrite using `[hY2def, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hE0E, Matrix.zero_mul, Matrix.zero_mul, zero_add, hE0E0]`. Establish `hY2E0' : Y2 * (1 - E) = 1 - E`.

Rewrite using `[hY2def, Matrix.add_mul, Matrix.mul_assoc, hEE0, Matrix.mul_zero, zero_add, hE0E0]`. Establish `hE0Y2 : Y2ᴴ * (1 - E) = 1 - E`. Use `congrArg conjTranspose hY2E0` as an intermediate fact. Rewrite `this` using `[conjTranspose_mul, hE0h]`. Then use the resulting hypothesis. Establish `hE0Y2' : (1 - E) * Y2ᴴ = 1 - E`.

Use `congrArg conjTranspose hY2E0'` as an intermediate fact. Rewrite `this` using `[conjTranspose_mul, hE0h]`. Then use the resulting hypothesis. Use `set X := Y2ᴴ * H * Y2 - H with hXdef`. Use `clear_value X`. Establish `hX0 : (1 - E) * X = 0`.

Rewrite using `[hXdef, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hE0Y2', ← hHE0, Matrix.mul_assoc, hY2E0, sub_self]`. Establish `hX1 : X * (1 - E) = 0`. Rewrite using `[hXdef, Matrix.sub_mul, Matrix.mul_assoc, hY2E0', Matrix.mul_assoc, hHE0, ← Matrix.mul_assoc, hE0Y2, sub_self]`. Establish `hEX : E * X = X`. Use `hX0` as an intermediate fact.

Rewrite `this` using `[Matrix.sub_mul, Matrix.one_mul, sub_eq_zero]`. Conclude with `this.symm`. Establish `hXE : X * E = X`. Use `hX1` as an intermediate fact. Rewrite `this` using `[Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]`.

Conclude with `this.symm`. Establish `hXh : Xᴴ = X`. Rewrite using `[hXdef, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hHh, Matrix.mul_assoc]`. Establish `hA : H * (E * W2 * E) * H = X`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨t, ht⟩` from `exists_trace_one hK hF h𝔭 k`. Use `set θ := Ideal.Quotient.mk (extP K 𝔭 ^ k) t with hθ`. Establish `hθ1 : θ + star θ = 1`. Rewrite using `[hθ, star_mk, ← map_add, ← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ k)), Ideal.Quotient.eq]`. Conclude with `ht`.

Use `set A := E * W2 * E with hAdef`. Use `clear_value A`. Use `set W' := θ • A + star θ • Aᴴ with hW'def`. Use `clear_value W'`. Establish `hAh : H * Aᴴ * H = X`.

Use `congrArg conjTranspose hA` as an intermediate fact. Rewrite `this` using `[conjTranspose_mul, conjTranspose_mul, hHh, hXh, ← Matrix.mul_assoc]`. Then use the resulting hypothesis. Establish `hW' : Y2ᴴ * H * Y2 - H = H * W' * H`. Rewrite using `[← hXdef, hW'def, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, hA, hAh, ← add_smul, hθ1, one_smul]`. Establish `hW'h : W'ᴴ = W'`.

Rewrite using `[hW'def, conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_conjTranspose, star_star, add_comm]`. Establish `hEAE : E * A * E = A`. Rewrite using `[hAdef]`. Simplify using `only [Matrix.mul_assoc, hEE, hEE']`. Establish `hEAhE : E * Aᴴ * E = Aᴴ`.

Use `congrArg conjTranspose hEAE` as an intermediate fact. Rewrite `this` using `[conjTranspose_mul, conjTranspose_mul, hE, ← Matrix.mul_assoc]`. Then use the resulting hypothesis. Establish `hW's : E * W' * E = W'`. Rewrite using `[hW'def, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, hEAE, hEAhE]`. Use `set P3 := (1 - E) + E * P2 * E with hP3def`.

Use `clear_value P3`. Establish `hEY2E : E * Y2 * E = E * Y0 * E`. Rewrite using `[hY2def, Matrix.mul_add, Matrix.add_mul, hEE0, Matrix.zero_mul, add_zero]`. Simplify using `only [Matrix.mul_assoc, hEE, hEE']`. Establish `hP3H : P3 * H = H * Y2`.

Establish `e1 : E * P2 * E * H = H * (E * Y0 * E)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hP3def, Matrix.add_mul, e1, ← hHE0, hY2def, Matrix.mul_add]`. Normalize the expressions using the abelian group laws. Establish `hEP3 : E * P3 = E * P3 * E`.

Rewrite using `[hP3def, Matrix.mul_add, Matrix.add_mul, hEE0, Matrix.zero_mul]`. Simplify using `only [Matrix.mul_assoc, hEE, hEE', zero_add]`. Establish `hP3E : P3 * E = E * P3 * E`. Rewrite using `[hP3def, Matrix.add_mul, hE0E, zero_add, Matrix.mul_add, Matrix.add_mul, hEE0, Matrix.zero_mul, zero_add]`. Simplify using `only [Matrix.mul_assoc, hEE, hEE']`.

Use `⟨Y2, P3, W', ZA + ZB, ?_, hP3H, hW', hW'h, hW's, hEP3, hP3E⟩` and prove the remaining obligations. Rewrite using `[Matrix.add_mul, ← hY2, ← hY1]`. Normalize the expressions using the abelian group laws.
-/
theorem norm_shape_holds : NormShape := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk Y
  obtain ⟨⟨P, hPY⟩, ⟨W, hW⟩⟩ := Y.2
  have hF : IsFixF K F := Fact.out
  set H := diagQ K 𝔭 k a with hHdef
  set E := eQ K 𝔭 k a with hEdef
  set G := gQ K h𝔭 k a with hGdef
  set Y0 := Y.1 with hY0
  have hGH : G * H = 1 - E := gQ_mul_diagQ h𝔭 k a
  have hHE : H * E = E * H := diag_comm _ _
  have hHG : H * G = G * H := diag_comm _ _
  have hEE : E * E = E := eQ_mul_self 𝔭 k a
  have hE : Eᴴ = E := eQ_conjTranspose 𝔭 k a
  have hEE' : ∀ M : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k), E * (E * M) = E * M :=
    fun M => by rw [← Matrix.mul_assoc, hEE]
  have hHh : Hᴴ = H := diagQ_conjTranspose 𝔭 k a
  have hE0E : (1 - E) * E = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hEE, sub_self]
  have hEE0 : E * (1 - E) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hEE, sub_self]
  have hE0E0 : (1 - E) * (1 - E) = 1 - E := by rw [Matrix.sub_mul, Matrix.one_mul, hEE0, sub_zero]
  have hE0h : (1 - E)ᴴ = 1 - E := by rw [conjTranspose_sub, conjTranspose_one, hE]
  have hHE0 : H * (1 - E) = (1 - E) * H := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hHE]

  set ZA := (1 - Y0) * G with hZA
  have hY1 : Y0 + ZA * H = Y0 * E + (1 - E) := by
    rw [hZA, Matrix.mul_assoc, hGH]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  have hP1 := hom_shift hPY ZA
  have hW1 := form_shift hPY hW ZA
  rw [hY1] at hP1 hW1
  rw [← hHdef] at hP1 hW1
  set P1 := P + H * ZA with hP1def
  set W1 := W + Pᴴ * ZA + ZAᴴ * P + ZAᴴ * H * ZA with hW1def
  set Y1 := Y0 * E + (1 - E) with hY1def
  clear_value ZA P1 W1 Y1
  have hY1E0 : Y1 * (1 - E) = 1 - E := by
    rw [hY1def, Matrix.add_mul, Matrix.mul_assoc, hEE0, Matrix.mul_zero, zero_add, hE0E0]
  have hE0Y1 : (1 - E) * Y1ᴴ = 1 - E := by
    have := congrArg conjTranspose hY1E0
    rwa [conjTranspose_mul, hE0h] at this

  have hoff : (1 - E) * Y1 * E = (1 - E) * W1 * E * H := by
    have h1 : (1 - E) * (Y1ᴴ * H * Y1 - H) * E = (1 - E) * H * Y1 * E := by
      rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hE0Y1,
        Matrix.mul_assoc (1 - E) H E, hHE, ← Matrix.mul_assoc, hE0E, Matrix.zero_mul, sub_zero]
    rw [hW1] at h1
    have h2 : G * ((1 - E) * H) = 1 - E := by rw [← hHE0, ← Matrix.mul_assoc, hGH, hE0E0]
    calc (1 - E) * Y1 * E = G * ((1 - E) * H) * Y1 * E := by rw [h2]
      _ = G * ((1 - E) * H * Y1 * E) := by simp only [Matrix.mul_assoc]
      _ = G * ((1 - E) * (H * W1 * H) * E) := by rw [← h1]
      _ = G * ((1 - E) * H) * W1 * (H * E) := by simp only [Matrix.mul_assoc]
      _ = (1 - E) * W1 * E * H := by rw [h2, hHE]; simp only [Matrix.mul_assoc]

  set ZB := -((1 - E) * W1 * E) with hZB
  have hY2 : Y1 + ZB * H = E * Y0 * E + (1 - E) := by
    rw [hZB, Matrix.neg_mul, ← hoff, hY1def]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc, hEE, hE0E, Matrix.zero_mul]
    abel
  have hP2 := hom_shift hP1 ZB
  have hW2 := form_shift hP1 hW1 ZB
  rw [hY2] at hP2 hW2
  rw [← hHdef] at hP2 hW2
  set P2 := P1 + H * ZB with hP2def
  set W2 := W1 + P1ᴴ * ZB + ZBᴴ * P1 + ZBᴴ * H * ZB with hW2def
  set Y2 := E * Y0 * E + (1 - E) with hY2def
  clear_value ZB P2 W2 Y2

  have hY2E0 : (1 - E) * Y2 = 1 - E := by
    rw [hY2def, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hE0E, Matrix.zero_mul,
      Matrix.zero_mul, zero_add, hE0E0]
  have hY2E0' : Y2 * (1 - E) = 1 - E := by
    rw [hY2def, Matrix.add_mul, Matrix.mul_assoc, hEE0, Matrix.mul_zero, zero_add, hE0E0]
  have hE0Y2 : Y2ᴴ * (1 - E) = 1 - E := by
    have := congrArg conjTranspose hY2E0
    rwa [conjTranspose_mul, hE0h] at this
  have hE0Y2' : (1 - E) * Y2ᴴ = 1 - E := by
    have := congrArg conjTranspose hY2E0'
    rwa [conjTranspose_mul, hE0h] at this
  set X := Y2ᴴ * H * Y2 - H with hXdef
  clear_value X
  have hX0 : (1 - E) * X = 0 := by
    rw [hXdef, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hE0Y2', ← hHE0,
      Matrix.mul_assoc, hY2E0, sub_self]
  have hX1 : X * (1 - E) = 0 := by
    rw [hXdef, Matrix.sub_mul, Matrix.mul_assoc, hY2E0', Matrix.mul_assoc, hHE0, ← Matrix.mul_assoc,
      hE0Y2, sub_self]
  have hEX : E * X = X := by
    have := hX0; rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this; exact this.symm
  have hXE : X * E = X := by
    have := hX1; rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this; exact this.symm
  have hXh : Xᴴ = X := by
    rw [hXdef, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      hHh, Matrix.mul_assoc]
  have hA : H * (E * W2 * E) * H = X := by
    calc H * (E * W2 * E) * H = (H * E) * W2 * (E * H) := by simp only [Matrix.mul_assoc]
      _ = (E * H) * W2 * (H * E) := by rw [hHE]
      _ = E * (H * W2 * H) * E := by simp only [Matrix.mul_assoc]
      _ = X := by rw [← hW2, hEX, hXE]
  obtain ⟨t, ht⟩ := exists_trace_one hK hF h𝔭 k
  set θ := Ideal.Quotient.mk (extP K 𝔭 ^ k) t with hθ
  have hθ1 : θ + star θ = 1 := by
    rw [hθ, star_mk, ← map_add, ← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ k)), Ideal.Quotient.eq]
    exact ht
  set A := E * W2 * E with hAdef
  clear_value A
  set W' := θ • A + star θ • Aᴴ with hW'def
  clear_value W'
  have hAh : H * Aᴴ * H = X := by
    have := congrArg conjTranspose hA
    rwa [conjTranspose_mul, conjTranspose_mul, hHh, hXh, ← Matrix.mul_assoc] at this
  have hW' : Y2ᴴ * H * Y2 - H = H * W' * H := by
    rw [← hXdef, hW'def, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul, hA, hAh, ← add_smul, hθ1, one_smul]
  have hW'h : W'ᴴ = W' := by
    rw [hW'def, conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_conjTranspose,
      star_star, add_comm]
  have hEAE : E * A * E = A := by
    rw [hAdef]; simp only [Matrix.mul_assoc, hEE, hEE']
  have hEAhE : E * Aᴴ * E = Aᴴ := by
    have := congrArg conjTranspose hEAE
    rwa [conjTranspose_mul, conjTranspose_mul, hE, ← Matrix.mul_assoc] at this
  have hW's : E * W' * E = W' := by
    rw [hW'def, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul, hEAE, hEAhE]
  set P3 := (1 - E) + E * P2 * E with hP3def
  clear_value P3
  have hEY2E : E * Y2 * E = E * Y0 * E := by
    rw [hY2def, Matrix.mul_add, Matrix.add_mul, hEE0, Matrix.zero_mul, add_zero]
    simp only [Matrix.mul_assoc, hEE, hEE']
  have hP3H : P3 * H = H * Y2 := by
    have e1 : E * P2 * E * H = H * (E * Y0 * E) := by
      calc E * P2 * E * H = E * P2 * (E * H) := by simp only [Matrix.mul_assoc]
        _ = E * P2 * (H * E) := by rw [hHE]
        _ = E * (P2 * H) * E := by simp only [Matrix.mul_assoc]
        _ = E * (H * Y2) * E := by rw [hP2]
        _ = (E * H) * Y2 * E := by simp only [Matrix.mul_assoc]
        _ = (H * E) * Y2 * E := by rw [hHE]
        _ = H * (E * Y2 * E) := by simp only [Matrix.mul_assoc]
        _ = H * (E * Y0 * E) := by rw [hEY2E]
    rw [hP3def, Matrix.add_mul, e1, ← hHE0, hY2def, Matrix.mul_add]
    abel
  have hEP3 : E * P3 = E * P3 * E := by
    rw [hP3def, Matrix.mul_add, Matrix.add_mul, hEE0, Matrix.zero_mul]
    simp only [Matrix.mul_assoc, hEE, hEE', zero_add]
  have hP3E : P3 * E = E * P3 * E := by
    rw [hP3def, Matrix.add_mul, hE0E, zero_add, Matrix.mul_add, Matrix.add_mul, hEE0, Matrix.zero_mul,
      zero_add]
    simp only [Matrix.mul_assoc, hEE, hEE']
  refine ⟨Y2, P3, W', ZA + ZB, ?_, hP3H, hW', hW'h, hW's, hEP3, hP3E⟩
  rw [Matrix.add_mul, ← hY2, ← hY1]
  abel

/- English proof (translation)
The claim follows from `discOnto_of_shape hU norm_shape_holds`.
-/
theorem discOnto_of_uDModel (hU : UDModel) : DiscOnto :=
  discOnto_of_shape hU norm_shape_holds

end Formalism.L2.SG.Pf.discriminantNormShapes
