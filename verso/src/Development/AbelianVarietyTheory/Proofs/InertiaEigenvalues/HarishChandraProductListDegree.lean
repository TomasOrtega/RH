import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicUnitriangularSubgroupsGLnPrimeFiel

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.HcDeg

variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero => simp`. Consider the case `succ d ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]`.
-/
theorem prod_Icc_eq_range (f : ℕ → ℂ) (d : ℕ) : ∏ i ∈ Finset.Icc 1 d, f i = ∏ i ∈ Finset.range d, f (i + 1) := by
  induction d with
  | zero => simp
  | succ d ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

/- English proof (translation)
Rewrite using `[← Nat.card_eq_fintype_card, Matrix.card_GL_field, ZMod.card, Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun i => (((g ^ d - g ^ i : ℕ)) : ℂ)) d]`. Establish `h1 : ∀ i ∈ Finset.range d, (((g ^ d - g ^ i : ℕ)) : ℂ) = (g : ℂ) ^ i * ((g : ℂ) ^ (d - 1 - i + 1) - 1)`. Introduce `i hi`. Establish `hi'` using `Finset.mem_range.mp hi`. Establish `hle : g ^ i ≤ g ^ d` using `Nat.pow_le_pow_right (Fact.out : g.Prime).pos hi'.le`.

Rewrite using `[Nat.cast_sub hle, mul_sub, mul_one, ← pow_add]`. Use `push_cast`. Use `congr 2`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.prod_congr rfl h1, Finset.prod_mul_distrib, prod_Icc_eq_range, Finset.prod_range_reflect (fun i => (g : ℂ) ^ (i + 1) - 1) d]`.
-/
theorem card_GL_C (d : ℕ) : (Fintype.card (Gn g d) : ℂ) =
    (∏ i ∈ Finset.range d, (g : ℂ) ^ i) * ∏ i ∈ Finset.Icc 1 d, ((g : ℂ) ^ i - 1) := by
  rw [← Nat.card_eq_fintype_card, Matrix.card_GL_field, ZMod.card, Nat.cast_prod,
    Fin.prod_univ_eq_prod_range (fun i => (((g ^ d - g ^ i : ℕ)) : ℂ)) d]
  have h1 : ∀ i ∈ Finset.range d, (((g ^ d - g ^ i : ℕ)) : ℂ) = (g : ℂ) ^ i * ((g : ℂ) ^ (d - 1 - i + 1) - 1) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hle : g ^ i ≤ g ^ d := Nat.pow_le_pow_right (Fact.out : g.Prime).pos hi'.le
    rw [Nat.cast_sub hle, mul_sub, mul_one, ← pow_add]
    push_cast
    congr 2
    omega
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, prod_Icc_eq_range,
    Finset.prod_range_reflect (fun i => (g : ℂ) ^ (i + 1) - 1) d]

/- English proof (translation)
Rewrite using `[Finset.prod_range_add]`. Simplify using `only [pow_add, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_pow_add (a b : ℕ) : ∏ i ∈ Finset.range (a + b), (g : ℂ) ^ i =
    (∏ i ∈ Finset.range a, (g : ℂ) ^ i) * (∏ i ∈ Finset.range b, (g : ℂ) ^ i) * (g : ℂ) ^ (a * b) := by
  rw [Finset.prod_range_add]
  simp only [pow_add, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
  ring

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[toG, dif_pos isUnit_one, IsUnit.unit_spec]`. Both sides reduce to the same expression.
-/
theorem toG_one (n : ℕ) : toG (1 : Mt g n) = 1 := by
  apply Units.ext
  rw [toG, dif_pos isUnit_one, IsUnit.unit_spec]
  rfl

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[GlobalTheory.GLm.ParBasic.tl_apply]`. Simplify using `[Matrix.one_apply, Fin.castAdd_inj]`.
-/
theorem tl_one (a b : ℕ) : tl a (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [GlobalTheory.GLm.ParBasic.tl_apply]
  simp [Matrix.one_apply, Fin.castAdd_inj]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[GlobalTheory.GLm.ParBasic.br_apply]`. Simplify using `[Matrix.one_apply, Fin.natAdd_inj]`.
-/
theorem br_one (a b : ℕ) : br a b (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [GlobalTheory.GLm.ParBasic.br_apply]
  simp [Matrix.one_apply, Fin.natAdd_inj]

/- English proof (translation)
Establish `hP` using `GlobalTheory.GLm.ParBasic.card_par (g := g) (a := a) (b := b)`. Establish `hne : ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ) ≠ 0`. Rewrite using `[Nat.cast_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]`. Conclude with `⟨1, by simpa using GlobalTheory.GLm.ParBasic.inPar_one (g := g) a (a + b)⟩`. Establish `hs : hc a b α β (a + b) 1 = ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ)⁻¹ * (Fintype.card (Gn g (a + b)) * (α 1 * β 1))`.

Simplify using `only [hc, hcT, mul_one, inv_mul_cancel, Units.val_one, GlobalTheory.GLm.ParBasic.inPar_one, if_true, tl_one, br_one, toG_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Establish `hP' : ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ) = Fintype.card (Gn g a) * Fintype.card (Gn g b) * (g : ℂ) ^ (a * b)`. Rewrite using `[hP]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hs, ← hP']`. Clear the denominators using the available nonvanishing facts.
-/
theorem hc_one (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) :
    hc a b α β (a + b) 1 * (Fintype.card (Gn g a) * Fintype.card (Gn g b) * (g : ℂ) ^ (a * b)) =
      Fintype.card (Gn g (a + b)) * (α 1 * β 1) := by
  have hP := GlobalTheory.GLm.ParBasic.card_par (g := g) (a := a) (b := b)
  have hne : ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
    exact ⟨1, by simpa using GlobalTheory.GLm.ParBasic.inPar_one (g := g) a (a + b)⟩
  have hs : hc a b α β (a + b) 1 = ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ)⁻¹ *
      (Fintype.card (Gn g (a + b)) * (α 1 * β 1)) := by
    simp only [hc, hcT, mul_one, inv_mul_cancel, Units.val_one, GlobalTheory.GLm.ParBasic.inPar_one, if_true, tl_one, br_one,
      toG_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hP' : ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ) =
      Fintype.card (Gn g a) * Fintype.card (Gn g b) * (g : ℂ) ^ (a * b) := by
    rw [hP]; push_cast; ring
  rw [hs, ← hP']
  field_simp

/- English proof (translation)
Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `i hi`. Establish `hi1 : 1 ≤ i` using `(Finset.mem_Icc.mp hi).1`. Establish `hg : 1 < g` using `(Fact.out : g.Prime).one_lt`. Establish `: (1 : ℕ) < g ^ i` using `Nat.one_lt_pow (by omega) hg`.

Rewrite using `[sub_ne_zero]`. Conclude with `this.ne'` after adjusting the coercions.
-/
theorem prodIcc_ne (d : ℕ) : ∏ i ∈ Finset.Icc 1 d, ((g : ℂ) ^ i - 1) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  have : (1 : ℕ) < g ^ i := Nat.one_lt_pow (by omega) hg
  rw [sub_ne_zero]
  exact_mod_cast this.ne'

/- English proof (translation)
Introduce `g _ L`. Proceed by induction on `L with`. Consider the case `nil`. Introduce `n hn`. Substitute `hn` using the available equality.

Simplify using `[hcL_nil, degL]`. Consider the case `cons p L ih`. Introduce `n hn`. Establish `hn' : n = p.1 + degL L` using `by rw [hn]; simp [degL]`. Substitute `hn'` using the available equality.

Establish `h1` using `hc_one p.1 (degL L) p.2 (hcL L (degL L))`. Establish `h2` using `ih (degL L) rfl`. Rewrite `h1` using `[card_GL_C, card_GL_C, card_GL_C, prod_pow_add]`. Establish `hA` using `prodIcc_ne (g := g) p.1`. Establish `hB` using `prodIcc_ne (g := g) (degL L)`.

Establish `hG : ∀ d, ∏ i ∈ Finset.range d, (g : ℂ) ^ i ≠ 0` using `fun d => Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (by exact_mod_cast (Fact.out : g.Prime).ne_zero)`. Establish `hg0 : (g : ℂ) ^ (p.1 * degL L) ≠ 0` using `pow_ne_zero _ (by exact_mod_cast (Fact.out : g.Prime).ne_zero)`. Simplify using `only [List.map_cons, List.prod_cons, hcL_cons]`. Use `set A := ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)`. Use `set B := ∏ i ∈ Finset.Icc 1 (degL L), ((g : ℂ) ^ i - 1)`.

Use `set C := ∏ i ∈ Finset.Icc 1 (p.1 + degL L), ((g : ℂ) ^ i - 1)`. Use `set Ga := ∏ i ∈ Finset.range p.1, (g : ℂ) ^ i`. Use `set Gb := ∏ i ∈ Finset.range (degL L), (g : ℂ) ^ i`. Use `set X := hc p.1 (degL L) p.2 (hcL L (degL L)) (p.1 + degL L) 1`. Use `set Y := (L.map fun p => ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)).prod`.

Use `set Z := (L.map fun p => p.2 1).prod`. Establish `key : X * (A * B) = C * (p.2 1 * hcL L (degL L) 1)`. Apply `mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (hG p.1) (hG (degL L))) hg0)` to reduce the goal to its premises. Take the linear combination `h1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hc_degree : ∀ (g : ℕ) [Fact g.Prime] (L : List (Pc g)) (n : ℕ), n = degL L → hcL L n 1 * (L.map fun p => ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)).prod = (∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1)) * (L.map fun p => p.2 1).prod := by
  intro g _ L
  induction L with
  | nil =>
    intro n hn
    subst hn
    simp [hcL_nil, degL]
  | cons p L ih =>
    intro n hn
    have hn' : n = p.1 + degL L := by rw [hn]; simp [degL]
    subst hn'
    have h1 := hc_one p.1 (degL L) p.2 (hcL L (degL L))
    have h2 := ih (degL L) rfl
    rw [card_GL_C, card_GL_C, card_GL_C, prod_pow_add] at h1
    have hA := prodIcc_ne (g := g) p.1
    have hB := prodIcc_ne (g := g) (degL L)
    have hG : ∀ d, ∏ i ∈ Finset.range d, (g : ℂ) ^ i ≠ 0 := fun d =>
      Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (by exact_mod_cast (Fact.out : g.Prime).ne_zero)
    have hg0 : (g : ℂ) ^ (p.1 * degL L) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : g.Prime).ne_zero)
    simp only [List.map_cons, List.prod_cons, hcL_cons]
    set A := ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)
    set B := ∏ i ∈ Finset.Icc 1 (degL L), ((g : ℂ) ^ i - 1)
    set C := ∏ i ∈ Finset.Icc 1 (p.1 + degL L), ((g : ℂ) ^ i - 1)
    set Ga := ∏ i ∈ Finset.range p.1, (g : ℂ) ^ i
    set Gb := ∏ i ∈ Finset.range (degL L), (g : ℂ) ^ i
    set X := hc p.1 (degL L) p.2 (hcL L (degL L)) (p.1 + degL L) 1
    set Y := (L.map fun p => ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)).prod
    set Z := (L.map fun p => p.2 1).prod

    have key : X * (A * B) = C * (p.2 1 * hcL L (degL L) 1) := by
      apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (hG p.1) (hG (degL L))) hg0)
      linear_combination h1
    calc X * (A * Y) = X * (A * B) * Y / B := by field_simp
      _ = C * (p.2 1 * (hcL L (degL L) 1 * Y)) / B := by rw [key]; ring
      _ = C * (p.2 1 * Z) := by rw [h2]; field_simp

end GlobalTheory.GLq.HcDeg
