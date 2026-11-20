import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotentsPropertiesPrimeFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionHarishChandraInductionMulStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BernsteinZelevinskyDerivativeGLnEqTwistedSumStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicClassFunBlockDiagonalEqSumDerivativesStatement

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

noncomputable section

namespace GlobalTheory.GLm.GGSum

variable {g : ℕ} [Fact g.Prime]

def dirac (g n : ℕ) [Fact g.Prime] : Gn g n → ℂ := fun x => if x = 1 then 1 else 0

/- English proof (translation)
Proceed by induction on `b with`. Consider the case `zero => simp`. Consider the case `succ b ih`. Rewrite using `[← add_assoc a b 1, Nat.triangle_succ, Nat.triangle_succ, ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tri_add (a b : ℕ) : (a + b) * (a + b - 1) / 2 = a * (a - 1) / 2 + (a * b + b * (b - 1) / 2) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc a b 1, Nat.triangle_succ, Nat.triangle_succ, ih]; ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `: x = p⁻¹ * (p * x * p⁻¹) * p` using `by group`. Rewrite using `[this, h]`. Use `group`.

Introduce and unpack `rfl`. Use `group`.
-/
theorem conj_eq_one {G : Type} [Group G] (p x : G) : p * x * p⁻¹ = 1 ↔ x = 1 := by
  constructor
  · intro h
    have : x = p⁻¹ * (p * x * p⁻¹) * p := by group
    rw [this, h]; group
  · rintro rfl; group

/- English proof (translation)
Introduce `x y`. Simplify using `only [dirac, conj_eq_one]`.
-/
theorem dirac_class (n : ℕ) : IsClass (dirac g n) := by
  intro x y
  simp only [dirac, conj_eq_one]

/- English proof (translation)
Introduce `x z`. Unfold `gg`. Use `congr 1`. Use `(Fintype.sum_equiv (Equiv.mulLeft z) _ _ ?_).symm` and prove the remaining obligations. Introduce `y`.

Establish `: (z * y)⁻¹ * (z * x * z⁻¹) * (z * y) = y⁻¹ * x * y` using `by group`. Simplify using `only [Equiv.coe_mulLeft, this]`.
-/
theorem gg_class (ψ : AddChar (ZMod g) ℂ) (n : ℕ) : IsClass (gg ψ n) := by
  intro x z
  unfold gg
  congr 1
  refine (Fintype.sum_equiv (Equiv.mulLeft z) _ _ ?_).symm
  intro y
  have : (z * y)⁻¹ * (z * x * z⁻¹) * (z * y) = y⁻¹ * x * y := by group
  simp only [Equiv.coe_mulLeft, this]

/- English proof (translation)
Rewrite using `[← (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g n 0 0 ψ).2.1]`. Simplify using `[wh, tr, dirac]`.
-/
theorem wh_dirac (ψ : AddChar (ZMod g) ℂ) (n : ℕ) :
    wh ψ (dirac g n) = ((g : ℂ) ^ (n * (n - 1) / 2))⁻¹ := by
  rw [← (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g n 0 0 ψ).2.1]
  simp [wh, tr, dirac]

/- English proof (translation)
Simplify using `only [wh, tr, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun x _ => by ring`.
-/
theorem wh_mul_left (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun x => c * f x) = c * wh ψ f := by
  simp only [wh, tr, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/- English proof (translation)
Simplify using `only [wh, tr, Finset.mul_sum]`. Conclude with `Finset.sum_comm`.
-/
theorem wh_sum (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (s : Finset ℕ) (f : ℕ → Gn g n → ℂ) :
    wh ψ (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, wh ψ (f i) := by
  simp only [wh, tr, Finset.mul_sum]
  exact Finset.sum_comm

/- English proof (translation)
Unfold `hc`. Rewrite using `[GlobalTheory.T.whittakerDimension_harishChandraInduction_mul g ψ hψ a b n hn _ (fun y x z => by simp only [hα x z]) (fun x y z => by simp only [hβ y z])]`. Simplify using `only [wh_mul_left]`. Rewrite using `[mul_comm, ← wh_mul_left]`. Simplify using `only [mul_comm]`.
-/
theorem wh_hc (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (a b n : ℕ) (hn : n = a + b) (α : Gn g a → ℂ)
    (β : Gn g b → ℂ) (hα : IsClass α) (hβ : IsClass β) : wh ψ (hc a b α β n) = wh ψ α * wh ψ β := by
  unfold hc
  rw [GlobalTheory.T.whittakerDimension_harishChandraInduction_mul g ψ hψ a b n hn _ (fun y x z => by simp only [hα x z]) (fun x y z => by simp only [hβ y z])]
  simp only [wh_mul_left]
  rw [mul_comm, ← wh_mul_left]
  simp only [mul_comm]

/- English proof (translation)
Simplify using `[entN, ha, hb, Matrix.one_apply]`.
-/
theorem entN_one (n a b : ℕ) (ha : a < n) (hb : b < n) : entN (1 : Mt g n) a b = if a = b then 1 else 0 := by
  simp [entN, ha, hb, Matrix.one_apply]

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[tl, entN_one n a b (by omega) (by omega), Matrix.one_apply]`. Simplify using `[Fin.ext_iff]`.
-/
theorem tl_one (i n : ℕ) (hi : i ≤ n) : tl i (1 : Mt g n) = 1 := by
  ext a b
  rw [tl, entN_one n a b (by omega) (by omega), Matrix.one_apply]
  simp [Fin.ext_iff]

/- English proof (translation)
Use `⟨fun a b h1 h2 => Matrix.one_apply_ne (fun h => by subst h; omega), fun a b => ?_⟩` and prove the remaining obligations. Establish `ha` using `a.2`. Establish `hb` using `b.2`. Rewrite using `[br, entN_one n _ _ (by omega) (by omega)]`. Use `⟨fun h => if_neg ?_, fun h => if_pos (by rw [h])⟩` and prove the remaining obligations.

Establish `: (b : ℕ) < a` using `h`. Use linear arithmetic over natural numbers and integers.
-/
theorem inR_one (i n : ℕ) (hi : i ≤ n) : InR i (1 : Mt g n) := by
  refine ⟨fun a b h1 h2 => Matrix.one_apply_ne (fun h => by subst h; omega), fun a b => ?_⟩
  have ha := a.2
  have hb := b.2
  rw [br, entN_one n _ _ (by omega) (by omega)]
  refine ⟨fun h => if_neg ?_, fun h => if_pos (by rw [h])⟩
  have : (b : ℕ) < a := h
  omega

/- English proof (translation)
Use `Finset.sum_eq_zero fun j hj => ?_` and prove the remaining obligations. Rewrite `hj` using `[Finset.mem_Ico]`. Rewrite using `[entN_one n _ _ (by omega) (by omega), if_neg (by omega)]`.
-/
theorem supFrom_one (i n : ℕ) : supFrom i (1 : Mt g n) = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mem_Ico] at hj
  rw [entN_one n _ _ (by omega) (by omega), if_neg (by omega)]

/- English proof (translation)
Use function extensionality and compare the values at `h`. Rewrite using `[GlobalTheory.T.bernsteinZelevinskyDerivativeGLn_eq_twisted_sum g ψ i n _ h hi]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single (1 : Gn g n)]`. Establish `e : ((1 : Mt g i) = (h : Mt g i)) ↔ h = 1` using `⟨fun e => Units.ext e.symm, fun e => by rw [e]; rfl⟩`.

Simplify using `only [Units.val_one, inR_one i n hi, tl_one i n hi, supFrom_one, dirac, true_and, e]`. Simplify using the standard rewrite rules. Introduce `x _ hx`. Simplify using `[dirac, hx]`. Simplify using the standard rewrite rules.
-/
theorem der_dirac (ψ : AddChar (ZMod g) ℂ) (i n : ℕ) (hi : i ≤ n) :
    der ψ i (dirac g n) =
      fun h => ((g : ℂ) ^ (i * (n - i) + (n - i) * (n - i - 1) / 2))⁻¹ * dirac g i h := by
  funext h
  rw [GlobalTheory.T.bernsteinZelevinskyDerivativeGLn_eq_twisted_sum g ψ i n _ h hi]
  congr 1
  rw [Finset.sum_eq_single (1 : Gn g n)]
  · have e : ((1 : Mt g i) = (h : Mt g i)) ↔ h = 1 :=
      ⟨fun e => Units.ext e.symm, fun e => by rw [e]; rfl⟩
    simp only [Units.val_one, inR_one i n hi, tl_one i n hi, supFrom_one, dirac, true_and, e]
    simp
  · intro x _ hx
    simp [dirac, hx]
  · simp

def dM {k : ℕ} (h : Mt g k) : Mt g (k + 1) :=
  fun i j => if (i : ℕ) < k ∧ (j : ℕ) < k then entN h i j else (1 : Mt g (k + 1)) i j

/- English proof (translation)
Simplify using `[dM, entN]`.
-/
theorem dM_cc {k : ℕ} (h : Mt g k) (i j : Fin k) : dM h i.castSucc j.castSucc = h i j := by
  simp [dM, entN]

/- English proof (translation)
Simplify using `[dM, Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne']`.
-/
theorem dM_lc {k : ℕ} (h : Mt g k) (j : Fin k) : dM h (Fin.last k) j.castSucc = 0 := by
  simp [dM, Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne']

/- English proof (translation)
Simplify using `[dM, Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne]`.
-/
theorem dM_cl {k : ℕ} (h : Mt g k) (j : Fin k) : dM h j.castSucc (Fin.last k) = 0 := by
  simp [dM, Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne]

/- English proof (translation)
Simplify using `[dM]`.
-/
theorem dM_ll {k : ℕ} (h : Mt g k) : dM h (Fin.last k) (Fin.last k) = 1 := by
  simp [dM]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_castSucc, dM_cc, dM_lc, dM_cl, dM_ll]`.
-/
theorem dM_mul {k : ℕ} (h h' : Mt g k) : dM h * dM h' = dM (h * h') := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, dM_cc, dM_lc, dM_cl, dM_ll]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>`. Simplify using `[dM_cc, dM_lc, dM_cl, dM_ll, Matrix.one_apply, (Fin.castSucc_lt_last _).ne, (Fin.castSucc_lt_last _).ne']`.
-/
theorem dM_one (k : ℕ) : dM (1 : Mt g k) = 1 := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [dM_cc, dM_lc, dM_cl, dM_ll, Matrix.one_apply, (Fin.castSucc_lt_last _).ne, (Fin.castSucc_lt_last _).ne']

/- English proof (translation)
Establish `hu : IsUnit (dM (h : Mt g k))` using `⟨⟨dM (h : Mt g k), dM ((h⁻¹ : Gn g k) : Mt g k), by rw [dM_mul, Units.mul_inv, dM_one], by rw [dM_mul, Units.inv_mul, dM_one]⟩, rfl⟩`. Establish `hc : ((diag1 h (k + 1) : Gn g (k + 1)) : Mt g (k + 1)) = dM (h : Mt g k)`. Express the relevant statement in the definitionally equal form `((toG (dM (h : Mt g k)) : Gn g (k + 1)) : Mt g (k + 1)) = _`. Rewrite using `[toG, dif_pos hu]`. Both sides reduce to the same expression.

Prove the components needed by the constructor for the conclusion. Introduce `e`. Rewrite `hc` using `[e]`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`.

Rewrite using `[← dM_cc (h : Mt g k) i j, ← hc]`. Simplify using `[Matrix.one_apply]`. Introduce `e`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hc, e]`.

Conclude with `dM_one k`.
-/
theorem blockDiagonalWithIdentityGL_eq_one_iff {k : ℕ} (h : Gn g k) : diag1 h (k + 1) = 1 ↔ h = 1 := by
  have hu : IsUnit (dM (h : Mt g k)) :=
    ⟨⟨dM (h : Mt g k), dM ((h⁻¹ : Gn g k) : Mt g k), by rw [dM_mul, Units.mul_inv, dM_one],
      by rw [dM_mul, Units.inv_mul, dM_one]⟩, rfl⟩
  have hc : ((diag1 h (k + 1) : Gn g (k + 1)) : Mt g (k + 1)) = dM (h : Mt g k) := by
    change ((toG (dM (h : Mt g k)) : Gn g (k + 1)) : Mt g (k + 1)) = _
    rw [toG, dif_pos hu]; rfl
  constructor
  · intro e
    rw [e] at hc
    apply Units.ext
    ext i j
    rw [← dM_cc (h : Mt g k) i j, ← hc]
    simp [Matrix.one_apply]
  · intro e
    apply Units.ext
    rw [hc, e]
    exact dM_one k

/- English proof (translation)
Introduce `g hg ψ hψ k`. Establish `hg0 : (g : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hg.out.ne_zero`. Establish `h1 : dirac g k = fun h => ∑ i ∈ Finset.range (k + 1), hc i (k - i) (der ψ i (dirac g (k + 1))) (gg ψ (k - i)) k h`. Use function extensionality and compare the values at `h`. Rewrite using `[← GlobalTheory.T.mirabolicClassFun_blockDiagonal_eq_sum_derivatives g ψ hψ k _ (fun p x _ _ => dirac_class _ x p) h]`.

Simplify using `only [dirac, blockDiagonalWithIdentityGL_eq_one_iff]`. Establish `h2` using `wh_dirac ψ k`. Rewrite `h2` using `[h1, wh_sum]`. Establish `h3 : ∀ i ∈ Finset.range (k + 1), wh ψ (hc i (k - i) (der ψ i (dirac g (k + 1))) (gg ψ (k - i)) k) = ((g : ℂ) ^ (k * (k - 1) / 2 + k))⁻¹ * wh ψ (gg ψ (k + 1 - 1 - i))`. Introduce `i hi`.

Rewrite `hi` using `[Finset.mem_range]`. Rewrite using `[der_dirac ψ i (k + 1) hi.le, wh_hc ψ hψ i (k - i) k (by omega) _ _ (fun x y => by simp only [dirac_class i x y]) (gg_class ψ _), wh_mul_left, wh_dirac, ← mul_inv, ← pow_add, add_comm _ (i * (i - 1) / 2), ← tri_add, Nat.add_sub_cancel' hi.le, Nat.triangle_succ]`. Both sides reduce to the same expression. Rewrite `h2` using `[Finset.sum_congr rfl h3, ← Finset.mul_sum, Finset.sum_range_reflect (fun j => wh ψ (gg ψ j)), pow_add]`. Clear denominators, using `at h2` for the nonvanishing conditions.

Conclude with `h2`.
-/
theorem sum_wh_gg : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ k : ℕ,
    ∑ j ∈ Finset.range (k + 1), wh ψ (gg ψ j) = (g : ℂ) ^ k := by
  intro g hg ψ hψ k
  have hg0 : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hg.out.ne_zero
  have h1 : dirac g k = fun h => ∑ i ∈ Finset.range (k + 1),
      hc i (k - i) (der ψ i (dirac g (k + 1))) (gg ψ (k - i)) k h := by
    funext h
    rw [← GlobalTheory.T.mirabolicClassFun_blockDiagonal_eq_sum_derivatives g ψ hψ k _ (fun p x _ _ => dirac_class _ x p) h]
    simp only [dirac, blockDiagonalWithIdentityGL_eq_one_iff]
  have h2 := wh_dirac ψ k
  rw [h1, wh_sum] at h2
  have h3 : ∀ i ∈ Finset.range (k + 1),
      wh ψ (hc i (k - i) (der ψ i (dirac g (k + 1))) (gg ψ (k - i)) k) =
        ((g : ℂ) ^ (k * (k - 1) / 2 + k))⁻¹ * wh ψ (gg ψ (k + 1 - 1 - i)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [der_dirac ψ i (k + 1) hi.le, wh_hc ψ hψ i (k - i) k (by omega) _ _
      (fun x y => by simp only [dirac_class i x y]) (gg_class ψ _), wh_mul_left, wh_dirac, ← mul_inv, ← pow_add,
      add_comm _ (i * (i - 1) / 2), ← tri_add, Nat.add_sub_cancel' hi.le, Nat.triangle_succ]
    rfl
  rw [Finset.sum_congr rfl h3, ← Finset.mul_sum, Finset.sum_range_reflect (fun j => wh ψ (gg ψ j)), pow_add] at h2
  field_simp at h2
  exact h2

end GlobalTheory.GLm.GGSum
