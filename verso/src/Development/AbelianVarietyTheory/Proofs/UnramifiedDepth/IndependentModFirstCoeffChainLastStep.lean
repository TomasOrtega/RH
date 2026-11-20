import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Formalism.LocalToGlobal.CharacterGerms.CharacteristicFromRanks
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowAdditiveAndRoots

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical GlobalTheory.FrobRoot

namespace GlobalTheory.LastStep

/- English proof (translation)
Unfold `VF.MM VF.Ge at *`. Rewrite using `[V.v.map_mul]`. Conclude with `add_pos_of_pos_of_nonneg ha (by simpa using hb)`.
-/
theorem mm_mul_int {C : Type} [Field C] {V : VF C} {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) :
    V.MM (a * b) := by
  unfold VF.MM VF.Ge at *
  rw [V.v.map_mul]
  exact add_pos_of_pos_of_nonneg ha (by simpa using hb)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using (mm_zero (V := V))`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `mm_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem mm_sum {C : Type} [Field C] {V : VF C} {ι : Type} (s : Finset ι) (f : ι → C)
    (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (mm_zero (V := V))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact mm_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Establish `h1 : S.U * S.U⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr S.U_det_ne)`. Establish `e : w c = ∑ k, (∑ b, w b * S.tan b k) * S.U⁻¹ k c`. Simplify using `only [Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Establish `: ∀ b, ∑ k, w b * S.tan b k * S.U⁻¹ k c = w b * (S.U * S.U⁻¹) b c`.

Introduce `b`. Rewrite using `[Matrix.mul_apply, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by simp only [Sys.U, Matrix.of_apply]; ring`. Simplify using `only [this, h1, Matrix.one_apply]`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Conclude with `mm_sum _ _ fun k _ => mm_mul_int (h k) (inv_int S.U S.U_int S.unimod k c)`.
-/
theorem mm_of_tan {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
    {G : Cart V d I J} (S : Sys G) (w : I → C) (h : ∀ k, V.MM (∑ c, w c * S.tan c k)) (c : I) :
    V.MM (w c) := by
  have h1 : S.U * S.U⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr S.U_det_ne)
  have e : w c = ∑ k, (∑ b, w b * S.tan b k) * S.U⁻¹ k c := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ b, ∑ k, w b * S.tan b k * S.U⁻¹ k c = w b * (S.U * S.U⁻¹) b c := by
      intro b
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp only [Sys.U, Matrix.of_apply]; ring
    simp only [this, h1, Matrix.one_apply]
    simp
  rw [e]
  exact mm_sum _ _ fun k _ => mm_mul_int (h k) (inv_int S.U S.U_int S.unimod k c)

/- English proof (translation)
Introduce `C _ V d _ I J _ _ X hA g a ha i S Z D hD s hs m y hy hind co hco hsum`. Use `haveI := X.algClosed`. Establish `hl : V.l ≠ 0` using `V.l_prime.ne_zero`. Use `choose r hr using fun δ => IsAlgClosed.exists_pow_nat_eq (co δ) (Nat.pos_of_ne_zero hl)`. Establish `hr0 : ∀ δ, V.Ge 0 (r δ)` using `fun δ => ge_of_pow hl (by rw [hr]; exact hco δ)`.

Use `set w : I g → C := fun c => ∑ δ, r δ * y δ c with hw`. Establish `hw0 : ∀ c, V.Ge 0 (w c)` using `fun c => VF.Ge.sum fun δ _ => (hr0 δ).mul_int (hy δ c)`. Use `set T := Finset.univ.filter (fun c => D.lev c = s) with hT`. Establish `hbig : X.big g (a + ((2 * s : ℕ) : ZMod d))` using `(S4.parity_of_alt (X.big g) (CharacteristicFromRanks.alt_step X.big X.big_compl hA g) a ha (2 * s)).2 (even_two_mul s)`. Establish `hgood : ∀ c ∈ T, (X.G g).Good (a + ((2 * s : ℕ) : ZMod d)) (S.tan c) (S.cur c)`.

Introduce `c hc`. Establish `h1 : D.lev c = s` using `(Finset.mem_filter.1 hc).2`. Establish `h2 : D.lev c < Formalism.BaseCaseIdentities.Kn i` using `h1 ▸ hs`. Establish `h3` using `hD.2.2.2.2 c h2`. Rewrite `h3` using `[h1]`.

Rewrite using `[← h3]`. Conclude with `hD.good (D.pure_good c (by rw [hD.2.2.1]; exact h2))`. Establish `hG` using `Cart.Good.comb T (co := w) (fun c _ => hw0 c) hgood`. Establish `hR` using `X.R2 hA g _ hbig _ _ hG (by`. Introduce `κ`.

Rewrite using `[Cart.c0'_comb]`. Establish `h1 : V.MM (∑ c ∈ T, (w c ^ V.l - ∑ δ, (r δ * y δ c) ^ V.l) * ((V.l : C) * S.be c 1 κ))`. Use `mm_sum _ _ fun c _ => mm_mul_int ?_ (l_mul_be_one_int S c κ)` and prove the remaining obligations. Use `mm_sum_pow 1 Finset.univ (fun δ => r δ * y δ c) (fun δ _ => (hr0 δ).mul_int (hy δ c))` as an intermediate fact. Simplify `this` using `only [pow_one]`.

Establish `h2` using `mm_add h1 (hsum κ)`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm (s := Finset.univ) (t := T), ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Simplify using `only [mul_pow, hr, sub_mul, Finset.sum_mul, mul_assoc, sub_add_cancel]`. Use the proof step `rfl)`. Establish `hwm : ∀ c, V.MM (if D.lev c = s then w c else 0)`. Use `mm_of_tan S _ fun k => ?_` and prove the remaining obligations. Use `hR k using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hT, Finset.sum_filter, ite_mul, zero_mul]`. Introduce `δ`. Rewrite using `[← hr δ]`. Use `mm_pow (hind r hr0 (fun c => ?_) δ) hl` and prove the remaining obligations. Use `hwm c using 1` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `by_cases hc : D.lev c = s <;> simp [hw, hc]`.
-/
theorem indepMod_first_coeff : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ (i : ℕ) (S : Sys (X.G g)) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z (I g)), Adapted S D a i → ∀ s : ℕ, s < Formalism.BaseCaseIdentities.Kn i → ∀ (m : ℕ) (y : Fin m → I g → C), (∀ δ c, V.Ge 0 (y δ c)) → IndepMod V (fun δ c => if D.lev c = s then y δ c else 0) → IndepMod V (fun δ (κ : J g) => ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s), y δ c ^ V.l * ((V.l : C) * S.be c 1 κ)) := by
  intro C _ V d _ I J _ _ X hA g a ha i S Z D hD s hs m y hy hind co hco hsum
  haveI := X.algClosed
  have hl : V.l ≠ 0 := V.l_prime.ne_zero
  choose r hr using fun δ => IsAlgClosed.exists_pow_nat_eq (co δ) (Nat.pos_of_ne_zero hl)
  have hr0 : ∀ δ, V.Ge 0 (r δ) := fun δ => ge_of_pow hl (by rw [hr]; exact hco δ)
  set w : I g → C := fun c => ∑ δ, r δ * y δ c with hw
  have hw0 : ∀ c, V.Ge 0 (w c) := fun c => VF.Ge.sum fun δ _ => (hr0 δ).mul_int (hy δ c)
  set T := Finset.univ.filter (fun c => D.lev c = s) with hT
  have hbig : X.big g (a + ((2 * s : ℕ) : ZMod d)) :=
    (S4.parity_of_alt (X.big g) (CharacteristicFromRanks.alt_step X.big X.big_compl hA g) a ha (2 * s)).2 (even_two_mul s)
  have hgood : ∀ c ∈ T, (X.G g).Good (a + ((2 * s : ℕ) : ZMod d)) (S.tan c) (S.cur c) := by
    intro c hc
    have h1 : D.lev c = s := (Finset.mem_filter.1 hc).2
    have h2 : D.lev c < Formalism.BaseCaseIdentities.Kn i := h1 ▸ hs
    have h3 := hD.2.2.2.2 c h2
    rw [h1] at h3
    rw [← h3]
    exact hD.good (D.pure_good c (by rw [hD.2.2.1]; exact h2))
  have hG := Cart.Good.comb T (co := w) (fun c _ => hw0 c) hgood
  have hR := X.R2 hA g _ hbig _ _ hG (by
    intro κ
    rw [Cart.c0'_comb]
    have h1 : V.MM (∑ c ∈ T, (w c ^ V.l - ∑ δ, (r δ * y δ c) ^ V.l) * ((V.l : C) * S.be c 1 κ)) := by
      refine mm_sum _ _ fun c _ => mm_mul_int ?_ (l_mul_be_one_int S c κ)
      have := mm_sum_pow 1 Finset.univ (fun δ => r δ * y δ c) (fun δ _ => (hr0 δ).mul_int (hy δ c))
      simpa only [pow_one] using this
    have h2 := mm_add h1 (hsum κ)
    convert h2 using 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ) (t := T), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [mul_pow, hr, sub_mul, Finset.sum_mul, mul_assoc, sub_add_cancel]
    rfl)
  have hwm : ∀ c, V.MM (if D.lev c = s then w c else 0) := by
    refine mm_of_tan S _ fun k => ?_
    convert hR k using 1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hT, Finset.sum_filter, ite_mul, zero_mul]
  intro δ
  rw [← hr δ]
  refine mm_pow (hind r hr0 (fun c => ?_) δ) hl
  convert hwm c using 1
  by_cases hc : D.lev c = s <;> simp [hw, hc]

end GlobalTheory.LastStep
