import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.QzBasic
import Mathlib.NumberTheory.Padics.ProperSpace

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

/- English proof (translation)
Introduce `l _ f`. Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hl0 : (l : ℚ_[l]) ≠ 0` using `by exact_mod_cast (Fact.out : l.Prime).ne_zero`. Establish `hz : ∀ q : ℚ_[l], QZ.mk l q = 0 ↔ ‖q‖ ≤ 1`. Introduce `q`.

Use `show (Submodule.Quotient.mk q : ℚ_[l] ⧸ ZlSub l) = 0 ↔ _`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `y.2`.

Introduce `h`. Conclude with `⟨⟨q, h⟩, rfl⟩`. Use `set x : ℕ → QZ l := fun k => QZ.mk l (((l : ℚ_[l]) ^ k)⁻¹) with hx`. Establish `hA : ∀ (c : ℤ_[l]) (k : ℕ), c • x k = 0 ↔ ‖c‖ ≤ (l : ℝ) ^ (-(k : ℤ))`. Introduce `c k`.

Use `show QZ.mk l ((c : ℚ_[l]) * ((l : ℚ_[l]) ^ k)⁻¹) = 0 ↔ _`. Establish `hpos : (0 : ℝ) < (l : ℝ) ^ (-(k : ℤ))` using `by positivity`. Rewrite using `[hz, norm_mul, norm_inv, Padic.norm_p_pow, mul_inv_le_iff₀ hpos, one_mul]`. Conclude with `Iff.rfl`. Establish `hC : ∀ (k : ℕ) (y : QZ l), (l ^ k) • y = 0 → ∃ a : ℤ_[l], y = a • x k`.

Introduce `k y hy`. Take `⟨q, rfl⟩` from `Submodule.Quotient.mk_surjective (ZlSub l) y`. Establish `h1 : QZ.mk l ((l : ℚ_[l]) ^ k * q) = 0`. Rewrite using `[← hy]`. Use `show _ = (Submodule.Quotient.mk ((l ^ k) • q) : ℚ_[l] ⧸ ZlSub l)`.

Rewrite using `[nsmul_eq_mul]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite `h1` using `[hz]`. Use `⟨⟨(l : ℚ_[l]) ^ k * q, h1⟩, ?_⟩` and prove the remaining obligations.

Use `show QZ.mk l q = QZ.mk l (((l : ℚ_[l]) ^ k * q) * ((l : ℚ_[l]) ^ k)⁻¹)`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Establish `hstep : ∀ k, x k = (l : ℤ_[l]) • x (k + 1)`. Introduce `k`.

Use `show QZ.mk l (((l : ℚ_[l]) ^ k)⁻¹) = QZ.mk l ((l : ℚ_[l]) * ((l : ℚ_[l]) ^ (k + 1))⁻¹)`. Use `congr 1`. Rewrite using `[pow_succ]`. Clear the denominators using the available nonvanishing facts. Establish `hkill : ∀ k, (l ^ k) • x k = 0`.

Introduce `k`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℤ_[l], hA]`. Use `push_cast`. Rewrite using `[PadicInt.norm_p_pow]`. Establish `hex : ∀ k, ∃ a : ℤ_[l], f (x k) = a • x k`.

Introduce `k`. Apply `hC` to reduce the goal to its premises. Rewrite using `[← map_nsmul, hkill, map_zero]`. Use `choose a ha using hex`. Establish `hdiff : ∀ k, ‖a (k + 1) - a k‖ ≤ (l : ℝ) ^ (-(k : ℤ))`.

Introduce `k`. Rewrite using `[← hA, sub_smul, sub_eq_zero, ← ha k, hstep k, map_smul, ha (k + 1)]`. Conclude with `smul_comm _ _ _`. Establish `hr : (l : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hl`. Establish `hcs : CauchySeq a`.

Use `cauchySeq_of_le_geometric ((l : ℝ)⁻¹) 1 hr (fun n => ?_)` and prove the remaining obligations. Rewrite using `[dist_comm, dist_eq_norm, one_mul, inv_pow, ← zpow_natCast, ← zpow_neg]`. Conclude with `hdiff n`. Take `⟨c, hc⟩` from `cauchySeq_tendsto_of_complete hcs`. Establish `hmono : ∀ k m, k ≤ m → ‖a m - a k‖ ≤ (l : ℝ) ^ (-(k : ℤ))`.

Introduce `k m hkm`. Proceed by induction on `m, hkm using Nat.le_induction with`. Consider the case `base`. Rewrite using `[sub_self, norm_zero]`. Check the signs of the components of the expression.

Consider the case `succ m hkm ih`. Use `PadicInt.nonarchimedean (a (m + 1) - a m) (a m - a k)` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Use `this.trans (max_le ((hdiff m).trans ?_) ih)` and prove the remaining obligations. Conclude with `zpow_le_zpow_right₀ hl.le (by omega)`.

Establish `hck : ∀ k, ‖c - a k‖ ≤ (l : ℝ) ^ (-(k : ℤ))`. Introduce `k`. Establish `ht : Filter.Tendsto (fun m => ‖a m - a k‖) Filter.atTop (nhds ‖c - a k‖)` using `(hc.sub_const (a k)).norm`. Conclude with `le_of_tendsto ht (Filter.eventually_atTop.2 ⟨k, fun m hm => hmono k m hm⟩)`. Establish `hfx : ∀ k, f (x k) = c • x k`.

Introduce `k`. Use `(hA (c - a k) k).2 (hck k)` as an intermediate fact. Rewrite `this` using `[sub_smul, sub_eq_zero]`. Rewrite using `[this, ha k]`. Use `⟨c, fun y => ?_⟩` and prove the remaining obligations.

Take `⟨k, hk⟩` from `(qzBasic l).2.1 y`. Take `⟨b, rfl⟩` from `hC k y hk`. Rewrite using `[map_smul, hfx, smul_comm]`.
-/
theorem UpperTheory.V.Two.qzEnd :
    ∀ (l : ℕ) [Fact l.Prime] (f : QZ l →ₗ[ℤ_[l]] QZ l), ∃ c : ℤ_[l], ∀ x, f x = c • x := by
  intro l _ f
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hz : ∀ q : ℚ_[l], QZ.mk l q = 0 ↔ ‖q‖ ≤ 1 := by
    intro q
    show (Submodule.Quotient.mk q : ℚ_[l] ⧸ ZlSub l) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro h
      exact ⟨⟨q, h⟩, rfl⟩
  set x : ℕ → QZ l := fun k => QZ.mk l (((l : ℚ_[l]) ^ k)⁻¹) with hx
  have hA : ∀ (c : ℤ_[l]) (k : ℕ), c • x k = 0 ↔ ‖c‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
    intro c k
    show QZ.mk l ((c : ℚ_[l]) * ((l : ℚ_[l]) ^ k)⁻¹) = 0 ↔ _
    have hpos : (0 : ℝ) < (l : ℝ) ^ (-(k : ℤ)) := by positivity
    rw [hz, norm_mul, norm_inv, Padic.norm_p_pow, mul_inv_le_iff₀ hpos, one_mul]
    exact Iff.rfl
  have hC : ∀ (k : ℕ) (y : QZ l), (l ^ k) • y = 0 → ∃ a : ℤ_[l], y = a • x k := by
    intro k y hy
    obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) y
    have h1 : QZ.mk l ((l : ℚ_[l]) ^ k * q) = 0 := by
      rw [← hy]
      show _ = (Submodule.Quotient.mk ((l ^ k) • q) : ℚ_[l] ⧸ ZlSub l)
      rw [nsmul_eq_mul]
      push_cast
      rfl
    rw [hz] at h1
    refine ⟨⟨(l : ℚ_[l]) ^ k * q, h1⟩, ?_⟩
    show QZ.mk l q = QZ.mk l (((l : ℚ_[l]) ^ k * q) * ((l : ℚ_[l]) ^ k)⁻¹)
    congr 1
    field_simp
  have hstep : ∀ k, x k = (l : ℤ_[l]) • x (k + 1) := by
    intro k
    show QZ.mk l (((l : ℚ_[l]) ^ k)⁻¹) = QZ.mk l ((l : ℚ_[l]) * ((l : ℚ_[l]) ^ (k + 1))⁻¹)
    congr 1
    rw [pow_succ]
    field_simp
  have hkill : ∀ k, (l ^ k) • x k = 0 := by
    intro k
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l], hA]
    push_cast
    rw [PadicInt.norm_p_pow]
  have hex : ∀ k, ∃ a : ℤ_[l], f (x k) = a • x k := by
    intro k
    apply hC
    rw [← map_nsmul, hkill, map_zero]
  choose a ha using hex
  have hdiff : ∀ k, ‖a (k + 1) - a k‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
    intro k
    rw [← hA, sub_smul, sub_eq_zero, ← ha k, hstep k, map_smul, ha (k + 1)]
    exact smul_comm _ _ _
  have hr : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  have hcs : CauchySeq a := by
    refine cauchySeq_of_le_geometric ((l : ℝ)⁻¹) 1 hr (fun n => ?_)
    rw [dist_comm, dist_eq_norm, one_mul, inv_pow, ← zpow_natCast, ← zpow_neg]
    exact hdiff n
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hcs
  have hmono : ∀ k m, k ≤ m → ‖a m - a k‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base =>
      rw [sub_self, norm_zero]
      positivity
    | succ m hkm ih =>
      have := PadicInt.nonarchimedean (a (m + 1) - a m) (a m - a k)
      rw [sub_add_sub_cancel] at this
      refine this.trans (max_le ((hdiff m).trans ?_) ih)
      exact zpow_le_zpow_right₀ hl.le (by omega)
  have hck : ∀ k, ‖c - a k‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
    intro k
    have ht : Filter.Tendsto (fun m => ‖a m - a k‖) Filter.atTop (nhds ‖c - a k‖) :=
      (hc.sub_const (a k)).norm
    exact le_of_tendsto ht (Filter.eventually_atTop.2 ⟨k, fun m hm => hmono k m hm⟩)
  have hfx : ∀ k, f (x k) = c • x k := by
    intro k
    have := (hA (c - a k) k).2 (hck k)
    rw [sub_smul, sub_eq_zero] at this
    rw [this, ha k]
  refine ⟨c, fun y => ?_⟩
  obtain ⟨k, hk⟩ := (qzBasic l).2.1 y
  obtain ⟨b, rfl⟩ := hC k y hk
  rw [map_smul, hfx, smul_comm]
