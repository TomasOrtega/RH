import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticFunctions
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticRational
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticDegree

open Complex Filter Topology Set
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable (L : PeriodPair)

def weierstrassCurve : WeierstrassCurve ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -(L.g₂ / 4)
  a₆ := -(L.g₃ / 4)

instance : (weierstrassCurve L).IsShortNF := ⟨rfl, rfl, rfl⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma weierstrassCurve_a₁ : (weierstrassCurve L).a₁ = 0 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma weierstrassCurve_a₂ : (weierstrassCurve L).a₂ = 0 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma weierstrassCurve_a₃ : (weierstrassCurve L).a₃ = 0 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma weierstrassCurve_a₄ : (weierstrassCurve L).a₄ = -(L.g₂ / 4) := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma weierstrassCurve_a₆ : (weierstrassCurve L).a₆ = -(L.g₃ / 4) := rfl

def discr : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2

/- English proof (translation)
Rewrite using `[WeierstrassCurve.Δ_of_isShortNF, discr]`. Simplify using `only [weierstrassCurve_a₄, weierstrassCurve_a₆]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weierstrassCurve_Δ : (weierstrassCurve L).Δ = discr L := by
  rw [WeierstrassCurve.Δ_of_isShortNF, discr]
  simp only [weierstrassCurve_a₄, weierstrassCurve_a₆]
  ring

/- English proof (translation)
Rewrite using `[WeierstrassCurve.Affine.equation_iff]`. Simplify using `only [weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃, weierstrassCurve_a₄, weierstrassCurve_a₆]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take the linear combination `4 * h`.

Introduce `h`. Take the linear combination `h / 4`.
-/
theorem weierstrassCurve_equation_iff (x Y : ℂ) :
    (weierstrassCurve L).toAffine.Equation x Y ↔
      (2 * Y) ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃ := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃, weierstrassCurve_a₄,
    weierstrassCurve_a₆]
  constructor
  · intro h
    linear_combination 4 * h
  · intro h
    linear_combination h / 4

/- English proof (translation)
Rewrite using `[weierstrassCurve_equation_iff, mul_div_cancel₀ _ two_ne_zero]`. Conclude with `L.derivWeierstrassP_sq z hz`.
-/
theorem equation_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    (weierstrassCurve L).toAffine.Equation (℘[L] z) (℘'[L] z / 2) := by
  rw [weierstrassCurve_equation_iff, mul_div_cancel₀ _ two_ne_zero]
  exact L.derivWeierstrassP_sq z hz

variable {L}

/- English proof (translation)
Rewrite using `[finsum_eq_sum_of_support_subset u (s := hu.toFinset ∪ s) (fun x hx ↦ by simp [hx])]`. Conclude with `Finset.sum_le_sum_of_subset Finset.subset_union_right`.
-/
lemma sum_le_finsum_of_finite {α : Type*} {u : α → ℕ} (hu : (Function.support u).Finite)
    (s : Finset α) : ∑ x ∈ s, u x ≤ ∑ᶠ x, u x := by
  classical
  rw [finsum_eq_sum_of_support_subset u (s := hu.toFinset ∪ s) (fun x hx ↦ by simp [hx])]
  exact Finset.sum_le_sum_of_subset Finset.subset_union_right

/- English proof (translation)
Use `⟨fun z ↦ ?_, fun z l hl ↦ by simp only [isPeriodic_weierstrassP z l hl]⟩` and prove the remaining obligations. Use `L.meromorphic_weierstrassP z` as an intermediate fact. Use `fun_prop`.
-/
lemma isEllipticFunction_weierstrassP_sub (c : ℂ) :
    IsEllipticFunction L (fun z ↦ ℘[L] z - c) := by
  refine ⟨fun z ↦ ?_, fun z l hl ↦ by simp only [isPeriodic_weierstrassP z l hl]⟩
  have := L.meromorphic_weierstrassP z
  fun_prop

/- English proof (translation)
Introduce `htop`. Establish `h1` using `meromorphicOrderAt_eq_top_iff.1 htop`. Establish `h2` using `eventually_nhdsNE_of_eventually_codiscrete (eventually_codiscrete_eval_weierstrassP_ne_zero (L := L) (Polynomial.X_sub_C_ne_zero c)) z`. Take `⟨w, hw1, hw2⟩` from `(h1.and h2).exists`. Simplify using `only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hw2`.

Conclude with `hw2 hw1`.
-/
lemma meromorphicOrderAt_weierstrassP_sub_ne_top (c z : ℂ) :
    meromorphicOrderAt (fun w ↦ ℘[L] w - c) z ≠ ⊤ := by
  intro htop
  have h1 := meromorphicOrderAt_eq_top_iff.1 htop
  have h2 := eventually_nhdsNE_of_eventually_codiscrete
    (eventually_codiscrete_eval_weierstrassP_ne_zero (L := L) (Polynomial.X_sub_C_ne_zero c)) z
  obtain ⟨w, hw1, hw2⟩ := (h1.and h2).exists
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hw2
  exact hw2 hw1

/- English proof (translation)
Establish `ha : AnalyticAt ℂ (fun w ↦ ℘[L] w - c) z` using `(L.analyticOnNhd_weierstrassP z hz).sub analyticAt_const`. Establish `hne` using `meromorphicOrderAt_weierstrassP_sub_ne_top (L := L) c z`. Establish `hle` using `(natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha).2 h`. Rewrite using `[torusOrder_mk (isEllipticFunction_weierstrassP_sub c), ha.meromorphicOrderAt_eq]`. Rewrite `hne` using `[ha.meromorphicOrderAt_eq]`.

Take `⟨m, hm⟩ : ∃ m : ℕ, (m : ℕ∞) = analyticOrderAt (fun w ↦ ℘[L] w - c) z` from `ENat.ne_top_iff_exists.1 (fun h ↦ hne (by simp [h]))`. Rewrite `hle`, the goal using `[← hm]`. Simplify using `only [ENat.map_natCast, WithTop.untopD_coe, Int.toNat_natCast]`. Conclude with `hle` after adjusting the coercions.
-/
lemma le_toNat_torusOrder_weierstrassP_sub {z c : ℂ} (hz : z ∉ L.lattice) {n : ℕ}
    (h : ∀ i < n, iteratedDeriv i (fun w ↦ ℘[L] w - c) z = 0) :
    n ≤ (torusOrder L (fun w ↦ ℘[L] w - c) (Torus.mk L z)).toNat := by
  have ha : AnalyticAt ℂ (fun w ↦ ℘[L] w - c) z :=
    (L.analyticOnNhd_weierstrassP z hz).sub analyticAt_const
  have hne := meromorphicOrderAt_weierstrassP_sub_ne_top (L := L) c z
  have hle := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha).2 h
  rw [torusOrder_mk (isEllipticFunction_weierstrassP_sub c), ha.meromorphicOrderAt_eq]
  rw [ha.meromorphicOrderAt_eq] at hne
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℕ∞) = analyticOrderAt (fun w ↦ ℘[L] w - c) z :=
    ENat.ne_top_iff_exists.1 (fun h ↦ hne (by simp [h]))
  rw [← hm] at hle ⊢
  simp only [ENat.map_natCast, WithTop.untopD_coe, Int.toNat_natCast]
  exact_mod_cast hle

/- English proof (translation)
The claim follows from `le_toNat_torusOrder_weierstrassP_sub hz fun i hi ↦ by obtain rfl : i = 0 := by omega simp [hc]`.
-/
lemma one_le_toNat_torusOrder_weierstrassP_sub {z c : ℂ} (hz : z ∉ L.lattice) (hc : ℘[L] z = c) :
    1 ≤ (torusOrder L (fun w ↦ ℘[L] w - c) (Torus.mk L z)).toNat :=
  le_toNat_torusOrder_weierstrassP_sub hz fun i hi ↦ by
    obtain rfl : i = 0 := by omega
    simp [hc]

/- English proof (translation)
The claim follows from `le_toNat_torusOrder_weierstrassP_sub hz fun i hi ↦ by interval_cases i · simp [hc] · rw [iteratedDeriv_one, deriv_sub_const, L.deriv_weierstrassP] exact h'`.
-/
lemma two_le_toNat_torusOrder_weierstrassP_sub {z c : ℂ} (hz : z ∉ L.lattice) (hc : ℘[L] z = c)
    (h' : ℘'[L] z = 0) :
    2 ≤ (torusOrder L (fun w ↦ ℘[L] w - c) (Torus.mk L z)).toNat :=
  le_toNat_torusOrder_weierstrassP_sub hz fun i hi ↦ by
    interval_cases i
    · simp [hc]
    · rw [iteratedDeriv_one, deriv_sub_const, L.deriv_weierstrassP]
      exact h'

/- English proof (translation)
Rewrite using `[finsum_toNat_torusOrder_sub_const isEllipticFunction_weierstrassP c, degree_weierstrassP]`.
-/
lemma finsum_toNat_torusOrder_weierstrassP_sub (c : ℂ) :
    ∑ᶠ x : Torus L, (torusOrder L (fun w ↦ ℘[L] w - c) x).toNat = 2 := by
  rw [finsum_toNat_torusOrder_sub_const isEllipticFunction_weierstrassP c, degree_weierstrassP]

/- English proof (translation)
The claim follows from `(finite_support_torusOrder (isEllipticFunction_weierstrassP_sub c)).subset fun x hx ↦ by simp only [Function.mem_support] at hx ⊢ omega`.
-/
lemma finite_support_toNat_torusOrder_weierstrassP_sub (c : ℂ) :
    (Function.support fun x ↦ (torusOrder L (fun w ↦ ℘[L] w - c) x).toNat).Finite :=
  (finite_support_torusOrder (isEllipticFunction_weierstrassP_sub c)).subset fun x hx ↦ by
    simp only [Function.mem_support] at hx ⊢
    omega

/- English proof (translation)
The claim follows from `fun e ↦ h ((Torus.mk_eq_mk_iff L).1 e)`.
-/
lemma torus_mk_ne {z w : ℂ} (h : z - w ∉ L.lattice) : Torus.mk L z ≠ Torus.mk L w :=
  fun e ↦ h ((Torus.mk_eq_mk_iff L).1 e)

/- English proof (translation)
Establish `h1 : ℘'[L] (w - 2 * w) = ℘'[L] w` using `L.derivWeierstrassP_sub_coe w ⟨_, h⟩`. Rewrite `h1` using `[show w - 2 * w = -w by ring, L.derivWeierstrassP_neg]`. Take the linear combination `-h1 / 2`.
-/
theorem derivWeierstrassP_eq_zero_of_two_mul_mem {w : ℂ} (h : 2 * w ∈ L.lattice) :
    ℘'[L] w = 0 := by
  have h1 : ℘'[L] (w - 2 * w) = ℘'[L] w := L.derivWeierstrassP_sub_coe w ⟨_, h⟩
  rw [show w - 2 * w = -w by ring, L.derivWeierstrassP_neg] at h1
  linear_combination -h1 / 2

/- English proof (translation)
Use `⟨derivWeierstrassP_eq_zero_of_two_mul_mem, fun h' ↦ ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h2`. Establish `hw' : -w ∉ L.lattice` using `fun h ↦ hw (by simpa using neg_mem h)`. Establish `hne : Torus.mk L w ≠ Torus.mk L (-w)` using `torus_mk_ne (by rwa [sub_neg_eq_add, ← two_mul])`. Establish `hsum` using `sum_le_finsum_of_finite (finite_support_toNat_torusOrder_weierstrassP_sub (℘[L] w)) {Torus.mk L w, Torus.mk L (-w)}`.

Rewrite `hsum` using `[finsum_toNat_torusOrder_weierstrassP_sub, Finset.sum_pair hne]`. Establish `o1` using `two_le_toNat_torusOrder_weierstrassP_sub hw rfl h'`. Establish `o2` using `one_le_toNat_torusOrder_weierstrassP_sub hw' (L.weierstrassP_neg w)`. Use linear arithmetic over natural numbers and integers.
-/
theorem two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero {w : ℂ} (hw : w ∉ L.lattice) :
    2 * w ∈ L.lattice ↔ ℘'[L] w = 0 := by
  classical
  refine ⟨derivWeierstrassP_eq_zero_of_two_mul_mem, fun h' ↦ ?_⟩
  by_contra h2
  have hw' : -w ∉ L.lattice := fun h ↦ hw (by simpa using neg_mem h)
  have hne : Torus.mk L w ≠ Torus.mk L (-w) :=
    torus_mk_ne (by rwa [sub_neg_eq_add, ← two_mul])
  have hsum := sum_le_finsum_of_finite (finite_support_toNat_torusOrder_weierstrassP_sub (℘[L] w))
    {Torus.mk L w, Torus.mk L (-w)}
  rw [finsum_toNat_torusOrder_weierstrassP_sub, Finset.sum_pair hne] at hsum
  have o1 := two_le_toNat_torusOrder_weierstrassP_sub hw rfl h'
  have o2 := one_le_toNat_torusOrder_weierstrassP_sub hw' (L.weierstrassP_neg w)
  omega

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Rewrite `hcon` using `[not_or]`. Take `⟨h1, h2⟩` from `hcon`. Establish `hw' : -w ∉ L.lattice` using `fun h ↦ hw (by simpa using neg_mem h)`. Establish `hfin` using `finite_support_toNat_torusOrder_weierstrassP_sub (L := L) (℘[L] w)`.

Establish `htot` using `finsum_toNat_torusOrder_weierstrassP_sub (L := L) (℘[L] w)`. Establish `oz` using `one_le_toNat_torusOrder_weierstrassP_sub hz h`. Establish `hzw : Torus.mk L z ≠ Torus.mk L w` using `torus_mk_ne h1`. Distinguish the cases in `h2w : 2 * w ∈ L.lattice`. Establish `hsum` using `sum_le_finsum_of_finite hfin {Torus.mk L z, Torus.mk L w}`.

Rewrite `hsum` using `[htot, Finset.sum_pair hzw]`. Establish `ow` using `two_le_toNat_torusOrder_weierstrassP_sub hw rfl (derivWeierstrassP_eq_zero_of_two_mul_mem h2w)`. Use linear arithmetic over natural numbers and integers. Establish `hzw' : Torus.mk L z ≠ Torus.mk L (-w)` using `torus_mk_ne (by rwa [sub_neg_eq_add])`. Establish `hww' : Torus.mk L w ≠ Torus.mk L (-w)` using `torus_mk_ne (by rwa [sub_neg_eq_add, ← two_mul])`.

Establish `hsum` using `sum_le_finsum_of_finite hfin {Torus.mk L z, Torus.mk L w, Torus.mk L (-w)}`. Rewrite using `[htot, Finset.sum_insert (by`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton, not_or]`. Conclude with `⟨hzw, hzw'⟩), Finset.sum_pair hww'] at hsum`. Establish `ow` using `one_le_toNat_torusOrder_weierstrassP_sub hw rfl`.

Establish `ow'` using `one_le_toNat_torusOrder_weierstrassP_sub hw' (L.weierstrassP_neg w)`. Use linear arithmetic over natural numbers and integers.
-/
theorem sub_mem_or_add_mem_of_weierstrassP_eq {z w : ℂ} (hz : z ∉ L.lattice)
    (hw : w ∉ L.lattice) (h : ℘[L] z = ℘[L] w) :
    z - w ∈ L.lattice ∨ z + w ∈ L.lattice := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hw' : -w ∉ L.lattice := fun h ↦ hw (by simpa using neg_mem h)
  have hfin := finite_support_toNat_torusOrder_weierstrassP_sub (L := L) (℘[L] w)
  have htot := finsum_toNat_torusOrder_weierstrassP_sub (L := L) (℘[L] w)
  have oz := one_le_toNat_torusOrder_weierstrassP_sub hz h
  have hzw : Torus.mk L z ≠ Torus.mk L w := torus_mk_ne h1
  by_cases h2w : 2 * w ∈ L.lattice
  · have hsum := sum_le_finsum_of_finite hfin {Torus.mk L z, Torus.mk L w}
    rw [htot, Finset.sum_pair hzw] at hsum
    have ow := two_le_toNat_torusOrder_weierstrassP_sub hw rfl
      (derivWeierstrassP_eq_zero_of_two_mul_mem h2w)
    omega
  · have hzw' : Torus.mk L z ≠ Torus.mk L (-w) := torus_mk_ne (by rwa [sub_neg_eq_add])
    have hww' : Torus.mk L w ≠ Torus.mk L (-w) :=
      torus_mk_ne (by rwa [sub_neg_eq_add, ← two_mul])
    have hsum := sum_le_finsum_of_finite hfin {Torus.mk L z, Torus.mk L w, Torus.mk L (-w)}
    rw [htot, Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hzw, hzw'⟩), Finset.sum_pair hww'] at hsum
    have ow := one_le_toNat_torusOrder_weierstrassP_sub hw rfl
    have ow' := one_le_toNat_torusOrder_weierstrassP_sub hw' (L.weierstrassP_neg w)
    omega

/- English proof (translation)
Rewrite using `[hx]`. Conclude with `fun hm ↦ h (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice.1 hm)`.
-/
lemma notMem_lattice_of_eq {x : ℂ} (α β : ℚ) (hx : x = α * L.ω₁ + β * L.ω₂)
    (h : ¬(α.den = 1 ∧ β.den = 1)) : x ∉ L.lattice := by
  rw [hx]
  exact fun hm ↦ h (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice.1 hm)

/- English proof (translation)
Use `set e1 := ℘[L] (L.ω₁ / 2)`. Use `set e2 := ℘[L] (L.ω₂ / 2)`. Use `set e3 := ℘[L] ((L.ω₁ + L.ω₂) / 2)`. Establish `n1 : L.ω₁ / 2 ∉ L.lattice` using `L.ω₁_div_two_notMem_lattice`. Establish `n2 : L.ω₂ / 2 ∉ L.lattice` using `L.ω₂_div_two_notMem_lattice`.

Establish `n3 : (L.ω₁ + L.ω₂) / 2 ∉ L.lattice` using `notMem_lattice_of_eq (1 / 2) (1 / 2) (by push_cast; ring) (by norm_num)`. Establish `root : ∀ u, u ∉ L.lattice → 2 * u ∈ L.lattice → 4 * ℘[L] u ^ 3 - L.g₂ * ℘[L] u - L.g₃ = 0` using `fun u hu h2 ↦ by`. Rewrite using `[← L.derivWeierstrassP_sq u hu, derivWeierstrassP_eq_zero_of_two_mul_mem h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `f1` using `root _ n1 (by rw [mul_div_cancel₀ _ two_ne_zero]; exact L.ω₁_mem_lattice)`.

Establish `f2` using `root _ n2 (by rw [mul_div_cancel₀ _ two_ne_zero]; exact L.ω₂_mem_lattice)`. Establish `f3` using `root _ n3 (by`. Rewrite using `[mul_div_cancel₀ _ two_ne_zero]`. Conclude with `add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice)`. Establish `d12 : e1 ≠ e2` using `fun h ↦ by`.

Break down `sub_mem_or_add_mem_of_weierstrassP_eq n1 n2 h with h' | h'` into its components or cases. Conclude with `notMem_lattice_of_eq (1 / 2) (-1 / 2) (by push_cast; ring) (by norm_num) h'`. Conclude with `notMem_lattice_of_eq (1 / 2) (1 / 2) (by push_cast; ring) (by norm_num) h'`. Establish `d13 : e1 ≠ e3` using `fun h ↦ by`. Break down `sub_mem_or_add_mem_of_weierstrassP_eq n1 n3 h with h' | h'` into its components or cases.

Conclude with `notMem_lattice_of_eq 0 (-1 / 2) (by push_cast; ring) (by norm_num) h'`. Conclude with `notMem_lattice_of_eq 1 (1 / 2) (by push_cast; ring) (by norm_num) h'`. Establish `d23 : e2 ≠ e3` using `fun h ↦ by`. Break down `sub_mem_or_add_mem_of_weierstrassP_eq n2 n3 h with h' | h'` into its components or cases. Conclude with `notMem_lattice_of_eq (-1 / 2) 0 (by push_cast; ring) (by norm_num) h'`.

Conclude with `notMem_lattice_of_eq (1 / 2) 1 (by push_cast; ring) (by norm_num) h'`. Establish `s12 : 4 * (e1 ^ 2 + e1 * e2 + e2 ^ 2) = L.g₂` using `mul_left_cancel₀ (sub_ne_zero.2 d12) (by linear_combination f1 - f2)`. Establish `s13 : 4 * (e1 ^ 2 + e1 * e3 + e3 ^ 2) = L.g₂` using `mul_left_cancel₀ (sub_ne_zero.2 d13) (by linear_combination f1 - f3)`. Establish `hs : e1 + e2 + e3 = 0` using `mul_left_cancel₀ (sub_ne_zero.2 d23) (by linear_combination (s12 - s13) / 4)`. Conclude with `⟨d12, d13, d23, hs, s12, by linear_combination -f1⟩`.
-/
lemma halfPeriod_facts :
    ℘[L] (L.ω₁ / 2) ≠ ℘[L] (L.ω₂ / 2) ∧ ℘[L] (L.ω₁ / 2) ≠ ℘[L] ((L.ω₁ + L.ω₂) / 2) ∧
      ℘[L] (L.ω₂ / 2) ≠ ℘[L] ((L.ω₁ + L.ω₂) / 2) ∧
      ℘[L] (L.ω₁ / 2) + ℘[L] (L.ω₂ / 2) + ℘[L] ((L.ω₁ + L.ω₂) / 2) = 0 ∧
      4 * (℘[L] (L.ω₁ / 2) ^ 2 + ℘[L] (L.ω₁ / 2) * ℘[L] (L.ω₂ / 2) + ℘[L] (L.ω₂ / 2) ^ 2) =
        L.g₂ ∧
      L.g₃ = 4 * ℘[L] (L.ω₁ / 2) ^ 3 - L.g₂ * ℘[L] (L.ω₁ / 2) := by
  set e1 := ℘[L] (L.ω₁ / 2)
  set e2 := ℘[L] (L.ω₂ / 2)
  set e3 := ℘[L] ((L.ω₁ + L.ω₂) / 2)
  have n1 : L.ω₁ / 2 ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  have n2 : L.ω₂ / 2 ∉ L.lattice := L.ω₂_div_two_notMem_lattice
  have n3 : (L.ω₁ + L.ω₂) / 2 ∉ L.lattice :=
    notMem_lattice_of_eq (1 / 2) (1 / 2) (by push_cast; ring) (by norm_num)
  have root : ∀ u, u ∉ L.lattice → 2 * u ∈ L.lattice →
      4 * ℘[L] u ^ 3 - L.g₂ * ℘[L] u - L.g₃ = 0 := fun u hu h2 ↦ by
    rw [← L.derivWeierstrassP_sq u hu, derivWeierstrassP_eq_zero_of_two_mul_mem h2]
    ring
  have f1 := root _ n1 (by rw [mul_div_cancel₀ _ two_ne_zero]; exact L.ω₁_mem_lattice)
  have f2 := root _ n2 (by rw [mul_div_cancel₀ _ two_ne_zero]; exact L.ω₂_mem_lattice)
  have f3 := root _ n3 (by
    rw [mul_div_cancel₀ _ two_ne_zero]; exact add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice)
  have d12 : e1 ≠ e2 := fun h ↦ by
    rcases sub_mem_or_add_mem_of_weierstrassP_eq n1 n2 h with h' | h'
    · exact notMem_lattice_of_eq (1 / 2) (-1 / 2) (by push_cast; ring) (by norm_num) h'
    · exact notMem_lattice_of_eq (1 / 2) (1 / 2) (by push_cast; ring) (by norm_num) h'
  have d13 : e1 ≠ e3 := fun h ↦ by
    rcases sub_mem_or_add_mem_of_weierstrassP_eq n1 n3 h with h' | h'
    · exact notMem_lattice_of_eq 0 (-1 / 2) (by push_cast; ring) (by norm_num) h'
    · exact notMem_lattice_of_eq 1 (1 / 2) (by push_cast; ring) (by norm_num) h'
  have d23 : e2 ≠ e3 := fun h ↦ by
    rcases sub_mem_or_add_mem_of_weierstrassP_eq n2 n3 h with h' | h'
    · exact notMem_lattice_of_eq (-1 / 2) 0 (by push_cast; ring) (by norm_num) h'
    · exact notMem_lattice_of_eq (1 / 2) 1 (by push_cast; ring) (by norm_num) h'
  have s12 : 4 * (e1 ^ 2 + e1 * e2 + e2 ^ 2) = L.g₂ :=
    mul_left_cancel₀ (sub_ne_zero.2 d12) (by linear_combination f1 - f2)
  have s13 : 4 * (e1 ^ 2 + e1 * e3 + e3 ^ 2) = L.g₂ :=
    mul_left_cancel₀ (sub_ne_zero.2 d13) (by linear_combination f1 - f3)
  have hs : e1 + e2 + e3 = 0 :=
    mul_left_cancel₀ (sub_ne_zero.2 d23) (by linear_combination (s12 - s13) / 4)
  exact ⟨d12, d13, d23, hs, s12, by linear_combination -f1⟩

variable (L)

/- English proof (translation)
The claim follows from `let h := halfPeriod_facts (L := L) ⟨h.1, h.2.1, h.2.2.1⟩`.
-/
theorem weierstrassP_halfPeriods_ne :
    ℘[L] (L.ω₁ / 2) ≠ ℘[L] (L.ω₂ / 2) ∧ ℘[L] (L.ω₁ / 2) ≠ ℘[L] ((L.ω₁ + L.ω₂) / 2) ∧
      ℘[L] (L.ω₂ / 2) ≠ ℘[L] ((L.ω₁ + L.ω₂) / 2) :=
  let h := halfPeriod_facts (L := L)
  ⟨h.1, h.2.1, h.2.2.1⟩

/- English proof (translation)
Take `⟨-, -, -, hs, s12, hg3⟩` from `halfPeriod_facts (L := L)`. Rewrite using `[discr, hg3, ← s12, show ℘[L] ((L.ω₁ + L.ω₂) / 2) = -℘[L] (L.ω₁ / 2) - ℘[L] (L.ω₂ / 2) by`. Take the linear combination `hs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem discr_eq :
    discr L = 16 * ((℘[L] (L.ω₁ / 2) - ℘[L] (L.ω₂ / 2)) *
      (℘[L] (L.ω₁ / 2) - ℘[L] ((L.ω₁ + L.ω₂) / 2)) *
      (℘[L] (L.ω₂ / 2) - ℘[L] ((L.ω₁ + L.ω₂) / 2))) ^ 2 := by
  obtain ⟨-, -, -, hs, s12, hg3⟩ := halfPeriod_facts (L := L)
  rw [discr, hg3, ← s12, show ℘[L] ((L.ω₁ + L.ω₂) / 2) = -℘[L] (L.ω₁ / 2) - ℘[L] (L.ω₂ / 2) by
    linear_combination hs]
  ring

/- English proof (translation)
Take `⟨d12, d13, d23⟩` from `weierstrassP_halfPeriods_ne L`. Rewrite using `[discr_eq]`. Conclude with `mul_ne_zero (by norm_num) (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (sub_ne_zero.2 d12) (sub_ne_zero.2 d13)) (sub_ne_zero.2 d23)))`.
-/
theorem discr_ne_zero : discr L ≠ 0 := by
  obtain ⟨d12, d13, d23⟩ := weierstrassP_halfPeriods_ne L
  rw [discr_eq]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (sub_ne_zero.2 d12)
    (sub_ne_zero.2 d13)) (sub_ne_zero.2 d23)))

/- English proof (translation)
Rewrite using `[weierstrassCurve_Δ]`. Conclude with `discr_ne_zero L`.
-/
theorem weierstrassCurve_Δ_ne_zero : (weierstrassCurve L).Δ ≠ 0 := by
  rw [weierstrassCurve_Δ]
  exact discr_ne_zero L

instance : (weierstrassCurve L).IsElliptic :=
  ⟨isUnit_iff_ne_zero.2 (weierstrassCurve_Δ_ne_zero L)⟩

/- English proof (translation)
Rewrite using `[WeierstrassCurve.j_of_isShortNF, discr]`. Simplify using `only [weierstrassCurve_a₄, weierstrassCurve_a₆]`. Establish `h` using `discr_ne_zero L`. Rewrite `h` using `[discr]`. Establish `h1 : 4 * (-(L.g₂ / 4)) ^ 3 + 27 * (-(L.g₃ / 4)) ^ 2 ≠ 0`.

Introduce `h0`. Apply `h` to reduce the goal to its premises. Take the linear combination `-16 * h0`. Rewrite using `[div_eq_div_iff h1 h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weierstrassCurve_j : (weierstrassCurve L).j = 1728 * L.g₂ ^ 3 / discr L := by
  rw [WeierstrassCurve.j_of_isShortNF, discr]
  simp only [weierstrassCurve_a₄, weierstrassCurve_a₆]
  have h := discr_ne_zero L
  rw [discr] at h
  have h1 : 4 * (-(L.g₂ / 4)) ^ 3 + 27 * (-(L.g₃ / 4)) ^ 2 ≠ 0 := by
    intro h0
    apply h
    linear_combination -16 * h0
  rw [div_eq_div_iff h1 h]
  ring

end Elliptic
end GroundTheory.Global
