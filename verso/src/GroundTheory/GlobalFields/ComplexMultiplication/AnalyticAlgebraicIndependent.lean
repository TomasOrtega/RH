import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticAlgebraicPoints

open Filter Topology Set Polynomial
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.sum_insert ha]`. Conclude with `(hf a).add ih`.
-/
theorem meromorphicAt_fun_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {x : ℂ}
    (hf : ∀ i, MeromorphicAt (f i) x) : MeromorphicAt (fun z ↦ ∑ i ∈ s, f i z) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a).add ih

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty]`. Rewrite using `[germ_const, map_zero]`. Consider the case `insert a s ha ih`.

Simplify using `only [Finset.sum_insert ha]`. Establish `hs : Meromorphic fun z ↦ ∑ i ∈ s, f i z` using `fun x ↦ meromorphicAt_fun_sum s fun i ↦ hf i x`. Rewrite using `[← ih]`. Conclude with `germ_add (hf a) hs`.
-/
theorem germ_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i, Meromorphic (f i)) :
    germ (fun z ↦ ∑ i ∈ s, f i z) = ∑ i ∈ s, germ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [germ_const, map_zero]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hs : Meromorphic fun z ↦ ∑ i ∈ s, f i z := fun x ↦
      meromorphicAt_fun_sum s fun i ↦ hf i x
    rw [← ih]
    exact germ_add (hf a) hs

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty]`. Rewrite using `[meromorphicOrderAt_eq_top_iff.2 (Eventually.of_forall fun _ ↦ rfl)]`. Conclude with `WithTop.coe_lt_top c`.

Consider the case `insert a s ha ih`. Simplify using `only [Finset.sum_insert ha]`. Establish `hs : MeromorphicAt (fun z ↦ ∑ i ∈ s, f i z) x` using `meromorphicAt_fun_sum s hf`. Establish `h1` using `hc a (Finset.mem_insert_self a s)`. Establish `h2` using `ih fun i hi ↦ hc i (Finset.mem_insert_of_mem hi)`.

Conclude with `lt_of_lt_of_le (lt_min h1 h2) (meromorphicOrderAt_add (hf a) hs)`.
-/
theorem lt_meromorphicOrderAt_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {x : ℂ}
    (hf : ∀ i, MeromorphicAt (f i) x) {c : ℤ}
    (hc : ∀ i ∈ s, (c : WithTop ℤ) < meromorphicOrderAt (f i) x) :
    (c : WithTop ℤ) < meromorphicOrderAt (fun z ↦ ∑ i ∈ s, f i z) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [meromorphicOrderAt_eq_top_iff.2 (Eventually.of_forall fun _ ↦ rfl)]
    exact WithTop.coe_lt_top c
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hs : MeromorphicAt (fun z ↦ ∑ i ∈ s, f i z) x := meromorphicAt_fun_sum s hf
    have h1 := hc a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi ↦ hc i (Finset.mem_insert_of_mem hi)
    exact lt_of_lt_of_le (lt_min h1 h2) (meromorphicOrderAt_add (hf a) hs)

/- English proof (translation)
Take `⟨m, n, e⟩` from `PeriodPair.mem_lattice.1 h`. Use `LinearIndependent.pair_iff.mp L.indep ((m : ℝ) - r) (n : ℝ) (by` as an intermediate fact. Simplify using `only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_intCast]`. Take the linear combination `e)`. Conclude with `⟨m, (sub_eq_zero.1 this.1).symm⟩`.
-/
theorem exists_int_of_real_mul_mem (L : PeriodPair) {r : ℝ} (h : (r : ℂ) * L.ω₁ ∈ L.lattice) :
    ∃ a : ℤ, r = a := by
  obtain ⟨m, n, e⟩ := PeriodPair.mem_lattice.1 h
  have := LinearIndependent.pair_iff.mp L.indep ((m : ℝ) - r) (n : ℝ) (by
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_intCast]
    linear_combination e)
  exact ⟨m, (sub_eq_zero.1 this.1).symm⟩

/- English proof (translation)
Rewrite using `[ne_eq, Complex.ofReal_eq_zero]`. Conclude with `(Real.sqrt_pos.2 two_pos).ne'`.
-/
theorem sqrt_two_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  rw [ne_eq, Complex.ofReal_eq_zero]
  exact (Real.sqrt_pos.2 two_pos).ne'

/- English proof (translation)
Introduce `m m' hm`. Simplify using `only at hm`. Rewrite `hm` using `[Torus.mk_eq_mk_iff]`. Establish `e : (m : ℂ) * L.ω₁ / (Real.sqrt 2 : ℂ) - (m' : ℂ) * L.ω₁ / (Real.sqrt 2 : ℂ) = ((((m : ℝ) - m') / Real.sqrt 2 : ℝ) : ℂ) * L.ω₁`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hm` using `[e]`. Take `⟨a, ha⟩` from `exists_int_of_real_mul_mem L hm`. Assume the negation of the conclusion as `hne`. Establish `hd : ((m : ℝ) - m') ≠ 0` using `sub_ne_zero.2 (by exact_mod_cast hne)`.

Establish `ha0 : (a : ℝ) ≠ 0`. Introduce `h0`. Rewrite `ha` using `[h0]`. Conclude with `hd ((div_eq_zero_iff.1 ha).resolve_right (Real.sqrt_pos.2 two_pos).ne')`. Establish `hs2 : Real.sqrt 2 ≠ 0` using `(Real.sqrt_pos.2 two_pos).ne'`.

Establish `hs : Real.sqrt 2 = ((m : ℝ) - m') / a`. Rewrite using `[eq_div_iff ha0]`. Rewrite `ha` using `[div_eq_iff hs2]`. Take the linear combination `(-1 : ℝ) * ha`. Conclude with `irrational_sqrt_two ⟨((m : ℚ) - m') / a, by push_cast; exact hs.symm⟩`.
-/
theorem injective_mk_div_sqrt_two (L : PeriodPair) :
    Function.Injective fun m : ℕ ↦ Torus.mk L ((m : ℂ) * L.ω₁ / (Real.sqrt 2 : ℂ)) := by
  intro m m' hm
  simp only at hm
  rw [Torus.mk_eq_mk_iff] at hm
  have e : (m : ℂ) * L.ω₁ / (Real.sqrt 2 : ℂ) - (m' : ℂ) * L.ω₁ / (Real.sqrt 2 : ℂ) =
      ((((m : ℝ) - m') / Real.sqrt 2 : ℝ) : ℂ) * L.ω₁ := by
    push_cast
    ring
  rw [e] at hm
  obtain ⟨a, ha⟩ := exists_int_of_real_mul_mem L hm
  by_contra hne
  have hd : ((m : ℝ) - m') ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hne)
  have ha0 : (a : ℝ) ≠ 0 := by
    intro h0
    rw [h0] at ha
    exact hd ((div_eq_zero_iff.1 ha).resolve_right (Real.sqrt_pos.2 two_pos).ne')
  have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 two_pos).ne'
  have hs : Real.sqrt 2 = ((m : ℝ) - m') / a := by
    rw [eq_div_iff ha0]
    rw [div_eq_iff hs2] at ha
    linear_combination (-1 : ℝ) * ha
  exact irrational_sqrt_two ⟨((m : ℚ) - m') / a, by push_cast; exact hs.symm⟩

/- English proof (translation)
Establish `hg : AnalyticAt ℂ (fun z : ℂ ↦ (Real.sqrt 2 : ℂ) * z + 0) z₀` using `by fun_prop`. Establish `hd : deriv (fun z : ℂ ↦ (Real.sqrt 2 : ℂ) * z + 0) z₀ ≠ 0`. Establish `h1` using `((hasDerivAt_id' z₀).const_mul (Real.sqrt 2 : ℂ)).add_const 0`. Rewrite using `[h1.deriv, mul_one]`. Conclude with `sqrt_two_ne_zero`.

Use `meromorphicOrderAt_comp_of_deriv_ne_zero (f := ℘[L]) hg hd` as an intermediate fact. Rewrite `this` using `[Function.comp_def]`. Rewrite using `[this, L.order_weierstrassP _ hz]`.
-/
theorem meromorphicOrderAt_weierstrassP_sqrt_two (L : PeriodPair) {z₀ : ℂ}
    (hz : (Real.sqrt 2 : ℂ) * z₀ + 0 ∈ L.lattice) :
    meromorphicOrderAt (fun z ↦ ℘[L] ((Real.sqrt 2 : ℂ) * z + 0)) z₀ = -2 := by
  have hg : AnalyticAt ℂ (fun z : ℂ ↦ (Real.sqrt 2 : ℂ) * z + 0) z₀ := by fun_prop
  have hd : deriv (fun z : ℂ ↦ (Real.sqrt 2 : ℂ) * z + 0) z₀ ≠ 0 := by
    have h1 := ((hasDerivAt_id' z₀).const_mul (Real.sqrt 2 : ℂ)).add_const 0
    rw [h1.deriv, mul_one]
    exact sqrt_two_ne_zero
  have := meromorphicOrderAt_comp_of_deriv_ne_zero (f := ℘[L]) hg hd
  rw [Function.comp_def] at this
  rw [this, L.order_weierstrassP _ hz]

/- English proof (translation)
Use `set t : ℂ := (Real.sqrt 2 : ℂ)`. Use `set h : ℂ → ℂ := fun z ↦ ℘[L] (t * z + 0)`. Establish `mh : Meromorphic h` using `meromorphic_weierstrassP_affine L t 0`. Use `choose f hf hfe using fun i ↦ exists_isEllipticFunction_ellEval_eq L (p.coeff i)`. Use `set n := p.natDegree`.

Establish `mt : ∀ i, Meromorphic fun z ↦ f i z * h z ^ i` using `fun i x ↦ ((hf i).1 x).mul ((mh x).pow i)`. Establish `heval : (p.map (ellEval L).toRingHom).eval (germ h) = germ fun z ↦ ∑ i ∈ Finset.range (n + 1), f i z * h z ^ i`. Rewrite using `[eval_eq_sum_range, natDegree_map_eq_of_injective (ellEval_injective L), germ_sum _ mt]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Rewrite using `[coeff_map, show (fun z ↦ f i z * h z ^ i) = f i * h ^ i from rfl, germ_mul (hf i).1 (mh.pow (n := i)), germ_pow mh]`.

Use `congr 1`. Conclude with `hfe i`. Introduce `h0`. Rewrite `h0` using `[heval, germ_eq_zero_iff (fun x ↦ meromorphicAt_fun_sum _ fun i ↦ mt i x)]`. Establish `hfn : ¬ f n =ᶠ[codiscrete ℂ] 0`.

Introduce `hz`. Establish `h1 : ellEval L (p.coeff n) = 0`. Rewrite using `[hfe n, ← germ_zero]`. Conclude with `germ_congr (hf n).1 hz`. Rewrite `h1` using `[map_eq_zero_iff _ (ellEval_injective L)]`.

Conclude with `hp (leadingCoeff_eq_zero.1 h1)`. Use `set bad : Set ℂ := (⋃ i ∈ Finset.range (n + 1), singularSet (f i)) ∪ singularSet (f n)⁻¹`. Establish `hbad : (Torus.mk L '' bad).Finite`. Rewrite using `[image_union, image_iUnion₂]`. Use `Finite.union (Finite.biUnion (Finset.finite_toSet _) fun i _ ↦ finite_image_singularSet L (hf i).1 (hf i).2) ?_` and prove the remaining obligations.

Conclude with `finite_image_singularSet L (hf n).1.inv fun z l hl ↦ by`. Simplify using `only [Pi.inv_apply, (hf n).2 z l hl]`. Take `⟨m, hm⟩` from `(hbad.preimage (injective_mk_div_sqrt_two L).injOn).infinite_compl.nonempty`. Use `set z₀ : ℂ := (m : ℂ) * L.ω₁ / t`. Establish `hz₀ : z₀ ∉ bad` using `fun hb ↦ hm ⟨z₀, hb, rfl⟩`.

Establish `hpole : t * z₀ + 0 ∈ L.lattice`. Establish `: t * z₀ + 0 = (m : ℤ) • L.ω₁`. Simplify using `only [z₀, t, add_zero, zsmul_eq_mul, Int.cast_natCast]`. Clear denominators, using `[sqrt_two_ne_zero]` for the nonvanishing conditions. Rewrite using `[this]`.

Conclude with `L.lattice.smul_mem (m : ℤ) L.ω₁_mem_lattice`. Establish `han : ∀ i ∈ Finset.range (n + 1), AnalyticAt ℂ (f i) z₀` using `fun i hi ↦ by`. Assume the negation of the conclusion as `hna`. Conclude with `hz₀ (Or.inl (mem_iUnion₂.2 ⟨i, hi, hna⟩))`. Establish `haninv : AnalyticAt ℂ (f n)⁻¹ z₀`.

Assume the negation of the conclusion as `hna`. Conclude with `hz₀ (Or.inr hna)`. Establish `hoh : meromorphicOrderAt h z₀ = -2` using `meromorphicOrderAt_weierstrassP_sqrt_two L hpole`. Establish `hon : meromorphicOrderAt (f n) z₀ = 0`. Establish `h1` using `(han n (Finset.self_mem_range_succ n)).meromorphicOrderAt_nonneg`.

Establish `h2` using `haninv.meromorphicOrderAt_nonneg`. Rewrite `h2` using `[meromorphicOrderAt_inv]`. Establish `hne : meromorphicOrderAt (f n) z₀ ≠ ⊤` using `fun ht ↦ hfn (eventuallyEq_zero_codiscrete_of_nhdsNE (hf n).1 (meromorphicOrderAt_eq_top_iff.1 ht))`. Take `⟨k, hk⟩` from `WithTop.ne_top_iff_exists.1 hne`. Rewrite `h1`, `h2`, the goal using `[← hk]`.

Establish `: (0 : ℤ) ≤ k` using `by exact_mod_cast h1`. Establish `: (0 : ℤ) ≤ -k` using `by exact_mod_cast h2`. Establish `: k = 0` using `by omega`. Rewrite using `[this]`. Both sides reduce to the same expression.

Establish `hterm : ∀ i, meromorphicOrderAt (fun z ↦ f i z * h z ^ i) z₀ = meromorphicOrderAt (f i) z₀ + ((i * (-2) : ℤ) : WithTop ℤ)` using `fun i ↦ by`. Rewrite using `[show (fun z ↦ f i z * h z ^ i) = f i * h ^ i from rfl, meromorphicOrderAt_mul ((hf i).1 z₀) ((mh z₀).pow i), meromorphicOrderAt_pow (mh z₀), hoh]`. Use `congr 1`. Establish `htop : meromorphicOrderAt (fun z ↦ f n z * h z ^ n) z₀ = ((-2 * n : ℤ) : WithTop ℤ)`. Rewrite using `[hterm, hon, zero_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hrest : ((-2 * n : ℤ) : WithTop ℤ) < meromorphicOrderAt (fun z ↦ ∑ i ∈ Finset.range n, f i z * h z ^ i) z₀`. Apply `lt_meromorphicOrderAt_sum _ (fun i ↦ mt i z₀)` to reduce the goal to its premises. Introduce `i hi`.

Rewrite using `[hterm]`. Establish `hi' : i < n` using `Finset.mem_range.1 hi`. Establish `h0` using `(han i (Finset.mem_range.2 (by omega))).meromorphicOrderAt_nonneg`. Consider the cases of `hc : meromorphicOrderAt (f i) z₀ with`. Consider the case `top`.

Rewrite using `[top_add]`. Conclude with `WithTop.coe_lt_top _`. Consider the case `coe k`. Rewrite `h0` using `[hc]`. Establish `: (0 : ℤ) ≤ k` using `by exact_mod_cast h0`.

Rewrite using `[← WithTop.coe_add, WithTop.coe_lt_coe]`. Use linear arithmetic over natural numbers and integers. Establish `hsum : meromorphicOrderAt (fun z ↦ ∑ i ∈ Finset.range (n + 1), f i z * h z ^ i) z₀ = ((-2 * n : ℤ) : WithTop ℤ)`. Establish `e : (fun z ↦ ∑ i ∈ Finset.range (n + 1), f i z * h z ^ i) = (fun z ↦ f n z * h z ^ n) + fun z ↦ ∑ i ∈ Finset.range n, f i z * h z ^ i`. Use function extensionality and compare the values at `z`.

Simplify using `only [Finset.sum_range_succ, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, meromorphicOrderAt_add_eq_left_of_lt (meromorphicAt_fun_sum _ fun i ↦ mt i z₀) (htop ▸ hrest), htop]`. Establish `hzero : meromorphicOrderAt (fun z ↦ ∑ i ∈ Finset.range (n + 1), f i z * h z ^ i) z₀ = ⊤` using `meromorphicOrderAt_eq_top_iff.2 (eventuallyEq_zero_codiscrete_iff.1 h0 z₀)`. Rewrite `hzero` using `[hsum]`.

Conclude with `WithTop.coe_ne_top hzero`.
-/
theorem ellEval_indep (L : PeriodPair) (p : (weierstrassCurve L).toAffine.FunctionField[X])
    (hp : p ≠ 0) :
    (p.map (ellEval L).toRingHom).eval (germ fun z ↦ ℘[L] ((Real.sqrt 2 : ℂ) * z + 0)) ≠ 0 := by
  set t : ℂ := (Real.sqrt 2 : ℂ)
  set h : ℂ → ℂ := fun z ↦ ℘[L] (t * z + 0)
  have mh : Meromorphic h := meromorphic_weierstrassP_affine L t 0
  choose f hf hfe using fun i ↦ exists_isEllipticFunction_ellEval_eq L (p.coeff i)
  set n := p.natDegree
  have mt : ∀ i, Meromorphic fun z ↦ f i z * h z ^ i := fun i x ↦
    ((hf i).1 x).mul ((mh x).pow i)
  have heval : (p.map (ellEval L).toRingHom).eval (germ h) =
      germ fun z ↦ ∑ i ∈ Finset.range (n + 1), f i z * h z ^ i := by
    rw [eval_eq_sum_range, natDegree_map_eq_of_injective (ellEval_injective L),
      germ_sum _ mt]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [coeff_map, show (fun z ↦ f i z * h z ^ i) = f i * h ^ i from rfl,
      germ_mul (hf i).1 (mh.pow (n := i)), germ_pow mh]
    congr 1
    exact hfe i
  intro h0
  rw [heval, germ_eq_zero_iff (fun x ↦ meromorphicAt_fun_sum _ fun i ↦ mt i x)] at h0

  have hfn : ¬ f n =ᶠ[codiscrete ℂ] 0 := by
    intro hz
    have h1 : ellEval L (p.coeff n) = 0 := by
      rw [hfe n, ← germ_zero]
      exact germ_congr (hf n).1 hz
    rw [map_eq_zero_iff _ (ellEval_injective L)] at h1
    exact hp (leadingCoeff_eq_zero.1 h1)

  set bad : Set ℂ := (⋃ i ∈ Finset.range (n + 1), singularSet (f i)) ∪ singularSet (f n)⁻¹
  have hbad : (Torus.mk L '' bad).Finite := by
    rw [image_union, image_iUnion₂]
    refine Finite.union (Finite.biUnion (Finset.finite_toSet _) fun i _ ↦
      finite_image_singularSet L (hf i).1 (hf i).2) ?_
    exact finite_image_singularSet L (hf n).1.inv fun z l hl ↦ by
      simp only [Pi.inv_apply, (hf n).2 z l hl]
  obtain ⟨m, hm⟩ := (hbad.preimage (injective_mk_div_sqrt_two L).injOn).infinite_compl.nonempty
  set z₀ : ℂ := (m : ℂ) * L.ω₁ / t
  have hz₀ : z₀ ∉ bad := fun hb ↦ hm ⟨z₀, hb, rfl⟩
  have hpole : t * z₀ + 0 ∈ L.lattice := by
    have : t * z₀ + 0 = (m : ℤ) • L.ω₁ := by
      simp only [z₀, t, add_zero, zsmul_eq_mul, Int.cast_natCast]
      field_simp [sqrt_two_ne_zero]
    rw [this]
    exact L.lattice.smul_mem (m : ℤ) L.ω₁_mem_lattice
  have han : ∀ i ∈ Finset.range (n + 1), AnalyticAt ℂ (f i) z₀ := fun i hi ↦ by
    by_contra hna
    exact hz₀ (Or.inl (mem_iUnion₂.2 ⟨i, hi, hna⟩))
  have haninv : AnalyticAt ℂ (f n)⁻¹ z₀ := by
    by_contra hna
    exact hz₀ (Or.inr hna)
  have hoh : meromorphicOrderAt h z₀ = -2 := meromorphicOrderAt_weierstrassP_sqrt_two L hpole
  have hon : meromorphicOrderAt (f n) z₀ = 0 := by
    have h1 := (han n (Finset.self_mem_range_succ n)).meromorphicOrderAt_nonneg
    have h2 := haninv.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_inv] at h2
    have hne : meromorphicOrderAt (f n) z₀ ≠ ⊤ := fun ht ↦
      hfn (eventuallyEq_zero_codiscrete_of_nhdsNE (hf n).1 (meromorphicOrderAt_eq_top_iff.1 ht))
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hne
    rw [← hk] at h1 h2 ⊢
    have : (0 : ℤ) ≤ k := by exact_mod_cast h1
    have : (0 : ℤ) ≤ -k := by exact_mod_cast h2
    have : k = 0 := by omega
    rw [this]
    rfl
  have hterm : ∀ i, meromorphicOrderAt (fun z ↦ f i z * h z ^ i) z₀ =
      meromorphicOrderAt (f i) z₀ + ((i * (-2) : ℤ) : WithTop ℤ) := fun i ↦ by
    rw [show (fun z ↦ f i z * h z ^ i) = f i * h ^ i from rfl,
      meromorphicOrderAt_mul ((hf i).1 z₀) ((mh z₀).pow i), meromorphicOrderAt_pow (mh z₀), hoh]
    congr 1
  have htop : meromorphicOrderAt (fun z ↦ f n z * h z ^ n) z₀ = ((-2 * n : ℤ) : WithTop ℤ) := by
    rw [hterm, hon, zero_add]
    congr 1
    ring
  have hrest : ((-2 * n : ℤ) : WithTop ℤ) <
      meromorphicOrderAt (fun z ↦ ∑ i ∈ Finset.range n, f i z * h z ^ i) z₀ := by
    apply lt_meromorphicOrderAt_sum _ (fun i ↦ mt i z₀)
    intro i hi
    rw [hterm]
    have hi' : i < n := Finset.mem_range.1 hi
    have h0 := (han i (Finset.mem_range.2 (by omega))).meromorphicOrderAt_nonneg
    cases hc : meromorphicOrderAt (f i) z₀ with
    | top =>
      rw [top_add]
      exact WithTop.coe_lt_top _
    | coe k =>
      rw [hc] at h0
      have : (0 : ℤ) ≤ k := by exact_mod_cast h0
      rw [← WithTop.coe_add, WithTop.coe_lt_coe]
      omega
  have hsum : meromorphicOrderAt (fun z ↦ ∑ i ∈ Finset.range (n + 1), f i z * h z ^ i) z₀ =
      ((-2 * n : ℤ) : WithTop ℤ) := by
    have e : (fun z ↦ ∑ i ∈ Finset.range (n + 1), f i z * h z ^ i) =
        (fun z ↦ f n z * h z ^ n) + fun z ↦ ∑ i ∈ Finset.range n, f i z * h z ^ i := by
      funext z
      simp only [Finset.sum_range_succ, Pi.add_apply]
      ring
    rw [e, meromorphicOrderAt_add_eq_left_of_lt (meromorphicAt_fun_sum _ fun i ↦ mt i z₀)
      (htop ▸ hrest), htop]
  have hzero : meromorphicOrderAt (fun z ↦ ∑ i ∈ Finset.range (n + 1), f i z * h z ^ i) z₀ = ⊤ :=
    meromorphicOrderAt_eq_top_iff.2 (eventuallyEq_zero_codiscrete_iff.1 h0 z₀)
  rw [hsum] at hzero
  exact WithTop.coe_ne_top hzero

end Elliptic
end GroundTheory.Global
