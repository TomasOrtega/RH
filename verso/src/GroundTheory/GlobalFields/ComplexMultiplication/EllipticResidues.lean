import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticFunctions
import GroundTheory.GlobalFields.ComplexMultiplication.Residue
import GroundTheory.GlobalFields.ComplexMultiplication.RectangleIntegral
import GroundTheory.GlobalFields.ComplexMultiplication.ResidueTheorem

open Complex Filter Topology Set
open scoped Interval Real

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable {L : PeriodPair}

/- English proof (translation)
Rewrite using `[← residue_comp_add (hf (z + l)), hp.comp_add hl]`.
-/
lemma IsPeriodic.residue_add {f : ℂ → ℂ} (hp : IsPeriodic L f) (hf : Meromorphic f) {l : ℂ}
    (hl : l ∈ L.lattice) (z : ℂ) : residue f (z + l) = residue f z := by
  rw [← residue_comp_add (hf (z + l)), hp.comp_add hl]

/- English proof (translation)
Establish `hzw` using `(Torus.mk_eq_mk_iff L).1 h`. Use `hp.residue_add hf hzw w` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis.
-/
lemma IsPeriodic.residue_eq_of_mk_eq {f : ℂ → ℂ} (hp : IsPeriodic L f) (hf : Meromorphic f)
    {z w : ℂ} (h : Torus.mk L z = Torus.mk L w) : residue f z = residue f w := by
  have hzw := (Torus.mk_eq_mk_iff L).1 h
  have := hp.residue_add hf hzw w
  rwa [add_sub_cancel] at this

variable (L) in

def torusResidue (f : ℂ → ℂ) (x : Torus L) : ℂ :=
  residue f x.out

/- English proof (translation)
The claim follows from `hf.2.residue_eq_of_mk_eq hf.1 (QuotientAddGroup.out_eq' (Torus.mk L z))`.
-/
lemma torusResidue_mk {f : ℂ → ℂ} (hf : IsEllipticFunction L f) (z : ℂ) :
    torusResidue L f (Torus.mk L z) = residue f z :=
  hf.2.residue_eq_of_mk_eq hf.1 (QuotientAddGroup.out_eq' (Torus.mk L z))

variable (L) in
/- English proof (translation)
Introduce `h`. Use `LinearIndependent.pair_iff.mp L.indep 1 0 (by simp [h])` as an intermediate fact. Simplify using `at this`.
-/
lemma ω₁_ne_zero : L.ω₁ ≠ 0 := by
  intro h
  have := LinearIndependent.pair_iff.mp L.indep 1 0 (by simp [h])
  simp at this

variable (L) in
/- English proof (translation)
Introduce `him`. Establish `hc` using `ω₁_ne_zero L`. Use `set τ := L.ω₂ / L.ω₁ with hτdef`. Establish `hτ : ((τ.re : ℝ) : ℂ) = τ` using `Complex.ext (by simp) (by simp [him])`. Establish `key` using `LinearIndependent.pair_iff.mp L.indep τ.re (-1) (by`.

Rewrite using `[Complex.real_smul, Complex.real_smul, hτ, hτdef]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Use the proof step `ring)`. Evaluate the numerical expressions using `at key`.
-/
lemma im_ω₂_div_ω₁_ne_zero : (L.ω₂ / L.ω₁).im ≠ 0 := by
  intro him
  have hc := ω₁_ne_zero L
  set τ := L.ω₂ / L.ω₁ with hτdef
  have hτ : ((τ.re : ℝ) : ℂ) = τ := Complex.ext (by simp) (by simp [him])
  have key := LinearIndependent.pair_iff.mp L.indep τ.re (-1) (by
    rw [Complex.real_smul, Complex.real_smul, hτ, hτdef]
    push_cast
    field_simp
    ring)
  norm_num at key

/- English proof (translation)
Take `⟨hmer, hper⟩` from `hf`. Establish `hω₁ : L.ω₁ ≠ 0` using `ω₁_ne_zero L`. Use `set c := L.ω₁ with hc_def`. Establish `hc : c ≠ 0` using `ω₁_ne_zero L`. Establish `hcL : c ∈ L.lattice` using `L.ω₁_mem_lattice`.

Choose the witnesses or unpack the hypotheses as in `⟨τ, s, hs, hω₂, hτ⟩ : ∃ τ : ℂ, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ L.ω₂ = (s : ℂ) * (c * τ) ∧ 0 < τ.im := by`. Break down `lt_or_gt_of_ne (im_ω₂_div_ω₁_ne_zero L) with h | h` into its components or cases. Use `⟨-(L.ω₂ / L.ω₁), -1, Or.inr rfl, ?_, by simpa using h⟩` and prove the remaining obligations. Rewrite using `[hc_def]`. Establish `h0` using `ω₁_ne_zero L`.

Clear the denominators using the available nonvanishing facts. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨L.ω₂ / L.ω₁, 1, Or.inl rfl, ?_, h⟩` and prove the remaining obligations. Rewrite using `[hc_def]`.

Establish `h0` using `ω₁_ne_zero L`. Clear the denominators using the available nonvanishing facts. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hτL : c * τ ∈ L.lattice`.

Establish `h2` using `L.ω₂_mem_lattice`. Break down `hs with rfl | rfl` into its components or cases. Simplify `h2` using `[hω₂]`. Simplify `L.lattice.neg_mem h2` using `[hω₂]`. Use `set h := τ.im with hh`.

Use `set g : ℂ → ℂ := fun w ↦ f (c * w) with hg_def`. Establish `hg1 : ∀ u, g (u + 1) = g u` using `fun u ↦ by`. Simplify using `only [hg_def, mul_add, mul_one]`. Conclude with `hper _ _ hcL`. Establish `hgτ : ∀ u, g (u + τ) = g u` using `fun u ↦ by`.

Simplify using `only [hg_def, mul_add]`. Conclude with `hper _ _ hτL`. Establish `hgmer : Meromorphic g` using `fun w ↦ (hmer (c * w)).comp_analyticAt (g := fun w ↦ c * w) (by fun_prop)`. Establish `hScount : (singularSet g).Countable`. Establish `e : singularSet g = ⋃ n : ℕ, Metric.closedBall (0 : ℂ) n ∩ singularSet g`.

Use extensionality with `z`. Simplify using `only [mem_iUnion, mem_inter_iff, Metric.mem_closedBall, dist_zero_right]`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Take `⟨n, hn⟩` from `exists_nat_ge ‖z‖`.

Conclude with `⟨n, hn, hz⟩`. Introduce and unpack `⟨n, -, hz⟩`. Conclude with `hz`. Rewrite using `[e]`. Conclude with `countable_iUnion fun n ↦ (finite_inter_singularSet hgmer (isCompact_closedBall 0 (n : ℝ))).countable`.

Take `⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, x₀ ∈ ((fun s : ℂ ↦ s.re) '' singularSet g ∪ (fun s : ℂ ↦ s.re - 1) '' singularSet g)ᶜ` from `(((hScount.image _).union (hScount.image _)).dense_compl ℝ).nonempty`. Take `⟨y₀, hy₀⟩ : ∃ y₀ : ℝ, y₀ ∈ ((fun s : ℂ ↦ s.im) '' singularSet g ∪ (fun s : ℂ ↦ s.im - h) '' singularSet g)ᶜ` from `(((hScount.image _).union (hScount.image _)).dense_compl ℝ).nonempty`. Use `set a : ℂ := x₀ + y₀ * I with ha`. Use `set b : ℂ := a + 1 + h * I with hb`. Establish `ha_re : a.re = x₀` using `by simp [ha]`.

Establish `ha_im : a.im = y₀` using `by simp [ha]`. Establish `hb_re : b.re = x₀ + 1` using `by simp [hb, ha]`. Establish `hb_im : b.im = y₀ + h` using `by simp [hb, ha]`. Use `set K : Set ℂ := [[a.re, b.re]] ×ℂ [[a.im, b.im]] with hK_def`. Establish `hK : IsCompact K` using `isCompact_uIcc.reProdIm isCompact_uIcc`.

Establish `hKmem : ∀ u : ℂ, u ∈ K ↔ u.re ∈ Icc x₀ (x₀ + 1) ∧ u.im ∈ Icc y₀ (y₀ + h)`. Introduce `u`. Rewrite using `[hK_def, mem_reProdIm, ha_re, hb_re, ha_im, hb_im, uIcc_of_le (by linarith), uIcc_of_le (by linarith)]`. Use `set T : Finset ℂ := (finite_inter_singularSet hgmer hK).toFinset with hT`. Establish `hTmem : ∀ p, p ∈ T ↔ p ∈ K ∧ p ∈ singularSet g`.

Introduce `p`. Simplify using `[hT]`. Establish `hTin : ∀ p ∈ T, x₀ < p.re ∧ p.re < x₀ + 1 ∧ y₀ < p.im ∧ p.im < y₀ + h`. Introduce `p hp`. Take `⟨hpK, hpS⟩` from `(hTmem p).1 hp`.

Take `⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩` from `(hKmem p).1 hpK`. Establish `nr1 : p.re ≠ x₀` using `fun e ↦ hx₀ (Or.inl ⟨p, hpS, e⟩)`. Establish `nr2 : p.re ≠ x₀ + 1` using `fun e ↦ hx₀ (Or.inr ⟨p, hpS, by simp [e]⟩)`. Establish `ni1 : p.im ≠ y₀` using `fun e ↦ hy₀ (Or.inl ⟨p, hpS, e⟩)`. Establish `ni2 : p.im ≠ y₀ + h` using `fun e ↦ hy₀ (Or.inr ⟨p, hpS, by simp [e]⟩)`.

Conclude with `⟨lt_of_le_of_ne r1 (Ne.symm nr1), lt_of_le_of_ne r2 nr2, lt_of_le_of_ne i1 (Ne.symm ni1), lt_of_le_of_ne i2 ni2⟩`. Establish `hsum0 : ∑ p ∈ T, residue g p = 0`. Establish `hres` using `rectIntegral_eq_sum_residue (f := g) (z := a) (w := b) T (fun p hp ↦ by`. Take `⟨r1, r2, i1, i2⟩` from `hTin p hp`. Conclude with `⟨by rwa [ha_re], by rwa [hb_re], by rwa [ha_im], by rwa [hb_im]⟩)`.

Use the proof step `(fun p _ ↦ hgmer p)`. Use the proof step `(fun u hu huT ↦ by`. Assume the negation of the conclusion as `hna`. Conclude with `huT ((hTmem u).2 ⟨hu, hna⟩))`. Establish `hper0 : rectIntegral g a b = 0` using `rectIntegral_eq_zero_of_periodic hg1 hgτ a`.

Rewrite `hres` using `[hper0]`. Establish `h2pi : (2 * π * I : ℂ) ≠ 0` using `two_pi_I_ne_zero`. Conclude with `(mul_eq_zero.1 hres.symm).resolve_left h2pi`. Use `set φ : ℂ → Torus L := fun p ↦ Torus.mk L (c * p) with hφ`. Establish `hlat : ∀ m n : ℤ, (m : ℂ) * c + (n : ℂ) * (c * τ) ∈ L.lattice` using `fun m n ↦ L.lattice.add_mem (by simpa [zsmul_eq_mul] using L.lattice.smul_mem m hcL) (by simpa [zsmul_eq_mul] using L.lattice.smul_mem n hτL)`.

Establish `hsupp : Function.support (torusResidue L f) ⊆ ↑(T.image φ)`. Introduce `x hx`. Use `set z := x.out with hz`. Establish `hxz : Torus.mk L z = x` using `QuotientAddGroup.out_eq' x`. Establish `hnz : residue f z ≠ 0` using `hx`.

Establish `hfz : ¬ AnalyticAt ℂ f z` using `fun ha ↦ hnz (residue_eq_zero_of_analyticAt ha)`. Use `set w := z / c with hw`. Use `set n : ℤ := ⌊(w.im - y₀) / h⌋ with hn`. Use `set p₁ : ℂ := w - n * τ with hp₁`. Use `set m : ℤ := ⌊p₁.re - x₀⌋ with hm`.

Use `set p : ℂ := p₁ - m with hp`. Establish `hp_re : p.re = p₁.re - m` using `by simp [hp]`. Establish `hp_im : p.im = w.im - n * h` using `by simp [hp, hp₁, hh]`. Establish `hn1` using `Int.floor_le ((w.im - y₀) / h)`. Establish `hn2` using `Int.lt_floor_add_one ((w.im - y₀) / h)`.

Establish `hm1` using `Int.floor_le (p₁.re - x₀)`. Establish `hm2` using `Int.lt_floor_add_one (p₁.re - x₀)`. Rewrite `hn1`, `hn2` using `[← hn]`. Rewrite `hm1`, `hm2` using `[← hm]`. Rewrite `hn1` using `[le_div_iff₀ hτ]`.

Rewrite `hn2` using `[div_lt_iff₀ hτ]`. Establish `hpK : p ∈ K`. Rewrite using `[hKmem, hp_re, hp_im]`. Use `⟨⟨by linarith, by linarith⟩, ⟨by nlinarith, by nlinarith⟩⟩` and prove the remaining obligations. Establish `hcp : z = c * p + ((m : ℂ) * c + (n : ℂ) * (c * τ))`.

Simplify using `only [hp, hp₁, hw]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hpS : p ∈ singularSet g`. Introduce `hga`.

Apply `hfz` to reduce the goal to its premises. Establish `h1 : AnalyticAt ℂ (fun z' ↦ g (c⁻¹ * z')) (c * p)`. Establish `: AnalyticAt ℂ (fun z' ↦ c⁻¹ * z') (c * p)` using `by fun_prop`. Conclude with `hga.comp_of_eq this (by field_simp)`. Establish `h2 : (fun z' ↦ g (c⁻¹ * z')) = f`.

Use function extensionality and compare the values at `z'`. Simplify using `only [hg_def]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite `h1` using `[h2]`.

Rewrite using `[hcp]`. Conclude with `(hper.analyticAt_add_iff (hlat m n) (c * p)).2 h1`. Use `Finset.mem_coe.2 (Finset.mem_image.2 ⟨p, (hTmem p).2 ⟨hpK, hpS⟩, ?_⟩)` and prove the remaining obligations. Rewrite using `[← hxz, hφ]`. Conclude with `((Torus.mk_eq_mk_iff L).2 (by rw [hcp]; simpa using hlat m n)).symm`.

Establish `hinj : Set.InjOn φ ↑T`. Introduce `p hp q hq hpq`. Take `⟨pr1, pr2, pi1, pi2⟩` from `hTin p hp`. Take `⟨qr1, qr2, qi1, qi2⟩` from `hTin q hq`. Establish `hdiff` using `(Torus.mk_eq_mk_iff L).1 hpq`.

Take `⟨m, n, hmn⟩` from `PeriodPair.mem_lattice.1 hdiff`. Establish `hk : p - q = (m : ℂ) + ((n * s : ℤ) : ℂ) * τ`. Establish `e : c * (p - q) = c * ((m : ℂ) + ((n * s : ℤ) : ℂ) * τ)`. Rewrite using `[mul_sub, ← hmn, hω₂]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `mul_left_cancel₀ hc e`. Use `set k : ℤ := n * s with hkdef`. Establish `him` using `congrArg Complex.im hk`. Establish `hre` using `congrArg Complex.re hk`.

Simplify using `only [sub_im, add_im, intCast_im, mul_im, intCast_re, zero_mul, add_zero, zero_add, sub_re, add_re, intCast_re, mul_re, intCast_im, zero_mul, sub_zero] at him hre`. Establish `hk0 : k = 0`. Establish `h1 : (k : ℝ) * h < h` using `by rw [hh]; linarith`. Establish `h2 : -h < (k : ℝ) * h` using `by rw [hh]; linarith`. Establish `h3 : (k : ℝ) < 1`.

Assume the negation of the conclusion as `hc'`. Rewrite `hc'` using `[not_lt]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h4 : (-1 : ℝ) < k`. Assume the negation of the conclusion as `hc'`.

Rewrite `hc'` using `[not_lt]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h5 : k < 1` using `by exact_mod_cast h3`. Establish `h6 : -1 < k` using `by exact_mod_cast h4`. Use linear arithmetic over natural numbers and integers.

Rewrite `hre`, `him` using `[hk0]`. Simplify using `only [Int.cast_zero, zero_mul, add_zero, sub_eq_zero] at hre him`. Establish `hm0 : m = 0`. Establish `h3 : (m : ℝ) < 1` using `by linarith`. Establish `h4 : (-1 : ℝ) < m` using `by linarith`.

Establish `h5 : m < 1` using `by exact_mod_cast h3`. Establish `h6 : -1 < m` using `by exact_mod_cast h4`. Use linear arithmetic over natural numbers and integers. Rewrite `hre` using `[hm0]`. Simplify using `only [Int.cast_zero, sub_eq_zero] at hre`.

Conclude with `Complex.ext hre him`. Rewrite using `[finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image hinj]`. Establish `hterm : ∀ p ∈ T, torusResidue L f (φ p) = c * residue g p`. Introduce `p _`. Rewrite using `[hφ, torusResidue_mk ⟨hmer, hper⟩, show residue g p = c⁻¹ * residue f (c * p) from residue_comp_mul hc (hmer _)]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum0, mul_zero]`.
-/
theorem finsum_torusResidue_eq_zero {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    ∑ᶠ x : Torus L, torusResidue L f x = 0 := by
  classical
  obtain ⟨hmer, hper⟩ := hf
  have hω₁ : L.ω₁ ≠ 0 := ω₁_ne_zero L
  set c := L.ω₁ with hc_def
  have hc : c ≠ 0 := ω₁_ne_zero L
  have hcL : c ∈ L.lattice := L.ω₁_mem_lattice
  obtain ⟨τ, s, hs, hω₂, hτ⟩ : ∃ τ : ℂ, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      L.ω₂ = (s : ℂ) * (c * τ) ∧ 0 < τ.im := by
    rcases lt_or_gt_of_ne (im_ω₂_div_ω₁_ne_zero L) with h | h
    · refine ⟨-(L.ω₂ / L.ω₁), -1, Or.inr rfl, ?_, by simpa using h⟩
      rw [hc_def]
      have h0 := ω₁_ne_zero L
      field_simp
      push_cast
      ring
    · refine ⟨L.ω₂ / L.ω₁, 1, Or.inl rfl, ?_, h⟩
      rw [hc_def]
      have h0 := ω₁_ne_zero L
      field_simp
      push_cast
      ring
  have hτL : c * τ ∈ L.lattice := by
    have h2 := L.ω₂_mem_lattice
    rcases hs with rfl | rfl
    · simpa [hω₂] using h2
    · simpa [hω₂] using L.lattice.neg_mem h2
  set h := τ.im with hh
  set g : ℂ → ℂ := fun w ↦ f (c * w) with hg_def
  have hg1 : ∀ u, g (u + 1) = g u := fun u ↦ by
    simp only [hg_def, mul_add, mul_one]
    exact hper _ _ hcL
  have hgτ : ∀ u, g (u + τ) = g u := fun u ↦ by
    simp only [hg_def, mul_add]
    exact hper _ _ hτL
  have hgmer : Meromorphic g := fun w ↦
    (hmer (c * w)).comp_analyticAt (g := fun w ↦ c * w) (by fun_prop)

  have hScount : (singularSet g).Countable := by
    have e : singularSet g = ⋃ n : ℕ, Metric.closedBall (0 : ℂ) n ∩ singularSet g := by
      ext z
      simp only [mem_iUnion, mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
      constructor
      · intro hz
        obtain ⟨n, hn⟩ := exists_nat_ge ‖z‖
        exact ⟨n, hn, hz⟩
      · rintro ⟨n, -, hz⟩
        exact hz
    rw [e]
    exact countable_iUnion fun n ↦
      (finite_inter_singularSet hgmer (isCompact_closedBall 0 (n : ℝ))).countable

  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, x₀ ∈ ((fun s : ℂ ↦ s.re) '' singularSet g ∪
      (fun s : ℂ ↦ s.re - 1) '' singularSet g)ᶜ :=
    (((hScount.image _).union (hScount.image _)).dense_compl ℝ).nonempty
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ℝ, y₀ ∈ ((fun s : ℂ ↦ s.im) '' singularSet g ∪
      (fun s : ℂ ↦ s.im - h) '' singularSet g)ᶜ :=
    (((hScount.image _).union (hScount.image _)).dense_compl ℝ).nonempty
  set a : ℂ := x₀ + y₀ * I with ha
  set b : ℂ := a + 1 + h * I with hb
  have ha_re : a.re = x₀ := by simp [ha]
  have ha_im : a.im = y₀ := by simp [ha]
  have hb_re : b.re = x₀ + 1 := by simp [hb, ha]
  have hb_im : b.im = y₀ + h := by simp [hb, ha]
  set K : Set ℂ := [[a.re, b.re]] ×ℂ [[a.im, b.im]] with hK_def
  have hK : IsCompact K := isCompact_uIcc.reProdIm isCompact_uIcc
  have hKmem : ∀ u : ℂ, u ∈ K ↔ u.re ∈ Icc x₀ (x₀ + 1) ∧ u.im ∈ Icc y₀ (y₀ + h) := by
    intro u
    rw [hK_def, mem_reProdIm, ha_re, hb_re, ha_im, hb_im, uIcc_of_le (by linarith),
      uIcc_of_le (by linarith)]
  set T : Finset ℂ := (finite_inter_singularSet hgmer hK).toFinset with hT
  have hTmem : ∀ p, p ∈ T ↔ p ∈ K ∧ p ∈ singularSet g := by
    intro p
    simp [hT]

  have hTin : ∀ p ∈ T, x₀ < p.re ∧ p.re < x₀ + 1 ∧ y₀ < p.im ∧ p.im < y₀ + h := by
    intro p hp
    obtain ⟨hpK, hpS⟩ := (hTmem p).1 hp
    obtain ⟨⟨r1, r2⟩, ⟨i1, i2⟩⟩ := (hKmem p).1 hpK
    have nr1 : p.re ≠ x₀ := fun e ↦ hx₀ (Or.inl ⟨p, hpS, e⟩)
    have nr2 : p.re ≠ x₀ + 1 := fun e ↦ hx₀ (Or.inr ⟨p, hpS, by simp [e]⟩)
    have ni1 : p.im ≠ y₀ := fun e ↦ hy₀ (Or.inl ⟨p, hpS, e⟩)
    have ni2 : p.im ≠ y₀ + h := fun e ↦ hy₀ (Or.inr ⟨p, hpS, by simp [e]⟩)
    exact ⟨lt_of_le_of_ne r1 (Ne.symm nr1), lt_of_le_of_ne r2 nr2,
      lt_of_le_of_ne i1 (Ne.symm ni1), lt_of_le_of_ne i2 ni2⟩

  have hsum0 : ∑ p ∈ T, residue g p = 0 := by
    have hres := rectIntegral_eq_sum_residue (f := g) (z := a) (w := b) T
      (fun p hp ↦ by
        obtain ⟨r1, r2, i1, i2⟩ := hTin p hp
        exact ⟨by rwa [ha_re], by rwa [hb_re], by rwa [ha_im], by rwa [hb_im]⟩)
      (fun p _ ↦ hgmer p)
      (fun u hu huT ↦ by
        by_contra hna
        exact huT ((hTmem u).2 ⟨hu, hna⟩))
    have hper0 : rectIntegral g a b = 0 := rectIntegral_eq_zero_of_periodic hg1 hgτ a
    rw [hper0] at hres
    have h2pi : (2 * π * I : ℂ) ≠ 0 := two_pi_I_ne_zero
    exact (mul_eq_zero.1 hres.symm).resolve_left h2pi

  set φ : ℂ → Torus L := fun p ↦ Torus.mk L (c * p) with hφ
  have hlat : ∀ m n : ℤ, (m : ℂ) * c + (n : ℂ) * (c * τ) ∈ L.lattice := fun m n ↦
    L.lattice.add_mem (by simpa [zsmul_eq_mul] using L.lattice.smul_mem m hcL)
      (by simpa [zsmul_eq_mul] using L.lattice.smul_mem n hτL)

  have hsupp : Function.support (torusResidue L f) ⊆ ↑(T.image φ) := by
    intro x hx
    set z := x.out with hz
    have hxz : Torus.mk L z = x := QuotientAddGroup.out_eq' x
    have hnz : residue f z ≠ 0 := hx
    have hfz : ¬ AnalyticAt ℂ f z := fun ha ↦ hnz (residue_eq_zero_of_analyticAt ha)
    set w := z / c with hw
    set n : ℤ := ⌊(w.im - y₀) / h⌋ with hn
    set p₁ : ℂ := w - n * τ with hp₁
    set m : ℤ := ⌊p₁.re - x₀⌋ with hm
    set p : ℂ := p₁ - m with hp
    have hp_re : p.re = p₁.re - m := by simp [hp]
    have hp_im : p.im = w.im - n * h := by simp [hp, hp₁, hh]
    have hn1 := Int.floor_le ((w.im - y₀) / h)
    have hn2 := Int.lt_floor_add_one ((w.im - y₀) / h)
    have hm1 := Int.floor_le (p₁.re - x₀)
    have hm2 := Int.lt_floor_add_one (p₁.re - x₀)
    rw [← hn] at hn1 hn2
    rw [← hm] at hm1 hm2
    rw [le_div_iff₀ hτ] at hn1
    rw [div_lt_iff₀ hτ] at hn2
    have hpK : p ∈ K := by
      rw [hKmem, hp_re, hp_im]
      refine ⟨⟨by linarith, by linarith⟩, ⟨by nlinarith, by nlinarith⟩⟩
    have hcp : z = c * p + ((m : ℂ) * c + (n : ℂ) * (c * τ)) := by
      simp only [hp, hp₁, hw]
      field_simp
      ring
    have hpS : p ∈ singularSet g := by
      intro hga
      apply hfz
      have h1 : AnalyticAt ℂ (fun z' ↦ g (c⁻¹ * z')) (c * p) := by
        have : AnalyticAt ℂ (fun z' ↦ c⁻¹ * z') (c * p) := by fun_prop
        exact hga.comp_of_eq this (by field_simp)
      have h2 : (fun z' ↦ g (c⁻¹ * z')) = f := by
        funext z'
        simp only [hg_def]
        congr 1
        field_simp
      rw [h2] at h1
      rw [hcp]
      exact (hper.analyticAt_add_iff (hlat m n) (c * p)).2 h1
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨p, (hTmem p).2 ⟨hpK, hpS⟩, ?_⟩)
    rw [← hxz, hφ]
    exact ((Torus.mk_eq_mk_iff L).2 (by rw [hcp]; simpa using hlat m n)).symm

  have hinj : Set.InjOn φ ↑T := by
    intro p hp q hq hpq
    obtain ⟨pr1, pr2, pi1, pi2⟩ := hTin p hp
    obtain ⟨qr1, qr2, qi1, qi2⟩ := hTin q hq
    have hdiff := (Torus.mk_eq_mk_iff L).1 hpq
    obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.1 hdiff
    have hk : p - q = (m : ℂ) + ((n * s : ℤ) : ℂ) * τ := by
      have e : c * (p - q) = c * ((m : ℂ) + ((n * s : ℤ) : ℂ) * τ) := by
        rw [mul_sub, ← hmn, hω₂]
        push_cast
        ring
      exact mul_left_cancel₀ hc e
    set k : ℤ := n * s with hkdef
    have him := congrArg Complex.im hk
    have hre := congrArg Complex.re hk
    simp only [sub_im, add_im, intCast_im, mul_im, intCast_re, zero_mul, add_zero, zero_add,
      sub_re, add_re, intCast_re, mul_re, intCast_im, zero_mul, sub_zero] at him hre
    have hk0 : k = 0 := by
      have h1 : (k : ℝ) * h < h := by rw [hh]; linarith
      have h2 : -h < (k : ℝ) * h := by rw [hh]; linarith
      have h3 : (k : ℝ) < 1 := by
        by_contra hc'
        rw [not_lt] at hc'
        nlinarith
      have h4 : (-1 : ℝ) < k := by
        by_contra hc'
        rw [not_lt] at hc'
        nlinarith
      have h5 : k < 1 := by exact_mod_cast h3
      have h6 : -1 < k := by exact_mod_cast h4
      omega
    rw [hk0] at hre him
    simp only [Int.cast_zero, zero_mul, add_zero, sub_eq_zero] at hre him
    have hm0 : m = 0 := by
      have h3 : (m : ℝ) < 1 := by linarith
      have h4 : (-1 : ℝ) < m := by linarith
      have h5 : m < 1 := by exact_mod_cast h3
      have h6 : -1 < m := by exact_mod_cast h4
      omega
    rw [hm0] at hre
    simp only [Int.cast_zero, sub_eq_zero] at hre
    exact Complex.ext hre him
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image hinj]
  have hterm : ∀ p ∈ T, torusResidue L f (φ p) = c * residue g p := by
    intro p _
    rw [hφ, torusResidue_mk ⟨hmer, hper⟩,
      show residue g p = c⁻¹ * residue f (c * p) from residue_comp_mul hc (hmer _)]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum0, mul_zero]

end Elliptic
end GroundTheory.Global
