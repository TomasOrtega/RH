import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

namespace GlobalTheory.CompanionTheory.KFin.EvenAniso

section Form

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {c : R →+* R} {h : V → V → R}

/- English proof (translation)
Rewrite using `[hH.symm z (x + y), hH.add_right, map_add, ← hH.symm z x, ← hH.symm z y]`.
-/
theorem add_left (hH : IsHerm c h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hH.symm z (x + y), hH.add_right, map_add, ← hH.symm z x, ← hH.symm z y]

/- English proof (translation)
Rewrite using `[hH.symm y (a • x), hH.smul_right, map_mul, ← hH.symm y x]`.
-/
theorem smul_left (hH : IsHerm c h) (a : R) (x y : V) : h (a • x) y = c a * h x y := by
  rw [hH.symm y (a • x), hH.smul_right, map_mul, ← hH.symm y x]

/- English proof (translation)
Rewrite using `[← zero_smul R (0 : V), smul_left hH, map_zero, zero_mul]`.
-/
theorem zero_left (hH : IsHerm c h) (y : V) : h 0 y = 0 := by
  rw [← zero_smul R (0 : V), smul_left hH, map_zero, zero_mul]

/- English proof (translation)
Rewrite using `[← zero_smul R (0 : V), hH.smul_right, zero_mul]`.
-/
theorem zero_right (hH : IsHerm c h) (x : V) : h x 0 = 0 := by
  rw [← zero_smul R (0 : V), hH.smul_right, zero_mul]

end Form

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Establish `hg : 1 < γ` using `not_le.mp hc`. Establish `hgg : 1 < γ * γ`. Combine the equalities or inequalities in the displayed calculation. Conclude with `absurd h (not_le.mpr hgg)`.
-/
theorem le_one_of_mul_self {γ : ℝ≥0} (h : γ * γ ≤ 1) : γ ≤ 1 := by
  by_contra hc
  have hg : 1 < γ := not_le.mp hc
  have hgg : 1 < γ * γ := by
    calc (1 : ℝ≥0) = 1 * 1 := (one_mul 1).symm
      _ < γ * γ := mul_lt_mul'' hg hg zero_le zero_le
  exact absurd h (not_le.mpr hgg)

/- English proof (translation)
Introduce `k R V _ _ _ _ _ c 𝔬 W hinv hcc hfix hck h𝔬 hWc hW0 hhen h hH hanis z w a b ha hb hzz hww`. Rewrite using `[h𝔬]`. Assume the negation of the conclusion as `hlt`. Establish `hs1 : 1 < W (h z w)` using `not_le.mp hlt`. Establish `hsym : ∀ x y : V, h y x = c (h x y)` using `hH.symm`.

Establish `hself : ∀ x : V, c (h x x) = h x x` using `fun x => (hH.symm x x).symm`. Establish `hWnorm : ∀ x : R, W (x * c x) = W x * W x` using `fun x => by rw [W.map_mul, hWc]`. Establish `hWtr : ∀ x : R, W x ≤ 1 → W (x + c x) ≤ 1` using `fun x hx => le_trans (W.map_add x (c x)) (max_le hx (by rw [hWc]; exact hx))`. Establish `hne : ∀ x : R, x ≠ 0 → W x ≠ 0` using `fun x hx h0 => hx (hW0 x h0)`. Establish `hnz : ∀ z w : V, 1 < W (h z w) → h z z ≠ 0 ∧ h w w ≠ 0`.

Introduce `z w hs`. Prove the components needed by the constructor for the conclusion. Introduce `h0`. Rewrite `hs` using `[hanis z h0, GlobalTheory.CompanionTheory.KFin.EvenAniso.zero_left hH, W.map_zero]`. Conclude with `absurd hs (not_lt.mpr zero_le)`.

Introduce `h0`. Rewrite `hs` using `[hanis w h0, GlobalTheory.CompanionTheory.KFin.EvenAniso.zero_right hH, W.map_zero]`. Conclude with `absurd hs (not_lt.mpr zero_le)`. Establish `core : ∀ (z w : V) (a b : R), W a ≤ 1 → W b ≤ 1 → h z z = a + c a → h w w = b + c b → 1 < W (h z w) → W (a * c a * h w w) < W (h z w * c (h z w) * h z z) → False`. Introduce `z w a b ha hb hzz hww hs hlt'`.

Take `⟨hA, hB⟩` from `hnz z w hs`. Establish `hs0 : W (h z w) ≠ 0` using `(lt_trans zero_lt_one hs).ne'`. Establish `hA0 : W (h z z) ≠ 0` using `hne _ hA`. Establish `hB0 : W (h w w) ≠ 0` using `hne _ hB`. Establish `ha0 : W a ≠ 0`.

Introduce `h0`. Apply `hA` to reduce the goal to its premises. Rewrite using `[hzz, hW0 a h0, map_zero, add_zero]`. Establish `hD : h z w * c (h z w) * h z z ≠ 0`. Introduce `h0`.

Establish `h0'` using `congrArg W h0`. Rewrite `h0'` using `[W.map_zero, W.map_mul, hWnorm]`. Conclude with `mul_ne_zero (mul_ne_zero hs0 hs0) hA0 h0'`. Take `⟨Dinv, hDinv⟩` from `hinv _ hD`. Establish `hcD : c (h z w * c (h z w) * h z z) = h z w * c (h z w) * h z z`.

Rewrite using `[map_mul, map_mul, hcc, hself z]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcDinv : c Dinv = Dinv`. Establish `h1 : (h z w * c (h z w) * h z z) * c Dinv = 1`. Rewrite using `[← hcD, ← map_mul, hDinv, map_one]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hce : c (a * c a * h w w * Dinv) = a * c a * h w w * Dinv`. Rewrite using `[map_mul, map_mul, map_mul, hcc, hself w, hcDinv]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨e', he'⟩` from `hfix _ hce`.

Establish `hWDD : W (h z w * c (h z w) * h z z) * W Dinv = 1`. Rewrite using `[← W.map_mul, hDinv, W.map_one]`. Establish `hWDinv : 0 < W Dinv`. Break down `(zero_le : (0 : ℝ≥0) ≤ W Dinv).lt_or_eq with h0 | h0` into its components or cases. Conclude with `h0`.

Rewrite `hWDD` using `[← h0, mul_zero]`. Conclude with `absurd hWDD zero_ne_one`. Establish `hWe : W (algebraMap k R e') < 1`. Rewrite using `[he', W.map_mul, ← hWDD]`. Conclude with `mul_lt_mul_of_pos_right hlt' hWDinv`.

Take `⟨m, hm⟩` from `hhen e' hWe`. Establish `hM' : algebraMap k R m * algebraMap k R m + algebraMap k R m + a * c a * h w w * Dinv = 0`. Establish `hm'` using `congrArg (algebraMap k R) hm`. Rewrite `hm'` using `[map_add, map_add, map_mul, map_zero, he']`. Conclude with `hm'`.

Establish `hcM' : c (algebraMap k R m) = algebraMap k R m` using `hck m`. Take `⟨M, hMdef⟩ : ∃ M, algebraMap k R m = M` from `⟨_, rfl⟩`. Rewrite `hM'`, `hcM'` using `[hMdef]`. Establish `hkey : (M * M + M) * (h z w * c (h z w) * h z z) + a * c a * h w w = 0`. Take the linear combination `(h z w * c (h z w) * h z z) * hM' - (a * c a * h w w) * hDinv`.

Establish `hv : h ((c a * h w w) • z + (h z z * M * c (h z w)) • w) ((c a * h w w) • z + (h z z * M * c (h z w)) • w) = 0`. Simplify using `only [GlobalTheory.CompanionTheory.KFin.EvenAniso.add_left hH, hH.add_right, GlobalTheory.CompanionTheory.KFin.EvenAniso.smul_left hH, hH.smul_right, map_mul, hcc, hself, hcM']`. Rewrite using `[hsym z w]`. Take the linear combination `(h z z * h w w) * hkey - (h z z * h w w * M * h z w * c (h z w)) * hzz`. Establish `hv0` using `hanis _ hv`.

Establish `e1 : h ((c a * h w w) • z + (h z z * M * c (h z w)) • w) w = 0`. Rewrite using `[hv0, GlobalTheory.CompanionTheory.KFin.EvenAniso.zero_left hH]`. Establish `e2 : h ((c a * h w w) • z + (h z z * M * c (h z w)) • w) z = 0`. Rewrite using `[hv0, GlobalTheory.CompanionTheory.KFin.EvenAniso.zero_left hH]`. Simplify using `only [GlobalTheory.CompanionTheory.KFin.EvenAniso.add_left hH, GlobalTheory.CompanionTheory.KFin.EvenAniso.smul_left hH, map_mul, hcc, hself, hcM'] at e1 e2`.

Rewrite `e2` using `[hsym z w]`. Establish `hfac1 : h w w * h z w * (a + h z z * M) = 0` using `by linear_combination e1`. Establish `hfac2 : h z z * (a * h w w + M * (h z w * c (h z w))) = 0` using `by linear_combination e2`. Establish `f1 : a + h z z * M = 0`. Apply `hW0` to reduce the goal to its premises.

Establish `h0'` using `congrArg W hfac1`. Rewrite `h0'` using `[W.map_zero, W.map_mul, W.map_mul]`. Conclude with `(mul_eq_zero.mp h0').resolve_left (mul_ne_zero hB0 hs0)`. Establish `f2 : a * h w w + M * (h z w * c (h z w)) = 0`. Apply `hW0` to reduce the goal to its premises.

Establish `h0'` using `congrArg W hfac2`. Rewrite `h0'` using `[W.map_zero, W.map_mul]`. Conclude with `(mul_eq_zero.mp h0').resolve_left hA0`. Establish `g1 : W a = W (h z z) * W M`. Rewrite using `[eq_neg_of_add_eq_zero_left f1, W.map_neg, W.map_mul]`.

Establish `g2 : W a * W (h w w) = W M * (W (h z w) * W (h z w))`. Rewrite using `[← W.map_mul a (h w w), eq_neg_of_add_eq_zero_left f2, W.map_neg, W.map_mul, hWnorm]`. Establish `hM0 : W M ≠ 0` using `fun h0 => ha0 (by rw [g1, h0, mul_zero])`. Establish `g3 : W (h z w) * W (h z w) = W (h z z) * W (h w w)`. Apply `mul_left_cancel₀ hM0` to reduce the goal to its premises.

Rewrite using `[← g2, g1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hAle : W (h z z) ≤ 1` using `by rw [hzz]; exact hWtr a ha`. Establish `hBle : W (h w w) ≤ 1` using `by rw [hww]; exact hWtr b hb`. Establish `hss : W (h z w) * W (h z w) ≤ 1`.

Rewrite using `[g3]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `absurd hs (not_lt.mpr (GlobalTheory.CompanionTheory.KFin.EvenAniso.le_one_of_mul_self hss))`. Establish `ha1 : W a ≤ 1` using `(h𝔬 a).mp ha`. Establish `hb1 : W b ≤ 1` using `(h𝔬 b).mp hb`.

Break down `lt_or_ge (W (a * c a * h w w)) (W (h z w * c (h z w) * h z z)) with hc1 | hc1` into its components or cases. Conclude with `core z w a b ha1 hb1 hzz hww hs1 hc1`. Establish `hs2 : 1 < W (h w z)` using `by rw [hsym z w, hWc]; exact hs1`. Break down `lt_or_ge (W (b * c b * h z z)) (W (h w z * c (h w z) * h w w)) with hc2 | hc2` into its components or cases. Conclude with `core w z b a hb1 ha1 hww hzz hs2 hc2`.

Take `⟨hA, hB⟩` from `hnz z w hs1`. Establish `hA0 : W (h z z) ≠ 0` using `hne _ hA`. Establish `hB0 : W (h w w) ≠ 0` using `hne _ hB`. Rewrite `hc2` using `[hsym z w]`. Simplify using `only [W.map_mul, hWc] at hc1 hc2`.

Establish `hm1 : ∀ x y : ℝ≥0, x ≤ 1 → y ≤ 1 → x * y ≤ 1` using `fun x y hx hy => by`. Combine the equalities or inequalities in the displayed calculation. Establish `hprod` using `mul_le_mul hc1 hc2 zero_le zero_le`. Establish `hAB : 0 < W (h z z) * W (h w w)` using `pos_iff_ne_zero.mpr (mul_ne_zero hA0 hB0)`. Establish `h4 : W (h z w) * W (h z w) * (W (h z w) * W (h z w)) ≤ W a * W a * (W b * W b)`.

Use `le_of_mul_le_mul_right ?_ hAB` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `h5` using `le_trans h4 (hm1 _ _ (hm1 _ _ ha1 ha1) (hm1 _ _ hb1 hb1))`. Establish `h6` using `GlobalTheory.CompanionTheory.KFin.EvenAniso.le_one_of_mul_self (GlobalTheory.CompanionTheory.KFin.EvenAniso.le_one_of_mul_self h5)`. Conclude with `absurd hs1 (not_lt.mpr h6)`.
-/
theorem pair_mem_of_even : ∀ {k R V : Type} [Field k] [CommRing R] [Algebra k R] [AddCommGroup V] [Module R V] (c : R →+* R) (𝔬 : Subring R) (W : Valuation R ℝ≥0), (∀ a : R, a ≠ 0 → ∃ b : R, a * b = 1) → (∀ a, c (c a) = a) → (∀ a, c a = a → ∃ x : k, algebraMap k R x = a) → (∀ x : k, c (algebraMap k R x) = algebraMap k R x) → (∀ a, a ∈ 𝔬 ↔ W a ≤ 1) → (∀ a, W (c a) = W a) → (∀ a, W a = 0 → a = 0) → (∀ e : k, W (algebraMap k R e) < 1 → ∃ u : k, u * u + u + e = 0) → ∀ h : V → V → R, IsHerm c h → (∀ z, h z z = 0 → z = 0) → ∀ (z w : V) (a b : R), a ∈ 𝔬 → b ∈ 𝔬 → h z z = a + c a → h w w = b + c b → h z w ∈ 𝔬 := by
  intro k R V _ _ _ _ _ c 𝔬 W hinv hcc hfix hck h𝔬 hWc hW0 hhen h hH hanis z w a b ha hb hzz hww
  rw [h𝔬]
  by_contra hlt
  have hs1 : 1 < W (h z w) := not_le.mp hlt
  have hsym : ∀ x y : V, h y x = c (h x y) := hH.symm
  have hself : ∀ x : V, c (h x x) = h x x := fun x => (hH.symm x x).symm
  have hWnorm : ∀ x : R, W (x * c x) = W x * W x := fun x => by rw [W.map_mul, hWc]
  have hWtr : ∀ x : R, W x ≤ 1 → W (x + c x) ≤ 1 := fun x hx =>
    le_trans (W.map_add x (c x)) (max_le hx (by rw [hWc]; exact hx))
  have hne : ∀ x : R, x ≠ 0 → W x ≠ 0 := fun x hx h0 => hx (hW0 x h0)
  have hnz : ∀ z w : V, 1 < W (h z w) → h z z ≠ 0 ∧ h w w ≠ 0 := by
    intro z w hs
    constructor
    · intro h0
      rw [hanis z h0, GlobalTheory.CompanionTheory.KFin.EvenAniso.zero_left hH, W.map_zero] at hs
      exact absurd hs (not_lt.mpr zero_le)
    · intro h0
      rw [hanis w h0, GlobalTheory.CompanionTheory.KFin.EvenAniso.zero_right hH, W.map_zero] at hs
      exact absurd hs (not_lt.mpr zero_le)
  have core : ∀ (z w : V) (a b : R), W a ≤ 1 → W b ≤ 1 → h z z = a + c a → h w w = b + c b →
      1 < W (h z w) →
      W (a * c a * h w w) < W (h z w * c (h z w) * h z z) → False := by
    intro z w a b ha hb hzz hww hs hlt'
    obtain ⟨hA, hB⟩ := hnz z w hs
    have hs0 : W (h z w) ≠ 0 := (lt_trans zero_lt_one hs).ne'
    have hA0 : W (h z z) ≠ 0 := hne _ hA
    have hB0 : W (h w w) ≠ 0 := hne _ hB
    have ha0 : W a ≠ 0 := by
      intro h0
      apply hA
      rw [hzz, hW0 a h0, map_zero, add_zero]
    have hD : h z w * c (h z w) * h z z ≠ 0 := by
      intro h0
      have h0' := congrArg W h0
      rw [W.map_zero, W.map_mul, hWnorm] at h0'
      exact mul_ne_zero (mul_ne_zero hs0 hs0) hA0 h0'
    obtain ⟨Dinv, hDinv⟩ := hinv _ hD
    have hcD : c (h z w * c (h z w) * h z z) = h z w * c (h z w) * h z z := by
      rw [map_mul, map_mul, hcc, hself z]; ring
    have hcDinv : c Dinv = Dinv := by
      have h1 : (h z w * c (h z w) * h z z) * c Dinv = 1 := by
        rw [← hcD, ← map_mul, hDinv, map_one]
      calc c Dinv = c Dinv * ((h z w * c (h z w) * h z z) * Dinv) := by rw [hDinv, mul_one]
        _ = ((h z w * c (h z w) * h z z) * c Dinv) * Dinv := by ring
        _ = Dinv := by rw [h1, one_mul]
    have hce : c (a * c a * h w w * Dinv) = a * c a * h w w * Dinv := by
      rw [map_mul, map_mul, map_mul, hcc, hself w, hcDinv]; ring
    obtain ⟨e', he'⟩ := hfix _ hce
    have hWDD : W (h z w * c (h z w) * h z z) * W Dinv = 1 := by
      rw [← W.map_mul, hDinv, W.map_one]
    have hWDinv : 0 < W Dinv := by
      rcases (zero_le : (0 : ℝ≥0) ≤ W Dinv).lt_or_eq with h0 | h0
      · exact h0
      · rw [← h0, mul_zero] at hWDD
        exact absurd hWDD zero_ne_one
    have hWe : W (algebraMap k R e') < 1 := by
      rw [he', W.map_mul, ← hWDD]
      exact mul_lt_mul_of_pos_right hlt' hWDinv
    obtain ⟨m, hm⟩ := hhen e' hWe
    have hM' : algebraMap k R m * algebraMap k R m + algebraMap k R m + a * c a * h w w * Dinv = 0 := by
      have hm' := congrArg (algebraMap k R) hm
      rw [map_add, map_add, map_mul, map_zero, he'] at hm'
      exact hm'
    have hcM' : c (algebraMap k R m) = algebraMap k R m := hck m
    obtain ⟨M, hMdef⟩ : ∃ M, algebraMap k R m = M := ⟨_, rfl⟩
    rw [hMdef] at hM' hcM'
    have hkey : (M * M + M) * (h z w * c (h z w) * h z z) + a * c a * h w w = 0 := by
      linear_combination (h z w * c (h z w) * h z z) * hM' - (a * c a * h w w) * hDinv
    have hv : h ((c a * h w w) • z + (h z z * M * c (h z w)) • w)
        ((c a * h w w) • z + (h z z * M * c (h z w)) • w) = 0 := by
      simp only [GlobalTheory.CompanionTheory.KFin.EvenAniso.add_left hH, hH.add_right,
        GlobalTheory.CompanionTheory.KFin.EvenAniso.smul_left hH, hH.smul_right, map_mul, hcc, hself, hcM']
      rw [hsym z w]
      linear_combination (h z z * h w w) * hkey - (h z z * h w w * M * h z w * c (h z w)) * hzz
    have hv0 := hanis _ hv
    have e1 : h ((c a * h w w) • z + (h z z * M * c (h z w)) • w) w = 0 := by
      rw [hv0, GlobalTheory.CompanionTheory.KFin.EvenAniso.zero_left hH]
    have e2 : h ((c a * h w w) • z + (h z z * M * c (h z w)) • w) z = 0 := by
      rw [hv0, GlobalTheory.CompanionTheory.KFin.EvenAniso.zero_left hH]
    simp only [GlobalTheory.CompanionTheory.KFin.EvenAniso.add_left hH, GlobalTheory.CompanionTheory.KFin.EvenAniso.smul_left hH, map_mul,
      hcc, hself, hcM'] at e1 e2
    rw [hsym z w] at e2
    have hfac1 : h w w * h z w * (a + h z z * M) = 0 := by linear_combination e1
    have hfac2 : h z z * (a * h w w + M * (h z w * c (h z w))) = 0 := by linear_combination e2
    have f1 : a + h z z * M = 0 := by
      apply hW0
      have h0' := congrArg W hfac1
      rw [W.map_zero, W.map_mul, W.map_mul] at h0'
      exact (mul_eq_zero.mp h0').resolve_left (mul_ne_zero hB0 hs0)
    have f2 : a * h w w + M * (h z w * c (h z w)) = 0 := by
      apply hW0
      have h0' := congrArg W hfac2
      rw [W.map_zero, W.map_mul] at h0'
      exact (mul_eq_zero.mp h0').resolve_left hA0
    have g1 : W a = W (h z z) * W M := by
      rw [eq_neg_of_add_eq_zero_left f1, W.map_neg, W.map_mul]
    have g2 : W a * W (h w w) = W M * (W (h z w) * W (h z w)) := by
      rw [← W.map_mul a (h w w), eq_neg_of_add_eq_zero_left f2, W.map_neg, W.map_mul, hWnorm]
    have hM0 : W M ≠ 0 := fun h0 => ha0 (by rw [g1, h0, mul_zero])
    have g3 : W (h z w) * W (h z w) = W (h z z) * W (h w w) := by
      apply mul_left_cancel₀ hM0
      rw [← g2, g1]; ring
    have hAle : W (h z z) ≤ 1 := by rw [hzz]; exact hWtr a ha
    have hBle : W (h w w) ≤ 1 := by rw [hww]; exact hWtr b hb
    have hss : W (h z w) * W (h z w) ≤ 1 := by
      rw [g3]
      calc W (h z z) * W (h w w) ≤ 1 * 1 := mul_le_mul hAle hBle zero_le zero_le
        _ = 1 := one_mul 1
    exact absurd hs (not_lt.mpr (GlobalTheory.CompanionTheory.KFin.EvenAniso.le_one_of_mul_self hss))
  have ha1 : W a ≤ 1 := (h𝔬 a).mp ha
  have hb1 : W b ≤ 1 := (h𝔬 b).mp hb
  rcases lt_or_ge (W (a * c a * h w w)) (W (h z w * c (h z w) * h z z)) with hc1 | hc1
  · exact core z w a b ha1 hb1 hzz hww hs1 hc1
  have hs2 : 1 < W (h w z) := by rw [hsym z w, hWc]; exact hs1
  rcases lt_or_ge (W (b * c b * h z z)) (W (h w z * c (h w z) * h w w)) with hc2 | hc2
  · exact core w z b a hb1 ha1 hww hzz hs2 hc2
  obtain ⟨hA, hB⟩ := hnz z w hs1
  have hA0 : W (h z z) ≠ 0 := hne _ hA
  have hB0 : W (h w w) ≠ 0 := hne _ hB
  rw [hsym z w] at hc2
  simp only [W.map_mul, hWc] at hc1 hc2
  have hm1 : ∀ x y : ℝ≥0, x ≤ 1 → y ≤ 1 → x * y ≤ 1 := fun x y hx hy => by
    calc x * y ≤ 1 * 1 := mul_le_mul hx hy zero_le zero_le
      _ = 1 := one_mul 1
  have hprod := mul_le_mul hc1 hc2 zero_le zero_le
  have hAB : 0 < W (h z z) * W (h w w) := pos_iff_ne_zero.mpr (mul_ne_zero hA0 hB0)
  have h4 : W (h z w) * W (h z w) * (W (h z w) * W (h z w)) ≤ W a * W a * (W b * W b) := by
    refine le_of_mul_le_mul_right ?_ hAB
    calc W (h z w) * W (h z w) * (W (h z w) * W (h z w)) * (W (h z z) * W (h w w))
        = W (h z w) * W (h z w) * W (h z z) * (W (h z w) * W (h z w) * W (h w w)) := by ring
      _ ≤ W a * W a * W (h w w) * (W b * W b * W (h z z)) := hprod
      _ = W a * W a * (W b * W b) * (W (h z z) * W (h w w)) := by ring
  have h5 := le_trans h4 (hm1 _ _ (hm1 _ _ ha1 ha1) (hm1 _ _ hb1 hb1))
  have h6 := GlobalTheory.CompanionTheory.KFin.EvenAniso.le_one_of_mul_self (GlobalTheory.CompanionTheory.KFin.EvenAniso.le_one_of_mul_self h5)
  exact absurd hs1 (not_lt.mpr h6)

end GlobalTheory.CompanionTheory.KFin.EvenAniso
