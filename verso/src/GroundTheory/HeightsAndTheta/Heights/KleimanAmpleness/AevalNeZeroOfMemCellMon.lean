import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideBis
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerExtra
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideMore
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Pointwise
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver GeneratesOver chartRingOver cellMon)

noncomputable section

namespace RowLocCover

section Poly

variable {S : Type} [CommRing S] {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Introduce `m hm k`. Take `⟨m1, hm1, m2, hm2, rfl⟩` from `Finset.mem_add.mp (MvPolynomial.support_mul f g hm)`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]`.
-/
theorem isMultiHomog_mul' {f g : MRingOver S ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

/- English proof (translation)
Introduce `m hm k'`. Rewrite `hm` using `[X_pow_eq_monomial]`. Establish `hm'` using `MvPolynomial.support_monomial_subset hm`. Rewrite `hm'` using `[Finset.mem_singleton]`. Substitute `hm'` using the available equality.

Distinguish the cases in `h : k' = k`. Substitute `h` using the available equality. Simplify using `[Finsupp.single_apply]`. Establish `: ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩` using `fun j e => h (congrArg Sigma.fst e).symm`. Simplify using `[h]`.
-/
theorem isMultiHomog_X_pow [DecidableEq K] (k : K) (i : ι k) (n : ℕ) :
    IsMultiHomog (X ⟨k, i⟩ ^ n : MRingOver S ι) (Pi.single k n) := by
  classical
  intro m hm k'
  rw [X_pow_eq_monomial] at hm
  have hm' := MvPolynomial.support_monomial_subset hm
  rw [Finset.mem_singleton] at hm'
  subst hm'
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [h]

/- English proof (translation)
Take `⟨m, hm⟩` from `MvPolynomial.ne_zero_iff.mp ht`. Establish `hm' : m ∈ t.support` using `MvPolynomial.mem_support_iff.mpr hm`. Use function extensionality and compare the values at `k`. Rewrite using `[← ha m hm' k, hb m hm' k]`.
-/
theorem isMultiHomog_unique {t : MRingOver S ι} {a b : K → ℕ} (ha : IsMultiHomog t a) (hb : IsMultiHomog t b)
    (ht : t ≠ 0) : a = b := by
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp ht
  have hm' : m ∈ t.support := MvPolynomial.mem_support_iff.mpr hm
  funext k
  rw [← ha m hm' k, hb m hm' k]

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Unfold `cellMon at ht`. Proceed by induction on `ht using Submonoid.closure_induction with`. Consider the case `mem f hf`. Take `⟨k, i, hi, rfl⟩` from `hf`. Break down `hB k i hi with h | h` into its components or cases.

Conclude with `⟨1, 1, one_mem _, by rw [h, pow_one, mul_one]⟩`. Conclude with `⟨0, X ⟨k, i⟩, Submonoid.subset_closure ⟨k, i, h, rfl⟩, by rw [pow_zero, one_mul]⟩`. Consider the case `one => exact ⟨0, 1, one_mem _, by simp⟩`. Consider the case `mul f g _ _ hf hg`. Take `⟨s, t, ht, rfl⟩` from `hf`.

Take `⟨s', t', ht', rfl⟩` from `hg`. Conclude with `⟨s + s', t * t', mul_mem ht ht', by ring⟩`.
-/
theorem cellMon_split {B B' : ∀ k, Finset (ι k)} {p : Σ k, ι k}
    (hB : ∀ k (i : ι k), i ∈ B' k → (⟨k, i⟩ : Σ k, ι k) = p ∨ i ∈ B k) {t : MRingOver S ι}
    (ht : t ∈ cellMon S B') : ∃ s : ℕ, ∃ t' ∈ cellMon S B, t = X p ^ s * t' := by
  unfold cellMon at ht
  induction ht using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    rcases hB k i hi with h | h
    · exact ⟨1, 1, one_mem _, by rw [h, pow_one, mul_one]⟩
    · exact ⟨0, X ⟨k, i⟩, Submonoid.subset_closure ⟨k, i, h, rfl⟩, by rw [pow_zero, one_mul]⟩
  | one => exact ⟨0, 1, one_mem _, by simp⟩
  | mul f g _ _ hf hg =>
    obtain ⟨s, t, ht, rfl⟩ := hf
    obtain ⟨s', t', ht', rfl⟩ := hg
    exact ⟨s + s', t * t', mul_mem ht ht', by ring⟩

/- English proof (translation)
Unfold `cellMon at ht`. Proceed by induction on `ht using Submonoid.closure_induction with`. Consider the case `mem f hf`. Take `⟨k, i, -, rfl⟩` from `hf`. Conclude with `⟨Pi.single k 1, by simpa using isMultiHomog_X_pow (S := S) k i 1⟩`.

Consider the case `one`. Use `⟨0, fun m hm k => ?_⟩` and prove the remaining obligations. Establish `h1 : m ∈ (monomial 0 (1 : S) : MRingOver S ι).support` using `by rwa [← C_apply, C_1]`. Rewrite using `[Finset.mem_singleton.mp (support_monomial_subset h1)]`. Simplify using the standard rewrite rules.

Consider the case `mul f g _ _ hf hg`. Take `⟨a, ha⟩` from `hf`. Take `⟨b, hb⟩` from `hg`. Conclude with `⟨a + b, isMultiHomog_mul' ha hb⟩`.
-/
theorem cellMon_isMultiHomog [DecidableEq K] {B : ∀ k, Finset (ι k)} {t : MRingOver S ι}
    (ht : t ∈ cellMon S B) : ∃ a : K → ℕ, IsMultiHomog t a := by
  unfold cellMon at ht
  induction ht using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, -, rfl⟩ := hf
    exact ⟨Pi.single k 1, by simpa using isMultiHomog_X_pow (S := S) k i 1⟩
  | one =>
    refine ⟨0, fun m hm k => ?_⟩
    have h1 : m ∈ (monomial 0 (1 : S) : MRingOver S ι).support := by rwa [← C_apply, C_1]
    rw [Finset.mem_singleton.mp (support_monomial_subset h1)]
    simp
  | mul f g _ _ hf hg =>
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    exact ⟨a + b, isMultiHomog_mul' ha hb⟩

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Unfold `cellMon at ht`. Proceed by induction on `ht using Submonoid.closure_induction with`. Consider the case `mem f hf`. Take `⟨k, i, hi, rfl⟩` from `hf`. Rewrite using `[aeval_X]`.

Conclude with `hB k i hi`. Consider the case `one => rw [map_one]`. Conclude with `one_ne_zero`. Consider the case `mul f g _ _ hf hg => rw [map_mul]`. Conclude with `mul_ne_zero hf hg`.
-/
theorem aeval_ne_zero_of_mem_cellMon {Ω : Type} [Field Ω] [Algebra S Ω] {y : (Σ k, ι k) → Ω}
    {B : ∀ k, Finset (ι k)} (hB : CellMeets y B) {t : MRingOver S ι} (ht : t ∈ cellMon S B) : aeval y t ≠ 0 := by
  unfold cellMon at ht
  induction ht using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    rw [aeval_X]
    exact hB k i hi
  | one => rw [map_one]; exact one_ne_zero
  | mul f g _ _ hf hg => rw [map_mul]; exact mul_ne_zero hf hg

end Poly

section Sec

variable {S : Type} [CommRing S] {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [Algebra S Ω]

/- English proof (translation)
Unfold `cellSec at ha hb ⊢`. Use `split_ifs at ha hb ⊢ with h`. Establish `hab` using `Submodule.mul_mem_mul ha hb`. Rewrite `hab` using `[Submodule.span_mul_span]`. Use `Submodule.span_mono ?_ hab` and prove the remaining obligations.

Introduce and unpack `z ⟨u, ⟨g, t, c, ht, htc, hc, hg, rfl⟩, v, ⟨g', t', c', ht', htc', hc', hg', rfl⟩, rfl⟩`. Use `⟨g * g', t * t', c + c', mul_mem ht ht', isMultiHomog_mul' htc htc', fun k => ?_, ?_, ?_⟩` and prove the remaining obligations. Use `hc k` as an intermediate fact. Use `hc' k` as an intermediate fact. Simplify using `only [Pi.add_apply, Nat.cast_add]`.

Use linear arithmetic over natural numbers and integers. Use `isMultiHomog_mul' hg hg' using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Use `hc k` as an intermediate fact. Use `hc' k` as an intermediate fact.

Simplify using `only [Pi.add_apply, Nat.cast_add]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [map_mul]`. Rewrite using `[div_mul_div_comm]`. Rewrite `ha` using `[Submodule.mem_bot]`.

Rewrite using `[ha, zero_mul]`. Conclude with `Submodule.zero_mem _`.
-/
theorem cellSec_mul (y : (Σ k, ι k) → Ω) {γ δ : K → ℤ} {B : ∀ k, Finset (ι k)} {a b : Ω}
    (ha : a ∈ cellSec S y γ B) (hb : b ∈ cellSec S y δ B) : a * b ∈ cellSec S y (γ + δ) B := by
  unfold cellSec at ha hb ⊢
  split_ifs at ha hb ⊢ with h
  · have hab := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at hab
    refine Submodule.span_mono ?_ hab
    rintro z ⟨u, ⟨g, t, c, ht, htc, hc, hg, rfl⟩, v, ⟨g', t', c', ht', htc', hc', hg', rfl⟩, rfl⟩
    refine ⟨g * g', t * t', c + c', mul_mem ht ht', isMultiHomog_mul' htc htc', fun k => ?_, ?_, ?_⟩
    · have := hc k
      have := hc' k
      simp only [Pi.add_apply, Nat.cast_add]
      omega
    · convert isMultiHomog_mul' hg hg' using 1
      funext k
      have := hc k
      have := hc' k
      simp only [Pi.add_apply, Nat.cast_add]
      omega
    · simp only [map_mul]
      rw [div_mul_div_comm]
  · rw [Submodule.mem_bot] at ha
    rw [ha, zero_mul]
    exact Submodule.zero_mem _

/- English proof (translation)
Unfold `cellSec at hz`. Use `split_ifs at hz with hB'm`. Use `swap`. Rewrite `hz` using `[Submodule.mem_bot]`. Conclude with `⟨0, fun r' _ => by rw [hz, mul_zero]; exact Submodule.zero_mem _⟩`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨g, t, a, ht, hta, hγ, hg, rfl⟩` from `hz`. Establish `ht0` using `aeval_ne_zero_of_mem_cellMon hB'm ht`. Take `⟨s, t', ht', rfl⟩` from `cellMon_split hB' ht`.

Take `⟨a', ha'⟩` from `cellMon_isMultiHomog ht'`. Establish `hne : X ⟨k, i⟩ ^ s * t' ≠ 0` using `fun h => ht0 (by rw [h, map_zero])`. Establish `haa` using `isMultiHomog_unique hta (isMultiHomog_mul' (isMultiHomog_X_pow k i s) ha') hne`. Establish `ht'0` using `aeval_ne_zero_of_mem_cellMon hB ht'`. Use `⟨s, fun r' hr' => ?_⟩` and prove the remaining obligations.

Take `⟨d, rfl⟩ : ∃ d, r' = s + d` from `⟨r' - s, by omega⟩`. Unfold `cellSec`. Rewrite using `[if_pos hB]`. Use `Submodule.subset_span ⟨X ⟨k, i⟩ ^ d * g, t', a', ht', ha', fun k' => ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hγ k'`.

Establish `h2` using `congrFun haa k'`. Simplify using `only [Pi.add_apply] at h2 ⊢`. Distinguish the cases in `hk : k' = k`. Substitute `hk` using the available equality. Simplify using `only [Pi.single_eq_same] at h2 ⊢`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [Pi.single_eq_of_ne hk] at h2 ⊢`. Use linear arithmetic over natural numbers and integers. Use `isMultiHomog_mul' (isMultiHomog_X_pow k i d) hg using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k'`.

Establish `h1` using `hγ k'`. Establish `h2` using `congrFun haa k'`. Simplify using `only [Pi.add_apply] at h2 ⊢`. Distinguish the cases in `hk : k' = k`. Substitute `hk` using the available equality.

Simplify using `only [Pi.single_eq_same] at h2 ⊢`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Pi.single_eq_of_ne hk] at h2 ⊢`. Use linear arithmetic over natural numbers and integers. Simplify using `only [map_mul, map_pow, aeval_X]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => exact ⟨0, fun r' _ => by rw [mul_zero]; exact Submodule.zero_mem _⟩`. Consider the case `add u v _ _ hu hv`. Take `⟨r₁, h₁⟩` from `hu`.

Take `⟨r₂, h₂⟩` from `hv`. Conclude with `⟨max r₁ r₂, fun r' hr' => by`. Rewrite using `[mul_add]`. Conclude with `Submodule.add_mem _ (h₁ r' (le_of_max_le_left hr')) (h₂ r' (le_of_max_le_right hr'))⟩`. Consider the case `smul c u _ hu`.

Take `⟨r, h⟩` from `hu`. Conclude with `⟨r, fun r' hr' => by rw [mul_smul_comm]; exact Submodule.smul_mem _ c (h r' hr')⟩`.
-/
theorem cellSec_shift [DecidableEq K] (y : (Σ k, ι k) → Ω) (γ : K → ℤ) {B B' : ∀ k, Finset (ι k)} {k : K} {i : ι k}
    (hy : y ⟨k, i⟩ ≠ 0) (hB : CellMeets y B) (hB' : ∀ k' (i' : ι k'), i' ∈ B' k' → (⟨k', i'⟩ : Σ k, ι k) = ⟨k, i⟩ ∨ i' ∈ B k')
    {z : Ω} (hz : z ∈ cellSec S y γ B') :
    ∃ r : ℕ, ∀ r' : ℕ, r ≤ r' → y ⟨k, i⟩ ^ r' * z ∈ cellSec S y (γ + Pi.single k (r' : ℤ)) B := by
  unfold cellSec at hz
  split_ifs at hz with hB'm
  swap
  · rw [Submodule.mem_bot] at hz
    exact ⟨0, fun r' _ => by rw [hz, mul_zero]; exact Submodule.zero_mem _⟩
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g, t, a, ht, hta, hγ, hg, rfl⟩ := hz
    have ht0 := aeval_ne_zero_of_mem_cellMon hB'm ht
    obtain ⟨s, t', ht', rfl⟩ := cellMon_split hB' ht
    obtain ⟨a', ha'⟩ := cellMon_isMultiHomog ht'
    have hne : X ⟨k, i⟩ ^ s * t' ≠ 0 := fun h => ht0 (by rw [h, map_zero])
    have haa := isMultiHomog_unique hta (isMultiHomog_mul' (isMultiHomog_X_pow k i s) ha') hne
    have ht'0 := aeval_ne_zero_of_mem_cellMon hB ht'
    refine ⟨s, fun r' hr' => ?_⟩
    obtain ⟨d, rfl⟩ : ∃ d, r' = s + d := ⟨r' - s, by omega⟩
    unfold cellSec
    rw [if_pos hB]
    refine Submodule.subset_span ⟨X ⟨k, i⟩ ^ d * g, t', a', ht', ha', fun k' => ?_, ?_, ?_⟩
    · have h1 := hγ k'
      have h2 := congrFun haa k'
      simp only [Pi.add_apply] at h2 ⊢
      by_cases hk : k' = k
      · subst hk
        simp only [Pi.single_eq_same] at h2 ⊢
        omega
      · simp only [Pi.single_eq_of_ne hk] at h2 ⊢
        omega
    · convert isMultiHomog_mul' (isMultiHomog_X_pow k i d) hg using 1
      funext k'
      have h1 := hγ k'
      have h2 := congrFun haa k'
      simp only [Pi.add_apply] at h2 ⊢
      by_cases hk : k' = k
      · subst hk
        simp only [Pi.single_eq_same] at h2 ⊢
        omega
      · simp only [Pi.single_eq_of_ne hk] at h2 ⊢
        omega
    · simp only [map_mul, map_pow, aeval_X]
      field_simp
      ring
  | zero => exact ⟨0, fun r' _ => by rw [mul_zero]; exact Submodule.zero_mem _⟩
  | add u v _ _ hu hv =>
    obtain ⟨r₁, h₁⟩ := hu
    obtain ⟨r₂, h₂⟩ := hv
    exact ⟨max r₁ r₂, fun r' hr' => by
      rw [mul_add]
      exact Submodule.add_mem _ (h₁ r' (le_of_max_le_left hr')) (h₂ r' (le_of_max_le_right hr'))⟩
  | smul c u _ hu =>
    obtain ⟨r, h⟩ := hu
    exact ⟨r, fun r' hr' => by rw [mul_smul_comm]; exact Submodule.smul_mem _ c (h r' hr')⟩

end Sec

section Loc

variable {S : Type} [CommRing S] {X : Type} {Ω : Type} [Field Ω] [Algebra S Ω]

/- English proof (translation)
Use `eq_bot_iff.mpr (iSup_le fun n a ha => ?_)` and prove the remaining obligations. Rewrite `ha` using `[Submodule.mem_comap, h, Submodule.mem_bot, LinearMap.mulLeft_apply]`. Rewrite using `[Submodule.mem_bot]`. Conclude with `(mul_eq_zero.mp ha).resolve_left (pow_ne_zero _ hf)`.
-/
theorem cellLocSys_eq_bot (G : X → Submodule S Ω) {f : Ω} (hf : f ≠ 0) {I : X} (h : G I = ⊥) :
    cellLocSys G f I = ⊥ := by
  refine eq_bot_iff.mpr (iSup_le fun n a ha => ?_)
  rw [Submodule.mem_comap, h, Submodule.mem_bot, LinearMap.mulLeft_apply] at ha
  rw [Submodule.mem_bot]
  exact (mul_eq_zero.mp ha).resolve_left (pow_ne_zero _ hf)

/- English proof (translation)
The claim follows from `iSup_mono fun _ => Submodule.comap_mono h`.
-/
theorem cellLocSys_mono (G : X → Submodule S Ω) (f : Ω) {I I' : X} (h : G I ≤ G I') :
    cellLocSys G f I ≤ cellLocSys G f I' :=
  iSup_mono fun _ => Submodule.comap_mono h

/- English proof (translation)
Use `iSup_le fun n a ha => ?_` and prove the remaining obligations. Take `⟨m, hm⟩` from `h n a ha`. Conclude with `Submodule.mem_iSup_of_mem (ι := ℕ) (p := fun n => (G I).comap (LinearMap.mulLeft S (f ^ n))) m hm`.
-/
theorem cellLocSys_le_of (G : X → Submodule S Ω) (f : Ω) {I I' : X}
    (h : ∀ (n : ℕ) (a : Ω), f ^ n * a ∈ G I' → ∃ m : ℕ, f ^ m * a ∈ G I) :
    cellLocSys G f I' ≤ cellLocSys G f I := by
  refine iSup_le fun n a ha => ?_
  obtain ⟨m, hm⟩ := h n a ha
  exact Submodule.mem_iSup_of_mem (ι := ℕ) (p := fun n => (G I).comap (LinearMap.mulLeft S (f ^ n))) m hm

end Loc

section Cells

variable {S : Type} [CommRing S] {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω]

/- English proof (translation)
Unfold `cellSec`. Rewrite using `[if_pos hI']`. Use `split_ifs with hI`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `z ⟨g, t, a, ht, hta, hγ, hg, rfl⟩`.

Use `⟨g, t, a, ?_, hta, hγ, hg, rfl⟩` and prove the remaining obligations. Use `Submonoid.closure_mono ?_ ht` and prove the remaining obligations. Introduce and unpack `f ⟨k, i, hi, rfl⟩`. Conclude with `⟨k, i, h k hi, rfl⟩`. Conclude with `bot_le`.
-/
theorem cellSec_mono (y : (Σ k, ι k) → Ω) (γ : K → ℤ) {I I' : ∀ k, Finset (ι k)} (h : ∀ k, I k ⊆ I' k)
    (hI' : CellMeets y I') : cellSec S y γ I ≤ cellSec S y γ I' := by
  classical
  unfold cellSec
  rw [if_pos hI']
  split_ifs with hI
  · refine Submodule.span_mono ?_
    rintro z ⟨g, t, a, ht, hta, hγ, hg, rfl⟩
    refine ⟨g, t, a, ?_, hta, hγ, hg, rfl⟩
    refine Submonoid.closure_mono ?_ ht
    rintro f ⟨k, i, hi, rfl⟩
    exact ⟨k, i, h k hi, rfl⟩
  · exact bot_le

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Distinguish the cases in `hk : k' = k`. Substitute `hk` using the available equality. Rewrite `h` using `[Function.update_self, Finset.mem_insert]`. Break down `h with rfl | h` into its components or cases. Conclude with `Or.inl rfl`.

Conclude with `Or.inr h`. Rewrite `h` using `[Function.update_of_ne hk]`. Conclude with `Or.inr h`.
-/
theorem mem_update_insert {I : ∀ k, Finset (ι k)} {k : K} {i : ι k} {k' : K} {i' : ι k'}
    (h : i' ∈ Function.update I k (insert i (I k)) k') : (⟨k', i'⟩ : Σ k, ι k) = ⟨k, i⟩ ∨ i' ∈ I k' := by
  by_cases hk : k' = k
  · subst hk
    rw [Function.update_self, Finset.mem_insert] at h
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr h
  · rw [Function.update_of_ne hk] at h
    exact Or.inr h

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Distinguish the cases in `hk : k' = k`. Substitute `hk` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `Finset.subset_insert _ _`. Rewrite using `[Function.update_of_ne hk]`.
-/
theorem subset_update_insert (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) (k' : K) :
    I k' ⊆ Function.update I k (insert i (I k)) k' := by
  by_cases hk : k' = k
  · subst hk
    rw [Function.update_self]
    exact Finset.subset_insert _ _
  · rw [Function.update_of_ne hk]

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Unfold `baseCell`. Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `Finset.subset_union_left`.

Rewrite using `[Function.update_of_ne hk]`.
-/
theorem subset_baseCell (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (J : Finset (Fin (N + 1)))
    (I : ∀ k, Finset (ι k)) (k : K) : I k ⊆ baseCell k₀ e J I k := by
  unfold baseCell
  by_cases hk : k = k₀
  · subst hk; rw [Function.update_self]; exact Finset.subset_union_left
  · rw [Function.update_of_ne hk]

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Unfold `baseCell`. Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality. Rewrite using `[Function.update_self, Function.update_self]`. Conclude with `Finset.union_subset_union (hI k) subset_rfl`.

Rewrite using `[Function.update_of_ne hk, Function.update_of_ne hk]`. Conclude with `hI k`.
-/
theorem baseCell_mono (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (J : Finset (Fin (N + 1)))
    {I I' : ∀ k, Finset (ι k)} (hI : ∀ k, I k ⊆ I' k) (k : K) :
    baseCell k₀ e J I k ⊆ baseCell k₀ e J I' k := by
  unfold baseCell
  by_cases hk : k = k₀
  · subst hk; rw [Function.update_self, Function.update_self]
    exact Finset.union_subset_union (hI k) subset_rfl
  · rw [Function.update_of_ne hk, Function.update_of_ne hk]; exact hI k

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Introduce `k i hi`. Unfold `baseCell at hi`. Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality. Rewrite `hi` using `[Function.update_self, Finset.mem_union]`.

Break down `hi with hi | hi` into its components or cases. Conclude with `hI k i hi`. Take `⟨j, hj, rfl⟩` from `Finset.mem_map.mp hi`. Conclude with `(Kleiman.mem_support _).mp (J.2.2 hj)`. Rewrite `hi` using `[Function.update_of_ne hk]`.

Conclude with `hI k i hi`.
-/
theorem cellMeets_baseCell (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1))
    (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) {I : ∀ k, Finset (ι k)} (hI : CellMeets y I) :
    CellMeets y (baseCell k₀ e J.1 I) := by
  intro k i hi
  unfold baseCell at hi
  by_cases hk : k = k₀
  · subst hk
    rw [Function.update_self, Finset.mem_union] at hi
    rcases hi with hi | hi
    · exact hI k i hi
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      exact (Kleiman.mem_support _).mp (J.2.2 hj)
  · rw [Function.update_of_ne hk] at hi; exact hI k i hi

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Unfold `baseCell at h ⊢`. Distinguish the cases in `h0 : k' = k₀`. Substitute `h0` using the available equality. Rewrite `h` using `[Function.update_self, Finset.mem_union]`. Rewrite using `[Function.update_self, Finset.mem_union]`.

Break down `h with h | h` into its components or cases. Break down `mem_update_insert h with h | h` into its components or cases. Conclude with `Or.inl h`. Conclude with `Or.inr (Or.inl h)`. Conclude with `Or.inr (Or.inr h)`.

Rewrite `h` using `[Function.update_of_ne h0]`. Rewrite using `[Function.update_of_ne h0]`. Conclude with `mem_update_insert h`.
-/
theorem mem_baseCell_update (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (J : Finset (Fin (N + 1)))
    (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) {k' : K} {i' : ι k'}
    (h : i' ∈ baseCell k₀ e J (Function.update I k (insert i (I k))) k') :
    (⟨k', i'⟩ : Σ k, ι k) = ⟨k, i⟩ ∨ i' ∈ baseCell k₀ e J I k' := by
  unfold baseCell at h ⊢
  by_cases h0 : k' = k₀
  · subst h0
    rw [Function.update_self, Finset.mem_union] at h
    rw [Function.update_self, Finset.mem_union]
    rcases h with h | h
    · rcases mem_update_insert h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rw [Function.update_of_ne h0] at h
    rw [Function.update_of_ne h0]
    exact mem_update_insert h

end Cells

section Model

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω] [Algebra F Ω]

/- English proof (translation)
Simplify using `only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply]`. Introduce `c _`. Simplify using `only [Pi.zero_apply, neg_zero, zpow_zero, Finset.prod_const_one, mul_one]`. Conclude with `Subalgebra.one_mem _`.
-/
theorem one_mem_secOver (y : (Σ k, ι k) → Ω) : (1 : Ω) ∈ secOver F y 0 := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply]
  intro c _
  simp only [Pi.zero_apply, neg_zero, zpow_zero, Finset.prod_const_one, mul_one]
  exact Subalgebra.one_mem _

/- English proof (translation)
Rewrite using `[Fintype.prod_eq_single k fun k' hk => by rw [Pi.single_eq_of_ne hk]; simp]`. Rewrite using `[Pi.single_eq_same, zpow_neg_one]`.
-/
theorem prod_zpow_single [DecidableEq K] (k : K) (v : K → Ω) :
    ∏ k', v k' ^ (-(Pi.single k (1 : ℤ) : K → ℤ) k') = (v k)⁻¹ := by
  rw [Fintype.prod_eq_single k fun k' hk => by rw [Pi.single_eq_of_ne hk]; simp]
  rw [Pi.single_eq_same, zpow_neg_one]

/- English proof (translation)
Simplify using `only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply, Subalgebra.mem_toSubmodule]`. Introduce `c _`. Rewrite using `[prod_zpow_single k (fun k' => y ⟨k', c k'⟩), ← div_eq_mul_inv]`. Conclude with `Algebra.subset_adjoin ⟨⟨k, i⟩, rfl⟩`.
-/
theorem coord_mem_secOver [DecidableEq K] (y : (Σ k, ι k) → Ω) (k : K) (i : ι k) :
    y ⟨k, i⟩ ∈ secOver F y (Pi.single k 1) := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  intro c _
  rw [prod_zpow_single k (fun k' => y ⟨k', c k'⟩), ← div_eq_mul_inv]
  exact Algebra.subset_adjoin ⟨⟨k, i⟩, rfl⟩

variable [LinearOrder K] [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω} {k₀ : K} {N : ℕ} (e : ι k₀ ≃ Fin (N + 1))

omit [LinearOrder K] in

/- English proof (translation)
Establish `hG : GeneratesOver F y (0 : K → ℤ) (fun _ : Fin 1 => (1 : Ω))`. Introduce `c _`. Use `⟨fun _ => 1, fun _ => Subalgebra.one_mem _, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `h` using `(hGen F K ι Ω y k₀ N e hM 0 1 (fun _ => 1) (fun _ => one_mem_secOver y)).mp hG J`.

Rewrite `hz` using `[← h, SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun]`. Take `⟨c, rfl⟩` from `hz`. Use `Subalgebra.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Subalgebra.smul_def, smul_eq_mul, mul_one]`. Conclude with `(c j).2`.
-/
theorem chartSecOver_zero_subset [DecidableEq K] (hGen : ChartSecGen.Statement)
    (hM : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀) (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) {z : Ω}
    (hz : z ∈ chartSecOver F y k₀ e 0 J) : z ∈ Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J := by
  have hG : GeneratesOver F y (0 : K → ℤ) (fun _ : Fin 1 => (1 : Ω)) := by
    intro c _
    refine ⟨fun _ => 1, fun _ => Subalgebra.one_mem _, ?_⟩
    simp
  have h := (hGen F K ι Ω y k₀ N e hM 0 1 (fun _ => 1) (fun _ => one_mem_secOver y)).mp hG J
  rw [← h, SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun] at hz
  obtain ⟨c, rfl⟩ := hz
  refine Subalgebra.sum_mem _ fun j _ => ?_
  rw [Subalgebra.smul_def, smul_eq_mul, mul_one]
  exact (c j).2

omit [LinearOrder K] in

/- English proof (translation)
Establish `h1 : (1 : Ω) ∈ chartSecOver F y k₀ e 0 J` using `mem_chartSecOver_of_mem F y k₀ e 0 J (one_mem_secOver y)`. Establish `hsub : ∀ δ : K → ℤ, ((Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J) (chartSecOver F y k₀ e δ J) : Set Ω)) = chartSecOver F y k₀ e δ J`. Introduce `δ`. Use `Set.Subset.antisymm (fun z hz => ?_) Submodule.subset_span` and prove the remaining obligations. Establish `h` using `hMul F K ι Ω y k₀ N e hM 0 δ J`.

Rewrite `h` using `[zero_add]`. Rewrite using `[← h]`. Establish `hs : chartSecOver F y k₀ e δ J ⊆ chartSecOver F y k₀ e 0 J * chartSecOver F y k₀ e δ J` using `fun z hz => ⟨1, h1, z, hz, one_mul z⟩`. Conclude with `Submodule.span_mono hs hz`. Set `M'` to `Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J) (chartSecOver F y k₀ e (-Pi.single k 1) J)`.

Set `T : Submodule (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J) Ω` to `{ carrier := {z | ∃ w : ι k → Ω, (∀ i, w i ∈ M') ∧ ∑ i, w i * y ⟨k, i⟩ = z} add_mem' := by`. Introduce and unpack `_ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩`. Conclude with `⟨w + w', fun i => M'.add_mem (hw i) (hw' i), by simp [add_mul, Finset.sum_add_distrib]⟩`. Use the proof step `zero_mem' := ⟨0, fun _ => M'.zero_mem, by simp⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `r _ ⟨w, hw, rfl⟩`. Conclude with `⟨r • w, fun i => M'.smul_mem r (hw i), by simp [Finset.smul_sum]⟩ }`. Set `σ` to `Fintype.equivFin (ι k)`. Establish `hgen : GeneratesOver F y (Pi.single k 1) (fun j => y ⟨k, σ.symm j⟩)`. Introduce `c hc`.

Use `⟨fun j => if j = σ (c k) then 1 else 0, fun j => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only split_ifs`. Conclude with `Subalgebra.one_mem _`. Conclude with `Subalgebra.zero_mem _`. Simplify using `only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Equiv.symm_apply_apply]`.

Rewrite using `[prod_zpow_single k (fun k' => y ⟨k', c k'⟩)]`. Conclude with `mul_inv_cancel₀ (hc k)`. Establish `hspan` using `(hGen F K ι Ω y k₀ N e hM (Pi.single k 1) _ (fun j => y ⟨k, σ.symm j⟩) (fun j => coord_mem_secOver y k _)).mp hgen J`. Establish `hone : (1 : Ω) ∈ Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J) (chartSecOver F y k₀ e (-Pi.single k 1) J * chartSecOver F y k₀ e (Pi.single k 1) J)`. Establish `h` using `hMul F K ι Ω y k₀ N e hM (-Pi.single k 1) (Pi.single k 1) J`.

Rewrite `h` using `[neg_add_cancel]`. Rewrite using `[← SetLike.mem_coe, h]`. Conclude with `h1`. Establish `hle : Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J) (chartSecOver F y k₀ e (-Pi.single k 1) J * chartSecOver F y k₀ e (Pi.single k 1) J) ≤ T`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨p, hp, q, hq, rfl⟩`. Rewrite `hq` using `[← hspan, SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun]`. Take `⟨c, rfl⟩` from `hq`. Use `⟨fun i => c (σ i) • p, fun i => M'.smul_mem _ (Submodule.subset_span hp), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Take `⟨w, hw, hsum⟩` from `hle hone`. Conclude with `⟨w, fun i => by rw [← hsub]; exact hw i, hsum⟩`.
-/
theorem exists_sum_eq_one [DecidableEq K] (hGen : ChartSecGen.Statement) (hMul : ChartSecMul.Statement)
    (hM : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀) (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (k : K) :
    ∃ w : ι k → Ω, (∀ i, w i ∈ chartSecOver F y k₀ e (-Pi.single k 1) J) ∧ ∑ i, w i * y ⟨k, i⟩ = 1 := by
  have h1 : (1 : Ω) ∈ chartSecOver F y k₀ e 0 J := mem_chartSecOver_of_mem F y k₀ e 0 J (one_mem_secOver y)
  have hsub : ∀ δ : K → ℤ, ((Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J)
      (chartSecOver F y k₀ e δ J) : Set Ω)) = chartSecOver F y k₀ e δ J := by
    intro δ
    refine Set.Subset.antisymm (fun z hz => ?_) Submodule.subset_span
    have h := hMul F K ι Ω y k₀ N e hM 0 δ J
    rw [zero_add] at h
    rw [← h]
    have hs : chartSecOver F y k₀ e δ J ⊆ chartSecOver F y k₀ e 0 J * chartSecOver F y k₀ e δ J :=
      fun z hz => ⟨1, h1, z, hz, one_mul z⟩
    exact Submodule.span_mono hs hz
  let M' := Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J)
    (chartSecOver F y k₀ e (-Pi.single k 1) J)
  let T : Submodule (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J) Ω :=
    { carrier := {z | ∃ w : ι k → Ω, (∀ i, w i ∈ M') ∧ ∑ i, w i * y ⟨k, i⟩ = z}
      add_mem' := by
        rintro _ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
        exact ⟨w + w', fun i => M'.add_mem (hw i) (hw' i), by simp [add_mul, Finset.sum_add_distrib]⟩
      zero_mem' := ⟨0, fun _ => M'.zero_mem, by simp⟩
      smul_mem' := by
        rintro r _ ⟨w, hw, rfl⟩
        exact ⟨r • w, fun i => M'.smul_mem r (hw i), by simp [Finset.smul_sum]⟩ }
  let σ := Fintype.equivFin (ι k)
  have hgen : GeneratesOver F y (Pi.single k 1) (fun j => y ⟨k, σ.symm j⟩) := by
    intro c hc
    refine ⟨fun j => if j = σ (c k) then 1 else 0, fun j => ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _
    · simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Equiv.symm_apply_apply]
      rw [prod_zpow_single k (fun k' => y ⟨k', c k'⟩)]
      exact mul_inv_cancel₀ (hc k)
  have hspan := (hGen F K ι Ω y k₀ N e hM (Pi.single k 1) _ (fun j => y ⟨k, σ.symm j⟩)
    (fun j => coord_mem_secOver y k _)).mp hgen J
  have hone : (1 : Ω) ∈ Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J)
      (chartSecOver F y k₀ e (-Pi.single k 1) J * chartSecOver F y k₀ e (Pi.single k 1) J) := by
    have h := hMul F K ι Ω y k₀ N e hM (-Pi.single k 1) (Pi.single k 1) J
    rw [neg_add_cancel] at h
    rw [← SetLike.mem_coe, h]
    exact h1
  have hle : Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J)
      (chartSecOver F y k₀ e (-Pi.single k 1) J * chartSecOver F y k₀ e (Pi.single k 1) J) ≤ T := by
    rw [Submodule.span_le]
    rintro _ ⟨p, hp, q, hq, rfl⟩
    rw [← hspan, SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun] at hq
    obtain ⟨c, rfl⟩ := hq
    refine ⟨fun i => c (σ i) • p, fun i => M'.smul_mem _ (Submodule.subset_span hp), ?_⟩
    calc ∑ i, (c (σ i) • p) * y ⟨k, i⟩ = ∑ i, p * (c (σ i) • y ⟨k, σ.symm (σ i)⟩) :=
          Finset.sum_congr rfl fun i _ => by simp only [Equiv.symm_apply_apply, smul_mul_assoc, mul_smul_comm]
      _ = ∑ j, p * (c j • y ⟨k, σ.symm j⟩) := Equiv.sum_comp σ (fun j => p * (c j • y ⟨k, σ.symm j⟩))
      _ = p * ∑ j, c j • y ⟨k, σ.symm j⟩ := (Finset.mul_sum _ _ _).symm
  obtain ⟨w, hw, hsum⟩ := hle hone
  exact ⟨w, fun i => by rw [← hsub]; exact hw i, hsum⟩

end Model

/- English proof (translation)
Introduce `F _ K _ _ ι _ _ Ω _ _ y k₀ N e hM γ J`. Use `choose w hw hsum using fun k => exists_sum_eq_one e hGen hMul hM J k`. Establish `h1 : (1 : Ω) ∈ chartSecOver F y k₀ e 0 J` using `mem_chartSecOver_of_mem F y k₀ e 0 J (one_mem_secOver y)`. Establish `hCmul : ∀ (δ₁ δ₂ : K → ℤ) (a b : Ω), a ∈ chartSecOver F y k₀ e δ₁ J → b ∈ chartSecOver F y k₀ e δ₂ J → a * b ∈ chartSecOver F y k₀ e (δ₁ + δ₂) J` using `fun δ₁ δ₂ a b ha hb => by`. Rewrite using `[← hMul F K ι Ω y k₀ N e hM δ₁ δ₂ J]`.

Conclude with `Submodule.subset_span ⟨a, ha, b, hb, rfl⟩`. Establish `hwy : ∀ k i, w k i * y ⟨k, i⟩ ∈ Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J` using `fun k i => by`. Use `chartSecOver_zero_subset e hGen hM J ?_` and prove the remaining obligations. Use `hCmul _ _ _ _ (hw k i) (mem_chartSecOver_of_mem F y k₀ e _ J (coord_mem_secOver y k i))` as an intermediate fact. Rewrite `this` using `[neg_add_cancel]`. Then use the resulting hypothesis.

Establish `hwpow : ∀ k i (r : ℕ), w k i ^ r ∈ chartSecOver F y k₀ e (Pi.single k (-(r : ℤ))) J`. Introduce `k i r`. Proceed by induction on `r with`. Consider the case `zero => simpa using h1`. Consider the case `succ r ih`.

Use `hCmul _ _ _ _ ih (hw k i)` as an intermediate fact. Rewrite using `[pow_succ]`. Use `this using 2` and compare the differences between its conclusion and the goal. Rewrite using `[← Pi.single_neg, ← Pi.single_add]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Set `fc : (∀ k, ι k) → Ω` to `fun c => ∏ k, w k (c k) * y ⟨k, c k⟩`. Establish `hfc_mem : ∀ c, fc c ∈ Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J` using `fun c => Subalgebra.prod_mem _ fun k _ => hwy k (c k)`. Establish `hfc_sum : ∑ c, fc c = 1`.

Combine the equalities or inequalities in the displayed calculation. Set `P` to `{c : ∀ k, ι k // fc c ≠ 0}`. Set `σ` to `(Fintype.equivFin P).symm`. Use `⟨Fintype.card P, fun l => fc (σ l).1, fun _ => 1, fun l => hfc_mem _, fun _ => Subalgebra.one_mem _, ?_, fun l => ?_⟩` and prove the remaining obligations. Simplify using `only [one_mul]`.

Rewrite using `[Equiv.sum_comp σ (fun p : P => fc p.1), ← Finset.sum_subtype (Finset.univ.filter fun c => fc c ≠ 0) (by simp) fc, Finset.sum_filter_ne_zero, hfc_sum]`. Simplify using `only`. Generalize the expression as in `σ l = p`. Take `⟨c, hc⟩` from `p`. Simplify using `only`.

Establish `hyc : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => right_ne_zero_of_mul (Finset.prod_ne_zero_iff.mp hc k (Finset.mem_univ k))`. Establish `hbot : ∀ I : ∀ k, Finset (ι k), ¬ CellMeets y I → cellSec F y γ (baseCell k₀ e J.1 I) = ⊥` using `fun I hI => by`. Unfold `cellSec`. Rewrite using `[if_neg fun h => hI fun k i hi => h k i (subset_baseCell k₀ e J.1 I k hi)]`. Use `⟨c, hyc, fun I _ hI => cellLocSys_eq_bot _ hc (hbot I hI), fun I I' _ hII' hI' => cellLocSys_mono _ _ (cellSec_mono y γ (baseCell_mono k₀ e J.1 hII') (cellMeets_baseCell y k₀ e J hI')), fun I hne k => ?_⟩` and prove the remaining obligations.

Establish `hsubI : ∀ k', I k' ⊆ Function.update I k (insert (c k) (I k)) k'` using `subset_update_insert I k (c k)`. Distinguish the cases in `hI : CellMeets y I`. Use `swap`. Establish `hI'n : ¬ CellMeets y (Function.update I k (insert (c k) (I k)))` using `fun h => hI fun k' i hi => h k' i (hsubI k' hi)`. Rewrite using `[cellLocSys_eq_bot (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) hc (hbot _ hI'n), cellLocSys_eq_bot (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) hc (hbot I hI)]`.

Establish `hI'm : CellMeets y (Function.update I k (insert (c k) (I k)))`. Introduce `k' i hi`. Break down `mem_update_insert hi with h | h` into its components or cases. Rewrite using `[h]`. Conclude with `hyc k`.

Conclude with `hI k' i h`. Use `le_antisymm (cellLocSys_le_of _ _ fun n a ha => ?_) (cellLocSys_mono _ _ (cellSec_mono y γ (baseCell_mono k₀ e J.1 hsubI) (cellMeets_baseCell y k₀ e J hI'm)))` and prove the remaining obligations. Take `⟨r, hr⟩` from `cellSec_shift y γ (hyc k) (cellMeets_baseCell y k₀ e J hI) (fun k' i' hi' => mem_baseCell_update k₀ e J.1 I k (c k) hi') ha`. Establish `hrest : ∏ k' ∈ Finset.univ.erase k, w k' (c k') * y ⟨k', c k'⟩ ∈ Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J` using `Subalgebra.prod_mem _ fun k' _ => hwy k' (c k')`. Establish `hfac : ∀ z : Ω, fc c ^ r * z = (∏ k' ∈ Finset.univ.erase k, w k' (c k') * y ⟨k', c k'⟩) ^ r * (w k (c k) ^ r * (y ⟨k, c k⟩ ^ r * z))` using `fun z => by`.

Simplify using `only [fc]`. Rewrite using `[← Finset.mul_prod_erase Finset.univ (fun k' => w k' (c k') * y ⟨k', c k'⟩) (Finset.mem_univ k)]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨r + n, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_add, mul_assoc, hfac]`.

Use `hAct F K ι Ω y k₀ N e γ J I _ _ (Subalgebra.pow_mem _ hrest r) ?_` and prove the remaining obligations. Establish `hw'` using `hSub F K ι Ω y k₀ N e _ J I hne hI (hwpow k (c k) r)`. Use `cellSec_mul y hw' (hr r le_rfl)` as an intermediate fact. Rewrite `this` using `[show Pi.single k (-(r : ℤ)) + (γ + Pi.single k (r : ℤ)) = γ by rw [Pi.single_neg]; abel]`. Then use the resulting hypothesis.
-/
theorem proof (hGen : ChartSecGen.Statement) (hMul : ChartSecMul.Statement) (hSub : RowSub.Statement)
    (hAct : RowChartAct.Statement) : RowLocCover.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y k₀ N e hM γ J
  classical
  choose w hw hsum using fun k => exists_sum_eq_one e hGen hMul hM J k
  have h1 : (1 : Ω) ∈ chartSecOver F y k₀ e 0 J := mem_chartSecOver_of_mem F y k₀ e 0 J (one_mem_secOver y)
  have hCmul : ∀ (δ₁ δ₂ : K → ℤ) (a b : Ω), a ∈ chartSecOver F y k₀ e δ₁ J → b ∈ chartSecOver F y k₀ e δ₂ J →
      a * b ∈ chartSecOver F y k₀ e (δ₁ + δ₂) J := fun δ₁ δ₂ a b ha hb => by
    rw [← hMul F K ι Ω y k₀ N e hM δ₁ δ₂ J]
    exact Submodule.subset_span ⟨a, ha, b, hb, rfl⟩
  have hwy : ∀ k i, w k i * y ⟨k, i⟩ ∈ Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J := fun k i => by
    refine chartSecOver_zero_subset e hGen hM J ?_
    have := hCmul _ _ _ _ (hw k i) (mem_chartSecOver_of_mem F y k₀ e _ J (coord_mem_secOver y k i))
    rwa [neg_add_cancel] at this
  have hwpow : ∀ k i (r : ℕ), w k i ^ r ∈ chartSecOver F y k₀ e (Pi.single k (-(r : ℤ))) J := by
    intro k i r
    induction r with
    | zero => simpa using h1
    | succ r ih =>
      have := hCmul _ _ _ _ ih (hw k i)
      rw [pow_succ]
      convert this using 2
      rw [← Pi.single_neg, ← Pi.single_add]
      congr 1
      push_cast
      ring
  let fc : (∀ k, ι k) → Ω := fun c => ∏ k, w k (c k) * y ⟨k, c k⟩
  have hfc_mem : ∀ c, fc c ∈ Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J :=
    fun c => Subalgebra.prod_mem _ fun k _ => hwy k (c k)
  have hfc_sum : ∑ c, fc c = 1 := by
    calc ∑ c, fc c = ∏ k, ∑ i, w k i * y ⟨k, i⟩ := by rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      _ = 1 := by simp [hsum]
  let P := {c : ∀ k, ι k // fc c ≠ 0}
  let σ := (Fintype.equivFin P).symm
  refine ⟨Fintype.card P, fun l => fc (σ l).1, fun _ => 1, fun l => hfc_mem _, fun _ => Subalgebra.one_mem _, ?_,
    fun l => ?_⟩
  · simp only [one_mul]
    rw [Equiv.sum_comp σ (fun p : P => fc p.1),
      ← Finset.sum_subtype (Finset.univ.filter fun c => fc c ≠ 0) (by simp) fc, Finset.sum_filter_ne_zero, hfc_sum]
  dsimp only
  generalize σ l = p
  obtain ⟨c, hc⟩ := p
  dsimp only
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k =>
    right_ne_zero_of_mul (Finset.prod_ne_zero_iff.mp hc k (Finset.mem_univ k))
  have hbot : ∀ I : ∀ k, Finset (ι k), ¬ CellMeets y I → cellSec F y γ (baseCell k₀ e J.1 I) = ⊥ := fun I hI => by
    unfold cellSec
    rw [if_neg fun h => hI fun k i hi => h k i (subset_baseCell k₀ e J.1 I k hi)]
  refine ⟨c, hyc, fun I _ hI => cellLocSys_eq_bot _ hc (hbot I hI), fun I I' _ hII' hI' =>
    cellLocSys_mono _ _ (cellSec_mono y γ (baseCell_mono k₀ e J.1 hII') (cellMeets_baseCell y k₀ e J hI')),
    fun I hne k => ?_⟩
  have hsubI : ∀ k', I k' ⊆ Function.update I k (insert (c k) (I k)) k' := subset_update_insert I k (c k)
  by_cases hI : CellMeets y I
  swap
  · have hI'n : ¬ CellMeets y (Function.update I k (insert (c k) (I k))) :=
      fun h => hI fun k' i hi => h k' i (hsubI k' hi)
    rw [cellLocSys_eq_bot (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) hc (hbot _ hI'n),
      cellLocSys_eq_bot (fun I => cellSec F y γ (baseCell k₀ e J.1 I)) hc (hbot I hI)]
  have hI'm : CellMeets y (Function.update I k (insert (c k) (I k))) := by
    intro k' i hi
    rcases mem_update_insert hi with h | h
    · rw [h]
      exact hyc k
    · exact hI k' i h
  refine le_antisymm (cellLocSys_le_of _ _ fun n a ha => ?_)
    (cellLocSys_mono _ _ (cellSec_mono y γ (baseCell_mono k₀ e J.1 hsubI) (cellMeets_baseCell y k₀ e J hI'm)))
  obtain ⟨r, hr⟩ := cellSec_shift y γ (hyc k) (cellMeets_baseCell y k₀ e J hI)
    (fun k' i' hi' => mem_baseCell_update k₀ e J.1 I k (c k) hi') ha
  have hrest : ∏ k' ∈ Finset.univ.erase k, w k' (c k') * y ⟨k', c k'⟩ ∈
      Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) J :=
    Subalgebra.prod_mem _ fun k' _ => hwy k' (c k')
  have hfac : ∀ z : Ω, fc c ^ r * z = (∏ k' ∈ Finset.univ.erase k, w k' (c k') * y ⟨k', c k'⟩) ^ r *
      (w k (c k) ^ r * (y ⟨k, c k⟩ ^ r * z)) := fun z => by
    simp only [fc]
    rw [← Finset.mul_prod_erase Finset.univ (fun k' => w k' (c k') * y ⟨k', c k'⟩) (Finset.mem_univ k)]
    ring
  refine ⟨r + n, ?_⟩
  rw [pow_add, mul_assoc, hfac]
  refine hAct F K ι Ω y k₀ N e γ J I _ _ (Subalgebra.pow_mem _ hrest r) ?_
  have hw' := hSub F K ι Ω y k₀ N e _ J I hne hI (hwpow k (c k) r)
  have := cellSec_mul y hw' (hr r le_rfl)
  rwa [show Pi.single k (-(r : ℤ)) + (γ + Pi.single k (r : ℤ)) = γ by rw [Pi.single_neg]; abel] at this

end RowLocCover

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
