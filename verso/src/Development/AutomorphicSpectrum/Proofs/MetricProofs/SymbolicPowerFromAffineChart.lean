import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AffineChartIdealPrimeAndSaturatedStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (cycBlockWt cyc_exists_blockComponent cyc_isHomogeneous_of_isMultiHomogIdeal)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def mdeg (m : (Σ k, ι k) →₀ ℕ) : K → ℕ := fun k => ∑ i, m ⟨k, i⟩

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[mdeg, Finset.sum_add_distrib]`.
-/
theorem mdeg_add (m n : (Σ k, ι k) →₀ ℕ) : mdeg (m + n) = mdeg m + mdeg n := by
  funext k
  simp [mdeg, Finset.sum_add_distrib]

open Classical in

def part (b : K → ℕ) (s : MvPolynomial (Σ k, ι k) ℂ) : MvPolynomial (Σ k, ι k) ℂ :=
  ∑ m ∈ s.support.filter (fun m => mdeg m = b), monomial m (coeff m s)

open Classical in
/- English proof (translation)
Unfold `part`. Rewrite using `[coeff_sum]`. Simplify using `only [coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`. Distinguish the cases in `h : mdeg m = b`.

Distinguish the cases in `hs : m ∈ s.support`. Simplify using `[h, hs]`. Establish `: coeff m s = 0` using `by simpa using hs`. Simplify using `[this]`. Simplify using `[h]`.
-/
theorem coeff_part (b : K → ℕ) (s : MvPolynomial (Σ k, ι k) ℂ) (m : (Σ k, ι k) →₀ ℕ) :
    coeff m (part b s) = if mdeg m = b then coeff m s else 0 := by
  unfold part
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h : mdeg m = b
  · by_cases hs : m ∈ s.support
    · simp [h, hs]
    · have : coeff m s = 0 := by simpa using hs
      simp [this]
  · simp [h]

open Classical in
/- English proof (translation)
Unfold `part`. Rewrite using `[Finset.sum_fiberwise_of_maps_to (fun m hm => Finset.mem_image_of_mem _ hm)]`. Conclude with `s.support_sum_monomial_coeff`.
-/
theorem sum_part (s : MvPolynomial (Σ k, ι k) ℂ) :
    ∑ b ∈ s.support.image mdeg, part b s = s := by
  unfold part
  rw [Finset.sum_fiberwise_of_maps_to (fun m hm => Finset.mem_image_of_mem _ hm)]
  exact s.support_sum_monomial_coeff

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[mem_support_iff, coeff_part]`. Assume the negation of the conclusion as `hk`. Use `hm (if_neg fun h => hk ?_)` and prove the remaining obligations. Conclude with `congrFun h k`.
-/
theorem isMultiHomog_part (b : K → ℕ) (s : MvPolynomial (Σ k, ι k) ℂ) :
    IsMultiHomog (part b s) b := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_part] at hm
  by_contra hk
  refine hm (if_neg fun h => hk ?_)
  exact congrFun h k

/- English proof (translation)
Introduce `m hm k`. Take `⟨m₁, h₁, m₂, h₂, rfl⟩` from `Finset.mem_add.1 (support_mul s f hm)`. Use `congrFun (mdeg_add m₁ m₂) k` as an intermediate fact. Simplify using `only [mdeg, Pi.add_apply] at this`. Rewrite using `[this, hs m₁ h₁ k, hf m₂ h₂ k]`.

Both sides reduce to the same expression.
-/
theorem isMultiHomog_mul {s f : MvPolynomial (Σ k, ι k) ℂ} {b a : K → ℕ}
    (hs : IsMultiHomog s b) (hf : IsMultiHomog f a) : IsMultiHomog (s * f) (b + a) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (support_mul s f hm)
  have := congrFun (mdeg_add m₁ m₂) k
  simp only [mdeg, Pi.add_apply] at this
  rw [this, hs m₁ h₁ k, hf m₂ h₂ k]
  rfl

/- English proof (translation)
Assume the negation of the conclusion as `h`. Take `⟨m₁, h₁, m₂, h₂, rfl⟩` from `Finset.mem_add.1 (support_mul r f (mem_support_iff.2 h))`. Use `hr m₁ h₁ (funext fun k => ?_)` and prove the remaining obligations. Establish `e` using `congrFun hm k`. Establish `e'` using `congrFun (mdeg_add m₁ m₂) k`.

Establish `e'' : mdeg m₂ k = a k` using `hf m₂ h₂ k`. Simplify using `only [Pi.add_apply] at e e'`. Use linear arithmetic over natural numbers and integers.
-/
theorem coeff_mul_eq_zero {r f : MvPolynomial (Σ k, ι k) ℂ} {b a : K → ℕ}
    (hr : ∀ m ∈ r.support, mdeg m ≠ b) (hf : IsMultiHomog f a) {m : (Σ k, ι k) →₀ ℕ}
    (hm : mdeg m = b + a) : coeff m (r * f) = 0 := by
  classical
  by_contra h
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (support_mul r f (mem_support_iff.2 h))
  refine hr m₁ h₁ (funext fun k => ?_)
  have e := congrFun hm k
  have e' := congrFun (mdeg_add m₁ m₂) k
  have e'' : mdeg m₂ k = a k := hf m₂ h₂ k
  simp only [Pi.add_apply] at e e'
  omega

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/- English proof (translation)
Take `⟨g, hgI, hg⟩` from `cyc_exists_blockComponent hI (b + a) Finset.univ h`. Establish `hgeq : g = part b s * f`. Use extensionality with `m`. Rewrite using `[hg m]`. Distinguish the cases in `hm : mdeg m = b + a`.

Establish `e : ∀ k ∈ (Finset.univ : Finset K), ∑ i, m ⟨k, i⟩ = (b + a) k` using `fun k _ => congrFun hm k`. Rewrite using `[if_pos e]`. Establish `hr : ∀ m' ∈ (s - part b s).support, mdeg m' ≠ b`. Introduce `m' hm' hb`. Rewrite `hm'` using `[mem_support_iff, coeff_sub, coeff_part, if_pos hb, sub_self]`.

Conclude with `hm' rfl`. Establish `e2 : s * f = part b s * f + (s - part b s) * f` using `by ring`. Rewrite using `[e2, coeff_add, coeff_mul_eq_zero hr hf hm, add_zero]`. Establish `e : ¬ ∀ k ∈ (Finset.univ : Finset K), ∑ i, m ⟨k, i⟩ = (b + a) k` using `fun h' => hm (funext fun k => h' k (Finset.mem_univ k))`. Rewrite using `[if_neg e]`.

Assume the negation of the conclusion as `hne`. Conclude with `hm (funext fun k => isMultiHomog_mul (isMultiHomog_part b s) hf m (mem_support_iff.2 (Ne.symm hne)) k)`. Conclude with `hgeq ▸ hgI`.
-/
theorem part_mul_mem [DecidableEq K] {I : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hI : ∀ k, I.IsHomogeneous (weightedHomogeneousSubmodule ℂ (cycBlockWt (ι := ι) k)))
    {s f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ} (hf : IsMultiHomog f a) (h : s * f ∈ I)
    (b : K → ℕ) : part b s * f ∈ I := by
  classical
  obtain ⟨g, hgI, hg⟩ := cyc_exists_blockComponent hI (b + a) Finset.univ h
  have hgeq : g = part b s * f := by
    ext m
    rw [hg m]
    by_cases hm : mdeg m = b + a
    · have e : ∀ k ∈ (Finset.univ : Finset K), ∑ i, m ⟨k, i⟩ = (b + a) k :=
        fun k _ => congrFun hm k
      rw [if_pos e]
      have hr : ∀ m' ∈ (s - part b s).support, mdeg m' ≠ b := by
        intro m' hm' hb
        rw [mem_support_iff, coeff_sub, coeff_part, if_pos hb, sub_self] at hm'
        exact hm' rfl
      have e2 : s * f = part b s * f + (s - part b s) * f := by ring
      rw [e2, coeff_add, coeff_mul_eq_zero hr hf hm, add_zero]
    · have e : ¬ ∀ k ∈ (Finset.univ : Finset K), ∑ i, m ⟨k, i⟩ = (b + a) k :=
        fun h' => hm (funext fun k => h' k (Finset.mem_univ k))
      rw [if_neg e]
      by_contra hne
      exact hm (funext fun k => isMultiHomog_mul (isMultiHomog_part b s) hf m
        (mem_support_iff.2 (Ne.symm hne)) k)
  exact hgeq ▸ hgI

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[pow_zero, Ideal.one_eq_top]`. Conclude with `(⊤ : HomogeneousIdeal 𝒜).isHomogeneous`. Consider the case `succ n ih`.

Rewrite using `[pow_succ]`. Conclude with `ih.mul hI`.
-/
theorem isHomogeneous_pow {A : Type*} [CommRing A] {R : Type*} [CommRing R] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {I : Ideal A} (hI : I.IsHomogeneous 𝒜) (n : ℕ) :
    (I ^ n).IsHomogeneous 𝒜 := by
  induction n with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top]
    exact (⊤ : HomogeneousIdeal 𝒜).isHomogeneous
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul hI

/- English proof (translation)
Unfold `ideal`. Rewrite using `[mem_map_renR_iff, RingEquiv.symm_apply_apply]`. Conclude with `hg`.
-/
theorem ren_mem {S : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {p : (k : K) → ι k}
    {g : MvPolynomial (Σ k, ι k) ℂ} (hg : g ∈ ReciprocityTheory.AnForm.R.chartIdeal S p) :
    renR (Σ k, ι k) g ∈ ideal S p := by
  unfold ideal
  rw [mem_map_renR_iff, RingEquiv.symm_apply_apply]
  exact hg

/- English proof (translation)
Take `⟨k, i⟩` from `q`. Unfold `lift`. Use `split_ifs with h`. Simplify using `only at h`. Substitute `h` using the available equality.

Establish `hm : (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ ReciprocityTheory.AnForm.R.chartIdeal S p` using `Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)`. Establish `h2 : renR (Σ k, ι k) (X ⟨k, p k⟩ - 1) ∈ ideal S p` using `ren_mem hm`. Establish `h3` using `(ideal S p).neg_mem h2`. Rewrite `h3` using `[map_sub, map_one, neg_sub]`. Conclude with `h3`.

Establish `: renR (Σ k, ι k) (X (⟨k, i⟩ : Σ k, ι k)) = X (Fintype.equivFin (Σ k, ι k) ⟨k, i⟩)`. Simplify using `[renameEquiv_apply]`. Rewrite using `[this, sub_self]`. Conclude with `zero_mem _`.
-/
theorem lift_sub_mem (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (q : Σ k, ι k) :
    lift p q - renR (Σ k, ι k) (X q) ∈ ideal S p := by
  classical
  obtain ⟨k, i⟩ := q
  unfold lift
  split_ifs with h
  · simp only at h
    subst h
    have hm : (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ ReciprocityTheory.AnForm.R.chartIdeal S p :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
    have h2 : renR (Σ k, ι k) (X ⟨k, p k⟩ - 1) ∈ ideal S p := ren_mem hm
    have h3 := (ideal S p).neg_mem h2
    rw [map_sub, map_one, neg_sub] at h3
    exact h3
  · have : renR (Σ k, ι k) (X (⟨k, i⟩ : Σ k, ι k)) = X (Fintype.equivFin (Σ k, ι k) ⟨k, i⟩) := by
      simp [renameEquiv_apply]
    rw [this, sub_self]
    exact zero_mem _

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C c`. Establish `e : renR (Σ k, ι k) (C c) = C c` using `by simp [renameEquiv_apply]`. Rewrite using `[e, bind₁_C_right, sub_self]`. Conclude with `zero_mem _`.

Consider the case `add g h hg hh`. Rewrite using `[map_add, map_add, add_sub_add_comm]`. Conclude with `add_mem hg hh`. Consider the case `mul_X g q hg`. Rewrite using `[map_mul, map_mul, bind₁_X_right]`.

Establish `e : bind₁ (lift p) g * lift p q - renR (Σ k, ι k) g * renR (Σ k, ι k) (X q) = (bind₁ (lift p) g - renR (Σ k, ι k) g) * lift p q + renR (Σ k, ι k) g * (lift p q - renR (Σ k, ι k) (X q))` using `by ring`. Rewrite using `[e]`. Conclude with `add_mem (Ideal.mul_mem_right _ _ hg) (Ideal.mul_mem_left _ _ (lift_sub_mem S p q))`.
-/
theorem deh_sub_mem (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k)
    (g : MvPolynomial (Σ k, ι k) ℂ) :
    bind₁ (lift p) g - renR (Σ k, ι k) g ∈ ideal S p := by
  induction g using MvPolynomial.induction_on with
  | C c =>
    have e : renR (Σ k, ι k) (C c) = C c := by simp [renameEquiv_apply]
    rw [e, bind₁_C_right, sub_self]
    exact zero_mem _
  | add g h hg hh =>
    rw [map_add, map_add, add_sub_add_comm]
    exact add_mem hg hh
  | mul_X g q hg =>
    rw [map_mul, map_mul, bind₁_X_right]
    have e : bind₁ (lift p) g * lift p q - renR (Σ k, ι k) g * renR (Σ k, ι k) (X q) =
        (bind₁ (lift p) g - renR (Σ k, ι k) g) * lift p q +
          renR (Σ k, ι k) g * (lift p q - renR (Σ k, ι k) (X q)) := by ring
    rw [e]
    exact add_mem (Ideal.mul_mem_right _ _ hg) (Ideal.mul_mem_left _ _ (lift_sub_mem S p q))

/- English proof (translation)
Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `g hg`. Establish `hm : renR (Σ k, ι k) g ∈ ideal S p` using `ren_mem (Ideal.mem_sup_left hg)`. Rewrite using `[Ideal.mem_comap]`. Use `add_mem (deh_sub_mem S p g) hm` as an intermediate fact.

Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem map_deh_le (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    Ideal.map (bind₁ (lift p) : _ →ₐ[ℂ] _) S ≤ ideal S p := by
  rw [Ideal.map_le_iff_le_comap]
  intro g hg
  have hm : renR (Σ k, ι k) g ∈ ideal S p := ren_mem (Ideal.mem_sup_left hg)
  rw [Ideal.mem_comap]
  have := add_mem (deh_sub_mem S p g) hm
  rwa [sub_add_cancel] at this

/- English proof (translation)
Introduce `K _ ι _ P Q p f s a n hP hQ hQp hX hf hs hrel`. Establish `hI : ∀ k, (Q ^ n ⊔ P).IsHomogeneous (weightedHomogeneousSubmodule ℂ (cycBlockWt (ι` using `ι) k)) := fun k => (isHomogeneous_pow _ (cyc_isHomogeneous_of_isMultiHomogIdeal hQ k) n).sup (cyc_isHomogeneous_of_isMultiHomogIdeal hP k)`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b, part b s ∉ Q := by`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`.

Conclude with `hs (sum_part s ▸ Ideal.sum_mem _ fun b _ => hall b)`. Establish `hmem` using `part_mul_mem hI hf hrel b`. Use `⟨bind₁ (lift p) (part b s), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[((GlobalTheory.T.affine_chart_ideal_prime_and_saturated K ι Q p hQ hQp hX).2 _ b (isMultiHomog_part b s))]`. Conclude with `hb`.

Establish `h1` using `Ideal.mem_map_of_mem (bind₁ (lift p) : _ →ₐ[ℂ] _) hmem`. Rewrite `h1` using `[map_mul, Ideal.map_sup, Ideal.map_pow]`. Conclude with `(sup_le_sup (Ideal.pow_right_mono (map_deh_le Q p) n) (map_deh_le P p)) h1`.
-/
theorem relation_dehom : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k)
    (f s : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (n : ℕ), IsMultiHomogIdeal P →
    IsMultiHomogIdeal Q → Q.IsPrime → (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) →
    IsMultiHomog f a → s ∉ Q → s * f ∈ Q ^ n ⊔ P →
    ∃ s' ∉ SncRes.ideal Q p, s' * bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ^ n ⊔ SncRes.ideal P p := by
  intro K _ ι _ P Q p f s a n hP hQ hQp hX hf hs hrel
  classical
  have hI : ∀ k, (Q ^ n ⊔ P).IsHomogeneous
      (weightedHomogeneousSubmodule ℂ (cycBlockWt (ι := ι) k)) := fun k =>
    (isHomogeneous_pow _ (cyc_isHomogeneous_of_isMultiHomogIdeal hQ k) n).sup
      (cyc_isHomogeneous_of_isMultiHomogIdeal hP k)
  obtain ⟨b, hb⟩ : ∃ b, part b s ∉ Q := by
    by_contra hall
    push_neg at hall
    exact hs (sum_part s ▸ Ideal.sum_mem _ fun b _ => hall b)
  have hmem := part_mul_mem hI hf hrel b
  refine ⟨bind₁ (lift p) (part b s), ?_, ?_⟩
  · rw [((GlobalTheory.T.affine_chart_ideal_prime_and_saturated K ι Q p hQ hQp hX).2 _ b (isMultiHomog_part b s))]
    exact hb
  · have h1 := Ideal.mem_map_of_mem (bind₁ (lift p) : _ →ₐ[ℂ] _) hmem
    rw [map_mul, Ideal.map_sup, Ideal.map_pow] at h1
    exact (sup_le_sup (Ideal.pow_right_mono (map_deh_le Q p) n) (map_deh_le P p)) h1

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom
