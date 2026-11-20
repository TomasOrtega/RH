import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelNonzeroModulusDeterminantEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelPropertiesOfHypotheses

set_option maxHeartbeats 400000

noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace PositiveSemidefiniteClosure

/- English proof (translation)
Introduce `a`. Establish `: ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k' x y = ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y` using `Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by rw [h x hx y hy]`. Rewrite using `[this]`. Conclude with `hk a`.
-/
theorem psd_congr {X : Type} {F : Finset X} {k k' : X → X → ℂ}
    (h : ∀ x ∈ F, ∀ y ∈ F, k x y = k' x y) (hk : IsPSD F k) : IsPSD F k' := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k' x y = ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y :=
    Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by rw [h x hx y hy]
  rw [this]; exact hk a

/- English proof (translation)
Introduce `a`. Establish `: ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * (k x y + k' x y) = ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y + ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k' x y`. Simplify using `only [mul_add, Finset.sum_add_distrib]`. Rewrite using `[this]`. Take `⟨h1, h2⟩` from `hk a`.

Take `⟨h3, h4⟩` from `hk' a`. Conclude with `⟨by rw [Complex.add_im, h1, h3, add_zero], by rw [Complex.add_re]; exact add_nonneg h2 h4⟩`.
-/
theorem psd_add {X : Type} {F : Finset X} {k k' : X → X → ℂ} (hk : IsPSD F k) (hk' : IsPSD F k') :
    IsPSD F (fun x y => k x y + k' x y) := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * (k x y + k' x y) =
      ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k x y + ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k' x y := by
    simp only [mul_add, Finset.sum_add_distrib]
  rw [this]
  obtain ⟨h1, h2⟩ := hk a
  obtain ⟨h3, h4⟩ := hk' a
  exact ⟨by rw [Complex.add_im, h1, h3, add_zero], by rw [Complex.add_re]; exact add_nonneg h2 h4⟩

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => exact A5x6.isPSD_zero F _ (fun _ _ _ _ => by simp)`. Consider the case `insert i T hi ih`. Establish `h1` using `psd_add (h i (Finset.mem_insert_self i T)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))`. Conclude with `psd_congr (fun x _ y _ => by rw [Finset.sum_insert hi]) h1`.
-/
theorem psd_sum {X ι : Type} {F : Finset X} (T : Finset ι) (k : ι → X → X → ℂ)
    (h : ∀ i ∈ T, IsPSD F (k i)) : IsPSD F (fun x y => ∑ i ∈ T, k i x y) := by
  classical
  induction T using Finset.induction_on with
  | empty => exact A5x6.isPSD_zero F _ (fun _ _ _ _ => by simp)
  | insert i T hi ih =>
    have h1 := psd_add (h i (Finset.mem_insert_self i T))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    exact psd_congr (fun x _ y _ => by rw [Finset.sum_insert hi]) h1

/- English proof (translation)
Introduce `a`. Establish `: ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * (((c x * c y : ℝ) : ℂ) * k x y) = ∑ x ∈ F, ∑ y ∈ F, (a x * (c x : ℂ)) * conj (a y * (c y : ℂ)) * k x y` using `Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by`. Rewrite using `[map_mul, Complex.conj_ofReal]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `hk _`.
-/
theorem psd_scale {X : Type} {F : Finset X} {k : X → X → ℂ} (c : X → ℝ) (hk : IsPSD F k) :
    IsPSD F (fun x y => ((c x * c y : ℝ) : ℂ) * k x y) := by
  intro a
  have : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * (((c x * c y : ℝ) : ℂ) * k x y) =
      ∑ x ∈ F, ∑ y ∈ F, (a x * (c x : ℂ)) * conj (a y * (c y : ℂ)) * k x y :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      rw [map_mul, Complex.conj_ofReal]; push_cast; ring
  rw [this]; exact hk _

/- English proof (translation)
Establish `: DiscreteTopology (K ⧸ Λ)` using `QuotientAddGroup.discreteTopology hΛ`. Establish `h1 : (((↑) : K → K ⧸ Λ) '' C).Finite` using `(hC.image QuotientAddGroup.continuous_mk).finite_of_discrete`. Use `h1.subset ?_` and prove the remaining obligations. Introduce `y hy`. Conclude with `⟨Quotient.out y, hy, QuotientAddGroup.out_eq' y⟩`.
-/
theorem finite_cosets {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (Λ : AddSubgroup K) (hΛ : IsOpen (Λ : Set K)) (C : Set K) (hC : IsCompact C) :
    {y : K ⧸ Λ | (Quotient.out y : K) ∈ C}.Finite := by
  have : DiscreteTopology (K ⧸ Λ) := QuotientAddGroup.discreteTopology hΛ
  have h1 : (((↑) : K → K ⧸ Λ) '' C).Finite :=
    (hC.image QuotientAddGroup.continuous_mk).finite_of_discrete
  refine h1.subset ?_
  intro y hy
  exact ⟨Quotient.out y, hy, QuotientAddGroup.out_eq' y⟩

/- English proof (translation)
Establish `h : ((Quotient.out ((z : K) : K ⧸ Λ) : K) : K ⧸ Λ) = (z : K ⧸ Λ)` using `QuotientAddGroup.out_eq' _`. Rewrite `h` using `[QuotientAddGroup.eq]`. Use `Λ.neg_mem h` as an intermediate fact. Simplify `this` using `[sub_eq_add_neg, add_comm]`.
-/
theorem out_sub_mem {K : Type} [CommRing K] (Λ : AddSubgroup K) (z : K) :
    (Quotient.out ((z : K) : K ⧸ Λ) : K) - z ∈ Λ := by
  have h : ((Quotient.out ((z : K) : K ⧸ Λ) : K) : K ⧸ Λ) = (z : K ⧸ Λ) := QuotientAddGroup.out_eq' _
  rw [QuotientAddGroup.eq] at h
  have := Λ.neg_mem h
  simpa [sub_eq_add_neg, add_comm] using this

/- English proof (translation)
Consider the cases of `m with`. Consider the case `zero => simp`. Consider the case `succ k`. Establish `: (k + 1) * (k + 1 + 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1)`. Simplify using `only [Nat.add_sub_cancel]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Nat.add_mul_div_left _ _ (by norm_num)]`.
-/
theorem nat_tri (m : ℕ) : m * (m + 1) / 2 = m * (m - 1) / 2 + m := by
  cases m with
  | zero => simp
  | succ k =>
    have : (k + 1) * (k + 1 + 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) := by
      simp only [Nat.add_sub_cancel]; ring
    rw [this, Nat.add_mul_div_left _ _ (by norm_num)]

open Classical in
/- English proof (translation)
Unfold `uGram`. Use `congr 1`. Rewrite using `[finsum_eq_sum_of_support_subset (s := T), Finset.sum_filter]`. Introduce `x hx`. Assume the negation of the conclusion as `hxT`.

Apply `hx` to reduce the goal to its premises. Simplify using `only [Finset.mem_coe] at hxT`. Use `show (if (cr x : K) ∈ S then Kp R ψ (pt2 h m t (cr x)) (pt2 h' m t' (cr x)) else 0) = 0`. Rewrite using `[hT x hxT]`. Simplify using the standard rewrite rules.
-/
theorem uGram_eq_sum {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ)
    (cr : K ⧸ R.toAddSubgroup → Kˣ) (S : Set K) (h h' : Point K) (t t' : Kˣ)
    (T : Finset (K ⧸ R.toAddSubgroup))
    (hT : ∀ x, x ∉ T → Kp R ψ (pt2 h m t (cr x)) (pt2 h' m t' (cr x)) = 0) :
    uGram R ψ m cr S h h' t t' =
      ((modK R ((t : K) * (t' : K)) ^ (m * (m + 1) / 2) : ℝ) : ℂ) *
        ∑ x ∈ T.filter (fun x => (cr x : K) ∈ S),
          Kp R ψ (pt2 h m t (cr x)) (pt2 h' m t' (cr x)) := by
  unfold uGram
  congr 1
  rw [finsum_eq_sum_of_support_subset (s := T), Finset.sum_filter]
  intro x hx
  by_contra hxT
  apply hx
  simp only [Finset.mem_coe] at hxT
  show (if (cr x : K) ∈ S then Kp R ψ (pt2 h m t (cr x)) (pt2 h' m t' (cr x)) else 0) = 0
  rw [hT x hxT]; simp

/- English proof (translation)
Introduce `hG hP hM K _ _ _ R ψ hD m cr S F hcr hsz`. Establish `hfin : (⋃ p ∈ F, ⋃ p' ∈ F, Function.support (fun x => Kp R ψ (pt2 p.1 m p.2 (cr x)) (pt2 p'.1 m p'.2 (cr x)))).Finite`. Use `Set.Finite.biUnion F.finite_toSet fun p hp => Set.Finite.biUnion F.finite_toSet fun p' hp' => ?_` and prove the remaining obligations. Establish `hs : (addBlock p.1 m p.2).1.sum = (addBlock p'.1 m p'.2).1.sum`. Simplify using `[addBlock, hsz p hp p' hp']`.

Use `(hP K R ψ hD (addBlock p.1 m p.2) (addBlock p'.1 m p'.2) hs cr hcr).1` as an intermediate fact. Use `this.subset ?_` and prove the remaining obligations. Introduce `x hx`. Simplify `hx` using `[Ns, pt2]`. Use `set T := hfin.toFinset with hTdef`.

Establish `hT : ∀ p ∈ F, ∀ p' ∈ F, ∀ x, x ∉ T → Kp R ψ (pt2 p.1 m p.2 (cr x)) (pt2 p'.1 m p'.2 (cr x)) = 0`. Introduce `p hp p' hp' x hx`. Assume the negation of the conclusion as `hne`. Apply `hx` to reduce the goal to its premises. Rewrite using `[hTdef, Set.Finite.mem_toFinset]`.

Simplify using `only [Set.mem_iUnion]`. Conclude with `⟨p, hp, p', hp', hne⟩`. Establish `hk : ∀ x, IsPSD F (fun p p' : Point K × Kˣ => Kp R ψ (pt2 p.1 m p.2 (cr x)) (pt2 p'.1 m p'.2 (cr x)))` using `fun x => A5x6.psd_comap (Kp R ψ) (fun p : Point K × Kˣ => pt2 p.1 m p.2 (cr x)) F (hG K R ψ hD _)`. Establish `hgen : ∀ T' : Finset (K ⧸ R.toAddSubgroup), IsPSD F (fun p p' : Point K × Kˣ => ((modK R (p.2 : K) ^ (m * (m + 1) / 2) * modK R (p'.2 : K) ^ (m * (m + 1) / 2) : ℝ) : ℂ) * ∑ x ∈ T', Kp R ψ (pt2 p.1 m p.2 (cr x)) (pt2 p'.1 m p'.2 (cr x)))` using `fun T' => psd_scale (fun p : Point K × Kˣ => modK R (p.2 : K) ^ (m * (m + 1) / 2)) (psd_sum T' _ fun x _ => hk x)`. Prove the components needed by the constructor for the conclusion.

Use `psd_congr ?_ (hgen (T.filter fun x => (cr x : K) ∈ S))` and prove the remaining obligations. Introduce `p hp p' hp'`. Rewrite using `[uGram_eq_sum R ψ m cr S p.1 p'.1 p.2 p'.2 T (hT p hp p' hp'), (hM K R ψ hD p.2 p'.2).2, mul_pow]`. Use `psd_congr ?_ (hgen (T.filter fun x => ¬ (cr x : K) ∈ S))` and prove the remaining obligations. Introduce `p hp p' hp'`.

Rewrite using `[uGram_eq_sum R ψ m cr S p.1 p'.1 p.2 p'.2 T (hT p hp p' hp'), uGram_eq_sum R ψ m cr Set.univ p.1 p'.1 p.2 p'.2 T (hT p hp p' hp'), (hM K R ψ hD p.2 p'.2).2, mul_pow, ← mul_sub]`. Use `congr 1`. Simplify using `only [Set.mem_univ, Finset.filter_true]`. Rewrite using `[← Finset.sum_filter_add_sum_filter_not T (fun x => (cr x : K) ∈ S)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cutPSD_main : CutPSD := by
  intro hG hP hM K _ _ _ R ψ hD m cr S F hcr hsz
  classical

  have hfin : (⋃ p ∈ F, ⋃ p' ∈ F, Function.support (fun x =>
      Kp R ψ (pt2 p.1 m p.2 (cr x)) (pt2 p'.1 m p'.2 (cr x)))).Finite := by
    refine Set.Finite.biUnion F.finite_toSet fun p hp => Set.Finite.biUnion F.finite_toSet
      fun p' hp' => ?_
    have hs : (addBlock p.1 m p.2).1.sum = (addBlock p'.1 m p'.2).1.sum := by
      simp [addBlock, hsz p hp p' hp']
    have := (hP K R ψ hD (addBlock p.1 m p.2) (addBlock p'.1 m p'.2) hs cr hcr).1
    refine this.subset ?_
    intro x hx
    simpa [Ns, pt2] using hx
  set T := hfin.toFinset with hTdef
  have hT : ∀ p ∈ F, ∀ p' ∈ F, ∀ x, x ∉ T →
      Kp R ψ (pt2 p.1 m p.2 (cr x)) (pt2 p'.1 m p'.2 (cr x)) = 0 := by
    intro p hp p' hp' x hx
    by_contra hne
    apply hx
    rw [hTdef, Set.Finite.mem_toFinset]
    simp only [Set.mem_iUnion]
    exact ⟨p, hp, p', hp', hne⟩
  have hk : ∀ x, IsPSD F (fun p p' : Point K × Kˣ =>
      Kp R ψ (pt2 p.1 m p.2 (cr x)) (pt2 p'.1 m p'.2 (cr x))) := fun x =>
    A5x6.psd_comap (Kp R ψ) (fun p : Point K × Kˣ => pt2 p.1 m p.2 (cr x)) F (hG K R ψ hD _)
  have hgen : ∀ T' : Finset (K ⧸ R.toAddSubgroup), IsPSD F (fun p p' : Point K × Kˣ =>
      ((modK R (p.2 : K) ^ (m * (m + 1) / 2) * modK R (p'.2 : K) ^ (m * (m + 1) / 2) : ℝ) : ℂ) *
        ∑ x ∈ T', Kp R ψ (pt2 p.1 m p.2 (cr x)) (pt2 p'.1 m p'.2 (cr x))) := fun T' =>
    psd_scale (fun p : Point K × Kˣ => modK R (p.2 : K) ^ (m * (m + 1) / 2))
      (psd_sum T' _ fun x _ => hk x)
  constructor
  · refine psd_congr ?_ (hgen (T.filter fun x => (cr x : K) ∈ S))
    intro p hp p' hp'
    rw [uGram_eq_sum R ψ m cr S p.1 p'.1 p.2 p'.2 T (hT p hp p' hp'), (hM K R ψ hD p.2 p'.2).2,
      mul_pow]
  · refine psd_congr ?_ (hgen (T.filter fun x => ¬ (cr x : K) ∈ S))
    intro p hp p' hp'
    rw [uGram_eq_sum R ψ m cr S p.1 p'.1 p.2 p'.2 T (hT p hp p' hp'),
      uGram_eq_sum R ψ m cr Set.univ p.1 p'.1 p.2 p'.2 T (hT p hp p' hp'),
      (hM K R ψ hD p.2 p'.2).2, mul_pow, ← mul_sub]
    congr 1
    simp only [Set.mem_univ, Finset.filter_true]
    rw [← Finset.sum_filter_add_sum_filter_not T (fun x => (cr x : K) ∈ S)]
    ring

/- English proof (translation)
Introduce `hB hC hM K _ _ _ R ψ hD m cr S h h' t t' ht hdet`. Unfold `uGram`. Establish `: ∀ x : K ⧸ R.toAddSubgroup, Kp R ψ (pt2 h m t (cr x)) (pt2 h' m t' (cr x)) = 0`. Introduce `x`. Assume the negation of the conclusion as `hne`.

Establish `h1` using `hB K R ψ hD _ _ hne`. Establish `c1` using `hC K R ψ hD (addBlock h m t) 1 (cr x)`. Establish `c2` using `hC K R ψ hD (addBlock h' m t') 1 (cr x)`. Rewrite `c1` using `[hC K R ψ hD h m t]`. Rewrite `c2` using `[hC K R ψ hD h' m t']`.

Establish `h3 : cSize R (pt2 h m t (cr x)) = cSize R (pt2 h' m t' (cr x))`. Unfold `cSize`. Rewrite using `[h1]`. Unfold `pt2 at h3`. Rewrite `h3` using `[c1, c2, ht]`.

Take `⟨hb, _⟩` from `hM K R ψ hD t' t`. Take `⟨hc, _⟩` from `hM K R ψ hD (cr x) t`. Establish `: cSize R h = cSize R h'`. Establish `hb'` using `ne_of_gt hb`. Establish `hc'` using `ne_of_gt hc`.

Establish `k1 : ((modK R (t' : K)) ^ m)⁻¹ ≠ 0` using `inv_ne_zero (pow_ne_zero _ hb')`. Establish `k2 : ((modK R ((cr x : Kˣ) : K)) ^ 1)⁻¹ ≠ 0` using `inv_ne_zero (pow_ne_zero _ hc')`. Conclude with `mul_right_cancel₀ k1 (mul_right_cancel₀ k2 h3)`. Unfold `cSize at this`. Conclude with `hdet (inv_injective this)`.

Simplify using `[this]`.
-/
theorem uBlock_main : UBlock := by
  intro hB hC hM K _ _ _ R ψ hD m cr S h h' t t' ht hdet
  unfold uGram
  have : ∀ x : K ⧸ R.toAddSubgroup, Kp R ψ (pt2 h m t (cr x)) (pt2 h' m t' (cr x)) = 0 := by
    intro x
    by_contra hne
    have h1 := hB K R ψ hD _ _ hne
    have c1 := hC K R ψ hD (addBlock h m t) 1 (cr x)
    have c2 := hC K R ψ hD (addBlock h' m t') 1 (cr x)
    rw [hC K R ψ hD h m t] at c1
    rw [hC K R ψ hD h' m t'] at c2
    have h3 : cSize R (pt2 h m t (cr x)) = cSize R (pt2 h' m t' (cr x)) := by
      unfold cSize; rw [h1]
    unfold pt2 at h3
    rw [c1, c2, ht] at h3
    obtain ⟨hb, _⟩ := hM K R ψ hD t' t
    obtain ⟨hc, _⟩ := hM K R ψ hD (cr x) t
    have : cSize R h = cSize R h' := by
      have hb' := ne_of_gt hb
      have hc' := ne_of_gt hc
      have k1 : ((modK R (t' : K)) ^ m)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hb')
      have k2 : ((modK R ((cr x : Kˣ) : K)) ^ 1)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hc')
      exact mul_right_cancel₀ k1 (mul_right_cancel₀ k2 h3)
    unfold cSize at this
    exact hdet (inv_injective this)
  simp [this]

/- English proof (translation)
Introduce `hU hP hC hM _ K _ _ _ R ψ hD m n₀ F Θ hF hA t cr hcr`. Take `⟨h1, h2, ⟨L, _, hLc, hL0⟩, h4, h5, _, _⟩` from `hA`. Establish `hfin` using `finite_cosets R.toAddSubgroup hD.isOpen (L : Set K) hLc`. Use `set x₀ : K ⧸ R.toAddSubgroup := ((t : K) : K ⧸ R.toAddSubgroup) with hx₀`. Use `set T := insert x₀ hfin.toFinset with hTdef`.

Establish `hsum : ∀ h ∈ F, ∀ h' ∈ F, ∑ᶠ x : K ⧸ R.toAddSubgroup, Θ (Quotient.out x) h h' = Θ (t : K) h h' + ∑ x ∈ T.erase x₀, Θ (Quotient.out x) h h'`. Introduce `h hh h' hh'`. Rewrite using `[finsum_eq_sum_of_support_subset (s := T)]`. Rewrite using `[← Finset.add_sum_erase T _ (Finset.mem_insert_self x₀ _)]`. Use `congr 1`.

Establish `hr` using `out_sub_mem R.toAddSubgroup (t : K)`. Use `h1 (t : K) _ hr` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Rewrite using `[this]`. Introduce `x hx`.

Assume the negation of the conclusion as `hxT`. Apply `hx` to reduce the goal to its premises. Apply `hL0 _ _ h hh h' hh'` to reduce the goal to its premises. Introduce `hxL`. Apply `hxT` to reduce the goal to its premises.

Rewrite using `[hTdef]`. Simplify using `only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Set.Finite.mem_toFinset]`. Conclude with `Or.inr hxL`. Establish `key` using `psd_scale (fun h : Point K => cSize R h) (psd_add (psd_add h5 (psd_sum (T.erase x₀) (fun x => Θ (Quotient.out x)) fun x _ => h2 _)) (h4 t))`. Use `psd_congr ?_ key` and prove the remaining obligations.

Introduce `h hh h' hh'`. Rewrite using `[hU hP hC hM K R ψ hD m h h' t t cr ((hF h hh).trans (hF h' hh').symm) hcr, hsum h hh h' hh']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem uNormBound_main : UNormBound := by
  intro hU hP hC hM _ K _ _ _ R ψ hD m n₀ F Θ hF hA t cr hcr
  classical
  obtain ⟨h1, h2, ⟨L, _, hLc, hL0⟩, h4, h5, _, _⟩ := hA
  have hfin := finite_cosets R.toAddSubgroup hD.isOpen (L : Set K) hLc
  set x₀ : K ⧸ R.toAddSubgroup := ((t : K) : K ⧸ R.toAddSubgroup) with hx₀
  set T := insert x₀ hfin.toFinset with hTdef
  have hsum : ∀ h ∈ F, ∀ h' ∈ F, ∑ᶠ x : K ⧸ R.toAddSubgroup, Θ (Quotient.out x) h h' =
      Θ (t : K) h h' + ∑ x ∈ T.erase x₀, Θ (Quotient.out x) h h' := by
    intro h hh h' hh'
    rw [finsum_eq_sum_of_support_subset (s := T)]
    · rw [← Finset.add_sum_erase T _ (Finset.mem_insert_self x₀ _)]
      congr 1
      have hr := out_sub_mem R.toAddSubgroup (t : K)
      have := h1 (t : K) _ hr
      rw [add_sub_cancel] at this
      rw [this]
    · intro x hx
      by_contra hxT
      apply hx
      apply hL0 _ _ h hh h' hh'
      intro hxL
      apply hxT
      rw [hTdef]
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Set.Finite.mem_toFinset]
      exact Or.inr hxL
  have key := psd_scale (fun h : Point K => cSize R h)
    (psd_add (psd_add h5 (psd_sum (T.erase x₀) (fun x => Θ (Quotient.out x)) fun x _ => h2 _)) (h4 t))
  refine psd_congr ?_ key
  intro h hh h' hh'
  rw [hU hP hC hM K R ψ hD m h h' t t cr ((hF h hh).trans (hF h' hh').symm) hcr, hsum h hh h' hh']
  push_cast
  ring

/- English proof (translation)
Establish `hfi : (M.addSubgroupOf L).FiniteIndex` using `⟨h⟩`. Establish `hfin : Finite (L ⧸ M.addSubgroupOf L)` using `AddSubgroup.finite_quotient_of_finiteIndex`. Set `_ : Fintype (L ⧸ M.addSubgroupOf L)` to `Fintype.ofFinite _`. Use `⟨Finset.univ.image (fun q : L ⧸ M.addSubgroupOf L => ((Quotient.out q : L) : K)), ?_, ?_⟩` and prove the remaining obligations. Introduce `a ha`.

Take `⟨q, _, rfl⟩` from `Finset.mem_image.mp ha`. Conclude with `(Quotient.out q : L).2`. Introduce `l hl`. Establish `key : ∀ q : L ⧸ M.addSubgroupOf L, l - ((Quotient.out q : L) : K) ∈ M ↔ q = ((⟨l, hl⟩ : L) : L ⧸ M.addSubgroupOf L)`. Introduce `q`.

Establish `e : q = ((Quotient.out q : L) : L ⧸ M.addSubgroupOf L)` using `(QuotientAddGroup.out_eq' q).symm`. Prove the components needed by the constructor for the conclusion. Introduce `hm`. Rewrite using `[e, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`. Simplify `hm` using `[sub_eq_add_neg, add_comm]`.

Introduce `hq`. Rewrite `hq` using `[e, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`. Simplify `hq` using `[sub_eq_add_neg, add_comm]`. Use `⟨((Quotient.out ((⟨l, hl⟩ : L) : L ⧸ M.addSubgroupOf L) : L) : K), ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, (key _).2 rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `a ⟨ha, hm⟩`.

Take `⟨q, _, rfl⟩` from `Finset.mem_image.mp ha`. Rewrite using `[(key q).1 hm]`.
-/
theorem exists_reps {K : Type} [CommRing K] (L M : AddSubgroup K) (h : M.relIndex L ≠ 0) :
    ∃ S : Finset K, IsReps S L M := by
  classical
  have hfi : (M.addSubgroupOf L).FiniteIndex := ⟨h⟩
  have hfin : Finite (L ⧸ M.addSubgroupOf L) := AddSubgroup.finite_quotient_of_finiteIndex
  let _ : Fintype (L ⧸ M.addSubgroupOf L) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : L ⧸ M.addSubgroupOf L => ((Quotient.out q : L) : K)), ?_, ?_⟩
  · intro a ha
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ha
    exact (Quotient.out q : L).2
  · intro l hl
    have key : ∀ q : L ⧸ M.addSubgroupOf L, l - ((Quotient.out q : L) : K) ∈ M ↔
        q = ((⟨l, hl⟩ : L) : L ⧸ M.addSubgroupOf L) := by
      intro q
      have e : q = ((Quotient.out q : L) : L ⧸ M.addSubgroupOf L) := (QuotientAddGroup.out_eq' q).symm
      constructor
      · intro hm
        rw [e, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
        simpa [sub_eq_add_neg, add_comm] using hm
      · intro hq
        rw [e, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at hq
        simpa [sub_eq_add_neg, add_comm] using hq
    refine ⟨((Quotient.out ((⟨l, hl⟩ : L) : L ⧸ M.addSubgroupOf L) : L) : K),
      ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, (key _).2 rfl⟩, ?_⟩
    rintro a ⟨ha, hm⟩
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ha
    rw [(key q).1 hm]

/- English proof (translation)
Take `⟨h1, h2⟩` from `h`. Set `f : S → L ⧸ M.addSubgroupOf L` to `fun a => ((⟨a.1, h1 a.1 a.2⟩ : L) : L ⧸ M.addSubgroupOf L)`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce `a a' haa`.

Establish `haa' : ((⟨a.1, h1 a.1 a.2⟩ : L) : L ⧸ M.addSubgroupOf L) = ((⟨a'.1, h1 a'.1 a'.2⟩ : L) : L ⧸ M.addSubgroupOf L)` using `haa`. Rewrite `haa'` using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`. Establish `hm : a'.1 - a.1 ∈ M` using `by simpa [sub_eq_add_neg, add_comm] using haa'`. Take `⟨b, _, hb⟩` from `h2 a'.1 (h1 a'.1 a'.2)`. Establish `e1` using `hb a.1 ⟨a.2, hm⟩`.

Establish `e2` using `hb a'.1 ⟨a'.2, by simp⟩`. Conclude with `Subtype.ext (e1.trans e2.symm)`. Introduce `q`. Proceed by induction on `q using QuotientAddGroup.induction_on with`. Consider the case `H l`.

Take `⟨a, ⟨ha, hm⟩, _⟩` from `h2 l.1 l.2`. Use `⟨⟨a, ha⟩, ?_⟩` and prove the remaining obligations. Use `show ((⟨a, h1 a ha⟩ : L) : L ⧸ M.addSubgroupOf L) = (l : L ⧸ M.addSubgroupOf L)`. Rewrite using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`. Simplify `hm` using `[sub_eq_add_neg, add_comm]`.

Use `Nat.card_congr (Equiv.ofBijective f hf)` as an intermediate fact. Rewrite `this` using `[Nat.card_eq_fintype_card, Fintype.card_coe]`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem card_reps {K : Type} [CommRing K] (L M : AddSubgroup K) (S : Finset K) (h : IsReps S L M) :
    S.card = M.relIndex L := by
  classical
  obtain ⟨h1, h2⟩ := h
  let f : S → L ⧸ M.addSubgroupOf L := fun a => ((⟨a.1, h1 a.1 a.2⟩ : L) : L ⧸ M.addSubgroupOf L)
  have hf : Function.Bijective f := by
    constructor
    · intro a a' haa
      have haa' : ((⟨a.1, h1 a.1 a.2⟩ : L) : L ⧸ M.addSubgroupOf L) =
        ((⟨a'.1, h1 a'.1 a'.2⟩ : L) : L ⧸ M.addSubgroupOf L) := haa
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at haa'
      have hm : a'.1 - a.1 ∈ M := by simpa [sub_eq_add_neg, add_comm] using haa'
      obtain ⟨b, _, hb⟩ := h2 a'.1 (h1 a'.1 a'.2)
      have e1 := hb a.1 ⟨a.2, hm⟩
      have e2 := hb a'.1 ⟨a'.2, by simp⟩
      exact Subtype.ext (e1.trans e2.symm)
    · intro q
      induction q using QuotientAddGroup.induction_on with
      | H l =>
        obtain ⟨a, ⟨ha, hm⟩, _⟩ := h2 l.1 l.2
        refine ⟨⟨a, ha⟩, ?_⟩
        show ((⟨a, h1 a ha⟩ : L) : L ⧸ M.addSubgroupOf L) = (l : L ⧸ M.addSubgroupOf L)
        rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
        simpa [sub_eq_add_neg, add_comm] using hm
  have := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at this
  rw [this]; rfl

/- English proof (translation)
The claim follows from `h.1.mem_nhds L.zero_mem`.
-/
theorem lat_mem_nhds {K : Type} [CommRing K] [TopologicalSpace K] {L : AddSubgroup K}
    (h : IsLat L) : (L : Set K) ∈ 𝓝 (0 : K) := h.1.mem_nhds L.zero_mem

/- English proof (translation)
Introduce `hLC hKH hML hCh hLF K _ _ _ R ψ hD hn s F Om Lc hs hOm hLc`. Take `⟨hOo, hOc, hOu, _⟩` from `hOm`. Establish `hRlat : IsLat R.toAddSubgroup` using `⟨hD.isOpen, hD.isCompact⟩`. Take `⟨L₁, hl₁, hle₁, hp₁⟩` from `(hCh K R ψ hD hn).1 (Om ∪ Lc) (hOc.union hLc)`. Take `⟨V₀, hV₀, hV₀s⟩` from `compact_open_separated_add_right hOc hOo (subset_refl Om)`.

Take `⟨Λ₀, hΛ₀, hΛ₀p⟩` from `hML K R ψ hD hn Om hOc hOu Set.univ Filter.univ_mem`. Use `choose Λ hΛ hΛp using fun h : Point K => hLC K R ψ hD hn s h Om hs hOc hOu`. Establish `hV : (V₀ ∩ (Λ₀ : Set K)) ∩ ⋂ h ∈ F, (Λ h : Set K) ∈ 𝓝 (0 : K)` using `Filter.inter_mem (Filter.inter_mem hV₀ (lat_mem_nhds hΛ₀)) ((Filter.biInter_finset_mem F).2 fun h _ => lat_mem_nhds (hΛ h))`. Take `⟨L₂, hl₂, hle₂, hp₂⟩` from `(hCh K R ψ hD hn).2 _ hV`. Take `⟨A, hA⟩` from `exists_reps L₂ R.toAddSubgroup (hLF K L₂ R.toAddSubgroup hl₂ hRlat)`.

Take `⟨B, hB⟩` from `exists_reps R.toAddSubgroup L₁ (hLF K R.toAddSubgroup L₁ hRlat hl₁)`. Use `⟨{ L₁ := L₁, L₂ := L₂, A := A, B := B, lat₁ := hl₁, lat₂ := hl₂, le₁ := hle₁, le₂ := hle₂, omPerp := fun z hz => hp₁ z (Or.inl hz), cutPerp := fun z hz => hp₁ z (Or.inr hz), omStable := ?_, nsInv := ?_, repsA := hA, repsB := hB }⟩` and prove the remaining obligations. Introduce `z hz l hl`. Conclude with `hV₀s (Set.add_mem_add hz (hp₂ l hl).1.1)`. Introduce `h hh h' hh' z hz l hl`.

Establish `hlV` using `hp₂ l hl`. Take `⟨hu', hmod, _⟩` from `hΛ₀p z hz l hlV.1.2`. Establish `hu` using `hOu z hz`. Establish `hlh : l ∈ Λ h`. Use `hlV.2` as an intermediate fact.

Simplify using `only [Set.mem_iInter] at this`. Conclude with `this h hh`. Establish `hlh' : l ∈ Λ h'`. Use `hlV.2` as an intermediate fact. Simplify using `only [Set.mem_iInter] at this`.

Conclude with `this h' hh'`. Unfold `NsK`. Rewrite using `[dif_pos hu', dif_pos hu]`. Unfold `Ns`. Establish `hz0 : ((hu.unit : Kˣ) : K) ∈ Om` using `by rw [IsUnit.unit_spec]; exact hz`.

Establish `hd : ((hu'.unit : Kˣ) : K) - ((hu.unit : Kˣ) : K) = l`. Rewrite using `[IsUnit.unit_spec, IsUnit.unit_spec]`. Expand and normalize the polynomial expressions, which then agree. Establish `e1 : modK R (((hu'.unit : Kˣ) : K) * ((hu'.unit : Kˣ) : K)) = modK R (((hu.unit : Kˣ) : K) * ((hu.unit : Kˣ) : K))`. Rewrite using `[(modulus_positive_multiplicative K R ψ hD hu'.unit hu'.unit).2, (modulus_positive_multiplicative K R ψ hD hu.unit hu.unit).2, IsUnit.unit_spec, IsUnit.unit_spec, hmod]`.

Establish `e2 : Kp R ψ (addBlock h s hu'.unit) (addBlock h' s hu'.unit) = Kp R ψ (addBlock h s hu.unit) (addBlock h' s hu.unit)`. Rewrite using `[hΛp h hu.unit hu'.unit hz0 (by rw [hd]; exact hlh) _, hKH K R ψ (addBlock h' s hu'.unit) (addBlock h s hu.unit), hΛp h' hu.unit hu'.unit hz0 (by rw [hd]; exact hlh') _, ← hKH K R ψ (addBlock h' s hu.unit) (addBlock h s hu.unit)]`. Rewrite using `[e1, e2]`.
-/
theorem avgDataExists_main : AvgDataExists := by
  intro hLC hKH hML hCh hLF K _ _ _ R ψ hD hn s F Om Lc hs hOm hLc
  classical
  obtain ⟨hOo, hOc, hOu, _⟩ := hOm
  have hRlat : IsLat R.toAddSubgroup := ⟨hD.isOpen, hD.isCompact⟩
  obtain ⟨L₁, hl₁, hle₁, hp₁⟩ := (hCh K R ψ hD hn).1 (Om ∪ Lc) (hOc.union hLc)
  obtain ⟨V₀, hV₀, hV₀s⟩ := compact_open_separated_add_right hOc hOo (subset_refl Om)
  obtain ⟨Λ₀, hΛ₀, hΛ₀p⟩ := hML K R ψ hD hn Om hOc hOu Set.univ Filter.univ_mem
  choose Λ hΛ hΛp using fun h : Point K => hLC K R ψ hD hn s h Om hs hOc hOu
  have hV : (V₀ ∩ (Λ₀ : Set K)) ∩ ⋂ h ∈ F, (Λ h : Set K) ∈ 𝓝 (0 : K) :=
    Filter.inter_mem (Filter.inter_mem hV₀ (lat_mem_nhds hΛ₀))
      ((Filter.biInter_finset_mem F).2 fun h _ => lat_mem_nhds (hΛ h))
  obtain ⟨L₂, hl₂, hle₂, hp₂⟩ := (hCh K R ψ hD hn).2 _ hV
  obtain ⟨A, hA⟩ := exists_reps L₂ R.toAddSubgroup (hLF K L₂ R.toAddSubgroup hl₂ hRlat)
  obtain ⟨B, hB⟩ := exists_reps R.toAddSubgroup L₁ (hLF K R.toAddSubgroup L₁ hRlat hl₁)
  refine ⟨{ L₁ := L₁, L₂ := L₂, A := A, B := B, lat₁ := hl₁, lat₂ := hl₂, le₁ := hle₁, le₂ := hle₂,
            omPerp := fun z hz => hp₁ z (Or.inl hz), cutPerp := fun z hz => hp₁ z (Or.inr hz),
            omStable := ?_, nsInv := ?_, repsA := hA, repsB := hB }⟩
  · intro z hz l hl
    exact hV₀s (Set.add_mem_add hz (hp₂ l hl).1.1)
  · intro h hh h' hh' z hz l hl
    have hlV := hp₂ l hl
    obtain ⟨hu', hmod, _⟩ := hΛ₀p z hz l hlV.1.2
    have hu := hOu z hz
    have hlh : l ∈ Λ h := by
      have := hlV.2; simp only [Set.mem_iInter] at this; exact this h hh
    have hlh' : l ∈ Λ h' := by
      have := hlV.2; simp only [Set.mem_iInter] at this; exact this h' hh'
    unfold NsK
    rw [dif_pos hu', dif_pos hu]
    unfold Ns
    have hz0 : ((hu.unit : Kˣ) : K) ∈ Om := by rw [IsUnit.unit_spec]; exact hz
    have hd : ((hu'.unit : Kˣ) : K) - ((hu.unit : Kˣ) : K) = l := by
      rw [IsUnit.unit_spec, IsUnit.unit_spec]; ring
    have e1 : modK R (((hu'.unit : Kˣ) : K) * ((hu'.unit : Kˣ) : K)) =
        modK R (((hu.unit : Kˣ) : K) * ((hu.unit : Kˣ) : K)) := by
      rw [(modulus_positive_multiplicative K R ψ hD hu'.unit hu'.unit).2,
        (modulus_positive_multiplicative K R ψ hD hu.unit hu.unit).2, IsUnit.unit_spec, IsUnit.unit_spec, hmod]
    have e2 : Kp R ψ (addBlock h s hu'.unit) (addBlock h' s hu'.unit) =
        Kp R ψ (addBlock h s hu.unit) (addBlock h' s hu.unit) := by
      rw [hΛp h hu.unit hu'.unit hz0 (by rw [hd]; exact hlh) _,
        hKH K R ψ (addBlock h' s hu'.unit) (addBlock h s hu.unit),
        hΛp h' hu.unit hu'.unit hz0 (by rw [hd]; exact hlh') _,
        ← hKH K R ψ (addBlock h' s hu.unit) (addBlock h s hu.unit)]
    rw [e1, e2]

open Classical in
/- English proof (translation)
Unfold `intLat`. Use `congr 1`. Rewrite using `[finsum_eq_sum_of_support_subset (s := hfin.toFinset)]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `y hy`.

Rewrite `hy` using `[Set.Finite.mem_toFinset]`. Conclude with `if_pos hy`. Introduce `y hy`. Assume the negation of the conclusion as `hyT`. Apply `hy` to reduce the goal to its premises.

Simplify using `only [Finset.mem_coe, Set.Finite.mem_toFinset] at hyT`. Conclude with `if_neg hyT`.
-/
theorem intLat_eq_sum {K : Type} [CommRing K] (R : Subring K) (Λ : AddSubgroup K) (Om : Set K)
    (hfin : {y : K ⧸ Λ | (Quotient.out y : K) ∈ Om}.Finite) (g : K → ℂ) :
    intLat R Λ Om g = (volL R Λ : ℂ) * ∑ y ∈ hfin.toFinset, g (Quotient.out y) := by
  unfold intLat
  congr 1
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · apply Finset.sum_congr rfl
    intro y hy
    rw [Set.Finite.mem_toFinset] at hy
    exact if_pos hy
  · intro y hy
    by_contra hyT
    apply hy
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at hyT
    exact if_neg hyT

open Classical in
/- English proof (translation)
Establish `e : ((A.card : ℂ) * (B.card : ℂ))⁻¹ * ∑ p ∈ A ×ˢ B, ψ (a * (p.1 + p.2)) = ((A.card : ℂ)⁻¹ * ∑ ρ ∈ A, ψ (a * ρ)) * ((B.card : ℂ)⁻¹ * ∑ b ∈ B, ψ (a * b))`. Rewrite using `[Finset.sum_product, mul_inv]`. Simplify using `only [mul_add, AddChar.map_add_eq_mul]`. Simplify using `only [← Finset.mul_sum, ← Finset.sum_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, hCM K ψ L₁ R.toAddSubgroup B le₁ hB a ha]`. Distinguish the cases in `hR : a ∈ perp ψ R.toAddSubgroup`. Rewrite using `[if_pos hR, mul_one, hCM K ψ R.toAddSubgroup L₂ A le₂ hA a hR]`. Rewrite using `[if_neg hR, mul_zero, if_neg]`. Introduce `h2`.

Conclude with `hR fun l hl => h2 l (le₂ hl)`.
-/
theorem mean_prod {K : Type} [CommRing K] (hCM : CharMean) (R : Subring K) (ψ : AddChar K ℂ)
    (L₁ L₂ : AddSubgroup K) (A B : Finset K) (le₁ : L₁ ≤ R.toAddSubgroup)
    (le₂ : R.toAddSubgroup ≤ L₂) (hA : IsReps A L₂ R.toAddSubgroup)
    (hB : IsReps B R.toAddSubgroup L₁) (a : K) (ha : a ∈ perp ψ L₁) :
    ((A.card : ℂ) * (B.card : ℂ))⁻¹ * ∑ p ∈ A ×ˢ B, ψ (a * (p.1 + p.2)) =
      if a ∈ perp ψ L₂ then 1 else 0 := by
  have e : ((A.card : ℂ) * (B.card : ℂ))⁻¹ * ∑ p ∈ A ×ˢ B, ψ (a * (p.1 + p.2)) =
      ((A.card : ℂ)⁻¹ * ∑ ρ ∈ A, ψ (a * ρ)) * ((B.card : ℂ)⁻¹ * ∑ b ∈ B, ψ (a * b)) := by
    rw [Finset.sum_product, mul_inv]
    simp only [mul_add, AddChar.map_add_eq_mul]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [e, hCM K ψ L₁ R.toAddSubgroup B le₁ hB a ha]
  by_cases hR : a ∈ perp ψ R.toAddSubgroup
  · rw [if_pos hR, mul_one, hCM K ψ R.toAddSubgroup L₂ A le₂ hA a hR]
  · rw [if_neg hR, mul_zero, if_neg]
    intro h2
    exact hR fun l hl => h2 l (le₂ hl)

/- English proof (translation)
Introduce `hCM hPL K _ _ _ R ψ hD hn s F Om Lc D hOc z₁ hz₁ h hh h' hh'`. Take `⟨hPlat, _, hvol⟩` from `hPL K R ψ hD hn D.L₂ D.lat₂`. Establish `hfin` using `finite_cosets (perp ψ D.L₂) hPlat.1 Om hOc`. Use `set T := hfin.toFinset with hT`. Use `set f := NsK R ψ s h h' with hf`.

Use `set c : ℂ := ((D.A.card : ℂ) * (D.B.card : ℂ))⁻¹ with hc`. Establish `hcc : conj c = c`. Rewrite using `[hc, map_inv₀, map_mul, Complex.conj_natCast, Complex.conj_natCast]`. Establish `hv : (volL R (perp ψ D.L₂) : ℂ) = (D.A.card : ℂ)⁻¹`. Establish `h1 : volL R D.L₂ = (D.A.card : ℝ)`.

Unfold `volL`. Rewrite using `[← card_reps D.L₂ R.toAddSubgroup D.A D.repsA, AddSubgroup.relIndex_eq_one.2 D.le₂]`. Simplify using the standard rewrite rules. Rewrite `hvol` using `[h1]`. Establish `: volL R (perp ψ D.L₂) = (D.A.card : ℝ)⁻¹` using `eq_inv_of_mul_eq_one_right hvol`.

Rewrite using `[this]`. Use `push_cast`. Both sides reduce to the same expression. Establish `step : ∀ p p' : K × K, ψ (-(z₁ * (p.1 + p.2))) * conj (ψ (-(z₁ * (p'.1 + p'.2)))) * intLat R (perp ψ D.L₂) Om (fun z => f z * ψ (z * ((p.1 + p.2) - (p'.1 + p'.2)))) = (volL R (perp ψ D.L₂) : ℂ) * ∑ y ∈ T, f (Quotient.out y) * (ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2)) * conj …`. Introduce `p p'`.

Rewrite using `[intLat_eq_sum R _ Om hfin, mul_left_comm, Finset.mul_sum]`. Use `congr 1`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `y _`. Establish `: ψ (-(z₁ * (p.1 + p.2))) * ψ (-(-(z₁ * (p'.1 + p'.2)))) * ψ ((Quotient.out y : K) * ((p.1 + p.2) - (p'.1 + p'.2))) = ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2)) * ψ (-(((Quotient.out y : K) - z₁) * (p'.1 + p'.2)))`.

Rewrite using `[← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hD.unitary, hD.unitary, ← this]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [step]`. Establish `swap : ∑ p ∈ D.A ×ˢ D.B, ∑ p' ∈ D.A ×ˢ D.B, (volL R (perp ψ D.L₂) : ℂ) * ∑ y ∈ T, f (Quotient.out y) * (ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2)) * conj (ψ (((Quotient.out y : K) - z₁) * (p'.1 + p'.2)))) = (volL R (perp ψ D.L₂) : ℂ) * ∑ y ∈ T, f (Quotient.out y) * ((∑ p ∈ D.A …`. Simplify using `only [← Finset.mul_sum]`. Use `congr 1`. Rewrite using `[Finset.sum_congr rfl fun p _ => Finset.sum_comm, Finset.sum_comm]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `y _`. Rewrite using `[map_sum, Finset.sum_mul_sum]`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[swap]`.

Establish `ind : ∀ y ∈ T, c * ∑ p ∈ D.A ×ˢ D.B, ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2)) = if (Quotient.out y : K) - z₁ ∈ perp ψ D.L₂ then 1 else 0`. Introduce `y hy`. Rewrite `hy` using `[hT, Set.Finite.mem_toFinset]`. Conclude with `mean_prod hCM R ψ D.L₁ D.L₂ D.A D.B D.le₁ D.le₂ D.repsA D.repsB _ ((perp ψ D.L₁).sub_mem (D.omPerp _ hy) (D.omPerp _ hz₁))`. Establish `e3 : c ^ 2 * ((volL R (perp ψ D.L₂) : ℂ) * ∑ y ∈ T, f (Quotient.out y) * ((∑ p ∈ D.A ×ˢ D.B, ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2))) * conj (∑ p ∈ D.A ×ˢ D.B, ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2))))) = (volL R (perp ψ D.L₂) : ℂ) * ∑ y ∈ T, f (Quotient.out y) * (if …`.

Rewrite using `[mul_left_comm, Finset.mul_sum]`. Use `congr 1`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `y hy`. Establish `h1` using `ind y hy`.

Apply the tactic sequence `have h3 : (if (Quotient.out y : K) - z₁ ∈ perp ψ D.L₂ then (1 : ℂ) else 0) = (if (Quotient.out y : K) - z₁ ∈ perp ψ D.L₂ then (1 : ℂ) else 0) * conj (if (Quotient.out y : K) - z₁ ∈ perp ψ D.L₂ then (1 : ℂ) else 0) := by split_ifs <;> simp`. Rewrite using `[h3, ← h1, map_mul, hcc]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e3, hv]`. Use `congr 1`.

Establish `hout` using `out_sub_mem (perp ψ D.L₂) z₁`. Establish `houteq : (Quotient.out ((z₁ : K) : K ⧸ perp ψ D.L₂) : K) = z₁ + ((Quotient.out ((z₁ : K) : K ⧸ perp ψ D.L₂) : K) - z₁)` using `by ring`. Rewrite using `[Finset.sum_eq_single ((z₁ : K) : K ⧸ perp ψ D.L₂)]`. Rewrite using `[if_pos hout, mul_one, houteq]`. Conclude with `D.nsInv h hh h' hh' z₁ hz₁ _ hout`.

Introduce `y _ hy`. Rewrite using `[if_neg, mul_zero]`. Introduce `hm`. Apply `hy` to reduce the goal to its premises. Rewrite using `[← QuotientAddGroup.out_eq' y, QuotientAddGroup.eq]`.

Use `(perp ψ D.L₂).neg_mem hm` as an intermediate fact. Simplify `this` using `[sub_eq_add_neg, add_comm]`. Introduce `hn'`. It suffices to derive a contradiction. Apply `hn'` to reduce the goal to its premises.

Rewrite using `[hT, Set.Finite.mem_toFinset]`. Use `show (Quotient.out ((z₁ : K) : K ⧸ perp ψ D.L₂) : K) ∈ Om`. Rewrite using `[houteq]`. Conclude with `D.omStable z₁ hz₁ _ hout`.
-/
theorem cutNormEval_main : CutNormEval := by
  intro hCM hPL K _ _ _ R ψ hD hn s F Om Lc D hOc z₁ hz₁ h hh h' hh'
  classical
  obtain ⟨hPlat, _, hvol⟩ := hPL K R ψ hD hn D.L₂ D.lat₂
  have hfin := finite_cosets (perp ψ D.L₂) hPlat.1 Om hOc
  set T := hfin.toFinset with hT
  set f := NsK R ψ s h h' with hf
  set c : ℂ := ((D.A.card : ℂ) * (D.B.card : ℂ))⁻¹ with hc
  have hcc : conj c = c := by
    rw [hc, map_inv₀, map_mul, Complex.conj_natCast, Complex.conj_natCast]

  have hv : (volL R (perp ψ D.L₂) : ℂ) = (D.A.card : ℂ)⁻¹ := by
    have h1 : volL R D.L₂ = (D.A.card : ℝ) := by
      unfold volL
      rw [← card_reps D.L₂ R.toAddSubgroup D.A D.repsA, AddSubgroup.relIndex_eq_one.2 D.le₂]
      simp
    rw [h1] at hvol
    have : volL R (perp ψ D.L₂) = (D.A.card : ℝ)⁻¹ := eq_inv_of_mul_eq_one_right hvol
    rw [this]; push_cast; rfl

  have step : ∀ p p' : K × K, ψ (-(z₁ * (p.1 + p.2))) * conj (ψ (-(z₁ * (p'.1 + p'.2)))) *
      intLat R (perp ψ D.L₂) Om (fun z => f z * ψ (z * ((p.1 + p.2) - (p'.1 + p'.2)))) =
      (volL R (perp ψ D.L₂) : ℂ) * ∑ y ∈ T, f (Quotient.out y) *
        (ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2)) *
          conj (ψ (((Quotient.out y : K) - z₁) * (p'.1 + p'.2)))) := by
    intro p p'
    rw [intLat_eq_sum R _ Om hfin, mul_left_comm, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro y _
    have : ψ (-(z₁ * (p.1 + p.2))) * ψ (-(-(z₁ * (p'.1 + p'.2)))) *
        ψ ((Quotient.out y : K) * ((p.1 + p.2) - (p'.1 + p'.2))) =
        ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2)) *
          ψ (-(((Quotient.out y : K) - z₁) * (p'.1 + p'.2))) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1; ring
    rw [hD.unitary, hD.unitary, ← this]
    ring
  simp only [step]
  have swap : ∑ p ∈ D.A ×ˢ D.B, ∑ p' ∈ D.A ×ˢ D.B, (volL R (perp ψ D.L₂) : ℂ) *
      ∑ y ∈ T, f (Quotient.out y) * (ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2)) *
          conj (ψ (((Quotient.out y : K) - z₁) * (p'.1 + p'.2)))) =
      (volL R (perp ψ D.L₂) : ℂ) * ∑ y ∈ T, f (Quotient.out y) *
        ((∑ p ∈ D.A ×ˢ D.B, ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2))) *
          conj (∑ p ∈ D.A ×ˢ D.B, ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2)))) := by
    simp only [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_congr rfl fun p _ => Finset.sum_comm, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [map_sum, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
  rw [swap]
  have ind : ∀ y ∈ T, c * ∑ p ∈ D.A ×ˢ D.B, ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2)) =
      if (Quotient.out y : K) - z₁ ∈ perp ψ D.L₂ then 1 else 0 := by
    intro y hy
    rw [hT, Set.Finite.mem_toFinset] at hy
    exact mean_prod hCM R ψ D.L₁ D.L₂ D.A D.B D.le₁ D.le₂ D.repsA D.repsB _
      ((perp ψ D.L₁).sub_mem (D.omPerp _ hy) (D.omPerp _ hz₁))
  have e3 : c ^ 2 * ((volL R (perp ψ D.L₂) : ℂ) * ∑ y ∈ T, f (Quotient.out y) *
        ((∑ p ∈ D.A ×ˢ D.B, ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2))) *
          conj (∑ p ∈ D.A ×ˢ D.B, ψ (((Quotient.out y : K) - z₁) * (p.1 + p.2))))) =
      (volL R (perp ψ D.L₂) : ℂ) * ∑ y ∈ T, f (Quotient.out y) *
        (if (Quotient.out y : K) - z₁ ∈ perp ψ D.L₂ then 1 else 0) := by
    rw [mul_left_comm, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro y hy
    have h1 := ind y hy
    have h3 : (if (Quotient.out y : K) - z₁ ∈ perp ψ D.L₂ then (1 : ℂ) else 0) =
        (if (Quotient.out y : K) - z₁ ∈ perp ψ D.L₂ then (1 : ℂ) else 0) *
          conj (if (Quotient.out y : K) - z₁ ∈ perp ψ D.L₂ then (1 : ℂ) else 0) := by
      split_ifs <;> simp
    rw [h3, ← h1, map_mul, hcc]
    ring
  rw [e3, hv]
  congr 1
  have hout := out_sub_mem (perp ψ D.L₂) z₁
  have houteq : (Quotient.out ((z₁ : K) : K ⧸ perp ψ D.L₂) : K) =
      z₁ + ((Quotient.out ((z₁ : K) : K ⧸ perp ψ D.L₂) : K) - z₁) := by ring
  rw [Finset.sum_eq_single ((z₁ : K) : K ⧸ perp ψ D.L₂)]
  · rw [if_pos hout, mul_one, houteq]
    exact D.nsInv h hh h' hh' z₁ hz₁ _ hout
  · intro y _ hy
    rw [if_neg, mul_zero]
    intro hm
    apply hy
    rw [← QuotientAddGroup.out_eq' y, QuotientAddGroup.eq]
    have := (perp ψ D.L₂).neg_mem hm
    simpa [sub_eq_add_neg, add_comm] using this
  · intro hn'
    exfalso
    apply hn'
    rw [hT, Set.Finite.mem_toFinset]
    show (Quotient.out ((z₁ : K) : K ⧸ perp ψ D.L₂) : K) ∈ Om
    rw [houteq]
    exact D.omStable z₁ hz₁ _ hout

end PositiveSemidefiniteClosure

/- English proof (translation)
The claim follows from `PositiveSemidefiniteClosure.uNormBound_main`.
-/
theorem averaged_vector_norm_bound : Formalism.FourierDecayAlt.A6.UNormBound := PositiveSemidefiniteClosure.uNormBound_main

/- English proof (translation)
The claim follows from `PositiveSemidefiniteClosure.cutPSD_main`.
-/
theorem cut_posSemidef : Formalism.FourierDecayAlt.A6.CutPSD := PositiveSemidefiniteClosure.cutPSD_main

/- English proof (translation)
The claim follows from `PositiveSemidefiniteClosure.uBlock_main`.
-/
theorem heads_distinct_determinant_orthogonal : Formalism.FourierDecayAlt.A6.UBlock := PositiveSemidefiniteClosure.uBlock_main

/- English proof (translation)
The claim follows from `PositiveSemidefiniteClosure.avgDataExists_main`.
-/
theorem averaged_vector_choices_exist : Formalism.FourierDecayAlt.A6.AvgDataExists := PositiveSemidefiniteClosure.avgDataExists_main

/- English proof (translation)
The claim follows from `PositiveSemidefiniteClosure.cutNormEval_main`.
-/
theorem truncated_average_norm_formula : Formalism.FourierDecayAlt.A6.CutNormEval := PositiveSemidefiniteClosure.cutNormEval_main

end Formalism.FourierDecayAlt.P
