import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ImportsFurther
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartRankAdjoin
import GroundTheory.ArithmeticGeometry.ToricVarieties.Dimension
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

namespace OneBlockPointDeg

variable {Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ'] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {k₀ : K}

/- English proof (translation)
Introduce `m hm k`. Establish `h` using `hf (mem_support_iff.mp hm)`. Rewrite `h` using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]`. Simplify using `only [Pi.one_apply, smul_eq_mul, mul_one] at h`. Rewrite `h` using `[Fintype.sum_sigma, Fintype.sum_eq_single k (fun k' hk' => absurd ((hK k').trans (hK k).symm) hk')]`.

Conclude with `h`.
-/
theorem isMultiHomog_of_isHomogeneous (hK : ∀ k, k = k₀) {f : MRingOver Φ ι} {n : ℕ}
    (hf : f.IsHomogeneous n) : IsMultiHomog f fun _ => n := by
  intro m hm k
  have h := hf (mem_support_iff.mp hm)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
  simp only [Pi.one_apply, smul_eq_mul, mul_one] at h
  rw [Fintype.sum_sigma, Fintype.sum_eq_single k
    (fun k' hk' => absurd ((hK k').trans (hK k).symm) hk')] at h
  exact h

/- English proof (translation)
Establish `hz : ∀ k, w ⟨k, c k⟩ ≠ 0` using `fun k => by obtain rfl := hK k; exact hc`. Establish `e : (fun p : Σ k, ι k => w p / w ⟨k₀, c k₀⟩) = Inter.ChartRankAdjoin.affCoord w c`. Use function extensionality and compare the values at `⟨k, i⟩`. Take `rfl` from `hK k`. Both sides reduce to the same expression.

Establish `h` using `Inter.ChartRankAdjoin.aeval_mul_of_isMultiHomog hz (isMultiHomog_of_isHomogeneous hK hg)`. Rewrite `h` using `[Fintype.prod_eq_single k₀ (fun k hk => absurd (hK k) hk), ← e]`. Then use the resulting hypothesis.
-/
theorem aeval_homog (hK : ∀ k, k = k₀) {w : (Σ k, ι k) → Φ'} {c : ∀ k, ι k} (hc : w ⟨k₀, c k₀⟩ ≠ 0)
    {g : MRingOver Φ ι} {n : ℕ} (hg : g.IsHomogeneous n) :
    aeval (fun p => w p / w ⟨k₀, c k₀⟩) g * w ⟨k₀, c k₀⟩ ^ n = aeval w g := by
  classical
  have hz : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => by obtain rfl := hK k; exact hc
  have e : (fun p : Σ k, ι k => w p / w ⟨k₀, c k₀⟩) = Inter.ChartRankAdjoin.affCoord w c := by
    funext ⟨k, i⟩; obtain rfl := hK k; rfl
  have h := Inter.ChartRankAdjoin.aeval_mul_of_isMultiHomog hz (isMultiHomog_of_isHomogeneous hK hg)
  rwa [Fintype.prod_eq_single k₀ (fun k hk => absurd (hK k) hk), ← e] at h

/- English proof (translation)
Establish `hAB : Algebra.adjoin Φ (Set.range w) ≤ (Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ`. Rewrite using `[← Algebra.adjoin_union_eq_adjoin_adjoin]`. Conclude with `Algebra.adjoin_le hs`. Set `_ : Algebra (Algebra.adjoin Φ (Set.range w)) ((Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ)` to `(Subalgebra.inclusion hAB).toRingHom.toAlgebra`. Set `f : (Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ →ₐ[Algebra.adjoin Φ (Set.range w)] Φ'` to `{ ((Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ).val.toRingHom with commutes' := fun _ => rfl }`.

Establish `hint : Algebra.IsIntegral (Algebra.adjoin Φ (Set.range w)) ((Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ)` using `⟨fun b => by`. Use `(isIntegral_algHom_iff f Subtype.val_injective).mp ?_` and prove the remaining obligations. Establish `hb : (b : Φ') ∈ Algebra.adjoin Φ (s ∪ {x})`. Rewrite using `[Algebra.adjoin_union_eq_adjoin_adjoin]`. Conclude with `b.2`.

Use `(Algebra.adjoin_le (S := (integralClosure (Algebra.adjoin Φ (Set.range w)) Φ').restrictScalars Φ) ?_) hb` and prove the remaining obligations. Introduce and unpack `y (hy | hy)`. Conclude with `((IsIntegral.of_finite Φ (⟨y, Algebra.subset_adjoin hy⟩ : Algebra.adjoin Φ s)).map (Algebra.adjoin Φ s).val).tower_top`. Rewrite using `[Set.mem_singleton_iff.mp hy]`. Conclude with `isIntegral_algebraMap (x := (⟨x, hx⟩ : Algebra.adjoin Φ (Set.range w)))⟩`.

Establish `: IsArtinianRing (Algebra.adjoin Φ s)` using `IsArtinianRing.of_finite Φ _`. Establish `: IsNoetherianRing (Algebra.adjoin Φ s)` using `IsNoetherianRing.of_finite Φ _`. Rewrite using `[← GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral (Subalgebra.inclusion_injective hAB)]`. Express the relevant statement in the definitionally equal form `ringKrullDim (Algebra.adjoin (Algebra.adjoin Φ s) {x}) = 1`. Rewrite using `[← ringKrullDim_eq_of_ringEquiv (Polynomial.algEquivOfTranscendental (s := x) (h := htr)).toRingEquiv, Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_isField (IsArtinianRing.isField_of_isDomain _)]`.

Both sides reduce to the same expression.
-/
theorem ringKrullDim_adjoin_eq_one {σ : Type} (w : σ → Φ') (s : Set Φ') (x : Φ')
    [Module.Finite Φ (Algebra.adjoin Φ s)] (htr : Transcendental (Algebra.adjoin Φ s) x)
    (hx : x ∈ Algebra.adjoin Φ (Set.range w)) (hs : Set.range w ⊆ Algebra.adjoin Φ (s ∪ {x})) :
    ringKrullDim (Algebra.adjoin Φ (Set.range w)) = 1 := by
  have hAB : Algebra.adjoin Φ (Set.range w) ≤ (Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ := by
    rw [← Algebra.adjoin_union_eq_adjoin_adjoin]; exact Algebra.adjoin_le hs
  let _ : Algebra (Algebra.adjoin Φ (Set.range w)) ((Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ) :=
    (Subalgebra.inclusion hAB).toRingHom.toAlgebra
  let f : (Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ →ₐ[Algebra.adjoin Φ (Set.range w)] Φ' :=
    { ((Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ).val.toRingHom with commutes' := fun _ => rfl }
  have hint : Algebra.IsIntegral (Algebra.adjoin Φ (Set.range w))
      ((Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ) := ⟨fun b => by
    refine (isIntegral_algHom_iff f Subtype.val_injective).mp ?_
    have hb : (b : Φ') ∈ Algebra.adjoin Φ (s ∪ {x}) := by
      rw [Algebra.adjoin_union_eq_adjoin_adjoin]; exact b.2
    refine (Algebra.adjoin_le (S := (integralClosure (Algebra.adjoin Φ (Set.range w)) Φ').restrictScalars Φ) ?_) hb
    rintro y (hy | hy)
    · exact ((IsIntegral.of_finite Φ (⟨y, Algebra.subset_adjoin hy⟩ : Algebra.adjoin Φ s)).map
        (Algebra.adjoin Φ s).val).tower_top
    · rw [Set.mem_singleton_iff.mp hy]
      exact isIntegral_algebraMap (x := (⟨x, hx⟩ : Algebra.adjoin Φ (Set.range w)))⟩
  have : IsArtinianRing (Algebra.adjoin Φ s) := IsArtinianRing.of_finite Φ _
  have : IsNoetherianRing (Algebra.adjoin Φ s) := IsNoetherianRing.of_finite Φ _
  rw [← GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral (Subalgebra.inclusion_injective hAB)]
  change ringKrullDim (Algebra.adjoin (Algebra.adjoin Φ s) {x}) = 1
  rw [← ringKrullDim_eq_of_ringEquiv (Polynomial.algEquivOfTranscendental (s := x) (h := htr)).toRingEquiv,
    Polynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_isField (IsArtinianRing.isField_of_isDomain _)]
  rfl

end OneBlockPointDeg

open OneBlockPointDeg in

/- English proof (translation)
Introduce `Φ Φ' _ _ _ K _ ι _ k₀ hK w c hc hfin htr`. Use `set r : (Σ k, ι k) → Φ' := fun p => w p / w ⟨k₀, c k₀⟩ with hr`. Use `set L := Algebra.adjoin Φ (Set.range r) with hL`. Establish `hz : ∀ k, w ⟨k, c k⟩ ≠ 0` using `fun k => by obtain rfl := hK k; exact hc`. Establish `hcard : Fintype.card K = 1` using `Fintype.card_eq_one_iff.mpr ⟨k₀, hK⟩`.

Establish `hrL : ∀ p, r p ∈ L` using `fun p => Algebra.subset_adjoin ⟨p, rfl⟩`. Establish `hcomp : ∀ f ∈ RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ'), ∀ n, homogeneousComponent n f ∈ RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')`. Introduce `f hf n`. Establish `hmem : ∀ g : MRingOver Φ ι, aeval r g ∈ L` using `fun g => by`. Rewrite using `[hL, ← aeval_range]`.

Conclude with `AlgHom.mem_range_self _ g`. Set `P : Polynomial L` to `∑ i ∈ Finset.range (f.totalDegree + 1), Polynomial.monomial i ⟨aeval r (homogeneousComponent i f), hmem _⟩`. Establish `hP : Polynomial.aeval (w ⟨k₀, c k₀⟩) P = 0`. Establish `h0` using `RingHom.mem_ker.mp hf`. Rewrite `h0` using `[← sum_homogeneousComponent f, map_sum]`.

Rewrite using `[← h0, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Polynomial.aeval_monomial, ← aeval_homog hK hc (homogeneousComponent_isHomogeneous i f)]`. Both sides reduce to the same expression. Establish `hP0` using `(transcendental_iff.mp htr) P hP`.

Rewrite using `[RingHom.mem_ker, ← aeval_homog hK hc (homogeneousComponent_isHomogeneous n f)]`. Distinguish the cases in `hn : n < f.totalDegree + 1`. Establish `h1` using `congrArg (fun q : Polynomial L => q.coeff n) hP0`. Simplify using `only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range, hn, if_true, Polynomial.coeff_zero] at h1`. Rewrite using `[show aeval r (homogeneousComponent n f) = ((⟨_, hmem _⟩ : L) : Φ') from rfl, h1]`.

Simplify using the standard rewrite rules. Rewrite using `[homogeneousComponent_eq_zero (φ := f) (n := n) (by omega)]; simp`. Establish `hchart : IsChart (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')) c` using `fun k => by`. Rewrite using `[RingHom.mem_ker, aeval_X]`. Conclude with `hz k`.

Establish `hhom : IsMultiHomogIdeal (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ'))`. Use `⟨{g | g ∈ RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ') ∧ ∃ a, IsMultiHomog g a}, fun g hg => hg.2, le_antisymm (fun f hf => ?_) (Ideal.span_le.mpr fun g hg => hg.1)⟩` and prove the remaining obligations. Rewrite using `[← sum_homogeneousComponent f]`. Conclude with `Ideal.sum_mem _ fun i _ => Ideal.subset_span ⟨hcomp f hf i, _, isMultiHomog_of_isHomogeneous hK (homogeneousComponent_isHomogeneous i f)⟩`. Use `⟨⟨⟨RingHom.ker_isPrime _, hhom, fun k => ⟨c k, hchart k⟩⟩, ?_⟩, hchart, ?_⟩` and prove the remaining obligations.

Establish `hs : Set.range w ⊆ Algebra.adjoin Φ (Set.range r ∪ {w ⟨k₀, c k₀⟩})`. Introduce and unpack `_ ⟨p, rfl⟩`. Rewrite using `[show w p = r p * w ⟨k₀, c k₀⟩ from (div_mul_cancel₀ _ hc).symm]`. Conclude with `Subalgebra.mul_mem _ (Algebra.subset_adjoin (Or.inl ⟨p, rfl⟩)) (Algebra.subset_adjoin (Or.inr rfl))`. Rewrite using `[ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')).toRingEquiv, aeval_range, ringKrullDim_adjoin_eq_one w (Set.range r) _ htr (Algebra.subset_adjoin ⟨_, rfl⟩) hs, hcard]`.

Both sides reduce to the same expression. Establish `halg : ∀ x ∈ Set.range r, IsAlgebraic Φ x`. Introduce and unpack `_ ⟨p, rfl⟩`. Conclude with `(IsAlgebraic.of_finite Φ (⟨r p, hrL p⟩ : L)).algHom L.val`. Establish `e : (fun q : Σ k, ι k => w q / w ⟨q.1, c q.1⟩) = r`.

Use function extensionality and compare the values at `⟨k, i⟩`. Take `rfl` from `hK k`. Both sides reduce to the same expression. Rewrite using `[Inter.ChartRankAdjoin.proof K ι Φ Φ' w c hz hhom, e, ← IntermediateField.finrank_eq_finrank_subalgebra, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]`.
-/
theorem OneBlockPointDeg.proof : OneBlockPointDeg.Statement := by
  classical
  intro Φ Φ' _ _ _ K _ ι _ k₀ hK w c hc hfin htr
  set r : (Σ k, ι k) → Φ' := fun p => w p / w ⟨k₀, c k₀⟩ with hr
  set L := Algebra.adjoin Φ (Set.range r) with hL
  have hz : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => by obtain rfl := hK k; exact hc
  have hcard : Fintype.card K = 1 := Fintype.card_eq_one_iff.mpr ⟨k₀, hK⟩
  have hrL : ∀ p, r p ∈ L := fun p => Algebra.subset_adjoin ⟨p, rfl⟩

  have hcomp : ∀ f ∈ RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ'), ∀ n,
      homogeneousComponent n f ∈ RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ') := by
    intro f hf n
    have hmem : ∀ g : MRingOver Φ ι, aeval r g ∈ L := fun g => by
      rw [hL, ← aeval_range]; exact AlgHom.mem_range_self _ g
    let P : Polynomial L := ∑ i ∈ Finset.range (f.totalDegree + 1),
      Polynomial.monomial i ⟨aeval r (homogeneousComponent i f), hmem _⟩
    have hP : Polynomial.aeval (w ⟨k₀, c k₀⟩) P = 0 := by
      have h0 := RingHom.mem_ker.mp hf
      rw [← sum_homogeneousComponent f, map_sum] at h0
      rw [← h0, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.aeval_monomial, ← aeval_homog hK hc (homogeneousComponent_isHomogeneous i f)]
      rfl
    have hP0 := (transcendental_iff.mp htr) P hP
    rw [RingHom.mem_ker, ← aeval_homog hK hc (homogeneousComponent_isHomogeneous n f)]
    by_cases hn : n < f.totalDegree + 1
    · have h1 := congrArg (fun q : Polynomial L => q.coeff n) hP0
      simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq',
        Finset.mem_range, hn, if_true, Polynomial.coeff_zero] at h1
      rw [show aeval r (homogeneousComponent n f) = ((⟨_, hmem _⟩ : L) : Φ') from rfl, h1]
      simp
    · rw [homogeneousComponent_eq_zero (φ := f) (n := n) (by omega)]; simp
  have hchart : IsChart (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')) c := fun k => by
    rw [RingHom.mem_ker, aeval_X]; exact hz k

  have hhom : IsMultiHomogIdeal (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')) := by
    refine ⟨{g | g ∈ RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ') ∧ ∃ a, IsMultiHomog g a}, fun g hg => hg.2,
      le_antisymm (fun f hf => ?_)
      (Ideal.span_le.mpr fun g hg => hg.1)⟩
    rw [← sum_homogeneousComponent f]
    exact Ideal.sum_mem _ fun i _ => Ideal.subset_span
      ⟨hcomp f hf i, _, isMultiHomog_of_isHomogeneous hK (homogeneousComponent_isHomogeneous i f)⟩
  refine ⟨⟨⟨RingHom.ker_isPrime _, hhom, fun k => ⟨c k, hchart k⟩⟩, ?_⟩, hchart, ?_⟩
  ·
    have hs : Set.range w ⊆ Algebra.adjoin Φ (Set.range r ∪ {w ⟨k₀, c k₀⟩}) := by
      rintro _ ⟨p, rfl⟩
      rw [show w p = r p * w ⟨k₀, c k₀⟩ from (div_mul_cancel₀ _ hc).symm]
      exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Or.inl ⟨p, rfl⟩))
        (Algebra.subset_adjoin (Or.inr rfl))
    rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')).toRingEquiv,
      aeval_range, ringKrullDim_adjoin_eq_one w (Set.range r) _ htr (Algebra.subset_adjoin ⟨_, rfl⟩) hs, hcard]
    rfl
  ·
    have halg : ∀ x ∈ Set.range r, IsAlgebraic Φ x := by
      rintro _ ⟨p, rfl⟩
      exact (IsAlgebraic.of_finite Φ (⟨r p, hrL p⟩ : L)).algHom L.val
    have e : (fun q : Σ k, ι k => w q / w ⟨q.1, c q.1⟩) = r := by
      funext ⟨k, i⟩; obtain rfl := hK k; rfl
    rw [Inter.ChartRankAdjoin.proof K ι Φ Φ' w c hz hhom, e,
      ← IntermediateField.finrank_eq_finrank_subalgebra,
      IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]

end

end GroundTheory.Heights₂.Heights
