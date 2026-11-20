import Mathlib
import GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainImageOfMapVecLattice
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual

open NumberField MeasureTheory Topology Set Filter IsDedekindDomain
open scoped NumberField.AdeleRing FourierTransform

namespace GroundTheory.Automorphic

noncomputable section

namespace FourierWhittaker

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

def pair (ξ : ι → K) (x : ι → 𝔸[K]) : 𝔸[K] := ∑ i, algebraMap K 𝔸[K] (ξ i) * x i

/- English proof (translation)
Simplify using `[pair, mul_add, Finset.sum_add_distrib]`.
-/
theorem pair_add (ξ : ι → K) (x y : ι → 𝔸[K]) : pair ξ (x + y) = pair ξ x + pair ξ y := by
  simp [pair, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[pair, Finset.sum_neg_distrib]`.
-/
theorem pair_neg (ξ : ι → K) (x : ι → 𝔸[K]) : pair ξ (-x) = -pair ξ x := by
  simp [pair, Finset.sum_neg_distrib]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, pair_add, pair_neg, ← sub_eq_add_neg]`.
-/
theorem pair_sub (ξ : ι → K) (x y : ι → 𝔸[K]) : pair ξ (x - y) = pair ξ x - pair ξ y := by
  rw [sub_eq_add_neg, pair_add, pair_neg, ← sub_eq_add_neg]

/- English proof (translation)
Simplify using `[pair]`.
-/
theorem pair_zero (ξ : ι → K) : pair ξ (0 : ι → 𝔸[K]) = 0 := by simp [pair]

/- English proof (translation)
Simplify using `[pair, map_sum]`.
-/
theorem pair_algebraMap (ξ η : ι → K) :
    pair ξ (fun i => algebraMap K 𝔸[K] (η i)) = algebraMap K 𝔸[K] (∑ i, ξ i * η i) := by
  simp [pair, map_sum]

/- English proof (translation)
Take `⟨η, rfl⟩` from `mem_vecLattice.1 hx`. Rewrite using `[pair_algebraMap, GroundTheory.Global.adelicChar_algebraMap]`.
-/
theorem adelicChar_pair_of_mem (ξ : ι → K) {x : ι → 𝔸[K]} (hx : x ∈ vecLattice K ι) :
    GroundTheory.Global.adelicChar K (pair ξ x) = 1 := by
  obtain ⟨η, rfl⟩ := mem_vecLattice.1 hx
  rw [pair_algebraMap, GroundTheory.Global.adelicChar_algebraMap]

/- English proof (translation)
The claim follows from `continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)`.
-/
theorem continuous_pair (ξ : ι → K) : Continuous (pair ξ) :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)

/- English proof (translation)
The claim follows from `continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_pair ξ).neg)`.
-/
theorem continuous_adelicChar_neg_pair (ξ : ι → K) :
    Continuous fun x : ι → 𝔸[K] => (GroundTheory.Global.adelicChar K (-pair ξ x) : ℂ) :=
  continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_pair ξ).neg)

def vecCoeff (f : (ι → 𝔸[K]) → ℂ) (ξ : ι → K) : ℂ :=
  ∫ x in vecDomain K ι, f x * (GroundTheory.Global.adelicChar K (-pair ξ x) : ℂ) ∂vecMeasure K ι

/- English proof (translation)
Establish `himg : (· + a) '' vecDomain K ι = (· - a) ⁻¹' vecDomain K ι`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Simplify using `using hx`.

Introduce `hy`. Conclude with `⟨y - a, hy, by simp⟩`. Use `IsAddFundamentalDomain.mk' ?_ fun x => ?_` and prove the remaining obligations. Rewrite using `[himg]`. Conclude with `(measurableSet_vecDomain.preimage (measurable_id.sub_const a)).nullMeasurableSet`.

Take `⟨g, hg, huniq⟩` from `existsUnique_vadd_mem_vecDomain (K := K) (ι := ι) (x - a)`. Use `⟨g, ?_, fun g' hg' => huniq g' ?_⟩` and prove the remaining obligations. Rewrite using `[himg]`. Express the relevant statement in the definitionally equal form `(g : ι → 𝔸[K]) + x - a ∈ vecDomain K ι`. Rewrite using `[add_sub_assoc]`.

Conclude with `hg`. Rewrite `hg'` using `[himg]`. Express the relevant statement in the definitionally equal form `(g' : ι → 𝔸[K]) + x - a ∈ vecDomain K ι at hg'`. Rewrite `hg'` using `[add_sub_assoc]`. Conclude with `hg'`.
-/
theorem isAddFundamentalDomain_image_add (a : ι → 𝔸[K]) :
    IsAddFundamentalDomain (vecLattice K ι) ((· + a) '' vecDomain K ι) (vecMeasure K ι) := by
  have himg : (· + a) '' vecDomain K ι = (· - a) ⁻¹' vecDomain K ι := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨y - a, hy, by simp⟩
  refine IsAddFundamentalDomain.mk' ?_ fun x => ?_
  · rw [himg]
    exact (measurableSet_vecDomain.preimage (measurable_id.sub_const a)).nullMeasurableSet
  · obtain ⟨g, hg, huniq⟩ := existsUnique_vadd_mem_vecDomain (K := K) (ι := ι) (x - a)
    refine ⟨g, ?_, fun g' hg' => huniq g' ?_⟩
    · rw [himg]
      change (g : ι → 𝔸[K]) + x - a ∈ vecDomain K ι
      rw [add_sub_assoc]
      exact hg
    · rw [himg] at hg'
      change (g' : ι → 𝔸[K]) + x - a ∈ vecDomain K ι at hg'
      rw [add_sub_assoc] at hg'
      exact hg'

/- English proof (translation)
Establish `hmp : MeasurePreserving (· + a) (vecMeasure K ι) (vecMeasure K ι)` using `measurePreserving_add_right _ a`. Establish `hme : MeasurableEmbedding (· + a : (ι → 𝔸[K]) → ι → 𝔸[K])` using `(Homeomorph.addRight a).measurableEmbedding`. Rewrite using `[← hmp.setIntegral_image_emb hme h]`. Conclude with `(isAddFundamentalDomain_image_add a).setIntegral_eq isAddFundamentalDomain_vecDomain fun g x => hh g g.2 x`.
-/
theorem setIntegral_comp_add (a : ι → 𝔸[K]) {h : (ι → 𝔸[K]) → ℂ}
    (hh : ∀ ξ ∈ vecLattice K ι, ∀ x, h (ξ + x) = h x) :
    ∫ x in vecDomain K ι, h (x + a) ∂vecMeasure K ι = ∫ x in vecDomain K ι, h x ∂vecMeasure K ι := by
  have hmp : MeasurePreserving (· + a) (vecMeasure K ι) (vecMeasure K ι) :=
    measurePreserving_add_right _ a
  have hme : MeasurableEmbedding (· + a : (ι → 𝔸[K]) → ι → 𝔸[K]) :=
    (Homeomorph.addRight a).measurableEmbedding
  rw [← hmp.setIntegral_image_emb hme h]
  exact (isAddFundamentalDomain_image_add a).setIntegral_eq isAddFundamentalDomain_vecDomain
    fun g x => hh g g.2 x

/- English proof (translation)
Use `set h : (ι → 𝔸[K]) → ℂ := fun x => f x * (GroundTheory.Global.adelicChar K (-pair ξ x) : ℂ)`. Establish `hinv : ∀ y : 𝔸[K], (GroundTheory.Global.adelicChar K y : ℂ) * GroundTheory.Global.adelicChar K (-y) = 1` using `fun y => by rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, Circle.coe_one]`. Establish `hh : ∀ l ∈ vecLattice K ι, ∀ x, h (l + x) = h x`. Introduce `l hl x`. Establish `h1 : GroundTheory.Global.adelicChar K (-pair ξ l) = 1`.

Rewrite using `[← pair_neg]`. Conclude with `adelicChar_pair_of_mem ξ (neg_mem hl)`. Simplify using `only [h, hf l hl x, pair_add, neg_add, AddChar.map_add_eq_mul, h1, one_mul]`. Establish `e : ∀ x, f (x + a) * (GroundTheory.Global.adelicChar K (-pair ξ x) : ℂ) = GroundTheory.Global.adelicChar K (pair ξ a) * h (x + a)`. Introduce `x`.

Simplify using `only [h, pair_add, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]`. Take the linear combination `(-(f (x + a) * (GroundTheory.Global.adelicChar K (-pair ξ x) : ℂ))) * hinv (pair ξ a)`. Unfold `vecCoeff`. Repeatedly rewrite using `[e]`. Rewrite using `[integral_const_mul, setIntegral_comp_add a hh]`.
-/
theorem vecCoeff_translate {f : (ι → 𝔸[K]) → ℂ} (hf : ∀ ξ ∈ vecLattice K ι, ∀ x, f (ξ + x) = f x)
    (a : ι → 𝔸[K]) (ξ : ι → K) :
    vecCoeff (fun x => f (x + a)) ξ = GroundTheory.Global.adelicChar K (pair ξ a) * vecCoeff f ξ := by
  set h : (ι → 𝔸[K]) → ℂ := fun x => f x * (GroundTheory.Global.adelicChar K (-pair ξ x) : ℂ)
  have hinv : ∀ y : 𝔸[K], (GroundTheory.Global.adelicChar K y : ℂ) * GroundTheory.Global.adelicChar K (-y) = 1 :=
    fun y => by rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, add_neg_cancel,
      AddChar.map_zero_eq_one, Circle.coe_one]
  have hh : ∀ l ∈ vecLattice K ι, ∀ x, h (l + x) = h x := by
    intro l hl x
    have h1 : GroundTheory.Global.adelicChar K (-pair ξ l) = 1 := by
      rw [← pair_neg]
      exact adelicChar_pair_of_mem ξ (neg_mem hl)
    simp only [h, hf l hl x, pair_add, neg_add, AddChar.map_add_eq_mul, h1, one_mul]
  have e : ∀ x, f (x + a) * (GroundTheory.Global.adelicChar K (-pair ξ x) : ℂ) =
      GroundTheory.Global.adelicChar K (pair ξ a) * h (x + a) := by
    intro x
    simp only [h, pair_add, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
    linear_combination (-(f (x + a) * (GroundTheory.Global.adelicChar K (-pair ξ x) : ℂ))) *
      hinv (pair ξ a)
  unfold vecCoeff
  simp_rw [e]
  rw [integral_const_mul, setIntegral_comp_add a hh]

/- English proof (translation)
Establish `hμ : vecMeasure K ι (vecDomain K ι) < ⊤` using `by rw [vecMeasure_vecDomain]; exact ENNReal.one_lt_top`. Use `norm_setIntegral_le_of_norm_le_const (f := fun x => f x * (GroundTheory.Global.adelicChar K (-pair ξ x) : ℂ)) hμ (C := C) fun x hx => by` as an intermediate fact. Rewrite using `[norm_mul, Circle.norm_coe, mul_one]`. Conclude with `hC x hx`. Rewrite `this` using `[measureReal_def, vecMeasure_vecDomain, ENNReal.toReal_one, mul_one]`. Then use the resulting hypothesis.
-/
theorem norm_vecCoeff_le {f : (ι → 𝔸[K]) → ℂ} {C : ℝ} (hC : ∀ x ∈ vecDomain K ι, ‖f x‖ ≤ C)
    (ξ : ι → K) : ‖vecCoeff f ξ‖ ≤ C := by
  have hμ : vecMeasure K ι (vecDomain K ι) < ⊤ := by rw [vecMeasure_vecDomain]; exact ENNReal.one_lt_top
  have := norm_setIntegral_le_of_norm_le_const (f := fun x =>
    f x * (GroundTheory.Global.adelicChar K (-pair ξ x) : ℂ)) hμ (C := C) fun x hx => by
      rw [norm_mul, Circle.norm_coe, mul_one]; exact hC x hx
  rwa [measureReal_def, vecMeasure_vecDomain, ENNReal.toReal_one, mul_one] at this

def IsDual (ξ : ι → K) : Prop :=
  ∀ i, algebraMap K (FiniteAdeleRing (𝓞 K) K) (ξ i) ∈ GroundTheory.Global.finiteInvDifferent K

/- English proof (translation)
Establish `e : GroundTheory.Global.finiteAdeleInr (algebraMap K (FiniteAdeleRing (𝓞 K) K) q) = algebraMap K 𝔸[K] q + GroundTheory.Global.infiniteAdeleInl (-algebraMap K (InfiniteAdeleRing K) q)`. Use `Prod.ext (α := InfiniteAdeleRing K) (β := FiniteAdeleRing (𝓞 K) K) ?_ ?_` and prove the remaining obligations. Use `show (0 : InfiniteAdeleRing K) = algebraMap K (InfiniteAdeleRing K) q + -algebraMap K (InfiniteAdeleRing K) q`. Rewrite using `[add_neg_cancel]`. Use `show algebraMap K (FiniteAdeleRing (𝓞 K) K) q = algebraMap K (FiniteAdeleRing (𝓞 K) K) q + 0`.

Rewrite using `[add_zero]`. Rewrite using `[e, AddChar.map_add_eq_mul, GroundTheory.Global.adelicChar_algebraMap, one_mul]`. Use `GroundTheory.Global.adelicChar_infinite (K := K) (-algebraMap K (InfiniteAdeleRing K) q)` as an intermediate fact. Rewrite `this` using `[map_neg (GroundTheory.Global.infiniteTrace K), neg_neg, GroundTheory.Global.infiniteTrace_algebraMap]`. Conclude with `this`.
-/
theorem adelicChar_finiteAdeleInr_algebraMap (q : K) :
    GroundTheory.Global.adelicChar K
      (GroundTheory.Global.finiteAdeleInr (algebraMap K (FiniteAdeleRing (𝓞 K) K) q)) =
      𝐞 (Algebra.trace ℚ K q : ℝ) := by
  have e : GroundTheory.Global.finiteAdeleInr (algebraMap K (FiniteAdeleRing (𝓞 K) K) q) =
      algebraMap K 𝔸[K] q + GroundTheory.Global.infiniteAdeleInl (-algebraMap K (InfiniteAdeleRing K) q) := by
    refine Prod.ext (α := InfiniteAdeleRing K) (β := FiniteAdeleRing (𝓞 K) K) ?_ ?_
    · show (0 : InfiniteAdeleRing K) = algebraMap K (InfiniteAdeleRing K) q +
        -algebraMap K (InfiniteAdeleRing K) q
      rw [add_neg_cancel]
    · show algebraMap K (FiniteAdeleRing (𝓞 K) K) q = algebraMap K (FiniteAdeleRing (𝓞 K) K) q + 0
      rw [add_zero]
  rw [e, AddChar.map_add_eq_mul, GroundTheory.Global.adelicChar_algebraMap, one_mul]
  have := GroundTheory.Global.adelicChar_infinite (K := K) (-algebraMap K (InfiniteAdeleRing K) q)
  rw [map_neg (GroundTheory.Global.infiniteTrace K), neg_neg, GroundTheory.Global.infiniteTrace_algebraMap] at this
  exact this

/- English proof (translation)
Introduce `v` and use `GroundTheory.Global.mul_mem_localInvDifferent (hz v) (ha v)`.
-/
theorem mul_mem_finiteInvDifferent {a z : FiniteAdeleRing (𝓞 K) K}
    (ha : a ∈ GroundTheory.Global.finiteInvDifferent K) (hz : z ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) :
    z * a ∈ GroundTheory.Global.finiteInvDifferent K :=
  fun v => GroundTheory.Global.mul_mem_localInvDifferent (hz v) (ha v)

/- English proof (translation)
Simplify using `[pair, GroundTheory.Global.algebraMap_mul_finiteAdeleInr, map_sum]`.
-/
theorem pair_finiteAdeleInr (ξ : ι → K) (z : ι → FiniteAdeleRing (𝓞 K) K) :
    pair ξ (fun i => GroundTheory.Global.finiteAdeleInr (z i)) =
      GroundTheory.Global.finiteAdeleInr (∑ i, algebraMap K (FiniteAdeleRing (𝓞 K) K) (ξ i) * z i) := by
  simp [pair, GroundTheory.Global.algebraMap_mul_finiteAdeleInr, map_sum]

/- English proof (translation)
Rewrite using `[pair_finiteAdeleInr, GroundTheory.Global.adelicChar_of_mem_invDifferentAdeles]`. Use `show 𝐞 (-(GroundTheory.Global.infiniteTrace K) 0) = 1`. Simplify using the standard rewrite rules. Rewrite using `[GroundTheory.Global.mem_invDifferentAdeles, GroundTheory.Global.finiteAdeleInr_snd]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_comm]`. Conclude with `mul_mem_finiteInvDifferent (hξ i) (hz i)`.
-/
theorem adelicChar_pair_finiteAdeleInr {ξ : ι → K} (hξ : IsDual ξ)
    {z : ι → FiniteAdeleRing (𝓞 K) K} (hz : ∀ i, z i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) :
    GroundTheory.Global.adelicChar K (pair ξ fun i => GroundTheory.Global.finiteAdeleInr (z i)) = 1 := by
  rw [pair_finiteAdeleInr, GroundTheory.Global.adelicChar_of_mem_invDifferentAdeles]
  · show 𝐞 (-(GroundTheory.Global.infiniteTrace K) 0) = 1
    simp
  · rw [GroundTheory.Global.mem_invDifferentAdeles, GroundTheory.Global.finiteAdeleInr_snd]
    refine sum_mem fun i _ => ?_
    rw [mul_comm]
    exact mul_mem_finiteInvDifferent (hξ i) (hz i)

/- English proof (translation)
Simplify using `only [IsDual, not_forall] at hξ`. Take `⟨i, hi⟩` from `hξ`. Rewrite `hi` using `[GroundTheory.Global.algebraMap_mem_finiteInvDifferent_iff]`. Use `push Not at hi`. Take `⟨a, ha⟩` from `hi`.

Use `set z : ι → FiniteAdeleRing (𝓞 K) K := Pi.single i (algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K a))`. Establish `hz : ∀ j, z j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K`. Introduce `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Simplify using `only [z, Pi.single_eq_same]`. Conclude with `fun v => GroundTheory.Global.coe_algebraMap_mem_adicCompletionIntegers v a`. Simplify using `only [z, Pi.single_eq_of_ne hj]`. Conclude with `zero_mem _`. Establish `h1` using `vecCoeff_translate hper (fun j => GroundTheory.Global.finiteAdeleInr (z j)) ξ`.

Establish `h2 : (fun x => f (x + fun j => GroundTheory.Global.finiteAdeleInr (z j))) = f`. Use function extensionality and compare the values at `fun x => hfin x z hz`. Rewrite `h1` using `[h2, pair_finiteAdeleInr]`. Establish `h3 : ∑ j, algebraMap K (FiniteAdeleRing (𝓞 K) K) (ξ j) * z j = algebraMap K (FiniteAdeleRing (𝓞 K) K) (ξ i * algebraMap (𝓞 K) K a)`. Rewrite using `[Finset.sum_eq_single i]`.

Simplify using `[z, map_mul]`. Introduce `j _ hj`. Simplify using `[z, Pi.single_eq_of_ne hj]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[h3, adelicChar_finiteAdeleInr_algebraMap]`.

Establish `hne : (𝐞 (Algebra.trace ℚ K (ξ i * algebraMap (𝓞 K) K a) : ℝ) : ℂ) ≠ 1`. Introduce `h`. Establish `h' : 𝐞 (Algebra.trace ℚ K (ξ i * algebraMap (𝓞 K) K a) : ℝ) = 1` using `by ext; simpa using h`. Take `⟨n, hn⟩` from `(GroundTheory.Global.fourierChar_eq_one_iff _).1 h'`. Conclude with `ha ⟨n, by exact_mod_cast hn.symm⟩`.

Establish `: (1 - (𝐞 (Algebra.trace ℚ K (ξ i * algebraMap (𝓞 K) K a) : ℝ) : ℂ)) * vecCoeff f ξ = 0`. Rewrite using `[sub_mul, one_mul, ← h1, sub_self]`. Conclude with `(mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hne))`.
-/
theorem vecCoeff_eq_zero_of_not_isDual {f : (ι → 𝔸[K]) → ℂ}
    (hper : ∀ ξ ∈ vecLattice K ι, ∀ x, f (ξ + x) = f x)
    (hfin : ∀ x (z : ι → FiniteAdeleRing (𝓞 K) K), (∀ i, z i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) →
      f (x + fun i => GroundTheory.Global.finiteAdeleInr (z i)) = f x)
    {ξ : ι → K} (hξ : ¬ IsDual ξ) : vecCoeff f ξ = 0 := by
  classical
  simp only [IsDual, not_forall] at hξ
  obtain ⟨i, hi⟩ := hξ
  rw [GroundTheory.Global.algebraMap_mem_finiteInvDifferent_iff] at hi
  push Not at hi
  obtain ⟨a, ha⟩ := hi
  set z : ι → FiniteAdeleRing (𝓞 K) K :=
    Pi.single i (algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K a))
  have hz : ∀ j, z j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [z, Pi.single_eq_same]
      exact fun v => GroundTheory.Global.coe_algebraMap_mem_adicCompletionIntegers v a
    · simp only [z, Pi.single_eq_of_ne hj]
      exact zero_mem _
  have h1 := vecCoeff_translate hper (fun j => GroundTheory.Global.finiteAdeleInr (z j)) ξ
  have h2 : (fun x => f (x + fun j => GroundTheory.Global.finiteAdeleInr (z j))) = f :=
    funext fun x => hfin x z hz
  rw [h2, pair_finiteAdeleInr] at h1
  have h3 : ∑ j, algebraMap K (FiniteAdeleRing (𝓞 K) K) (ξ j) * z j =
      algebraMap K (FiniteAdeleRing (𝓞 K) K) (ξ i * algebraMap (𝓞 K) K a) := by
    rw [Finset.sum_eq_single i]
    · simp [z, map_mul]
    · intro j _ hj
      simp [z, Pi.single_eq_of_ne hj]
    · simp
  rw [h3, adelicChar_finiteAdeleInr_algebraMap] at h1
  have hne : (𝐞 (Algebra.trace ℚ K (ξ i * algebraMap (𝓞 K) K a) : ℝ) : ℂ) ≠ 1 := by
    intro h
    have h' : 𝐞 (Algebra.trace ℚ K (ξ i * algebraMap (𝓞 K) K a) : ℝ) = 1 := by
      ext; simpa using h
    obtain ⟨n, hn⟩ := (GroundTheory.Global.fourierChar_eq_one_iff _).1 h'
    exact ha ⟨n, by exact_mod_cast hn.symm⟩
  have : (1 - (𝐞 (Algebra.trace ℚ K (ξ i * algebraMap (𝓞 K) K a) : ℝ) : ℂ)) * vecCoeff f ξ = 0 := by
    rw [sub_mul, one_mul, ← h1, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hne))

end FourierWhittaker

end

end GroundTheory.Automorphic
