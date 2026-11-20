import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MonomialRatioIntegralModelStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_flagpair_of_frames

section Linear

variable {Ω : Type*} [Field Ω] {V : Type*} [AddCommGroup V] [Module Ω V] {N : ℕ}

/- English proof (translation)
Establish `hv` using `congrArg (fun u => w.repr u j) (w'.sum_repr v)`. Simplify using `only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul] at hv`. Conclude with `hv.symm`.
-/
theorem repr_expand (w w' : Module.Basis (Fin N) Ω V) (v : V) (j : Fin N) :
    w.repr v j = ∑ l, w'.repr v l * w.repr (w' l) j := by
  have hv := congrArg (fun u => w.repr u j) (w'.sum_repr v)
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul] at hv
  exact hv.symm

/- English proof (translation)
Introduce `j hj`. Rewrite using `[repr_expand w w' v j]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Break down `lt_or_ge i l with hl | hl` into its components or cases. Rewrite using `[hv l hl, zero_mul]`.

Rewrite using `[h l j (lt_of_le_of_lt hl hj), mul_zero]`.
-/
theorem step_le (w w' : Module.Basis (Fin N) Ω V)
    (h : ∀ i j : Fin N, i < j → w.repr (w' i) j = 0) (i : Fin N) (v : V)
    (hv : ∀ j, i < j → w'.repr v j = 0) : ∀ j, i < j → w.repr v j = 0 := by
  intro j hj
  rw [repr_expand w w' v j]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge i l with hl | hl
  · rw [hv l hl, zero_mul]
  · rw [h l j (lt_of_le_of_lt hl hj), mul_zero]

/- English proof (translation)
Rewrite using `[repr_expand w w' v i, Finset.sum_eq_single i]`. Introduce `l _ hl`. Break down `lt_or_gt_of_ne hl with hl | hl` into its components or cases. Rewrite using `[h l i hl, mul_zero]`. Rewrite using `[hv l hl, zero_mul]`.

Introduce `hi`. Conclude with `absurd (Finset.mem_univ i) hi`.
-/
theorem step_coord (w w' : Module.Basis (Fin N) Ω V)
    (h : ∀ i j : Fin N, i < j → w.repr (w' i) j = 0) (i : Fin N) (v : V)
    (hv : ∀ j, i < j → w'.repr v j = 0) : w.repr v i = w'.repr v i * w.repr (w' i) i := by
  rw [repr_expand w w' v i, Finset.sum_eq_single i]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with hl | hl
    · rw [h l i hl, mul_zero]
    · rw [hv l hl, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/- English proof (translation)
Establish `hM : (w.toMatrix w').BlockTriangular id` using `fun i j hij => h j i hij`. Establish `hMN : w.toMatrix w' * w'.toMatrix w = 1` using `Module.Basis.toMatrix_mul_toMatrix_flip w w'`. Use `haveI : Invertible (w.toMatrix w') := ⟨w'.toMatrix w, Module.Basis.toMatrix_mul_toMatrix_flip w' w, hMN⟩`. Establish `hinv : (w.toMatrix w')⁻¹ = w'.toMatrix w` using `Matrix.inv_eq_right_inv hMN`. Establish `hN : (w'.toMatrix w).BlockTriangular id` using `hinv ▸ Matrix.blockTriangular_inv_of_blockTriangular hM`.

Introduce `i j hij`. Conclude with `hN hij`.
-/
theorem triangular_symm (w w' : Module.Basis (Fin N) Ω V)
    (h : ∀ i j : Fin N, i < j → w.repr (w' i) j = 0) :
    ∀ i j : Fin N, i < j → w'.repr (w i) j = 0 := by
  have hM : (w.toMatrix w').BlockTriangular id := fun i j hij => h j i hij
  have hMN : w.toMatrix w' * w'.toMatrix w = 1 := Module.Basis.toMatrix_mul_toMatrix_flip w w'
  haveI : Invertible (w.toMatrix w') := ⟨w'.toMatrix w, Module.Basis.toMatrix_mul_toMatrix_flip w' w, hMN⟩
  have hinv : (w.toMatrix w')⁻¹ = w'.toMatrix w := Matrix.inv_eq_right_inv hMN
  have hN : (w'.toMatrix w).BlockTriangular id := hinv ▸ Matrix.blockTriangular_inv_of_blockTriangular hM
  intro i j hij
  exact hN hij

end Linear

/- English proof (translation)
Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `hmem : algebraMap O Ω (↑u⁻¹ : O) ∈ chartRing O y s` using `Subalgebra.algebraMap_mem _ _`. Establish `key : algebraMap O Ω ϖ ^ n • v = algebraMap O Ω (↑u⁻¹ : O) • (algebraMap O Ω c • v)`. Rewrite using `[smul_smul, ← map_mul, hu, ← mul_assoc, Units.inv_mul, one_mul, map_pow]`.

Rewrite using `[key]`. Conclude with `E.stable s _ hmem _ hv`.
-/
theorem pow_smul_mem {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Ω : Type*} [Field Ω] [Algebra O Ω] {τ : Type*} {y : τ → Ω} {N : ℕ} {V : Type*}
    [AddCommGroup V] [Module Ω V] {ϖ : O} (hϖ : Irreducible ϖ) (E : ChartBundle O y N V) (s : τ)
    (v : V) (c : O) (hc : c ≠ 0) (hv : algebraMap O Ω c • v ∈ E.lat s) :
    ∃ n : ℕ, algebraMap O Ω ϖ ^ n • v ∈ E.lat s := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  refine ⟨n, ?_⟩
  have hmem : algebraMap O Ω (↑u⁻¹ : O) ∈ chartRing O y s := Subalgebra.algebraMap_mem _ _
  have key : algebraMap O Ω ϖ ^ n • v = algebraMap O Ω (↑u⁻¹ : O) • (algebraMap O Ω c • v) := by
    rw [smul_smul, ← map_mul, hu, ← mul_assoc, Units.inv_mul, one_mul, map_pow]
  rw [key]
  exact E.stable s _ hmem _ hv

end PositivityTheory.Xgn.A_flagpair_of_frames

/- English proof (translation)
Establish `hXpow : ∀ (q : (k : K) × ι k) (n : ℕ), IsMultiHomog ((X q : MRing ι O) ^ n) (n • blockWeight ι q)`. Introduce `q n`. Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[pow_zero, zero_smul]`.

Conclude with `isWeightedHomogeneous_one O (blockWeight ι)`. Consider the case `succ n ih`. Rewrite using `[pow_succ, succ_nsmul]`. Conclude with `IsWeightedHomogeneous.mul ih (isWeightedHomogeneous_X O (blockWeight ι) q)`. Establish `h` using `IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, c k⟩ : MRing ι O) ^ e k) (fun k => e k • blockWeight ι ⟨k, c k⟩) (fun k _ => hXpow _ _)`.

Establish `hsum : (∑ k, e k • blockWeight ι ⟨k, c k⟩) = e`. Use function extensionality and compare the values at `k'`. Simplify using `[Finset.sum_apply, blockWeight, Pi.single_apply, Pi.smul_apply]`. Rewrite `h` using `[hsum]`. Conclude with `h`.
-/
private theorem isMultiHomog_prod_X_pow' {O : Type} [CommRing O] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} (c : (k : K) → ι k) (e : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι O) ^ e k) e := by
  have hXpow : ∀ (q : (k : K) × ι k) (n : ℕ),
      IsMultiHomog ((X q : MRing ι O) ^ n) (n • blockWeight ι q) := by
    intro q n
    induction n with
    | zero =>
      rw [pow_zero, zero_smul]
      exact isWeightedHomogeneous_one O (blockWeight ι)
    | succ n ih =>
      rw [pow_succ, succ_nsmul]
      exact IsWeightedHomogeneous.mul ih (isWeightedHomogeneous_X O (blockWeight ι) q)
  have h := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, c k⟩ : MRing ι O) ^ e k)
    (fun k => e k • blockWeight ι ⟨k, c k⟩) (fun k _ => hXpow _ _)
  have hsum : (∑ k, e k • blockWeight ι ⟨k, c k⟩) = e := by
    funext k'
    simp [Finset.sum_apply, blockWeight, Pi.single_apply, Pi.smul_apply]
  rw [hsum] at h
  exact h

/- English proof (translation)
Establish `hdeg : ∀ {h : MRing ι O} {d d' : K → ℕ}, IsMultiHomog h d → d = d' → IsMultiHomog h d'` using `fun h e => e ▸ h`. Establish `hmc : ∀ q : ℕ, mseg x c ^ q = ∏ k, x ⟨k, c k⟩ ^ q`. Introduce `q`. Rewrite using `[Finset.prod_pow]`. Both sides reduce to the same expression.

Express the relevant statement in the definitionally equal form `a ∈ Algebra.adjoin O _ at ha`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem u hu`. Take `⟨s, rfl⟩` from `hu`. Use `⟨1, ∏ k, (X ⟨k, s k⟩ : MRing ι O) ^ (fun _ : K => 1) k, isMultiHomog_prod_X_pow' (O := O) s _, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_one, div_mul_cancel₀ _ hc]`. Simplify using `[mseg, map_prod]`. Consider the case `algebraMap r`. Use `⟨0, C r, hdeg (isWeightedHomogeneous_C _ r) rfl, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Consider the case `add u v _ _ hu hv`. Take `⟨p1, h1, hh1, he1⟩` from `hu`. Take `⟨p2, h2, hh2, he2⟩` from `hv`. Use `⟨p1 + p2, h1 * (∏ k, (X ⟨k, c k⟩ : MRing ι O) ^ (fun _ : K => p2) k) + h2 * (∏ k, (X ⟨k, c k⟩ : MRing ι O) ^ (fun _ : K => p1) k), ?_, ?_⟩` and prove the remaining obligations. Use `IsWeightedHomogeneous.add (hdeg (IsWeightedHomogeneous.mul hh1 (isMultiHomog_prod_X_pow' (O := O) c _)) ?_) (hdeg (IsWeightedHomogeneous.mul hh2 (isMultiHomog_prod_X_pow' (O := O) c _)) ?_)` and prove the remaining obligations.

Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Use function extensionality and compare the values at `k`. Simplify using `[add_comm]`. Rewrite using `[map_add, map_mul, map_mul, he1, he2]`.

Simplify using `only [map_prod, map_pow, aeval_X, hmc, pow_add, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul u v _ _ hu hv`. Take `⟨p1, h1, hh1, he1⟩` from `hu`. Take `⟨p2, h2, hh2, he2⟩` from `hv`.

Use `⟨p1 + p2, h1 * h2, hdeg (IsWeightedHomogeneous.mul hh1 hh2) (by funext k; simp), ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, he1, he2, pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exists_multiHomog_aeval_eq_mul_mseg_pow {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} (x : (k : K) × ι k → Ω)
    (c : (k : K) → ι k) (hc : mseg x c ≠ 0) (a : Ω) (ha : a ∈ chartRing O (mseg x) c) :
    ∃ (p : ℕ) (h : MRing ι O), IsMultiHomog h (fun _ => p) ∧ aeval x h = a * mseg x c ^ p := by
  have hdeg : ∀ {h : MRing ι O} {d d' : K → ℕ}, IsMultiHomog h d → d = d' → IsMultiHomog h d' :=
    fun h e => e ▸ h
  have hmc : ∀ q : ℕ, mseg x c ^ q = ∏ k, x ⟨k, c k⟩ ^ q := by
    intro q
    rw [Finset.prod_pow]
    rfl
  change a ∈ Algebra.adjoin O _ at ha
  induction ha using Algebra.adjoin_induction with
  | mem u hu =>
    obtain ⟨s, rfl⟩ := hu
    refine ⟨1, ∏ k, (X ⟨k, s k⟩ : MRing ι O) ^ (fun _ : K => 1) k, isMultiHomog_prod_X_pow' (O := O) s _, ?_⟩
    rw [pow_one, div_mul_cancel₀ _ hc]
    simp [mseg, map_prod]
  | algebraMap r =>
    refine ⟨0, C r, hdeg (isWeightedHomogeneous_C _ r) rfl, ?_⟩
    simp
  | add u v _ _ hu hv =>
    obtain ⟨p1, h1, hh1, he1⟩ := hu
    obtain ⟨p2, h2, hh2, he2⟩ := hv
    refine ⟨p1 + p2, h1 * (∏ k, (X ⟨k, c k⟩ : MRing ι O) ^ (fun _ : K => p2) k) +
      h2 * (∏ k, (X ⟨k, c k⟩ : MRing ι O) ^ (fun _ : K => p1) k), ?_, ?_⟩
    · refine IsWeightedHomogeneous.add
        (hdeg (IsWeightedHomogeneous.mul hh1 (isMultiHomog_prod_X_pow' (O := O) c _)) ?_)
        (hdeg (IsWeightedHomogeneous.mul hh2 (isMultiHomog_prod_X_pow' (O := O) c _)) ?_)
      · funext k
        simp
      · funext k
        simp [add_comm]
    · rw [map_add, map_mul, map_mul, he1, he2]
      simp only [map_prod, map_pow, aeval_X, hmc, pow_add, Finset.prod_mul_distrib]
      ring
  | mul u v _ _ hu hv =>
    obtain ⟨p1, h1, hh1, he1⟩ := hu
    obtain ⟨p2, h2, hh2, he2⟩ := hv
    refine ⟨p1 + p2, h1 * h2, hdeg (IsWeightedHomogeneous.mul hh1 hh2) (by funext k; simp), ?_⟩
    rw [map_mul, he1, he2, pow_add]
    ring

open PositivityTheory.Xgn.A_flagpair_of_frames in
/- English proof (translation)
Introduce `O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ d hP N V _ _ E E' hSG w w' b b' hE hE' htri`. Establish `hdeg : ∀ {h : MRing ι O} {d d' : K → ℕ}, IsMultiHomog h d → d = d' → IsMultiHomog h d'` using `fun h e => e ▸ h`. Establish `hSGF : SameGenericFibre ϖ E E'`. Introduce `s hs`. Prove the components needed by the constructor for the conclusion.

Introduce `v hv`. Take `⟨c, hc0, hcv⟩` from `(hSG s hs).1 v hv`. Conclude with `pow_smul_mem hϖ E' s v c hc0 hcv`. Introduce `v hv`. Take `⟨c, hc0, hcv⟩` from `(hSG s hs).2 v hv`.

Conclude with `pow_smul_mem hϖ E s v c hc0 hcv`. Use `⟨hSGF, ?_⟩` and prove the remaining obligations. Establish `htri'` using `triangular_symm w w' htri`. Establish `hrr : ∀ i, w.repr (w' i) i * w'.repr (w i) i = 1`. Introduce `i`.

Use `step_coord w' w htri' i (w' i) (fun j hj => htri i j hj)` as an intermediate fact. Simplify using `using this.symm`. Establish `hx0 : ∀ c : (k : K) → ι k, mseg x c ≠ 0 → ∀ k, x ⟨k, c k⟩ ≠ 0` using `fun c hc k => Finset.prod_ne_zero_iff.mp hc k (Finset.mem_univ k)`. Establish `hdata : ∀ c : (k : K) → ι k, mseg x c ≠ 0 → ∀ i : Fin N, ∃ (F G : MRing ι O) (bf bg : K → ℕ), IsMultiHomog F bf ∧ IsMultiHomog G bg ∧ (fun k => (bf k : ℤ) - bg k) = b i - b' i ∧ aeval x F = w.repr (w' i) i * aeval x G ∧ ∀ W : Ideal (MRing ι O), W.IsPrime → pointIdeal O x ≤ W → C …`. Introduce `c hc i`.

Establish `hm : (∏ k, x ⟨k, c k⟩ ^ b i k) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hx0 c hc k)`. Establish `hm' : (∏ k, x ⟨k, c k⟩ ^ b' i k) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hx0 c hc k)`. Choose the witnesses or unpack the hypotheses as in `⟨v, hvE', hvz, hvi⟩ : ∃ v ∈ E'.lat c, (∀ j, i < j → w'.repr v j = 0) ∧ w'.repr v i = ∏ k, x ⟨k, c k⟩ ^ b' i k := by`. Establish `hmem : (∏ k, x ⟨k, c k⟩ ^ b' i k) ∈ degLat O x (b' i) c` using `⟨1, one_mem _, (one_mul _).symm⟩`. Rewrite `hmem` using `[← hE'.graded c hc i]`.

Conclude with `hmem`. Take `⟨n, hn⟩` from `(hSGF c hc).2 v hvE'`. Establish `huz : ∀ j, i < j → w'.repr (algebraMap O Ω ϖ ^ n • v) j = 0`. Introduce `j hj`. Rewrite using `[map_smul, Finsupp.smul_apply, hvz j hj, smul_zero]`.

Establish `hmemE : w.repr (algebraMap O Ω ϖ ^ n • v) i ∈ degLat O x (b i) c`. Rewrite using `[← hE.graded c hc i]`. Conclude with `⟨_, hn, step_le w w' htri i _ huz, rfl⟩`. Take `⟨α, hα, hαeq⟩` from `hmemE`. Establish `eq1 : algebraMap O Ω ϖ ^ n * (∏ k, x ⟨k, c k⟩ ^ b' i k) * w.repr (w' i) i = α * ∏ k, x ⟨k, c k⟩ ^ b i k`.

Rewrite using `[← hαeq, step_coord w w' htri i _ huz, map_smul, Finsupp.smul_apply, hvi, smul_eq_mul]`. Choose the witnesses or unpack the hypotheses as in `⟨v2, hvE, hv2z, hv2i⟩ : ∃ v ∈ E.lat c, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = ∏ k, x ⟨k, c k⟩ ^ b i k := by`. Establish `hmem : (∏ k, x ⟨k, c k⟩ ^ b i k) ∈ degLat O x (b i) c` using `⟨1, one_mem _, (one_mul _).symm⟩`. Rewrite `hmem` using `[← hE.graded c hc i]`. Conclude with `hmem`.

Take `⟨n2, hn2⟩` from `(hSGF c hc).1 v2 hvE`. Establish `hu2z : ∀ j, i < j → w.repr (algebraMap O Ω ϖ ^ n2 • v2) j = 0`. Introduce `j hj`. Rewrite using `[map_smul, Finsupp.smul_apply, hv2z j hj, smul_zero]`. Establish `hmemE' : w'.repr (algebraMap O Ω ϖ ^ n2 • v2) i ∈ degLat O x (b' i) c`.

Rewrite using `[← hE'.graded c hc i]`. Conclude with `⟨_, hn2, step_le w' w htri' i _ hu2z, rfl⟩`. Take `⟨α', hα', hα'eq⟩` from `hmemE'`. Establish `eq1' : algebraMap O Ω ϖ ^ n2 * (∏ k, x ⟨k, c k⟩ ^ b i k) * w'.repr (w i) i = α' * ∏ k, x ⟨k, c k⟩ ^ b' i k`. Rewrite using `[← hα'eq, step_coord w' w htri' i _ hu2z, map_smul, Finsupp.smul_apply, hv2i, smul_eq_mul]`.

Establish `hαα : α * α' = algebraMap O Ω ϖ ^ (n + n2)`. Apply `mul_right_cancel₀ (mul_ne_zero hm hm')` to reduce the goal to its premises. Take the linear combination `(-(α' * ∏ k, x ⟨k, c k⟩ ^ b' i k)) * eq1 + (-(algebraMap O Ω ϖ ^ n * (∏ k, x ⟨k, c k⟩ ^ b' i k) * w.repr (w' i) i)) * eq1' + (algebraMap O Ω ϖ ^ (n + n2) * (∏ k, x ⟨k, c k⟩ ^ b i k) * ∏ k, x ⟨k, c k⟩ ^ b' i k) * hrr i`. Take `⟨p, h, hh, hhev⟩` from `exists_multiHomog_aeval_eq_mul_mseg_pow x c hc α hα`. Take `⟨p', h', hh', hh'ev⟩` from `exists_multiHomog_aeval_eq_mul_mseg_pow x c hc α' hα'`.

Establish `hmc : ∀ q : ℕ, mseg x c ^ q = ∏ k, x ⟨k, c k⟩ ^ q`. Introduce `q`. Rewrite using `[Finset.prod_pow]`. Both sides reduce to the same expression. Use `⟨h * ∏ k, (X ⟨k, c k⟩ : MRing ι O) ^ (b i k - b' i k).toNat, C (ϖ ^ n) * ∏ k, (X ⟨k, c k⟩ : MRing ι O) ^ (p + (-(b i k - b' i k)).toNat), fun k => p + (b i k - b' i k).toNat, fun k => p + (-(b i k - b' i k)).toNat, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `hdeg (IsWeightedHomogeneous.mul hh (isMultiHomog_prod_X_pow' (O := O) c (fun k => (b i k - b' i k).toNat))) (by funext k; simp)`. Conclude with `hdeg (IsWeightedHomogeneous.mul (isWeightedHomogeneous_C _ _) (isMultiHomog_prod_X_pow' (O := O) c (fun k => p + (-(b i k - b' i k)).toNat))) (by funext k; simp)`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.sub_apply]`. Use `push_cast`.

Use linear arithmetic over natural numbers and integers. Establish `eq2 : (∏ k, x ⟨k, c k⟩ ^ b i k) * ∏ k, x ⟨k, c k⟩ ^ (-(b i k - b' i k)).toNat = (∏ k, x ⟨k, c k⟩ ^ b' i k) * ∏ k, x ⟨k, c k⟩ ^ (b i k - b' i k).toNat`. Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [← zpow_natCast]`.

Rewrite using `[← zpow_add₀ (hx0 c hc k), ← zpow_add₀ (hx0 c hc k)]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Simplify using `only [map_mul, map_prod, map_pow, aeval_X, aeval_C, hhev, hmc, pow_add, Finset.prod_mul_distrib]`. Apply `mul_right_cancel₀ hm'` to reduce the goal to its premises.

Take the linear combination `(-(α * ∏ k, x ⟨k, c k⟩ ^ p)) * eq2 + (-((∏ k, x ⟨k, c k⟩ ^ p) * ∏ k, x ⟨k, c k⟩ ^ (-(b i k - b' i k)).toNat)) * eq1`. Introduce `W hW hPW hϖW hXW`. Establish `hXc : ∀ e : K → ℕ, (∏ k, (X ⟨k, c k⟩ : MRing ι O) ^ e k) ∈ W.primeCompl` using `fun e => prod_mem fun k _ => pow_mem (Ideal.mem_primeCompl_iff.mpr (hXW k)) _`. Establish `hCpow : ∀ q : ℕ, (C (ϖ ^ q) : MRing ι O) ∈ W.primeCompl`. Introduce `q`.

Rewrite using `[map_pow]`. Conclude with `pow_mem (Ideal.mem_primeCompl_iff.mpr hϖW) q`. Establish `hhW : h ∉ W`. Introduce `hhW`. Establish `hrel : h * h' - C (ϖ ^ (n + n2)) * ∏ k, (X ⟨k, c k⟩ : MRing ι O) ^ (fun _ : K => p + p') k ∈ pointIdeal O x`.

Use `GenericProjClosureDivisor.mem_of_homog (b := fun _ => p + p') ?_ ?_` and prove the remaining obligations. Use `IsWeightedHomogeneous.sub (hdeg (IsWeightedHomogeneous.mul hh hh') (by funext k; simp)) (hdeg (IsWeightedHomogeneous.mul (isWeightedHomogeneous_C _ _) (isMultiHomog_prod_X_pow' (O := O) c (fun _ : K => p + p'))) (by funext k; simp))` and prove the remaining obligations. Rewrite using `[map_sub, map_mul, map_mul, hhev, hh'ev, aeval_C, map_pow]`. Simplify using `only [map_prod, map_pow, aeval_X]`. Rewrite using `[show (∏ k, x ⟨k, c k⟩ ^ (p + p')) = mseg x c ^ (p + p') by rw [Finset.prod_pow]; rfl]`.

Take the linear combination `(mseg x c ^ (p + p')) * hαα`. Establish `hmemW : C (ϖ ^ (n + n2)) * ∏ k, (X ⟨k, c k⟩ : MRing ι O) ^ (fun _ : K => p + p') k ∈ W`. Establish `h1 : h * h' ∈ W` using `W.mul_mem_right h' hhW`. Establish `h2` using `hPW hrel`. Establish `h3` using `W.sub_mem h1 h2`.

Rewrite `h3` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Conclude with `(Ideal.mem_primeCompl_iff.mp (mul_mem (hCpow _) (hXc _))) hmemW`. Conclude with `⟨fun hF => (hW.mem_or_mem hF).elim hhW (Ideal.mem_primeCompl_iff.mp (hXc _)), Ideal.mem_primeCompl_iff.mp (mul_mem (hCpow n) (hXc _))⟩`. Establish `hXnotP : ∀ q : (k : K) × ι k, (X q : MRing ι O) ∉ pointIdeal O x → x q ≠ 0`. Introduce `q hq hx`.

Conclude with `hq (GenericProjClosureDivisor.mem_of_homog (b := blockWeight ι q) (isWeightedHomogeneous_X O (blockWeight ι) q) (by simp [hx]))`. Establish `hrelP : ∀ k, ∃ j : ι k, (X ⟨k, j⟩ : MRing ι O) ∉ pointIdeal O x` using `hP.multiProj.relevant`. Use `choose c0 hc0 using hrelP`. Establish `hmc0 : mseg x c0 ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => hXnotP _ (hc0 k)`. Establish `hCϖ : (C ϖ : MRing ι O) ∉ pointIdeal O x`.

Introduce `hmem`. Establish `hcm : ϖ ∈ Ideal.comap (C : O →+* MRing ι O) (pointIdeal O x)` using `hmem`. Rewrite `hcm` using `[hP.noTorsion]`. Conclude with `hϖ.ne_zero (Ideal.mem_bot.mp hcm)`. Establish `hPprime : (pointIdeal O x).IsPrime` using `hP.multiProj.isPrime`.

Use `choose F G bf bg hF hG hdiff hgen hnot using hdata c0 hmc0`. Use `⟨F, G, ⟨hE, hE', htri, fun i => ?_, fun i => hgen i⟩⟩` and prove the remaining obligations. Use `IsVerticalDivisor.of_unit_off_special ⟨bf i, bg i, hF i, hG i, hdiff i⟩ (hnot i _ hPprime le_rfl hCϖ hc0).1 (hnot i _ hPprime le_rfl hCϖ hc0).2 ?_` and prove the remaining obligations. Introduce `W hW hPW hRW hϖW`. Establish `hRW' : ∀ k, ∃ j : ι k, (X ⟨k, j⟩ : MRing ι O) ∉ W` using `hRW`.

Use `choose cW hcW using hRW'`. Establish `hmcW : mseg x cW ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => hXnotP _ (fun hm => hcW k (hPW hm))`. Take `⟨FW, GW, bfW, bgW, hFW, hGW, hdiffW, hgenW, hnotW⟩` from `hdata cW hmcW i`. Take `⟨hFWn, hGWn⟩` from `hnotW W hW hPW hϖW hcW`. Use `⟨GW, FW, hGWn, hFWn, ?_⟩` and prove the remaining obligations.

Use `GenericProjClosureDivisor.mem_of_homog (b := bgW + bf i) ?_ ?_` and prove the remaining obligations. Establish `hdeq : bfW + bg i = bgW + bf i`. Use function extensionality and compare the values at `k`. Establish `h1` using `congrFun (hdiff i) k`. Establish `h2` using `congrFun hdiffW k`.

Simplify using `only [Pi.sub_apply] at h1 h2`. Simplify using `only [Pi.add_apply]`. Use linear arithmetic over natural numbers and integers. Conclude with `IsWeightedHomogeneous.sub (IsWeightedHomogeneous.mul hGW (hF i)) (hdeg (IsWeightedHomogeneous.mul hFW (hG i)) hdeq)`. Rewrite using `[map_sub, map_mul, map_mul, hgen i, hgenW]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem PositivityTheory.Xgn.t_flagpair_of_frames : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, IsModelOver (pointIdeal O x) d → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V), SameGeneric O x E E' → ∀ (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K → ℤ), IsFlagFrame x E w b → IsFlagFrame x E' w' b' → (∀ i j : Fin N, i < j → w.repr (w' i) j = 0) → SameGenericFibre ϖ E E' ∧ ∃ f g : Fin N → MRing ι O, IsFlagPair ϖ x E E' w w' b b' f g := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ d hP N V _ _ E E' hSG w w' b b' hE hE' htri
  have hdeg : ∀ {h : MRing ι O} {d d' : K → ℕ}, IsMultiHomog h d → d = d' → IsMultiHomog h d' :=
    fun h e => e ▸ h
  have hSGF : SameGenericFibre ϖ E E' := by
    intro s hs
    constructor
    · intro v hv
      obtain ⟨c, hc0, hcv⟩ := (hSG s hs).1 v hv
      exact pow_smul_mem hϖ E' s v c hc0 hcv
    · intro v hv
      obtain ⟨c, hc0, hcv⟩ := (hSG s hs).2 v hv
      exact pow_smul_mem hϖ E s v c hc0 hcv
  refine ⟨hSGF, ?_⟩
  have htri' := triangular_symm w w' htri
  have hrr : ∀ i, w.repr (w' i) i * w'.repr (w i) i = 1 := by
    intro i
    have := step_coord w' w htri' i (w' i) (fun j hj => htri i j hj)
    simpa using this.symm
  have hx0 : ∀ c : (k : K) → ι k, mseg x c ≠ 0 → ∀ k, x ⟨k, c k⟩ ≠ 0 :=
    fun c hc k => Finset.prod_ne_zero_iff.mp hc k (Finset.mem_univ k)
  have hdata : ∀ c : (k : K) → ι k, mseg x c ≠ 0 → ∀ i : Fin N,
      ∃ (F G : MRing ι O) (bf bg : K → ℕ), IsMultiHomog F bf ∧ IsMultiHomog G bg ∧
        (fun k => (bf k : ℤ) - bg k) = b i - b' i ∧
        aeval x F = w.repr (w' i) i * aeval x G ∧
        ∀ W : Ideal (MRing ι O), W.IsPrime → pointIdeal O x ≤ W → C ϖ ∉ W →
          (∀ k, (X ⟨k, c k⟩ : MRing ι O) ∉ W) → F ∉ W ∧ G ∉ W := by
    intro c hc i
    have hm : (∏ k, x ⟨k, c k⟩ ^ b i k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hx0 c hc k)
    have hm' : (∏ k, x ⟨k, c k⟩ ^ b' i k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hx0 c hc k)
    obtain ⟨v, hvE', hvz, hvi⟩ : ∃ v ∈ E'.lat c, (∀ j, i < j → w'.repr v j = 0) ∧
        w'.repr v i = ∏ k, x ⟨k, c k⟩ ^ b' i k := by
      have hmem : (∏ k, x ⟨k, c k⟩ ^ b' i k) ∈ degLat O x (b' i) c := ⟨1, one_mem _, (one_mul _).symm⟩
      rw [← hE'.graded c hc i] at hmem
      exact hmem
    obtain ⟨n, hn⟩ := (hSGF c hc).2 v hvE'
    have huz : ∀ j, i < j → w'.repr (algebraMap O Ω ϖ ^ n • v) j = 0 := by
      intro j hj
      rw [map_smul, Finsupp.smul_apply, hvz j hj, smul_zero]
    have hmemE : w.repr (algebraMap O Ω ϖ ^ n • v) i ∈ degLat O x (b i) c := by
      rw [← hE.graded c hc i]
      exact ⟨_, hn, step_le w w' htri i _ huz, rfl⟩
    obtain ⟨α, hα, hαeq⟩ := hmemE
    have eq1 : algebraMap O Ω ϖ ^ n * (∏ k, x ⟨k, c k⟩ ^ b' i k) * w.repr (w' i) i =
        α * ∏ k, x ⟨k, c k⟩ ^ b i k := by
      rw [← hαeq, step_coord w w' htri i _ huz, map_smul, Finsupp.smul_apply, hvi, smul_eq_mul]
    obtain ⟨v2, hvE, hv2z, hv2i⟩ : ∃ v ∈ E.lat c, (∀ j, i < j → w.repr v j = 0) ∧
        w.repr v i = ∏ k, x ⟨k, c k⟩ ^ b i k := by
      have hmem : (∏ k, x ⟨k, c k⟩ ^ b i k) ∈ degLat O x (b i) c := ⟨1, one_mem _, (one_mul _).symm⟩
      rw [← hE.graded c hc i] at hmem
      exact hmem
    obtain ⟨n2, hn2⟩ := (hSGF c hc).1 v2 hvE
    have hu2z : ∀ j, i < j → w.repr (algebraMap O Ω ϖ ^ n2 • v2) j = 0 := by
      intro j hj
      rw [map_smul, Finsupp.smul_apply, hv2z j hj, smul_zero]
    have hmemE' : w'.repr (algebraMap O Ω ϖ ^ n2 • v2) i ∈ degLat O x (b' i) c := by
      rw [← hE'.graded c hc i]
      exact ⟨_, hn2, step_le w' w htri' i _ hu2z, rfl⟩
    obtain ⟨α', hα', hα'eq⟩ := hmemE'
    have eq1' : algebraMap O Ω ϖ ^ n2 * (∏ k, x ⟨k, c k⟩ ^ b i k) * w'.repr (w i) i =
        α' * ∏ k, x ⟨k, c k⟩ ^ b' i k := by
      rw [← hα'eq, step_coord w' w htri' i _ hu2z, map_smul, Finsupp.smul_apply, hv2i, smul_eq_mul]
    have hαα : α * α' = algebraMap O Ω ϖ ^ (n + n2) := by
      apply mul_right_cancel₀ (mul_ne_zero hm hm')
      linear_combination (-(α' * ∏ k, x ⟨k, c k⟩ ^ b' i k)) * eq1 +
        (-(algebraMap O Ω ϖ ^ n * (∏ k, x ⟨k, c k⟩ ^ b' i k) * w.repr (w' i) i)) * eq1' +
        (algebraMap O Ω ϖ ^ (n + n2) * (∏ k, x ⟨k, c k⟩ ^ b i k) * ∏ k, x ⟨k, c k⟩ ^ b' i k) * hrr i
    obtain ⟨p, h, hh, hhev⟩ := exists_multiHomog_aeval_eq_mul_mseg_pow x c hc α hα
    obtain ⟨p', h', hh', hh'ev⟩ := exists_multiHomog_aeval_eq_mul_mseg_pow x c hc α' hα'
    have hmc : ∀ q : ℕ, mseg x c ^ q = ∏ k, x ⟨k, c k⟩ ^ q := by
      intro q
      rw [Finset.prod_pow]
      rfl
    refine ⟨h * ∏ k, (X ⟨k, c k⟩ : MRing ι O) ^ (b i k - b' i k).toNat,
      C (ϖ ^ n) * ∏ k, (X ⟨k, c k⟩ : MRing ι O) ^ (p + (-(b i k - b' i k)).toNat),
      fun k => p + (b i k - b' i k).toNat, fun k => p + (-(b i k - b' i k)).toNat, ?_, ?_, ?_, ?_, ?_⟩
    · exact hdeg (IsWeightedHomogeneous.mul hh (isMultiHomog_prod_X_pow' (O := O) c (fun k => (b i k - b' i k).toNat)))
        (by funext k; simp)
    · exact hdeg (IsWeightedHomogeneous.mul (isWeightedHomogeneous_C _ _)
        (isMultiHomog_prod_X_pow' (O := O) c (fun k => p + (-(b i k - b' i k)).toNat))) (by funext k; simp)
    · funext k
      simp only [Pi.sub_apply]
      push_cast
      omega
    · have eq2 : (∏ k, x ⟨k, c k⟩ ^ b i k) * ∏ k, x ⟨k, c k⟩ ^ (-(b i k - b' i k)).toNat =
          (∏ k, x ⟨k, c k⟩ ^ b' i k) * ∏ k, x ⟨k, c k⟩ ^ (b i k - b' i k).toNat := by
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        simp only [← zpow_natCast]
        rw [← zpow_add₀ (hx0 c hc k), ← zpow_add₀ (hx0 c hc k)]
        congr 1
        omega
      simp only [map_mul, map_prod, map_pow, aeval_X, aeval_C, hhev, hmc, pow_add,
        Finset.prod_mul_distrib]
      apply mul_right_cancel₀ hm'
      linear_combination (-(α * ∏ k, x ⟨k, c k⟩ ^ p)) * eq2 +
        (-((∏ k, x ⟨k, c k⟩ ^ p) * ∏ k, x ⟨k, c k⟩ ^ (-(b i k - b' i k)).toNat)) * eq1
    · intro W hW hPW hϖW hXW
      have hXc : ∀ e : K → ℕ, (∏ k, (X ⟨k, c k⟩ : MRing ι O) ^ e k) ∈ W.primeCompl :=
        fun e => prod_mem fun k _ => pow_mem (Ideal.mem_primeCompl_iff.mpr (hXW k)) _
      have hCpow : ∀ q : ℕ, (C (ϖ ^ q) : MRing ι O) ∈ W.primeCompl := by
        intro q
        rw [map_pow]
        exact pow_mem (Ideal.mem_primeCompl_iff.mpr hϖW) q
      have hhW : h ∉ W := by
        intro hhW
        have hrel : h * h' - C (ϖ ^ (n + n2)) * ∏ k, (X ⟨k, c k⟩ : MRing ι O) ^ (fun _ : K => p + p') k
            ∈ pointIdeal O x := by
          refine GenericProjClosureDivisor.mem_of_homog (b := fun _ => p + p') ?_ ?_
          · refine IsWeightedHomogeneous.sub
              (hdeg (IsWeightedHomogeneous.mul hh hh') (by funext k; simp))
              (hdeg (IsWeightedHomogeneous.mul (isWeightedHomogeneous_C _ _)
                (isMultiHomog_prod_X_pow' (O := O) c (fun _ : K => p + p'))) (by funext k; simp))
          · rw [map_sub, map_mul, map_mul, hhev, hh'ev, aeval_C, map_pow]
            simp only [map_prod, map_pow, aeval_X]
            rw [show (∏ k, x ⟨k, c k⟩ ^ (p + p')) = mseg x c ^ (p + p') by rw [Finset.prod_pow]; rfl]
            linear_combination (mseg x c ^ (p + p')) * hαα
        have hmemW : C (ϖ ^ (n + n2)) * ∏ k, (X ⟨k, c k⟩ : MRing ι O) ^ (fun _ : K => p + p') k ∈ W := by
          have h1 : h * h' ∈ W := W.mul_mem_right h' hhW
          have h2 := hPW hrel
          have h3 := W.sub_mem h1 h2
          rwa [sub_sub_cancel] at h3
        exact (Ideal.mem_primeCompl_iff.mp (mul_mem (hCpow _) (hXc _))) hmemW
      exact ⟨fun hF => (hW.mem_or_mem hF).elim hhW (Ideal.mem_primeCompl_iff.mp (hXc _)),
        Ideal.mem_primeCompl_iff.mp (mul_mem (hCpow n) (hXc _))⟩
  have hXnotP : ∀ q : (k : K) × ι k, (X q : MRing ι O) ∉ pointIdeal O x → x q ≠ 0 := by
    intro q hq hx
    exact hq (GenericProjClosureDivisor.mem_of_homog (b := blockWeight ι q)
      (isWeightedHomogeneous_X O (blockWeight ι) q) (by simp [hx]))
  have hrelP : ∀ k, ∃ j : ι k, (X ⟨k, j⟩ : MRing ι O) ∉ pointIdeal O x := hP.multiProj.relevant
  choose c0 hc0 using hrelP
  have hmc0 : mseg x c0 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hXnotP _ (hc0 k)
  have hCϖ : (C ϖ : MRing ι O) ∉ pointIdeal O x := by
    intro hmem
    have hcm : ϖ ∈ Ideal.comap (C : O →+* MRing ι O) (pointIdeal O x) := hmem
    rw [hP.noTorsion] at hcm
    exact hϖ.ne_zero (Ideal.mem_bot.mp hcm)
  have hPprime : (pointIdeal O x).IsPrime := hP.multiProj.isPrime
  choose F G bf bg hF hG hdiff hgen hnot using hdata c0 hmc0
  refine ⟨F, G, ⟨hE, hE', htri, fun i => ?_, fun i => hgen i⟩⟩
  refine IsVerticalDivisor.of_unit_off_special ⟨bf i, bg i, hF i, hG i, hdiff i⟩
    (hnot i _ hPprime le_rfl hCϖ hc0).1 (hnot i _ hPprime le_rfl hCϖ hc0).2 ?_
  intro W hW hPW hRW hϖW
  have hRW' : ∀ k, ∃ j : ι k, (X ⟨k, j⟩ : MRing ι O) ∉ W := hRW
  choose cW hcW using hRW'
  have hmcW : mseg x cW ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => hXnotP _ (fun hm => hcW k (hPW hm))
  obtain ⟨FW, GW, bfW, bgW, hFW, hGW, hdiffW, hgenW, hnotW⟩ := hdata cW hmcW i
  obtain ⟨hFWn, hGWn⟩ := hnotW W hW hPW hϖW hcW
  refine ⟨GW, FW, hGWn, hFWn, ?_⟩
  refine GenericProjClosureDivisor.mem_of_homog (b := bgW + bf i) ?_ ?_
  · have hdeq : bfW + bg i = bgW + bf i := by
      funext k
      have h1 := congrFun (hdiff i) k
      have h2 := congrFun hdiffW k
      simp only [Pi.sub_apply] at h1 h2
      simp only [Pi.add_apply]
      omega
    exact IsWeightedHomogeneous.sub (IsWeightedHomogeneous.mul hGW (hF i))
      (hdeg (IsWeightedHomogeneous.mul hFW (hG i)) hdeq)
  · rw [map_sub, map_mul, map_mul, hgen i, hgenW]
    ring
