import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Homog

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] in
/- English proof (translation)
Introduce `m hm`. Simplify using `at hm`.
-/
theorem isMultiHomog_zero (d : K → ℕ) : IsMultiHomog (0 : MRing ι) d := by
  intro m hm
  simp at hm

omit [Fintype K] in
/- English proof (translation)
Introduce `m hm`. Break down `Finset.mem_union.mp (support_add hm) with hm | hm` into its components or cases. Conclude with `hg m hm`. Conclude with `hh m hm`.
-/
theorem isMultiHomog_add {g h : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (hh : IsMultiHomog h d) : IsMultiHomog (g + h) d := by
  classical
  intro m hm
  rcases Finset.mem_union.mp (support_add hm) with hm | hm
  · exact hg m hm
  · exact hh m hm

omit [Fintype K] in
/- English proof (translation)
Introduce `m hm k`. Take `⟨m₁, hm₁, m₂, hm₂, rfl⟩` from `Finset.mem_add.mp (support_mul g h hm)`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply]`. Rewrite using `[hg m₁ hm₁ k, hh m₂ hm₂ k]`.
-/
theorem isMultiHomog_mul {g h : MRing ι} {a b : K → ℕ} (hg : IsMultiHomog g a)
    (hh : IsMultiHomog h b) : IsMultiHomog (g * h) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul g h hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply]
  rw [hg m₁ hm₁ k, hh m₂ hm₂ k]

/- English proof (translation)
Simplify using `using isMultiHomog_C_zero (ι := ι) 1`.
-/
theorem isMultiHomog_one : IsMultiHomog (1 : MRing ι) 0 := by
  simpa using isMultiHomog_C_zero (ι := ι) 1

end Homog

section Cone

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Use `conv_lhs => rw [g.as_sum]`. Use `conv_rhs => rw [g.as_sum]`. Rewrite using `[map_sum, map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hdeg` using `hg m hm`.

Simplify using `only [mConeMap, aeval_monomial, map_mul]`. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]`. Establish `hX : (∏ p : Σ k, ι k, (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ m p) = ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k`. Rewrite using `[Fintype.prod_sigma]`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ m ⟨k, i⟩ = _`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hdeg k]`. Rewrite using `[hX, MvPolynomial.algebraMap_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mConeMap_of_isMultiHomog (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) :
    mConeMap y g = MvPolynomial.C (aeval y g) * ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hg m hm
  simp only [mConeMap, aeval_monomial, map_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  have hX : (∏ p : Σ k, ι k, (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ m p) =
      ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hdeg k]
  rw [hX, MvPolynomial.algebraMap_apply]
  ring

/- English proof (translation)
Use `show g ∈ RingHom.ker (mConeMap y)`. Rewrite using `[RingHom.mem_ker]`. Use `erw [mConeMap_of_isMultiHomog y hg, h0]`. Simplify using the standard rewrite rules.
-/
theorem mem_mCoordIdeal_of_aeval_eq_zero (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) (h0 : aeval y g = 0) : g ∈ mCoordIdeal y := by
  show g ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  erw [mConeMap_of_isMultiHomog y hg, h0]
  simp

omit [Fintype K] [∀ k, Fintype (ι k)] in
/- English proof (translation)
The claim follows from `hz.2 g hg`.
-/
theorem eval_eq_zero_of_mem_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    {g : MRing ι} (hg : g ∈ P) : eval z (map (Int.castRingHom ℂ) g) = 0 :=
  hz.2 g hg

/- English proof (translation)
Take `⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩` from `hv`. Establish `hsub : IsMultiHomog (g - h) d`. Rewrite using `[sub_eq_add_neg]`. Use `isMultiHomog_add hg ?_` and prove the remaining obligations. Introduce `m hm`.

Conclude with `hh m (by simpa using hm)`. Establish `h0 : aeval y (g - h) = 0` using `by rw [map_sub, heq, one_mul, sub_self]`. Use `eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero y hsub h0)` as an intermediate fact. Rewrite `this` using `[map_sub, map_sub, sub_eq_zero]`. Rewrite using `[this, div_self hz0]`.
-/
theorem isValueAt_one {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    {v : ℂ} (hv : IsValueAt y 1 z v) : v = 1 := by
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  have hsub : IsMultiHomog (g - h) d := by
    rw [sub_eq_add_neg]
    refine isMultiHomog_add hg ?_
    intro m hm
    exact hh m (by simpa using hm)
  have h0 : aeval y (g - h) = 0 := by rw [map_sub, heq, one_mul, sub_self]
  have := eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero y hsub h0)
  rw [map_sub, map_sub, sub_eq_zero] at this
  rw [this, div_self hz0]

/- English proof (translation)
Take `⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩` from `hv`. Rewrite `heq` using `[zero_mul]`. Rewrite using `[eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero y hg heq), zero_div]`.
-/
theorem isValueAt_zero {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    {v : ℂ} (hv : IsValueAt y 0 z v) : v = 0 := by
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  rw [zero_mul] at heq
  rw [eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero y hg heq), zero_div]

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, 1, 1, isMultiHomog_one, isMultiHomog_one, by simp, by simp, by simp, by simp⟩`.
-/
theorem isValueAt_one_self (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : IsValueAt y 1 z 1 :=
  ⟨0, 1, 1, isMultiHomog_one, isMultiHomog_one, by simp, by simp, by simp, by simp⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, isValueAt_one_self y z, one_ne_zero⟩`.
-/
theorem isUnitAt_one (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : IsUnitAt y 1 z :=
  ⟨1, isValueAt_one_self y z, one_ne_zero⟩

end Cone

section Trivial

variable {Ω : Type} [Field Ω] {κ : Type}

def trivLat (x : κ → Ω) (N : ℕ) (i : κ) : AddSubgroup (Fin N → Ω) :=
  AddSubgroup.pi Set.univ fun _ => (chartRing ℤ x i).toSubring.toAddSubgroup

/- English proof (translation)
Simplify using `[trivLat, AddSubgroup.mem_pi]`.
-/
theorem mem_trivLat {x : κ → Ω} {N : ℕ} {i : κ} {e : Fin N → Ω} :
    e ∈ trivLat x N i ↔ ∀ q, e q ∈ chartRing ℤ x i := by
  simp [trivLat, AddSubgroup.mem_pi]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn⟩`. Rewrite `hn` using `[one_pow, one_smul, mem_trivLat]`. Use `⟨e, fun q => ⟨0, by simpa using hn q⟩, ?_⟩` and prove the remaining obligations. Conclude with `((Pi.basisFun Ω (Fin N)).sum_repr e).symm.trans (by simp)`.

Introduce and unpack `⟨a, ha, rfl⟩`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero, one_smul, mem_trivLat]`. Introduce `q`. Take `⟨n, hn⟩` from `ha q`.

Simplify `hn` using `[Finset.sum_apply, Pi.single_apply]`.
-/
theorem trivial_frame_iff (x : κ → Ω) (N : ℕ) (i : κ) (e : Fin N → Ω) :
    (∃ n : ℕ, (1 : Ω) ^ n • e ∈ trivLat x N i) ↔
      ∃ a : Fin N → Ω, (∀ q, ∃ n : ℕ, (1 : Ω) ^ n * a q ∈ chartRing ℤ x i) ∧
        e = ∑ q, a q • (Pi.basisFun Ω (Fin N)) q := by
  constructor
  · rintro ⟨n, hn⟩
    rw [one_pow, one_smul, mem_trivLat] at hn
    refine ⟨e, fun q => ⟨0, by simpa using hn q⟩, ?_⟩
    exact ((Pi.basisFun Ω (Fin N)).sum_repr e).symm.trans (by simp)
  · rintro ⟨a, ha, rfl⟩
    refine ⟨0, ?_⟩
    rw [pow_zero, one_smul, mem_trivLat]
    intro q
    obtain ⟨n, hn⟩ := ha q
    simpa [Finset.sum_apply, Pi.single_apply] using hn

def trivialBundle (x : κ → Ω) (N : ℕ) : ChartBundle ℤ x N (Fin N → Ω) where
  lat := trivLat x N
  stable i a ha e he := mem_trivLat.2 fun q => by
    simpa [smul_eq_mul] using mul_mem ha (mem_trivLat.1 he q)
  frame i _ := ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp,
    fun _ => ⟨Pi.basisFun Ω (Fin N), (Pi.basisFun Ω (Fin N)).linearIndependent,
      (Pi.basisFun Ω (Fin N)).span_eq, trivial_frame_iff x N i⟩⟩
  overlap i j hi hj e he := by
    have h := fun q => exists_pow_mul_mem_chartRing (o := ℤ) x i j hi (mem_trivLat.1 he q)
    choose m hm using h
    refine ⟨∑ q, m q, mem_trivLat.2 fun q => ?_⟩
    have hle : m q ≤ ∑ q, m q := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    have : (x i / x j) ^ (∑ q, m q) * e q =
        (x i / x j) ^ (∑ q, m q - m q) * ((x i / x j) ^ m q * e q) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [this]
    exact mul_mem (pow_mem (div_mem_chartRing x j i) _) (hm q)

end Trivial

end GroundTheory.Heights₂.Heights.LowerBoundFree
