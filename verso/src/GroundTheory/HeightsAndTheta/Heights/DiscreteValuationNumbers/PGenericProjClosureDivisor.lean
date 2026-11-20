import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsGenericProjClosureDivisor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsTwistedDualGensExpress
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace GenericProjClosureDivisor

section PointIdeal

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {O : Type} [CommRing O] {Φ : Type} [Field Φ] [Algebra O Φ]

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Establish `key : ((aeval (fun _ : K => (1 : Φ))).restrictScalars O).comp (pointConeMap O z) = aeval z`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `p`. Simplify using `[pointConeMap]`. Establish `h` using `congrArg (fun ψ => ψ f) key`.

Simplify using `only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h`. Rewrite using `[← h]`. Establish `hf' : pointConeMap O z f = 0` using `hf`. Rewrite using `[hf', map_zero]`.
-/
theorem aeval_eq_zero_of_mem {z : (Σ k, ι k) → Φ} {f : MRing ι O} (hf : f ∈ pointIdeal O z) :
    aeval z f = 0 := by
  have key : ((aeval (fun _ : K => (1 : Φ))).restrictScalars O).comp (pointConeMap O z) = aeval z := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [pointConeMap]
  have h := congrArg (fun ψ => ψ f) key
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h
  rw [← h]
  have hf' : pointConeMap O z f = 0 := hf
  rw [hf', map_zero]

/- English proof (translation)
Use `conv_lhs => rw [f.as_sum]`. Use `conv_rhs => rw [f.as_sum]`. Rewrite using `[map_sum, map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hw : ∀ k, ∑ i : ι k, m ⟨k, i⟩ = b k`.

Introduce `k`. Establish `h1` using `congrFun (hf (mem_support_iff.mp hm)) k`. Rewrite `h1` using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]`. Rewrite using `[← h1, Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single k]`. Simplify using `[blockWeight]`.

Introduce `k' _ hk'`. Simplify using `[blockWeight, Ne.symm hk']`. Simplify using the standard rewrite rules. Simplify using `only [pointConeMap, aeval_monomial]`. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`.

Simplify using `only [mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, mul_assoc]`. Establish `hB : ∏ x : (Σ k, ι k), (X x.1 : MvPolynomial K Φ) ^ m x = ∏ k, X k ^ b k`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ i : ι k, (X k : MvPolynomial K Φ) ^ m ⟨k, i⟩ = _`.

Rewrite using `[Finset.prod_pow_eq_pow_sum, hw k]`. Rewrite using `[hB, MvPolynomial.algebraMap_apply]`.
-/
theorem pointConeMap_of_homog (z : (Σ k, ι k) → Φ) {f : MRing ι O} {b : K → ℕ} (hf : IsMultiHomog f b) :
    pointConeMap O z f = C (aeval z f) * ∏ k, X k ^ b k := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw : ∀ k, ∑ i : ι k, m ⟨k, i⟩ = b k := by
    intro k
    have h1 := congrFun (hf (mem_support_iff.mp hm)) k
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h1
    rw [← h1, Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single k]
    · simp [blockWeight]
    · intro k' _ hk'
      simp [blockWeight, Ne.symm hk']
    · simp
  simp only [pointConeMap, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, mul_assoc]
  have hB : ∏ x : (Σ k, ι k), (X x.1 : MvPolynomial K Φ) ^ m x = ∏ k, X k ^ b k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i : ι k, (X k : MvPolynomial K Φ) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hw k]
  rw [hB, MvPolynomial.algebraMap_apply]

/- English proof (translation)
Rewrite using `[pointIdeal, RingHom.mem_ker, pointConeMap_of_homog z hf, h0, map_zero, zero_mul]`.
-/
theorem mem_of_homog {z : (Σ k, ι k) → Φ} {f : MRing ι O} {b : K → ℕ} (hf : IsMultiHomog f b)
    (h0 : aeval z f = 0) : f ∈ pointIdeal O z := by
  rw [pointIdeal, RingHom.mem_ker, pointConeMap_of_homog z hf, h0, map_zero, zero_mul]

/- English proof (translation)
Establish `hd : bf + bg' = bf' + bg`. Use function extensionality and compare the values at `k`. Use `hdeg k` as an intermediate fact. Simplify using `only [Pi.add_apply]`. Use linear arithmetic over natural numbers and integers.

Establish `h1 : IsWeightedHomogeneous (blockWeight ι) (f * g') (bf + bg')` using `IsWeightedHomogeneous.mul hf hg'`. Establish `h2 : IsWeightedHomogeneous (blockWeight ι) (f' * g) (bf + bg')`. Rewrite using `[hd]`. Conclude with `IsWeightedHomogeneous.mul hf' hg`. Use `mem_of_homog (b := bf + bg') ?_ ?_` and prove the remaining obligations.

Conclude with `(mem_weightedHomogeneousSubmodule _ _ _ _).mp (sub_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h1) ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))`. Rewrite using `[map_sub, map_mul, map_mul, hv, hv']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cross_mem {z : (Σ k, ι k) → Φ} {f g f' g' : MRing ι O} {bf bg bf' bg' : K → ℕ}
    (hf : IsMultiHomog f bf) (hg : IsMultiHomog g bg) (hf' : IsMultiHomog f' bf')
    (hg' : IsMultiHomog g' bg') (hdeg : ∀ k, (bf k : ℤ) - bg k = bf' k - bg' k)
    (hv : aeval z f = aeval z g) (hv' : aeval z f' = aeval z g') :
    f * g' - f' * g ∈ pointIdeal O z := by
  have hd : bf + bg' = bf' + bg := by
    funext k
    have := hdeg k
    simp only [Pi.add_apply]
    omega
  have h1 : IsWeightedHomogeneous (blockWeight ι) (f * g') (bf + bg') := IsWeightedHomogeneous.mul hf hg'
  have h2 : IsWeightedHomogeneous (blockWeight ι) (f' * g) (bf + bg') := by
    rw [hd]; exact IsWeightedHomogeneous.mul hf' hg
  refine mem_of_homog (b := bf + bg') ?_ ?_
  · exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp
      (sub_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h1)
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))
  · rw [map_sub, map_mul, map_mul, hv, hv']
    ring

end PointIdeal

section Forms

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {N M M' : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
  {Φ : Type} [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]

def vdeg (α : K → ℕ) : Option (Option K) → ℕ
  | some (some k) => α k
  | _ => 0

omit [Fintype K] [DecidableEq K] in
/- English proof (translation)
Use function extensionality and compare the values at `o`. Apply the tactic sequence `rcases o with _ | _ | k <;> simp [vdeg]`.
-/
theorem vdeg_add (α β : K → ℕ) : vdeg (α + β) = vdeg α + vdeg β := by
  funext o
  rcases o with _ | _ | k <;> simp [vdeg]

def chartMonoZ (O : Type) [CommRing O] (M M' : ℕ) (c : ∀ k, ι k) (α : K → ℕ) :
    MRing (bundleIdx (bundleIdx ι M) M') O :=
  ∏ k, X (⟨some (some k), c k⟩ : Σ o, bundleIdx (bundleIdx ι M) M' o) ^ α k

/- English proof (translation)
Establish `h` using `IsWeightedHomogeneous.prod (R := O) Finset.univ (fun k => X (⟨some (some k), c k⟩ : Σ o, bundleIdx (bundleIdx ι M) M' o) ^ α k) (fun k => α k • blockWeight (bundleIdx (bundleIdx ι M) M') ⟨some (some k), c k⟩) (fun k _ => (isWeightedHomogeneous_X O _ _).pow (α k))`. Establish `hw : vdeg α = ∑ k, α k • blockWeight (bundleIdx (bundleIdx ι M) M') ⟨some (some k), c k⟩`. Use function extensionality and compare the values at `o`. Apply the tactic sequence `rcases o with _ | _ | k <;> simp [vdeg, blockWeight, Finset.sum_apply, Pi.single_apply]`. Rewrite using `[IsMultiHomog, chartMonoZ, hw]`.

Conclude with `h`.
-/
theorem chartMonoZ_homog (c : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (chartMonoZ O M M' c α) (vdeg α) := by
  have h := IsWeightedHomogeneous.prod (R := O) Finset.univ
    (fun k => X (⟨some (some k), c k⟩ : Σ o, bundleIdx (bundleIdx ι M) M' o) ^ α k)
    (fun k => α k • blockWeight (bundleIdx (bundleIdx ι M) M') ⟨some (some k), c k⟩)
    (fun k _ => (isWeightedHomogeneous_X O _ _).pow (α k))
  have hw : vdeg α = ∑ k, α k • blockWeight (bundleIdx (bundleIdx ι M) M') ⟨some (some k), c k⟩ := by
    funext o
    rcases o with _ | _ | k <;> simp [vdeg, blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [IsMultiHomog, chartMonoZ, hw]
  exact h

def genVal (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ) (ψ : Module.Dual Ω E) : Φ :=
  ∑ i, t i * algebraMap Ω Φ (ψ (e i))

omit [Algebra O Φ] in
/- English proof (translation)
Simplify using `only [genVal, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring`.
-/
theorem genVal_sum_smul (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ) {L : ℕ} (r : Fin L → Ω)
    (ψ : Fin L → Module.Dual Ω E) :
    genVal e t (∑ l, r l • ψ l) = ∑ l, algebraMap Ω Φ (r l) * genVal e t (ψ l) := by
  simp only [genVal, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_sum, map_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

omit [Algebra O Φ] in
/- English proof (translation)
Simplify using `only [genVal, LinearMap.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem genVal_smul (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ) (r : Ω) (ψ : Module.Dual Ω E) :
    genVal e t (r • ψ) = algebraMap Ω Φ r * genVal e t ψ := by
  simp only [genVal, LinearMap.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

omit [Fintype K] [DecidableEq K] [Algebra O Ω] [IsScalarTower O Ω Φ] in
/- English proof (translation)
Rewrite using `[chartMonoZ, map_prod, map_prod]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, map_pow, aeval_X]`. Both sides reduce to the same expression.
-/
theorem aeval_chartMonoZ (y : (Σ k, ι k) → Ω) (e : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k)
    (α : K → ℕ) [Fintype K] :
    aeval (pairProjCoord y e φ φ' t) (chartMonoZ O M M' c α) = algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ α k) := by
  rw [chartMonoZ, map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_pow, map_pow, aeval_X]
  rfl

/- English proof (translation)
Establish `hQ : ∀ (j : ∀ k, ι k) (n : ℕ), aeval (pairProjCoord y e φ φ' t) (chartMonoZ O M M' j (fun _ => n)) = algebraMap Ω Φ (segreVec y j ^ n)`. Introduce `j n`. Rewrite using `[aeval_chartMonoZ, segreVec, Finset.prod_pow]`. Establish `hlift : ∀ n n' : ℕ, vdeg (K` using `K) (fun _ => n + n') = vdeg (fun _ => n) + vdeg (fun _ => n') := fun n n' => vdeg_add _ _`. Proceed by induction on `hu using Algebra.adjoin_induction with`.

Consider the case `mem z hz`. Take `⟨j, rfl⟩` from `hz`. Use `⟨1, chartMonoZ O M M' j (fun _ => 1), chartMonoZ_homog j _, ?_⟩` and prove the remaining obligations. Rewrite using `[hQ, pow_one, pow_one, div_mul_cancel₀ _ hc]`. Consider the case `algebraMap r`.

Use `⟨0, C r, ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : vdeg (K` using `K) (fun _ => 0) = 0 := by`. Use function extensionality and compare the values at `o`. Apply the tactic sequence `rcases o with _ | _ | k <;> rfl`. Rewrite using `[h0]`.

Conclude with `isWeightedHomogeneous_C _ _`. Rewrite using `[aeval_C, pow_zero, mul_one, IsScalarTower.algebraMap_apply O Ω Φ]`. Consider the case `add z z' _ _ hz hz'`. Take `⟨n, U, hU, hUe⟩` from `hz`. Take `⟨n', U', hU', hUe'⟩` from `hz'`.

Use `⟨n + n', U * chartMonoZ O M M' c (fun _ => n') + U' * chartMonoZ O M M' c (fun _ => n), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hlift]`. Use `(IsWeightedHomogeneous.mul hU (chartMonoZ_homog c _)).add ?_` and prove the remaining obligations. Rewrite using `[add_comm]`. Conclude with `IsWeightedHomogeneous.mul hU' (chartMonoZ_homog c _)`.

Rewrite using `[map_add, map_mul, map_mul, hUe, hUe', hQ, hQ, ← map_mul, ← map_mul, ← map_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul z z' _ _ hz hz'`. Take `⟨n, U, hU, hUe⟩` from `hz`.

Take `⟨n', U', hU', hUe'⟩` from `hz'`. Use `⟨n + n', U * U', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hlift]`. Conclude with `IsWeightedHomogeneous.mul hU hU'`. Rewrite using `[map_mul, hUe, hUe', ← map_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chart_form (y : (Σ k, ι k) → Ω) (e : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) {u : Ω} (hu : u ∈ chartRing O (segreVec y) c) :
    ∃ (n : ℕ) (U : MRing (bundleIdx (bundleIdx ι M) M') O), IsMultiHomog U (vdeg fun _ => n) ∧
      aeval (pairProjCoord y e φ φ' t) U = algebraMap Ω Φ (u * segreVec y c ^ n) := by
  have hQ : ∀ (j : ∀ k, ι k) (n : ℕ), aeval (pairProjCoord y e φ φ' t) (chartMonoZ O M M' j (fun _ => n)) =
      algebraMap Ω Φ (segreVec y j ^ n) := by
    intro j n
    rw [aeval_chartMonoZ, segreVec, Finset.prod_pow]
  have hlift : ∀ n n' : ℕ, vdeg (K := K) (fun _ => n + n') = vdeg (fun _ => n) + vdeg (fun _ => n') :=
    fun n n' => vdeg_add _ _
  induction hu using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨j, rfl⟩ := hz
    refine ⟨1, chartMonoZ O M M' j (fun _ => 1), chartMonoZ_homog j _, ?_⟩
    rw [hQ, pow_one, pow_one, div_mul_cancel₀ _ hc]
  | algebraMap r =>
    refine ⟨0, C r, ?_, ?_⟩
    · have h0 : vdeg (K := K) (fun _ => 0) = 0 := by
        funext o
        rcases o with _ | _ | k <;> rfl
      rw [h0]
      exact isWeightedHomogeneous_C _ _
    · rw [aeval_C, pow_zero, mul_one, IsScalarTower.algebraMap_apply O Ω Φ]
  | add z z' _ _ hz hz' =>
    obtain ⟨n, U, hU, hUe⟩ := hz
    obtain ⟨n', U', hU', hUe'⟩ := hz'
    refine ⟨n + n', U * chartMonoZ O M M' c (fun _ => n') + U' * chartMonoZ O M M' c (fun _ => n), ?_, ?_⟩
    · rw [hlift]
      refine (IsWeightedHomogeneous.mul hU (chartMonoZ_homog c _)).add ?_
      rw [add_comm]
      exact IsWeightedHomogeneous.mul hU' (chartMonoZ_homog c _)
    · rw [map_add, map_mul, map_mul, hUe, hUe', hQ, hQ, ← map_mul, ← map_mul, ← map_add]
      congr 1
      ring
  | mul z z' _ _ hz hz' =>
    obtain ⟨n, U, hU, hUe⟩ := hz
    obtain ⟨n', U', hU', hUe'⟩ := hz'
    refine ⟨n + n', U * U', ?_, ?_⟩
    · rw [hlift]
      exact IsWeightedHomogeneous.mul hU hU'
    · rw [map_mul, hUe, hUe', ← map_mul]
      congr 1
      ring

/- English proof (translation)
Use `choose n U hU hUe using fun l => chart_form (O := O) (M := M) (M' := M') y e φ φ' t c hc (hr l)`. Use `⟨∑ l, n l, fun l => U l * chartMonoZ O M M' c (fun _ => ∑ j, n j - n l), fun l => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `hle : n l ≤ ∑ j, n j` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)`. Establish `h : vdeg (K` using `K) (fun _ => ∑ j, n j) = vdeg (fun _ => n l) + vdeg (fun _ => ∑ j, n j - n l) := by`. Rewrite using `[← vdeg_add]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.add_apply]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h]`.

Conclude with `IsWeightedHomogeneous.mul (hU l) (chartMonoZ_homog c _)`. Establish `hle : n l ≤ ∑ j, n j` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)`. Rewrite using `[map_mul, hUe l, aeval_chartMonoZ, Finset.prod_pow, ← map_mul]`. Use `congr 1`. Rewrite using `[mul_assoc, show ∏ k, y ⟨k, c k⟩ = segreVec y c from rfl, ← pow_add, Nat.add_sub_cancel' hle]`.
-/
theorem chart_forms_uniform (y : (Σ k, ι k) → Ω) (e : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) {L : ℕ} (r : Fin L → Ω) (hr : ∀ l, r l ∈ chartRing O (segreVec y) c) :
    ∃ (n : ℕ) (U : Fin L → MRing (bundleIdx (bundleIdx ι M) M') O), ∀ l,
      IsMultiHomog (U l) (vdeg fun _ => n) ∧
        aeval (pairProjCoord y e φ φ' t) (U l) = algebraMap Ω Φ (r l * segreVec y c ^ n) := by
  choose n U hU hUe using fun l => chart_form (O := O) (M := M) (M' := M') y e φ φ' t c hc (hr l)
  refine ⟨∑ l, n l, fun l => U l * chartMonoZ O M M' c (fun _ => ∑ j, n j - n l), fun l => ⟨?_, ?_⟩⟩
  · have hle : n l ≤ ∑ j, n j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
    have h : vdeg (K := K) (fun _ => ∑ j, n j) = vdeg (fun _ => n l) + vdeg (fun _ => ∑ j, n j - n l) := by
      rw [← vdeg_add]
      congr 1
      funext k
      simp only [Pi.add_apply]
      omega
    rw [h]
    exact IsWeightedHomogeneous.mul (hU l) (chartMonoZ_homog c _)
  · have hle : n l ≤ ∑ j, n j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
    rw [map_mul, hUe l, aeval_chartMonoZ, Finset.prod_pow, ← map_mul]
    congr 1
    rw [mul_assoc, show ∏ k, y ⟨k, c k⟩ = segreVec y c from rfl, ← pow_add, Nat.add_sub_cancel' hle]

/- English proof (translation)
Establish `hy : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k h0 => hc (Finset.prod_eq_zero (Finset.mem_univ k) h0)`. Take `⟨n₀, U, hU⟩` from `chart_forms_uniform (O := O) (M := M) (M' := M') y e φ φ' t c hc r hr`. Set `A : K → ℕ` to `fun k => (a' k - a k).toNat`. Set `B : K → ℕ` to `fun k => (a k - a' k).toNat`. Establish `hAB : ∀ k, ((n₀ + B k : ℕ) : ℤ) + (a' k - a k) = (n₀ : ℤ) + (A k : ℤ)`.

Introduce `k`. Simplify using `only [A, B]`. Use linear arithmetic over natural numbers and integers. Use `⟨fun k => n₀ + A k, fun k => n₀ + B k, fun l => U l * chartMonoZ O M M' c A, fun l => ?_, fun k => ?_, ?_⟩` and prove the remaining obligations. Establish `hv : vdeg (K` using `K) (fun k => n₀ + A k) = vdeg (fun _ => n₀) + vdeg A := vdeg_add _ _`.

Rewrite using `[hv]`. Conclude with `IsWeightedHomogeneous.mul (hU l).1 (chartMonoZ_homog c A)`. Use `hAB k` as an intermediate fact. Move the coercions through the operations in `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hk : ∀ k, y ⟨k, c k⟩ ^ (n₀ + B k) * y ⟨k, c k⟩ ^ (a' k - a k) = y ⟨k, c k⟩ ^ n₀ * y ⟨k, c k⟩ ^ A k`. Introduce `k`. Rewrite using `[← zpow_natCast (y _) (n₀ + B k), ← zpow_add₀ (hy k), hAB k, zpow_add₀ (hy k), zpow_natCast, zpow_natCast]`. Establish `key : (algebraMap O Ω ϖ ^ n * ∏ k, y ⟨k, c k⟩ ^ (n₀ + B k)) • χ = ∑ l, (r l * segreVec y c ^ n₀ * ∏ k, y ⟨k, c k⟩ ^ A k) • ψ l`. Rewrite using `[mul_comm, ← smul_smul, h, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_mul_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = r l * segreVec y c ^ n₀ * ∏ k, y ⟨k, c k⟩ ^ A k := by`. Repeatedly rewrite using `[hk]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_pow, show ∏ k, y ⟨k, c k⟩ = segreVec y c from rfl]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hval` using `congrArg (genVal e t) key`. Rewrite `hval` using `[genVal_smul, genVal_sum_smul]`. Rewrite using `[map_mul, aeval_C, aeval_chartMonoZ, map_pow, IsScalarTower.algebraMap_apply O Ω Φ, ← map_pow, ← map_mul, hval]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Use `show _ = aeval _ (U l * chartMonoZ O M M' c A) * _`.

Rewrite using `[map_mul (aeval (pairProjCoord y e φ φ' t)) (U l), (hU l).2, aeval_chartMonoZ, map_mul (algebraMap Ω Φ) (r l * segreVec y c ^ n₀)]`.
-/
theorem express_forms (y : (Σ k, ι k) → Ω) (e : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) (ϖ : O) {L : ℕ} (ψ : Fin L → Module.Dual Ω E) (χ : Module.Dual Ω E)
    (a a' : K → ℤ) (n : ℕ) (r : Fin L → Ω) (hr : ∀ l, r l ∈ chartRing O (segreVec y) c)
    (h : algebraMap O Ω ϖ ^ n • χ = ∑ l, (r l * ∏ k, y ⟨k, c k⟩ ^ (a' k - a k)) • ψ l) :
    ∃ (bG bH : K → ℕ) (G : Fin L → MRing (bundleIdx (bundleIdx ι M) M') O),
      (∀ l, IsMultiHomog (G l) (vdeg bG)) ∧ (∀ k, (bG k : ℤ) - bH k = a' k - a k) ∧
      aeval (pairProjCoord y e φ φ' t) (C (ϖ ^ n) * chartMonoZ O M M' c bH) * genVal e t χ =
        ∑ l, aeval (pairProjCoord y e φ φ' t) (G l) * genVal e t (ψ l) := by
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hc (Finset.prod_eq_zero (Finset.mem_univ k) h0)
  obtain ⟨n₀, U, hU⟩ := chart_forms_uniform (O := O) (M := M) (M' := M') y e φ φ' t c hc r hr
  let A : K → ℕ := fun k => (a' k - a k).toNat
  let B : K → ℕ := fun k => (a k - a' k).toNat
  have hAB : ∀ k, ((n₀ + B k : ℕ) : ℤ) + (a' k - a k) = (n₀ : ℤ) + (A k : ℤ) := by
    intro k
    simp only [A, B]
    omega
  refine ⟨fun k => n₀ + A k, fun k => n₀ + B k, fun l => U l * chartMonoZ O M M' c A, fun l => ?_,
    fun k => ?_, ?_⟩
  · have hv : vdeg (K := K) (fun k => n₀ + A k) = vdeg (fun _ => n₀) + vdeg A := vdeg_add _ _
    rw [hv]
    exact IsWeightedHomogeneous.mul (hU l).1 (chartMonoZ_homog c A)
  · have := hAB k
    push_cast at this ⊢
    linarith
  · have hk : ∀ k, y ⟨k, c k⟩ ^ (n₀ + B k) * y ⟨k, c k⟩ ^ (a' k - a k) =
        y ⟨k, c k⟩ ^ n₀ * y ⟨k, c k⟩ ^ A k := by
      intro k
      rw [← zpow_natCast (y _) (n₀ + B k), ← zpow_add₀ (hy k), hAB k, zpow_add₀ (hy k), zpow_natCast,
        zpow_natCast]
    have key : (algebraMap O Ω ϖ ^ n * ∏ k, y ⟨k, c k⟩ ^ (n₀ + B k)) • χ =
        ∑ l, (r l * segreVec y c ^ n₀ * ∏ k, y ⟨k, c k⟩ ^ A k) • ψ l := by
      rw [mul_comm, ← smul_smul, h, Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_smul]
      congr 1
      calc (∏ k, y ⟨k, c k⟩ ^ (n₀ + B k)) * (r l * ∏ k, y ⟨k, c k⟩ ^ (a' k - a k))
          = r l * ∏ k, (y ⟨k, c k⟩ ^ (n₀ + B k) * y ⟨k, c k⟩ ^ (a' k - a k)) := by
            rw [Finset.prod_mul_distrib]
            ring
        _ = r l * segreVec y c ^ n₀ * ∏ k, y ⟨k, c k⟩ ^ A k := by
            simp_rw [hk]
            rw [Finset.prod_mul_distrib, Finset.prod_pow, show ∏ k, y ⟨k, c k⟩ = segreVec y c from rfl]
            ring
    have hval := congrArg (genVal e t) key
    rw [genVal_smul, genVal_sum_smul] at hval
    rw [map_mul, aeval_C, aeval_chartMonoZ, map_pow, IsScalarTower.algebraMap_apply O Ω Φ, ← map_pow,
      ← map_mul, hval]
    refine Finset.sum_congr rfl fun l _ => ?_
    show _ = aeval _ (U l * chartMonoZ O M M' c A) * _
    rw [map_mul (aeval (pairProjCoord y e φ φ' t)) (U l), (hU l).2, aeval_chartMonoZ,
      map_mul (algebraMap Ω Φ) (r l * segreVec y c ^ n₀)]

variable [∀ k, Fintype (ι k)]

def IsZPair (a₀ a₀' : K → ℤ) (z : (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ)
    (f g : MRing (bundleIdx (bundleIdx ι M) M') O) : Prop :=
  (∃ bf bg : Option (Option K) → ℕ, IsMultiHomog f bf ∧ IsMultiHomog g bg ∧
    (fun o => (bf o : ℤ) - bg o) = zetaFirst a₀ - zetaSecond a₀') ∧ aeval z f = aeval z g

omit [Algebra O Ω] [IsScalarTower O Ω Φ] in

/- English proof (translation)
Take `⟨⟨bf, bg, hf, hg, hd⟩, hv⟩` from `h`. Take `⟨⟨bf', bg', hf', hg', hd'⟩, hv'⟩` from `h'`. Conclude with `cross_mem hf hg hf' hg' (fun o => (congrFun hd o).trans (congrFun hd' o).symm) hv hv'`.
-/
theorem IsZPair.cross {a₀ a₀' : K → ℤ} {z : (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ}
    {f g f' g' : MRing (bundleIdx (bundleIdx ι M) M') O} (h : IsZPair a₀ a₀' z f g)
    (h' : IsZPair a₀ a₀' z f' g') : f * g' - f' * g ∈ pointIdeal O z := by
  obtain ⟨⟨bf, bg, hf, hg, hd⟩, hv⟩ := h
  obtain ⟨⟨bf', bg', hf', hg', hd'⟩, hv'⟩ := h'
  exact cross_mem hf hg hf' hg' (fun o => (congrFun hd o).trans (congrFun hd' o).symm) hv hv'

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] [Algebra O Ω] [IsScalarTower O Ω Φ] in

/- English proof (translation)
Rewrite using `[map_sum, map_mul, hx, mul_comm, hval]`. Conclude with `Finset.sum_congr rfl fun l _ => by rw [map_mul, hxs, mul_comm]`.
-/
theorem val_pair {z : (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ} {L : ℕ}
    {xs : Fin L → MRing (bundleIdx (bundleIdx ι M) M') O} {v : Fin L → Φ} (hxs : ∀ l, aeval z (xs l) = v l)
    (G : Fin L → MRing (bundleIdx (bundleIdx ι M) M') O) {x : MRing (bundleIdx (bundleIdx ι M) M') O} {w : Φ}
    (hx : aeval z x = w) (H : MRing (bundleIdx (bundleIdx ι M) M') O)
    (hval : aeval z H * w = ∑ l, aeval z (G l) * v l) :
    aeval z (∑ l, xs l * G l) = aeval z (x * H) := by
  rw [map_sum, map_mul, hx, mul_comm, hval]
  exact Finset.sum_congr rfl fun l _ => by rw [map_mul, hxs, mul_comm]

/- English proof (translation)
Use `choose c hc using fun k : K => hWr (some (some k))`. Take `⟨l₀, hl₀⟩` from `hWr (some none)`. Take `⟨m₁, hm₁⟩` from `hWr none`. Establish `nz : ∀ p, (X p : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ W → pairProjCoord y e φ φ' t p ≠ 0`. Introduce `p hp h0`.

Conclude with `hp (hPW (mem_of_homog (isWeightedHomogeneous_X O _ p) (by rw [aeval_X]; exact h0)))`. Establish `hyc : segreVec y c ≠ 0`. Use `Finset.prod_ne_zero_iff.mpr fun k _ h0 => nz _ (hc k) ?_` and prove the remaining obligations. Use `show algebraMap Ω Φ (y ⟨k, c k⟩) = 0`. Rewrite using `[h0, map_zero]`.

Establish `hmono : ∀ (n : ℕ) (α : K → ℕ), (C (ϖ ^ n) * chartMonoZ O M M' c α) ∉ W`. Introduce `n α hm`. Break down `hW.mem_or_mem hm with h | h` into its components or cases. Rewrite `h` using `[map_pow]`. Conclude with `hϖW (hW.mem_of_pow_mem n h)`.

Use `hW` as an intermediate fact. Take `⟨k, -, hk⟩` from `Ideal.IsPrime.prod_mem_iff.mp h`. Conclude with `hc k (hW.mem_of_pow_mem _ hk)`. Prove the components needed by the constructor for the conclusion. Take `⟨n, r, hr, hx⟩` from `hexp O ϖ Ω K ι y N E B B' hB a₀ a₀' M M' φ φ' hφ hφ' c hyc m₁`.

Take `⟨bG, bH, G, hG, hdeg, hval⟩` from `express_forms (M := M) (M' := M') y e φ φ' t c hyc ϖ φ (φ' m₁) a₀ a₀' n r hr hx`. Use `⟨∑ l, X ⟨some none, l⟩ * G l, X ⟨none, m₁⟩ * (C (ϖ ^ n) * chartMonoZ O M M' c bH), ⟨⟨Pi.single (some none) 1 + vdeg bG, Pi.single none 1 + vdeg bH, ?_, ?_, ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `IsWeightedHomogeneous.sum _ _ _ fun l _ => IsWeightedHomogeneous.mul (isWeightedHomogeneous_X O _ _) (hG l)`. Use `IsWeightedHomogeneous.mul (isWeightedHomogeneous_X O (blockWeight (bundleIdx (bundleIdx ι M) M')) ⟨none, m₁⟩) (IsWeightedHomogeneous.mul (isWeightedHomogeneous_C _ (ϖ ^ n)) (chartMonoZ_homog (O := O) (M := M) (M' := M') c bH))` as an intermediate fact. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis.

Use function extensionality and compare the values at `o`. Break down `o with _ | _ | k` into its components or cases. Simplify using `[vdeg, zetaFirst, zetaSecond]`. Simplify using `[vdeg, zetaFirst, zetaSecond]`. Simplify using `[vdeg, zetaFirst, zetaSecond]`.

Combine the linear relations using `[hdeg k]`. Conclude with `val_pair (z := pairProjCoord y e φ φ' t) (v := fun l => genVal e t (φ l)) (w := genVal e t (φ' m₁)) (fun l => aeval_X _ _) G (aeval_X _ _) _ hval`. Introduce `hm`. Break down `hW.mem_or_mem hm with h | h` into its components or cases. Conclude with `hm₁ h`.

Conclude with `hmono n bH h`. Take `⟨n, r, hr, hx⟩` from `hexp O ϖ Ω K ι y N E B' B (fun c hc => ⟨(hB c hc).2, (hB c hc).1⟩) a₀' a₀ M' M φ' φ hφ' hφ c hyc l₀`. Take `⟨bG, bH, G, hG, hdeg, hval⟩` from `express_forms (M := M) (M' := M') y e φ φ' t c hyc ϖ φ' (φ l₀) a₀' a₀ n r hr hx`. Use `⟨X ⟨some none, l₀⟩ * (C (ϖ ^ n) * chartMonoZ O M M' c bH), ∑ m, X ⟨none, m⟩ * G m, ⟨⟨Pi.single (some none) 1 + vdeg bH, Pi.single none 1 + vdeg bG, ?_, ?_, ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Use `IsWeightedHomogeneous.mul (isWeightedHomogeneous_X O (blockWeight (bundleIdx (bundleIdx ι M) M')) ⟨some none, l₀⟩) (IsWeightedHomogeneous.mul (isWeightedHomogeneous_C _ (ϖ ^ n)) (chartMonoZ_homog (O := O) (M := M) (M' := M') c bH))` as an intermediate fact.

Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis. Conclude with `IsWeightedHomogeneous.sum _ _ _ fun m _ => IsWeightedHomogeneous.mul (isWeightedHomogeneous_X O _ _) (hG m)`. Use function extensionality and compare the values at `o`. Break down `o with _ | _ | k` into its components or cases. Simplify using `[vdeg, zetaFirst, zetaSecond]`.

Simplify using `[vdeg, zetaFirst, zetaSecond]`. Simplify using `[vdeg, zetaFirst, zetaSecond]`. Combine the linear relations using `[hdeg k]`. Conclude with `(val_pair (z := pairProjCoord y e φ φ' t) (v := fun m => genVal e t (φ' m)) (w := genVal e t (φ l₀)) (fun m => aeval_X _ _) G (aeval_X _ _) _ hval).symm`. Introduce `hm`.

Break down `hW.mem_or_mem hm with h | h` into its components or cases. Conclude with `hl₀ h`. Conclude with `hmono n bH h`.
-/
theorem pairs_at (hexp : TwistedDualGensExpress.Statement) {ϖ : O} (y : (Σ k, ι k) → Ω)
    (B B' : ChartBundle O (segreVec y) N E) (hB : SameGenericFibre ϖ B B') (a₀ a₀' : K → ℤ)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E)
    (hφ : IsTwistedDualGens y B a₀ φ) (hφ' : IsTwistedDualGens y B' a₀' φ')
    (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ)
    (W : Ideal (MRing (bundleIdx (bundleIdx ι M) M') O)) (hW : W.IsPrime)
    (hPW : pointIdeal O (pairProjCoord y e φ φ' t) ≤ W) (hWr : IsRelevant W)
    (hϖW : (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ W) :
    (∃ f g, IsZPair a₀ a₀' (pairProjCoord y e φ φ' t) f g ∧ g ∉ W) ∧
      (∃ f g, IsZPair a₀ a₀' (pairProjCoord y e φ φ' t) f g ∧ f ∉ W) := by
  choose c hc using fun k : K => hWr (some (some k))
  obtain ⟨l₀, hl₀⟩ := hWr (some none)
  obtain ⟨m₁, hm₁⟩ := hWr none
  have nz : ∀ p, (X p : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ W → pairProjCoord y e φ φ' t p ≠ 0 := by
    intro p hp h0
    exact hp (hPW (mem_of_homog (isWeightedHomogeneous_X O _ p) (by rw [aeval_X]; exact h0)))
  have hyc : segreVec y c ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun k _ h0 => nz _ (hc k) ?_
    show algebraMap Ω Φ (y ⟨k, c k⟩) = 0
    rw [h0, map_zero]
  have hmono : ∀ (n : ℕ) (α : K → ℕ), (C (ϖ ^ n) * chartMonoZ O M M' c α) ∉ W := by
    intro n α hm
    rcases hW.mem_or_mem hm with h | h
    · rw [map_pow] at h
      exact hϖW (hW.mem_of_pow_mem n h)
    · have := hW
      obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
      exact hc k (hW.mem_of_pow_mem _ hk)
  constructor
  · obtain ⟨n, r, hr, hx⟩ := hexp O ϖ Ω K ι y N E B B' hB a₀ a₀' M M' φ φ' hφ hφ' c hyc m₁
    obtain ⟨bG, bH, G, hG, hdeg, hval⟩ :=
      express_forms (M := M) (M' := M') y e φ φ' t c hyc ϖ φ (φ' m₁) a₀ a₀' n r hr hx
    refine ⟨∑ l, X ⟨some none, l⟩ * G l, X ⟨none, m₁⟩ * (C (ϖ ^ n) * chartMonoZ O M M' c bH),
      ⟨⟨Pi.single (some none) 1 + vdeg bG, Pi.single none 1 + vdeg bH, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · exact IsWeightedHomogeneous.sum _ _ _ fun l _ =>
        IsWeightedHomogeneous.mul (isWeightedHomogeneous_X O _ _) (hG l)
    · have := IsWeightedHomogeneous.mul
        (isWeightedHomogeneous_X O (blockWeight (bundleIdx (bundleIdx ι M) M')) ⟨none, m₁⟩)
        (IsWeightedHomogeneous.mul (isWeightedHomogeneous_C _ (ϖ ^ n))
          (chartMonoZ_homog (O := O) (M := M) (M' := M') c bH))
      rwa [zero_add] at this
    · funext o
      rcases o with _ | _ | k
      · simp [vdeg, zetaFirst, zetaSecond]
      · simp [vdeg, zetaFirst, zetaSecond]
      · simp [vdeg, zetaFirst, zetaSecond]
        linarith [hdeg k]
    · exact val_pair (z := pairProjCoord y e φ φ' t) (v := fun l => genVal e t (φ l))
        (w := genVal e t (φ' m₁)) (fun l => aeval_X _ _) G (aeval_X _ _) _ hval
    · intro hm
      rcases hW.mem_or_mem hm with h | h
      · exact hm₁ h
      · exact hmono n bH h
  · obtain ⟨n, r, hr, hx⟩ := hexp O ϖ Ω K ι y N E B' B (fun c hc => ⟨(hB c hc).2, (hB c hc).1⟩)
      a₀' a₀ M' M φ' φ hφ' hφ c hyc l₀
    obtain ⟨bG, bH, G, hG, hdeg, hval⟩ :=
      express_forms (M := M) (M' := M') y e φ φ' t c hyc ϖ φ' (φ l₀) a₀' a₀ n r hr hx
    refine ⟨X ⟨some none, l₀⟩ * (C (ϖ ^ n) * chartMonoZ O M M' c bH), ∑ m, X ⟨none, m⟩ * G m,
      ⟨⟨Pi.single (some none) 1 + vdeg bH, Pi.single none 1 + vdeg bG, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · have := IsWeightedHomogeneous.mul
        (isWeightedHomogeneous_X O (blockWeight (bundleIdx (bundleIdx ι M) M')) ⟨some none, l₀⟩)
        (IsWeightedHomogeneous.mul (isWeightedHomogeneous_C _ (ϖ ^ n))
          (chartMonoZ_homog (O := O) (M := M) (M' := M') c bH))
      rwa [zero_add] at this
    · exact IsWeightedHomogeneous.sum _ _ _ fun m _ =>
        IsWeightedHomogeneous.mul (isWeightedHomogeneous_X O _ _) (hG m)
    · funext o
      rcases o with _ | _ | k
      · simp [vdeg, zetaFirst, zetaSecond]
      · simp [vdeg, zetaFirst, zetaSecond]
      · simp [vdeg, zetaFirst, zetaSecond]
        linarith [hdeg k]
    · exact (val_pair (z := pairProjCoord y e φ φ' t) (v := fun m => genVal e t (φ' m))
        (w := genVal e t (φ l₀)) (fun m => aeval_X _ _) G (aeval_X _ _) _ hval).symm
    · intro hm
      rcases hW.mem_or_mem hm with h | h
      · exact hl₀ h
      · exact hmono n bH h

end Forms

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht hZ`. Establish `hP : (pointIdeal O (pairProjCoord y e φ φ' t)).IsPrime` using `hZ.multiProj.isPrime`. Establish `hϖP : (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ pointIdeal O (pairProjCoord y e φ φ' t)`. Introduce `hm`. Establish `h1 : ϖ ∈ (pointIdeal O (pairProjCoord y e φ φ' t)).comap (C : O →+* MRing (bundleIdx (bundleIdx ι M) M') O)` using `hm`.

Rewrite `h1` using `[hZ.noTorsion, Ideal.mem_bot]`. Conclude with `hϖ.ne_zero h1`. Establish `pairs` using `pairs_at hexp y B B' hB a₀ a₀' φ φ' hφ hφ' e t`. Take `⟨⟨f₀, g₀, hp₀, hg₀⟩, -⟩` from `pairs _ hP le_rfl hZ.multiProj.relevant hϖP`. Establish `hf₀ : f₀ ∉ pointIdeal O (pairProjCoord y e φ φ' t)`.

Introduce `hm`. Take `⟨⟨bf, bg, -, hg, -⟩, hv⟩` from `hp₀`. Conclude with `hg₀ (mem_of_homog hg (by rw [← hv]; exact aeval_eq_zero_of_mem hm))`. Use `⟨f₀, g₀, IsVerticalDivisor.of_unit_off_special hp₀.1 hf₀ hg₀ ?_, hp₀.2⟩` and prove the remaining obligations. Introduce `W hW hPW hWr hϖW`.

Take `⟨⟨f₁, g₁, hp₁, hg₁⟩, ⟨f₂, g₂, hp₂, hf₂⟩⟩` from `pairs W hW hPW hWr hϖW`. Establish `h12` using `hPW (hp₁.cross hp₂)`. Use `⟨g₁, f₁, hg₁, fun hf₁ => ?_, ?_⟩` and prove the remaining obligations. Establish `h' : f₁ * g₂ - (f₁ * g₂ - f₂ * g₁) ∈ W` using `W.sub_mem (W.mul_mem_right _ hf₁) h12`. Rewrite `h'` using `[sub_sub_cancel]`.

Break down `hW.mem_or_mem h' with h | h` into its components or cases. Conclude with `hf₂ h`. Conclude with `hg₁ h`. Rewrite using `[show g₁ * f₀ - f₁ * g₀ = f₀ * g₁ - f₁ * g₀ by ring]`. Conclude with `hp₀.cross hp₁`.
-/
theorem proof (hexp : TwistedDualGensExpress.Statement) : GenericProjClosureDivisor.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht hZ
  have hP : (pointIdeal O (pairProjCoord y e φ φ' t)).IsPrime := hZ.multiProj.isPrime
  have hϖP : (C ϖ : MRing (bundleIdx (bundleIdx ι M) M') O) ∉ pointIdeal O (pairProjCoord y e φ φ' t) := by
    intro hm
    have h1 : ϖ ∈ (pointIdeal O (pairProjCoord y e φ φ' t)).comap
        (C : O →+* MRing (bundleIdx (bundleIdx ι M) M') O) := hm
    rw [hZ.noTorsion, Ideal.mem_bot] at h1
    exact hϖ.ne_zero h1
  have pairs := pairs_at hexp y B B' hB a₀ a₀' φ φ' hφ hφ' e t
  obtain ⟨⟨f₀, g₀, hp₀, hg₀⟩, -⟩ := pairs _ hP le_rfl hZ.multiProj.relevant hϖP
  have hf₀ : f₀ ∉ pointIdeal O (pairProjCoord y e φ φ' t) := by
    intro hm
    obtain ⟨⟨bf, bg, -, hg, -⟩, hv⟩ := hp₀
    exact hg₀ (mem_of_homog hg (by rw [← hv]; exact aeval_eq_zero_of_mem hm))
  refine ⟨f₀, g₀, IsVerticalDivisor.of_unit_off_special hp₀.1 hf₀ hg₀ ?_, hp₀.2⟩
  intro W hW hPW hWr hϖW
  obtain ⟨⟨f₁, g₁, hp₁, hg₁⟩, ⟨f₂, g₂, hp₂, hf₂⟩⟩ := pairs W hW hPW hWr hϖW
  have h12 := hPW (hp₁.cross hp₂)
  refine ⟨g₁, f₁, hg₁, fun hf₁ => ?_, ?_⟩
  · have h' : f₁ * g₂ - (f₁ * g₂ - f₂ * g₁) ∈ W := W.sub_mem (W.mul_mem_right _ hf₁) h12
    rw [sub_sub_cancel] at h'
    rcases hW.mem_or_mem h' with h | h
    · exact hf₂ h
    · exact hg₁ h
  · rw [show g₁ * f₀ - f₁ * g₀ = f₀ * g₁ - f₁ * g₀ by ring]
    exact hp₀.cross hp₁

end GenericProjClosureDivisor

end

end GroundTheory.Heights₂.Heights.NumbersDVR
