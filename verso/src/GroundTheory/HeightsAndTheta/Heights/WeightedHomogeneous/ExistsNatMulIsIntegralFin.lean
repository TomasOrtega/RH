import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PointHeightDegreeHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo (mConeMap mCoordIdeal mcPts)

noncomputable section

namespace OneBlockPoints

section Denominators

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Establish `hx : IsAlgebraic ℤ x` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (.of_finite ℚ x)`. Take `⟨m, s, hm, hs⟩` from `hx.exists_nsmul_eq (𝓞 K)`. Use `⟨m, Nat.pos_of_ne_zero hm, ?_⟩` and prove the remaining obligations. Rewrite using `[← nsmul_eq_mul, hs]`. Conclude with `RingOfIntegers.isIntegral_coe s`.
-/
theorem exists_nat_mul_isIntegral (x : K) : ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : K) * x) := by
  have hx : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (.of_finite ℚ x)
  obtain ⟨m, s, hm, hs⟩ := hx.exists_nsmul_eq (𝓞 K)
  refine ⟨m, Nat.pos_of_ne_zero hm, ?_⟩
  rw [← nsmul_eq_mul, hs]
  exact RingOfIntegers.isIntegral_coe s

/- English proof (translation)
Use `choose m hm hi using fun i ↦ exists_nat_mul_isIntegral (x i)`. Use `⟨∏ i, m i, Finset.prod_pos fun i _ ↦ hm i, fun i ↦ ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem m (Finset.mem_univ i)`. Rewrite using `[hc, Nat.cast_mul, mul_comm (m i : K), mul_assoc]`. Establish `hc' : IsIntegral ℤ (c : K)`.

Simplify using `using (isIntegral_algebraMap (R := ℤ) (A := K) (x := (c : ℤ)))`. Conclude with `hc'.mul (hi i)`.
-/
theorem exists_nat_mul_isIntegral_fin {ι : Type*} [Fintype ι] (x : ι → K) :
    ∃ m : ℕ, 0 < m ∧ ∀ i, IsIntegral ℤ ((m : K) * x i) := by
  choose m hm hi using fun i ↦ exists_nat_mul_isIntegral (x i)
  refine ⟨∏ i, m i, Finset.prod_pos fun i _ ↦ hm i, fun i ↦ ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  rw [hc, Nat.cast_mul, mul_comm (m i : K), mul_assoc]
  have hc' : IsIntegral ℤ (c : K) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := (c : ℤ)))
  exact hc'.mul (hi i)

/- English proof (translation)
Take `⟨S, hS⟩` from `hL`. Take `⟨D, hD, hi⟩` from `exists_nat_mul_isIntegral_fin (fun p : S × Fin m ↦ (p.1 : Fin m → K) p.2)`. Use `⟨D, hD, fun v hv ↦ ?_⟩` and prove the remaining obligations. Rewrite `hv` using `[← hS]`. Proceed by induction on `hv using Submodule.span_induction with`.

Consider the case `mem u hu => exact fun j ↦ hi (⟨u, hu⟩, j)`. Consider the case `zero => intro j`. Simplify using `using (isIntegral_zero : IsIntegral ℤ (0 : K))`. Consider the case `add a b _ _ ha hb => intro j`. Simplify `(ha j).add (hb j)` using `[mul_add]`.

Consider the case `smul c a _ ha`. Introduce `j`. Establish `h` using `(RingOfIntegers.isIntegral_coe c).mul (ha j)`. Rewrite using `[Pi.smul_apply, Algebra.smul_def, mul_left_comm]`. Conclude with `h`.
-/
theorem exists_nat_lattice_integral {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) (hL : L.FG) :
    ∃ D : ℕ, 0 < D ∧ ∀ v ∈ L, ∀ j, IsIntegral ℤ ((D : K) * v j) := by
  obtain ⟨S, hS⟩ := hL
  obtain ⟨D, hD, hi⟩ := exists_nat_mul_isIntegral_fin (fun p : S × Fin m ↦ (p.1 : Fin m → K) p.2)
  refine ⟨D, hD, fun v hv ↦ ?_⟩
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem u hu => exact fun j ↦ hi (⟨u, hu⟩, j)
  | zero => intro j; simpa using (isIntegral_zero : IsIntegral ℤ (0 : K))
  | add a b _ _ ha hb => intro j; simpa [mul_add] using (ha j).add (hb j)
  | smul c a _ ha =>
    intro j
    have h := (RingOfIntegers.isIntegral_coe c).mul (ha j)
    rw [Pi.smul_apply, Algebra.smul_def, mul_left_comm]
    exact h

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction generalizing j with`. Consider the case `mem u hu`. Take `⟨i, rfl⟩` from `hu`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality.

Simplify using `using (isIntegral_one : IsIntegral ℤ (1 : K))`. Simplify `(isIntegral_zero : IsIntegral ℤ (0 : K))` using `[Pi.single_apply, h]`. Consider the case `zero => simpa using (isIntegral_zero : IsIntegral ℤ (0 : K))`. Consider the case `add a b _ _ ha hb => exact (ha j).add (hb j)`. Consider the case `smul c a _ ha`.

Rewrite using `[Pi.smul_apply, Algebra.smul_def]`. Conclude with `(RingOfIntegers.isIntegral_coe c).mul (ha j)`.
-/
theorem isIntegral_of_mem_standard {n : ℕ} {v : Fin n → K}
    (hv : v ∈ (HermLattice.standard K n).lattice) (j : Fin n) : IsIntegral ℤ (v j) := by
  induction hv using Submodule.span_induction generalizing j with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    by_cases h : j = i
    · subst h
      simpa using (isIntegral_one : IsIntegral ℤ (1 : K))
    · simpa [Pi.single_apply, h] using (isIntegral_zero : IsIntegral ℤ (0 : K))
  | zero => simpa using (isIntegral_zero : IsIntegral ℤ (0 : K))
  | add a b _ _ ha hb => exact (ha j).add (hb j)
  | smul c a _ ha =>
    rw [Pi.smul_apply, Algebra.smul_def]
    exact (RingOfIntegers.isIntegral_coe c).mul (ha j)

end Denominators

section Forms

variable {K : Type} [Field K] [NumberField K] {e r : ℕ}

omit [NumberField K] in

/- English proof (translation)
Rewrite using `[Finset.sum_apply, ← (oneBlockIndex e r).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]`. Rewrite using `[Finset.sum_eq_single j]`. Use `Finset.sum_congr rfl fun a _ ↦ ?_` and prove the remaining obligations. Simplify using `[oneBlockForms]`. Introduce `j' _ hj'`.

Use `Finset.sum_eq_zero fun a _ ↦ ?_` and prove the remaining obligations. Simplify using `[oneBlockForms, Ne.symm hj']`. Simplify using the standard rewrite rules.
-/
theorem sum_smul_oneBlockForms_apply (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K))
    (f : Fin (oneBlockSize e r + 1) → ℤ) (j : Fin (r + 1)) :
    (∑ b, f b • oneBlockForms om b) j = ∑ a, f ((oneBlockIndex e r).symm (a, j)) • ((om a : 𝓞 K) : K) := by
  rw [Finset.sum_apply, ← (oneBlockIndex e r).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_eq_single j]
  · refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp [oneBlockForms]
  · intro j' _ hj'
    refine Finset.sum_eq_zero fun a _ ↦ ?_
    simp [oneBlockForms, Ne.symm hj']
  · simp

omit [NumberField K] in

/- English proof (translation)
Rewrite using `[← (oneBlockIndex e r).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]`. Rewrite using `[Finset.sum_eq_single j]`. Use `Finset.sum_congr rfl fun a _ ↦ ?_` and prove the remaining obligations. Simplify using `[oneBlockForms]`. Introduce `j' _ hj'`.

Use `Finset.sum_eq_zero fun a _ ↦ ?_` and prove the remaining obligations. Simplify using `[oneBlockForms, Ne.symm hj']`. Simplify using the standard rewrite rules.
-/
theorem sum_mul_oneBlockForms (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K))
    (g : Fin (oneBlockSize e r + 1) → ℂ) (τ : K →+* ℂ) (j : Fin (r + 1)) :
    ∑ b, g b * τ (oneBlockForms om b j) = ∑ a, g ((oneBlockIndex e r).symm (a, j)) * τ ((om a : 𝓞 K) : K) := by
  rw [← (oneBlockIndex e r).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_eq_single j]
  · refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp [oneBlockForms]
  · intro j' _ hj'
    refine Finset.sum_eq_zero fun a _ ↦ ?_
    simp [oneBlockForms, Ne.symm hj']
  · simp

omit [NumberField K] in

/- English proof (translation)
Set `s : Fin (r + 1) → 𝓞 K` to `fun j ↦ ⟨u j, hu j⟩`. Use `⟨fun p ↦ om.repr (s (oneBlockIndex e r p).2) (oneBlockIndex e r p).1, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Rewrite using `[sum_smul_oneBlockForms_apply]`. Simplify using `only [Equiv.apply_symm_apply]`.

Establish `h` using `congrArg (algebraMap (𝓞 K) K) (om.sum_repr (s j))`. Simplify using `only [map_sum, map_zsmul] at h`. Conclude with `h`.
-/
theorem exists_int_comb_oneBlockForms (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K))
    (u : Fin (r + 1) → K) (hu : ∀ j, IsIntegral ℤ (u j)) :
    ∃ c : Fin (oneBlockSize e r + 1) → ℤ, ∑ p, c p • oneBlockForms om p = u := by
  let s : Fin (r + 1) → 𝓞 K := fun j ↦ ⟨u j, hu j⟩
  refine ⟨fun p ↦ om.repr (s (oneBlockIndex e r p).2) (oneBlockIndex e r p).1, ?_⟩
  funext j
  rw [sum_smul_oneBlockForms_apply]
  simp only [Equiv.apply_symm_apply]
  have h := congrArg (algebraMap (𝓞 K) K) (om.sum_repr (s j))
  simp only [map_sum, map_zsmul] at h
  exact h

/- English proof (translation)
Use `⟨?_, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg p`. Establish `hj` using `congrFun hg (oneBlockIndex e r p).2`. Rewrite `hj` using `[sum_smul_oneBlockForms_apply]`.

Establish `h0 : ∑ a, g ((oneBlockIndex e r).symm (a, (oneBlockIndex e r p).2)) • om a = 0`. Apply `FaithfulSMul.algebraMap_injective (𝓞 K) K` to reduce the goal to its premises. Simplify `hj` using `[map_sum, map_zsmul]`. Use `(Fintype.linearIndependent_iff.mp om.linearIndependent) _ h0 (oneBlockIndex e r p).1` as an intermediate fact. Simplify using `using this`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨p, rfl⟩ v hv`. Take `⟨t, ht⟩` from `(IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).mp (isIntegral_of_mem_standard hv (oneBlockIndex e r p).2)`. Use `⟨om (oneBlockIndex e r p).1 * t, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ht]`.

Simplify using `[oneBlockForms]`. Introduce `χ hχ`. Establish `hi : ∀ j, IsIntegral ℤ (χ j)`. Introduce `j`. Take `⟨a, ha⟩` from `hχ (Pi.single j 1) (Submodule.subset_span ⟨j, rfl⟩)`.

Establish `h1 : χ ⬝ᵥ (Pi.single j 1 : Fin (r + 1) → K) = χ j` using `by simp`. Rewrite using `[← h1, ← ha]`. Conclude with `RingOfIntegers.isIntegral_coe a`. Take `⟨c, hc⟩` from `exists_int_comb_oneBlockForms om χ hi`. Rewrite using `[← hc]`.

Conclude with `Submodule.sum_mem _ fun p _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)`.
-/
theorem isDualBasis_oneBlockForms (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) :
    IsDualBasis (HermLattice.standard K (r + 1)).lattice (oneBlockForms (r := r) om) := by
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg p
    have hj := congrFun hg (oneBlockIndex e r p).2
    rw [sum_smul_oneBlockForms_apply] at hj
    have h0 : ∑ a, g ((oneBlockIndex e r).symm (a, (oneBlockIndex e r p).2)) • om a = 0 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      simpa [map_sum, map_zsmul] using hj
    have := (Fintype.linearIndependent_iff.mp om.linearIndependent) _ h0 (oneBlockIndex e r p).1
    simpa using this
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩ v hv
    obtain ⟨t, ht⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).mp
      (isIntegral_of_mem_standard hv (oneBlockIndex e r p).2)
    refine ⟨om (oneBlockIndex e r p).1 * t, ?_⟩
    rw [map_mul, ht]
    simp [oneBlockForms]
  · intro χ hχ
    have hi : ∀ j, IsIntegral ℤ (χ j) := by
      intro j
      obtain ⟨a, ha⟩ := hχ (Pi.single j 1) (Submodule.subset_span ⟨j, rfl⟩)
      have h1 : χ ⬝ᵥ (Pi.single j 1 : Fin (r + 1) → K) = χ j := by simp
      rw [← h1, ← ha]
      exact RingOfIntegers.isIntegral_coe a
    obtain ⟨c, hc⟩ := exists_int_comb_oneBlockForms om χ hi
    rw [← hc]
    exact Submodule.sum_mem _ fun p _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

omit [NumberField K] in
/- English proof (translation)
Rewrite using `[latticeForm, Finset.sum_eq_single j (fun j' _ hj' ↦ by simp [hj']) (by simp), Pi.single_eq_same]`.
-/
theorem latticeForm_single {m : ℕ} (j : Fin m) (x : K) :
    latticeForm (Pi.single j x : Fin m → K) = C x * X j := by
  rw [latticeForm, Finset.sum_eq_single j (fun j' _ hj' ↦ by simp [hj'])
    (by simp), Pi.single_eq_same]

omit [NumberField K] in

/- English proof (translation)
Use `MvPolynomial.ringHom_ext (fun a ↦ by simp [latticeMap, Heights.oneBlockMap]) fun v ↦ ?_` and prove the remaining obligations. Simplify using `only [latticeMap, Heights.oneBlockMap, coe_eval₂Hom, eval₂_X, oneBlockForms]`. Conclude with `latticeForm_single _ _`.
-/
theorem latticeMap_oneBlockForms (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) :
    latticeMap (oneBlockForms (r := r) om) = Heights.oneBlockMap om := by
  refine MvPolynomial.ringHom_ext (fun a ↦ by simp [latticeMap, Heights.oneBlockMap]) fun v ↦ ?_
  simp only [latticeMap, Heights.oneBlockMap, coe_eval₂Hom, eval₂_X, oneBlockForms]
  exact latticeForm_single _ _

omit [NumberField K] in
/- English proof (translation)
Rewrite using `[latticeIdeal, Heights.oneBlockIdeal, latticeMap_oneBlockForms]`.
-/
theorem latticeIdeal_oneBlockForms (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) :
    latticeIdeal (oneBlockForms (r := r) om) = Heights.oneBlockIdeal om := by
  rw [latticeIdeal, Heights.oneBlockIdeal, latticeMap_oneBlockForms]

omit [NumberField K] in
/- English proof (translation)
Use function extensionality and compare the values at `u p`. Rewrite using `[latticePoint, Finset.sum_eq_single (oneBlockIndex e r p).2 (fun j _ hj ↦ by simp [oneBlockForms, hj]) (by simp)]`. Simplify using `[oneBlockForms, Heights.oneBlockPoint]`.
-/
theorem latticePoint_oneBlockForms (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) (σ : K →+* ℂ)
    (w : Fin (r + 1) → ℂ) : latticePoint (oneBlockForms om) σ w = Heights.oneBlockPoint om σ w := by
  funext u p
  rw [latticePoint, Finset.sum_eq_single (oneBlockIndex e r p).2
    (fun j _ hj ↦ by simp [oneBlockForms, hj]) (by simp)]
  simp [oneBlockForms, Heights.oneBlockPoint]

omit [NumberField K] in

/- English proof (translation)
Rewrite using `[latticePoint_oneBlockForms]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl m j`. Simplify using `[coneToPairs, Heights.oneBlockPoint]`. Introduce `h`.

Use function extensionality and compare the values at `u v`. Use `h (oneBlockIndex e r v).1 (oneBlockIndex e r v).2` as an intermediate fact. Simplify `this` using `[coneToPairs, Heights.oneBlockPoint]`.
-/
theorem eq_latticePoint_iff (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) (y : Cone (oneBlockSizes e r) ℂ)
    (σ : K →+* ℂ) (w : Fin (r + 1) → ℂ) :
    y = latticePoint (oneBlockForms om) σ w ↔
      ∀ m j, coneToPairs y ⟨(), (m, j)⟩ = σ (om m : K) * w j := by
  rw [latticePoint_oneBlockForms]
  constructor
  · rintro rfl m j
    simp [coneToPairs, Heights.oneBlockPoint]
  · intro h
    funext u v
    have := h (oneBlockIndex e r v).1 (oneBlockIndex e r v).2
    simpa [coneToPairs, Heights.oneBlockPoint] using this

omit [NumberField K] in

def pairsToCone (z : (Σ _ : Unit, Fin (e + 1) × Fin (r + 1)) → ℂ) : Cone (oneBlockSizes e r) ℂ :=
  fun _ v ↦ z ⟨(), oneBlockIndex e r v⟩

omit [NumberField K] in
/- English proof (translation)
Use function extensionality and compare the values at `p`. Break down `p with ⟨⟨⟩, q⟩` into its components or cases. Simplify using `[coneToPairs, pairsToCone]`.
-/
theorem coneToPairs_pairsToCone (z : (Σ _ : Unit, Fin (e + 1) × Fin (r + 1)) → ℂ) :
    coneToPairs (pairsToCone z) = z := by
  funext p
  rcases p with ⟨⟨⟩, q⟩
  simp [coneToPairs, pairsToCone]

end Forms

section OfLattice

variable {K : Type} [Field K] [NumberField K]

open Classical in

/- English proof (translation)
Establish `h` using `congrFun (congrFun hM σ) σ`. Simplify using `only [Matrix.mul_apply, embMat, Matrix.of_apply, Matrix.one_apply_eq] at h`. Repeatedly rewrite using `[hz, ← mul_assoc, ← Finset.sum_mul, h, one_mul]`.
-/
theorem recover {d i : ℕ} (om : Module.Basis (Fin d) ℤ (𝓞 K)) (Minv : Matrix (K →+* ℂ) (Fin d) ℂ)
    (hM : Minv * embMat om = 1) (z : (Σ _ : Unit, Fin d × Fin (i + 1)) → ℂ) (σ : K →+* ℂ)
    (w : Fin (i + 1) → ℂ) (hz : ∀ m j, z ⟨(), (m, j)⟩ = σ (om m : K) * w j) (j : Fin (i + 1)) :
    w j = ∑ m, Minv σ m * z ⟨(), (m, j)⟩ := by
  have h := congrFun (congrFun hM σ) σ
  simp only [Matrix.mul_apply, embMat, Matrix.of_apply, Matrix.one_apply_eq] at h
  simp_rw [hz, ← mul_assoc, ← Finset.sum_mul, h, one_mul]

def embEquiv {d : ℕ} (om : Module.Basis (Fin d) ℤ (𝓞 K)) : Fin d ≃ (K →+* ℂ) :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, NumberField.Embeddings.card K ℂ, ← RingOfIntegers.rank,
      Module.finrank_eq_card_basis om, Fintype.card_fin])

open Classical in

/- English proof (translation)
Introduce `K _ _ d om i`. Take `_ | e` from `d`. Conclude with `absurd om.index_nonempty (not_nonempty_iff.mpr inferInstance)`. Take `⟨h1, -, h3⟩` from `hA K i (oneBlockSize e i) (HermLattice.standard K (i + 1)) (oneBlockForms om) (isDualBasis_oneBlockForms om)`. Use `choose R hR using h3`.

Set `Minv : Matrix (K →+* ℂ) (Fin (e + 1)) ℂ` to `Matrix.of fun σ m ↦ R σ 0 ((oneBlockIndex e i).symm (m, 0))`. Establish `hM : Minv * embMat om = 1`. Use extensionality with `σ τ`. Establish `h` using `hR σ 0 τ 0`. Rewrite `h` using `[sum_mul_oneBlockForms]`.

Simplify using `only [Matrix.mul_apply, embMat, Matrix.of_apply, Minv, Matrix.one_apply]`. Rewrite using `[h]`. Distinguish the cases in `hστ : σ = τ`. Substitute `hστ` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hστ, Ne.symm hστ]`. Use `⟨fun z hz ↦ ?_, ⟨Minv, hM, (mul_eq_one_comm_of_equiv (embEquiv om).symm).mp hM⟩, recover om⟩` and prove the remaining obligations. Rewrite `hz` using `[← coneToPairs_pairsToCone z, ← mem_conePoints_iff, ← latticeIdeal_oneBlockForms]`. Take `⟨σ, ⟨w, hw, hzw⟩, huniq⟩` from `h1 _ hz`. Use `⟨σ, ⟨w, hw, ?_⟩, fun τ ⟨w', hw', hzw'⟩ ↦ huniq τ ⟨w', hw', ?_⟩⟩` and prove the remaining obligations.

Use `(eq_latticePoint_iff om _ σ w).mp hzw` as an intermediate fact. Rewrite `this` using `[coneToPairs_pairsToCone]`. Then use the resulting hypothesis. Rewrite using `[eq_latticePoint_iff, coneToPairs_pairsToCone]`. Conclude with `hzw'`.
-/
theorem of_lattice (hA : Heights.OneBlockPoints.Statement) : OneBlockPoints.Statement := by
  intro K _ _ d om i
  obtain _ | e := d
  · exact absurd om.index_nonempty (not_nonempty_iff.mpr inferInstance)
  obtain ⟨h1, -, h3⟩ := hA K i (oneBlockSize e i) (HermLattice.standard K (i + 1))
    (oneBlockForms om) (isDualBasis_oneBlockForms om)
  choose R hR using h3
  let Minv : Matrix (K →+* ℂ) (Fin (e + 1)) ℂ := Matrix.of fun σ m ↦ R σ 0 ((oneBlockIndex e i).symm (m, 0))
  have hM : Minv * embMat om = 1 := by
    ext σ τ
    have h := hR σ 0 τ 0
    rw [sum_mul_oneBlockForms] at h
    simp only [Matrix.mul_apply, embMat, Matrix.of_apply, Minv, Matrix.one_apply]
    rw [h]
    by_cases hστ : σ = τ
    · subst hστ; simp
    · simp [hστ, Ne.symm hστ]
  refine ⟨fun z hz ↦ ?_, ⟨Minv, hM, (mul_eq_one_comm_of_equiv (embEquiv om).symm).mp hM⟩, recover om⟩
  rw [← coneToPairs_pairsToCone z, ← mem_conePoints_iff, ← latticeIdeal_oneBlockForms] at hz
  obtain ⟨σ, ⟨w, hw, hzw⟩, huniq⟩ := h1 _ hz
  refine ⟨σ, ⟨w, hw, ?_⟩, fun τ ⟨w', hw', hzw'⟩ ↦ huniq τ ⟨w', hw', ?_⟩⟩
  · have := (eq_latticePoint_iff om _ σ w).mp hzw
    rwa [coneToPairs_pairsToCone] at this
  · rw [eq_latticePoint_iff, coneToPairs_pairsToCone]
    exact hzw'

end OfLattice

section OfStandard

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
/- English proof (translation)
Simplify using `[Finset.sum_apply, map_sum, zsmul_eq_mul]`.
-/
theorem sum_intCast_mul_apply {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℤ) (u : ι → Fin m → K)
    (τ : K →+* ℂ) (j : Fin m) : ∑ i, (c i : ℂ) * τ (u i j) = τ ((∑ i, c i • u i) j) := by
  simp [Finset.sum_apply, map_sum, zsmul_eq_mul]

omit [NumberField K] in
/- English proof (translation)
Repeatedly rewrite using `[Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← sum_intCast_mul_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[zsmul_eq_mul, mul_assoc]`.
-/
theorem sum_zsmul_sum_mul {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℤ) (u : ι → Fin m → K)
    (τ : K →+* ℂ) (w : Fin m → ℂ) :
    ∑ i, c i • ∑ j, τ (u i j) * w j = ∑ j, τ ((∑ i, c i • u i) j) * w j := by
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← sum_intCast_mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [zsmul_eq_mul, mul_assoc]

/- English proof (translation)
Repeatedly rewrite using `[Finset.sum_smul, Finset.smul_sum, mul_smul]`. Conclude with `Finset.sum_comm`.
-/
theorem sum_comb_comb {M : Type*} [AddCommGroup M] {ι κ : Type*} [Fintype ι] [Fintype κ] (q : κ → ℤ)
    (c : κ → ι → ℤ) (x : ι → M) :
    ∑ b, (∑ p, q p * c p b) • x b = ∑ p, q p • ∑ b, c p b • x b := by
  simp_rw [Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

omit [NumberField K] in
/- English proof (translation)
Simplify using `only [latticeForm, Finset.smul_sum, Finset.sum_apply, Pi.smul_apply, map_sum, map_zsmul, Finset.sum_mul, smul_mul_assoc]`. Conclude with `Finset.sum_comm`.
-/
theorem latticeForm_sum_zsmul {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℤ) (u : ι → Fin m → K) :
    ∑ i, c i • latticeForm (u i) = latticeForm (∑ i, c i • u i) := by
  simp only [latticeForm, Finset.smul_sum, Finset.sum_apply, Pi.smul_apply, map_sum, map_zsmul,
    Finset.sum_mul, smul_mul_assoc]
  exact Finset.sum_comm

omit [NumberField K] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evalCone_eq {N : ℕ} (z : Cone (fun _ : Unit ↦ N) ℂ) (f : MvPolynomial (Coord (fun _ : Unit ↦ N)) ℤ) :
    evalCone z f = eval₂Hom (Int.castRingHom ℂ) (fun v ↦ z v.1 v.2) f := rfl

omit [NumberField K] in

/- English proof (translation)
Establish `hmem : (∑ b, (c b - c' b) • X ⟨(), b⟩ : MvPolynomial (Coord (fun _ : Unit ↦ N)) ℤ) ∈ latticeIdeal φ`. Rewrite using `[latticeIdeal, RingHom.mem_ker, map_sum]`. Simplify using `only [map_zsmul, latticeMap, coe_eval₂Hom, eval₂_X]`. Rewrite using `[latticeForm_sum_zsmul]`. Simplify using `only [sub_smul, Finset.sum_sub_distrib, hc, sub_self]`.

Simplify using `[latticeForm]`. Establish `h` using `hz.2 _ hmem`. Rewrite `h` using `[evalCone_eq]`. Simplify using `only [sub_smul, Finset.sum_sub_distrib, map_sub, map_sum, map_zsmul, eval₂Hom_X'] at h`. Conclude with `sub_eq_zero.mp h`.
-/
theorem linear_relation {r N : ℕ} {φ : Fin (N + 1) → Fin (r + 1) → K} {z : Cone (fun _ : Unit ↦ N) ℂ}
    (hz : z ∈ Heights.conePoints (latticeIdeal φ) ℂ) (c c' : Fin (N + 1) → ℤ)
    (hc : ∑ b, c b • φ b = ∑ b, c' b • φ b) : ∑ b, c b • z () b = ∑ b, c' b • z () b := by
  have hmem : (∑ b, (c b - c' b) • X ⟨(), b⟩ : MvPolynomial (Coord (fun _ : Unit ↦ N)) ℤ) ∈
      latticeIdeal φ := by
    rw [latticeIdeal, RingHom.mem_ker, map_sum]
    simp only [map_zsmul, latticeMap, coe_eval₂Hom, eval₂_X]
    rw [latticeForm_sum_zsmul]
    simp only [sub_smul, Finset.sum_sub_distrib, hc, sub_self]
    simp [latticeForm]
  have h := hz.2 _ hmem
  rw [evalCone_eq] at h
  simp only [sub_smul, Finset.sum_sub_distrib, map_sub, map_sum, map_zsmul, eval₂Hom_X'] at h
  exact sub_eq_zero.mp h

/- English proof (translation)
Introduce `K _ _ r N F φ hφ`. Take `⟨e, he⟩ : ∃ e, Module.finrank ℤ (𝓞 K) = e + 1` from `Nat.exists_eq_succ_of_ne_zero (Module.finrank_pos (R := ℤ) (M := 𝓞 K)).ne'`. Set `om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)` to `(Module.finBasis ℤ (𝓞 K)).reindex (finCongr he)`. Take `⟨hP1, ⟨Minv, hM, -⟩, hP3⟩` from `hB K (e + 1) om r`. Use `set ψ := oneBlockForms (r := r) om with hψ`.

Take `⟨D, hD, hDint⟩` from `exists_nat_lattice_integral F.lattice F.fg`. Establish `hC : ∀ p, ∃ c : Fin (N + 1) → ℤ, ∑ b, c b • φ b = (D : ℤ) • ψ p`. Introduce `p`. Establish `hmem : (D : ℤ) • ψ p ∈ Submodule.span ℤ (Set.range φ)`. Rewrite using `[hφ.span_eq, Submodule.restrictScalars_mem]`.

Introduce `v hv`. Take `⟨t, ht⟩` from `(IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).mp (hDint v hv (oneBlockIndex e r p).2)`. Use `⟨om (oneBlockIndex e r p).1 * t, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ht, smul_dotProduct, hψ]`. Simplify using `only [oneBlockForms, single_dotProduct, zsmul_eq_mul, Int.cast_natCast, ← RingOfIntegers.coe_eq_algebraMap]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `(Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem`. Use `choose Cm hCm using hC`. Establish `hQ : ∀ b, ∃ E : ℕ, 0 < E ∧ ∃ q : Fin (oneBlockSize e r + 1) → ℤ, ∑ p, q p • ψ p = (E : ℤ) • φ b`. Introduce `b`.

Take `⟨E, hE, hi⟩` from `exists_nat_mul_isIntegral_fin (φ b)`. Take `⟨q, hq⟩` from `exists_int_comb_oneBlockForms om ((E : ℤ) • φ b) (fun j ↦ by simpa using hi j)`. Conclude with `⟨E, hE, q, hq⟩`. Use `choose E hE Q hQ using hQ`. Establish `hD0 : (D : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hD.ne'`.

Set `zz : Cone (fun _ : Unit ↦ N) ℂ → Cone (oneBlockSizes e r) ℂ` to `fun z _ p ↦ ∑ b, Cm p b • z () b`. Establish `hzzpt : ∀ τ w, zz (latticePoint φ τ w) = latticePoint ψ τ ((D : ℂ) • w)`. Introduce `τ w`. Use function extensionality and compare the values at `u p`. Simplify using `only [zz, latticePoint]`.

Rewrite using `[sum_zsmul_sum_mul, hCm p]`. Use `Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Simplify using `[zsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hrec : ∀ z ∈ Heights.conePoints (latticeIdeal φ) ℂ, ∀ b, ((D : ℤ) * E b) • z () b = ∑ p, Q b p • zz z () p`.

Introduce `z hz b`. Establish `h` using `linear_relation hz (fun b' ↦ ((D : ℤ) * E b) * if b' = b then 1 else 0) (fun b' ↦ ∑ p, Q b p * Cm p b') (by`. Rewrite using `[sum_comb_comb]`. Repeatedly rewrite using `[hCm, smul_comm (Q b _) ((D : ℤ)), ← Finset.smul_sum, hQ b, smul_smul]`. Simplify using `[mul_smul])`.

Rewrite `h` using `[sum_comb_comb]`. Simplify `h` using `[mul_smul, zz]`. Establish `hzzmem : ∀ z ∈ Heights.conePoints (latticeIdeal φ) ℂ, zz z ∈ Heights.conePoints (Heights.oneBlockIdeal om) ℂ`. Introduce `z hz`. Use `⟨fun u hu ↦ hz.1 () ?_, fun g hg ↦ ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `b`. Establish `h` using `hrec z hz b`. Establish `hu' : zz z () = 0` using `hu`. Simplify using `only [hu', Pi.zero_apply, smul_zero, Finset.sum_const_zero] at h`. Establish `hDE : ((D : ℤ) * E b) ≠ 0` using `mul_ne_zero (by exact_mod_cast hD.ne') (by exact_mod_cast (hE b).ne')`.

Conclude with `(smul_eq_zero.mp h).resolve_left hDE`. Set `Θ : MvPolynomial (Coord (oneBlockSizes e r)) ℤ →+* MvPolynomial (Coord (fun _ : Unit ↦ N)) ℤ` to `eval₂Hom (Int.castRingHom _) fun v ↦ ∑ b, Cm v.2 b • X ⟨(), b⟩`. Set `sc : MvPolynomial (Fin (r + 1)) K →+* MvPolynomial (Fin (r + 1)) K` to `eval₂Hom C fun j ↦ C (D : K) * X j`. Establish `hΘ : (latticeMap φ).comp Θ = sc.comp (Heights.oneBlockMap om)`. Use `MvPolynomial.ringHom_ext (fun a ↦ by simp [Θ, sc]) fun v ↦ ?_` and prove the remaining obligations.

Simplify using `only [RingHom.comp_apply, Θ, sc, coe_eval₂Hom, eval₂_X, map_sum, map_zsmul, Heights.oneBlockMap, eval₂_mul, eval₂_C]`. Simplify using `only [latticeMap, coe_eval₂Hom, eval₂_X]`. Rewrite using `[latticeForm_sum_zsmul, hCm, hψ]`. Simplify using `only [oneBlockForms]`. Rewrite using `[← Pi.single_smul', latticeForm_single, zsmul_eq_mul, Int.cast_natCast, C_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hev : evalCone z (Θ g) = evalCone (zz z) g`. Rewrite using `[evalCone_eq, evalCone_eq, ← RingHom.comp_apply]`. Use `congr 1`. Use `MvPolynomial.ringHom_ext (fun a ↦ by simp [Θ]) fun v ↦ ?_` and prove the remaining obligations.

Rewrite using `[RingHom.comp_apply]`. Simplify using `only [Θ, eval₂Hom_X', map_sum, map_zsmul]`. Both sides reduce to the same expression. Rewrite using `[← hev]`. Use `hz.2 _ ?_` and prove the remaining obligations.

Rewrite using `[latticeIdeal, RingHom.mem_ker, ← RingHom.comp_apply, hΘ, RingHom.comp_apply]`. Rewrite `hg` using `[Heights.oneBlockIdeal, RingHom.mem_ker]`. Rewrite using `[hg, map_zero]`. Use `⟨fun z hz ↦ ?_, fun σ w hw ↦ ⟨fun u hu ↦ hw ?_, fun f hf ↦ ?_⟩, fun σ j₀ ↦ ?_⟩` and prove the remaining obligations. Establish `hm` using `hzzmem z hz`.

Rewrite `hm` using `[mem_conePoints_iff]`. Take `⟨σ, ⟨w, hw, hzw⟩, huniq⟩` from `hP1 _ hm`. Rewrite `hzw` using `[← eq_latticePoint_iff]`. Use `⟨σ, ⟨(D : ℂ)⁻¹ • w, smul_ne_zero (inv_ne_zero hD0) hw, ?_⟩, fun τ ⟨w', hw', hzw'⟩ ↦ huniq τ ⟨(D : ℂ) • w', smul_ne_zero hD0 hw', ?_⟩⟩` and prove the remaining obligations. Use function extensionality and compare the values at `u b`.

Establish `h1` using `hrec z hz b`. Rewrite `h1` using `[hzw]`. Simplify using `only [latticePoint] at h1 ⊢`. Rewrite `h1` using `[sum_zsmul_sum_mul, hQ b]`. Establish `hS : ∑ j, σ ((((E b : ℕ) : ℤ) • φ b) j) * w j = (E b : ℂ) * ∑ j, σ (φ b j) * w j`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Simplify using `[zsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[hS, zsmul_eq_mul]`.

Move the coercions through the operations in `at h1`. Establish `hE0 : (E b : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (hE b).ne'`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Repeatedly rewrite using `[mul_left_comm _ (D : ℂ)⁻¹]`. Rewrite using `[← Finset.mul_sum, eq_inv_mul_iff_mul_eq₀ hD0]`.

Apply `mul_left_cancel₀ hE0` to reduce the goal to its premises. Take the linear combination `h1`. Rewrite using `[← eq_latticePoint_iff, hzw', hzzpt]`. Establish `h0 : zz (latticePoint φ σ w) = 0`. Use function extensionality and compare the values at `u' p`.

Establish `hu' : latticePoint φ σ w () = 0` using `hu`. Simplify using `[zz, hu']`. Establish `hform` using `(eq_latticePoint_iff om _ σ _).mp (hzzpt σ w)`. Use function extensionality and compare the values at `j`. Use `hP3 Minv hM _ σ _ hform j` as an intermediate fact.

Rewrite `this` using `[h0]`. Simplify using `only [coneToPairs, Pi.zero_apply, mul_zero, Finset.sum_const_zero, Pi.smul_apply, smul_eq_mul, mul_eq_zero] at this`. Conclude with `this.resolve_left hD0`. Establish `hval : ∀ f' : MvPolynomial (Coord (fun _ : Unit ↦ N)) ℤ, evalCone (latticePoint φ σ w) f' = eval w (map σ (latticeMap φ f'))`. Introduce `f'`.

Establish `hh : (eval₂Hom (Int.castRingHom ℂ) fun v ↦ latticePoint φ σ w v.1 v.2) = ((eval w).comp (MvPolynomial.map σ)).comp (latticeMap φ)` using `MvPolynomial.ringHom_ext (fun a ↦ by simp) fun v ↦ by`. Simplify using `[latticeMap, latticeForm, latticePoint]`. Rewrite using `[evalCone_eq, hh]`. Both sides reduce to the same expression. Rewrite `*` using `[hval, latticeIdeal, RingHom.mem_ker]`.

Rewrite using `[hf, map_zero, map_zero]`. Use `⟨fun b ↦ (D : ℂ)⁻¹ * ∑ a, Minv σ a * (Cm ((oneBlockIndex e r).symm (a, j₀)) b : ℂ), fun τ j ↦ ?_⟩` and prove the remaining obligations. Establish `hstep : ∀ a, ∑ b, (Cm ((oneBlockIndex e r).symm (a, j₀)) b : ℂ) * τ (φ b j) = (D : ℂ) * τ (ψ ((oneBlockIndex e r).symm (a, j₀)) j)`. Introduce `a`. Rewrite using `[sum_intCast_mul_apply, hCm]`.

Simplify using `[zsmul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation. Repeatedly rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Use `_ = ∑ a, Minv σ a * τ (ψ ((oneBlockIndex e r).symm (a, j₀)) j) := by`. Repeatedly rewrite using `[hstep, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ ↦ ?_` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts.

Use `_ = if τ = σ ∧ j = j₀ then 1 else 0 := by`. Establish `hM'` using `congrFun (congrFun hM σ) τ`. Simplify using `only [Matrix.mul_apply, embMat, Matrix.of_apply, Matrix.one_apply] at hM'`. Distinguish the cases in `hj : j = j₀`. Substitute `hj` using the available equality.

Simplify using `only [hψ, oneBlockForms, Equiv.apply_symm_apply, Pi.single_eq_same]`. Rewrite using `[hM']`. Distinguish the cases in `hστ : σ = τ`. Substitute `hστ` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hστ, Ne.symm hστ]`. Simplify using `[hψ, oneBlockForms, hj]`.
-/
theorem of_standard (hB : OneBlockPoints.Statement) : Heights.OneBlockPoints.Statement := by
  intro K _ _ r N F φ hφ
  classical
  obtain ⟨e, he⟩ : ∃ e, Module.finrank ℤ (𝓞 K) = e + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Module.finrank_pos (R := ℤ) (M := 𝓞 K)).ne'
  let om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K) := (Module.finBasis ℤ (𝓞 K)).reindex (finCongr he)
  obtain ⟨hP1, ⟨Minv, hM, -⟩, hP3⟩ := hB K (e + 1) om r
  set ψ := oneBlockForms (r := r) om with hψ

  obtain ⟨D, hD, hDint⟩ := exists_nat_lattice_integral F.lattice F.fg
  have hC : ∀ p, ∃ c : Fin (N + 1) → ℤ, ∑ b, c b • φ b = (D : ℤ) • ψ p := by
    intro p
    have hmem : (D : ℤ) • ψ p ∈ Submodule.span ℤ (Set.range φ) := by
      rw [hφ.span_eq, Submodule.restrictScalars_mem]
      intro v hv
      obtain ⟨t, ht⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).mp
        (hDint v hv (oneBlockIndex e r p).2)
      refine ⟨om (oneBlockIndex e r p).1 * t, ?_⟩
      rw [map_mul, ht, smul_dotProduct, hψ]
      simp only [oneBlockForms, single_dotProduct, zsmul_eq_mul, Int.cast_natCast,
        ← RingOfIntegers.coe_eq_algebraMap]
      ring
    exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem
  choose Cm hCm using hC

  have hQ : ∀ b, ∃ E : ℕ, 0 < E ∧ ∃ q : Fin (oneBlockSize e r + 1) → ℤ,
      ∑ p, q p • ψ p = (E : ℤ) • φ b := by
    intro b
    obtain ⟨E, hE, hi⟩ := exists_nat_mul_isIntegral_fin (φ b)
    obtain ⟨q, hq⟩ := exists_int_comb_oneBlockForms om ((E : ℤ) • φ b) (fun j ↦ by simpa using hi j)
    exact ⟨E, hE, q, hq⟩
  choose E hE Q hQ using hQ
  have hD0 : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'

  let zz : Cone (fun _ : Unit ↦ N) ℂ → Cone (oneBlockSizes e r) ℂ := fun z _ p ↦ ∑ b, Cm p b • z () b
  have hzzpt : ∀ τ w, zz (latticePoint φ τ w) = latticePoint ψ τ ((D : ℂ) • w) := by
    intro τ w
    funext u p
    simp only [zz, latticePoint]
    rw [sum_zsmul_sum_mul, hCm p]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [zsmul_eq_mul]
    ring

  have hrec : ∀ z ∈ Heights.conePoints (latticeIdeal φ) ℂ, ∀ b,
      ((D : ℤ) * E b) • z () b = ∑ p, Q b p • zz z () p := by
    intro z hz b
    have h := linear_relation hz (fun b' ↦ ((D : ℤ) * E b) * if b' = b then 1 else 0)
      (fun b' ↦ ∑ p, Q b p * Cm p b') (by
        rw [sum_comb_comb]
        simp_rw [hCm, smul_comm (Q b _) ((D : ℤ)), ← Finset.smul_sum, hQ b, smul_smul]
        simp [mul_smul])
    rw [sum_comb_comb] at h
    simpa [mul_smul, zz] using h
  have hzzmem : ∀ z ∈ Heights.conePoints (latticeIdeal φ) ℂ,
      zz z ∈ Heights.conePoints (Heights.oneBlockIdeal om) ℂ := by
    intro z hz
    refine ⟨fun u hu ↦ hz.1 () ?_, fun g hg ↦ ?_⟩
    · funext b
      have h := hrec z hz b
      have hu' : zz z () = 0 := hu
      simp only [hu', Pi.zero_apply, smul_zero, Finset.sum_const_zero] at h
      have hDE : ((D : ℤ) * E b) ≠ 0 := mul_ne_zero (by exact_mod_cast hD.ne') (by exact_mod_cast (hE b).ne')
      exact (smul_eq_zero.mp h).resolve_left hDE
    · let Θ : MvPolynomial (Coord (oneBlockSizes e r)) ℤ →+* MvPolynomial (Coord (fun _ : Unit ↦ N)) ℤ :=
        eval₂Hom (Int.castRingHom _) fun v ↦ ∑ b, Cm v.2 b • X ⟨(), b⟩
      let sc : MvPolynomial (Fin (r + 1)) K →+* MvPolynomial (Fin (r + 1)) K :=
        eval₂Hom C fun j ↦ C (D : K) * X j
      have hΘ : (latticeMap φ).comp Θ = sc.comp (Heights.oneBlockMap om) := by
        refine MvPolynomial.ringHom_ext (fun a ↦ by simp [Θ, sc]) fun v ↦ ?_
        simp only [RingHom.comp_apply, Θ, sc, coe_eval₂Hom, eval₂_X, map_sum, map_zsmul,
          Heights.oneBlockMap, eval₂_mul, eval₂_C]
        simp only [latticeMap, coe_eval₂Hom, eval₂_X]
        rw [latticeForm_sum_zsmul, hCm, hψ]
        simp only [oneBlockForms]
        rw [← Pi.single_smul', latticeForm_single, zsmul_eq_mul, Int.cast_natCast, C_mul]
        ring
      have hev : evalCone z (Θ g) = evalCone (zz z) g := by
        rw [evalCone_eq, evalCone_eq, ← RingHom.comp_apply]
        congr 1
        refine MvPolynomial.ringHom_ext (fun a ↦ by simp [Θ]) fun v ↦ ?_
        rw [RingHom.comp_apply]
        simp only [Θ, eval₂Hom_X', map_sum, map_zsmul]
        rfl
      rw [← hev]
      refine hz.2 _ ?_
      rw [latticeIdeal, RingHom.mem_ker, ← RingHom.comp_apply, hΘ, RingHom.comp_apply]
      rw [Heights.oneBlockIdeal, RingHom.mem_ker] at hg
      rw [hg, map_zero]
  refine ⟨fun z hz ↦ ?_, fun σ w hw ↦ ⟨fun u hu ↦ hw ?_, fun f hf ↦ ?_⟩, fun σ j₀ ↦ ?_⟩
  ·
    have hm := hzzmem z hz
    rw [mem_conePoints_iff] at hm
    obtain ⟨σ, ⟨w, hw, hzw⟩, huniq⟩ := hP1 _ hm
    rw [← eq_latticePoint_iff] at hzw
    refine ⟨σ, ⟨(D : ℂ)⁻¹ • w, smul_ne_zero (inv_ne_zero hD0) hw, ?_⟩,
      fun τ ⟨w', hw', hzw'⟩ ↦ huniq τ ⟨(D : ℂ) • w', smul_ne_zero hD0 hw', ?_⟩⟩
    · funext u b
      have h1 := hrec z hz b
      rw [hzw] at h1
      simp only [latticePoint] at h1 ⊢
      rw [sum_zsmul_sum_mul, hQ b] at h1
      have hS : ∑ j, σ ((((E b : ℕ) : ℤ) • φ b) j) * w j = (E b : ℂ) * ∑ j, σ (φ b j) * w j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simp [zsmul_eq_mul]
        ring
      rw [hS, zsmul_eq_mul] at h1
      push_cast at h1
      have hE0 : (E b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hE b).ne'
      simp only [Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_left_comm _ (D : ℂ)⁻¹]
      rw [← Finset.mul_sum, eq_inv_mul_iff_mul_eq₀ hD0]
      apply mul_left_cancel₀ hE0
      linear_combination h1
    · rw [← eq_latticePoint_iff, hzw', hzzpt]
  ·
    have h0 : zz (latticePoint φ σ w) = 0 := by
      funext u' p
      have hu' : latticePoint φ σ w () = 0 := hu
      simp [zz, hu']
    have hform := (eq_latticePoint_iff om _ σ _).mp (hzzpt σ w)
    funext j
    have := hP3 Minv hM _ σ _ hform j
    rw [h0] at this
    simp only [coneToPairs, Pi.zero_apply, mul_zero, Finset.sum_const_zero, Pi.smul_apply,
      smul_eq_mul, mul_eq_zero] at this
    exact this.resolve_left hD0
  ·
    have hval : ∀ f' : MvPolynomial (Coord (fun _ : Unit ↦ N)) ℤ,
        evalCone (latticePoint φ σ w) f' = eval w (map σ (latticeMap φ f')) := by
      intro f'
      have hh : (eval₂Hom (Int.castRingHom ℂ) fun v ↦ latticePoint φ σ w v.1 v.2) =
          ((eval w).comp (MvPolynomial.map σ)).comp (latticeMap φ) :=
        MvPolynomial.ringHom_ext (fun a ↦ by simp) fun v ↦ by
          simp [latticeMap, latticeForm, latticePoint]
      rw [evalCone_eq, hh]
      rfl
    rw [hval, latticeIdeal, RingHom.mem_ker] at *
    rw [hf, map_zero, map_zero]
  ·
    refine ⟨fun b ↦ (D : ℂ)⁻¹ * ∑ a, Minv σ a * (Cm ((oneBlockIndex e r).symm (a, j₀)) b : ℂ),
      fun τ j ↦ ?_⟩
    have hstep : ∀ a, ∑ b, (Cm ((oneBlockIndex e r).symm (a, j₀)) b : ℂ) * τ (φ b j) =
        (D : ℂ) * τ (ψ ((oneBlockIndex e r).symm (a, j₀)) j) := by
      intro a
      rw [sum_intCast_mul_apply, hCm]
      simp [zsmul_eq_mul]
    calc ∑ b, ((D : ℂ)⁻¹ * ∑ a, Minv σ a * (Cm ((oneBlockIndex e r).symm (a, j₀)) b : ℂ)) * τ (φ b j)
        = (D : ℂ)⁻¹ * ∑ a, Minv σ a *
            ∑ b, (Cm ((oneBlockIndex e r).symm (a, j₀)) b : ℂ) * τ (φ b j) := by
          simp_rw [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
          ring
      _ = ∑ a, Minv σ a * τ (ψ ((oneBlockIndex e r).symm (a, j₀)) j) := by
          simp_rw [hstep, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          field_simp
      _ = if τ = σ ∧ j = j₀ then 1 else 0 := by
          have hM' := congrFun (congrFun hM σ) τ
          simp only [Matrix.mul_apply, embMat, Matrix.of_apply, Matrix.one_apply] at hM'
          by_cases hj : j = j₀
          · subst hj
            simp only [hψ, oneBlockForms, Equiv.apply_symm_apply, Pi.single_eq_same]
            rw [hM']
            by_cases hστ : σ = τ
            · subst hστ; simp
            · simp [hστ, Ne.symm hστ]
          · simp [hψ, oneBlockForms, hj]

end OfStandard

end OneBlockPoints

/- English proof (translation)
Assemble the required witnesses or components as `⟨OneBlockPoints.of_lattice, OneBlockPoints.of_standard⟩`.
-/
theorem OneBlockPoints.equiv :
    GroundTheory.Heights₂.Heights.OneBlockPoints.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.OneBlockPoints.Statement :=
  ⟨OneBlockPoints.of_lattice, OneBlockPoints.of_standard⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
