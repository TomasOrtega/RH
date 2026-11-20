import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatUniformSummableMajorant
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SummableProdCoord
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.EisRkNBound

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors Pointwise
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix GlobalTheory.CompanionTheory.EisRk1Bound

set_option synthInstance.maxSize 1000

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qo1.summable_prod_coord h0 hg`.
-/
theorem summable_prod_coord {α : Type*} {g : α → ℝ} (h0 : ∀ x, 0 ≤ g x) (hg : Summable g) :
    Summable fun ξ : ι → α ↦ ∏ i, g (ξ i) :=
  _root_.UpperTheory.Reformulated.B.Qo1.summable_prod_coord h0 hg

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`.
-/
theorem inv_mulVec_mulVec (x : ι → 𝔸[K]) (h : GL ι 𝔸[K]) :
    ((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) *ᵥ ((h : Matrix ι ι 𝔸[K]) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

/- English proof (translation)
Establish `h : Continuous fun h : GL ι 𝔸[K] ↦ ((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K])` using `Units.continuous_val.comp continuous_inv`. Conclude with `h.matrix_elem i j`.
-/
theorem continuous_inv_entry (i j : ι) :
    Continuous fun h : GL ι 𝔸[K] ↦ ((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) i j := by
  have h : Continuous fun h : GL ι 𝔸[K] ↦ ((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) :=
    Units.continuous_val.comp continuous_inv
  exact h.matrix_elem i j

omit [DecidableEq ι] in

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show Adele2.finRingHom (∑ j, M i j * x j) = _`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun j _ ↦ map_mul _ _ _`.
-/
theorem finPartPi_mulVec (M : Matrix ι ι 𝔸[K]) (x : ι → 𝔸[K]) :
    finPartPi (M *ᵥ x) = M.map Adele2.finRingHom *ᵥ finPartPi x := by
  funext i
  show Adele2.finRingHom (∑ j, M i j * x j) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ map_mul _ _ _

omit [DecidableEq ι] in

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show Adele2.infRingHom (∑ j, M i j * x j) = _`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun j _ ↦ map_mul _ _ _`.
-/
theorem infPartPi_mulVec (M : Matrix ι ι 𝔸[K]) (x : ι → 𝔸[K]) :
    infPartPi (M *ᵥ x) = M.map Adele2.infRingHom *ᵥ infPartPi x := by
  funext i
  show Adele2.infRingHom (∑ j, M i j * x j) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ map_mul _ _ _

omit [DecidableEq ι] in

/- English proof (translation)
Establish `hc : 0 ≤ ∑ i, ∑ j, ‖M i j‖` using `Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _`. Use `(pi_norm_le_iff_of_nonneg (mul_nonneg hc (norm_nonneg _))).mpr fun i ↦ ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun i ↦ ∑ j, ‖M i j‖) (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)`.
-/
theorem norm_mulVec_le (M : Matrix ι ι (mixedSpace K)) (u : ι → mixedSpace K) :
    ‖M *ᵥ u‖ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖u‖ := by
  have hc : 0 ≤ ∑ i, ∑ j, ‖M i j‖ :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hc (norm_nonneg _))).mpr fun i ↦ ?_
  calc ‖(M *ᵥ u) i‖ = ‖∑ j, M i j * u j‖ := rfl
    _ ≤ ∑ j, ‖M i j * u j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖M i j‖ * ‖u‖ := Finset.sum_le_sum fun j _ ↦
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm u j) (norm_nonneg _))
    _ = (∑ j, ‖M i j‖) * ‖u‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖u‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun i ↦ ∑ j, ‖M i j‖)
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)

/- English proof (translation)
Use `set B : Set (ι → 𝔸ᶠ[K]) := Set.pi Set.univ fun i ↦ b i +ᵥ (idealFiniteAdeles I : Set 𝔸ᶠ[K])`. Establish `hB : IsCompact B` using `isCompact_univ_pi fun i ↦ (isCompact_idealFiniteAdeles I).vadd (b i)`. Set `T : GL ι 𝔸[K] × (ι → 𝔸ᶠ[K]) → ι → 𝔸ᶠ[K]` to `fun p ↦ (((p.1⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]).map Adele2.finRingHom) *ᵥ p.2`. Establish `hT : Continuous T`. Use `continuous_pi fun i ↦ ?_` and prove the remaining obligations.

Simplify using `only [T, Matrix.mulVec, dotProduct, Matrix.map_apply]`. Use `continuous_finset_sum _ fun j _ ↦ ?_` and prove the remaining obligations. Apply the tactic sequence `exact (continuous_finRingHom.comp ((continuous_inv_entry i j).comp continuous_fst)).mul ((continuous_apply j).comp continuous_snd)`. Use `set S : Set 𝔸ᶠ[K] := ⋃ i : ι, (fun x : ι → 𝔸ᶠ[K] ↦ x i) '' (T '' (C ×ˢ B))`. Establish `hS : IsCompact S` using `isCompact_iUnion fun i ↦ ((hC.prod hB).image hT).image (continuous_apply i)`.

Take `⟨d, hd0, hd⟩` from `exists_mul_mem_integralFiniteAdeles_of_isCompact hS`. Use `set dK := algebraMap (𝓞 K) K d`. Establish `hdK : dK ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0`. Use `⟨Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ dK⁻¹) ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hdK)), ?_⟩` and prove the remaining obligations. Introduce `h hh ξ hξ i`.

Use `set X : ι → 𝔸[K] := fun i ↦ algebraMap K 𝔸[K] (ξ i)`. Establish `hTX : T (h, finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ X)) = fun i ↦ algebraMap K 𝔸ᶠ[K] (ξ i)` using `by show _ *ᵥ finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ X) = _`. Rewrite using `[← finPartPi_mulVec, inv_mulVec_mulVec, finPartPi_algebraMap]`. Establish `hmem : algebraMap K 𝔸ᶠ[K] (ξ i) ∈ S`. Establish `hp : finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ X) ∈ B` using `fun j _ ↦ mem_vadd_idealFiniteAdeles.mpr (hξ j)`.

Establish `hq : (fun i ↦ algebraMap K 𝔸ᶠ[K] (ξ i)) ∈ T '' (C ×ˢ B)` using `⟨(h, finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ X)), ⟨hh, hp⟩, hTX⟩`. Conclude with `Set.mem_iUnion.mpr ⟨i, _, hq, rfl⟩`. Establish `h1` using `hd _ hmem`. Rewrite `h1` using `[← map_mul]`. Establish `h2 : dK * ξ i ∈ ((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)`.

Rewrite using `[← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]`. Conclude with `h1`. Rewrite `h2` using `[Units.val_one]`. Take `⟨r, hr⟩` from `(FractionalIdeal.mem_one_iff _).mp h2`. Use `(FractionalIdeal.mem_spanSingleton _).mpr ⟨r, ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.smul_def, hr, mul_comm dK, mul_assoc, mul_inv_cancel₀ hdK, mul_one]`.
-/
theorem exists_fractionalIdeal_of_isCompact (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : ι → 𝔸ᶠ[K])
    {C : Set (GL ι 𝔸[K])} (hC : IsCompact C) :
    ∃ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∀ h ∈ C, ∀ ξ : ι → K,
      (∀ i, finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ fun i ↦ algebraMap K 𝔸[K] (ξ i)) i - b i ∈
        idealFiniteAdeles I) → ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 K)⁰ K) := by
  set B : Set (ι → 𝔸ᶠ[K]) :=
    Set.pi Set.univ fun i ↦ b i +ᵥ (idealFiniteAdeles I : Set 𝔸ᶠ[K])
  have hB : IsCompact B := isCompact_univ_pi fun i ↦ (isCompact_idealFiniteAdeles I).vadd (b i)
  let T : GL ι 𝔸[K] × (ι → 𝔸ᶠ[K]) → ι → 𝔸ᶠ[K] := fun p ↦
    (((p.1⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]).map Adele2.finRingHom) *ᵥ p.2
  have hT : Continuous T := by
    refine continuous_pi fun i ↦ ?_
    simp only [T, Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine continuous_finset_sum _ fun j _ ↦ ?_
    exact (continuous_finRingHom.comp ((continuous_inv_entry i j).comp continuous_fst)).mul
      ((continuous_apply j).comp continuous_snd)
  set S : Set 𝔸ᶠ[K] := ⋃ i : ι, (fun x : ι → 𝔸ᶠ[K] ↦ x i) '' (T '' (C ×ˢ B))
  have hS : IsCompact S := isCompact_iUnion fun i ↦
    ((hC.prod hB).image hT).image (continuous_apply i)
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hS
  set dK := algebraMap (𝓞 K) K d
  have hdK : dK ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  refine ⟨Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ dK⁻¹)
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hdK)), ?_⟩
  intro h hh ξ hξ i
  set X : ι → 𝔸[K] := fun i ↦ algebraMap K 𝔸[K] (ξ i)
  have hTX : T (h, finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ X)) =
      fun i ↦ algebraMap K 𝔸ᶠ[K] (ξ i) := by
    show _ *ᵥ finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ X) = _
    rw [← finPartPi_mulVec, inv_mulVec_mulVec, finPartPi_algebraMap]
  have hmem : algebraMap K 𝔸ᶠ[K] (ξ i) ∈ S := by
    have hp : finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ X) ∈ B := fun j _ ↦
      mem_vadd_idealFiniteAdeles.mpr (hξ j)
    have hq : (fun i ↦ algebraMap K 𝔸ᶠ[K] (ξ i)) ∈ T '' (C ×ˢ B) :=
      ⟨(h, finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ X)), ⟨hh, hp⟩, hTX⟩
    exact Set.mem_iUnion.mpr ⟨i, _, hq, rfl⟩
  have h1 := hd _ hmem
  rw [← map_mul] at h1
  have h2 : dK * ξ i ∈ ((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]
    exact h1
  rw [Units.val_one] at h2
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h2
  refine (FractionalIdeal.mem_spanSingleton _).mpr ⟨r, ?_⟩
  rw [Algebra.smul_def, hr, mul_comm dK, mul_assoc, mul_inv_cancel₀ hdK, mul_one]

/- English proof (translation)
The claim follows from `summable_prod_coord (latticeWeight_nonneg J _) (summable_ite_mem_of_summable_idealLattice J (h := fun x ↦ ((1 + ‖x‖) ^ (Module.finrank ℤ (idealLattice K J) + 1))⁻¹) (summable_inv_one_add_norm_pow_idealLattice J))`.
-/
theorem summable_latticeWeight_prod (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Summable fun ξ : ι → K ↦
      ∏ i, latticeWeight J (Module.finrank ℤ (idealLattice K J) + 1) (ξ i) :=
  summable_prod_coord (latticeWeight_nonneg J _)
    (summable_ite_mem_of_summable_idealLattice J
      (h := fun x ↦ ((1 + ‖x‖) ^ (Module.finrank ℤ (idealLattice K J) + 1))⁻¹)
      (summable_inv_one_add_norm_pow_idealLattice J))

/- English proof (translation)
Take `⟨J, hJ⟩` from `exists_fractionalIdeal_of_isCompact I b hC`. Use `set k := Module.finrank ℤ (idealLattice K J) + 1`. Use `set n := Fintype.card ι`. Take `⟨A, hA, hφ⟩` from `exists_norm_le_inv_one_add_pow φ (k * n)`. Set `c : GL ι 𝔸[K] → ℝ` to `fun h ↦ ∑ i, ∑ j, ‖(((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]).map Adele2.infRingHom) i j‖`.

Apply the tactic sequence `have hc : Continuous c := continuous_finset_sum _ fun i _ ↦ continuous_finset_sum _ fun j _ ↦ (continuous_infRingHom.comp (continuous_inv_entry i j)).norm`. Take `⟨B, hB⟩` from `hC.exists_bound_of_continuousOn hc.continuousOn`. Use `set B' := max B 1`. Establish `hB'1 : 1 ≤ B'` using `le_max_right _ _`. Establish `hB'0 : 0 < B'` using `zero_lt_one.trans_le hB'1`.

Use `⟨fun ξ ↦ A * B' ^ (k * n) * ∏ i, latticeWeight J k (ξ i), (summable_latticeWeight_prod J).mul_left _, ?_⟩` and prove the remaining obligations. Introduce `h hh ξ`. Establish `hu0 : 0 ≤ A * B' ^ (k * n) * ∏ i, latticeWeight J k (ξ i)` using `mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ ↦ latticeWeight_nonneg J k _)`. Use `set X : ι → 𝔸[K] := fun i ↦ algebraMap K 𝔸[K] (ξ i)`. Use `set Y := (h : Matrix ι ι 𝔸[K]) *ᵥ X`.

Simplify using `only [schwartzBruhatTensorPi, finiteTensor]`. Distinguish the cases in `hm : ∀ i, finPartPi Y i - b i ∈ idealFiniteAdeles I`. Establish `h1 : ∏ i, cosetIndicator I (b i) (finPartPi Y i) = 1` using `Finset.prod_eq_one fun i _ ↦ by rw [cosetIndicator_apply, if_pos (hm i)]`. Rewrite using `[h1, mul_one]`. Establish `hξJ` using `hJ h hh ξ hm`.

Establish `hw : ∀ i, latticeWeight J k (ξ i) = ((1 + ‖mixedEmbedding K (ξ i)‖) ^ k)⁻¹` using `fun i ↦ if_pos (hξJ i)`. Simplify using `only [hw]`. Use `set y := infPartPi Y`. Establish `hy : embPi K ξ = (((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]).map Adele2.infRingHom) *ᵥ y`. Rewrite using `[← infPartPi_mulVec, inv_mulVec_mulVec, infPartPi_algebraMap]`.

Establish `hcB : c h ≤ B'` using `(le_abs_self _).trans (((Real.norm_eq_abs _).symm.trans_le (hB h hh)).trans (le_max_left _ _))`. Establish `he : ‖embPi K ξ‖ ≤ B' * ‖y‖`. Rewrite using `[hy]`. Conclude with `(norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right hcB (norm_nonneg _))`. Use `set t := B' * (1 + ‖y‖)`.

Establish `ht : 0 < t` using `by positivity`. Establish `hle : ∀ i, 1 + ‖mixedEmbedding K (ξ i)‖ ≤ t` using `fun i ↦ by`. Establish `h1 : ‖mixedEmbedding K (ξ i)‖ ≤ ‖embPi K ξ‖` using `norm_le_pi_norm (embPi K ξ) i`. Establish `: t = B' + B' * ‖y‖` using `by simp only [t]; ring`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hinv : ∀ i, (t ^ k)⁻¹ ≤ ((1 + ‖mixedEmbedding K (ξ i)‖) ^ k)⁻¹` using `fun i ↦ by`. Establish `h0 : 0 < 1 + ‖mixedEmbedding K (ξ i)‖` using `by positivity`. Use `gcongr`. Conclude with `hle i`. Combine the equalities or inequalities in the displayed calculation.

Establish `hB0 : B' ^ (k * n) ≠ 0` using `by positivity`. Establish `hprod : ∏ _i : ι, (t ^ k)⁻¹ = (t ^ (k * n))⁻¹`. Rewrite using `[Finset.prod_const, Finset.card_univ, inv_pow, ← pow_mul]`. Establish `ht' : t ^ (k * n) = B' ^ (k * n) * (1 + ‖y‖) ^ (k * n)` using `mul_pow _ _ _`. Rewrite using `[hprod, ht', mul_inv, ← mul_assoc, mul_assoc A, mul_inv_cancel₀ hB0, mul_one]`.

Use `_ ≤ A * B' ^ (k * n) * ∏ i, ((1 + ‖mixedEmbedding K (ξ i)‖) ^ k)⁻¹ := by`. Use `mul_le_mul_of_nonneg_left ?_ (by positivity)` and prove the remaining obligations. Conclude with `Finset.prod_le_prod (fun _ _ ↦ by positivity) fun i _ ↦ hinv i`. Use `push_neg at hm`. Take `⟨i, hi⟩` from `hm`.

Establish `hz : ∏ i, cosetIndicator I (b i) (finPartPi Y i) = 0` using `Finset.prod_eq_zero (Finset.mem_univ i) (by rw [cosetIndicator_apply, if_neg hi])`. Rewrite using `[hz, mul_zero, norm_zero]`. Conclude with `hu0`.
-/
theorem exists_summable_bound_tensor_cosetIndicator (φ : 𝓢(ι → mixedSpace K, ℂ))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : ι → 𝔸ᶠ[K]) {C : Set (GL ι 𝔸[K])}
    (hC : IsCompact C) :
    ∃ u : (ι → K) → ℝ, Summable u ∧ ∀ h ∈ C, ∀ ξ : ι → K,
      ‖schwartzBruhatTensorPi φ (finiteTensor fun i ↦ cosetIndicator I (b i))
        ((h : Matrix ι ι 𝔸[K]) *ᵥ fun i ↦ algebraMap K 𝔸[K] (ξ i))‖ ≤ u ξ := by
  obtain ⟨J, hJ⟩ := exists_fractionalIdeal_of_isCompact I b hC
  set k := Module.finrank ℤ (idealLattice K J) + 1
  set n := Fintype.card ι
  obtain ⟨A, hA, hφ⟩ := exists_norm_le_inv_one_add_pow φ (k * n)
  let c : GL ι 𝔸[K] → ℝ := fun h ↦ ∑ i, ∑ j,
    ‖(((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]).map Adele2.infRingHom) i j‖
  have hc : Continuous c := continuous_finset_sum _ fun i _ ↦ continuous_finset_sum _ fun j _ ↦
    (continuous_infRingHom.comp (continuous_inv_entry i j)).norm
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  set B' := max B 1
  have hB'1 : 1 ≤ B' := le_max_right _ _
  have hB'0 : 0 < B' := zero_lt_one.trans_le hB'1
  refine ⟨fun ξ ↦ A * B' ^ (k * n) * ∏ i, latticeWeight J k (ξ i),
    (summable_latticeWeight_prod J).mul_left _, ?_⟩
  intro h hh ξ
  have hu0 : 0 ≤ A * B' ^ (k * n) * ∏ i, latticeWeight J k (ξ i) :=
    mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ ↦ latticeWeight_nonneg J k _)
  set X : ι → 𝔸[K] := fun i ↦ algebraMap K 𝔸[K] (ξ i)
  set Y := (h : Matrix ι ι 𝔸[K]) *ᵥ X
  simp only [schwartzBruhatTensorPi, finiteTensor]
  by_cases hm : ∀ i, finPartPi Y i - b i ∈ idealFiniteAdeles I
  · have h1 : ∏ i, cosetIndicator I (b i) (finPartPi Y i) = 1 :=
      Finset.prod_eq_one fun i _ ↦ by rw [cosetIndicator_apply, if_pos (hm i)]
    rw [h1, mul_one]
    have hξJ := hJ h hh ξ hm
    have hw : ∀ i, latticeWeight J k (ξ i) = ((1 + ‖mixedEmbedding K (ξ i)‖) ^ k)⁻¹ :=
      fun i ↦ if_pos (hξJ i)
    simp only [hw]
    set y := infPartPi Y
    have hy : embPi K ξ =
        (((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]).map Adele2.infRingHom) *ᵥ y := by
      rw [← infPartPi_mulVec, inv_mulVec_mulVec, infPartPi_algebraMap]
    have hcB : c h ≤ B' := (le_abs_self _).trans (((Real.norm_eq_abs _).symm.trans_le (hB h hh)).trans
      (le_max_left _ _))
    have he : ‖embPi K ξ‖ ≤ B' * ‖y‖ := by
      rw [hy]
      exact (norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right hcB (norm_nonneg _))
    set t := B' * (1 + ‖y‖)
    have ht : 0 < t := by positivity
    have hle : ∀ i, 1 + ‖mixedEmbedding K (ξ i)‖ ≤ t := fun i ↦ by
      have h1 : ‖mixedEmbedding K (ξ i)‖ ≤ ‖embPi K ξ‖ := norm_le_pi_norm (embPi K ξ) i
      have : t = B' + B' * ‖y‖ := by simp only [t]; ring
      linarith
    have hinv : ∀ i, (t ^ k)⁻¹ ≤ ((1 + ‖mixedEmbedding K (ξ i)‖) ^ k)⁻¹ := fun i ↦ by
      have h0 : 0 < 1 + ‖mixedEmbedding K (ξ i)‖ := by positivity
      gcongr
      exact hle i
    calc ‖φ y‖ ≤ A * ((1 + ‖y‖) ^ (k * n))⁻¹ := hφ y
      _ = A * B' ^ (k * n) * ∏ _i : ι, (t ^ k)⁻¹ := by
          have hB0 : B' ^ (k * n) ≠ 0 := by positivity
          have hprod : ∏ _i : ι, (t ^ k)⁻¹ = (t ^ (k * n))⁻¹ := by
            rw [Finset.prod_const, Finset.card_univ, inv_pow, ← pow_mul]
          have ht' : t ^ (k * n) = B' ^ (k * n) * (1 + ‖y‖) ^ (k * n) := mul_pow _ _ _
          rw [hprod, ht', mul_inv, ← mul_assoc, mul_assoc A, mul_inv_cancel₀ hB0, mul_one]
      _ ≤ A * B' ^ (k * n) * ∏ i, ((1 + ‖mixedEmbedding K (ξ i)‖) ^ k)⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Finset.prod_le_prod (fun _ _ ↦ by positivity) fun i _ ↦ hinv i
  · push_neg at hm
    obtain ⟨i, hi⟩ := hm
    have hz : ∏ i, cosetIndicator I (b i) (finPartPi Y i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [cosetIndicator_apply, if_neg hi])
    rw [hz, mul_zero, norm_zero]
    exact hu0

/- English proof (translation)
Rewrite `hF` using `[schwartzBruhatPi_eq_cosetSpanPi]`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem G hG`. Take `⟨φ, I, b, rfl⟩` from `hG`. Conclude with `exists_summable_bound_tensor_cosetIndicator φ I b hC`.

Consider the case `zero => exact ⟨0, summable_zero, fun _ _ _ ↦ by simp⟩`. Consider the case `add G H _ _ hG hH`. Take `⟨u, hu, hGu⟩` from `hG`. Take `⟨w, hw, hHw⟩` from `hH`. Conclude with `⟨u + w, hu.add hw, fun a ha ξ ↦ (norm_add_le _ _).trans (add_le_add (hGu a ha ξ) (hHw a ha ξ))⟩`.

Consider the case `smul r G _ hG`. Take `⟨u, hu, hGu⟩` from `hG`. Use `⟨fun ξ ↦ ‖r‖ * u ξ, hu.mul_left _, fun a ha ξ ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul, norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hGu a ha ξ) (norm_nonneg r)`.
-/
theorem exists_summable_bound_mulVec {F : (ι → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhatPi K ι)
    {C : Set (GL ι 𝔸[K])} (hC : IsCompact C) :
    ∃ u : (ι → K) → ℝ, Summable u ∧ ∀ h ∈ C, ∀ ξ : ι → K,
      ‖F ((h : Matrix ι ι 𝔸[K]) *ᵥ fun i ↦ algebraMap K 𝔸[K] (ξ i))‖ ≤ u ξ := by
  rw [schwartzBruhatPi_eq_cosetSpanPi] at hF
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, I, b, rfl⟩ := hG
    exact exists_summable_bound_tensor_cosetIndicator φ I b hC
  | zero => exact ⟨0, summable_zero, fun _ _ _ ↦ by simp⟩
  | add G H _ _ hG hH =>
    obtain ⟨u, hu, hGu⟩ := hG
    obtain ⟨w, hw, hHw⟩ := hH
    exact ⟨u + w, hu.add hw,
      fun a ha ξ ↦ (norm_add_le _ _).trans (add_le_add (hGu a ha ξ) (hHw a ha ξ))⟩
  | smul r G _ hG =>
    obtain ⟨u, hu, hGu⟩ := hG
    refine ⟨fun ξ ↦ ‖r‖ * u ξ, hu.mul_left _, fun a ha ξ ↦ ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hGu a ha ξ) (norm_nonneg r)

/- English proof (translation)
The claim follows from `exists_summable_bound_mulVec hF hC`.
-/
theorem exists_summable_bound_thetaC {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι]
    [DecidableEq ι] {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι)
    {C : Set (GL ι 𝔸[k])} (hC : IsCompact C) :
    ∃ u : (ι → k) → ℝ, Summable u ∧ ∀ h ∈ C, ∀ ξ : ι → k,
      ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ PositivityTheory.RgEis.ratV ξ)‖ ≤ u ξ :=
  exists_summable_bound_mulVec hF hC

end

end GlobalTheory.CompanionTheory.EisRkNBound
