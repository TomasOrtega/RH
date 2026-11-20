import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPart
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.DegStB

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt GlobalTheory.LieRead Module

namespace GlobalTheory.LocIndex

/- English proof (translation)
Distinguish the cases in `h0 : H.relIndex E = 0`. Rewrite using `[h0, padicValNat.zero]`. Apply `padicValNat.eq_zero_of_not_dvd` to reduce the goal to its premises. Introduce `hdvd`. Establish `hfi : (H.addSubgroupOf E).FiniteIndex` using `⟨h0⟩`.

Establish `: Finite (E ⧸ H.addSubgroupOf E)` using `AddSubgroup.finite_quotient_of_finiteIndex`. Establish `hdvd' : p ∣ Nat.card (E ⧸ H.addSubgroupOf E)` using `hdvd`. Take `⟨q, hq⟩` from `exists_prime_addOrderOf_dvd_card' p hdvd'`. Proceed by induction on `q using QuotientAddGroup.induction_on with`. Consider the case `H v`.

Establish `hz : s • (QuotientAddGroup.mk v : E ⧸ H.addSubgroupOf E) = 0`. Rewrite using `[← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]`. Conclude with `hE v v.2`. Use `addOrderOf_dvd_of_nsmul_eq_zero hz` as an intermediate fact. Rewrite `this` using `[hq]`.

Conclude with `hs this`.
-/
theorem padicValNat_relIndex_eq_zero {G : Type*} [AddCommGroup G] (p : ℕ) [Fact p.Prime]
    {H E : AddSubgroup G} {s : ℕ} (hs : ¬ p ∣ s) (hE : ∀ v ∈ E, s • v ∈ H) :
    padicValNat p (H.relIndex E) = 0 := by
  by_cases h0 : H.relIndex E = 0
  · rw [h0, padicValNat.zero]
  apply padicValNat.eq_zero_of_not_dvd
  intro hdvd
  have hfi : (H.addSubgroupOf E).FiniteIndex := ⟨h0⟩
  have : Finite (E ⧸ H.addSubgroupOf E) := AddSubgroup.finite_quotient_of_finiteIndex
  have hdvd' : p ∣ Nat.card (E ⧸ H.addSubgroupOf E) := hdvd
  obtain ⟨q, hq⟩ := exists_prime_addOrderOf_dvd_card' p hdvd'
  induction q using QuotientAddGroup.induction_on with
  | H v =>
    have hz : s • (QuotientAddGroup.mk v : E ⧸ H.addSubgroupOf E) = 0 := by
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      exact hE v v.2
    have := addOrderOf_dvd_of_nsmul_eq_zero hz
    rw [hq] at this
    exact hs this

/- English proof (translation)
Use extensionality with `i k`. Rewrite using `[Matrix.of_apply, hw k, Matrix.mul_apply, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, Matrix.of_apply, Matrix.map_apply, ← algebraMap_smul K (A l k) (v l i), smul_eq_mul, mul_comm]`.
-/
theorem of_comb_eq_mul {K : Type} [Field K] [NumberField K] {n : ℕ} (v w : Fin n → Fin n → K)
    (A : Matrix (Fin n) (Fin n) (𝓞 K)) (hw : ∀ k, w k = ∑ l, A l k • v l) :
    (Matrix.of fun i k => w k i) = (Matrix.of fun i k => v k i) * A.map (algebraMap (𝓞 K) K) := by
  ext i k
  rw [Matrix.of_apply, hw k, Matrix.mul_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.smul_apply, Matrix.of_apply, Matrix.map_apply, ← algebraMap_smul K (A l k) (v l i), smul_eq_mul, mul_comm]

/- English proof (translation)
Establish `hp` using `(Fact.out : p.Prime)`. Establish `hs0 : (s : K) ≠ 0` using `Nat.cast_ne_zero.mpr (by rintro rfl; exact hs (dvd_zero p))`. Establish `hs0' : (s' : K) ≠ 0` using `Nat.cast_ne_zero.mpr (by rintro rfl; exact hs' (dvd_zero p))`. Establish `spanK : ∀ (t : ℕ) (z : Fin g → Fin g → K), (t : K) ≠ 0 → ∀ v, (t : K) • v ∈ Submodule.span (𝓞 K) (Set.range z) → v ∈ Submodule.span K (Set.range z)`. Introduce `t z ht v hv`.

Establish `h2 : (t : K) • v ∈ Submodule.span K (Set.range z)` using `Submodule.span_le_restrictScalars (𝓞 K) K _ hv`. Use `Submodule.smul_mem _ ((t : K)⁻¹) h2` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ ht, one_smul]`. Then use the resulting hypothesis. Establish `hframe : IsFrame K L x` using `⟨hx, hxi, fun v hv => spanK s x hs0 v (hsL v hv)⟩`. Establish `hframe' : IsFrame K L' x'` using `⟨hx', hxi', fun v hv => spanK s' x' hs0' v (hsL' v hv)⟩`.

Establish `hxK : ∀ j, x j ∈ Submodule.span K (Set.range x')` using `fun j => spanK s' x' hs0' _ (hsL' _ (hLL (hx j)))`. Use `choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun K).mp (hxK j)`. Take `⟨y, hy0, hy⟩` from `exists_integral_multiples ℤ ℚ (L := K) (Finset.univ.image fun q : Fin g × Fin g => c q.1 q.2)`. Establish `hd : ∀ j i, IsIntegral ℤ (y • c j i)` using `fun j i => hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ (j, i)))`. Set `G : Matrix (Fin g) (Fin g) (𝓞 K)` to `fun i j => ⟨y • c j i, hd j i⟩`.

Set `D : Matrix (Fin g) (Fin g) (𝓞 K)` to `Matrix.diagonal fun _ => (y : 𝓞 K)`. Establish `hw1 : ∀ j, y • x j = ∑ i, G i j • x' i`. Introduce `j`. Rewrite using `[← hc j, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← algebraMap_smul K (G i j) (x' i), ← smul_assoc]`. Both sides reduce to the same expression. Establish `hw2 : ∀ j, y • x j = ∑ i, D i j • x i`. Introduce `j`. Simplify using `[D, Matrix.diagonal_apply, Int.cast_smul_eq_zsmul]`.

Establish `hwli : LinearIndependent K (fun j => y • x j)`. Use `hxi.units_smul (fun _ => Units.mk0 (y : K) (Int.cast_ne_zero.mpr hy0))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Simplify using `[Units.smul_def, Int.cast_smul_eq_zsmul]`.

Establish `hf1 : (fun j => ∑ i, G i j • x' i) = fun j => y • x j` using `funext fun j => (hw1 j).symm`. Establish `hf2 : (fun j => ∑ i, D i j • x i) = fun j => y • x j` using `funext fun j => (hw2 j).symm`. Establish `hGdet : G.det ≠ 0` using `ds_det_ne_zero_of_comb G (by rw [hf1]; exact hwli)`. Establish `hDdet : D.det ≠ 0` using `ds_det_ne_zero_of_comb D (by rw [hf2]; exact hwli)`. Establish `iG` using `ds_relIndex_span_comb hxi' G hGdet`.

Establish `iD` using `ds_relIndex_span_comb hxi D hDdet`. Rewrite `iG` using `[hf1]`. Rewrite `iD` using `[hf2]`. Use `set M := Submodule.span (𝓞 K) (Set.range fun j => y • x j) with hM`. Use `set Λ := Submodule.span (𝓞 K) (Set.range x) with hΛ`.

Use `set Λ' := Submodule.span (𝓞 K) (Set.range x') with hΛ'`. Establish `hMΛ : M ≤ Λ`. Rewrite using `[hM, Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Use `show y • x j ∈ Λ`.

Rewrite using `[hw2 j]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hMΛ' : M ≤ Λ'`. Rewrite using `[hM, Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Use `show y • x j ∈ Λ'`. Rewrite using `[hw1 j]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hΛL : Λ ≤ L` using `Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hx i)`. Establish `hΛL' : Λ' ≤ L'` using `Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hx' i)`.

Establish `e1` using `AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hMΛ) (Submodule.toAddSubgroup_mono (hΛL.trans hLL))`. Establish `e2` using `AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hΛL) (Submodule.toAddSubgroup_mono hLL)`. Establish `e3` using `AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hMΛ') (Submodule.toAddSubgroup_mono hΛL')`. Establish `hneL` using `hframe.relIndex_span_frame_ne_zero hL.1`. Establish `hneL'` using `hframe'.relIndex_span_frame_ne_zero hL'.1`.

Establish `hv1 : padicValNat p (Λ.toAddSubgroup.relIndex L.toAddSubgroup) = 0` using `padicValNat_relIndex_eq_zero p hs fun v hv => by`. Rewrite using `[Submodule.mem_toAddSubgroup, ← Nat.cast_smul_eq_nsmul K]`. Conclude with `hsL v hv`. Establish `hv1' : padicValNat p (Λ'.toAddSubgroup.relIndex L'.toAddSubgroup) = 0` using `padicValNat_relIndex_eq_zero p hs' fun v hv => by`. Rewrite using `[Submodule.mem_toAddSubgroup, ← Nat.cast_smul_eq_nsmul K]`.

Conclude with `hsL' v hv`. Establish `hidx : (Algebra.norm ℤ D.det).natAbs * (Λ.toAddSubgroup.relIndex L.toAddSubgroup * L.toAddSubgroup.relIndex L'.toAddSubgroup) = (Algebra.norm ℤ G.det).natAbs * Λ'.toAddSubgroup.relIndex L'.toAddSubgroup`. Rewrite using `[e2, ← iD, e1, ← iG, e3]`. Establish `hnD : Algebra.norm ℤ D.det ≠ 0`. Introduce `h0`.

Use `Algebra.coe_norm_int (K := K) D.det` as an intermediate fact. Rewrite `this` using `[h0, Int.cast_zero, eq_comm, Algebra.norm_eq_zero_iff]`. Conclude with `hDdet (by exact_mod_cast this)`. Establish `hnG : Algebra.norm ℤ G.det ≠ 0`. Introduce `h0`.

Use `Algebra.coe_norm_int (K := K) G.det` as an intermediate fact. Rewrite `this` using `[h0, Int.cast_zero, eq_comm, Algebra.norm_eq_zero_iff]`. Conclude with `hGdet (by exact_mod_cast this)`. Establish `hprod0 : Λ.toAddSubgroup.relIndex L.toAddSubgroup * L.toAddSubgroup.relIndex L'.toAddSubgroup ≠ 0`. Introduce `h0`.

Rewrite `hidx` using `[h0, mul_zero, eq_comm, mul_eq_zero]`. Break down `hidx with h | h` into its components or cases. Conclude with `hnG (Int.natAbs_eq_zero.mp h)`. Conclude with `hneL' h`. Establish `hneLL : L.toAddSubgroup.relIndex L'.toAddSubgroup ≠ 0` using `right_ne_zero_of_mul hprod0`.

Establish `hvN` using `congrArg (padicValNat p) hidx`. Rewrite `hvN` using `[padicValNat.mul (Int.natAbs_ne_zero.mpr hnD) hprod0, padicValNat.mul hneL hneLL, hv1, padicValNat.mul (Int.natAbs_ne_zero.mpr hnG) hneL', hv1']`. Use `set X : Matrix (Fin g) (Fin g) K := Matrix.of fun i k => x k i with hX`. Use `set X' : Matrix (Fin g) (Fin g) K := Matrix.of fun i k => x' k i with hX'`. Establish `hmat : X * D.map (algebraMap (𝓞 K) K) = X' * G.map (algebraMap (𝓞 K) K)`.

Rewrite using `[hX, hX', ← of_comb_eq_mul x (fun j => y • x j) D hw2, ← of_comb_eq_mul x' (fun j => y • x j) G hw1]`. Establish `hdetX : X.det ≠ 0`. Establish `hu : IsUnit X` using `Matrix.linearIndependent_cols_iff_isUnit.mp hxi`. Conclude with `(Matrix.isUnit_iff_isUnit_det X |>.mp hu).ne_zero`. Establish `hdetX' : X'.det ≠ 0`.

Establish `hu : IsUnit X'` using `Matrix.linearIndependent_cols_iff_isUnit.mp hxi'`. Conclude with `(Matrix.isUnit_iff_isUnit_det X' |>.mp hu).ne_zero`. Establish `hmapdet : ∀ A : Matrix (Fin g) (Fin g) (𝓞 K), Algebra.norm ℚ (A.map (algebraMap (𝓞 K) K)).det = (Algebra.norm ℤ A.det : ℚ)`. Introduce `A`. Rewrite using `[Algebra.coe_norm_int]`.

Use `congr 1`. Conclude with `(RingHom.map_det (algebraMap (𝓞 K) K) A).symm`. Establish `hN` using `congrArg (fun A => Algebra.norm ℚ A.det) hmat`. Simplify using `only [Matrix.det_mul, map_mul, hmapdet] at hN`. Establish `hNX : Algebra.norm ℚ X.det ≠ 0` using `Algebra.norm_ne_zero_iff.mpr hdetX`.

Establish `hNX' : Algebra.norm ℚ X'.det ≠ 0` using `Algebra.norm_ne_zero_iff.mpr hdetX'`. Establish `hvQ` using `congrArg (padicValRat p) hN`. Rewrite `hvQ` using `[padicValRat.mul hNX (by exact_mod_cast hnD), padicValRat.mul hNX' (by exact_mod_cast hnG), padicValRat.of_int, padicValRat.of_int]`. Establish `hD' : padicValInt p (Algebra.norm ℤ D.det) = padicValNat p (Algebra.norm ℤ D.det).natAbs` using `rfl`. Establish `hG' : padicValInt p (Algebra.norm ℤ G.det) = padicValNat p (Algebra.norm ℤ G.det).natAbs` using `rfl`.

Rewrite `hvQ` using `[hD', hG']`. Establish `hvN' : ((padicValNat p (Algebra.norm ℤ D.det).natAbs : ℕ) : ℤ) + (padicValNat p (L.toAddSubgroup.relIndex L'.toAddSubgroup) : ℤ) = (padicValNat p (Algebra.norm ℤ G.det).natAbs : ℤ)`. Use `hvN` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem padicValNat_relIndex_eq (K : Type) [Field K] [NumberField K] (g p : ℕ) [Fact p.Prime]
    (L L' : Submodule (𝓞 K) (Fin g → K)) (x x' : Fin g → Fin g → K) (s s' : ℕ) (hL : Full L) (hL' : Full L')
    (hLL : L ≤ L') (hx : ∀ i, x i ∈ L) (hxi : LinearIndependent K x) (hs : ¬ p ∣ s)
    (hsL : ∀ v ∈ L, (s : K) • v ∈ Submodule.span (𝓞 K) (Set.range x)) (hx' : ∀ i, x' i ∈ L')
    (hxi' : LinearIndependent K x') (hs' : ¬ p ∣ s')
    (hsL' : ∀ v ∈ L', (s' : K) • v ∈ Submodule.span (𝓞 K) (Set.range x')) :
    (padicValNat p (L.toAddSubgroup.relIndex L'.toAddSubgroup) : ℤ) =
      padicValRat p (Algebra.norm ℚ (Matrix.of fun i k => x k i).det) -
        padicValRat p (Algebra.norm ℚ (Matrix.of fun i k => x' k i).det) := by
  classical
  have hp := (Fact.out : p.Prime)
  have hs0 : (s : K) ≠ 0 := Nat.cast_ne_zero.mpr (by rintro rfl; exact hs (dvd_zero p))
  have hs0' : (s' : K) ≠ 0 := Nat.cast_ne_zero.mpr (by rintro rfl; exact hs' (dvd_zero p))

  have spanK : ∀ (t : ℕ) (z : Fin g → Fin g → K), (t : K) ≠ 0 → ∀ v,
      (t : K) • v ∈ Submodule.span (𝓞 K) (Set.range z) → v ∈ Submodule.span K (Set.range z) := by
    intro t z ht v hv
    have h2 : (t : K) • v ∈ Submodule.span K (Set.range z) :=
      Submodule.span_le_restrictScalars (𝓞 K) K _ hv
    have := Submodule.smul_mem _ ((t : K)⁻¹) h2
    rwa [smul_smul, inv_mul_cancel₀ ht, one_smul] at this
  have hframe : IsFrame K L x := ⟨hx, hxi, fun v hv => spanK s x hs0 v (hsL v hv)⟩
  have hframe' : IsFrame K L' x' := ⟨hx', hxi', fun v hv => spanK s' x' hs0' v (hsL' v hv)⟩
  have hxK : ∀ j, x j ∈ Submodule.span K (Set.range x') := fun j =>
    spanK s' x' hs0' _ (hsL' _ (hLL (hx j)))
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun K).mp (hxK j)
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := K)
    (Finset.univ.image fun q : Fin g × Fin g => c q.1 q.2)
  have hd : ∀ j i, IsIntegral ℤ (y • c j i) := fun j i =>
    hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ (j, i)))
  let G : Matrix (Fin g) (Fin g) (𝓞 K) := fun i j => ⟨y • c j i, hd j i⟩
  let D : Matrix (Fin g) (Fin g) (𝓞 K) := Matrix.diagonal fun _ => (y : 𝓞 K)
  have hw1 : ∀ j, y • x j = ∑ i, G i j • x' i := by
    intro j
    rw [← hc j, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (G i j) (x' i), ← smul_assoc]
    rfl
  have hw2 : ∀ j, y • x j = ∑ i, D i j • x i := by
    intro j
    simp [D, Matrix.diagonal_apply, Int.cast_smul_eq_zsmul]
  have hwli : LinearIndependent K (fun j => y • x j) := by
    have := hxi.units_smul (fun _ => Units.mk0 (y : K) (Int.cast_ne_zero.mpr hy0))
    convert this using 1
    funext j
    simp [Units.smul_def, Int.cast_smul_eq_zsmul]
  have hf1 : (fun j => ∑ i, G i j • x' i) = fun j => y • x j := funext fun j => (hw1 j).symm
  have hf2 : (fun j => ∑ i, D i j • x i) = fun j => y • x j := funext fun j => (hw2 j).symm
  have hGdet : G.det ≠ 0 := ds_det_ne_zero_of_comb G (by rw [hf1]; exact hwli)
  have hDdet : D.det ≠ 0 := ds_det_ne_zero_of_comb D (by rw [hf2]; exact hwli)
  have iG := ds_relIndex_span_comb hxi' G hGdet
  have iD := ds_relIndex_span_comb hxi D hDdet
  rw [hf1] at iG
  rw [hf2] at iD
  set M := Submodule.span (𝓞 K) (Set.range fun j => y • x j) with hM
  set Λ := Submodule.span (𝓞 K) (Set.range x) with hΛ
  set Λ' := Submodule.span (𝓞 K) (Set.range x') with hΛ'
  have hMΛ : M ≤ Λ := by
    rw [hM, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show y • x j ∈ Λ
    rw [hw2 j]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hMΛ' : M ≤ Λ' := by
    rw [hM, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show y • x j ∈ Λ'
    rw [hw1 j]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hΛL : Λ ≤ L := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hx i)
  have hΛL' : Λ' ≤ L' := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hx' i)
  have e1 := AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hMΛ)
    (Submodule.toAddSubgroup_mono (hΛL.trans hLL))
  have e2 := AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hΛL)
    (Submodule.toAddSubgroup_mono hLL)
  have e3 := AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hMΛ')
    (Submodule.toAddSubgroup_mono hΛL')
  have hneL := hframe.relIndex_span_frame_ne_zero hL.1
  have hneL' := hframe'.relIndex_span_frame_ne_zero hL'.1
  have hv1 : padicValNat p (Λ.toAddSubgroup.relIndex L.toAddSubgroup) = 0 :=
    padicValNat_relIndex_eq_zero p hs fun v hv => by
      rw [Submodule.mem_toAddSubgroup, ← Nat.cast_smul_eq_nsmul K]; exact hsL v hv
  have hv1' : padicValNat p (Λ'.toAddSubgroup.relIndex L'.toAddSubgroup) = 0 :=
    padicValNat_relIndex_eq_zero p hs' fun v hv => by
      rw [Submodule.mem_toAddSubgroup, ← Nat.cast_smul_eq_nsmul K]; exact hsL' v hv

  have hidx : (Algebra.norm ℤ D.det).natAbs * (Λ.toAddSubgroup.relIndex L.toAddSubgroup *
      L.toAddSubgroup.relIndex L'.toAddSubgroup) =
      (Algebra.norm ℤ G.det).natAbs * Λ'.toAddSubgroup.relIndex L'.toAddSubgroup := by
    rw [e2, ← iD, e1, ← iG, e3]
  have hnD : Algebra.norm ℤ D.det ≠ 0 := by
    intro h0
    have := Algebra.coe_norm_int (K := K) D.det
    rw [h0, Int.cast_zero, eq_comm, Algebra.norm_eq_zero_iff] at this
    exact hDdet (by exact_mod_cast this)
  have hnG : Algebra.norm ℤ G.det ≠ 0 := by
    intro h0
    have := Algebra.coe_norm_int (K := K) G.det
    rw [h0, Int.cast_zero, eq_comm, Algebra.norm_eq_zero_iff] at this
    exact hGdet (by exact_mod_cast this)
  have hprod0 : Λ.toAddSubgroup.relIndex L.toAddSubgroup * L.toAddSubgroup.relIndex L'.toAddSubgroup ≠ 0 := by
    intro h0
    rw [h0, mul_zero, eq_comm, mul_eq_zero] at hidx
    rcases hidx with h | h
    · exact hnG (Int.natAbs_eq_zero.mp h)
    · exact hneL' h
  have hneLL : L.toAddSubgroup.relIndex L'.toAddSubgroup ≠ 0 := right_ne_zero_of_mul hprod0
  have hvN := congrArg (padicValNat p) hidx
  rw [padicValNat.mul (Int.natAbs_ne_zero.mpr hnD) hprod0, padicValNat.mul hneL hneLL, hv1,
    padicValNat.mul (Int.natAbs_ne_zero.mpr hnG) hneL', hv1'] at hvN

  set X : Matrix (Fin g) (Fin g) K := Matrix.of fun i k => x k i with hX
  set X' : Matrix (Fin g) (Fin g) K := Matrix.of fun i k => x' k i with hX'
  have hmat : X * D.map (algebraMap (𝓞 K) K) = X' * G.map (algebraMap (𝓞 K) K) := by
    rw [hX, hX', ← of_comb_eq_mul x (fun j => y • x j) D hw2, ← of_comb_eq_mul x' (fun j => y • x j) G hw1]
  have hdetX : X.det ≠ 0 := by
    have hu : IsUnit X := Matrix.linearIndependent_cols_iff_isUnit.mp hxi
    exact (Matrix.isUnit_iff_isUnit_det X |>.mp hu).ne_zero
  have hdetX' : X'.det ≠ 0 := by
    have hu : IsUnit X' := Matrix.linearIndependent_cols_iff_isUnit.mp hxi'
    exact (Matrix.isUnit_iff_isUnit_det X' |>.mp hu).ne_zero
  have hmapdet : ∀ A : Matrix (Fin g) (Fin g) (𝓞 K),
      Algebra.norm ℚ (A.map (algebraMap (𝓞 K) K)).det = (Algebra.norm ℤ A.det : ℚ) := by
    intro A
    rw [Algebra.coe_norm_int]
    congr 1
    exact (RingHom.map_det (algebraMap (𝓞 K) K) A).symm
  have hN := congrArg (fun A => Algebra.norm ℚ A.det) hmat
  simp only [Matrix.det_mul, map_mul, hmapdet] at hN
  have hNX : Algebra.norm ℚ X.det ≠ 0 := Algebra.norm_ne_zero_iff.mpr hdetX
  have hNX' : Algebra.norm ℚ X'.det ≠ 0 := Algebra.norm_ne_zero_iff.mpr hdetX'
  have hvQ := congrArg (padicValRat p) hN
  rw [padicValRat.mul hNX (by exact_mod_cast hnD), padicValRat.mul hNX' (by exact_mod_cast hnG),
    padicValRat.of_int, padicValRat.of_int] at hvQ
  have hD' : padicValInt p (Algebra.norm ℤ D.det) = padicValNat p (Algebra.norm ℤ D.det).natAbs := rfl
  have hG' : padicValInt p (Algebra.norm ℤ G.det) = padicValNat p (Algebra.norm ℤ G.det).natAbs := rfl
  rw [hD', hG'] at hvQ
  have hvN' : ((padicValNat p (Algebra.norm ℤ D.det).natAbs : ℕ) : ℤ) +
      (padicValNat p (L.toAddSubgroup.relIndex L'.toAddSubgroup) : ℤ) =
      (padicValNat p (Algebra.norm ℤ G.det).natAbs : ℤ) := by
    have := hvN
    omega
  linarith

end GlobalTheory.LocIndex
