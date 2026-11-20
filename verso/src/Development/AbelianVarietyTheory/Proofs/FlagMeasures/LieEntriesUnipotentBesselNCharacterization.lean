import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalBlockUnitriangularFlag
import Formalism.FormalDegreeBessel.FinalG

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal Nat

noncomputable section

namespace GlobalTheory.CellDens.LieN

def Cond (k r : ℕ) (X : Mat k r) : Prop :=
  Xᴴ * Hpk k r + Hpk k r * X = 0 ∧ ∀ i j : Fin (2 * r + k + 1), lev k r j ≤ lev k r i → X i j = 0

/- English proof (translation)
Use `⟨?_, fun i j hij => by rw [Matrix.smul_apply, h.2 i j hij, smul_zero]⟩` and prove the remaining obligations. Rewrite using `[conjTranspose_smul, smul_mul_assoc, mul_smul_comm, Complex.star_def, Complex.conj_ofReal, ← smul_add, h.1, smul_zero]`.
-/
theorem Cond.smul {k r : ℕ} {X : Mat k r} (h : Cond k r X) (t : ℝ) : Cond k r ((t : ℂ) • X) := by
  refine ⟨?_, fun i j hij => by rw [Matrix.smul_apply, h.2 i j hij, smul_zero]⟩
  rw [conjTranspose_smul, smul_mul_assoc, mul_smul_comm, Complex.star_def, Complex.conj_ofReal, ← smul_add, h.1,
    smul_zero]

/- English proof (translation)
Use `⟨?_, fun i j hij => by rw [Matrix.add_apply, h.2 i j hij, h'.2 i j hij, add_zero]⟩` and prove the remaining obligations. Rewrite using `[conjTranspose_add, add_mul, mul_add, add_add_add_comm, h.1, h'.1, add_zero]`.
-/
theorem Cond.add {k r : ℕ} {X Y : Mat k r} (h : Cond k r X) (h' : Cond k r Y) : Cond k r (X + Y) := by
  refine ⟨?_, fun i j hij => by rw [Matrix.add_apply, h.2 i j hij, h'.2 i j hij, add_zero]⟩
  rw [conjTranspose_add, add_mul, mul_add, add_add_add_comm, h.1, h'.1, add_zero]

open MeasureTheory Matrix Filter Topology in
open scoped InnerProductSpace ENNReal Nat in
/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `apply Complex.ext <;> simp [_root_.Formalism.MainNotions.S.unrealify, hx, _root_.Formalism.MainNotions.S.realifyFun]`.
-/
private lemma unrealify_eq_of_realifyFun_coords {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool))
    (X : Matrix (Fin m) (Fin m) ℂ) (hx : ∀ p, x.ofLp p = _root_.Formalism.MainNotions.S.realifyFun X p) : _root_.Formalism.MainNotions.S.unrealify x = X := by
  ext i j
  apply Complex.ext <;> simp [_root_.Formalism.MainNotions.S.unrealify, hx, _root_.Formalism.MainNotions.S.realifyFun]

open MeasureTheory Matrix Filter Topology in
open scoped InnerProductSpace ENNReal Nat in
/- English proof (translation)
Use `letI : NormedRing (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAlgebra`. Establish `h` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0`. Rewrite `h` using `[hasDerivAt_iff_tendsto_slope]`. Simplify using `only [zero_smul, NormedSpace.exp_zero, one_mul] at h`.

Use `h.congr' ?_` and prove the remaining obligations. Use `filter_upwards with t`. Simplify using `[slope, Complex.coe_smul]`. Both sides reduce to the same expression.
-/
private lemma tendsto_inv_smul_exp_smul_sub_one {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    Tendsto (fun t : ℝ => t⁻¹ • (NormedSpace.exp ((t : ℂ) • X) - 1)) (𝓝[≠] 0) (𝓝 X) := by
  letI : NormedRing (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAlgebra
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  rw [hasDerivAt_iff_tendsto_slope] at h
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  refine h.congr' ?_
  filter_upwards with t
  simp [slope, Complex.coe_smul]
  rfl

open MeasureTheory Matrix Filter Topology in
open scoped InnerProductSpace ENNReal Nat in
/- English proof (translation)
Establish `hD` using `tendsto_inv_smul_exp_smul_sub_one X`. Use `⟨?_, fun i j h => ?_⟩` and prove the remaining obligations. Establish `hg : Tendsto (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) (𝓝[≠] 0) (𝓝 1)`. Establish `h0 : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (𝓝 0)` using `tendsto_id.mono_left nhdsWithin_le_nhds`. Establish `h1` using `(h0.smul hD).const_add 1`.

Rewrite `h1` using `[zero_smul, add_zero]`. Use `h1.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with t ht`. Simplify using `only [smul_smul, mul_inv_cancel₀ (show t ≠ 0 from ht), one_smul, add_sub_cancel]`. Establish `hE : Tendsto (fun t : ℝ => (t⁻¹ • (NormedSpace.exp ((t : ℂ) • X) - 1))ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * NormedSpace.exp ((t : ℂ) • X) + _root_.Formalism.QuantumDeterminants.Hpk k r * (t⁻¹ • (NormedSpace.exp ((t : ℂ) • X) - 1))) (𝓝[≠] 0) (𝓝 (Xᴴ * _root_.Formalism. …` using `((((continuous_id.matrix_conjTranspose).tendsto X).comp hD).mul_const (_root_.Formalism.QuantumDeterminants.Hpk k r) |>.mul hg).add (hD.const_mul (_root_.Formalism.QuantumDeterminants.Hpk k r))`.

Establish `hzero : ∀ t : ℝ, (t⁻¹ • (NormedSpace.exp ((t : ℂ) • X) - 1))ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * NormedSpace.exp ((t : ℂ) • X) + _root_.Formalism.QuantumDeterminants.Hpk k r * (t⁻¹ • (NormedSpace.exp ((t : ℂ) • X) - 1)) = 0`. Introduce `t`. Establish `hu : (NormedSpace.exp ((t : ℂ) • X))ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * NormedSpace.exp ((t : ℂ) • X) = _root_.Formalism.QuantumDeterminants.Hpk k r` using `((_root_.Formalism.QuantumDeterminants.WeylGroupFacts.nset_iff _).1 (hX t)).1`. Establish `e : (NormedSpace.exp ((t : ℂ) • X) - 1)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * NormedSpace.exp ((t : ℂ) • X) + _root_.Formalism.QuantumDeterminants.Hpk k r * (NormedSpace.exp ((t : ℂ) • X) - 1) = 0`. Rewrite using `[conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, hu, Matrix.one_mul, Matrix.mul_one]`.

Normalize the expressions using the abelian group laws. Rewrite using `[conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, e, smul_zero]`. Establish `hlim` using `tendsto_nhds_unique hE (by simp only [hzero]; exact tendsto_const_nhds)`. Simplify `hlim` using `[Matrix.mul_one]`. Establish `hE : Tendsto (fun t : ℝ => (t⁻¹ • (NormedSpace.exp ((t : ℂ) • X) - 1)) i j) (𝓝[≠] 0) (𝓝 (X i j))` using `((continuous_id.matrix_elem i j).tendsto X).comp hD`.

Establish `hz : ∀ t : ℝ, (t⁻¹ • (NormedSpace.exp ((t : ℂ) • X) - 1)) i j = 0`. Introduce `t`. Establish `he` using `_root_.GlobalTheory.CellDens.nset_block_unitriangular k r _ (hX t) i j h`. Rewrite using `[Matrix.smul_apply, Matrix.sub_apply, he]`. Simplify using the standard rewrite rules.

Conclude with `tendsto_nhds_unique hE (by simp only [hz]; exact tendsto_const_nhds)`.
-/
private lemma lieNCond_of_exp_smul_mem_Nset {k r : ℕ}
    (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ _root_.Formalism.QuantumDeterminants.Nset k r) :
    _root_.GlobalTheory.CellDens.LieN.Cond k r X := by
  have hD := tendsto_inv_smul_exp_smul_sub_one X
  refine ⟨?_, fun i j h => ?_⟩
  · have hg : Tendsto (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) (𝓝[≠] 0) (𝓝 1) := by
      have h0 : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have h1 := (h0.smul hD).const_add 1
      rw [zero_smul, add_zero] at h1
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [smul_smul, mul_inv_cancel₀ (show t ≠ 0 from ht), one_smul, add_sub_cancel]
    have hE : Tendsto (fun t : ℝ => (t⁻¹ • (NormedSpace.exp ((t : ℂ) • X) - 1))ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r *
        NormedSpace.exp ((t : ℂ) • X) + _root_.Formalism.QuantumDeterminants.Hpk k r * (t⁻¹ • (NormedSpace.exp ((t : ℂ) • X) - 1)))
        (𝓝[≠] 0) (𝓝 (Xᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * 1 + _root_.Formalism.QuantumDeterminants.Hpk k r * X)) :=
      ((((continuous_id.matrix_conjTranspose).tendsto X).comp hD).mul_const (_root_.Formalism.QuantumDeterminants.Hpk k r)
        |>.mul hg).add (hD.const_mul (_root_.Formalism.QuantumDeterminants.Hpk k r))
    have hzero : ∀ t : ℝ, (t⁻¹ • (NormedSpace.exp ((t : ℂ) • X) - 1))ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r *
        NormedSpace.exp ((t : ℂ) • X) + _root_.Formalism.QuantumDeterminants.Hpk k r * (t⁻¹ • (NormedSpace.exp ((t : ℂ) • X) - 1))
        = 0 := by
      intro t
      have hu : (NormedSpace.exp ((t : ℂ) • X))ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * NormedSpace.exp ((t : ℂ) • X)
          = _root_.Formalism.QuantumDeterminants.Hpk k r := ((_root_.Formalism.QuantumDeterminants.WeylGroupFacts.nset_iff _).1 (hX t)).1
      have e : (NormedSpace.exp ((t : ℂ) • X) - 1)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * NormedSpace.exp ((t : ℂ) • X)
          + _root_.Formalism.QuantumDeterminants.Hpk k r * (NormedSpace.exp ((t : ℂ) • X) - 1) = 0 := by
        rw [conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, hu,
          Matrix.one_mul, Matrix.mul_one]
        abel
      rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
        ← smul_add, e, smul_zero]
    have hlim := tendsto_nhds_unique hE (by simp only [hzero]; exact tendsto_const_nhds)
    simpa [Matrix.mul_one] using hlim
  · have hE : Tendsto (fun t : ℝ => (t⁻¹ • (NormedSpace.exp ((t : ℂ) • X) - 1)) i j) (𝓝[≠] 0)
        (𝓝 (X i j)) := ((continuous_id.matrix_elem i j).tendsto X).comp hD
    have hz : ∀ t : ℝ, (t⁻¹ • (NormedSpace.exp ((t : ℂ) • X) - 1)) i j = 0 := by
      intro t
      have he := _root_.GlobalTheory.CellDens.nset_block_unitriangular k r _ (hX t) i j h
      rw [Matrix.smul_apply, Matrix.sub_apply, he]
      simp
    exact tendsto_nhds_unique hE (by simp only [hz]; exact tendsto_const_nhds)

open MeasureTheory Matrix Filter Topology in
open scoped InnerProductSpace ENNReal Nat in
/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `apply Complex.ext <;> simp [_root_.Formalism.MainNotions.S.unrealify]`.
-/
private lemma unrealify_zero_flag_measures {m : ℕ} :
    _root_.Formalism.MainNotions.S.unrealify (0 : EuclideanSpace ℝ (Fin m × Fin m × Bool)) = 0 := by
  ext i j
  apply Complex.ext <;> simp [_root_.Formalism.MainNotions.S.unrealify]

open MeasureTheory Matrix Filter Topology in
open scoped InnerProductSpace ENNReal Nat in
/- English proof (translation)
Assemble the required witnesses or components as `⟨by simp, fun _ _ _ => rfl⟩`.
-/
private lemma lieNCond_zero {k r : ℕ} :
    _root_.GlobalTheory.CellDens.LieN.Cond k r (0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  ⟨by simp, fun _ _ _ => rfl⟩

open MeasureTheory Matrix Filter Topology in
open scoped InnerProductSpace ENNReal Nat in
/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `apply Complex.ext <;> simp [_root_.Formalism.MainNotions.S.unrealify]`.
-/
private lemma unrealify_add_flag_measures {m : ℕ} (x y : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    _root_.Formalism.MainNotions.S.unrealify (x + y) = _root_.Formalism.MainNotions.S.unrealify x + _root_.Formalism.MainNotions.S.unrealify y := by
  ext i j
  apply Complex.ext <;> simp [_root_.Formalism.MainNotions.S.unrealify]

open MeasureTheory Matrix Filter Topology in
open scoped InnerProductSpace ENNReal Nat in
/- English proof (translation)
Use `⟨?_, fun i j h => ?_⟩` and prove the remaining obligations. Rewrite using `[conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX.1, hY.1, add_zero]`. Rewrite using `[Matrix.add_apply, hX.2 i j h, hY.2 i j h, add_zero]`.
-/
private lemma lieNCond_add {k r : ℕ} {X Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hX : _root_.GlobalTheory.CellDens.LieN.Cond k r X) (hY : _root_.GlobalTheory.CellDens.LieN.Cond k r Y) :
    _root_.GlobalTheory.CellDens.LieN.Cond k r (X + Y) := by
  refine ⟨?_, fun i j h => ?_⟩
  · rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX.1, hY.1, add_zero]
  · rw [Matrix.add_apply, hX.2 i j h, hY.2 i j h, add_zero]

open MeasureTheory Matrix Filter Topology in
open scoped InnerProductSpace ENNReal Nat in
/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `apply Complex.ext <;> simp [_root_.Formalism.MainNotions.S.unrealify]`.
-/
private lemma unrealify_smul_flag_measures {m : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    _root_.Formalism.MainNotions.S.unrealify (c • x) = (c : ℂ) • _root_.Formalism.MainNotions.S.unrealify x := by
  ext i j
  apply Complex.ext <;> simp [_root_.Formalism.MainNotions.S.unrealify]

open MeasureTheory Matrix Filter Topology in
open scoped InnerProductSpace ENNReal Nat in
/- English proof (translation)
Use `⟨?_, fun i j h => ?_⟩` and prove the remaining obligations. Rewrite using `[conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX.1, smul_zero]`. Rewrite using `[Matrix.smul_apply, hX.2 i j h, smul_zero]`.
-/
private lemma lieNCond_smul {k r : ℕ} (c : ℝ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hX : _root_.GlobalTheory.CellDens.LieN.Cond k r X) :
    _root_.GlobalTheory.CellDens.LieN.Cond k r ((c : ℂ) • X) := by
  refine ⟨?_, fun i j h => ?_⟩
  · rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hX.1, smul_zero]
  · rw [Matrix.smul_apply, hX.2 i j h, smul_zero]

open MeasureTheory Matrix Filter Topology in
open scoped InnerProductSpace ENNReal Nat in
/- English proof (translation)
Introduce `i j h`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : f l ≤ f i`. Rewrite using `[hA i l hl, zero_mul]`.

Rewrite using `[hB l j (by omega), mul_zero]`.
-/
private lemma mul_apply_eq_zero_of_level_le {n : ℕ} (f : Fin n → ℕ) (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, f j ≤ f i → A i j = 0) (hB : ∀ i j, f j ≤ f i → B i j = 0) :
    ∀ i j, f j ≤ f i → (A * B) i j = 0 := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : f l ≤ f i
  · rw [hA i l hl, zero_mul]
  · rw [hB l j (by omega), mul_zero]

open MeasureTheory Matrix Filter Topology in
open scoped InnerProductSpace ENNReal Nat in
/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simpa using hY`. Consider the case `succ m ih`. Introduce `i j h`.

Rewrite using `[pow_succ]`. Conclude with `mul_apply_eq_zero_of_level_le f _ _ ih hY i j h`.
-/
private lemma pow_succ_apply_eq_zero_of_level_le {n : ℕ} (f : Fin n → ℕ)
    (Y : Matrix (Fin n) (Fin n) ℂ) (hY : ∀ i j, f j ≤ f i → Y i j = 0) :
    ∀ m i j, f j ≤ f i → (Y ^ (m + 1)) i j = 0 := by
  intro m
  induction m with
  | zero => simpa using hY
  | succ m ih =>
    intro i j h
    rw [pow_succ]
    exact mul_apply_eq_zero_of_level_le f _ _ ih hY i j h

open MeasureTheory Matrix Filter Topology in
open scoped InnerProductSpace ENNReal Nat in
/- English proof (translation)
Use `letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra`. Establish `hs : HasSum (fun m : ℕ => ((m.factorial : ℂ)⁻¹ • Y ^ m)) (NormedSpace.exp Y)` using `NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y`. Establish `hs' : HasSum (fun m : ℕ => ((m.factorial : ℂ)⁻¹ • Y ^ m) i j) (NormedSpace.exp Y i j)` using `Pi.hasSum.1 (Pi.hasSum.1 hs i) j`. Use `hs'.unique ?_` and prove the remaining obligations.

Use `hasSum_single (f := fun m : ℕ => ((m.factorial : ℂ)⁻¹ • Y ^ m) i j) 0 ?_ using 1` and compare the differences between its conclusion and the goal. Simplify using the standard rewrite rules. Introduce `m hm`. Take `⟨m, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hm`. Simplify using `[Matrix.smul_apply, pow_succ_apply_eq_zero_of_level_le f Y hY m i j h]`.
-/
private lemma exp_apply_eq_one_apply_of_level_le {n : ℕ} (f : Fin n → ℕ) (Y : Matrix (Fin n) (Fin n) ℂ)
    (hY : ∀ i j, f j ≤ f i → Y i j = 0) (i j : Fin n) (h : f j ≤ f i) :
    NormedSpace.exp Y i j = (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have hs : HasSum (fun m : ℕ => ((m.factorial : ℂ)⁻¹ • Y ^ m)) (NormedSpace.exp Y) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y
  have hs' : HasSum (fun m : ℕ => ((m.factorial : ℂ)⁻¹ • Y ^ m) i j) (NormedSpace.exp Y i j) :=
    Pi.hasSum.1 (Pi.hasSum.1 hs i) j
  refine hs'.unique ?_
  convert hasSum_single (f := fun m : ℕ => ((m.factorial : ℂ)⁻¹ • Y ^ m) i j) 0 ?_ using 1
  · simp
  · intro m hm
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    simp [Matrix.smul_apply, pow_succ_apply_eq_zero_of_level_le f Y hY m i j h]

open MeasureTheory Matrix Filter Topology in
open scoped InnerProductSpace ENNReal Nat in
/- English proof (translation)
Rewrite using `[_root_.Formalism.QuantumDeterminants.WeylGroupFacts.nset_iff]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show (NormedSpace.exp Y)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * NormedSpace.exp Y = _root_.Formalism.QuantumDeterminants.Hpk k r`. Establish `hH2 : _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.Formalism.QuantumDeterminants.Hpk k r = 1` using `_root_.Formalism.QuantumDeterminants.GBasic.Hpk_sq k r`. Establish `hinv : (_root_.Formalism.QuantumDeterminants.Hpk k r)⁻¹ = _root_.Formalism.QuantumDeterminants.Hpk k r` using `Matrix.inv_eq_left_inv hH2`.

Establish `hunit : IsUnit (_root_.Formalism.QuantumDeterminants.Hpk k r)` using `⟨⟨_, _, hH2, hH2⟩, rfl⟩`. Establish `e1 : Yᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r = -(_root_.Formalism.QuantumDeterminants.Hpk k r * Y)` using `eq_neg_of_add_eq_zero_left hY.1`. Establish `hYh : Yᴴ = _root_.Formalism.QuantumDeterminants.Hpk k r * -Y * (_root_.Formalism.QuantumDeterminants.Hpk k r)⁻¹`. Rewrite using `[hinv]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hc : (NormedSpace.exp Y)ᴴ = _root_.Formalism.QuantumDeterminants.Hpk k r * NormedSpace.exp (-Y) * _root_.Formalism.QuantumDeterminants.Hpk k r`. Rewrite using `[← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hunit, hinv]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hc]`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.QuantumDeterminants.Hpk k r), hH2, Matrix.one_mul]`. Use `_ = _root_.Formalism.QuantumDeterminants.Hpk k r := by`. Rewrite using `[← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel, NormedSpace.exp_zero, Matrix.mul_one]`. Unfold `_root_.Formalism.QuantumDeterminants.WeylGroupFacts.col`. Introduce `i j hj hij`.

Rewrite using `[exp_apply_eq_one_apply_of_level_le (_root_.GlobalTheory.CellDens.lev k r) Y hY.2 i j ?_, Matrix.one_apply]`. Unfold `_root_.GlobalTheory.CellDens.lev`. Apply the tactic sequence `rcases hij with hij | hij <;> split_ifs <;> omega`.
-/
private lemma exp_mem_Nset_of_lieNCond {k r : ℕ}
    (Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hY : _root_.GlobalTheory.CellDens.LieN.Cond k r Y) : NormedSpace.exp Y ∈ _root_.Formalism.QuantumDeterminants.Nset k r := by
  rw [_root_.Formalism.QuantumDeterminants.WeylGroupFacts.nset_iff]
  refine ⟨?_, ?_⟩
  · show (NormedSpace.exp Y)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * NormedSpace.exp Y = _root_.Formalism.QuantumDeterminants.Hpk k r
    have hH2 : _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.Formalism.QuantumDeterminants.Hpk k r = 1 := _root_.Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
    have hinv : (_root_.Formalism.QuantumDeterminants.Hpk k r)⁻¹ = _root_.Formalism.QuantumDeterminants.Hpk k r := Matrix.inv_eq_left_inv hH2
    have hunit : IsUnit (_root_.Formalism.QuantumDeterminants.Hpk k r) := ⟨⟨_, _, hH2, hH2⟩, rfl⟩
    have e1 : Yᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r = -(_root_.Formalism.QuantumDeterminants.Hpk k r * Y) := eq_neg_of_add_eq_zero_left hY.1
    have hYh : Yᴴ = _root_.Formalism.QuantumDeterminants.Hpk k r * -Y * (_root_.Formalism.QuantumDeterminants.Hpk k r)⁻¹ := by
      rw [hinv]
      calc Yᴴ = Yᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.Formalism.QuantumDeterminants.Hpk k r := by rw [Matrix.mul_assoc, hH2, Matrix.mul_one]
        _ = _root_.Formalism.QuantumDeterminants.Hpk k r * -Y * _root_.Formalism.QuantumDeterminants.Hpk k r := by rw [e1, Matrix.mul_neg]
    have hc : (NormedSpace.exp Y)ᴴ = _root_.Formalism.QuantumDeterminants.Hpk k r * NormedSpace.exp (-Y) * _root_.Formalism.QuantumDeterminants.Hpk k r := by
      rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hunit, hinv]
    calc (NormedSpace.exp Y)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * NormedSpace.exp Y
        = _root_.Formalism.QuantumDeterminants.Hpk k r * (NormedSpace.exp (-Y) * NormedSpace.exp Y) := by
          rw [hc]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.QuantumDeterminants.Hpk k r), hH2, Matrix.one_mul]
      _ = _root_.Formalism.QuantumDeterminants.Hpk k r := by
          rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
            NormedSpace.exp_zero, Matrix.mul_one]
  · unfold _root_.Formalism.QuantumDeterminants.WeylGroupFacts.col
    intro i j hj hij
    rw [exp_apply_eq_one_apply_of_level_le (_root_.GlobalTheory.CellDens.lev k r) Y hY.2 i j ?_,
      Matrix.one_apply]
    unfold _root_.GlobalTheory.CellDens.lev
    rcases hij with hij | hij <;> split_ifs <;> omega

open MeasureTheory Matrix Filter Topology in
open scoped InnerProductSpace ENNReal Nat in
/- English proof (translation)
Use extensionality with `p`. Take `⟨i, j, b⟩` from `p`. Apply the tactic sequence `cases b <;> simp [_root_.Formalism.MainNotions.S.unrealify, _root_.Formalism.MainNotions.S.realifyFun]`.
-/
private lemma equiv_symm_realifyFun_unrealify {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    (WithLp.equiv 2 (Fin m × Fin m × Bool → ℝ)).symm (_root_.Formalism.MainNotions.S.realifyFun (_root_.Formalism.MainNotions.S.unrealify x)) = x := by
  ext p
  obtain ⟨i, j, b⟩ := p
  cases b <;> simp [_root_.Formalism.MainNotions.S.unrealify, _root_.Formalism.MainNotions.S.realifyFun]

open MeasureTheory Matrix Filter Topology in
open scoped InnerProductSpace ENNReal Nat in

/- English proof (translation)
Introduce `k r x`. Establish `key : ∀ y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool), y ∈ _root_.Formalism.MainNotions.S.lieE (_root_.Formalism.QuantumDeterminants.Nset k r) ↔ _root_.GlobalTheory.CellDens.LieN.Cond k r (_root_.Formalism.MainNotions.S.unrealify y)`. Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Unfold `_root_.Formalism.MainNotions.S.lieE at hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨X, hX, rfl⟩` from `hz`. Rewrite using `[unrealify_eq_of_realifyFun_coords _ X (fun _ => rfl)]`.

Conclude with `lieNCond_of_exp_smul_mem_Nset X hX`. Consider the case `zero`. Rewrite using `[unrealify_zero_flag_measures]`. Conclude with `lieNCond_zero`. Consider the case `add z w _ _ hz hw`.

Rewrite using `[unrealify_add_flag_measures]`. Conclude with `lieNCond_add hz hw`. Consider the case `smul c z _ hz`. Rewrite using `[unrealify_smul_flag_measures]`. Conclude with `lieNCond_smul c _ hz`.

Introduce `hy`. Unfold `_root_.Formalism.MainNotions.S.lieE`. Use `Submodule.subset_span ⟨_root_.Formalism.MainNotions.S.unrealify y, fun t => exp_mem_Nset_of_lieNCond _ (lieNCond_smul t _ hy), ?_⟩` and prove the remaining obligations. Conclude with `equiv_symm_realifyFun_unrealify y`. Conclude with `⟨key x, fun hx => exp_mem_Nset_of_lieNCond _ ((key x).1 hx)⟩`.
-/
theorem _root_.GlobalTheory.CellDens.LieN.lieE_Nset : ∀ (k r : ℕ)
    (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)),
    (x ∈ _root_.Formalism.MainNotions.S.lieE (_root_.Formalism.QuantumDeterminants.Nset k r) ↔ ((_root_.Formalism.MainNotions.S.unrealify x)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r + _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.Formalism.MainNotions.S.unrealify x = 0 ∧
      ∀ i j : Fin (2 * r + k + 1),
        _root_.GlobalTheory.CellDens.lev k r j ≤ _root_.GlobalTheory.CellDens.lev k r i →
          _root_.Formalism.MainNotions.S.unrealify x i j = 0)) ∧
    (x ∈ _root_.Formalism.MainNotions.S.lieE (_root_.Formalism.QuantumDeterminants.Nset k r) → NormedSpace.exp (_root_.Formalism.MainNotions.S.unrealify x) ∈ _root_.Formalism.QuantumDeterminants.Nset k r) := by
  intro k r x
  have key : ∀ y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool),
      y ∈ _root_.Formalism.MainNotions.S.lieE (_root_.Formalism.QuantumDeterminants.Nset k r) ↔ _root_.GlobalTheory.CellDens.LieN.Cond k r (_root_.Formalism.MainNotions.S.unrealify y) := by
    intro y
    constructor
    · intro hy
      unfold _root_.Formalism.MainNotions.S.lieE at hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨X, hX, rfl⟩ := hz
        rw [unrealify_eq_of_realifyFun_coords _ X (fun _ => rfl)]
        exact lieNCond_of_exp_smul_mem_Nset X hX
      | zero =>
        rw [unrealify_zero_flag_measures]
        exact lieNCond_zero
      | add z w _ _ hz hw =>
        rw [unrealify_add_flag_measures]
        exact lieNCond_add hz hw
      | smul c z _ hz =>
        rw [unrealify_smul_flag_measures]
        exact lieNCond_smul c _ hz
    · intro hy
      unfold _root_.Formalism.MainNotions.S.lieE
      refine Submodule.subset_span ⟨_root_.Formalism.MainNotions.S.unrealify y, fun t => exp_mem_Nset_of_lieNCond _
        (lieNCond_smul t _ hy), ?_⟩
      exact equiv_symm_realifyFun_unrealify y
  exact ⟨key x, fun hx => exp_mem_Nset_of_lieNCond _ ((key x).1 hx)⟩

end GlobalTheory.CellDens.LieN
