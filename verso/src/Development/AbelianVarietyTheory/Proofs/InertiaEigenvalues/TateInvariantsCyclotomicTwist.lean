import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicNormZpowSubOnePadicValIntStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDecompositionCompletedCyclotomicIntegersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerGeneratorMatrixPerturbationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFixedIffMemCompletedIntegersStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.CyclotomicTowerSubgroupInclusions

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
The claim follows from `le_sup_left`.
-/
theorem unramified_subfield_le_Ks (K : FinExt l) (j : ℕ) : K0 K ≤ Ks K j := le_sup_left

/- English proof (translation)
The claim follows from `sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ (fun _ hx => Exists.intro j hx)) _`.
-/
theorem Ks_le_Kinf (K : FinExt l) (j : ℕ) : Ks K j ≤ Kinf K :=
  sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ (fun _ hx => Exists.intro j hx)) _

/- English proof (translation)
Introduce `_ hg x` and use `hg ⟨x.1, unramified_subfield_le_Ks K j x.2⟩`.
-/
theorem cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified (K : FinExt l) (j : ℕ) : Gj K j ≤ (K0 K).fixingSubgroup :=
  fun _ hg x => hg ⟨x.1, unramified_subfield_le_Ks K j x.2⟩

/- English proof (translation)
Introduce `_ hg x` and use `hg ⟨x.1, Ks_le_Kinf K j x.2⟩`.
-/
theorem Hinf_le_Gj (K : FinExt l) (j : ℕ) : Hinf K ≤ Gj K j :=
  fun _ hg x => hg ⟨x.1, Ks_le_Kinf K j x.2⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_inC_iff (F : IntermediateField ℚ_[l] (Om l)) (y : PadicComplex l) :
    y ∈ inC F ↔ y ∈ F.toSubfield.map (algebraMap (Om l) (PadicComplex l)) := Iff.rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨algebraMap ℚ_[l] (Om l) u, F.algebraMap_mem u, rfl⟩`.
-/
theorem algebraMap_mem_inC (F : IntermediateField ℚ_[l] (Om l)) (u : ℚ_[l]) :
    algebraMap ℚ_[l] (PadicComplex l) u ∈ inC F :=
  ⟨algebraMap ℚ_[l] (Om l) u, F.algebraMap_mem u, rfl⟩

/- English proof (translation)
Take `⟨x, hx, rfl⟩` from `hy`. Use `hg ⟨x, hx⟩` as an intermediate fact. Express the relevant statement in the definitionally equal form `g x = x at this`. Simplify using `only [ha.1, this]`.
-/
theorem act_fix {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {F : IntermediateField ℚ_[l] (Om l)} {g : GQ l} (hg : g ∈ F.fixingSubgroup)
    {y : PadicComplex l} (hy : y ∈ inC F) : act g y = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  have := hg ⟨x, hx⟩
  change g x = x at this
  simp only [ha.1, this]

/- English proof (translation)
Establish `hl : ‖(l : PadicComplex l)‖ < 1`. Establish `h1 : ‖algebraMap ℚ_[l] (PadicComplex l) (l : ℚ_[l])‖ = ‖(l : ℚ_[l])‖` using `norm_algebraMap' _ _`. Rewrite `h1` using `[map_natCast]`. Rewrite using `[h1]`. Conclude with `Padic.norm_p_lt_one`.

Establish `h` using `(tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl).mul_const ‖y‖`. Rewrite `h` using `[zero_mul]`. Take `⟨n, hn⟩` from `(h.eventually (ge_mem_nhds (zero_lt_one' ℝ))).exists`. Conclude with `⟨n, by rwa [norm_mul, norm_pow]⟩`.
-/
theorem exists_scale (y : PadicComplex l) : ∃ n : ℕ, ‖(l : PadicComplex l) ^ n * y‖ ≤ 1 := by
  have hl : ‖(l : PadicComplex l)‖ < 1 := by
    have h1 : ‖algebraMap ℚ_[l] (PadicComplex l) (l : ℚ_[l])‖ = ‖(l : ℚ_[l])‖ := norm_algebraMap' _ _
    rw [map_natCast] at h1
    rw [h1]
    exact Padic.norm_p_lt_one
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl).mul_const ‖y‖
  rw [zero_mul] at h
  obtain ⟨n, hn⟩ := (h.eventually (ge_mem_nhds (zero_lt_one' ℝ))).exists
  exact ⟨n, by rwa [norm_mul, norm_pow]⟩

/- English proof (translation)
Introduce `l _ act χ ha hχ K j hj i y hy`. Take `⟨hnorm, -, hker⟩` from `GlobalTheory.T.cyclotomicCharacterPadic_basic_properties l χ hχ`. Take `⟨⟨g, hg⟩, -⟩` from `GlobalTheory.T.exists_cyclotomicTowerLevelGenerator_properties l act χ ha hχ K j hj`. Take `⟨hdec, hdir, -, hmul, hact, -⟩` from `GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ ha hχ K j hj.1`. Take `⟨n, hn⟩` from `exists_scale y`.

Establish `hl0 : (l : PadicComplex l) ^ n ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)`. Use `set z := (l : PadicComplex l) ^ n * y with hz`. Establish `hzinv : ∀ σ ∈ Gj K j, chiC χ i σ * act σ z = z`. Introduce `σ hσ`. Rewrite using `[hz, map_mul, map_pow, map_natCast, mul_left_comm, hy σ hσ]`.

Establish `hzO : z ∈ Ohat K`. Use `(GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act ha K z hn).mp fun h hh => ?_` and prove the remaining obligations. Establish `h1 : χ h = 1` using `(hker K h (cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified K j (Hinf_le_Gj K j hh))).2.mp hh`. Establish `h2` using `hzinv h (Hinf_le_Gj K j hh)`. Simplify `h2` using `[chiC, h1]`.

Take `⟨a, haK, x, hx, hax⟩` from `hdec z hzO`. Use `set c := chiC χ i g with hc`. Establish `hcK : c ∈ inC (Ks K j)` using `algebraMap_mem_inC _ _`. Establish `hc1 : ‖c‖ = 1`. Rewrite using `[hc, chiC, norm_algebraMap', Units.val_zpow_eq_zpow_val, norm_zpow, hnorm, one_zpow]`.

Establish `hga : act g a = a` using `act_fix ha hg.1 haK.1`. Establish `heq : c * (a + act g x) = a + x`. Use `hzinv g hg.1` as an intermediate fact. Rewrite `this` using `[hax, map_add, hga]`. Then use the resulting hypothesis. Establish `hX : x - c * act g x ∈ Xj K j` using `(Xj K j).sub_mem hx (hmul c ⟨hcK, hc1.le⟩ _ (hact g (cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified K j hg.1) x hx))`.

Establish `hK : (c - 1) * a ∈ inC (Ks K j)`. Rewrite using `[mem_inC_iff]`. Conclude with `Subfield.mul_mem _ (Subfield.sub_mem _ hcK (Subfield.one_mem _)) haK.1`. Establish `h0 : (c - 1) * a = 0` using `hdir _ hK _ hX 0 (by linear_combination heq)`. Establish `hrho : 0 < rho1 l` using `Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Fact.out : l.Prime).pos) _`.

Establish `hx0 : x = 0`. Establish `h` using `(GlobalTheory.T.cyclotomic_tower_generator_matrix_perturbation l act χ ha hχ K j hj g hg 1 (fun _ => 1) (by`. Introduce `a b`. Rewrite using `[Subsingleton.elim a b, Matrix.one_apply_eq]`. Use `⟨?_, by simp⟩` and prove the remaining obligations.

Rewrite using `[mem_inC_iff]`. Conclude with `Subfield.one_mem _) (by intro a b; simpa using hrho) i).1 (fun _ => x) (fun _ => hx) (by`. Use function extensionality and compare the values at `b`. Simplify using `only [twAct, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]`. Take the linear combination `heq - h0)`.

Conclude with `congrFun h 0`. Rewrite `hax` using `[hx0, add_zero]`. Use `⟨fun hi => ?_, fun _ => ?_⟩` and prove the remaining obligations. Establish `hv` using `GlobalTheory.T.padic_norm_zpow_sub_one_padicValInt l j hj (χ g : ℚ_[l]) hg.2 i hi`. Establish `hne : c - 1 ≠ 0`.

Introduce `h`. Establish `h2 : c - 1 = algebraMap ℚ_[l] (PadicComplex l) ((χ g : ℚ_[l]) ^ i - 1)`. Rewrite using `[hc, chiC, Units.val_zpow_eq_zpow_val, map_sub, map_one]`. Rewrite `h` using `[h2, map_eq_zero]`. Rewrite `hv` using `[h, norm_zero]`.

Conclude with `(zpow_pos (Nat.cast_pos.mpr (Fact.out : l.Prime).pos : (0 : ℝ) < l) _).ne hv`. Establish `ha0 : a = 0` using `(mul_eq_zero.mp h0).resolve_left hne`. Rewrite `hax` using `[ha0, hz]`. Conclude with `(mul_eq_zero.mp hax).resolve_left hl0`. Establish `: y = ((l : PadicComplex l) ^ n)⁻¹ * a`.

Rewrite using `[← hax, hz, inv_mul_cancel_left₀ hl0]`. Rewrite using `[this, mem_inC_iff]`. Conclude with `Subfield.mul_mem _ (Subfield.inv_mem _ (Subfield.pow_mem _ (natCast_mem _ l) n)) haK.1`.
-/
theorem invariants_twist : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → ∀ (i : ℤ) (y : PadicComplex l), (∀ g ∈ Gj K j, chiC χ i g * act g y = y) → (i ≠ 0 → y = 0) ∧ (i = 0 → y ∈ inC (Ks K j)) := by
  intro l _ act χ ha hχ K j hj i y hy
  obtain ⟨hnorm, -, hker⟩ := GlobalTheory.T.cyclotomicCharacterPadic_basic_properties l χ hχ
  obtain ⟨⟨g, hg⟩, -⟩ := GlobalTheory.T.exists_cyclotomicTowerLevelGenerator_properties l act χ ha hχ K j hj
  obtain ⟨hdec, hdir, -, hmul, hact, -⟩ := GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ ha hχ K j hj.1
  obtain ⟨n, hn⟩ := exists_scale y
  have hl0 : (l : PadicComplex l) ^ n ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  set z := (l : PadicComplex l) ^ n * y with hz
  have hzinv : ∀ σ ∈ Gj K j, chiC χ i σ * act σ z = z := by
    intro σ hσ
    rw [hz, map_mul, map_pow, map_natCast, mul_left_comm, hy σ hσ]
  have hzO : z ∈ Ohat K := by
    refine (GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act ha K z hn).mp fun h hh => ?_
    have h1 : χ h = 1 := (hker K h (cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified K j (Hinf_le_Gj K j hh))).2.mp hh
    have h2 := hzinv h (Hinf_le_Gj K j hh)
    simpa [chiC, h1] using h2
  obtain ⟨a, haK, x, hx, hax⟩ := hdec z hzO
  set c := chiC χ i g with hc
  have hcK : c ∈ inC (Ks K j) := algebraMap_mem_inC _ _
  have hc1 : ‖c‖ = 1 := by
    rw [hc, chiC, norm_algebraMap', Units.val_zpow_eq_zpow_val, norm_zpow, hnorm, one_zpow]
  have hga : act g a = a := act_fix ha hg.1 haK.1
  have heq : c * (a + act g x) = a + x := by
    have := hzinv g hg.1
    rwa [hax, map_add, hga] at this
  have hX : x - c * act g x ∈ Xj K j :=
    (Xj K j).sub_mem hx (hmul c ⟨hcK, hc1.le⟩ _ (hact g (cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified K j hg.1) x hx))
  have hK : (c - 1) * a ∈ inC (Ks K j) := by
    rw [mem_inC_iff]
    exact Subfield.mul_mem _ (Subfield.sub_mem _ hcK (Subfield.one_mem _)) haK.1
  have h0 : (c - 1) * a = 0 := hdir _ hK _ hX 0 (by linear_combination heq)
  have hrho : 0 < rho1 l :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Fact.out : l.Prime).pos) _
  have hx0 : x = 0 := by
    have h := (GlobalTheory.T.cyclotomic_tower_generator_matrix_perturbation l act χ ha hχ K j hj g hg 1 (fun _ => 1) (by
      intro a b
      rw [Subsingleton.elim a b, Matrix.one_apply_eq]
      refine ⟨?_, by simp⟩
      rw [mem_inC_iff]
      exact Subfield.one_mem _) (by intro a b; simpa using hrho) i).1 (fun _ => x) (fun _ => hx) (by
      funext b
      simp only [twAct, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]
      linear_combination heq - h0)
    exact congrFun h 0
  rw [hx0, add_zero] at hax
  refine ⟨fun hi => ?_, fun _ => ?_⟩
  · have hv := GlobalTheory.T.padic_norm_zpow_sub_one_padicValInt l j hj (χ g : ℚ_[l]) hg.2 i hi
    have hne : c - 1 ≠ 0 := by
      intro h
      have h2 : c - 1 = algebraMap ℚ_[l] (PadicComplex l) ((χ g : ℚ_[l]) ^ i - 1) := by
        rw [hc, chiC, Units.val_zpow_eq_zpow_val, map_sub, map_one]
      rw [h2, map_eq_zero] at h
      rw [h, norm_zero] at hv
      exact (zpow_pos (Nat.cast_pos.mpr (Fact.out : l.Prime).pos : (0 : ℝ) < l) _).ne hv
    have ha0 : a = 0 := (mul_eq_zero.mp h0).resolve_left hne
    rw [ha0, hz] at hax
    exact (mul_eq_zero.mp hax).resolve_left hl0
  · have : y = ((l : PadicComplex l) ^ n)⁻¹ * a := by
      rw [← hax, hz, inv_mul_cancel_left₀ hl0]
    rw [this, mem_inC_iff]
    exact Subfield.mul_mem _ (Subfield.inv_mem _ (Subfield.pow_mem _ (natCast_mem _ l) n)) haK.1

end GlobalTheory.CyclotomicTowerSubgroupInclusions
