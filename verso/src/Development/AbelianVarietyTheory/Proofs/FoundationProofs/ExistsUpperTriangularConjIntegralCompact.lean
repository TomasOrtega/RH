import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.StableLatticeTriangular

/- English proof (translation)
Use `set K : Set F := {x : F | x ∈ E ∧ ‖x‖ ≤ 1} with hKdef`. Use `set L : Set (Fin 2 → F) := {x | ∀ i, x i ∈ K} ∩ {x | ∀ g i, ‖((r g : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i‖ ≤ 1} with hL`. Establish `mkL : ∀ x : Fin 2 → F, (∀ i, x i ∈ E) → (∀ g i, ‖((r g : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i‖ ≤ 1) → x ∈ L`. Introduce `x h1 h2`. Use `⟨fun i => ⟨h1 i, ?_⟩, h2⟩` and prove the remaining obligations.

Simplify using `using h2 1 i`. Establish `hLc : IsCompact L`. Use `(isCompact_pi_infinite (fun _ => hK)).inter_right ?_` and prove the remaining obligations. Simplify using `only [Set.setOf_forall]`. Use `isClosed_iInter fun g => isClosed_iInter fun i => ?_` and prove the remaining obligations.

Use `isClosed_le ?_ continuous_const` and prove the remaining obligations. Simplify using `only [Matrix.mulVec, dotProduct]`. Use `fun_prop`. Establish `hL0c : IsCompact (L ∩ {x | x 1 = 0})` using `hLc.inter_right (isClosed_eq (continuous_apply 1) continuous_const)`. Establish `hs : ∀ j : Fin 2, (Pi.single j c : Fin 2 → F) ∈ L`.

Introduce `j`. Use `mkL _ (fun i => ?_) (fun g i => ?_)` and prove the remaining obligations. Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Conclude with `hcE`.

Conclude with `E.zero_mem`. Rewrite using `[Matrix.mulVec_single]`. Simplify using `using hc g i j`. Establish `hr : ∀ h, ∀ x ∈ L, (r h : Matrix (Fin 2) (Fin 2) F) *ᵥ x ∈ L`. Introduce `h x hx`.

Use `mkL _ (fun i => ?_) (fun g i => ?_)` and prove the remaining obligations. Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `E.sum_mem fun j _ => E.mul_mem (hE h i j) (hx.1 j).1`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]`. Conclude with `hx.2 _ _`.

Establish `hsub : ∀ x ∈ L, ∀ y ∈ L, ∀ t ∈ K, x - t • y ∈ L`. Introduce `x hx y hy t ht`. Use `mkL _ (fun i => ?_) (fun g i => ?_)` and prove the remaining obligations. Conclude with `E.sub_mem (hx.1 i).1 (E.mul_mem ht.1 (hy.1 i).1)`. Rewrite using `[Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx.2 g i) ?_)` and prove the remaining obligations. Rewrite using `[norm_neg, norm_mul]`. Conclude with `mul_le_one₀ ht.2 (norm_nonneg _) (hy.2 g i)`. Take `⟨f1, hf1, hm1⟩` from `hLc.exists_isMaxOn ⟨_, hs 1⟩ (f := fun x : Fin 2 → F => ‖x 1‖) (by fun_prop)`. Take `⟨f0, hf0, hm0⟩` from `hL0c.exists_isMaxOn ⟨Pi.single 0 c, hs 0, by simp⟩ (f := fun x : Fin 2 → F => ‖x 0‖) (by fun_prop)`.

Establish `hcpos : 0 < ‖c‖` using `norm_pos_iff.mpr hc0`. Establish `h1pos : 0 < ‖f1 1‖` using `lt_of_lt_of_le hcpos (by simpa using hm1 (hs 1))`. Establish `h0pos : 0 < ‖f0 0‖` using `lt_of_lt_of_le hcpos (by`. Simplify using `using hm0 (a := Pi.single 0 c) ⟨hs 0, by simp⟩)`. Establish `h1ne : f1 1 ≠ 0` using `norm_pos_iff.mp h1pos`.

Establish `h0ne : f0 0 ≠ 0` using `norm_pos_iff.mp h0pos`. Establish `hf01 : f0 1 = 0` using `hf0.2`. Set `Pm : Matrix (Fin 2) (Fin 2) F` to `!![f0 0, f1 0; 0, f1 1]`. Establish `hdet : Pm.det ≠ 0`. Simplify using `[Pm, Matrix.det_fin_two, h0ne, h1ne]`.

Set `P : GL (Fin 2) F` to `Matrix.GeneralLinearGroup.mkOfDetNeZero Pm hdet`. Establish `hP : (P : Matrix (Fin 2) (Fin 2) F) = Pm` using `rfl`. Establish `key : ∀ x ∈ L, ∃ v : Fin 2 → F, (∀ i, v i ∈ K) ∧ x = Pm *ᵥ v`. Introduce `x hx`. Establish `ht : x 1 / f1 1 ∈ K` using `⟨E.div_mem (hx.1 1).1 (hf1.1 1).1, by`.

Rewrite using `[norm_div, div_le_one h1pos]`. Conclude with `hm1 hx⟩`. Establish `hy` using `hsub x hx f1 hf1 _ ht`. Establish `hy1 : (x - (x 1 / f1 1) • f1) 1 = 0`. Simplify using `[div_mul_cancel₀ _ h1ne]`.

Establish `hs' : (x - (x 1 / f1 1) • f1) 0 / f0 0 ∈ K` using `⟨E.div_mem (hy.1 0).1 (hf0.1.1 0).1, by`. Rewrite using `[norm_div, div_le_one h0pos]`. Conclude with `hm0 ⟨hy, hy1⟩⟩`. Use `⟨![(x - (x 1 / f1 1) • f1) 0 / f0 0, x 1 / f1 1], ?_, ?_⟩` and prove the remaining obligations. Introduce `i`.

Use `fin_cases i`. Conclude with `hs'`. Conclude with `ht`. Use extensionality with `i`. Use `fin_cases i`.

Simplify using `[Pm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `[Pm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]`. Clear the denominators using the available nonvanishing facts.

Use `⟨P⁻¹, ?_, fun g i j => ?_⟩` and prove the remaining obligations. Establish `h : (Pm * ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) 1 0 = 0`. Rewrite using `[← hP, ← Units.val_mul, mul_inv_cancel]`. Simplify using the standard rewrite rules. Rewrite `h` using `[Matrix.mul_apply, Fin.sum_univ_two]`.

Establish `e0 : Pm 1 0 = 0` using `rfl`. Establish `e1 : Pm 1 1 = f1 1` using `rfl`. Rewrite `h` using `[e0, e1, zero_mul, zero_add]`. Conclude with `(mul_eq_zero.mp h).resolve_left h1ne`. Establish `hcol : (fun k => Pm k j) ∈ L` using `by fin_cases j`.

Use `hf0.1 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `k`. Use `fin_cases k`. Both sides reduce to the same expression. Conclude with `hf01.symm`.

Use `hf1 using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `ext k; fin_cases k <;> rfl`. Take `⟨v, hv, hxv⟩` from `key _ (hr g _ hcol)`. Establish `: ((P⁻¹ * r g * P⁻¹⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j = v i`. Establish `h2 : ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ (Pm *ᵥ v) = v`.

Rewrite using `[Matrix.mulVec_mulVec, ← hP, ← Units.val_mul, inv_mul_cancel]`. Simplify using the standard rewrite rules. Rewrite `h2` using `[← hxv, Matrix.mulVec_mulVec]`. Rewrite using `[inv_inv, Units.val_mul, Units.val_mul, hP, ← h2]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Conclude with `hv i`.
-/
theorem exists_conj_of_bounded {F : Type} [NormedField F] [IsUltrametricDist F] {Γ : Type} [Group Γ]
    (E : Subfield F) (hK : IsCompact {x : F | x ∈ E ∧ ‖x‖ ≤ 1})
    (r : Γ →* GL (Fin 2) F) (hE : ∀ g i j, (r g : Matrix (Fin 2) (Fin 2) F) i j ∈ E)
    (c : F) (hcE : c ∈ E) (hc0 : c ≠ 0)
    (hc : ∀ g i j, ‖(r g : Matrix (Fin 2) (Fin 2) F) i j * c‖ ≤ 1) :
    ∃ B : GL (Fin 2) F, (B : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧ ∀ g i j,
      ((B * r g * B⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ E ∧
      ‖((B * r g * B⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j‖ ≤ 1 := by
  classical
  set K : Set F := {x : F | x ∈ E ∧ ‖x‖ ≤ 1} with hKdef
  set L : Set (Fin 2 → F) := {x | ∀ i, x i ∈ K} ∩
    {x | ∀ g i, ‖((r g : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i‖ ≤ 1} with hL
  have mkL : ∀ x : Fin 2 → F, (∀ i, x i ∈ E) →
      (∀ g i, ‖((r g : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i‖ ≤ 1) → x ∈ L := by
    intro x h1 h2
    refine ⟨fun i => ⟨h1 i, ?_⟩, h2⟩
    simpa using h2 1 i
  have hLc : IsCompact L := by
    refine (isCompact_pi_infinite (fun _ => hK)).inter_right ?_
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun g => isClosed_iInter fun i => ?_
    refine isClosed_le ?_ continuous_const
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hL0c : IsCompact (L ∩ {x | x 1 = 0}) :=
    hLc.inter_right (isClosed_eq (continuous_apply 1) continuous_const)
  have hs : ∀ j : Fin 2, (Pi.single j c : Fin 2 → F) ∈ L := by
    intro j
    refine mkL _ (fun i => ?_) (fun g i => ?_)
    · rw [Pi.single_apply]; split_ifs
      · exact hcE
      · exact E.zero_mem
    · rw [Matrix.mulVec_single]; simpa using hc g i j
  have hr : ∀ h, ∀ x ∈ L, (r h : Matrix (Fin 2) (Fin 2) F) *ᵥ x ∈ L := by
    intro h x hx
    refine mkL _ (fun i => ?_) (fun g i => ?_)
    · simp only [Matrix.mulVec, dotProduct]
      exact E.sum_mem fun j _ => E.mul_mem (hE h i j) (hx.1 j).1
    · rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
      exact hx.2 _ _
  have hsub : ∀ x ∈ L, ∀ y ∈ L, ∀ t ∈ K, x - t • y ∈ L := by
    intro x hx y hy t ht
    refine mkL _ (fun i => ?_) (fun g i => ?_)
    · exact E.sub_mem (hx.1 i).1 (E.mul_mem ht.1 (hy.1 i).1)
    · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx.2 g i) ?_)
      rw [norm_neg, norm_mul]
      exact mul_le_one₀ ht.2 (norm_nonneg _) (hy.2 g i)
  obtain ⟨f1, hf1, hm1⟩ := hLc.exists_isMaxOn ⟨_, hs 1⟩
    (f := fun x : Fin 2 → F => ‖x 1‖) (by fun_prop)
  obtain ⟨f0, hf0, hm0⟩ := hL0c.exists_isMaxOn ⟨Pi.single 0 c, hs 0, by simp⟩
    (f := fun x : Fin 2 → F => ‖x 0‖) (by fun_prop)
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  have h1pos : 0 < ‖f1 1‖ := lt_of_lt_of_le hcpos (by simpa using hm1 (hs 1))
  have h0pos : 0 < ‖f0 0‖ := lt_of_lt_of_le hcpos (by
    simpa using hm0 (a := Pi.single 0 c) ⟨hs 0, by simp⟩)
  have h1ne : f1 1 ≠ 0 := norm_pos_iff.mp h1pos
  have h0ne : f0 0 ≠ 0 := norm_pos_iff.mp h0pos
  have hf01 : f0 1 = 0 := hf0.2
  let Pm : Matrix (Fin 2) (Fin 2) F := !![f0 0, f1 0; 0, f1 1]
  have hdet : Pm.det ≠ 0 := by
    simp [Pm, Matrix.det_fin_two, h0ne, h1ne]
  let P : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero Pm hdet
  have hP : (P : Matrix (Fin 2) (Fin 2) F) = Pm := rfl
  have key : ∀ x ∈ L, ∃ v : Fin 2 → F, (∀ i, v i ∈ K) ∧ x = Pm *ᵥ v := by
    intro x hx
    have ht : x 1 / f1 1 ∈ K := ⟨E.div_mem (hx.1 1).1 (hf1.1 1).1, by
      rw [norm_div, div_le_one h1pos]; exact hm1 hx⟩
    have hy := hsub x hx f1 hf1 _ ht
    have hy1 : (x - (x 1 / f1 1) • f1) 1 = 0 := by
      simp [div_mul_cancel₀ _ h1ne]
    have hs' : (x - (x 1 / f1 1) • f1) 0 / f0 0 ∈ K :=
      ⟨E.div_mem (hy.1 0).1 (hf0.1.1 0).1, by
        rw [norm_div, div_le_one h0pos]; exact hm0 ⟨hy, hy1⟩⟩
    refine ⟨![(x - (x 1 / f1 1) • f1) 0 / f0 0, x 1 / f1 1], ?_, ?_⟩
    · intro i; fin_cases i
      · exact hs'
      · exact ht
    · ext i; fin_cases i
      · simp [Pm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        field_simp
        ring
      · simp [Pm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        field_simp
  refine ⟨P⁻¹, ?_, fun g i j => ?_⟩
  · have h : (Pm * ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) 1 0 = 0 := by
      rw [← hP, ← Units.val_mul, mul_inv_cancel]; simp
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h
    have e0 : Pm 1 0 = 0 := rfl
    have e1 : Pm 1 1 = f1 1 := rfl
    rw [e0, e1, zero_mul, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_left h1ne
  · have hcol : (fun k => Pm k j) ∈ L := by
      fin_cases j
      · convert hf0.1 using 1
        ext k; fin_cases k
        · rfl
        · exact hf01.symm
      · convert hf1 using 1
        ext k; fin_cases k <;> rfl
    obtain ⟨v, hv, hxv⟩ := key _ (hr g _ hcol)
    have : ((P⁻¹ * r g * P⁻¹⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j = v i := by
      have h2 : ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ (Pm *ᵥ v) = v := by
        rw [Matrix.mulVec_mulVec, ← hP, ← Units.val_mul, inv_mul_cancel]; simp
      rw [← hxv, Matrix.mulVec_mulVec] at h2
      rw [inv_inv, Units.val_mul, Units.val_mul, hP, ← h2]
      rfl
    rw [this]
    exact hv i

/- English proof (translation)
Introduce `l _ Γ _ _ _ E r hfin hcont hE`. Establish `hK : IsCompact {x : Qbar l | x ∈ E.toSubfield ∧ ‖x‖ ≤ 1}`. Set `V : Submodule ℚ_[l] (Qbar l)` to `E.toSubalgebra.toSubmodule`. Use `haveI : FiniteDimensional ℚ_[l] V := hfin`. Use `haveI : ProperSpace V := FiniteDimensional.proper ℚ_[l] V`.

Establish `h` using `(isCompact_closedBall (0 : V) 1).image continuous_subtype_val`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨⟨x, h1⟩, by simpa using h2, rfl⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨y.2, by simpa using hy⟩`. Establish `hf : Continuous fun g : Γ => fun p : Fin 2 × Fin 2 => (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) p.1 p.2`. Use `continuous_pi fun p => ?_` and prove the remaining obligations.

Conclude with `(Units.continuous_val.comp hcont).matrix_elem p.1 p.2`. Take `⟨C, hC⟩` from `(isCompact_range hf).isBounded.exists_pos_norm_le`. Take `⟨c, hc0, hc⟩` from `NormedField.exists_norm_lt ℚ_[l] (inv_pos.mpr hC.1)`. Establish `hn : ‖algebraMap ℚ_[l] (Qbar l) c‖ = ‖c‖` using `norm_algebraMap' _ _`. Use `exists_conj_of_bounded E.toSubfield hK r hE (algebraMap ℚ_[l] (Qbar l) c) (E.algebraMap_mem c) (norm_pos_iff.mp (hn ▸ hc0)) (fun g i j => ?_)` and prove the remaining obligations.

Rewrite using `[norm_mul, hn]`. Establish `h1 : ‖(r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j‖ ≤ C` using `(norm_le_pi_norm (fun p : Fin 2 × Fin 2 => (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) p.1 p.2) (i, j)).trans (hC.2 _ ⟨g, rfl⟩)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_upperTriangular_conj_integral :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (E : IntermediateField ℚ_[l] (Qbar l)) (r : Γ →* GL (Fin 2) (Qbar l)), FiniteDimensional ℚ_[l] E → Continuous r → (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ E) → ∃ B : GL (Fin 2) (Qbar l), (B : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0 ∧ ∀ g i j, ((B * r g * B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ E ∧ ‖((B * r g * B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) i j‖ ≤ 1 := by
  intro l _ Γ _ _ _ E r hfin hcont hE
  have hK : IsCompact {x : Qbar l | x ∈ E.toSubfield ∧ ‖x‖ ≤ 1} := by
    let V : Submodule ℚ_[l] (Qbar l) := E.toSubalgebra.toSubmodule
    haveI : FiniteDimensional ℚ_[l] V := hfin
    haveI : ProperSpace V := FiniteDimensional.proper ℚ_[l] V
    have h := (isCompact_closedBall (0 : V) 1).image continuous_subtype_val
    convert h using 1
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h1⟩, by simpa using h2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by simpa using hy⟩
  have hf : Continuous fun g : Γ => fun p : Fin 2 × Fin 2 =>
      (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) p.1 p.2 := by
    refine continuous_pi fun p => ?_
    exact (Units.continuous_val.comp hcont).matrix_elem p.1 p.2
  obtain ⟨C, hC⟩ := (isCompact_range hf).isBounded.exists_pos_norm_le
  obtain ⟨c, hc0, hc⟩ := NormedField.exists_norm_lt ℚ_[l] (inv_pos.mpr hC.1)
  have hn : ‖algebraMap ℚ_[l] (Qbar l) c‖ = ‖c‖ := norm_algebraMap' _ _
  refine exists_conj_of_bounded E.toSubfield hK r hE (algebraMap ℚ_[l] (Qbar l) c)
    (E.algebraMap_mem c) (norm_pos_iff.mp (hn ▸ hc0)) (fun g i j => ?_)
  rw [norm_mul, hn]
  have h1 : ‖(r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j‖ ≤ C :=
    (norm_le_pi_norm (fun p : Fin 2 × Fin 2 =>
      (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) p.1 p.2) (i, j)).trans (hC.2 _ ⟨g, rfl⟩)
  calc _ ≤ C * C⁻¹ := mul_le_mul h1 hc.le (norm_nonneg _) hC.1.le
    _ = 1 := mul_inv_cancel₀ hC.1.ne'

end GlobalTheory.StableLatticeTriangular
