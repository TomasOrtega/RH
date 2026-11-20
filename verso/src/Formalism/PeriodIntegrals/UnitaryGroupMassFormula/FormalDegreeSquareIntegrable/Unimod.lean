import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeSquareIntegrable.FormalDegreeFromOrthogonality

noncomputable section

namespace PIW.HCFdeg

open MeasureTheory PI.UpqRep Matrix
open scoped MatrixOrder NNReal ENNReal ComplexOrder Pointwise

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Take `⟨V, hVc, hV1⟩` from `exists_compact_mem_nhds (1 : G)`. Use `set E : Set G := V * (K : Set G) with hE`. Establish `hEc : IsCompact E` using `hVc.mul hK`. Establish `hVE : V ⊆ E` using `fun v hv => ⟨v, hv, 1, K.one_mem, mul_one v⟩`. Establish `hEn : E ∈ nhds (1 : G)` using `Filter.mem_of_superset hV1 hVE`.

Establish `hpos : 0 < μ E` using `Measure.measure_pos_of_mem_nhds μ hEn`. Establish `hfin : μ E ≠ ⊤` using `hEc.measure_lt_top.ne`. Establish `hpre : (fun x => x * k) ⁻¹' E = E`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, hE, Set.mem_mul]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, c, hc, hvc⟩`. Use `⟨v, hv, c * k⁻¹, K.mul_mem hc (K.inv_mem hk), ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, hvc, mul_inv_cancel_right]`. Introduce and unpack `⟨v, hv, c, hc, rfl⟩`.

Conclude with `⟨v, hv, c * k, K.mul_mem hc hk, (mul_assoc _ _ _).symm⟩`. Establish `h` using `Measure.map_right_mul_eq_modularCharacterFun_smul μ k`. Establish `h2` using `congrArg (fun ν : Measure G => ν E) h`. Rewrite `h2` using `[Measure.map_apply (measurable_mul_const k) hEc.isClosed.measurableSet, hpre, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]`. Establish `h3 : ((Measure.modularCharacterFun k : ℝ≥0) : ℝ≥0∞) * μ E = 1 * μ E`.

Rewrite using `[one_mul]`. Conclude with `h2.symm`. Establish `h4` using `(ENNReal.mul_left_inj hpos.ne' hfin).1 h3`. Conclude with `h4` after adjusting the coercions.
-/
lemma modChar_eq_one_of_compact (μ : Measure G) [μ.IsHaarMeasure] [μ.InnerRegular]
    (K : Subgroup G) (hK : IsCompact (K : Set G)) (k : G) (hk : k ∈ K) :
    Measure.modularCharacter k = 1 := by
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : G)
  set E : Set G := V * (K : Set G) with hE
  have hEc : IsCompact E := hVc.mul hK
  have hVE : V ⊆ E := fun v hv => ⟨v, hv, 1, K.one_mem, mul_one v⟩
  have hEn : E ∈ nhds (1 : G) := Filter.mem_of_superset hV1 hVE
  have hpos : 0 < μ E := Measure.measure_pos_of_mem_nhds μ hEn
  have hfin : μ E ≠ ⊤ := hEc.measure_lt_top.ne
  have hpre : (fun x => x * k) ⁻¹' E = E := by
    ext x
    simp only [Set.mem_preimage, hE, Set.mem_mul]
    constructor
    · rintro ⟨v, hv, c, hc, hvc⟩
      refine ⟨v, hv, c * k⁻¹, K.mul_mem hc (K.inv_mem hk), ?_⟩
      rw [← mul_assoc, hvc, mul_inv_cancel_right]
    · rintro ⟨v, hv, c, hc, rfl⟩
      exact ⟨v, hv, c * k, K.mul_mem hc hk, (mul_assoc _ _ _).symm⟩
  have h := Measure.map_right_mul_eq_modularCharacterFun_smul μ k
  have h2 := congrArg (fun ν : Measure G => ν E) h
  rw [Measure.map_apply (measurable_mul_const k) hEc.isClosed.measurableSet, hpre,
    Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  have h3 : ((Measure.modularCharacterFun k : ℝ≥0) : ℝ≥0∞) * μ E = 1 * μ E := by
    rw [one_mul]; exact h2.symm
  have h4 := (ENNReal.mul_left_inj hpos.ne' hfin).1 h3
  exact_mod_cast h4

/- English proof (translation)
Establish `hR : μ.IsMulRightInvariant` using `⟨fun g => by`. Rewrite using `[Measure.map_right_mul_eq_modularCharacterFun_smul μ g]`. Establish `: Measure.modularCharacterFun g = 1` using `h g`. Rewrite using `[this, one_smul]⟩`. Use `⟨hR, ⟨?_⟩⟩` and prove the remaining obligations.

Set `c : ℝ≥0∞` to `Measure.haarScalarFactor μ.inv μ`. Establish `hc : μ.inv = c • μ` using `Measure.isMulLeftInvariant_eq_smul_of_innerRegular μ.inv μ`. Establish `h1 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ`. Rewrite using `[← Measure.inv_def μ, hc, Measure.map_smul, ← Measure.inv_def μ, hc, smul_smul, pow_two]`. Establish `μeq : μ = c ^ 2 • μ`.

Rewrite `h1` using `[Measure.map_map continuous_inv.measurable continuous_inv.measurable]`. Simplify `h1` using `only [inv_involutive, Function.Involutive.comp_self, Measure.map_id]`. Establish `K : TopologicalSpace.PositiveCompacts G` using `Classical.arbitrary _`. Establish `h2 : c ^ 2 * μ K = 1 ^ 2 * μ K` using `by conv_rhs => rw [μeq]`. Simplify using the standard rewrite rules.

Establish `h3 : c ^ 2 = 1 ^ 2` using `(ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne' K.isCompact.measure_lt_top.ne).1 h2`. Establish `h4 : c = 1` using `(ENNReal.pow_right_strictMono two_ne_zero).injective h3`. Rewrite using `[hc, h4, one_smul]`.
-/
lemma unimod_of_modChar (μ : Measure G) [μ.IsHaarMeasure] [μ.InnerRegular]
    (h : ∀ g : G, Measure.modularCharacter g = 1) :
    μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by
  have hR : μ.IsMulRightInvariant :=
    ⟨fun g => by
      rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g]
      have : Measure.modularCharacterFun g = 1 := h g
      rw [this, one_smul]⟩
  refine ⟨hR, ⟨?_⟩⟩
  let c : ℝ≥0∞ := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul_of_innerRegular μ.inv μ
  have h1 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul, ← Measure.inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h1
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h1
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h2 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have h3 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 h2
  have h4 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h3
  rw [hc, h4, one_smul]

end Abstract

section Matrices

variable {n : ℕ} (ε : Fin n → Bool)

def mkU (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) : UJ ε :=
  ⟨⟨g, Jm ε * gᴴ * Jm ε, mul_eq_one_comm.mp (coeMatrix_left_inv ε g hg), coeMatrix_left_inv ε g hg⟩, hg⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma toM_mkU (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) : toM (mkU ε g hg) = g := rfl

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext h)`.
-/
lemma ext_toM {a b : UJ ε} (h : toM a = toM b) : a = b := Subtype.ext (Units.ext h)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma toM_mul (a b : UJ ε) : toM (a * b) = toM a * toM b := rfl

/- English proof (translation)
Use `show (((a : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = _`. Conclude with `Units.inv_eq_of_mul_eq_one_left (coeMatrix_left_inv ε _ a.2)`.
-/
lemma toM_inv (a : UJ ε) : toM a⁻¹ = Jm ε * (toM a)ᴴ * Jm ε := by
  show (((a : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = _
  exact Units.inv_eq_of_mul_eq_one_left (coeMatrix_left_inv ε _ a.2)

/- English proof (translation)
Unfold `Jm`. Rewrite using `[diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `by_cases h : ε a = true <;> simp [h]`.
-/
private lemma Jm_mul_self_eq_one' : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

/- English proof (translation)
Unfold `inUJ Jm`. Rewrite using `[diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `by_cases h : ε a = true <;> simp [h]`.
-/
lemma inUJ_J : inUJ ε (Jm ε) := by
  unfold inUJ Jm
  rw [diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

/- English proof (translation)
Establish `h1 : g * (Jm ε * gᴴ * Jm ε) = 1` using `mul_eq_one_comm.mp (coeMatrix_left_inv ε g hg)`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma inUJ_mul_J_conj {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : g * Jm ε * gᴴ = Jm ε := by
  have h1 : g * (Jm ε * gᴴ * Jm ε) = 1 := mul_eq_one_comm.mp (coeMatrix_left_inv ε g hg)
  calc g * Jm ε * gᴴ = g * Jm ε * gᴴ * (Jm ε * Jm ε) := by rw [Jm_mul_self_eq_one', Matrix.mul_one]
    _ = (g * (Jm ε * gᴴ * Jm ε)) * Jm ε := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [h1, Matrix.one_mul]

/- English proof (translation)
Use `set j := mkU ε (Jm ε) (inUJ_J ε) with hj`. Establish `hjj : j * j = 1` using `ext_toM ε (by show Jm ε * Jm ε = 1`. Conclude with `Jm_mul_self ε)`. Establish `hinv : h⁻¹ = j * h * j` using `ext_toM ε (by`. Rewrite using `[toM_inv, hh]`.

Use the proof step `rfl)`. Use `set D : UJ ε →* ℝ≥0 := Measure.modularCharacter with hD`. Establish `e1 : D j * D j = 1` using `by rw [← map_mul, hjj, map_one]`. Establish `e0 : D h * D h⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel, map_one]`. Rewrite `e0` using `[hinv, map_mul, map_mul]`.

Establish `e2 : D h * D h = 1`. Rewrite using `[← e0, show D h * (D j * D h * D j) = D h * D h * (D j * D j) by ring, e1, mul_one]`. Establish `e3 : ((D h : ℝ)) * (D h : ℝ) = 1` using `by exact_mod_cast e2`. Break down `mul_self_eq_one_iff.mp e3 with e4 | e4` into its components or cases. Conclude with `e4` after adjusting the coercions.

Use `(D h).2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma modChar_herm (h : UJ ε) (hh : (toM h)ᴴ = toM h) : Measure.modularCharacter h = 1 := by
  set j := mkU ε (Jm ε) (inUJ_J ε) with hj
  have hjj : j * j = 1 := ext_toM ε (by
    show Jm ε * Jm ε = 1
    exact Jm_mul_self ε)
  have hinv : h⁻¹ = j * h * j := ext_toM ε (by
    rw [toM_inv, hh]
    rfl)
  set D : UJ ε →* ℝ≥0 := Measure.modularCharacter with hD
  have e1 : D j * D j = 1 := by rw [← map_mul, hjj, map_one]
  have e0 : D h * D h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [hinv, map_mul, map_mul] at e0
  have e2 : D h * D h = 1 := by
    rw [← e0, show D h * (D j * D h * D j) = D h * D h * (D j * D j) by ring, e1, mul_one]
  have e3 : ((D h : ℝ)) * (D h : ℝ) = 1 := by exact_mod_cast e2
  rcases mul_self_eq_one_iff.mp e3 with e4 | e4
  · exact_mod_cast e4
  · have := (D h).2
    linarith

/- English proof (translation)
Unfold `Kset`. Establish `hK : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) 1)` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1`. Use `hK.of_isClosed_subset ?_ ?_` and prove the remaining obligations. Use `IsClosed.inter (s₁ := {g : Matrix (Fin n) (Fin n) ℂ | g ∈ unitaryGroup (Fin n) ℂ}) (s₂ := {g : Matrix (Fin n) (Fin n) ℂ | g * Jm ε = Jm ε * g}) ?_ ?_` and prove the remaining obligations. Establish `e : {g : Matrix (Fin n) (Fin n) ℂ | g ∈ unitaryGroup (Fin n) ℂ} = {g | g * star g = 1}` using `Set.ext fun g => mem_unitaryGroup_iff`.

Rewrite using `[e]`. Conclude with `isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose) continuous_const`. Conclude with `isClosed_eq (continuous_id.matrix_mul continuous_const) (continuous_const.matrix_mul continuous_id)`. Introduce and unpack `(g : Matrix (Fin n) (Fin n) ℂ) ⟨hg, -⟩`. Use `Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j => ?_` and prove the remaining obligations.

Rewrite using `[Metric.mem_closedBall, dist_zero_right]`. Establish `hu : g * gᴴ = 1` using `mem_unitaryGroup_iff.mp hg`. Establish `h` using `congrFun (congrFun hu i) i`. Rewrite `h` using `[Matrix.mul_apply]`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h`.

Establish `h2 : ∑ k, ‖g i k‖ ^ 2 = 1`. Establish `h4 : ∑ k, g i k * star (g i k) = ∑ k, ((‖g i k‖ ^ 2 : ℝ) : ℂ)`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Rewrite `h` using `[h4, ← Complex.ofReal_sum]`.

Conclude with `h` after adjusting the coercions. Establish `h3 : ‖g i j‖ ^ 2 ≤ 1` using `h2 ▸ Finset.single_le_sum (fun k _ => sq_nonneg ‖g i k‖) (Finset.mem_univ j)`. Use polynomial arithmetic with `[norm_nonneg (g i j)]`.
-/
lemma isCompact_Kset : IsCompact (Kset ε) := by
  unfold Kset
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hK.of_isClosed_subset ?_ ?_
  · refine IsClosed.inter (s₁ := {g : Matrix (Fin n) (Fin n) ℂ | g ∈ unitaryGroup (Fin n) ℂ})
      (s₂ := {g : Matrix (Fin n) (Fin n) ℂ | g * Jm ε = Jm ε * g}) ?_ ?_
    · have e : {g : Matrix (Fin n) (Fin n) ℂ | g ∈ unitaryGroup (Fin n) ℂ} = {g | g * star g = 1} :=
        Set.ext fun g => mem_unitaryGroup_iff
      rw [e]
      exact isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose) continuous_const
    · exact isClosed_eq (continuous_id.matrix_mul continuous_const) (continuous_const.matrix_mul continuous_id)
  · rintro (g : Matrix (Fin n) (Fin n) ℂ) ⟨hg, -⟩
    refine Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    have hu : g * gᴴ = 1 := mem_unitaryGroup_iff.mp hg
    have h := congrFun (congrFun hu i) i
    rw [Matrix.mul_apply] at h
    simp only [Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
    have h2 : ∑ k, ‖g i k‖ ^ 2 = 1 := by
      have h4 : ∑ k, g i k * star (g i k) = ∑ k, ((‖g i k‖ ^ 2 : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [h4, ← Complex.ofReal_sum] at h
      exact_mod_cast h
    have h3 : ‖g i j‖ ^ 2 ≤ 1 := h2 ▸ Finset.single_le_sum (fun k _ => sq_nonneg ‖g i k‖) (Finset.mem_univ j)
    nlinarith [norm_nonneg (g i j)]

/- English proof (translation)
The claim follows from `(isClosedEmbeddingMatrix n ε).1.isCompact_preimage (isCompact_Kset ε)`.
-/
lemma isCompact_KG : IsCompact ((KG ε : Set (UJ ε))) :=
  (isClosedEmbeddingMatrix n ε).1.isCompact_preimage (isCompact_Kset ε)

/- English proof (translation)
Use `set G := toM g with hG`. Use `set P := Gᴴ * G with hPdef`. Establish `hP : 0 ≤ P` using `(posSemidef_conjTranspose_mul_self G).nonneg`. Use `set s := CFC.sqrt P with hsdef`. Establish `hs0 : 0 ≤ s` using `CFC.sqrt_nonneg P`.

Establish `hss : s * s = P` using `CFC.sqrt_mul_sqrt_self P hP`. Establish `hsH : sᴴ = s` using `hs0.posSemidef.isHermitian.eq`. Establish `hJ` using `Jm_mul_self ε`. Establish `hJH` using `Jm_conjTranspose ε`. Establish `hPJP : P * Jm ε * P = Jm ε`.

Use `inUJ_mul_J_conj ε g.2` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Establish `hPi : P⁻¹ = Jm ε * P * Jm ε`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.

Use `set w := Jm ε * s * Jm ε with hw`. Establish `hw0 : 0 ≤ w`. Use `hs0.posSemidef.conjTranspose_mul_mul_same (Jm ε)` as an intermediate fact. Rewrite `this` using `[hJH]`. Conclude with `this.nonneg`.

Establish `hJPJ0 : 0 ≤ Jm ε * P * Jm ε`. Use `hP.posSemidef.conjTranspose_mul_mul_same (Jm ε)` as an intermediate fact. Rewrite `this` using `[hJH]`. Conclude with `this.nonneg`. Establish `hww : w * w = Jm ε * P * Jm ε`.

Combine the equalities or inequalities in the displayed calculation. Establish `hsq : CFC.sqrt (Jm ε * P * Jm ε) = w` using `(CFC.sqrt_eq_iff _ _ hJPJ0 hw0).2 hww`. Establish `hsinv : s⁻¹ = w`. Rewrite using `[hsdef, hP.posSemidef.inv_sqrt, hPi, hsq]`. Establish `hdetP : IsUnit P.det` using `Matrix.isUnit_det_of_right_inverse (B := Jm ε * P * Jm ε) (by`.

Combine the equalities or inequalities in the displayed calculation. Establish `hdets : IsUnit s.det`. Rewrite `hdetP` using `[← hss, Matrix.det_mul]`. Conclude with `isUnit_of_mul_isUnit_left hdetP`. Establish `hsw : s * w = 1` using `by rw [← hsinv]; exact Matrix.mul_nonsing_inv s hdets`.

Establish `hsJs : s * Jm ε * s = Jm ε`. Combine the equalities or inequalities in the displayed calculation. Establish `hws : w * s = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `hsU : inUJ ε s` using `by unfold inUJ; rw [hsH]; exact hsJs`.

Use `⟨mkU ε s hsU, hsH, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_KG]`. Use `set M := toM (g * (mkU ε s hsU)⁻¹) with hM`. Establish `hMw : M = G * w`. Rewrite using `[hM, toM_mul, toM_inv, toM_mkU, hsH]`.

Establish `hMU : Mᴴ * M = 1`. Establish `hwH : wᴴ = w` using `hw0.posSemidef.isHermitian.eq`. Rewrite using `[hMw, Matrix.conjTranspose_mul, hwH]`. Combine the equalities or inequalities in the displayed calculation. Establish `hMJ : Mᴴ * Jm ε * M = Jm ε` using `(g * (mkU ε s hsU)⁻¹).2`.

Use `⟨Matrix.mem_unitaryGroup_iff'.mpr (by rw [Matrix.star_eq_conjTranspose]; exact hMU), ?_⟩` and prove the remaining obligations. Establish `hMM : M * Mᴴ = 1` using `mul_eq_one_comm.mp hMU`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma polar (g : UJ ε) : ∃ s : UJ ε, (toM s)ᴴ = toM s ∧ g * s⁻¹ ∈ KG ε := by
  set G := toM g with hG
  set P := Gᴴ * G with hPdef
  have hP : 0 ≤ P := (posSemidef_conjTranspose_mul_self G).nonneg
  set s := CFC.sqrt P with hsdef
  have hs0 : 0 ≤ s := CFC.sqrt_nonneg P
  have hss : s * s = P := CFC.sqrt_mul_sqrt_self P hP
  have hsH : sᴴ = s := hs0.posSemidef.isHermitian.eq
  have hJ := Jm_mul_self ε
  have hJH := Jm_conjTranspose ε
  have hPJP : P * Jm ε * P = Jm ε := by
    have := inUJ_mul_J_conj ε g.2
    calc P * Jm ε * P = Gᴴ * (G * Jm ε * Gᴴ) * G := by simp only [hPdef, Matrix.mul_assoc]
      _ = Jm ε := by rw [this]; exact g.2
  have hPi : P⁻¹ = Jm ε * P * Jm ε := by
    apply Matrix.inv_eq_left_inv
    calc Jm ε * P * Jm ε * P = Jm ε * (P * Jm ε * P) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPJP, hJ]
  set w := Jm ε * s * Jm ε with hw
  have hw0 : 0 ≤ w := by
    have := hs0.posSemidef.conjTranspose_mul_mul_same (Jm ε)
    rw [hJH] at this
    exact this.nonneg
  have hJPJ0 : 0 ≤ Jm ε * P * Jm ε := by
    have := hP.posSemidef.conjTranspose_mul_mul_same (Jm ε)
    rw [hJH] at this
    exact this.nonneg
  have hww : w * w = Jm ε * P * Jm ε := by
    calc w * w = Jm ε * s * (Jm ε * Jm ε) * s * Jm ε := by simp only [hw, Matrix.mul_assoc]
      _ = Jm ε * P * Jm ε := by rw [hJ, Matrix.mul_one, ← hss]; simp only [Matrix.mul_assoc]
  have hsq : CFC.sqrt (Jm ε * P * Jm ε) = w := (CFC.sqrt_eq_iff _ _ hJPJ0 hw0).2 hww
  have hsinv : s⁻¹ = w := by
    rw [hsdef, hP.posSemidef.inv_sqrt, hPi, hsq]
  have hdetP : IsUnit P.det := Matrix.isUnit_det_of_right_inverse (B := Jm ε * P * Jm ε) (by
    calc P * (Jm ε * P * Jm ε) = (P * Jm ε * P) * Jm ε := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPJP, hJ])
  have hdets : IsUnit s.det := by
    rw [← hss, Matrix.det_mul] at hdetP
    exact isUnit_of_mul_isUnit_left hdetP
  have hsw : s * w = 1 := by rw [← hsinv]; exact Matrix.mul_nonsing_inv s hdets
  have hsJs : s * Jm ε * s = Jm ε := by
    calc s * Jm ε * s = (s * w) * Jm ε := by simp only [hw, Matrix.mul_assoc, hJ, Matrix.mul_one]
      _ = Jm ε := by rw [hsw, Matrix.one_mul]
  have hws : w * s = 1 := by
    calc w * s = Jm ε * (s * Jm ε * s) := by simp only [hw, Matrix.mul_assoc]
      _ = 1 := by rw [hsJs, hJ]
  have hsU : inUJ ε s := by unfold inUJ; rw [hsH]; exact hsJs
  refine ⟨mkU ε s hsU, hsH, ?_⟩
  rw [mem_KG]
  set M := toM (g * (mkU ε s hsU)⁻¹) with hM
  have hMw : M = G * w := by
    rw [hM, toM_mul, toM_inv, toM_mkU, hsH]
  have hMU : Mᴴ * M = 1 := by
    have hwH : wᴴ = w := hw0.posSemidef.isHermitian.eq
    rw [hMw, Matrix.conjTranspose_mul, hwH]
    calc w * Gᴴ * (G * w) = w * (s * s) * w := by rw [hss]; simp only [hPdef, Matrix.mul_assoc]
      _ = (w * s) * (s * w) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hws, hsw, Matrix.mul_one]
  have hMJ : Mᴴ * Jm ε * M = Jm ε := (g * (mkU ε s hsU)⁻¹).2
  refine ⟨Matrix.mem_unitaryGroup_iff'.mpr (by rw [Matrix.star_eq_conjTranspose]; exact hMU), ?_⟩
  have hMM : M * Mᴴ = 1 := mul_eq_one_comm.mp hMU
  calc M * Jm ε = M * (Mᴴ * Jm ε * M) := by rw [hMJ]
    _ = (M * Mᴴ) * Jm ε * M := by simp only [Matrix.mul_assoc]
    _ = Jm ε * M := by rw [hMM, Matrix.one_mul]

/- English proof (translation)
Take `⟨s, hs, hk⟩` from `polar ε g`. Establish `h1` using `modChar_eq_one_of_compact (muG ε) (KG ε) (isCompact_KG ε) _ hk`. Establish `h2` using `modChar_herm ε s hs`. Establish `e : g = (g * s⁻¹) * s` using `by group`. Rewrite using `[e, map_mul, h1, h2, mul_one]`.
-/
theorem modChar_UJ [T2Space (UJ ε)] (g : UJ ε) : Measure.modularCharacter g = 1 := by
  obtain ⟨s, hs, hk⟩ := polar ε g
  have h1 := modChar_eq_one_of_compact (muG ε) (KG ε) (isCompact_KG ε) _ hk
  have h2 := modChar_herm ε s hs
  have e : g = (g * s⁻¹) * s := by group
  rw [e, map_mul, h1, h2, mul_one]

end Matrices

/- English proof (translation)
Unfold `StUnimod`. Introduce `n ε`. Conclude with `unimod_of_modChar (muG ε) (fun g => modChar_UJ ε g)`.
-/
theorem stUnimod : StUnimod := by
  unfold StUnimod
  intro n ε
  exact unimod_of_modChar (muG ε) (fun g => modChar_UJ ε g)

end PIW.HCFdeg
