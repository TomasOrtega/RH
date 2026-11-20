import Formalism.LocalRingCardinality.DataCD
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Upqcpt

noncomputable section

namespace Formalism.BasicNotions.Examples₂.CD

open MeasureTheory Filter Topology Set Matrix Formalism.UG.P
open scoped ENNReal NNReal

variable (P Q : ℕ)

abbrev MM : Type := Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

local notation "J" => Formalism.UG.Jpq P Q

instance instBorelLie : BorelSpace (lieU P Q) := ⟨rfl⟩
instance instBorelU : BorelSpace (UpqT P Q) := ⟨rfl⟩
instance instTopGroupU : IsTopologicalGroup (UpqT P Q) :=
  inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))

/- English proof (translation)
The claim follows from `Jpq_mul_self P Q`.
-/
theorem J_sq : J * J = 1 := Jpq_mul_self P Q

/- English proof (translation)
Rewrite using `[Jpq_eq_diagonal, diagonal_conjTranspose]`. Use `congr 1`. Use extensionality with `i`. Apply the tactic sequence `rcases i with i | i <;> simp`.
-/
theorem J_star : Jᴴ = J := by
  rw [Jpq_eq_diagonal, diagonal_conjTranspose]
  congr 1
  ext i
  rcases i with i | i <;> simp

/- English proof (translation)
The claim follows from `isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).add (continuous_const.matrix_mul continuous_id)) continuous_const`.
-/
theorem isClosed_lieU : IsClosed (lieU P Q : Set (MM P Q)) :=
  isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).add
    (continuous_const.matrix_mul continuous_id)) continuous_const

instance instLCLie : LocallyCompactSpace (lieU P Q) :=
  haveI : LocallyCompactSpace (MM P Q) :=
    inferInstanceAs (LocallyCompactSpace (Fin P ⊕ Fin Q → Fin P ⊕ Fin Q → ℂ))
  (isClosed_lieU P Q).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance instSCLie : SecondCountableTopology (lieU P Q) :=
  haveI : SecondCountableTopology (MM P Q) :=
    inferInstanceAs (SecondCountableTopology (Fin P ⊕ Fin Q → Fin P ⊕ Fin Q → ℂ))
  IsInducing.subtypeVal.secondCountableTopology

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem finDimLie : FiniteDimensional ℝ (lieU P Q) := inferInstance

/- English proof (translation)
Use `show Zᴴ * J + J * Z = 0 ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : Zᴴ * J = -(J * Z)` using `eq_neg_of_add_eq_zero_left h`. Combine the equalities or inequalities in the displayed calculation.

Introduce `h`. Establish `: J * Z = -(Zᴴ * J)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this, add_neg_cancel]`.
-/
theorem mem_lieU_iff (Z : MM P Q) : Z ∈ lieU P Q ↔ J * (-Zᴴ) * J = Z := by
  show Zᴴ * J + J * Z = 0 ↔ _
  constructor
  · intro h
    have h1 : Zᴴ * J = -(J * Z) := eq_neg_of_add_eq_zero_left h
    calc J * (-Zᴴ) * J = -(J * (Zᴴ * J)) := by simp [Matrix.mul_assoc]
      _ = J * J * Z := by rw [h1]; simp [Matrix.mul_assoc]
      _ = Z := by rw [J_sq, Matrix.one_mul]
  · intro h
    have : J * Z = -(Zᴴ * J) := by
      calc J * Z = J * (J * (-Zᴴ) * J) := by rw [h]
        _ = (J * J) * (-Zᴴ) * J := by simp only [Matrix.mul_assoc]
        _ = -(Zᴴ * J) := by rw [J_sq]; simp
    rw [this, add_neg_cancel]

def th (Z : MM P Q) : MM P Q := J * (-Zᴴ) * J

/- English proof (translation)
Simplify using `[th, Matrix.mul_add, Matrix.add_mul, add_comm]`.
-/
theorem th_add (Z W : MM P Q) : th P Q (Z + W) = th P Q Z + th P Q W := by
  simp [th, Matrix.mul_add, Matrix.add_mul, add_comm]

/- English proof (translation)
Simplify using `[th, Matrix.conjTranspose_smul]`.
-/
theorem th_smul (c : ℂ) (Z : MM P Q) : th P Q (c • Z) = (starRingEnd ℂ c) • th P Q Z := by
  simp [th, Matrix.conjTranspose_smul]

/- English proof (translation)
Unfold `th`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, J_star, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem th_th (Z : MM P Q) : th P Q (th P Q Z) = Z := by
  unfold th
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, J_star, Matrix.conjTranspose_neg,
    Matrix.conjTranspose_conjTranspose]
  calc J * -(J * (-Z * J)) * J = (J * J) * Z * (J * J) := by simp [Matrix.mul_assoc]
    _ = Z := by rw [J_sq]; simp

/- English proof (translation)
The claim follows from `(mem_lieU_iff P Q _).mp X.2`.
-/
theorem th_of_mem (X : lieU P Q) : th P Q (X : MM P Q) = X := (mem_lieU_iff P Q _).mp X.2

def psiLin : (lieU P Q × lieU P Q) →ₗ[ℝ] ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ) where
  toFun ab := entries ((ab.1 : MM P Q) + Complex.I • (ab.2 : MM P Q))
  map_add' x y := by
    funext ij
    simp [entries]
    ring
  map_smul' c x := by
    funext ij
    simp [entries]
    ring

/- English proof (translation)
Use extensionality with `i j`. Conclude with `congrFun h (i, j)`.
-/
theorem entries_inj {Z W : MM P Q} (h : entries Z = entries W) : Z = W := by
  ext i j
  exact congrFun h (i, j)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce and unpack `⟨a, b⟩ h`. Establish `h1 : (a : MM P Q) + Complex.I • (b : MM P Q) = 0` using `entries_inj P Q (Z := (a : MM P Q) + Complex.I • (b : MM P Q)) (W := 0) h`. Establish `h2 : (a : MM P Q) - Complex.I • (b : MM P Q) = 0`.

Use `congrArg (th P Q) h1` as an intermediate fact. Rewrite `this` using `[th_add, th_smul, th_of_mem, th_of_mem]`. Simplify `this` using `[th, sub_eq_add_neg]`. Establish `ha : (a : MM P Q) = 0`. Establish `: (2 : ℂ) • (a : MM P Q) = 0`.

Establish `e : (2 : ℂ) • (a : MM P Q) = ((a : MM P Q) + Complex.I • (b : MM P Q)) + ((a : MM P Q) - Complex.I • (b : MM P Q))` using `by rw [two_smul]; abel`. Rewrite using `[e, h1, h2, add_zero]`. Simplify using `using this`. Establish `hb : (b : MM P Q) = 0`. Rewrite `h1` using `[ha, zero_add]`.

Simplify using `using h1`. Conclude with `Prod.ext (Subtype.ext ha) (Subtype.ext hb)`. Introduce `z`. Set `Z : MM P Q` to `Matrix.of fun i j => z (i, j)`. Establish `ha : ((1 / 2 : ℂ) • (Z + th P Q Z)) ∈ lieU P Q`.

Rewrite using `[mem_lieU_iff]`. Use `show th P Q _ = _`. Rewrite using `[th_smul, th_add, th_th, add_comm, map_div₀, map_one, map_ofNat]`. Establish `hb : ((-Complex.I / 2 : ℂ) • (Z - th P Q Z)) ∈ lieU P Q`. Rewrite using `[mem_lieU_iff]`.

Use `show th P Q _ = _`. Rewrite using `[th_smul, sub_eq_add_neg, th_add, show -th P Q Z = (-1 : ℂ) • th P Q Z by simp, th_smul, th_th, map_div₀, map_neg, Complex.conj_I, map_ofNat, map_neg, map_one]`. Use `module`. Use `⟨(⟨_, ha⟩, ⟨_, hb⟩), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `ij`.

Use `show ((1 / 2 : ℂ) • (Z + th P Q Z) + Complex.I • ((-Complex.I / 2 : ℂ) • (Z - th P Q Z))) ij.1 ij.2 = z ij`. Establish `hI : Complex.I * Complex.I = -1` using `Complex.I_mul_I`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]`. Establish `: Z ij.1 ij.2 = z ij` using `rfl`. Rewrite using `[← this]`.

Take the linear combination `(-(1 / 2 : ℂ) * (Z ij.1 ij.2 - th P Q Z ij.1 ij.2)) * hI`.
-/
theorem psiLin_bij : Function.Bijective (psiLin P Q) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ h
    have h1 : (a : MM P Q) + Complex.I • (b : MM P Q) = 0 :=
      entries_inj P Q (Z := (a : MM P Q) + Complex.I • (b : MM P Q)) (W := 0) h
    have h2 : (a : MM P Q) - Complex.I • (b : MM P Q) = 0 := by
      have := congrArg (th P Q) h1
      rw [th_add, th_smul, th_of_mem, th_of_mem] at this
      simpa [th, sub_eq_add_neg] using this
    have ha : (a : MM P Q) = 0 := by
      have : (2 : ℂ) • (a : MM P Q) = 0 := by
        have e : (2 : ℂ) • (a : MM P Q) = ((a : MM P Q) + Complex.I • (b : MM P Q)) +
            ((a : MM P Q) - Complex.I • (b : MM P Q)) := by rw [two_smul]; abel
        rw [e, h1, h2, add_zero]
      simpa using this
    have hb : (b : MM P Q) = 0 := by
      rw [ha, zero_add] at h1
      simpa using h1
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  · intro z
    let Z : MM P Q := Matrix.of fun i j => z (i, j)
    have ha : ((1 / 2 : ℂ) • (Z + th P Q Z)) ∈ lieU P Q := by
      rw [mem_lieU_iff]
      show th P Q _ = _
      rw [th_smul, th_add, th_th, add_comm, map_div₀, map_one, map_ofNat]
    have hb : ((-Complex.I / 2 : ℂ) • (Z - th P Q Z)) ∈ lieU P Q := by
      rw [mem_lieU_iff]
      show th P Q _ = _
      rw [th_smul, sub_eq_add_neg, th_add,
        show -th P Q Z = (-1 : ℂ) • th P Q Z by simp, th_smul, th_th, map_div₀, map_neg,
        Complex.conj_I, map_ofNat, map_neg, map_one]
      module
    refine ⟨(⟨_, ha⟩, ⟨_, hb⟩), ?_⟩
    funext ij
    show ((1 / 2 : ℂ) • (Z + th P Q Z) + Complex.I • ((-Complex.I / 2 : ℂ) • (Z - th P Q Z))) ij.1 ij.2 = z ij
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    have : Z ij.1 ij.2 = z ij := rfl
    rw [← this]
    linear_combination (-(1 / 2 : ℂ) * (Z ij.1 ij.2 - th P Q Z ij.1 ij.2)) * hI

def psiE : (lieU P Q × lieU P Q) ≃L[ℝ] ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ) :=
  haveI := finDimLie P Q
  haveI : FiniteDimensional ℝ (lieU P Q × lieU P Q) := Module.Finite.prod
  (LinearEquiv.ofBijective (psiLin P Q) (psiLin_bij P Q)).toContinuousLinearEquiv

/- English proof (translation)
Use function extensionality and compare the values at `ab`. Both sides reduce to the same expression.
-/
theorem psiE_coe : ⇑(psiE P Q) = fun ab : lieU P Q × lieU P Q =>
    entries ((ab.1 : MM P Q) + Complex.I • (ab.2 : MM P Q)) := by
  funext ab
  rfl

/- English proof (translation)
Set `lam0 : Measure (lieU P Q)` to `Measure.addHaar`. Set `m` to `(lam0.prod lam0).map (psiE P Q)`. Establish `hm : m.IsAddHaarMeasure` using `inferInstance`. Establish `hs` using `Measure.isAddLeftInvariant_eq_smul m volume`. Use `set s := Measure.addHaarScalarFactor m volume with hsdef`.

Establish `hs0 : 0 < s` using `Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure m volume`. Set `t : ℝ≥0` to `(NNReal.sqrt s)⁻¹`. Establish `ht0 : t ≠ 0` using `inv_ne_zero (NNReal.sqrt_pos.mpr hs0).ne'`. Establish `hts : t * t * s = 1`. Establish `h1 : NNReal.sqrt s * NNReal.sqrt s = s` using `NNReal.mul_self_sqrt s`.

Establish `h2 : NNReal.sqrt s ≠ 0` using `(NNReal.sqrt_pos.mpr hs0).ne'`. Combine the equalities or inequalities in the displayed calculation. Establish `hl : (t • lam0).IsAddHaarMeasure` using `Measure.IsAddHaarMeasure.nnreal_smul lam0 ht0`. Use `⟨t • lam0, hl, ?_⟩` and prove the remaining obligations. Rewrite using `[← psiE_coe]`.

Rewrite using `[Measure.prod_smul_left, Measure.prod_smul_right, Measure.map_smul, Measure.map_smul]`. Use `show t • t • m = volume`. Rewrite using `[hs, smul_smul, smul_smul, hts, one_smul]`.
-/
theorem exists_omegaLeb : ∃ lam : Measure (lieU P Q), IsOmegaLeb lam := by
  let lam0 : Measure (lieU P Q) := Measure.addHaar
  let m := (lam0.prod lam0).map (psiE P Q)
  have hm : m.IsAddHaarMeasure := inferInstance
  have hs := Measure.isAddLeftInvariant_eq_smul m volume
  set s := Measure.addHaarScalarFactor m volume with hsdef
  have hs0 : 0 < s := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure m volume
  let t : ℝ≥0 := (NNReal.sqrt s)⁻¹
  have ht0 : t ≠ 0 := inv_ne_zero (NNReal.sqrt_pos.mpr hs0).ne'
  have hts : t * t * s = 1 := by
    have h1 : NNReal.sqrt s * NNReal.sqrt s = s := NNReal.mul_self_sqrt s
    have h2 : NNReal.sqrt s ≠ 0 := (NNReal.sqrt_pos.mpr hs0).ne'
    calc (NNReal.sqrt s)⁻¹ * (NNReal.sqrt s)⁻¹ * s
        = (NNReal.sqrt s)⁻¹ * (NNReal.sqrt s)⁻¹ * (NNReal.sqrt s * NNReal.sqrt s) := by rw [h1]
      _ = 1 := by field_simp
  have hl : (t • lam0).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul lam0 ht0
  refine ⟨t • lam0, hl, ?_⟩
  rw [← psiE_coe]
  rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.map_smul, Measure.map_smul]
  show t • t • m = volume
  rw [hs, smul_smul, smul_smul, hts, one_smul]

/- English proof (translation)
Establish `: Continuous (fun X : lieU P Q => ∑ i, ∑ j, ‖(X : MM P Q) i j‖)` using `continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => (continuous_subtype_val.matrix_elem i j).norm`. Conclude with `isOpen_lt this continuous_const`.
-/
theorem isOpen_ballU (r : ℝ) : IsOpen (ballU P Q r) := by
  have : Continuous (fun X : lieU P Q => ∑ i, ∑ j, ‖(X : MM P Q) i j‖) :=
    continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (continuous_subtype_val.matrix_elem i j).norm
  exact isOpen_lt this continuous_const

/- English proof (translation)
Use `show ∑ i, ∑ j, ‖((0 : lieU P Q) : MM P Q) i j‖ < r`. Simplify using `using hr`.
-/
theorem zero_mem_ballU {r : ℝ} (hr : 0 < r) : (0 : lieU P Q) ∈ ballU P Q r := by
  show ∑ i, ∑ j, ‖((0 : lieU P Q) : MM P Q) i j‖ < r
  simpa using hr

/- English proof (translation)
The claim follows from `(Finset.single_le_sum (f := fun j => ‖X i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖X i j‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))`.
-/
theorem entry_le_sum (X : MM P Q) (i j : Fin P ⊕ Fin Q) : ‖X i j‖ ≤ ∑ i, ∑ j, ‖X i j‖ :=
  (Finset.single_le_sum (f := fun j => ‖X i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, ‖X i j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))

/- English proof (translation)
Establish `hbox : IsCompact (Set.pi Set.univ fun _ : Fin P ⊕ Fin Q => Set.pi Set.univ fun _ : Fin P ⊕ Fin Q => Metric.closedBall (0 : ℂ) r : Set (MM P Q))` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 r`. Establish `hK` using `(isClosed_lieU P Q).isClosedEmbedding_subtypeVal.isCompact_preimage hbox`. Use `lt_of_le_of_lt (measure_mono ?_) hK.measure_lt_top` and prove the remaining obligations. Introduce `X hX i _ j _`. Rewrite using `[mem_closedBall_zero_iff]`.

Conclude with `(entry_le_sum P Q X i j).trans (le_of_lt hX)`.
-/
theorem ballU_lt_top (lam : Measure (lieU P Q)) [lam.IsAddHaarMeasure] (r : ℝ) :
    lam (ballU P Q r) < ⊤ := by
  have hbox : IsCompact (Set.pi Set.univ fun _ : Fin P ⊕ Fin Q =>
      Set.pi Set.univ fun _ : Fin P ⊕ Fin Q => Metric.closedBall (0 : ℂ) r : Set (MM P Q)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 r
  have hK := (isClosed_lieU P Q).isClosedEmbedding_subtypeVal.isCompact_preimage hbox
  refine lt_of_le_of_lt (measure_mono ?_) hK.measure_lt_top
  intro X hX i _ j _
  rw [mem_closedBall_zero_iff]
  exact (entry_le_sum P Q X i j).trans (le_of_lt hX)

/- English proof (translation)
The claim follows from `(isOpen_ballU P Q r).measure_pos lam ⟨0, zero_mem_ballU P Q hr⟩`.
-/
theorem ballU_pos (lam : Measure (lieU P Q)) [lam.IsAddHaarMeasure] {r : ℝ} (hr : 0 < r) :
    0 < lam (ballU P Q r) :=
  (isOpen_ballU P Q r).measure_pos lam ⟨0, zero_mem_ballU P Q hr⟩

end Formalism.BasicNotions.Examples₂.CD
