import Formalism.LocalRingCardinality.SpanPowerMembership.ExistsDensity
import Formalism.LocalRingCardinality.SpanPowerMembership.ExistsOmegaLeb
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLeSum

noncomputable section

namespace Formalism.BasicNotions.Examples₂.CD

open MeasureTheory Filter Topology Metric NormedSpace Set Matrix Formalism.UG.P
open scoped ENNReal NNReal Matrix.Norms.Operator

variable (P Q : ℕ)

local notation "J" => Formalism.UG.Jpq P Q

instance : CompleteSpace (MM P Q) := FiniteDimensional.complete ℝ _

def matHom : UpqT P Q →* MM P Q where
  toFun := UpqT.mat
  map_one' := rfl
  map_mul' _ _ := rfl

/- English proof (translation)
The claim follows from `g.2`.
-/
theorem mat_mem (g : UpqT P Q) : (UpqT.mat g)ᴴ * J * UpqT.mat g = J := g.2

/- English proof (translation)
Establish `h` using `mat_mem P Q g`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [h, J_sq]`.
-/
theorem mat_left_inv (g : UpqT P Q) : (J * (UpqT.mat g)ᴴ * J) * UpqT.mat g = 1 := by
  have h := mat_mem P Q g
  calc J * (UpqT.mat g)ᴴ * J * UpqT.mat g = J * ((UpqT.mat g)ᴴ * J * UpqT.mat g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, J_sq]

/- English proof (translation)
Establish `h1` using `mat_left_inv P Q g`. Establish `h2 : UpqT.mat (P` using `P) (Q := Q) g * (((g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : MM P Q) = 1 := Units.mul_inv (g : GL (Fin P ⊕ Fin Q) ℂ)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, Matrix.one_mul]`. Use `_ = J * (UpqT.mat (P := P) (Q := Q) g)ᴴ * J := by`.

Rewrite using `[Matrix.mul_assoc (J * (UpqT.mat (P := P) (Q := Q) g)ᴴ * J), h2, Matrix.mul_one]`.
-/
theorem mat_inv_eq (g : Formalism.UG.Upq P Q) :
    (((g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : MM P Q) =
      J * (UpqT.mat (P := P) (Q := Q) g)ᴴ * J := by
  have h1 := mat_left_inv P Q g
  have h2 : UpqT.mat (P := P) (Q := Q) g *
      (((g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : MM P Q) = 1 :=
    Units.mul_inv (g : GL (Fin P ⊕ Fin Q) ℂ)
  calc (((g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : MM P Q)
      = (J * (UpqT.mat (P := P) (Q := Q) g)ᴴ * J * UpqT.mat (P := P) (Q := Q) g) *
          (((g : GL (Fin P ⊕ Fin Q) ℂ)⁻¹ : GL (Fin P ⊕ Fin Q) ℂ) : MM P Q) := by
        rw [h1, Matrix.one_mul]
    _ = J * (UpqT.mat (P := P) (Q := Q) g)ᴴ * J := by
        rw [Matrix.mul_assoc (J * (UpqT.mat (P := P) (Q := Q) g)ᴴ * J), h2, Matrix.mul_one]

/- English proof (translation)
The claim follows from `Units.continuous_val.comp continuous_subtype_val`.
-/
theorem mat_cont : Continuous (UpqT.mat : UpqT P Q → MM P Q) := Units.continuous_val.comp continuous_subtype_val

/- English proof (translation)
Conclude with `Units.isOpenEmbedding_val.toIsEmbedding.toIsInducing.comp Topology.IsInducing.subtypeVal`.
-/
theorem mat_inducing : IsInducing (UpqT.mat : UpqT P Q → MM P Q) := by
  exact Units.isOpenEmbedding_val.toIsEmbedding.toIsInducing.comp Topology.IsInducing.subtypeVal

/- English proof (translation)
Introduce `a b h` and use `Subtype.ext (Units.ext h)`.
-/
theorem mat_injective : Function.Injective (UpqT.mat : UpqT P Q → MM P Q) := fun a b h => Subtype.ext (Units.ext h)

/- English proof (translation)
Assemble the required witnesses or components as `⟨mat_inducing P Q, mat_injective P Q⟩`.
-/
theorem mat_embedding : IsEmbedding (UpqT.mat : UpqT P Q → MM P Q) := ⟨mat_inducing P Q, mat_injective P Q⟩

/- English proof (translation)
Establish `hl : J * hᴴ * J * h = 1`. Combine the equalities or inequalities in the displayed calculation. Establish `hr : h * (J * hᴴ * J) = 1` using `mul_eq_one_comm.mp hl`. Conclude with `⟨⟨⟨h, J * hᴴ * J, hr, hl⟩, hh⟩, rfl⟩`.
-/
theorem exists_of_mem (h : MM P Q) (hh : hᴴ * J * h = J) : ∃ g : UpqT P Q, UpqT.mat g = h := by
  have hl : J * hᴴ * J * h = 1 := by
    calc J * hᴴ * J * h = J * (hᴴ * J * h) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hh, J_sq]
  have hr : h * (J * hᴴ * J) = 1 := mul_eq_one_comm.mp hl
  exact ⟨⟨⟨h, J * hᴴ * J, hr, hl⟩, hh⟩, rfl⟩

/- English proof (translation)
Use extensionality with `h`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩`. Conclude with `mat_mem P Q g`. Introduce `hh`.

Conclude with `exists_of_mem P Q h hh`.
-/
theorem mat_range : Set.range (UpqT.mat : UpqT P Q → MM P Q) = {h | hᴴ * J * h = J} := by
  ext h
  constructor
  · rintro ⟨g, rfl⟩
    exact mat_mem P Q g
  · intro hh
    exact exists_of_mem P Q h hh

/- English proof (translation)
Use `⟨mat_embedding P Q, ?_⟩` and prove the remaining obligations. Rewrite using `[mat_range]`. Conclude with `isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const`.
-/
theorem mat_closedEmbedding : IsClosedEmbedding (UpqT.mat : UpqT P Q → MM P Q) := by
  refine ⟨mat_embedding P Q, ?_⟩
  rw [mat_range]
  exact isClosed_eq
    ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

instance : LocallyCompactSpace (UpqT P Q) :=
  haveI : LocallyCompactSpace (MM P Q) :=
    inferInstanceAs (LocallyCompactSpace (Fin P ⊕ Fin Q → Fin P ⊕ Fin Q → ℂ))
  (mat_closedEmbedding P Q).locallyCompactSpace

instance (N : ℕ) : CompactSpace (UpqT N 0) :=
  isCompact_iff_compactSpace.mp (indefinite_unitary_compact N)

/- English proof (translation)
Establish `h` using `NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl X))`. Rewrite `h` using `[neg_add_cancel, NormedSpace.exp_zero]`. Conclude with `h.symm`.
-/
theorem exp_neg_mul' (X : MM P Q) : exp (-X) * exp X = 1 := by
  have h := NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl X))
  rw [neg_add_cancel, NormedSpace.exp_zero] at h
  exact h.symm

/- English proof (translation)
Establish `h` using `NormedSpace.exp_add_of_commute (Commute.neg_right (Commute.refl X))`. Rewrite `h` using `[add_neg_cancel, NormedSpace.exp_zero]`. Conclude with `h.symm`.
-/
theorem exp_mul_neg' (X : MM P Q) : exp X * exp (-X) = 1 := by
  have h := NormedSpace.exp_add_of_commute (Commute.neg_right (Commute.refl X))
  rw [add_neg_cancel, NormedSpace.exp_zero] at h
  exact h.symm

/- English proof (translation)
Set `u : (MM P Q)ˣ` to `⟨J, J, J_sq P Q, J_sq P Q⟩`. Conclude with `NormedSpace.exp_units_conj u A`.
-/
theorem exp_conjJ (A : MM P Q) : exp (J * A * J) = J * exp A * J := by
  let u : (MM P Q)ˣ := ⟨J, J, J_sq P Q, J_sq P Q⟩
  exact NormedSpace.exp_units_conj u A

/- English proof (translation)
Establish `h1 : J * (-Xᴴ) * J = X` using `(mem_lieU_iff P Q X).1 hX`. Establish `e : J * (J * (-Xᴴ) * J) * J = -Xᴴ`. Rewrite using `[mul_assoc, mul_assoc (J * (-Xᴴ)), J_sq, mul_one, ← mul_assoc, J_sq, one_mul]`. Establish `h2 : Xᴴ = J * (-X) * J`. Rewrite `e` using `[h1]`.

Rewrite using `[mul_neg, neg_mul, e, neg_neg]`. Rewrite using `[← Matrix.exp_conjTranspose, h2, exp_conjJ]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = J := by rw [J_sq, mul_one, exp_neg_mul', mul_one]`.
-/
theorem exp_mem (X : MM P Q) (hX : X ∈ lieU P Q) : (exp X)ᴴ * J * exp X = J := by
  have h1 : J * (-Xᴴ) * J = X := (mem_lieU_iff P Q X).1 hX
  have e : J * (J * (-Xᴴ) * J) * J = -Xᴴ := by
    rw [mul_assoc, mul_assoc (J * (-Xᴴ)), J_sq, mul_one, ← mul_assoc, J_sq, one_mul]
  have h2 : Xᴴ = J * (-X) * J := by
    rw [h1] at e
    rw [mul_neg, neg_mul, e, neg_neg]
  rw [← Matrix.exp_conjTranspose, h2, exp_conjJ]
  calc J * exp (-X) * J * J * exp X = J * (exp (-X) * (J * J) * exp X) := by
        simp only [mul_assoc]
    _ = J := by rw [J_sq, mul_one, exp_neg_mul', mul_one]

/- English proof (translation)
Establish `hc : (exp Z)ᴴ = exp Zᴴ` using `(Matrix.exp_conjTranspose Z).symm`. Rewrite `hZ` using `[hc]`. Establish `h1 : J * exp Z = exp (-Zᴴ) * J`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[exp_conjJ]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exp_theta (Z : MM P Q) (hZ : (exp Z)ᴴ * J * exp Z = J) : exp (J * (-Zᴴ) * J) = exp Z := by
  have hc : (exp Z)ᴴ = exp Zᴴ := (Matrix.exp_conjTranspose Z).symm
  rw [hc] at hZ
  have h1 : J * exp Z = exp (-Zᴴ) * J := by
    calc J * exp Z = exp (-Zᴴ) * exp Zᴴ * J * exp Z := by rw [exp_neg_mul', one_mul]
      _ = exp (-Zᴴ) * (exp Zᴴ * J * exp Z) := by simp only [mul_assoc]
      _ = exp (-Zᴴ) * J := by rw [hZ]
  rw [exp_conjJ]
  calc J * exp (-Zᴴ) * J = J * (exp (-Zᴴ) * J) := by rw [mul_assoc]
    _ = J * (J * exp Z) := by rw [h1]
    _ = exp Z := by rw [← mul_assoc, J_sq, one_mul]

def chart : Chart (lieU P Q) (UpqT P Q) where
  mat := matHom P Q
  emb := mat_embedding P Q
  H1 := fun X => exists_of_mem P Q _ (exp_mem P Q X X.2)
  H2 := by
    have hθ : Continuous (fun Z : MM P Q => J * (-Zᴴ) * J) :=
      (continuous_const.matrix_mul continuous_id.matrix_conjTranspose.neg).matrix_mul continuous_const
    have h0 : Tendsto (fun Z : MM P Q => J * (-Zᴴ) * J) (𝓝 0) (𝓝 0) := by
      have := hθ.tendsto 0
      simpa using this
    filter_upwards [logA_exp (𝔸 := MM P Q), h0.eventually (logA_exp (𝔸 := MM P Q))] with Z h1 h2
    rintro ⟨g, hg⟩
    have hm : (exp Z)ᴴ * J * exp Z = J := by
      have := mat_mem P Q g
      rw [show UpqT.mat g = exp Z from hg] at this
      exact this
    rw [mem_lieU_iff]
    calc J * (-Zᴴ) * J = logA (MM P Q) (exp (J * (-Zᴴ) * J)) := h2.symm
      _ = logA (MM P Q) (exp Z) := congrArg (logA (MM P Q)) (exp_theta P Q Z hm)
      _ = Z := h1

/- English proof (translation)
Establish `hs : (Finset.univ.sup fun i => ∑ j, ‖X i j‖₊) ≤ ∑ i, ∑ j, ‖X i j‖₊` using `Finset.sup_le fun i _ => Finset.single_le_sum (f := fun i => ∑ j, ‖X i j‖₊) (fun _ _ => zero_le) (Finset.mem_univ i)`. Rewrite using `[Matrix.linfty_opNorm_def]`. Use `(NNReal.coe_le_coe.mpr hs).trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using `[NNReal.coe_sum]`.
-/
theorem norm_le_sum (X : MM P Q) : ‖X‖ ≤ ∑ i, ∑ j, ‖X i j‖ := by
  have hs : (Finset.univ.sup fun i => ∑ j, ‖X i j‖₊) ≤ ∑ i, ∑ j, ‖X i j‖₊ :=
    Finset.sup_le fun i _ =>
      Finset.single_le_sum (f := fun i => ∑ j, ‖X i j‖₊) (fun _ _ => zero_le) (Finset.mem_univ i)
  rw [Matrix.linfty_opNorm_def]
  refine (NNReal.coe_le_coe.mpr hs).trans (le_of_eq ?_)
  simp [NNReal.coe_sum]

/- English proof (translation)
Take `⟨lam, hlam⟩` from `exists_omegaLeb P Q`. Use `hlam.1` as an intermediate fact. Take `⟨c, hc0, hct, h⟩` from `(chart P Q).exists_density' (finDimLie P Q) _ (instBorelLie P Q) _ (instBorelU P Q) (instTopGroupU P Q) μ inferInstance lam hlam.1`. Use `⟨c, hc0, hct, lam, hlam, ?_⟩` and prove the remaining obligations. Conclude with `h (ballU P Q) (fun r => (isOpen_ballU P Q r).measurableSet) (fun δ hδ => by filter_upwards [Ioo_mem_nhdsGT hδ] with r hr X hX`.

Conclude with `lt_of_le_of_lt (norm_le_sum P Q X) (lt_trans hX hr.2))`. Use the proof step `(by filter_upwards [self_mem_nhdsWithin] with r hr`. Conclude with `⟨(ballU_pos P Q lam hr).ne', (ballU_lt_top P Q lam r).ne⟩)`.
-/
theorem omegaDensity_haar (μ : Measure (UpqT P Q)) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ OmegaDensity μ c := by
  obtain ⟨lam, hlam⟩ := exists_omegaLeb P Q
  have := hlam.1
  obtain ⟨c, hc0, hct, h⟩ := (chart P Q).exists_density' (finDimLie P Q) _ (instBorelLie P Q) _
    (instBorelU P Q) (instTopGroupU P Q) μ inferInstance lam hlam.1
  refine ⟨c, hc0, hct, lam, hlam, ?_⟩
  exact h (ballU P Q) (fun r => (isOpen_ballU P Q r).measurableSet)
    (fun δ hδ => by
      filter_upwards [Ioo_mem_nhdsGT hδ] with r hr X hX
      exact lt_of_le_of_lt (norm_le_sum P Q X) (lt_trans hX hr.2))
    (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact ⟨(ballU_pos P Q lam hr).ne', (ballU_lt_top P Q lam r).ne⟩)

/- English proof (translation)
Take `⟨lam, hl, hc⟩` from `h`. Use `⟨lam, hl, ?_⟩` and prove the remaining obligations. Use `(ENNReal.Tendsto.const_mul hc (Or.inr ht)).congr (fun r => ?_)` and prove the remaining obligations. Rewrite using `[Measure.smul_apply, smul_eq_mul, mul_div_assoc]`.
-/
theorem omegaDensity_smul {μ : Measure (UpqT P Q)} {c : ℝ≥0∞} (h : OmegaDensity μ c) (t : ℝ≥0∞)
    (ht : t ≠ ⊤) : OmegaDensity (t • μ) (t * c) := by
  obtain ⟨lam, hl, hc⟩ := h
  refine ⟨lam, hl, ?_⟩
  refine (ENNReal.Tendsto.const_mul hc (Or.inr ht)).congr (fun r => ?_)
  rw [Measure.smul_apply, smul_eq_mul, mul_div_assoc]

def mu0 : Measure (UpqT P Q) := Measure.haar

instance : (mu0 P Q).IsHaarMeasure := inferInstanceAs (Measure.haar.IsHaarMeasure)

def c0 : ℝ≥0∞ := (omegaDensity_haar P Q (mu0 P Q)).choose

/- English proof (translation)
The claim follows from `(omegaDensity_haar P Q (mu0 P Q)).choose_spec.1`.
-/
theorem haar_density_ne_zero : c0 P Q ≠ 0 := (omegaDensity_haar P Q (mu0 P Q)).choose_spec.1
/- English proof (translation)
The claim follows from `(omegaDensity_haar P Q (mu0 P Q)).choose_spec.2.1`.
-/
theorem haar_density_ne_top : c0 P Q ≠ ⊤ := (omegaDensity_haar P Q (mu0 P Q)).choose_spec.2.1
/- English proof (translation)
The claim follows from `(omegaDensity_haar P Q (mu0 P Q)).choose_spec.2.2`.
-/
theorem haar_density_spec : OmegaDensity (mu0 P Q) (c0 P Q) := (omegaDensity_haar P Q (mu0 P Q)).choose_spec.2.2

def mass (N : ℕ) : ℝ≥0∞ := mu0 N 0 Set.univ

/- English proof (translation)
The claim follows from `isOpen_univ.measure_ne_zero (mu0 N 0) ⟨1, trivial⟩`.
-/
theorem mass_ne_zero (N : ℕ) : mass N ≠ 0 := isOpen_univ.measure_ne_zero (mu0 N 0) ⟨1, trivial⟩

/- English proof (translation)
The claim follows from `(isCompact_univ.measure_lt_top (μ := mu0 N 0)).ne`.
-/
theorem mass_ne_top (N : ℕ) : mass N ≠ ⊤ := (isCompact_univ.measure_lt_top (μ := mu0 N 0)).ne

def scale : ℝ≥0∞ := c0 (P + Q) 0 / (mass (P + Q) * c0 P Q)

/- English proof (translation)
The claim follows from `ENNReal.div_ne_zero.mpr ⟨haar_density_ne_zero _ _, ENNReal.mul_ne_top (mass_ne_top _) (haar_density_ne_top _ _)⟩`.
-/
theorem scale_ne_zero : scale P Q ≠ 0 := ENNReal.div_ne_zero.mpr ⟨haar_density_ne_zero _ _, ENNReal.mul_ne_top (mass_ne_top _) (haar_density_ne_top _ _)⟩

/- English proof (translation)
The claim follows from `ENNReal.div_ne_top (haar_density_ne_top _ _) (mul_ne_zero (mass_ne_zero _) (haar_density_ne_zero _ _))`.
-/
theorem scale_ne_top : scale P Q ≠ ⊤ := ENNReal.div_ne_top (haar_density_ne_top _ _) (mul_ne_zero (mass_ne_zero _) (haar_density_ne_zero _ _))

/- English proof (translation)
Unfold `scale`. Rewrite using `[div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inr (haar_density_ne_top _ _)) (Or.inr (haar_density_ne_zero _ _)), mul_assoc, mul_assoc, ENNReal.inv_mul_cancel (haar_density_ne_zero _ _) (haar_density_ne_top _ _), mul_one]`.
-/
theorem scale_mul : scale P Q * c0 P Q = c0 (P + Q) 0 / mass (P + Q) := by
  unfold scale
  rw [div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr (haar_density_ne_top _ _)) (Or.inr (haar_density_ne_zero _ _)), mul_assoc, mul_assoc,
    ENNReal.inv_mul_cancel (haar_density_ne_zero _ _) (haar_density_ne_top _ _), mul_one]

/- English proof (translation)
Unfold `scale`. Rewrite using `[Nat.add_zero, div_eq_mul_inv, ENNReal.mul_inv (Or.inl (mass_ne_zero _)) (Or.inl (mass_ne_top _)), mul_comm (mass N)⁻¹, ← mul_assoc, ENNReal.mul_inv_cancel (haar_density_ne_zero _ _) (haar_density_ne_top _ _), one_mul, ENNReal.inv_mul_cancel (mass_ne_zero _) (mass_ne_top _)]`.
-/
theorem scale_mass (N : ℕ) : scale N 0 * mass N = 1 := by
  unfold scale
  rw [Nat.add_zero, div_eq_mul_inv, ENNReal.mul_inv (Or.inl (mass_ne_zero _)) (Or.inl (mass_ne_top _)),
    mul_comm (mass N)⁻¹, ← mul_assoc, ENNReal.mul_inv_cancel (haar_density_ne_zero _ _) (haar_density_ne_top _ _), one_mul,
    ENNReal.inv_mul_cancel (mass_ne_zero _) (mass_ne_top _)]

def cdHaar : CDHaar where
  cd := fun P Q => scale P Q • mu0 P Q
  haar := fun P Q => Measure.IsHaarMeasure.smul (mu0 P Q) (scale_ne_zero P Q) (scale_ne_top P Q)
  prob := fun N => ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact scale_mass N⟩
  trick := fun P Q => ⟨c0 (P + Q) 0 / mass (P + Q),
    ENNReal.div_ne_zero.mpr ⟨haar_density_ne_zero _ _, mass_ne_top _⟩,
    ENNReal.div_ne_top (haar_density_ne_top _ _) (mass_ne_zero _),
    by
      rw [← scale_mul P Q]
      exact omegaDensity_smul P Q (haar_density_spec P Q) _ (scale_ne_top P Q),
    by
      have h := omegaDensity_smul (P + Q) 0 (haar_density_spec (P + Q) 0) _ (scale_ne_top (P + Q) 0)
      rw [scale_mul (P + Q) 0] at h
      exact h⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨cdHaar⟩`.
-/
theorem cdHaar_nonempty : Nonempty CDHaar := ⟨cdHaar⟩

end Formalism.BasicNotions.Examples₂.CD
