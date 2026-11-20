import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroupA

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace MatrixSubsetMeasurability

variable {k r : ℕ} {U : Set (Mat k r)}

def SG (_hU : IsClosedSubgroup U) : Type := {x : Mt k r // (Matrix.of x : Mat k r) ∈ U}

def mat {hU : IsClosedSubgroup U} (g : SG hU) : Mat k r := Matrix.of g.1

/- English proof (translation)
Conclude with `g.2`.
-/
theorem mat_mem {hU : IsClosedSubgroup U} (g : SG hU) : mat g ∈ U := by
  exact g.2

def mk (hU : IsClosedSubgroup U) (A : Mat k r) (hA : A ∈ U) : SG hU := ⟨Matrix.of.symm A, hA⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_mk (hU : IsClosedSubgroup U) (A : Mat k r) (hA : A ∈ U) : mat (mk hU A hA) = A := rfl

variable {hU : IsClosedSubgroup U}

instance : One (SG hU) := ⟨mk hU 1 hU.one_mem⟩
instance : Mul (SG hU) := ⟨fun a b => mk hU (mat a * mat b) (hU.mul_mem _ a.2 _ b.2)⟩
instance : Inv (SG hU) := ⟨fun a => mk hU (mat a)⁻¹ (hU.inv_mem _ a.2)⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_one : mat (1 : SG hU) = 1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_mul (a b : SG hU) : mat (a * b) = mat a * mat b := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_inv (a : SG hU) : mat a⁻¹ = (mat a)⁻¹ := rfl

/- English proof (translation)
Conclude with `Subtype.ext (Matrix.of.injective h)`.
-/
theorem ext' {a b : SG hU} (h : mat a = mat b) : a = b := by
  exact Subtype.ext (Matrix.of.injective h)

instance : Group (SG hU) :=
  Group.ofLeftAxioms (fun a b c => ext' (Matrix.mul_assoc (mat a) (mat b) (mat c)))
    (fun a => ext' (Matrix.one_mul (mat a)))
    (fun a => ext' (Matrix.nonsing_inv_mul (mat a) (hU.unit _ a.2)))

instance : TopologicalSpace (SG hU) := instTopologicalSpaceSubtype
instance : MeasurableSpace (SG hU) := Subtype.instMeasurableSpace
instance : BorelSpace (SG hU) :=
  inferInstanceAs (BorelSpace ({x : Mt k r | (Matrix.of x : Mat k r) ∈ U} : Set (Mt k r)))

/- English proof (translation)
The claim follows from `continuous_matrix (fun i j => (continuous_apply j).comp (continuous_apply i))`.
-/
private theorem continuous_matrix_of_Mt : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) :=
  continuous_matrix (fun i j => (continuous_apply j).comp (continuous_apply i))

/- English proof (translation)
Conclude with `continuous_subtype_val`.
-/
theorem continuous_val : Continuous (fun g : SG hU => g.1) := by
  exact continuous_subtype_val

/- English proof (translation)
Conclude with `continuous_matrix_of_Mt.comp continuous_subtype_val`.
-/
theorem continuous_mat : Continuous (fun g : SG hU => mat g) := by
  exact continuous_matrix_of_Mt.comp continuous_subtype_val

instance : ContinuousMul (SG hU) := by
  refine ⟨Continuous.subtype_mk ?_ _⟩
  exact (continuous_mat.comp continuous_fst).matrix_mul (continuous_mat.comp continuous_snd)

instance : ContinuousInv (SG hU) := by
  refine ⟨Continuous.subtype_mk ?_ _⟩
  have h : (fun a : SG hU => (mat a)⁻¹) = fun a => (mat a).det⁻¹ • (mat a).adjugate := by
    funext a; rw [Matrix.inv_def, Ring.inverse_eq_inv]
  show Continuous fun a : SG hU => (mat a)⁻¹
  rw [h]
  exact ((continuous_mat.matrix_det).inv₀ fun a => (hU.unit _ a.2).ne_zero).smul continuous_mat.matrix_adjugate

instance : IsTopologicalGroup (SG hU) := {}

/- English proof (translation)
Conclude with `(hU.closed.preimage continuous_matrix_of_Mt).measurableSet`.
-/
theorem measurableSet_U (hU : IsClosedSubgroup U) : MeasurableSet {x : Mt k r | (Matrix.of x : Mat k r) ∈ U} := by
  exact (hU.closed.preimage continuous_matrix_of_Mt).measurableSet

/- English proof (translation)
Conclude with `MeasurableEmbedding.subtype_coe (measurableSet_U hU)`.
-/
theorem me_val (hU : IsClosedSubgroup U) : MeasurableEmbedding (fun g : SG hU => g.1) := by
  exact MeasurableEmbedding.subtype_coe (measurableSet_U hU)

def nu (hU : IsClosedSubgroup U) (μ : Measure (Mt k r)) : Measure (SG hU) := μ.comap (fun g : SG hU => g.1)

/- English proof (translation)
Unfold `nu`. Rewrite using `[(me_val hU).map_comap]`. Apply the tactic sequence `first | rw [Subtype.range_coe_subtype] | rw [Subtype.range_val_subtype] | skip`. Establish `hae : ∀ᵐ x ∂μ, (Matrix.of x : Mat k r) ∈ U` using `ae_iff.mpr hμ.conc`. Conclude with `Measure.restrict_eq_self_of_ae_mem (hae.mono fun x hx => ⟨⟨x, hx⟩, rfl⟩)`.
-/
theorem map_nu {μ : Measure (Mt k r)} (hμ : IsHaarOn U μ) : (nu hU μ).map (fun g : SG hU => g.1) = μ := by
  unfold nu
  rw [(me_val hU).map_comap]
  first | rw [Subtype.range_coe_subtype] | rw [Subtype.range_val_subtype] | skip
  have hae : ∀ᵐ x ∂μ, (Matrix.of x : Mat k r) ∈ U := ae_iff.mpr hμ.conc
  exact Measure.restrict_eq_self_of_ae_mem (hae.mono fun x hx => ⟨⟨x, hx⟩, rfl⟩)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `g`. Establish `hc : Continuous (lmulM (k` using `k) (r := r) (mat g)) := (continuous_const.mul continuous_matrix_of_Mt : Continuous fun x : Mt k r => (mat g * Matrix.of x : Mat k r))`. Establish `hm : Measurable (fun x : SG hU => g * x)`. Use `Measurable.subtype_mk ?_` and prove the remaining obligations.

Conclude with `hc.measurable.comp measurable_subtype_coe`. Establish `hval : (fun g : SG hU => g.1) ∘ (fun x : SG hU => g * x) = lmulM (mat g) ∘ (fun g : SG hU => g.1)` using `rfl`. Establish `hmap : ((nu hU μ).map (fun x : SG hU => g * x)).map (fun g : SG hU => g.1) = (nu hU μ).map (fun g : SG hU => g.1)`. Rewrite using `[Measure.map_map (me_val hU).measurable hm, hval, ← Measure.map_map hc.measurable (me_val hU).measurable, map_nu hμ, hμ.left _ (mat_mem g)]`. Use extensionality with `s hs`.

Establish `h1` using `congrArg (fun m : Measure (Mt k r) => m ((fun g : SG hU => g.1) '' s)) hmap`. Rewrite `h1` using `[(me_val hU).map_apply, (me_val hU).map_apply, Set.preimage_image_eq s (me_val hU).injective]`. Then use the resulting hypothesis.
-/
theorem nu_left {μ : Measure (Mt k r)} (hμ : IsHaarOn U μ) : (nu hU μ).IsMulLeftInvariant := by
  constructor
  intro g
  have hc : Continuous (lmulM (k := k) (r := r) (mat g)) :=
    (continuous_const.mul continuous_matrix_of_Mt : Continuous fun x : Mt k r => (mat g * Matrix.of x : Mat k r))
  have hm : Measurable (fun x : SG hU => g * x) := by
    refine Measurable.subtype_mk ?_
    exact hc.measurable.comp measurable_subtype_coe
  have hval : (fun g : SG hU => g.1) ∘ (fun x : SG hU => g * x) = lmulM (mat g) ∘ (fun g : SG hU => g.1) := rfl
  have hmap : ((nu hU μ).map (fun x : SG hU => g * x)).map (fun g : SG hU => g.1)
      = (nu hU μ).map (fun g : SG hU => g.1) := by
    rw [Measure.map_map (me_val hU).measurable hm, hval,
      ← Measure.map_map hc.measurable (me_val hU).measurable, map_nu hμ, hμ.left _ (mat_mem g)]
  ext s hs
  have h1 := congrArg (fun m : Measure (Mt k r) => m ((fun g : SG hU => g.1) '' s)) hmap
  rwa [(me_val hU).map_apply, (me_val hU).map_apply,
    Set.preimage_image_eq s (me_val hU).injective] at h1

/- English proof (translation)
Establish `hae : AEMeasurable invM μ`. Assume the negation of the conclusion as `h`. Conclude with `hμ.ne_zero (by rw [← HI k r U μ hU hμ, Measure.map_of_not_aemeasurable h])`. Prove the components needed by the constructor for the conclusion. Use extensionality with `s hs`.

Establish `hset : (fun g : SG hU => g.1) '' s⁻¹ = invM ⁻¹' ((fun g : SG hU => g.1) '' s) ∩ {x : Mt k r | (Matrix.of x : Mat k r) ∈ U}`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨⟨(@id (SG hU) x)⁻¹, hx, rfl⟩, x.2⟩`.

Introduce and unpack `⟨⟨x, hx, hxy⟩, hy⟩`. Use `⟨⟨y, hy⟩, ?_, rfl⟩` and prove the remaining obligations. Establish `e : (@id (SG hU) ⟨y, hy⟩)⁻¹ = x`. Apply `ext'` to reduce the goal to its premises. Rewrite using `[mat_inv]`.

Use `show (Matrix.of y : Mat k r)⁻¹ = Matrix.of x.1`. Rewrite using `[show x.1 = invM y from hxy]`. Apply the tactic sequence `all_goals rfl`. Use `show (@id (SG hU) ⟨y, hy⟩)⁻¹ ∈ s`. Rewrite using `[e]`.

Conclude with `hx`. Rewrite using `[Measure.inv_apply]`. Simplify using `only [nu]`. Rewrite using `[(me_val hU).comap_apply, (me_val hU).comap_apply, hset, measure_inter_conull (t := {x : Mt k r | (Matrix.of x : Mat k r) ∈ U}) hμ.conc, ← Measure.map_apply_of_aemeasurable hae ((me_val hU).measurableSet_image.mpr hs), HI k r U μ hU hμ]`.
-/
theorem nu_inv (HI : HaarInv) {μ : Measure (Mt k r)} (hμ : IsHaarOn U μ) : (nu hU μ).IsInvInvariant := by
  have hae : AEMeasurable invM μ := by
    by_contra h
    exact hμ.ne_zero (by rw [← HI k r U μ hU hμ, Measure.map_of_not_aemeasurable h])
  constructor
  ext s hs
  have hset : (fun g : SG hU => g.1) '' s⁻¹ = invM ⁻¹' ((fun g : SG hU => g.1) '' s) ∩
      {x : Mt k r | (Matrix.of x : Mat k r) ∈ U} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(@id (SG hU) x)⁻¹, hx, rfl⟩, x.2⟩
    · rintro ⟨⟨x, hx, hxy⟩, hy⟩
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      have e : (@id (SG hU) ⟨y, hy⟩)⁻¹ = x := by
        apply ext'
        rw [mat_inv]
        show (Matrix.of y : Mat k r)⁻¹ = Matrix.of x.1
        rw [show x.1 = invM y from hxy]
        all_goals rfl
      show (@id (SG hU) ⟨y, hy⟩)⁻¹ ∈ s
      rw [e]
      exact hx
  rw [Measure.inv_apply]
  simp only [nu]
  rw [(me_val hU).comap_apply, (me_val hU).comap_apply, hset,
    measure_inter_conull (t := {x : Mt k r | (Matrix.of x : Mat k r) ∈ U}) hμ.conc,
    ← Measure.map_apply_of_aemeasurable hae ((me_val hU).measurableSet_image.mpr hs), HI k r U μ hU hμ]

end MatrixSubsetMeasurability

end ReciprocityTheory.ChartRestriction.DS.Mult1
