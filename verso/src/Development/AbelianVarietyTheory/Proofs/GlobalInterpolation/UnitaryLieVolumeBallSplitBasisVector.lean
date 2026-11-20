import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.OmegaSplit

/- English proof (translation)
Establish `e1` using `measurePreserving_prodAssoc a b (c.prod d)`. Establish `e2` using `(measurePreserving_prodAssoc b c d).symm`. Establish `e3` using `(Measure.measurePreserving_swap (μ := b) (ν := c)).prod (MeasurePreserving.id d)`. Establish `e4` using `measurePreserving_prodAssoc c b d`. Establish `e5` using `(measurePreserving_prodAssoc a c (b.prod d)).symm`.

Conclude with `e5.comp (((MeasurePreserving.id a).prod (e4.comp (e3.comp e2))).comp e1)`.
-/
theorem mp_interchange {A B C D : Type} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSpace D] (a : Measure A) (b : Measure B) (c : Measure C) (d : Measure D)
    [SFinite a] [SFinite b] [SFinite c] [SFinite d] :
    MeasurePreserving (fun x : (A × B) × (C × D) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
      ((a.prod b).prod (c.prod d)) ((a.prod c).prod (b.prod d)) := by
  have e1 := measurePreserving_prodAssoc a b (c.prod d)
  have e2 := (measurePreserving_prodAssoc b c d).symm
  have e3 := (Measure.measurePreserving_swap (μ := b) (ν := c)).prod (MeasurePreserving.id d)
  have e4 := measurePreserving_prodAssoc c b d
  have e5 := (measurePreserving_prodAssoc a c (b.prod d)).symm
  exact e5.comp (((MeasurePreserving.id a).prod (e4.comp (e3.comp e2))).comp e1)

/- English proof (translation)
Establish `h2` using `(rotation (Circle.exp (Real.pi / 2))).measurePreserving`. Establish `h3` using `Complex.volume_preserving_equiv_real_prod.symm`. Establish `h4` using `h2.comp h3`. Establish `h5 : (fun t : ℝ × ℝ => ((t.1 : ℂ) * Complex.I + Complex.I * ((t.2 : ℂ) * Complex.I))) = rotation (Circle.exp (Real.pi / 2)) ∘ Complex.measurableEquivRealProd.symm`. Use function extensionality and compare the values at `ab`.

Simplify using `[rotation_apply, Complex.measurableEquivRealProd, Complex.ext_iff]`. Rewrite using `[h5]`. Conclude with `h4`.
-/
theorem mp_diag : MeasurePreserving
    (fun t : ℝ × ℝ => ((t.1 : ℂ) * Complex.I + Complex.I * ((t.2 : ℂ) * Complex.I)))
    ((volume : Measure ℝ).prod volume) volume := by
  have h2 := (rotation (Circle.exp (Real.pi / 2))).measurePreserving
  have h3 := Complex.volume_preserving_equiv_real_prod.symm
  have h4 := h2.comp h3
  have h5 : (fun t : ℝ × ℝ => ((t.1 : ℂ) * Complex.I + Complex.I * ((t.2 : ℂ) * Complex.I))) =
      rotation (Circle.exp (Real.pi / 2)) ∘ Complex.measurableEquivRealProd.symm := by
    funext ab
    simp [rotation_apply, Complex.measurableEquivRealProd, Complex.ext_iff]
  rw [h5]
  exact h4

/- English proof (translation)
Establish `h` using `(rotation ⟨s, by simpa [Submonoid.unitSphere] using hs⟩).measurePreserving`. Conclude with `h`.
-/
theorem mp_unit (s : ℂ) (hs : ‖s‖ = 1) : MeasurePreserving (fun z : ℂ => s * z) volume volume := by
  have h := (rotation ⟨s, by simpa [Submonoid.unitSphere] using hs⟩).measurePreserving
  exact h

/- English proof (translation)
Use `set n := Fintype.card ι with hn`. Establish `hI : MeasurePreserving (fun (z : ι → ℂ) i => Complex.I * z i) volume volume` using `volume_preserving_pi fun _ => mp_unit _ Complex.norm_I`. Establish `hS : MeasurePreserving (fun (z : ι → ℂ) i => s i * (starRingEnd ℂ) (z i)) volume volume` using `volume_preserving_pi (f := fun i z => s i * (starRingEnd ℂ) z) fun i => (mp_unit _ (hs i)).comp Complex.conjLIE.measurePreserving`. Establish `hsc : MeasurePreserving (fun z : ι → ℂ => (-2 : ℝ) • z) (((2 : ℝ≥0∞) ^ n * 2 ^ n) • volume) volume`. Use `⟨measurable_const_smul _, ?_⟩` and prove the remaining obligations.

Rewrite using `[Measure.map_smul, Measure.map_addHaar_smul _ (by norm_num), smul_smul]`. Establish `hf : Module.finrank ℝ (ι → ℂ) = n * 2`. Simplify using `[Module.finrank_pi_fintype, hn]`. Establish `h1 : ENNReal.ofReal |((-2 : ℝ) ^ Module.finrank ℝ (ι → ℂ))⁻¹| = ((2 : ℝ≥0∞) ^ n * 2 ^ n)⁻¹`. Rewrite using `[hf, abs_inv, abs_pow, abs_neg, abs_two, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num), mul_two, pow_add]`.

Simplify using the standard rewrite rules. Rewrite using `[h1, ENNReal.mul_inv_cancel (by simp) (by finiteness), one_smul]`. Establish `hsh1` using `measurePreserving_add_prod (volume : Measure (ι → ℂ)) (volume : Measure (ι → ℂ))`. Establish `hsh2` using `measurePreserving_prod_add (volume : Measure (ι → ℂ)) (volume : Measure (ι → ℂ))`. Establish `hA` using `(hsh1.comp ((MeasurePreserving.id volume).prod hI)).smul_measure ((2 : ℝ≥0∞) ^ n * 2 ^ n)`.

Establish `hB` using `((MeasurePreserving.id volume).prod hS).comp (hsh2.comp ((MeasurePreserving.id (volume : Measure (ι → ℂ))).prod hsc))`. Use `haveI : SFinite (((2 : ℝ≥0∞) ^ n • volume : Measure (ι → ℂ))) := inferInstance`. Rewrite `hB` using `[Measure.prod_smul_right]`. Rewrite using `[Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]`. Use `hB.comp hA using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `z`. Use extensionality with `i`. Simplify using the standard rewrite rules. Simplify using `[map_ofNat]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mp_colrow {ι : Type} [Fintype ι] (s : ι → ℂ) (hs : ∀ i, ‖s i‖ = 1) :
    MeasurePreserving (fun z : (ι → ℂ) × (ι → ℂ) =>
      ((fun i => z.1 i + Complex.I * z.2 i : ι → ℂ),
        (fun i => s i * (starRingEnd ℂ) (z.1 i) + Complex.I * (s i * (starRingEnd ℂ) (z.2 i)) : ι → ℂ)))
      (((2 : ℝ≥0∞) ^ Fintype.card ι • volume : Measure (ι → ℂ)).prod
        ((2 : ℝ≥0∞) ^ Fintype.card ι • volume : Measure (ι → ℂ)))
      ((volume : Measure (ι → ℂ)).prod volume) := by
  set n := Fintype.card ι with hn
  have hI : MeasurePreserving (fun (z : ι → ℂ) i => Complex.I * z i) volume volume :=
    volume_preserving_pi fun _ => mp_unit _ Complex.norm_I
  have hS : MeasurePreserving (fun (z : ι → ℂ) i => s i * (starRingEnd ℂ) (z i)) volume volume :=
    volume_preserving_pi (f := fun i z => s i * (starRingEnd ℂ) z) fun i =>
      (mp_unit _ (hs i)).comp Complex.conjLIE.measurePreserving
  have hsc : MeasurePreserving (fun z : ι → ℂ => (-2 : ℝ) • z)
      (((2 : ℝ≥0∞) ^ n * 2 ^ n) • volume) volume := by
    refine ⟨measurable_const_smul _, ?_⟩
    rw [Measure.map_smul, Measure.map_addHaar_smul _ (by norm_num), smul_smul]
    have hf : Module.finrank ℝ (ι → ℂ) = n * 2 := by
      simp [Module.finrank_pi_fintype, hn]
    have h1 : ENNReal.ofReal |((-2 : ℝ) ^ Module.finrank ℝ (ι → ℂ))⁻¹| = ((2 : ℝ≥0∞) ^ n * 2 ^ n)⁻¹ := by
      rw [hf, abs_inv, abs_pow, abs_neg, abs_two, ENNReal.ofReal_inv_of_pos (by positivity),
        ENNReal.ofReal_pow (by norm_num), mul_two, pow_add]
      simp
    rw [h1, ENNReal.mul_inv_cancel (by simp) (by finiteness), one_smul]
  have hsh1 := measurePreserving_add_prod (volume : Measure (ι → ℂ)) (volume : Measure (ι → ℂ))
  have hsh2 := measurePreserving_prod_add (volume : Measure (ι → ℂ)) (volume : Measure (ι → ℂ))
  have hA := (hsh1.comp ((MeasurePreserving.id volume).prod hI)).smul_measure ((2 : ℝ≥0∞) ^ n * 2 ^ n)
  have hB := ((MeasurePreserving.id volume).prod hS).comp
    (hsh2.comp ((MeasurePreserving.id (volume : Measure (ι → ℂ))).prod hsc))
  haveI : SFinite (((2 : ℝ≥0∞) ^ n • volume : Measure (ι → ℂ))) := inferInstance
  rw [Measure.prod_smul_right] at hB
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  convert hB.comp hA using 1
  funext z
  ext i
  · simp
  · simp [map_ofNat]
    ring

def idxEquiv (ι : Type) : (Unit ⊕ (ι ⊕ ι)) ⊕ (ι × ι) ≃ Option ι × Option ι where
  toFun x := match x with
    | .inl (.inl _) => (none, none)
    | .inl (.inr (.inl a)) => (some a, none)
    | .inl (.inr (.inr b)) => (none, some b)
    | .inr (a, b) => (some a, some b)
  invFun y := match y with
    | (none, none) => .inl (.inl ())
    | (some a, none) => .inl (.inr (.inl a))
    | (none, some b) => .inl (.inr (.inr b))
    | (some a, some b) => .inr (a, b)
  left_inv := by rintro ((_ | _ | _) | ⟨_, _⟩) <;> rfl
  right_inv := by rintro ⟨_ | _, _ | _⟩ <;> rfl

/- English proof (translation)
Establish `h1` using `(volume_preserving_funUnique Unit ℂ).symm`. Establish `h2` using `volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : ι ⊕ ι => ℂ)`. Establish `h3` using `volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Unit ⊕ (ι ⊕ ι) => ℂ)`. Establish `h4` using `volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : (Unit ⊕ (ι ⊕ ι)) ⊕ (ι × ι) => ℂ)`. Establish `h5` using `volume_measurePreserving_piCongrLeft (fun _ : κ × κ => ℂ) ((idxEquiv ι).trans (e.prodCongr e))`.

Use `⟨_, h5.comp (h4.comp ((h3.comp (h1.prod h2)).prod (MeasurePreserving.id volume))), ?_⟩` and prove the remaining obligations. Introduce `x`. Establish `key` using `fun y i => MeasurableEquiv.piCongrLeft_apply_apply ((idxEquiv ι).trans (e.prodCongr e)) (β := fun _ : κ × κ => ℂ) y i`. Conclude with `⟨key _ (.inl (.inl ())), fun a => key _ (.inl (.inr (.inl a))), fun b => key _ (.inl (.inr (.inr b))), fun a b => key _ (.inr (a, b))⟩`.
-/
theorem exists_assemble {ι κ : Type} [Fintype ι] [Fintype κ] (e : Option ι ≃ κ) :
    ∃ f : (ℂ × ((ι → ℂ) × (ι → ℂ))) × (ι × ι → ℂ) → (κ × κ → ℂ),
      MeasurePreserving f (((volume : Measure ℂ).prod
        ((volume : Measure (ι → ℂ)).prod volume)).prod volume) volume ∧
      ∀ x, f x (e none, e none) = x.1.1 ∧ (∀ a, f x (e (some a), e none) = x.1.2.1 a) ∧
        (∀ b, f x (e none, e (some b)) = x.1.2.2 b) ∧
        ∀ a b, f x (e (some a), e (some b)) = x.2 (a, b) := by
  have h1 := (volume_preserving_funUnique Unit ℂ).symm
  have h2 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : ι ⊕ ι => ℂ)
  have h3 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Unit ⊕ (ι ⊕ ι) => ℂ)
  have h4 := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : (Unit ⊕ (ι ⊕ ι)) ⊕ (ι × ι) => ℂ)
  have h5 := volume_measurePreserving_piCongrLeft (fun _ : κ × κ => ℂ)
    ((idxEquiv ι).trans (e.prodCongr e))
  refine ⟨_, h5.comp (h4.comp ((h3.comp (h1.prod h2)).prod (MeasurePreserving.id volume))), ?_⟩
  intro x
  have key := fun y i => MeasurableEquiv.piCongrLeft_apply_apply
    ((idxEquiv ι).trans (e.prodCongr e)) (β := fun _ : κ × κ => ℂ) y i
  exact ⟨key _ (.inl (.inl ())), fun a => key _ (.inl (.inr (.inl a))),
    fun b => key _ (.inl (.inr (.inr b))), fun a b => key _ (.inr (a, b))⟩

variable {P Q P' Q' : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`. Simplify using `[Formalism.UG.Jpq, sg, Matrix.one_apply, Matrix.diagonal_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem Jpq_eq (P Q : ℕ) : Formalism.UG.Jpq P Q = Matrix.diagonal fun i => (sg i : ℂ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Formalism.UG.Jpq, sg, Matrix.one_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

/- English proof (translation)
Apply the tactic sequence `rcases sg_eq i with h | h <;> rw [h] <;> simp`.
-/
theorem sg_mul_self (i : Fin P ⊕ Fin Q) : (sg i : ℂ) * sg i = 1 := by
  rcases sg_eq i with h | h <;> rw [h] <;> simp

/- English proof (translation)
Apply the tactic sequence `rcases sg_eq i with h | h <;> rw [h] <;> simp`.
-/
theorem norm_sg (i : Fin P ⊕ Fin Q) : ‖(sg i : ℂ)‖ = 1 := by
  rcases sg_eq i with h | h <;> rw [h] <;> simp

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Xᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0 ↔ _`. Rewrite using `[Jpq_eq, ← Matrix.ext_iff]`. Use `forall_congr' fun a => forall_congr' fun b => ?_` and prove the remaining obligations. Simplify using `only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, conjTranspose_apply, Matrix.zero_apply, Complex.star_def]`. Establish `ha` using `sg_mul_self a`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Take the linear combination `(sg a : ℂ) * h - X a b * ha`. Introduce `h`. Take the linear combination `(sg a : ℂ) * h - (sg b : ℂ) * (starRingEnd ℂ) (X b a) * ha`.
-/
theorem mem_lieU_iff (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    X ∈ lieU P Q ↔ ∀ a b, X a b = -((sg a : ℂ) * sg b) * (starRingEnd ℂ) (X b a) := by
  change Xᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X = 0 ↔ _
  rw [Jpq_eq, ← Matrix.ext_iff]
  refine forall_congr' fun a => forall_congr' fun b => ?_
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, conjTranspose_apply,
    Matrix.zero_apply, Complex.star_def]
  have ha := sg_mul_self a
  constructor
  · intro h
    linear_combination (sg a : ℂ) * h - X a b * ha
  · intro h
    linear_combination (sg a : ℂ) * h - (sg b : ℂ) * (starRingEnd ℂ) (X b a) * ha

def coord (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (he : SignCompat e) :
    lieU P Q →ₗ[ℝ] (ℝ × Sp P' Q') × lieU P' Q' where
  toFun X := (((X.val (e none) (e none)).im, fun a => X.val (e (some a)) (e none)),
    ⟨Matrix.of fun a b => X.val (e (some a)) (e (some b)), by
      rw [mem_lieU_iff]
      intro a b
      have := (mem_lieU_iff _).1 X.2 (e (some a)) (e (some b))
      rw [he, he] at this
      exact this⟩)
  map_add' X Y := by
    refine Prod.ext (Prod.ext ?_ rfl) rfl
    simp
  map_smul' c X := by
    refine Prod.ext (Prod.ext ?_ rfl) rfl
    simp

/- English proof (translation)
Establish `h` using `(mem_lieU_iff _).1 X.2 k k`. Rewrite `h` using `[sg_mul_self]`. Establish `h2` using `congrArg Complex.re h`. Simplify using `at h2`. Apply the tactic sequence `apply Complex.ext <;> simp`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem diag_eq (X : lieU P Q) (k : Fin P ⊕ Fin Q) :
    X.val k k = ((X.val k k).im : ℂ) * Complex.I := by
  have h := (mem_lieU_iff _).1 X.2 k k
  rw [sg_mul_self] at h
  have h2 := congrArg Complex.re h
  simp at h2
  apply Complex.ext <;> simp
  linarith

/- English proof (translation)
The claim follows from `(mem_lieU_iff _).1 X.2 _ _`.
-/
theorem row_eq (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (X : lieU P Q) (b) :
    X.val (e none) (e (some b)) = -((sg (e none) : ℂ) * sg (e (some b))) *
      (starRingEnd ℂ) (X.val (e (some b)) (e none)) :=
  (mem_lieU_iff _).1 X.2 _ _

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `X h`. Establish `h1 : (X.val (e none) (e none)).im = 0` using `congrArg (fun t => t.1.1) h`. Establish `h2 : ∀ a, X.val (e (some a)) (e none) = 0` using `fun a => congrArg (fun t => t.1.2 a) h`. Establish `h3 : ∀ a b, X.val (e (some a)) (e (some b)) = 0` using `fun a b => congrArg (fun t => t.2.val a b) h`.

Use extensionality with `i j`. Take `⟨i, rfl⟩` from `e.surjective i`. Take `⟨j, rfl⟩` from `e.surjective j`. Apply the tactic sequence `rcases i with _ | i <;> rcases j with _ | j`. Rewrite using `[diag_eq, h1]`.

Simplify using the standard rewrite rules. Rewrite using `[row_eq, h2]`. Simplify using the standard rewrite rules. Conclude with `h2 i`. Conclude with `h3 i j`.
-/
theorem coord_injective (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (he : SignCompat e) :
    Function.Injective (coord e he) := by
  rw [injective_iff_map_eq_zero]
  intro X h
  have h1 : (X.val (e none) (e none)).im = 0 := congrArg (fun t => t.1.1) h
  have h2 : ∀ a, X.val (e (some a)) (e none) = 0 := fun a => congrArg (fun t => t.1.2 a) h
  have h3 : ∀ a b, X.val (e (some a)) (e (some b)) = 0 := fun a b =>
    congrArg (fun t => t.2.val a b) h
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases i with _ | i <;> rcases j with _ | j
  · rw [diag_eq, h1]; simp
  · rw [row_eq, h2]; simp
  · exact h2 i
  · exact h3 i j

/- English proof (translation)
Introduce and unpack `⟨⟨θ, z⟩, Y⟩`. Set `g : Option (Fin P' ⊕ Fin Q') → Option (Fin P' ⊕ Fin Q') → ℂ` to `fun i j => match i, j with`. Consider the case `none, none => (θ : ℂ) * Complex.I`. Consider the case `some a, none => z a`. Consider the case `none, some b => -((sg (e none) : ℂ) * sg (e (some b))) * (starRingEnd ℂ) (z b)`.

Consider the case `some a, some b => Y.val a b`. Use `⟨⟨Matrix.of fun i j => g (e.symm i) (e.symm j), ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_lieU_iff]`. Introduce `i j`. Take `⟨i, rfl⟩` from `e.surjective i`.

Take `⟨j, rfl⟩` from `e.surjective j`. Simplify using `only [Matrix.of_apply, Equiv.symm_apply_apply]`. Apply the tactic sequence `rcases i with _ | i <;> rcases j with _ | j`. Rewrite using `[sg_mul_self]`. Simplify using `[g]`.

Both sides reduce to the same expression. Establish `h1` using `sg_mul_self (e none)`. Establish `h2` using `sg_mul_self (e (some i))`. Simplify using `only [g, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_conj]`. Take the linear combination `(-z i) * h1 - z i * (sg (e none) : ℂ) * (sg (e none) : ℂ) * h2`.

Rewrite using `[he, he]`. Conclude with `(mem_lieU_iff _).1 Y.2 i j`. Use `Prod.ext (Prod.ext ?_ ?_) ?_` and prove the remaining obligations. Simplify using `[coord, g]`. Use function extensionality and compare the values at `a`.

Simplify using `[coord, g]`. Use extensionality with `a b`. Simplify using `[coord, g]`.
-/
theorem coord_surjective (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (he : SignCompat e) :
    Function.Surjective (coord e he) := by
  rintro ⟨⟨θ, z⟩, Y⟩
  let g : Option (Fin P' ⊕ Fin Q') → Option (Fin P' ⊕ Fin Q') → ℂ := fun i j =>
    match i, j with
    | none, none => (θ : ℂ) * Complex.I
    | some a, none => z a
    | none, some b => -((sg (e none) : ℂ) * sg (e (some b))) * (starRingEnd ℂ) (z b)
    | some a, some b => Y.val a b
  refine ⟨⟨Matrix.of fun i j => g (e.symm i) (e.symm j), ?_⟩, ?_⟩
  · rw [mem_lieU_iff]
    intro i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    simp only [Matrix.of_apply, Equiv.symm_apply_apply]
    rcases i with _ | i <;> rcases j with _ | j
    · rw [sg_mul_self]; simp [g]
    · rfl
    · have h1 := sg_mul_self (e none)
      have h2 := sg_mul_self (e (some i))
      simp only [g, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_conj]
      linear_combination (-z i) * h1 - z i * (sg (e none) : ℂ) * (sg (e none) : ℂ) * h2
    · rw [he, he]
      exact (mem_lieU_iff _).1 Y.2 i j
  · refine Prod.ext (Prod.ext ?_ ?_) ?_
    · simp [coord, g]
    · funext a; simp [coord, g]
    · ext a b; simp [coord, g]

/- English proof (translation)
Establish `h1 : ‖X.val (e none) (e none)‖ = |(X.val (e none) (e none)).im|` using `by conv_lhs => rw [diag_eq]`. Simplify using the standard rewrite rules. Establish `h2 : ∀ b, ‖X.val (e none) (e (some b))‖ = ‖X.val (e (some b)) (e none)‖`. Introduce `b`. Rewrite using `[row_eq, norm_mul, norm_neg, norm_mul, norm_sg, norm_sg]`.

Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `∑ i, ∑ j, ‖X.val i j‖ = |(X.val (e none) (e none)).im| + 2 * ∑ a, ‖X.val (e (some a)) (e none)‖ + ∑ a, ∑ b, ‖X.val (e (some a)) (e (some b))‖`. Establish `h3 : ∀ i, ∑ j, ‖X.val i j‖ = ‖X.val i (e none)‖ + ∑ b, ‖X.val i (e (some b))‖`. Introduce `i`. Rewrite using `[← e.sum_comp, Fintype.sum_option]`.

Simplify using `only [h3]`. Rewrite using `[← e.sum_comp, Fintype.sum_option, Finset.sum_add_distrib, h1]`. Simplify using `only [h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem matrixEntryAbsSum_unitaryLie_coordinates_split (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (he : SignCompat e) (X : lieU P Q) :
    l1 X.val = tanGauge (coord e he X).1 + l1 (coord e he X).2.val := by
  have h1 : ‖X.val (e none) (e none)‖ = |(X.val (e none) (e none)).im| := by
    conv_lhs => rw [diag_eq]
    simp
  have h2 : ∀ b, ‖X.val (e none) (e (some b))‖ = ‖X.val (e (some b)) (e none)‖ := by
    intro b
    rw [row_eq, norm_mul, norm_neg, norm_mul, norm_sg, norm_sg]; simp
  change ∑ i, ∑ j, ‖X.val i j‖ = |(X.val (e none) (e none)).im| +
    2 * ∑ a, ‖X.val (e (some a)) (e none)‖ + ∑ a, ∑ b, ‖X.val (e (some a)) (e (some b))‖
  have h3 : ∀ i, ∑ j, ‖X.val i j‖ = ‖X.val i (e none)‖ + ∑ b, ‖X.val i (e (some b))‖ := by
    intro i
    rw [← e.sum_comp, Fintype.sum_option]
  simp only [h3]
  rw [← e.sum_comp, Fintype.sum_option, Finset.sum_add_distrib, h1]
  simp only [h2]
  ring

/- English proof (translation)
Introduce `P Q P' Q' e he lam lam' hl hl' r`. Establish `: BorelSpace (lieU P Q)` using `⟨rfl⟩`. Establish `: BorelSpace (lieU P' Q')` using `⟨rfl⟩`. Establish `: SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)` using `inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))`. Establish `: SecondCountableTopology (Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ)` using `inferInstanceAs (SecondCountableTopology ((Fin P' ⊕ Fin Q') → (Fin P' ⊕ Fin Q') → ℂ))`.

Establish `: SecondCountableTopology (lieU P Q)` using `TopologicalSpace.Subtype.secondCountableTopology _`. Establish `: SecondCountableTopology (lieU P' Q')` using `TopologicalSpace.Subtype.secondCountableTopology _`. Establish `: LocallyCompactSpace (lieU P Q)` using `LocallyCompactSpace.of_finiteDimensional_of_complete ℝ _`. Establish `: LocallyCompactSpace (lieU P' Q')` using `LocallyCompactSpace.of_finiteDimensional_of_complete ℝ _`. Take `⟨h1, h2⟩` from `hl'`.

Set `D : lieU P Q ≃L[ℝ] (ℝ × Sp P' Q') × lieU P' Q'` to `(LinearEquiv.ofBijective (coord e he) ⟨coord_injective e he, coord_surjective e he⟩).toContinuousLinearEquiv`. Establish `hD : ∀ X, D X = coord e he X` using `fun _ => rfl`. Establish `hn : Fintype.card (Fin P' ⊕ Fin Q') = P' + Q'` using `by simp`. Set `μ : Measure (Sp P' Q')` to `(2 : ℝ≥0∞) ^ Fintype.card (Fin P' ⊕ Fin Q') • volume`. Establish `: μ.IsAddHaarMeasure` using `Measure.IsAddHaarMeasure.smul _ (by simp) (by finiteness)`.

Set `ν : Measure ((ℝ × Sp P' Q') × lieU P' Q')` to `((volume : Measure ℝ).prod μ).prod lam'`. Establish `: ((volume : Measure ℝ).prod μ).IsAddHaarMeasure` using `Measure.prod.instIsAddHaarMeasure _ _`. Establish `: ν.IsAddHaarMeasure` using `Measure.prod.instIsAddHaarMeasure _ _`. Establish `hc : ∀ A B : ℕ, Continuous (fun ab : lieU A B × lieU A B => entries ((ab.1 : Matrix (Fin A ⊕ Fin B) (Fin A ⊕ Fin B) ℂ) + Complex.I • (ab.2 : Matrix (Fin A ⊕ Fin B) (Fin A ⊕ Fin B) ℂ)))`. Introduce `A B`.

Use `continuous_pi fun ij => ?_` and prove the remaining obligations. Conclude with `((continuous_subtype_val.comp continuous_fst).add ((continuous_subtype_val.comp continuous_snd).const_smul Complex.I)).matrix_elem ij.1 ij.2`. Establish `hm : Measurable D.symm` using `D.symm.continuous.measurable`. Establish `hω : IsOmegaLeb (ν.map D.symm)`. Use `⟨D.symm.isAddHaarMeasure_map ν, ?_⟩` and prove the remaining obligations.

Take `⟨f, hf, hf'⟩` from `exists_assemble e`. Establish `m1` using `mp_interchange ((volume : Measure ℝ).prod μ) lam' ((volume : Measure ℝ).prod μ) lam'`. Establish `m2` using `mp_interchange (volume : Measure ℝ) μ (volume : Measure ℝ) μ`. Establish `m3` using `mp_colrow (fun b => -((sg (e none) : ℂ) * sg (e (some b)))) (fun b => by rw [norm_neg, norm_mul, norm_sg, norm_sg, mul_one])`. Establish `m4 : MeasurePreserving _ (lam'.prod lam') volume` using `⟨(hc P' Q').measurable, h2⟩`.

Establish `m5` using `hf.comp ((((mp_diag.prod m3).comp m2).prod m4).comp m1)`. Rewrite using `[Measure.map_prod_map _ _ hm hm, Measure.map_map (hc P Q).measurable (hm.prodMap hm), ← m5.map_eq]`. Use `congr 1`. Use function extensionality and compare the values at `⟨x, y⟩ ⟨i, j⟩`. Take `⟨X, rfl⟩` from `D.surjective x`.

Take `⟨Y, rfl⟩` from `D.surjective y`. Take `⟨i, rfl⟩` from `e.surjective i`. Take `⟨j, rfl⟩` from `e.surjective j`. Simplify using `only [Function.comp_apply, Prod.map_apply, ContinuousLinearEquiv.symm_apply_apply]`. Express the relevant statement in the definitionally equal form `X.val (e i) (e j) + Complex.I * Y.val (e i) (e j) = _`.

Apply the tactic sequence `rcases i with _ | i <;> rcases j with _ | j`. Rewrite using `[(hf' _).1, diag_eq X, diag_eq Y]`. Both sides reduce to the same expression. Rewrite using `[(hf' _).2.2.1, row_eq e X, row_eq e Y]`. Both sides reduce to the same expression.

Rewrite using `[(hf' _).2.1]`. Both sides reduce to the same expression. Rewrite using `[(hf' _).2.2.2]`. Both sides reduce to the same expression. Establish `hopen : IsOpen (ballU P Q r)` using `isOpen_lt (continuous_matrixEntryAbsSum.comp continuous_subtype_val) continuous_const`.

Rewrite using `[GlobalTheory.CompactDualUnique.isOmegaLeb_unique hl hω, Measure.map_apply hm hopen.measurableSet]`. Establish `hset : D.symm ⁻¹' ballU P Q r = {p | tanGauge p.1 + l1 (p.2 : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) < r}`. Use extensionality with `p`. Take `⟨X, rfl⟩` from `D.surjective p`. Rewrite using `[Set.mem_preimage, D.symm_apply_apply]`.

Express the relevant statement in the definitionally equal form `l1 X.val < r ↔ _`. Rewrite using `[matrixEntryAbsSum_unitaryLie_coordinates_split e he]`. Both sides reduce to the same expression. Rewrite using `[hset]`. Simplify using `only [ν, μ, hn]`.

Rewrite using `[Measure.prod_smul_right, Measure.prod_smul_left, Measure.smul_apply, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem omega_split : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)), SignCompat e → ∀ (lam : Measure (lieU P Q)) (lam' : Measure (lieU P' Q')), IsOmegaLeb lam → IsOmegaLeb lam' → ∀ r : ℝ, lam (ballU P Q r) = (2 : ℝ≥0∞) ^ (P' + Q') * ((volume : Measure (ℝ × Sp P' Q')).prod lam') {p | tanGauge p.1 + l1 (p.2 : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) < r} := by
  intro P Q P' Q' e he lam lam' hl hl' r
  have : BorelSpace (lieU P Q) := ⟨rfl⟩
  have : BorelSpace (lieU P' Q') := ⟨rfl⟩
  have : SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  have : SecondCountableTopology (Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P' ⊕ Fin Q') → (Fin P' ⊕ Fin Q') → ℂ))
  have : SecondCountableTopology (lieU P Q) := TopologicalSpace.Subtype.secondCountableTopology _
  have : SecondCountableTopology (lieU P' Q') := TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (lieU P Q) := LocallyCompactSpace.of_finiteDimensional_of_complete ℝ _
  have : LocallyCompactSpace (lieU P' Q') := LocallyCompactSpace.of_finiteDimensional_of_complete ℝ _
  obtain ⟨h1, h2⟩ := hl'
  let D : lieU P Q ≃L[ℝ] (ℝ × Sp P' Q') × lieU P' Q' :=
    (LinearEquiv.ofBijective (coord e he)
      ⟨coord_injective e he, coord_surjective e he⟩).toContinuousLinearEquiv
  have hD : ∀ X, D X = coord e he X := fun _ => rfl
  have hn : Fintype.card (Fin P' ⊕ Fin Q') = P' + Q' := by simp
  let μ : Measure (Sp P' Q') := (2 : ℝ≥0∞) ^ Fintype.card (Fin P' ⊕ Fin Q') • volume
  have : μ.IsAddHaarMeasure := Measure.IsAddHaarMeasure.smul _ (by simp) (by finiteness)
  let ν : Measure ((ℝ × Sp P' Q') × lieU P' Q') := ((volume : Measure ℝ).prod μ).prod lam'
  have : ((volume : Measure ℝ).prod μ).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have : ν.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hc : ∀ A B : ℕ, Continuous (fun ab : lieU A B × lieU A B =>
      entries ((ab.1 : Matrix (Fin A ⊕ Fin B) (Fin A ⊕ Fin B) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin A ⊕ Fin B) (Fin A ⊕ Fin B) ℂ))) := by
    intro A B
    refine continuous_pi fun ij => ?_
    exact ((continuous_subtype_val.comp continuous_fst).add
      ((continuous_subtype_val.comp continuous_snd).const_smul Complex.I)).matrix_elem ij.1 ij.2
  have hm : Measurable D.symm := D.symm.continuous.measurable
  have hω : IsOmegaLeb (ν.map D.symm) := by
    refine ⟨D.symm.isAddHaarMeasure_map ν, ?_⟩
    obtain ⟨f, hf, hf'⟩ := exists_assemble e
    have m1 := mp_interchange ((volume : Measure ℝ).prod μ) lam' ((volume : Measure ℝ).prod μ) lam'
    have m2 := mp_interchange (volume : Measure ℝ) μ (volume : Measure ℝ) μ
    have m3 := mp_colrow (fun b => -((sg (e none) : ℂ) * sg (e (some b))))
      (fun b => by rw [norm_neg, norm_mul, norm_sg, norm_sg, mul_one])
    have m4 : MeasurePreserving _ (lam'.prod lam') volume := ⟨(hc P' Q').measurable, h2⟩
    have m5 := hf.comp ((((mp_diag.prod m3).comp m2).prod m4).comp m1)
    rw [Measure.map_prod_map _ _ hm hm, Measure.map_map (hc P Q).measurable (hm.prodMap hm),
      ← m5.map_eq]
    congr 1
    funext ⟨x, y⟩ ⟨i, j⟩
    obtain ⟨X, rfl⟩ := D.surjective x
    obtain ⟨Y, rfl⟩ := D.surjective y
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    simp only [Function.comp_apply, Prod.map_apply, ContinuousLinearEquiv.symm_apply_apply]
    change X.val (e i) (e j) + Complex.I * Y.val (e i) (e j) = _
    rcases i with _ | i <;> rcases j with _ | j
    · rw [(hf' _).1, diag_eq X, diag_eq Y]; rfl
    · rw [(hf' _).2.2.1, row_eq e X, row_eq e Y]; rfl
    · rw [(hf' _).2.1]; rfl
    · rw [(hf' _).2.2.2]; rfl
  have hopen : IsOpen (ballU P Q r) :=
    isOpen_lt (continuous_matrixEntryAbsSum.comp continuous_subtype_val) continuous_const
  rw [GlobalTheory.CompactDualUnique.isOmegaLeb_unique hl hω, Measure.map_apply hm hopen.measurableSet]
  have hset : D.symm ⁻¹' ballU P Q r = {p | tanGauge p.1 +
      l1 (p.2 : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) < r} := by
    ext p
    obtain ⟨X, rfl⟩ := D.surjective p
    rw [Set.mem_preimage, D.symm_apply_apply]
    change l1 X.val < r ↔ _
    rw [matrixEntryAbsSum_unitaryLie_coordinates_split e he]
    rfl
  rw [hset]
  simp only [ν, μ, hn]
  rw [Measure.prod_smul_right, Measure.prod_smul_left, Measure.smul_apply, smul_eq_mul]
  rfl

end GlobalTheory.OmegaSplit
