import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarEventuallyEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopologyStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open Filter Topology

namespace GlobalTheory.KSp.ParNear

variable {E : Type} [Field E] {ν : Type} [Fintype ν] [DecidableEq ν]

/- English proof (translation)
Rewrite using `[← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N, h, fromBlocks_multiply]`. Simplify using the standard rewrite rules.
-/
theorem toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero (M N : Matrix (ν ⊕ ν) (ν ⊕ ν) E) (h : N.toBlocks₂₁ = 0) :
    (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ := by
  rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N, h, fromBlocks_multiply]
  simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[toBlocks₁₁, one_apply]`.
-/
theorem toBlocks₁₁_one' : (1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₁₁ = 1 := by
  ext i j; simp [toBlocks₁₁, one_apply]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[toBlocks₁₂, one_apply]`.
-/
theorem toBlocks₁₂_one' : (1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₁₂ = 0 := by
  ext i j; simp [toBlocks₁₂, one_apply]

variable {F : Type} [Field F] [Algebra F E] (c : E →ₐ[F] E) {α : Type} [Fintype α] [DecidableEq α]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_one : mat c (1 : UG c (stdJ ν E)) = 1 := rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(((g * g⁻¹ : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = 1`. Rewrite using `[mul_inv_cancel]`. Both sides reduce to the same expression.
-/
theorem mat_mul_mat_inv (g : UG c (stdJ ν E)) : mat c g * mat c g⁻¹ = 1 := by
  change (((g * g⁻¹ : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = 1
  rw [mul_inv_cancel]; rfl

/- English proof (translation)
Simplify using `[pr, form, GlobalTheory.WeilM.hTens]`.
-/
theorem pr_zero_right (Q : Matrix α α E) (x : Matrix α ν E) : pr c Q x 0 = 0 := by
  simp [pr, form, GlobalTheory.WeilM.hTens]

variable [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing E]

/- English proof (translation)
The claim follows from `Units.continuous_val.comp continuous_subtype_val`.
-/
theorem continuous_mat : Continuous fun g : UG c (stdJ ν E) => mat c g :=
  Units.continuous_val.comp continuous_subtype_val

/- English proof (translation)
The claim follows from `Units.continuous_coe_inv.comp continuous_subtype_val`.
-/
theorem continuous_mat_inv : Continuous fun g : UG c (stdJ ν E) => mat c g⁻¹ :=
  Units.continuous_coe_inv.comp continuous_subtype_val

/- English proof (translation)
Simplify using `only [pr, form, GlobalTheory.WeilM.hTens]`. Use `continuous_const.mul (htr.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun l _ => ?_))` and prove the remaining obligations. Use `Continuous.mul (Continuous.mul (Continuous.mul ?_ continuous_const) continuous_const) (hc.comp ?_)` and prove the remaining obligations. Break down `j with j | j` into its components or cases. Conclude with `continuous_fst.matrix_elem i j`.

Conclude with `continuous_const`. Break down `l with l | l` into its components or cases. Conclude with `continuous_const`. Conclude with `continuous_snd.matrix_elem k l`.
-/
theorem continuous_pr (hc : Continuous c) (htr : Continuous (Algebra.trace F E)) [ContinuousMul F] (Q : Matrix α α E) :
    Continuous fun p : Matrix α ν E × Matrix α ν E => pr c Q p.1 p.2 := by
  simp only [pr, form, GlobalTheory.WeilM.hTens]
  refine continuous_const.mul (htr.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun l _ => ?_))
  refine Continuous.mul (Continuous.mul (Continuous.mul ?_ continuous_const) continuous_const) (hc.comp ?_)
  · rcases j with j | j
    · exact continuous_fst.matrix_elem i j
    · exact continuous_const
  · rcases l with l | l
    · exact continuous_const
    · exact continuous_snd.matrix_elem k l

/- English proof (translation)
Establish `h` using `(continuous_pr (ν := ν) c hc htr Q).comp (hf.prodMk hg)`. Conclude with `h`.
-/
theorem continuous_pr_comp (hc : Continuous c) (htr : Continuous (Algebra.trace F E)) [ContinuousMul F] (Q : Matrix α α E)
    {X : Type} [TopologicalSpace X] {f g : X → Matrix α ν E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => pr c Q (f x) (g x) := by
  have h := (continuous_pr (ν := ν) c hc htr Q).comp (hf.prodMk hg)
  exact h

end GlobalTheory.KSp.ParNear

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q _ ψ hψ _ _ χ hχ _ φ hφ`. Take `⟨-, htop, -, -, hcc, -, htr, -⟩` from `GlobalTheory.T.quadExt_topological_properties F E c δ hE`. Use `haveI := htop`. Use `haveI := GlobalTheory.WeilM.nonarch_field F`. Establish `hψl` using `GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ`.

Establish `hφl : IsLocallyConstant φ` using `hφ.1`. Establish `hK : IsCompact (tsupport φ)` using `hφ.2`. Establish `hA : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₁₁` using `continuous_pi fun i => continuous_pi fun j => (GlobalTheory.KSp.ParNear.continuous_mat c).matrix_elem _ _`. Establish `hB : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₁₂` using `continuous_pi fun i => continuous_pi fun j => (GlobalTheory.KSp.ParNear.continuous_mat c).matrix_elem _ _`. Establish `hA' : Continuous fun g : UG c (stdJ ν E) => (mat c g⁻¹).toBlocks₁₁` using `continuous_pi fun i => continuous_pi fun j => (GlobalTheory.KSp.ParNear.continuous_mat_inv c).matrix_elem _ _`.

Establish `hi : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), sc F χ (Fintype.card α) (mat c g).toBlocks₁₁.det = 1`. Establish `ht : Tendsto (fun g : UG c (stdJ ν E) => (mat c g).toBlocks₁₁.det) (𝓝 1) (𝓝 1)`. Use `hA.matrix_det.tendsto 1` as an intermediate fact. Rewrite `this` using `[GlobalTheory.KSp.ParNear.mat_one, GlobalTheory.KSp.ParNear.toBlocks₁₁_one', det_one]`. Then use the resulting hypothesis. Conclude with `ht.eventually (GlobalTheory.T.unitaryCharacterAbsScalar_eventually_eq_one F E c δ hE _ χ hχ)`.

Establish `hii : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), ∀ x ∈ tsupport φ, ψ (2⁻¹ * pr c Q (x * (mat c g).toBlocks₁₁) (x * (mat c g).toBlocks₁₂)) * φ (x * (mat c g).toBlocks₁₁) = φ x`. Use `hK.eventually_forall_of_forall_eventually fun x _ => ?_` and prove the remaining obligations. Establish `hP : Continuous fun p : UG c (stdJ ν E) × Matrix α ν E => pr c Q (p.2 * (mat c p.1).toBlocks₁₁) (p.2 * (mat c p.1).toBlocks₁₂)` using `GlobalTheory.KSp.ParNear.continuous_pr_comp c hcc htr Q (continuous_snd.matrix_mul (hA.comp continuous_fst)) (continuous_snd.matrix_mul (hB.comp continuous_fst))`. Establish `hP2 : Continuous fun p : UG c (stdJ ν E) × Matrix α ν E => (2 : F)⁻¹ * pr c Q (p.2 * (mat c p.1).toBlocks₁₁) (p.2 * (mat c p.1).toBlocks₁₂)` using `continuous_const.mul hP`. Establish `h1 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => ψ (2⁻¹ * pr c Q (p.2 * (mat c p.1).toBlocks₁₁) (p.2 * (mat c p.1).toBlocks₁₂))` using `hψl.comp_continuous hP2`.

Establish `h2 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ (p.2 * (mat c p.1).toBlocks₁₁)` using `hφl.comp_continuous (continuous_snd.matrix_mul (hA.comp continuous_fst))`. Establish `h3 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ p.2` using `hφl.comp_continuous continuous_snd`. Use `filter_upwards [h1.eventually_eq (1, x), h2.eventually_eq (1, x), h3.eventually_eq (1, x)] with p e1 e2 e3`. Rewrite using `[e1, e2, e3, GlobalTheory.KSp.ParNear.mat_one, GlobalTheory.KSp.ParNear.toBlocks₁₁_one', GlobalTheory.KSp.ParNear.toBlocks₁₂_one', Matrix.mul_one, Matrix.mul_zero, GlobalTheory.KSp.ParNear.pr_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul]`. Establish `hiii : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), ∀ y ∈ tsupport φ, φ (y * (mat c g⁻¹).toBlocks₁₁) = φ y`.

Use `hK.eventually_forall_of_forall_eventually fun y _ => ?_` and prove the remaining obligations. Establish `h2 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ (p.2 * (mat c p.1⁻¹).toBlocks₁₁)` using `hφl.comp_continuous (continuous_snd.matrix_mul (hA'.comp continuous_fst))`. Establish `h3 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ p.2` using `hφl.comp_continuous continuous_snd`. Use `filter_upwards [h2.eventually_eq (1, y), h3.eventually_eq (1, y)] with p e2 e3`. Rewrite using `[e2, e3, inv_one, GlobalTheory.KSp.ParNear.mat_one, GlobalTheory.KSp.ParNear.toBlocks₁₁_one', Matrix.mul_one]`.

Use `filter_upwards [hi, hii, hiii] with g hg1 hg2 hg3 hg`. Establish `hinv : (mat c g).toBlocks₁₁ * (mat c g⁻¹).toBlocks₁₁ = 1`. Rewrite using `[← GlobalTheory.KSp.ParNear.toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero _ _ ((GlobalTheory.KSp.mem_sieg c).mp ((sieg c ν).inv_mem hg)), GlobalTheory.KSp.ParNear.mat_mul_mat_inv, GlobalTheory.KSp.ParNear.toBlocks₁₁_one']`. Use function extensionality and compare the values at `x`. Simplify using `only [parFun]`.

Rewrite using `[hg1, one_mul]`. Distinguish the cases in `hx : x ∈ tsupport φ`. Conclude with `hg2 x hx`. Rewrite using `[image_eq_zero_of_notMem_tsupport hx]`. Assume the negation of the conclusion as `hne`.

Establish `hne' : φ (x * (mat c g).toBlocks₁₁) ≠ 0` using `right_ne_zero_of_mul hne`. Establish `hy : x * (mat c g).toBlocks₁₁ ∈ tsupport φ` using `subset_tsupport _ hne'`. Establish `e` using `hg3 _ hy`. Rewrite `e` using `[Matrix.mul_assoc, hinv, Matrix.mul_one]`. Conclude with `hx (subset_tsupport _ (by rw [Function.mem_support, e]; exact hne'))`.
-/
theorem GlobalTheory.KSp.parFun_fixed_near_one : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)), ∀ φ ∈ SB (Matrix α ν E), ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → parFun c ψ χ Q (mat c g) φ = φ := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q _ ψ hψ _ _ χ hχ _ φ hφ
  obtain ⟨-, htop, -, -, hcc, -, htr, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  haveI := htop
  haveI := GlobalTheory.WeilM.nonarch_field F
  have hψl := GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ
  have hφl : IsLocallyConstant φ := hφ.1
  have hK : IsCompact (tsupport φ) := hφ.2
  have hA : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₁₁ :=
    continuous_pi fun i => continuous_pi fun j => (GlobalTheory.KSp.ParNear.continuous_mat c).matrix_elem _ _
  have hB : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₁₂ :=
    continuous_pi fun i => continuous_pi fun j => (GlobalTheory.KSp.ParNear.continuous_mat c).matrix_elem _ _
  have hA' : Continuous fun g : UG c (stdJ ν E) => (mat c g⁻¹).toBlocks₁₁ :=
    continuous_pi fun i => continuous_pi fun j => (GlobalTheory.KSp.ParNear.continuous_mat_inv c).matrix_elem _ _

  have hi : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), sc F χ (Fintype.card α) (mat c g).toBlocks₁₁.det = 1 := by
    have ht : Tendsto (fun g : UG c (stdJ ν E) => (mat c g).toBlocks₁₁.det) (𝓝 1) (𝓝 1) := by
      have := hA.matrix_det.tendsto 1
      rwa [GlobalTheory.KSp.ParNear.mat_one, GlobalTheory.KSp.ParNear.toBlocks₁₁_one', det_one] at this
    exact ht.eventually (GlobalTheory.T.unitaryCharacterAbsScalar_eventually_eq_one F E c δ hE _ χ hχ)

  have hii : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), ∀ x ∈ tsupport φ,
      ψ (2⁻¹ * pr c Q (x * (mat c g).toBlocks₁₁) (x * (mat c g).toBlocks₁₂)) * φ (x * (mat c g).toBlocks₁₁) = φ x := by
    refine hK.eventually_forall_of_forall_eventually fun x _ => ?_
    have hP : Continuous fun p : UG c (stdJ ν E) × Matrix α ν E =>
        pr c Q (p.2 * (mat c p.1).toBlocks₁₁) (p.2 * (mat c p.1).toBlocks₁₂) :=
      GlobalTheory.KSp.ParNear.continuous_pr_comp c hcc htr Q (continuous_snd.matrix_mul (hA.comp continuous_fst))
        (continuous_snd.matrix_mul (hB.comp continuous_fst))
    have hP2 : Continuous fun p : UG c (stdJ ν E) × Matrix α ν E =>
        (2 : F)⁻¹ * pr c Q (p.2 * (mat c p.1).toBlocks₁₁) (p.2 * (mat c p.1).toBlocks₁₂) :=
      continuous_const.mul hP
    have h1 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E =>
        ψ (2⁻¹ * pr c Q (p.2 * (mat c p.1).toBlocks₁₁) (p.2 * (mat c p.1).toBlocks₁₂)) :=
      hψl.comp_continuous hP2
    have h2 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ (p.2 * (mat c p.1).toBlocks₁₁) :=
      hφl.comp_continuous (continuous_snd.matrix_mul (hA.comp continuous_fst))
    have h3 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ p.2 :=
      hφl.comp_continuous continuous_snd
    filter_upwards [h1.eventually_eq (1, x), h2.eventually_eq (1, x), h3.eventually_eq (1, x)] with p e1 e2 e3
    rw [e1, e2, e3, GlobalTheory.KSp.ParNear.mat_one, GlobalTheory.KSp.ParNear.toBlocks₁₁_one', GlobalTheory.KSp.ParNear.toBlocks₁₂_one', Matrix.mul_one, Matrix.mul_zero,
      GlobalTheory.KSp.ParNear.pr_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul]

  have hiii : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), ∀ y ∈ tsupport φ, φ (y * (mat c g⁻¹).toBlocks₁₁) = φ y := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have h2 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ (p.2 * (mat c p.1⁻¹).toBlocks₁₁) :=
      hφl.comp_continuous (continuous_snd.matrix_mul (hA'.comp continuous_fst))
    have h3 : IsLocallyConstant fun p : UG c (stdJ ν E) × Matrix α ν E => φ p.2 :=
      hφl.comp_continuous continuous_snd
    filter_upwards [h2.eventually_eq (1, y), h3.eventually_eq (1, y)] with p e2 e3
    rw [e2, e3, inv_one, GlobalTheory.KSp.ParNear.mat_one, GlobalTheory.KSp.ParNear.toBlocks₁₁_one', Matrix.mul_one]
  filter_upwards [hi, hii, hiii] with g hg1 hg2 hg3 hg
  have hinv : (mat c g).toBlocks₁₁ * (mat c g⁻¹).toBlocks₁₁ = 1 := by
    rw [← GlobalTheory.KSp.ParNear.toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero _ _ ((GlobalTheory.KSp.mem_sieg c).mp ((sieg c ν).inv_mem hg)),
      GlobalTheory.KSp.ParNear.mat_mul_mat_inv, GlobalTheory.KSp.ParNear.toBlocks₁₁_one']
  funext x
  simp only [parFun]
  rw [hg1, one_mul]
  by_cases hx : x ∈ tsupport φ
  · exact hg2 x hx
  · rw [image_eq_zero_of_notMem_tsupport hx]
    by_contra hne
    have hne' : φ (x * (mat c g).toBlocks₁₁) ≠ 0 := right_ne_zero_of_mul hne
    have hy : x * (mat c g).toBlocks₁₁ ∈ tsupport φ := subset_tsupport _ hne'
    have e := hg3 _ hy
    rw [Matrix.mul_assoc, hinv, Matrix.mul_one] at e
    exact hx (subset_tsupport _ (by rw [Function.mem_support, e]; exact hne'))
