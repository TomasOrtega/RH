import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTwoLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevSplitOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentQuotientUnitVolumeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedPlaneThetaIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPlaneRestrictedSkewStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicUnfoldingRationalLeviStatement

noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.DescB.LevRatInv
open GlobalTheory.LeviLine
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Introduce `hd`. Establish `h0 : (J.map e).det = 0` using `by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hd, map_zero]`. Take `⟨z, hz0, hz⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Establish `hx : star z ≠ 0` using `fun h' => hz0 (by simpa using congrArg star h')`. Use `h.2.2 (star z) hx` as an intermediate fact.

Rewrite `this` using `[star_star, Matrix.smul_mulVec, hz, smul_zero, dotProduct_zero, Complex.zero_re]`. Conclude with `lt_irrefl _ this`.
-/
theorem det_ne_zero_of_cartan {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (e : E →+* ℂ) {θ : Matrix (Fin n) (Fin n) ℂ}
    (h : IsCartan (Complex.I • J.map e) θ) : J.det ≠ 0 := by
  intro hd
  have h0 : (J.map e).det = 0 := by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hd, map_zero]
  obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hx : star z ≠ 0 := fun h' => hz0 (by simpa using congrArg star h')
  have := h.2.2 (star z) hx
  rw [star_star, Matrix.smul_mulVec, hz, smul_zero, dotProduct_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

/- English proof (translation)
Establish `e : mat (m * m') = mat m * mat m'` using `rfl`. Establish `e1 : mat (γ * h₁) = mat γ * mat h₁` using `rfl`. Take `⟨h1, h2, h3⟩` from `h`. Take `⟨h1', h2', h3'⟩` from `h'`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[e, ← Matrix.mulVec_mulVec, h1', Matrix.mulVec_smul, h1, smul_smul, Units.val_one, one_mul]`. Rewrite using `[e, ← Matrix.mulVec_mulVec, h2', Matrix.mulVec_smul, h2, smul_smul, inv_one, Units.val_one, map_one, one_mul]`. Rewrite using `[e, e1, Matrix.mul_assoc, h3', ← Matrix.mul_assoc, h3, Matrix.mul_assoc]`.
-/
theorem isLevi_mul_one {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {γ h₁ : UA σ Y₁.J}
    {m m' : UA σ Y.J} (h : IsLevi (W₁ := Y₁) H 1 γ m) (h' : IsLevi (W₁ := Y₁) H 1 h₁ m') :
    IsLevi (W₁ := Y₁) H 1 (γ * h₁) (m * m') := by
  have e : mat (m * m') = mat m * mat m' := rfl
  have e1 : mat (γ * h₁) = mat γ * mat h₁ := rfl
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · rw [e, ← Matrix.mulVec_mulVec, h1', Matrix.mulVec_smul, h1, smul_smul, Units.val_one, one_mul]
  · rw [e, ← Matrix.mulVec_mulVec, h2', Matrix.mulVec_smul, h2, smul_smul, inv_one, Units.val_one, map_one, one_mul]
  · rw [e, e1, Matrix.mul_assoc, h3', ← Matrix.mul_assoc, h3, Matrix.mul_assoc]

/- English proof (translation)
Take `⟨a1, a2, a3⟩` from `h₀`. Take `⟨b1, b2, b3⟩` from `h`. Establish `e : mat (m₀ * m * m₀⁻¹) = mat m₀ * mat m * mat m₀⁻¹` using `rfl`. Establish `inv1 : mat m₀⁻¹ * mat m₀ = 1` using `GlobalTheory.UnipCT.mat_inv_mul' m₀`. Establish `inv2 : mat γ * mat γ⁻¹ = 1` using `by show (γ.1 * γ.1⁻¹ : GL _ _).1 = 1`.

Simplify using the standard rewrite rules. Establish `c1 : mat m₀⁻¹ *ᵥ incV F H.x = incV F H.x`. Use `congrArg (mat m₀⁻¹ *ᵥ ·) a1` as an intermediate fact. Simplify using `only [Matrix.mulVec_mulVec, inv1, Matrix.one_mulVec, Units.val_one, one_smul] at this`. Conclude with `this.symm`.

Establish `c2 : mat m₀⁻¹ *ᵥ incV F H.y = incV F H.y`. Use `congrArg (mat m₀⁻¹ *ᵥ ·) a2` as an intermediate fact. Simplify using `only [Matrix.mulVec_mulVec, inv1, Matrix.one_mulVec, inv_one, Units.val_one, map_one, one_smul] at this`. Conclude with `this.symm`. Establish `c3 : mat m₀⁻¹ * incM F H.ι = incM F H.ι * mat γ⁻¹`.

Use `congrArg (fun M => mat m₀⁻¹ * M * mat γ⁻¹) a3` as an intermediate fact. Simplify using `only [← Matrix.mul_assoc, inv1, Matrix.one_mul] at this`. Rewrite `this` using `[Matrix.mul_assoc (mat m₀⁻¹ * incM F H.ι), inv2, Matrix.mul_one]`. Conclude with `this.symm`. Establish `a1' : mat m₀ *ᵥ incV F H.x = incV F H.x` using `by simpa using a1`.

Establish `a2' : mat m₀ *ᵥ incV F H.y = incV F H.y` using `by simpa using a2`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, c1, b1, Matrix.mulVec_smul, a1']`. Rewrite using `[e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, c2, b2, Matrix.mulVec_smul, a2']`. Establish `b3' : mat m * incM F H.ι = incM F H.ι` using `by simpa [mat] using b3`.

Establish `e1 : mat (1 : UA σ Y₁.J) = 1` using `rfl`. Rewrite using `[e, e1, Matrix.mul_one, Matrix.mul_assoc, c3, ← Matrix.mul_assoc (mat m₀ * mat m), Matrix.mul_assoc (mat m₀), b3', a3, Matrix.mul_assoc, inv2, Matrix.mul_one]`.
-/
theorem isLevi_conj {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {γ : UA σ Y₁.J}
    {m₀ m : UA σ Y.J} {t : (AE F E)ˣ} (h₀ : IsLevi (W₁ := Y₁) H 1 γ m₀) (h : IsLevi (W₁ := Y₁) H t 1 m) :
    IsLevi (W₁ := Y₁) H t 1 (m₀ * m * m₀⁻¹) := by
  obtain ⟨a1, a2, a3⟩ := h₀
  obtain ⟨b1, b2, b3⟩ := h
  have e : mat (m₀ * m * m₀⁻¹) = mat m₀ * mat m * mat m₀⁻¹ := rfl
  have inv1 : mat m₀⁻¹ * mat m₀ = 1 := GlobalTheory.UnipCT.mat_inv_mul' m₀
  have inv2 : mat γ * mat γ⁻¹ = 1 := by
    show (γ.1 * γ.1⁻¹ : GL _ _).1 = 1
    simp
  have c1 : mat m₀⁻¹ *ᵥ incV F H.x = incV F H.x := by
    have := congrArg (mat m₀⁻¹ *ᵥ ·) a1
    simp only [Matrix.mulVec_mulVec, inv1, Matrix.one_mulVec, Units.val_one, one_smul] at this
    exact this.symm
  have c2 : mat m₀⁻¹ *ᵥ incV F H.y = incV F H.y := by
    have := congrArg (mat m₀⁻¹ *ᵥ ·) a2
    simp only [Matrix.mulVec_mulVec, inv1, Matrix.one_mulVec, inv_one, Units.val_one, map_one, one_smul] at this
    exact this.symm
  have c3 : mat m₀⁻¹ * incM F H.ι = incM F H.ι * mat γ⁻¹ := by
    have := congrArg (fun M => mat m₀⁻¹ * M * mat γ⁻¹) a3
    simp only [← Matrix.mul_assoc, inv1, Matrix.one_mul] at this
    rw [Matrix.mul_assoc (mat m₀⁻¹ * incM F H.ι), inv2, Matrix.mul_one] at this
    exact this.symm
  have a1' : mat m₀ *ᵥ incV F H.x = incV F H.x := by simpa using a1
  have a2' : mat m₀ *ᵥ incV F H.y = incV F H.y := by simpa using a2
  refine ⟨?_, ?_, ?_⟩
  · rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, c1, b1, Matrix.mulVec_smul, a1']
  · rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, c2, b2, Matrix.mulVec_smul, a2']
  · have b3' : mat m * incM F H.ι = incM F H.ι := by simpa [mat] using b3
    have e1 : mat (1 : UA σ Y₁.J) = 1 := rfl
    rw [e, e1, Matrix.mul_one, Matrix.mul_assoc, c3, ← Matrix.mul_assoc (mat m₀ * mat m), Matrix.mul_assoc (mat m₀), b3', a3,
      Matrix.mul_assoc, inv2, Matrix.mul_one]

/- English proof (translation)
Take `⟨μ, 𝓕, hμ, h𝓕, h1⟩` from `hdom`. Establish `hsum : ∀ x, fa (m₀ * x) + fb (m₀ * x) = fa x + fb x` using `fun x => by`. Establish `e1` using `hs.1 μ 𝓕 hμ h𝓕 h1 (m₀ * x)`. Establish `e2` using `hs.1 μ 𝓕 hμ h𝓕 h1 x`. Simplify using `only [Pi.add_apply] at e1 e2`.

Rewrite using `[e1, e2]`. Conclude with `GlobalTheory.T.parabolic_unfolding_rational_levi F E σ n n₁ Y Y₁ H f hf γ m₀ hm₀ hL μ 𝓕 hμ h𝓕 h1 x`. Use `set T : UA σ Y.J → ℂ := fun x => fa (m₀ * x) - fa x with hT`. Establish `hTa : HasLaw Y₁ H χa za T`. Introduce `t m hm x`.

Establish `hc` using `isLevi_conj hL hm`. Establish `e : m₀ * (m * x) = (m₀ * m * m₀⁻¹) * (m₀ * x)` using `by group`. Simplify using `only [hT]`. Rewrite using `[e, hs.2.1 t _ hc, hs.2.1 t m hm]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hTb : HasLaw Y₁ H χb zb T`. Establish `eT : ∀ x, T x = -(fb (m₀ * x) - fb x)` using `fun x => by`. Simplify using `only [hT]`. Take the linear combination `hsum x`. Introduce `t m hm x`.

Establish `hc` using `isLevi_conj hL hm`. Establish `e : m₀ * (m * x) = (m₀ * m * m₀⁻¹) * (m₀ * x)` using `by group`. Rewrite using `[eT, eT, e, hs.2.2 t _ hc, hs.2.2 t m hm]`. Expand and normalize the polynomial expressions, which then agree. Establish `h0` using `GlobalTheory.ThK.DescB.NextStep.eq_zero_of_two_laws hz hlevi hTa hTb`.

Introduce `x`. Use `congrFun h0 x` as an intermediate fact. Simplify using `only [hT, Pi.zero_apply] at this`. Conclude with `sub_eq_zero.1 this`.
-/
theorem fa_inv {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {χa χb : Chr F E} {za zb : ℝ}
    (hz : za < zb)
    (hlevi : ∃ (t : (AE F E)ˣ) (m : UA σ Y.J), IsLevi (W₁ := Y₁) H t 1 m ∧ 1 < (absE F E t : ℝ))
    (hdom : ∃ (μ : Measure (unip σ Y H)) (𝓕 : Set (unip σ Y H)), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μ ∧ μ 𝓕 = 1)
    {f fa fb : UA σ Y.J → ℂ} (hf : ∀ γ ∈ ratU σ Y.J, ∀ x, f (γ * x) = f x)
    (hs : SplitZ Y₁ H χa χb za zb f fa fb) {γ : UA σ Y₁.J} {m₀ : UA σ Y.J} (hm₀ : m₀ ∈ ratU σ Y.J)
    (hL : IsLevi (W₁ := Y₁) H 1 γ m₀) : ∀ x, fa (m₀ * x) = fa x := by
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := hdom
  have hsum : ∀ x, fa (m₀ * x) + fb (m₀ * x) = fa x + fb x := fun x => by
    have e1 := hs.1 μ 𝓕 hμ h𝓕 h1 (m₀ * x)
    have e2 := hs.1 μ 𝓕 hμ h𝓕 h1 x
    simp only [Pi.add_apply] at e1 e2
    rw [e1, e2]
    exact GlobalTheory.T.parabolic_unfolding_rational_levi F E σ n n₁ Y Y₁ H f hf γ m₀ hm₀ hL μ 𝓕 hμ h𝓕 h1 x
  set T : UA σ Y.J → ℂ := fun x => fa (m₀ * x) - fa x with hT
  have hTa : HasLaw Y₁ H χa za T := by
    intro t m hm x
    have hc := isLevi_conj hL hm
    have e : m₀ * (m * x) = (m₀ * m * m₀⁻¹) * (m₀ * x) := by group
    simp only [hT]
    rw [e, hs.2.1 t _ hc, hs.2.1 t m hm]
    ring
  have hTb : HasLaw Y₁ H χb zb T := by
    have eT : ∀ x, T x = -(fb (m₀ * x) - fb x) := fun x => by
      simp only [hT]; linear_combination hsum x
    intro t m hm x
    have hc := isLevi_conj hL hm
    have e : m₀ * (m * x) = (m₀ * m * m₀⁻¹) * (m₀ * x) := by group
    rw [eT, eT, e, hs.2.2 t _ hc, hs.2.2 t m hm]
    ring
  have h0 := GlobalTheory.ThK.DescB.NextStep.eq_zero_of_two_laws hz hlevi hTa hTb
  intro x
  have := congrFun h0 x
  simp only [hT, Pi.zero_apply] at this
  exact sub_eq_zero.1 this

/- English proof (translation)
Introduce `γ hγ h₁`. Take `⟨m₀, hm₀, hL⟩` from `hrat γ hγ`. Take `⟨m₁, hm₁⟩` from `hex h₁`. Rewrite using `[hg _ _ (isLevi_mul_one hL hm₁), hg _ _ hm₁, mul_assoc]`. Conclude with `fa_inv hz hlevi hdom hf hs hm₀ hL (m₁ * h)`.
-/
theorem gen_inv {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {χa χb : Chr F E} {za zb : ℝ}
    (hz : za < zb)
    (hlevi : ∃ (t : (AE F E)ˣ) (m : UA σ Y.J), IsLevi (W₁ := Y₁) H t 1 m ∧ 1 < (absE F E t : ℝ))
    (hdom : ∃ (μ : Measure (unip σ Y H)) (𝓕 : Set (unip σ Y H)), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μ ∧ μ 𝓕 = 1)
    (hrat : ∀ γ ∈ ratU σ Y₁.J, ∃ m ∈ ratU σ Y.J, IsLevi (W₁ := Y₁) H 1 γ m)
    {f fa fb : UA σ Y.J → ℂ} (hf : ∀ γ ∈ ratU σ Y.J, ∀ x, f (γ * x) = f x)
    (hs : SplitZ Y₁ H χa χb za zb f fa fb) (h : UA σ Y.J)
    (hex : ∀ h₁ : UA σ Y₁.J, ∃ m : UA σ Y.J, IsLevi (W₁ := Y₁) H 1 h₁ m)
    {g : UA σ Y₁.J → ℂ} (hg : ∀ h₁ m, IsLevi (W₁ := Y₁) H 1 h₁ m → g h₁ = fa (m * h)) :
    ∀ γ ∈ ratU σ Y₁.J, ∀ h₁, g (γ * h₁) = g h₁ := by
  intro γ hγ h₁
  obtain ⟨m₀, hm₀, hL⟩ := hrat γ hγ
  obtain ⟨m₁, hm₁⟩ := hex h₁
  rw [hg _ _ (isLevi_mul_one hL hm₁), hg _ _ hm₁, mul_assoc]
  exact fa_inv hz hlevi hdom hf hs hm₀ hL (m₁ * h)

/- English proof (translation)
Introduce `f hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx => exact hS x hx`. Consider the case `zero => intro _ _ _`. Both sides reduce to the same expression.

Consider the case `add x y _ _ hx hy => intro γ hγ z`. Simplify using `only [Pi.add_apply]`. Rewrite using `[hx γ hγ z, hy γ hγ z]`. Consider the case `smul r x _ hx => intro γ hγ z`. Simplify using `only [Pi.smul_apply]`.

Rewrite using `[hx γ hγ z]`.
-/
theorem inv_span {n : ℕ} {Y : Spc F E n} (S : Set (UA σ Y.J → ℂ))
    (hS : ∀ f ∈ S, ∀ γ ∈ ratU σ Y.J, ∀ x, f (γ * x) = f x) :
    ∀ f ∈ Submodule.span ℂ S, ∀ γ ∈ ratU σ Y.J, ∀ x, f (γ * x) = f x := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => intro _ _ _; rfl
  | add x y _ _ hx hy => intro γ hγ z; simp only [Pi.add_apply]; rw [hx γ hγ z, hy γ hγ z]
  | smul r x _ hx => intro γ hγ z; simp only [Pi.smul_apply]; rw [hx γ hγ z]

/- English proof (translation)
Use `inv_span _ ?_` and prove the remaining obligations. Introduce and unpack `g ⟨f, hf, fa, fb, hs, h, -, hex, hg⟩`. Conclude with `gen_inv hz hlevi hdom hrat (hS f hf) hs h hex hg`.
-/
theorem inv_alphaSpan {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {χa χb : Chr F E} {za zb : ℝ}
    (hz : za < zb)
    (hlevi : ∃ (t : (AE F E)ˣ) (m : UA σ Y.J), IsLevi (W₁ := Y₁) H t 1 m ∧ 1 < (absE F E t : ℝ))
    (hdom : ∃ (μ : Measure (unip σ Y H)) (𝓕 : Set (unip σ Y H)), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μ ∧ μ 𝓕 = 1)
    (hrat : ∀ γ ∈ ratU σ Y₁.J, ∃ m ∈ ratU σ Y.J, IsLevi (W₁ := Y₁) H 1 γ m)
    (Kh : Set (UA σ Y.J)) (S : Submodule ℂ (UA σ Y.J → ℂ))
    (hS : ∀ f ∈ S, ∀ γ ∈ ratU σ Y.J, ∀ x, f (γ * x) = f x) :
    ∀ g ∈ alphaSpan Y₁ H χa χb za zb Kh S, ∀ γ ∈ ratU σ Y₁.J, ∀ x, g (γ * x) = g x := by
  refine inv_span _ ?_
  rintro g ⟨f, hf, fa, fb, hs, h, -, hex, hg⟩
  exact gen_inv hz hlevi hdom hrat (hS f hf) hs h hex hg

/- English proof (translation)
Establish `hcm` using `hB.cm`. Use `⟨GlobalTheory.ThK.DescB.NextStep.exists_levi_of hcm hsk hI.2.1 hI.2.2.1 hI.2.2.2.1 hI.2.2.2.2.1, GlobalTheory.T.unipotent_quotient_unit_volume F E σ B hB n n₁ Y Y₁ H hsk hI, ?_⟩` and prove the remaining obligations. Establish `w : InfinitePlace F` using `Classical.arbitrary _`. Conclude with `GlobalTheory.T.isotropic_plane_restricted_skew F E σ (sigma_invol hcm) n n₁ Y Y₁ H hsk hI.2.1 hI.2.2.1 hI.2.2.2.1 hI.2.2.2.2.1 hI.2.2.2.2.2.1 (det_ne_zero_of_cartan _ (hI.2.2.2.2.2.2.2 w))`.
-/
theorem plane_facts (B : Base F E) (hB : B.IsGood σ) {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁}
    (hsk : ∀ i j, σ (Y.J j i) = -Y.J i j) (hI : IsIsoPlane σ B H Y Y₁) :
    (∃ (t : (AE F E)ˣ) (m : UA σ Y.J), IsLevi (W₁ := Y₁) H t 1 m ∧ 1 < (absE F E t : ℝ)) ∧
    (∃ (μ : Measure (unip σ Y H)) (𝓕 : Set (unip σ Y H)), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) 𝓕 μ ∧ μ 𝓕 = 1) ∧
    (∀ γ ∈ ratU σ Y₁.J, ∃ m ∈ ratU σ Y.J, IsLevi (W₁ := Y₁) H 1 γ m) := by
  have hcm := hB.cm
  refine ⟨GlobalTheory.ThK.DescB.NextStep.exists_levi_of hcm hsk hI.2.1 hI.2.2.1 hI.2.2.2.1 hI.2.2.2.2.1,
    GlobalTheory.T.unipotent_quotient_unit_volume F E σ B hB n n₁ Y Y₁ H hsk hI, ?_⟩
  have w : InfinitePlace F := Classical.arbitrary _
  exact GlobalTheory.T.isotropic_plane_restricted_skew F E σ (sigma_invol hcm) n n₁ Y Y₁ H hsk hI.2.1 hI.2.2.1 hI.2.2.2.1 hI.2.2.2.2.1 hI.2.2.2.2.2.1
    (det_ne_zero_of_cartan _ (hI.2.2.2.2.2.2.2 w))

/- English proof (translation)
Take `⟨T, -, m, m', f, φ, f', φ', hi, -, rfl, -, -⟩` from `h`. Use `Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, (hi i).1, φ i, (hi i).2.1, ?_, rfl⟩` and prove the remaining obligations. Use `Filter.eventually_cofinite.2 ((T.finite_toSet).subset fun v hv => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `hT`. Conclude with `hv ((hi i).2.2 v hT)`.
-/
theorem polData_of_polMatch (B : Base F E) {a a' : ℕ} (G : Geo σ a a') (X : Chars F E) (R : RealMaps F a a')
    (Rf : FinMaps F a a') {Φ : (Fin a × Fin (a + a') → AF F) → ℂ} {Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ}
    (h : PolMatch B G X R Rf Φ Φ') : Φ ∈ PolData B G.M := by
  obtain ⟨T, -, m, m', f, φ, f', φ', hi, -, rfl, -, -⟩ := h
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, (hi i).1, φ i, (hi i).2.1, ?_, rfl⟩
  refine Filter.eventually_cofinite.2 ((T.finite_toSet).subset fun v hv => ?_)
  by_contra hT
  exact hv ((hi i).2.2 v hT)

/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq d₁ H' i₀ i₁ sp pl hH hiso k hk f hf fa fb hs h _ hex g hg`. Establish `hB` using `hM.triple.base`. Establish `hcm` using `hB.cm`. Establish `hσ : ∀ x, σ (σ x) = x` using `sigma_invol hcm`. Establish `hsk` using `GlobalTheory.ThK.DescB.NextStep.skew_sp hσ B hM.triple.geo.hW.skew hH hiso`.

Establish `hzj : ∀ j, j + 1 ≤ G.p → (a' : ℝ) / 2 < zb a j` using `fun j hj => by`. Establish `e` using `hM.triple.geo.eBig`. Establish `hn : a' + 2 * (j + 1) < a` using `by omega`. Establish `hr : ((a' + 2 * (j + 1) : ℕ) : ℝ) < a` using `by exact_mod_cast hn`. Unfold `zb`.

Move the coercions through the operations in `at hr ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlev : ∀ j, j ≤ k → ∀ f ∈ Lev B X a a' H' sp pl (thetaSpanV B G X om R Rf) j, ∀ γ ∈ ratU σ (sp j).J, ∀ x, f (γ * x) = f x`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero`. Introduce `_`. Rewrite using `[lev_zero]`. Establish `hI0` using `hiso 0 (by omega)`. Establish `w : InfinitePlace F` using `Classical.arbitrary _`.

Use `inv_alphaSpan (χa := X.α) (χb := X.β) ?_ (GlobalTheory.ThK.DescB.NextStep.exists_levi_of hcm hM.triple.geo.hW.skew hH.xx hH.yy hH.xy hH.orth) (GlobalTheory.T.triple_adapted_plane_theta_integral F E σ B a a' G X om om' hM.triple d₁ (sp 0) H' i₀ i₁ hH) (GlobalTheory.T.isotropic_pla …` and prove the remaining obligations. Establish `hlt` using `hM.triple.geo.lt`. Establish `: (a' : ℝ) < a` using `by exact_mod_cast hlt`. Combine the linear equalities and inequalities to obtain the conclusion. Use `inv_span _ ?_` and prove the remaining obligations.

Introduce and unpack `f ⟨Φ, Φ', -, hm, rfl⟩`. Conclude with `(GlobalTheory.T.theta_lift_left_invariant hK F E σ B a a' G X om om' hM.triple d₁ (sp 0) H' i₀ i₁ hH).1 Φ (polData_of_polMatch B G X R Rf hm)`. Consider the case `succ j ih`. Introduce `hj`. Rewrite using `[lev_succ]`.

Establish `hI` using `hiso j (by omega)`. Take `⟨p1, p2, p3⟩` from `plane_facts B hB (hsk j (by omega)) hI`. Conclude with `inv_alphaSpan (hzj j (by omega)) p1 p2 p3 _ _ (ih (by omega))`. Take `⟨p1, p2, p3⟩` from `plane_facts B hB (hsk k (by omega)) (hiso k (by omega))`. Conclude with `gen_inv (hzj k (by omega)) p1 p2 p3 (hlev k le_rfl f hf) hs h hex hg`.
-/
theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ) (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j))
      (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))), H'.IsAdapted σ B G.W (sp 0) i₀ i₁ →
      (∀ i < G.p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) → ∀ k, k + 1 + 1 ≤ G.p →
      ∀ f ∈ Lev B X a a' H' sp pl (thetaSpanV B G X om R Rf) k, ∀ fa fb : UA σ (sp k).J → ℂ,
        SplitZ (sp (k + 1)) (pl k) X.α X.β ((a' : ℝ) / 2) (zb a k) f fa fb →
      ∀ h ∈ finK σ (sp k) B.emb, (∀ h₁ : UA σ (sp (k + 1)).J, ∃ m : UA σ (sp k).J, IsLevi (W₁ := sp (k + 1)) (pl k) 1 h₁ m) →
      ∀ g : UA σ (sp (k + 1)).J → ℂ, (∀ h₁ m, IsLevi (W₁ := sp (k + 1)) (pl k) 1 h₁ m → g h₁ = fa (m * h)) →
      ∀ γ ∈ ratU σ (sp (k + 1)).J, ∀ h₁, g (γ * h₁) = g h₁ := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq d₁ H' i₀ i₁ sp pl hH hiso k hk f hf fa fb hs h _ hex g hg
  have hB := hM.triple.base
  have hcm := hB.cm
  have hσ : ∀ x, σ (σ x) = x := sigma_invol hcm
  have hsk := GlobalTheory.ThK.DescB.NextStep.skew_sp hσ B hM.triple.geo.hW.skew hH hiso
  have hzj : ∀ j, j + 1 ≤ G.p → (a' : ℝ) / 2 < zb a j := fun j hj => by
    have e := hM.triple.geo.eBig
    have hn : a' + 2 * (j + 1) < a := by omega
    have hr : ((a' + 2 * (j + 1) : ℕ) : ℝ) < a := by exact_mod_cast hn
    unfold zb
    push_cast at hr ⊢
    linarith
  have hlev : ∀ j, j ≤ k → ∀ f ∈ Lev B X a a' H' sp pl (thetaSpanV B G X om R Rf) j,
      ∀ γ ∈ ratU σ (sp j).J, ∀ x, f (γ * x) = f x := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [lev_zero]
      have hI0 := hiso 0 (by omega)
      have w : InfinitePlace F := Classical.arbitrary _
      refine inv_alphaSpan (χa := X.α) (χb := X.β) ?_
        (GlobalTheory.ThK.DescB.NextStep.exists_levi_of hcm hM.triple.geo.hW.skew hH.xx hH.yy hH.xy hH.orth)
        (GlobalTheory.T.triple_adapted_plane_theta_integral F E σ B a a' G X om om' hM.triple d₁ (sp 0) H' i₀ i₁ hH)
        (GlobalTheory.T.isotropic_plane_restricted_skew F E σ hσ _ _ G.W (sp 0) H' hM.triple.geo.hW.skew hH.xx hH.yy hH.xy hH.orth hH.gram
          (det_ne_zero_of_cartan _ (hI0.2.2.2.2.2.2.1 w))) _ _ ?_
      · have hlt := hM.triple.geo.lt
        have : (a' : ℝ) < a := by exact_mod_cast hlt
        linarith
      · refine inv_span _ ?_
        rintro f ⟨Φ, Φ', -, hm, rfl⟩
        exact (GlobalTheory.T.theta_lift_left_invariant hK F E σ B a a' G X om om' hM.triple d₁ (sp 0) H' i₀ i₁ hH).1 Φ
          (polData_of_polMatch B G X R Rf hm)
    | succ j ih =>
      intro hj
      rw [lev_succ]
      have hI := hiso j (by omega)
      obtain ⟨p1, p2, p3⟩ := plane_facts B hB (hsk j (by omega)) hI
      exact inv_alphaSpan (hzj j (by omega)) p1 p2 p3 _ _ (ih (by omega))
  obtain ⟨p1, p2, p3⟩ := plane_facts B hB (hsk k (by omega)) (hiso k (by omega))
  exact gen_inv (hzj k (by omega)) p1 p2 p3 (hlev k le_rfl f hf) hs h hex hg

end GlobalTheory.ThK.DescB.LevRatInv

end
