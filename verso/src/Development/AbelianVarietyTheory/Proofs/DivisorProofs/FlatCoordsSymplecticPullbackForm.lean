import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapSymplecticTransformStatement
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.SympFlatChange

/- English proof (translation)
Simplify using `[vecMul, dotProduct, Complex.re_sum]`.
-/
theorem re_vecMul {g : ℕ} (p : Fin g → ℝ) (τ : Matrix (Fin g) (Fin g) ℂ) (j : Fin g) :
    (((fun i => (p i : ℂ)) ᵥ* τ) j).re = (p ᵥ* τ.map Complex.re) j := by
  simp [vecMul, dotProduct, Complex.re_sum]

/- English proof (translation)
Simplify using `[vecMul, dotProduct, Complex.im_sum]`.
-/
theorem im_vecMul {g : ℕ} (p : Fin g → ℝ) (τ : Matrix (Fin g) (Fin g) ℂ) (j : Fin g) :
    (((fun i => (p i : ℂ)) ᵥ* τ) j).im = (p ᵥ* τ.map Complex.im) j := by
  simp [vecMul, dotProduct, Complex.im_sum]

/- English proof (translation)
Establish `him : (fun i => (per τ x i).im) = (fun i => x (Sum.inl i)) ᵥ* τ.map Complex.im`. Use extensionality with `i`. Simplify using `[per, im_vecMul]`. Establish `hre : (fun i => (per τ x i).re) = (fun i => x (Sum.inl i)) ᵥ* τ.map Complex.re + fun i => x (Sum.inr i)`. Use extensionality with `i`.

Simplify using `[per, re_vecMul]`. Establish `hp : ((fun i => x (Sum.inl i)) ᵥ* τ.map Complex.im) ᵥ* (τ.map Complex.im)⁻¹ = fun i => x (Sum.inl i)`. Rewrite using `[vecMul_vecMul, mul_nonsing_inv _ h, vecMul_one]`. Apply the tactic sequence `ext (j | j) <;> simp only [flatOf, Sum.elim_inl, Sum.elim_inr, him, hre, hp] <;> simp`.
-/
theorem flatOf_per {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (h : IsUnit (τ.map Complex.im).det)
    (x : Fl g) : flatOf τ (per τ x) = x := by
  have him : (fun i => (per τ x i).im) = (fun i => x (Sum.inl i)) ᵥ* τ.map Complex.im := by
    ext i; simp [per, im_vecMul]
  have hre : (fun i => (per τ x i).re) =
      (fun i => x (Sum.inl i)) ᵥ* τ.map Complex.re + fun i => x (Sum.inr i) := by
    ext i; simp [per, re_vecMul]
  have hp : ((fun i => x (Sum.inl i)) ᵥ* τ.map Complex.im) ᵥ* (τ.map Complex.im)⁻¹ =
      fun i => x (Sum.inl i) := by
    rw [vecMul_vecMul, mul_nonsing_inv _ h, vecMul_one]
  ext (j | j) <;> simp only [flatOf, Sum.elim_inl, Sum.elim_inr, him, hre, hp] <;> simp

/- English proof (translation)
Establish `hp : ((fun i => (z i).im) ᵥ* (τ.map Complex.im)⁻¹) ᵥ* τ.map Complex.im = fun i => (z i).im`. Rewrite using `[vecMul_vecMul, nonsing_inv_mul _ h, vecMul_one]`. Use extensionality with `i`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[per, flatOf, re_vecMul]`.

Simplify using `[per, flatOf, im_vecMul, hp]`.
-/
theorem per_flatOf {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (h : IsUnit (τ.map Complex.im).det)
    (z : Fin g → ℂ) : per τ (flatOf τ z) = z := by
  have hp : ((fun i => (z i).im) ᵥ* (τ.map Complex.im)⁻¹) ᵥ* τ.map Complex.im =
      fun i => (z i).im := by
    rw [vecMul_vecMul, nonsing_inv_mul _ h, vecMul_one]
  ext i; apply Complex.ext
  · simp [per, flatOf, re_vecMul]
  · simp [per, flatOf, im_vecMul, hp]

/- English proof (translation)
Use `show (γ⁻¹ * γ : Sp g).1 = 1`. Simplify using the standard rewrite rules.
-/
theorem inv_mat_mul {g : ℕ} (γ : Sp g) : (γ⁻¹).mat * γ.mat = 1 := by
  show (γ⁻¹ * γ : Sp g).1 = 1
  simp

abbrev pC {g : ℕ} (x : Fl g) : Fin g → ℂ := fun i => (x (Sum.inl i) : ℂ)

abbrev qC {g : ℕ} (x : Fl g) : Fin g → ℂ := fun i => (x (Sum.inr i) : ℂ)

/- English proof (translation)
Use extensionality with `j`. Simplify using `[pC, qC, vecMul, dotProduct, Fintype.sum_sum_type, toBlocks₁₁, toBlocks₂₁]`.
-/
theorem pC_vecMul {g : ℕ} (y : Fl g) (γ : Sp g) :
    pC (y ᵥ* γ.mat) = pC y ᵥ* γ.mat.toBlocks₁₁.map (fun t : ℝ => (t : ℂ)) +
      qC y ᵥ* γ.mat.toBlocks₂₁.map (fun t : ℝ => (t : ℂ)) := by
  ext j; simp [pC, qC, vecMul, dotProduct, Fintype.sum_sum_type, toBlocks₁₁, toBlocks₂₁]

/- English proof (translation)
Use extensionality with `j`. Simplify using `[pC, qC, vecMul, dotProduct, Fintype.sum_sum_type, toBlocks₁₂, toBlocks₂₂]`.
-/
theorem qC_vecMul {g : ℕ} (y : Fl g) (γ : Sp g) :
    qC (y ᵥ* γ.mat) = pC y ᵥ* γ.mat.toBlocks₁₂.map (fun t : ℝ => (t : ℂ)) +
      qC y ᵥ* γ.mat.toBlocks₂₂.map (fun t : ℝ => (t : ℂ)) := by
  ext j; simp [pC, qC, vecMul, dotProduct, Fintype.sum_sum_type, toBlocks₁₂, toBlocks₂₂]

/- English proof (translation)
Establish `h1` using `pC_vecMul y γ`. Establish `h2` using `qC_vecMul y γ`. Use `show pC (y ᵥ* γ.mat) ᵥ* τ + qC (y ᵥ* γ.mat) = _`. Rewrite using `[h1, h2]`. Simplify using `only [den, add_vecMul, vecMul_add, vecMul_vecMul]`.

Normalize the expressions using the abelian group laws.
-/
theorem per_vecMul {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (y : Fl g) (γ : Sp g) :
    per τ (y ᵥ* γ.mat) = pC y ᵥ* (γ.mat.toBlocks₁₁.map (fun t : ℝ => (t : ℂ)) * τ +
      γ.mat.toBlocks₁₂.map (fun t : ℝ => (t : ℂ))) + qC y ᵥ* den γ τ := by
  have h1 := pC_vecMul y γ
  have h2 := qC_vecMul y γ
  show pC (y ᵥ* γ.mat) ᵥ* τ + qC (y ᵥ* γ.mat) = _
  rw [h1, h2]
  simp only [den, add_vecMul, vecMul_add, vecMul_vecMul]
  abel

/- English proof (translation)
Establish `hd` using `(Matrix.isUnit_iff_isUnit_det _).1 hY`. Use `set y := x ᵥ* (γ⁻¹).mat with hy`. Establish `hyx : y ᵥ* γ.mat = x` using `by rw [hy, vecMul_vecMul, inv_mat_mul, vecMul_one]`. Establish `key : per (moeb γ τ) y ᵥ* den γ τ = per τ x`. Rewrite using `[← hyx, per_vecMul τ y γ]`.

Simplify using `only [per, moeb, add_vecMul, vecMul_vecMul, Matrix.mul_assoc, nonsing_inv_mul _ hd, Matrix.mul_one]`. Rewrite using `[← key, vecMul_vecMul, mul_nonsing_inv _ hd, vecMul_one]`.
-/
theorem per_moeb {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (γ : Sp g) (hY : IsUnit (den γ τ))
    (x : Fl g) : per (moeb γ τ) (x ᵥ* (γ⁻¹).mat) = per τ x ᵥ* (den γ τ)⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hY
  set y := x ᵥ* (γ⁻¹).mat with hy
  have hyx : y ᵥ* γ.mat = x := by rw [hy, vecMul_vecMul, inv_mat_mul, vecMul_one]
  have key : per (moeb γ τ) y ᵥ* den γ τ = per τ x := by
    rw [← hyx, per_vecMul τ y γ]
    simp only [per, moeb, add_vecMul, vecMul_vecMul, Matrix.mul_assoc, nonsing_inv_mul _ hd,
      Matrix.mul_one]
  rw [← key, vecMul_vecMul, mul_nonsing_inv _ hd, vecMul_one]

end GlobalTheory.SympFlatChange

namespace GlobalTheory.SympFlatChange

/- English proof (translation)
The claim follows from `(h.2.det_pos).ne'.isUnit`.
-/
theorem isUnit_im_det {g : ℕ} {σ : Matrix (Fin g) (Fin g) ℂ} (h : IsSiegel σ) :
    IsUnit (σ.map Complex.im).det :=
  (h.2.det_pos).ne'.isUnit

/- English proof (translation)
Establish `h` using `per_moeb γ hY (flatOf (τ P.1) P.2)`. Rewrite `h` using `[per_flatOf (isUnit_im_det hS)]`. Use `show flatOf (moeb γ (τ P.1)) (P.2 ᵥ* (den γ (τ P.1))⁻¹) = flatOf (τ P.1) P.2 ᵥ* _`. Rewrite using `[← h, flatOf_per (isUnit_im_det hS')]`.
-/
theorem flat_reframe_pt {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {τ : E → Matrix (Fin g) (Fin g) ℂ} (γ : Sp g) (P : Pt E g) (hS : IsSiegel (τ P.1))
    (hS' : IsSiegel (moeb γ (τ P.1))) (hY : IsUnit (den γ (τ P.1))) :
    flat (fun b => moeb γ (τ b)) (reframe τ γ P) = flat τ P ᵥ* (γ⁻¹).mat := by
  have h := per_moeb γ hY (flatOf (τ P.1) P.2)
  rw [per_flatOf (isUnit_im_det hS)] at h
  show flatOf (moeb γ (τ P.1)) (P.2 ᵥ* (den γ (τ P.1))⁻¹) = flatOf (τ P.1) P.2 ᵥ* _
  rw [← h, flatOf_per (isUnit_im_det hS')]

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Use `fun_prop`.
-/
theorem diffAt_det {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : Type*} [Fintype n]
    [DecidableEq n] {A : F → Matrix n n ℝ} {x : F}
    (h : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) :
    DifferentiableAt ℝ (fun y => (A y).det) x := by
  simp only [Matrix.det_apply']
  fun_prop

/- English proof (translation)
Establish `hadj : DifferentiableAt ℝ (fun y => (A y).adjugate i j) x`. Simplify using `only [adjugate_apply]`. Use `diffAt_det fun k l => ?_` and prove the remaining obligations. Simplify using `only [updateRow_apply]`. Use `split_ifs`.

Use `fun_prop`. Conclude with `h k l`. Establish `hd` using `diffAt_det h`. Simplify using `only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']`. Conclude with `(hd.inv hx).mul hadj`.
-/
theorem diffAt_inv_entry {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : Type*}
    [Fintype n] [DecidableEq n] {A : F → Matrix n n ℝ} {x : F}
    (h : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) (hx : (A x).det ≠ 0) (i j : n) :
    DifferentiableAt ℝ (fun y => (A y)⁻¹ i j) x := by
  have hadj : DifferentiableAt ℝ (fun y => (A y).adjugate i j) x := by
    simp only [adjugate_apply]
    refine diffAt_det fun k l => ?_
    simp only [updateRow_apply]
    split_ifs
    · fun_prop
    · exact h k l
  have hd := diffAt_det h
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact (hd.inv hx).mul hadj

/- English proof (translation)
Establish `hb : P.1 ∈ B` using `hP.1`. Establish `he : ∀ i j, DifferentiableAt ℝ (fun Q : Pt E g => τ Q.1 i j) P` using `fun i j => (((hτ.2.1 i j).differentiableAt (hτ.1.mem_nhds hb)).restrictScalars ℝ).comp P differentiableAt_fst`. Establish `him : ∀ i j, DifferentiableAt ℝ (fun Q : Pt E g => (τ Q.1).map Complex.im i j) P` using `fun i j => Complex.imCLM.differentiableAt.comp P (he i j)`. Establish `hre : ∀ i j, DifferentiableAt ℝ (fun Q : Pt E g => (τ Q.1).map Complex.re i j) P` using `fun i j => Complex.reCLM.differentiableAt.comp P (he i j)`. Apply the tactic sequence `have hinv := diffAt_inv_entry him (isUnit_im_det (hτ.2.2 _ hb)).ne_zero`.

Establish `hzi : ∀ i, DifferentiableAt ℝ (fun Q : Pt E g => (Q.2 i).im) P` using `fun i => Complex.imCLM.differentiableAt.comp P (by fun_prop : DifferentiableAt ℝ (fun Q : Pt E g => Q.2 i) P)`. Establish `hzr : ∀ i, DifferentiableAt ℝ (fun Q : Pt E g => (Q.2 i).re) P` using `fun i => Complex.reCLM.differentiableAt.comp P (by fun_prop : DifferentiableAt ℝ (fun Q : Pt E g => Q.2 i) P)`. Establish `hp : ∀ j, DifferentiableAt ℝ (fun Q : Pt E g => ((fun i => (Q.2 i).im) ᵥ* ((τ Q.1).map Complex.im)⁻¹) j) P`. Introduce `j`. Simplify using `only [vecMul, dotProduct]`.

Conclude with `DifferentiableAt.fun_sum fun i _ => (hzi i).mul (hinv i j)`. Rewrite using `[differentiableAt_pi]`. Introduce and unpack `(j | j)`. Conclude with `hp j`. Simplify using `only [flat, flatOf, Sum.elim_inr, Pi.sub_apply]`.

Use `(hzr j).sub ?_` and prove the remaining obligations. Simplify using `only [vecMul, dotProduct]`. Conclude with `DifferentiableAt.fun_sum fun i _ => (hp i).mul (hre i j)`.
-/
theorem flat_diffAt {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap B τ) {P : Pt E g}
    (hP : P ∈ cov B g) : DifferentiableAt ℝ (flat τ) P := by
  have hb : P.1 ∈ B := hP.1
  have he : ∀ i j, DifferentiableAt ℝ (fun Q : Pt E g => τ Q.1 i j) P := fun i j =>
    (((hτ.2.1 i j).differentiableAt (hτ.1.mem_nhds hb)).restrictScalars ℝ).comp P
      differentiableAt_fst
  have him : ∀ i j, DifferentiableAt ℝ (fun Q : Pt E g => (τ Q.1).map Complex.im i j) P :=
    fun i j => Complex.imCLM.differentiableAt.comp P (he i j)
  have hre : ∀ i j, DifferentiableAt ℝ (fun Q : Pt E g => (τ Q.1).map Complex.re i j) P :=
    fun i j => Complex.reCLM.differentiableAt.comp P (he i j)
  have hinv := diffAt_inv_entry him (isUnit_im_det (hτ.2.2 _ hb)).ne_zero
  have hzi : ∀ i, DifferentiableAt ℝ (fun Q : Pt E g => (Q.2 i).im) P := fun i =>
    Complex.imCLM.differentiableAt.comp P (by fun_prop : DifferentiableAt ℝ (fun Q : Pt E g => Q.2 i) P)
  have hzr : ∀ i, DifferentiableAt ℝ (fun Q : Pt E g => (Q.2 i).re) P := fun i =>
    Complex.reCLM.differentiableAt.comp P (by fun_prop : DifferentiableAt ℝ (fun Q : Pt E g => Q.2 i) P)
  have hp : ∀ j, DifferentiableAt ℝ (fun Q : Pt E g =>
      ((fun i => (Q.2 i).im) ᵥ* ((τ Q.1).map Complex.im)⁻¹) j) P := by
    intro j
    simp only [vecMul, dotProduct]
    exact DifferentiableAt.fun_sum fun i _ => (hzi i).mul (hinv i j)
  rw [differentiableAt_pi]
  rintro (j | j)
  · exact hp j
  · simp only [flat, flatOf, Sum.elim_inr, Pi.sub_apply]
    refine (hzr j).sub ?_
    simp only [vecMul, dotProduct]
    exact DifferentiableAt.fun_sum fun i _ => (hp i).mul (hre i j)

end GlobalTheory.SympFlatChange

namespace GlobalTheory.SympFlatChange

/- English proof (translation)
Establish `hγ : γ.mat * J (Fin g) ℝ * γ.matᵀ = J (Fin g) ℝ` using `SymplecticGroup.mem_iff.1 γ.2`. Rewrite using `[riem_eq_J, riem_eq_J, ← dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, mulVec_mulVec, hγ]`.
-/
theorem riem_vecMul_symp {g : ℕ} (γ : Sp g) (x y : Fl g) :
    riem (x ᵥ* γ.mat) (y ᵥ* γ.mat) = riem x y := by
  have hγ : γ.mat * J (Fin g) ℝ * γ.matᵀ = J (Fin g) ℝ := SymplecticGroup.mem_iff.1 γ.2
  rw [riem_eq_J, riem_eq_J, ← dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec,
    mulVec_mulVec, hγ]

/- English proof (translation)
Take `⟨hτ', hY, hR⟩` from `GlobalTheory.T.period_map_symplectic_transform hτ γ`. Establish `hopen : IsOpen (cov B g)` using `hτ.1.prod isOpen_univ`. Establish `hpt : ∀ Q ∈ cov B g, flat (fun b => moeb γ (τ b)) (reframe τ γ Q) = flat τ Q ᵥ* (γ⁻¹).mat` using `fun Q hQ => flat_reframe_pt γ Q (hτ.2.2 _ hQ.1) (hτ'.2.2 _ hQ.1) (hY _ hQ.1)`. Use `⟨hpt P hP, ?_⟩` and prove the remaining obligations. Establish `hRP : reframe τ γ P ∈ cov B g` using `⟨hP.1, trivial⟩`.

Establish `hF` using `flat_diffAt hτ' hRP`. Establish `hRd : DifferentiableAt ℝ (reframe τ γ) P` using `((hR P hP).differentiableAt (hopen.mem_nhds hP)).restrictScalars ℝ`. Establish `hG` using `flat_diffAt hτ hP`. Set `L : Fl g →L[ℝ] Fl g` to `LinearMap.toContinuousLinearMap (Matrix.vecMulLinear (γ⁻¹).mat)`. Establish `hL : HasFDerivAt (fun Q => flat τ Q ᵥ* (γ⁻¹).mat) (L.comp (fderiv ℝ (flat τ) P)) P` using `L.hasFDerivAt.comp P hG.hasFDerivAt`.

Establish `heq : (flat (fun b => moeb γ (τ b)) ∘ reframe τ γ) =ᶠ[nhds P] fun Q => flat τ Q ᵥ* (γ⁻¹).mat` using `Filter.eventually_of_mem (hopen.mem_nhds hP) fun Q hQ => hpt Q hQ`. Establish `hd : (dflat (fun b => moeb γ (τ b)) (reframe τ γ P)).comp (fderiv ℝ (reframe τ γ) P) = L.comp (dflat τ P)`. Rewrite using `[dflat, dflat, ← fderiv_comp P hF hRd, heq.fderiv_eq, hL.fderiv]`. Use extensionality with `v`. Establish `h0` using `congrArg (fun f => f (v 0)) hd`.

Establish `h1` using `congrArg (fun f => f (v 1)) hd`. Simplify using `only [ContinuousLinearMap.comp_apply] at h0 h1`. Use `show riem (dflat _ (reframe τ γ P) (fderiv ℝ (reframe τ γ) P (v 0))) (dflat _ (reframe τ γ P) (fderiv ℝ (reframe τ γ) P (v 1))) = riem (dflat τ P (v 0)) (dflat τ P (v 1))`. Rewrite using `[h0, h1]`. Conclude with `riem_vecMul_symp γ⁻¹ _ _`.
-/
theorem flat_reframe {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap B τ) (γ : Sp g) (P : Pt E g) (hP : P ∈ cov B g) :
    flat (fun b => moeb γ (τ b)) (reframe τ γ P) = flat τ P ᵥ* (γ⁻¹).mat ∧
      pull (reframe τ γ) (om0 fun b => moeb γ (τ b)) P = om0 τ P := by
  obtain ⟨hτ', hY, hR⟩ := GlobalTheory.T.period_map_symplectic_transform hτ γ
  have hopen : IsOpen (cov B g) := hτ.1.prod isOpen_univ
  have hpt : ∀ Q ∈ cov B g, flat (fun b => moeb γ (τ b)) (reframe τ γ Q) =
      flat τ Q ᵥ* (γ⁻¹).mat := fun Q hQ =>
    flat_reframe_pt γ Q (hτ.2.2 _ hQ.1) (hτ'.2.2 _ hQ.1) (hY _ hQ.1)
  refine ⟨hpt P hP, ?_⟩
  have hRP : reframe τ γ P ∈ cov B g := ⟨hP.1, trivial⟩
  have hF := flat_diffAt hτ' hRP
  have hRd : DifferentiableAt ℝ (reframe τ γ) P :=
    ((hR P hP).differentiableAt (hopen.mem_nhds hP)).restrictScalars ℝ
  have hG := flat_diffAt hτ hP
  let L : Fl g →L[ℝ] Fl g := LinearMap.toContinuousLinearMap (Matrix.vecMulLinear (γ⁻¹).mat)
  have hL : HasFDerivAt (fun Q => flat τ Q ᵥ* (γ⁻¹).mat) (L.comp (fderiv ℝ (flat τ) P)) P :=
    L.hasFDerivAt.comp P hG.hasFDerivAt
  have heq : (flat (fun b => moeb γ (τ b)) ∘ reframe τ γ) =ᶠ[nhds P]
      fun Q => flat τ Q ᵥ* (γ⁻¹).mat :=
    Filter.eventually_of_mem (hopen.mem_nhds hP) fun Q hQ => hpt Q hQ
  have hd : (dflat (fun b => moeb γ (τ b)) (reframe τ γ P)).comp (fderiv ℝ (reframe τ γ) P) =
      L.comp (dflat τ P) := by
    rw [dflat, dflat, ← fderiv_comp P hF hRd, heq.fderiv_eq, hL.fderiv]
  ext v
  have h0 := congrArg (fun f => f (v 0)) hd
  have h1 := congrArg (fun f => f (v 1)) hd
  simp only [ContinuousLinearMap.comp_apply] at h0 h1
  show riem (dflat _ (reframe τ γ P) (fderiv ℝ (reframe τ γ) P (v 0)))
      (dflat _ (reframe τ γ P) (fderiv ℝ (reframe τ γ) P (v 1))) = riem (dflat τ P (v 0)) (dflat τ P (v 1))
  rw [h0, h1]
  exact riem_vecMul_symp γ⁻¹ _ _

end GlobalTheory.SympFlatChange

/- English proof (translation)
Introduce `hτ γ P hP` and use `GlobalTheory.SympFlatChange.flat_reframe hτ γ P hP`.
-/
theorem GlobalTheory.sympFlat_change : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ γ : Sp g, ∀ P ∈ cov B g, flat (fun b => moeb γ (τ b)) (reframe τ γ P) = flat τ P ᵥ* (γ⁻¹).mat ∧ pull (reframe τ γ) (om0 fun b => moeb γ (τ b)) P = om0 τ P :=
  fun hτ γ P hP => GlobalTheory.SympFlatChange.flat_reframe hτ γ P hP
