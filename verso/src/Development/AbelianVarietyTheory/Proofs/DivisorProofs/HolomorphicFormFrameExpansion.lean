import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionTorusEquivariantOrthonormalFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnFramesOfKilledNilpotentDerivativStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameUnitCorrespondenceStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.AdExt

section Mat
variable {n : ℕ} {G S x : Matrix (Fin n) (Fin n) ℂ}

/- English proof (translation)
Rewrite using `[← h]`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`.
-/
theorem conj_form (hx : IsUnit x.det) (h : xᴴ * G * x = S) (A B : Matrix (Fin n) (Fin n) ℂ) :
    (x * A * x⁻¹)ᴴ * G * (x * B * x⁻¹) = x⁻¹ᴴ * (Aᴴ * S * B) * x⁻¹ := by
  rw [← h]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Use `congrArg det h` as an intermediate fact. Rewrite `this` using `[det_mul, h0, mul_zero, det_diagonal]`. Use `Finset.prod_ne_zero_iff.2 (fun c _ => ?_) this.symm` and prove the remaining obligations.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem isUnit_det_of_sign {q : ℕ} (h : xᴴ * G * x = diagonal fun c : Fin n => if (c : ℕ) < q then (-1 : ℂ) else 1) :
    IsUnit x.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have := congrArg det h
  rw [det_mul, h0, mul_zero, det_diagonal] at this
  refine Finset.prod_ne_zero_iff.2 (fun c _ => ?_) this.symm
  split_ifs <;> simp

/- English proof (translation)
Establish `h1` using `conj_form hx h Z 1`. Establish `h2` using `conj_form hx h 1 Z`. Rewrite `h1`, `h2` using `[Matrix.mul_one, mul_nonsing_inv _ hx]`. Rewrite `h1` using `[Matrix.mul_one]`. Rewrite `h2` using `[conjTranspose_one, Matrix.one_mul]`.

Rewrite using `[h1, h2, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, hZ]`. Simplify using the standard rewrite rules.
-/
theorem conj_mem_lie (hx : IsUnit x.det) (h : xᴴ * G * x = S) {Z : Matrix (Fin n) (Fin n) ℂ}
    (hZ : Zᴴ * S + S * Z = 0) : (x * Z * x⁻¹)ᴴ * G + G * (x * Z * x⁻¹) = 0 := by
  have h1 := conj_form hx h Z 1
  have h2 := conj_form hx h 1 Z
  rw [Matrix.mul_one, mul_nonsing_inv _ hx] at h1 h2
  rw [Matrix.mul_one] at h1
  rw [conjTranspose_one, Matrix.one_mul] at h2
  rw [h1, h2, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, hZ]
  simp

/- English proof (translation)
Establish `h2` using `conj_form hx h 1 1`. Rewrite `h2` using `[Matrix.mul_one, mul_nonsing_inv _ hx, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]`. Rewrite using `[conj_form hx h, hA, ← h2]`.
-/
theorem conj_mem_unitary (hx : IsUnit x.det) (h : xᴴ * G * x = S) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : Aᴴ * S * A = S) : (x * A * x⁻¹)ᴴ * G * (x * A * x⁻¹) = G := by
  have h2 := conj_form hx h 1 1
  rw [Matrix.mul_one, mul_nonsing_inv _ hx, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_one] at h2
  rw [conj_form hx h, hA, ← h2]

/- English proof (translation)
Rewrite using `[diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `c`. Establish `: star (Complex.exp ((t c : ℂ) * Complex.I)) * Complex.exp ((t c : ℂ) * Complex.I) = 1`. Rewrite using `[Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]`.

Simplify using the standard rewrite rules. Simplify using `only [Pi.star_apply]`. Take the linear combination `s c * this`.
-/
theorem diag_unitary (s : Fin n → ℂ) (t : Fin n → ℝ) :
    (diagonal fun c => Complex.exp ((t c : ℂ) * Complex.I))ᴴ * diagonal s *
      (diagonal fun c => Complex.exp ((t c : ℂ) * Complex.I)) = diagonal s := by
  rw [diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext c
  have : star (Complex.exp ((t c : ℂ) * Complex.I)) * Complex.exp ((t c : ℂ) * Complex.I) = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp
  simp only [Pi.star_apply]
  linear_combination s c * this

/- English proof (translation)
Establish `e1 : (G⁻¹ * Wᴴ * G)ᴴ * G = G * W`. Rewrite using `[conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hG]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[nonsing_inv_mul _ hd, Matrix.mul_one]`. Establish `e2 : G * (G⁻¹ * Wᴴ * G) = Wᴴ * G`.

Rewrite using `[Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hd]`. Establish `e3 : star (1 / 2 : ℂ) = 1 / 2` using `by simp`. Rewrite using `[conjTranspose_smul, e3, smul_mul_assoc, mul_smul_comm, ← smul_add, conjTranspose_add, conjTranspose_neg, Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, e1, e2]`. Simplify using the standard rewrite rules.
-/
theorem half_mem_lie (hG : Gᴴ = G) (hd : IsUnit G.det) (W : Matrix (Fin n) (Fin n) ℂ) :
    ((1 / 2 : ℂ) • (W + -(G⁻¹ * Wᴴ * G)))ᴴ * G + G * ((1 / 2 : ℂ) • (W + -(G⁻¹ * Wᴴ * G))) = 0 := by
  have e1 : (G⁻¹ * Wᴴ * G)ᴴ * G = G * W := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hG]
    simp only [Matrix.mul_assoc]
    rw [nonsing_inv_mul _ hd, Matrix.mul_one]
  have e2 : G * (G⁻¹ * Wᴴ * G) = Wᴴ * G := by
    rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hd]
  have e3 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [conjTranspose_smul, e3, smul_mul_assoc, mul_smul_comm, ← smul_add, conjTranspose_add, conjTranspose_neg,
    Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, e1, e2]
  simp

/- English proof (translation)
Rewrite using `[Matrix.mul_assoc, eq_neg_of_add_eq_zero_left hW, Matrix.mul_neg, neg_neg, nonsing_inv_mul_cancel_left _ _ hd]`.
-/
theorem conj_eq_of_mem_lie (hd : IsUnit G.det) {W : Matrix (Fin n) (Fin n) ℂ} (hW : Wᴴ * G + G * W = 0) :
    -(G⁻¹ * Wᴴ * G) = W := by
  rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left hW, Matrix.mul_neg, neg_neg, nonsing_inv_mul_cancel_left _ _ hd]

end Mat

variable {D : D7} {θ : InfFam D} {V : HSp D}

/- English proof (translation)
Establish `h : ∃ k, IsAtTau θ V ρ g k`. Take `⟨k, hk, h⟩` from `R.2.1 (fun τ => if τ = ρ then g else 1) fun τ => by`. Express the relevant statement in the definitionally equal form `_ᴴ * _ * _ = _`. Use `split_ifs with c`. Substitute `c` using the available equality.

Conclude with `hg`. Simplify using the standard rewrite rules. Conclude with `⟨k, hk, by simpa using h ρ, fun τ c => by simpa [c] using h τ⟩`. Rewrite using `[atTau, dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem atTau_spec (R : RealPoints θ V) (ρ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : gᴴ * gramAt D V ρ * g = gramAt D V ρ) : IsAtTau θ V ρ g (atTau θ V ρ g) := by
  have h : ∃ k, IsAtTau θ V ρ g k := by
    obtain ⟨k, hk, h⟩ := R.2.1 (fun τ => if τ = ρ then g else 1) fun τ => by
      change _ᴴ * _ * _ = _
      split_ifs with c
      · subst c; exact hg
      · simp
    exact ⟨k, hk, by simpa using h ρ, fun τ c => by simpa [c] using h τ⟩
  rw [atTau, dif_pos h]
  exact h.choose_spec

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Conclude with `⟨1, one_mem _, fun ρ => by simpa using R.2.2.2.2.1 1 (one_mem _) ρ, by simp⟩`. Consider the case `insert ρ s hρ ih`. Take `⟨k, hk, h1, h2⟩` from `ih`.

Establish `ha` using `atTau_spec R ρ (conj_mem_unitary (isUnit_det_of_sign (hx ρ)) (hx ρ) (diag_unitary _ (t ρ)))`. Use `⟨k * _, mul_mem hk ha.1, fun τ => ?_, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[R.2.2.2.1, h1]`. Distinguish the cases in `c : τ = ρ`. Substitute `c` using the available equality.

Rewrite using `[ha.2.1]`. Simplify using `[hρ]`. Rewrite using `[ha.2.2 _ c]`. Simplify using `[c]`. Rewrite using `[← mul_assoc, hφ.2.2, h2, Finset.prod_insert hρ, mul_assoc]`.
-/
theorem exists_torus (R : RealPoints θ V) {q : ℕ} {x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hx : NegFirst V q x) {w : D.what₂.Tau → Fin V.rank → ℤ} {φ : GA D V → ℂ} (hφ : IsHolFor θ V x w φ)
    (t : D.what₂.Tau → Fin V.rank → ℝ) (s : Finset D.what₂.Tau) :
    ∃ k ∈ GinfC V, (∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) k = if ρ ∈ s then
      x ρ * diagonal (fun c => Complex.exp ((t ρ c : ℂ) * Complex.I)) * (x ρ)⁻¹ else 1) ∧
      ∀ h, φ (h * k) = (∏ ρ ∈ s, Complex.exp (((∑ c, (w ρ c : ℝ) * t ρ c : ℝ) : ℂ) * Complex.I)) * φ h := by
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1, one_mem _, fun ρ => by simpa using R.2.2.2.2.1 1 (one_mem _) ρ, by simp⟩
  | insert ρ s hρ ih =>
    obtain ⟨k, hk, h1, h2⟩ := ih
    have ha := atTau_spec R ρ (conj_mem_unitary (isUnit_det_of_sign (hx ρ)) (hx ρ) (diag_unitary _ (t ρ)))
    refine ⟨k * _, mul_mem hk ha.1, fun τ => ?_, fun h => ?_⟩
    · rw [R.2.2.2.1, h1]
      by_cases c : τ = ρ
      · subst c
        rw [ha.2.1]; simp [hρ]
      · rw [ha.2.2 _ c]; simp [c]
    · rw [← mul_assoc, hφ.2.2, h2, Finset.prod_insert hρ, mul_assoc]

def toLie (R : RealPoints θ V) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {Ψ : Finset (D.host.E →+* ℂ)}
    (σ : D.what₂.Tau → Ψ) : Frame Ψ V.rank →ₗ[ℝ] LieN V where
  toFun Z := fun ρ => ⟨(1 / 2 : ℂ) • (x ρ * mat Z (σ ρ) * (x ρ)⁻¹ + conjAt V ρ (x ρ * mat Z (σ ρ) * (x ρ)⁻¹)),
    half_mem_lie (R.1 ρ).1 (R.1 ρ).2 _⟩
  map_add' Z Z' := funext fun ρ => Subtype.ext (by
    have : mat (Z + Z') (σ ρ) = mat Z (σ ρ) + mat Z' (σ ρ) := rfl
    change (1 / 2 : ℂ) • _ = (1 / 2 : ℂ) • _ + (1 / 2 : ℂ) • _
    simp only [this, conjAt, Matrix.mul_add, Matrix.add_mul, conjTranspose_add]
    module)
  map_smul' c Z := funext fun ρ => Subtype.ext (by
    have : mat (c • Z) (σ ρ) = c • mat Z (σ ρ) := rfl
    change (1 / 2 : ℂ) • _ = c • (1 / 2 : ℂ) • _
    simp only [this, conjAt, mul_smul_comm, smul_mul_assoc, conjTranspose_smul, star_trivial]
    module)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toLie_val (R : RealPoints θ V) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {Ψ : Finset (D.host.E →+* ℂ)}
    (σ : D.what₂.Tau → Ψ) (Z : Frame Ψ V.rank) (ρ : D.what₂.Tau) : (toLie R x σ Z ρ).1 =
    (1 / 2 : ℂ) • (x ρ * mat Z (σ ρ) * (x ρ)⁻¹ + conjAt V ρ (x ρ * mat Z (σ ρ) * (x ρ)⁻¹)) := rfl

/- English proof (translation)
Establish `: mat (Complex.I • Z) (σ ρ) = Complex.I • mat Z (σ ρ)` using `rfl`. Rewrite using `[toLie_val]`. Simplify using `only [this, conjAt, mul_smul_comm, smul_mul_assoc, conjTranspose_smul, Complex.star_def, Complex.conj_I]`. Use `module`.
-/
theorem toLie_I (R : RealPoints θ V) (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) {Ψ : Finset (D.host.E →+* ℂ)}
    (σ : D.what₂.Tau → Ψ) (Z : Frame Ψ V.rank) (ρ : D.what₂.Tau) : (toLie R x σ (Complex.I • Z) ρ).1 =
    (Complex.I / 2 : ℂ) • (x ρ * mat Z (σ ρ) * (x ρ)⁻¹ - conjAt V ρ (x ρ * mat Z (σ ρ) * (x ρ)⁻¹)) := by
  have : mat (Complex.I • Z) (σ ρ) = Complex.I • mat Z (σ ρ) := rfl
  rw [toLie_val]
  simp only [this, conjAt, mul_smul_comm, smul_mul_assoc, conjTranspose_smul, Complex.star_def, Complex.conj_I]
  module

/- English proof (translation)
Use `conj_eq_of_mem_lie (R.1 ρ).2 (conj_mem_lie (isUnit_det_of_sign (hx ρ)) (hx ρ) ?_)` and prove the remaining obligations. Establish `e : (diagonal fun c : Fin V.rank => if (c : ℕ) < X.p0 then (-1 : ℂ) else 1) = -diagonal fun a : Fin V.rank => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)`. Rewrite using `[diagonal_neg]`. Use `congr 1`. Use function extensionality and compare the values at `c`.

Unfold `sgn`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[e, Matrix.mul_neg, Matrix.neg_mul, ← neg_add, hZ (σ ρ), neg_zero]`.
-/
theorem conjAt_unitLie (R : RealPoints θ V) {X : Data D.host.E V.rank}
    {x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hx : NegFirst V X.p0 x) (σ : D.what₂.Tau → X.Ψ)
    {Z : Frame X.Ψ V.rank} (hZ : Z ∈ unitLie X) (ρ : D.what₂.Tau) :
    conjAt V ρ (x ρ * mat Z (σ ρ) * (x ρ)⁻¹) = x ρ * mat Z (σ ρ) * (x ρ)⁻¹ := by
  refine conj_eq_of_mem_lie (R.1 ρ).2 (conj_mem_lie (isUnit_det_of_sign (hx ρ)) (hx ρ) ?_)
  have e : (diagonal fun c : Fin V.rank => if (c : ℕ) < X.p0 then (-1 : ℂ) else 1) =
      -diagonal fun a : Fin V.rank => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
    rw [diagonal_neg]
    congr 1
    funext c
    unfold sgn
    split_ifs <;> simp
  rw [e, Matrix.mul_neg, Matrix.neg_mul, ← neg_add, hZ (σ ρ), neg_zero]

/- English proof (translation)
Rewrite using `[Rder_eq R]`. Establish `h1 : ∀ Y' : LieN V, HasDerivAt (fun t : ℝ => t • Y') Y' 0` using `fun Y' => by`. Simplify using `using (hasDerivAt_id (0 : ℝ)).smul_const Y'`. Establish `h2` using `hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (h1 (atPlace V ρ Y)) (zero_smul ℝ _).symm`. Conclude with `h2.deriv.symm`.
-/
theorem fderiv_atPlace (R : RealPoints θ V) {φ : GA D V → ℂ} (g : GA D V)
    (hf : DifferentiableAt ℝ (fun Y : LieN V => φ (g * expInf θ V Y)) 0) (ρ : D.what₂.Tau) (Y : LieAt V ρ) :
    fderiv ℝ (fun Y : LieN V => φ (g * expInf θ V Y)) 0 (atPlace V ρ Y : LieN V) = Rder θ V ρ Y.1 φ g := by
  rw [Rder_eq R]
  have h1 : ∀ Y' : LieN V, HasDerivAt (fun t : ℝ => t • Y') Y' 0 := fun Y' => by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const Y'
  have h2 := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (h1 (atPlace V ρ Y)) (zero_smul ℝ _).symm
  exact h2.deriv.symm

/- English proof (translation)
The claim follows from `(RealPts.infMat_eq ..).symm`.
-/
theorem archM_eq (ρ : D.what₂.Tau) (u : GA D V) : archM V (θ ρ) u = infMat D.sp.cm.sig V.gram (θ ρ) u :=
  (RealPts.infMat_eq ..).symm

/- English proof (translation)
Use extensionality with `a b`. Distinguish the cases in `h : τ' = τ`. Simplify using `[mat, unitFr, h, Matrix.single, eq_comm]`. Simplify using `[mat, unitFr, h]`.
-/
theorem mat_unitFr {Ψ : Finset (D.host.E →+* ℂ)} {r : ℕ} (τ τ' : Ψ) (c d : Fin r) :
    mat (unitFr τ c d) τ' = if τ' = τ then Matrix.single c d 1 else 0 := by
  ext a b
  by_cases h : τ' = τ
  · simp [mat, unitFr, h, Matrix.single, eq_comm]
  · simp [mat, unitFr, h]

/- English proof (translation)
Take `⟨U1, U2, -, -, U5⟩` from `GlobalTheory.T.frame_unit_correspondence D θ V r hr X x hθ hM hx`. Substitute `hr` using the available equality. Establish `R : RealPoints θ V` using `(RealPts.realPoints D).2 θ hθ V`. Set `σ : D.what₂.Tau → X.Ψ` to `fun ρ => ⟨tauE D ρ, (hM.1 _).2 ⟨ρ, rfl⟩⟩`. Establish `σinj : Function.Injective σ` using `fun a b h => RealPts.tauE_injective D (congrArg Subtype.val h)`.

Establish `σsurj : Function.Surjective σ` using `fun τ => by`. Take `⟨ρ, h⟩` from `(hM.1 τ.1).1 τ.2`. Conclude with `⟨ρ, Subtype.ext h.symm⟩`. Establish `hxu : ∀ ρ, IsUnit (x ρ).det` using `fun ρ => isUnit_det_of_sign (hx ρ)`. Establish `frIs : ∀ u y, FrIs θ V rfl X x u y ↔ ∀ ρ, mat y (σ ρ) = infMat D.sp.cm.sig V.gram (θ ρ) u * x ρ`.

Introduce `u y`. Prove the components needed by the constructor for the conclusion. Introduce `h ρ`. Rewrite using `[h ρ (σ ρ) rfl, archM_eq]`. Both sides reduce to the same expression.

Introduce `h ρ τ e`. Take `rfl : τ = σ ρ` from `Subtype.ext e`. Rewrite using `[h ρ, archM_eq]`. Both sides reduce to the same expression. Establish `frMul : ∀ u y k b, FrIs θ V rfl X x u y → (∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) k = x ρ * mat b (σ ρ) * (x ρ)⁻¹) → FrIs θ V rfl X x (u * k) (rmul y b)`.

Introduce `u y k b h hk`. Rewrite `h`, the goal using `[frIs]`. Introduce `ρ`. Express the relevant statement in the definitionally equal form `mat y (σ ρ) * mat b (σ ρ) = _`. Rewrite using `[h, R.2.2.2.1, hk]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[nonsing_inv_mul _ (hxu ρ), Matrix.mul_one]`. Set `F : Frame X.Ψ V.rank → ℂ` to `fun y => if h : IsUnitFr X y then φ (g * (U2 y h).choose) else 0`. Establish `hF : ∀ u ∈ GinfC V, ∀ y, FrIs θ V rfl X x u y → F y = φ (g * u)`. Introduce `u hu y h`.

Establish `hy` using `U1 u y h`. Simplify using `only [F, dif_pos hy]`. Rewrite using `[U5 _ (U2 y hy).choose_spec.1 u hu y (U2 y hy).choose_spec.2 h]`. Take `⟨Q, Q1, Q2⟩` from `GlobalTheory.T.exists_extension_torusEquivariant_orthonormalFrames _ _ X la F (by`. Introduce `y hy t`.

Take `⟨u, hu, h⟩` from `U2 y hy`. Take `⟨k, hk, k1, k2⟩` from `exists_torus R hx hφ (fun ρ => t (σ ρ)) Finset.univ`. Use `(hF (u * k) (mul_mem hu hk) _ (frMul u y k _ h fun ρ => ?_)).trans ?_` and prove the remaining obligations. Rewrite using `[k1, if_pos (Finset.mem_univ _)]`. Both sides reduce to the same expression.

Rewrite using `[hF u hu y h, ← mul_assoc, k2]`. Use `congr 1`. Unfold `bchar`. Use `Fintype.prod_bijective σ ⟨σinj, σsurj⟩ _ _ fun ρ => ?_` and prove the remaining obligations. Use `push_cast`.

Rewrite using `[Finset.sum_mul, Complex.exp_sum]`. Use `Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[diagonal_apply_eq, ← hw ρ (σ ρ) rfl c, mul_assoc, Complex.exp_int_mul]`. Use the proof step `rfl)`. Establish `hQ : ∀ u ∈ GinfC V, ∀ y, FrIs θ V rfl X x u y → Q y = φ (g * u)` using `fun u hu y h => by`.

Rewrite using `[Q1 y (U1 u y h), hF u hu y h]`. Use `⟨Q, GlobalTheory.T.differentiableOn_frames_of_killedNilpotentDerivative _ _ X la Q Q2 fun y hy => ?_, Q2, hQ⟩` and prove the remaining obligations. Take `⟨u, hu, h⟩` from `U2 y hy`. Establish `hs : DifferentiableAt ℝ (fun Y : LieN V => φ (g * u * expInf θ V Y)) 0` using `(((isSmoothInf_iff φ).1 ((smooth_iff R φ).1 hφ.1) (g * u)).differentiable (by simp)) 0`. Set `L : Frame X.Ψ V.rank →L[ℝ] LieN V` to `LinearMap.toContinuousLinearMap (toLie R x σ)`.

Establish `hL : ∀ Z, L Z = toLie R x σ Z` using `fun _ => rfl`. Establish `hv : ∀ Z ∈ unitLie X, ∀ ρ, (toLie R x σ Z ρ).1 = x ρ * mat Z (σ ρ) * (x ρ)⁻¹` using `fun Z hZ ρ => by`. Rewrite using `[toLie_val, conjAt_unitLie R hx σ hZ]`. Use `module`. Establish `hI : ∀ Z ∈ unitLie X, toLie R x σ (Complex.I • Z) = 0` using `fun Z hZ => funext fun ρ => Subtype.ext (by`.

Rewrite using `[toLie_I, conjAt_unitLie R hx σ hZ, sub_self, smul_zero]`. Use the proof step `rfl)`. Establish `key : ∀ Z ∈ unitLie X, Q (rmul y (expFr Z)) = φ (g * u * expInf θ V (L Z))`. Introduce `Z hZ`. Establish `he` using `isExpFam_expInf R (toLie R x σ Z)`.

Rewrite using `[mul_assoc]`. Use `hQ _ (mul_mem hu he.1) _ (frMul u y _ _ h fun ρ => (he.2 ρ).trans ?_)` and prove the remaining obligations. Use `(congrArg NormedSpace.exp (hv Z hZ ρ)).trans ?_` and prove the remaining obligations. Rewrite using `[Matrix.exp_conj _ _ ((isUnit_iff_isUnit_det _).2 (hxu ρ))]`. Both sides reduce to the same expression.

Establish `h0 : (0 : Frame X.Ψ V.rank) ∈ unitLie X` using `fun τ => by`. Establish `: mat (0 : Frame X.Ψ V.rank) τ = 0` using `rfl`. Simplify using `[this]`. Use `⟨(fderiv ℝ (fun Y : LieN V => φ (g * u * expInf θ V Y)) 0).comp L, ?_, ?_⟩` and prove the remaining obligations. Establish `hs' : HasFDerivAt (fun Y : LieN V => φ (g * u * expInf θ V Y)) (fderiv ℝ (fun Y : LieN V => φ (g * u * expInf θ V Y)) 0) (L 0)`.

Rewrite using `[map_zero]`. Conclude with `hs.hasFDerivAt`. Establish `h1` using `hs'.comp (0 : Frame X.Ψ V.rank) L.hasFDerivAt`. Conclude with `h1.hasFDerivWithinAt.congr key (key 0 h0)`. Introduce `τ c d hcd Z hZ Z' hZ' e`.

Take `⟨ρ, rfl⟩` from `σsurj τ`. Establish `e1 : toLie R x σ Z = toLie R x σ (unitFr (σ ρ) c d)` using `by rw [← e, map_add, hI Z' hZ', add_zero]`. Establish `e2 : toLie R x σ Z' = -toLie R x σ (Complex.I • unitFr (σ ρ) c d)`. Rewrite using `[← e, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul, map_add, hI Z hZ, map_neg, zero_add, neg_neg]`. Establish `at1 : ∀ Y : LieN V, (∀ ρ', ρ' ≠ ρ → (Y ρ').1 = 0) → Y = atPlace V ρ ⟨(Y ρ).1, (Y ρ).2⟩`.

Introduce `Y hY`. Use function extensionality and compare the values at `ρ'`. Distinguish the cases in `cc : ρ' = ρ`. Substitute `cc` using the available equality. Simplify using `only [atPlace, Pi.single_eq_same]`.

Both sides reduce to the same expression. Simplify using `only [atPlace, Pi.single_eq_of_ne cc]`. Conclude with `Subtype.ext (hY ρ' cc)`. Establish `z : ∀ ρ', ρ' ≠ ρ → mat (unitFr (σ ρ) c d) (σ ρ') = 0` using `fun ρ' cc => by`. Rewrite using `[mat_unitFr, if_neg fun e => cc (σinj e)]`.

Establish `z' : mat (unitFr (σ ρ) c d) (σ ρ) = Matrix.single c d 1` using `by rw [mat_unitFr, if_pos rfl]`. Establish `hneg : ∀ (Y : LieN V) ρ', ((-Y) ρ').1 = -(Y ρ').1` using `fun _ _ => rfl`. Establish `a1` using `at1 (toLie R x σ Z) fun ρ' cc => by rw [e1, toLie_val, z ρ' cc]; simp [conjAt]`. Establish `a2` using `at1 (toLie R x σ Z') fun ρ' cc => by rw [e2, hneg, toLie_I, z ρ' cc]; simp [conjAt]`. Establish `hk` using `congrFun (hφ.2.1 ρ c d hcd) (g * u)`.

Rewrite using `[ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hL, hL, a1, a2, fderiv_atPlace R _ hs, fderiv_atPlace R _ hs]`. Establish `v1 : (toLie R x σ Z ρ).1 = (1 / 2 : ℂ) • (x ρ * Matrix.single c d 1 * (x ρ)⁻¹ + conjAt V ρ (x ρ * Matrix.single c d 1 * (x ρ)⁻¹))` using `by rw [e1, toLie_val, z']`. Establish `v2 : (toLie R x σ Z' ρ).1 = (1 / (2 * Complex.I) : ℂ) • (x ρ * Matrix.single c d 1 * (x ρ)⁻¹ - conjAt V ρ (x ρ * Matrix.single c d 1 * (x ρ)⁻¹))`. Rewrite using `[e2, hneg, toLie_I, z', ← neg_smul]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `Rder θ V ρ (toLie R x σ Z ρ).1 φ _ + _ * Rder θ V ρ (toLie R x σ Z' ρ).1 φ _ = 0`. Rewrite using `[v1, v2]`. Conclude with `hk`.
-/
theorem exists_extension (D : D7) (θ : InfFam D) (V : HSp D) (r : ℕ) (hr : V.rank = r) (X : Data D.host.E r)
    (x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (w : D.what₂.Tau → Fin V.rank → ℤ)
    (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (φ : GA D V → ℂ) (hθ : IsInfFam θ) (hM : ModelOf V hr X)
    (hx : NegFirst V X.p0 x)
    (hw : ∀ (ρ : D.what₂.Tau) (τ : X.Ψ), τ.1 = tauE D ρ → ∀ c : Fin V.rank, la τ (Fin.cast hr c) = w ρ c)
    (hφ : IsHolFor θ V x w φ) (g : GA D V) :
    ∃ Q : Frame X.Ψ r → ℂ, DifferentiableOn ℂ Q X.dom ∧
      (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul y b) = bchar la b * Q y) ∧
      ∀ u ∈ GinfC V, ∀ y, FrIs θ V hr X x u y → Q y = φ (g * u) := by
  obtain ⟨U1, U2, -, -, U5⟩ := GlobalTheory.T.frame_unit_correspondence D θ V r hr X x hθ hM hx
  subst hr
  have R : RealPoints θ V := (RealPts.realPoints D).2 θ hθ V
  let σ : D.what₂.Tau → X.Ψ := fun ρ => ⟨tauE D ρ, (hM.1 _).2 ⟨ρ, rfl⟩⟩
  have σinj : Function.Injective σ := fun a b h => RealPts.tauE_injective D (congrArg Subtype.val h)
  have σsurj : Function.Surjective σ := fun τ => by
    obtain ⟨ρ, h⟩ := (hM.1 τ.1).1 τ.2
    exact ⟨ρ, Subtype.ext h.symm⟩
  have hxu : ∀ ρ, IsUnit (x ρ).det := fun ρ => isUnit_det_of_sign (hx ρ)
  have frIs : ∀ u y, FrIs θ V rfl X x u y ↔ ∀ ρ, mat y (σ ρ) = infMat D.sp.cm.sig V.gram (θ ρ) u * x ρ := by
    intro u y
    constructor
    · intro h ρ
      rw [h ρ (σ ρ) rfl, archM_eq]; rfl
    · intro h ρ τ e
      obtain rfl : τ = σ ρ := Subtype.ext e
      rw [h ρ, archM_eq]; rfl
  have frMul : ∀ u y k b, FrIs θ V rfl X x u y →
      (∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) k = x ρ * mat b (σ ρ) * (x ρ)⁻¹) →
      FrIs θ V rfl X x (u * k) (rmul y b) := by
    intro u y k b h hk
    rw [frIs] at h ⊢
    intro ρ
    change mat y (σ ρ) * mat b (σ ρ) = _
    rw [h, R.2.2.2.1, hk]
    simp only [Matrix.mul_assoc]
    rw [nonsing_inv_mul _ (hxu ρ), Matrix.mul_one]
  let F : Frame X.Ψ V.rank → ℂ := fun y => if h : IsUnitFr X y then φ (g * (U2 y h).choose) else 0
  have hF : ∀ u ∈ GinfC V, ∀ y, FrIs θ V rfl X x u y → F y = φ (g * u) := by
    intro u hu y h
    have hy := U1 u y h
    simp only [F, dif_pos hy]
    rw [U5 _ (U2 y hy).choose_spec.1 u hu y (U2 y hy).choose_spec.2 h]
  obtain ⟨Q, Q1, Q2⟩ := GlobalTheory.T.exists_extension_torusEquivariant_orthonormalFrames _ _ X la F (by
    intro y hy t
    obtain ⟨u, hu, h⟩ := U2 y hy
    obtain ⟨k, hk, k1, k2⟩ := exists_torus R hx hφ (fun ρ => t (σ ρ)) Finset.univ
    refine (hF (u * k) (mul_mem hu hk) _ (frMul u y k _ h fun ρ => ?_)).trans ?_
    · rw [k1, if_pos (Finset.mem_univ _)]; rfl
    rw [hF u hu y h, ← mul_assoc, k2]
    congr 1
    unfold bchar
    refine Fintype.prod_bijective σ ⟨σinj, σsurj⟩ _ _ fun ρ => ?_
    push_cast
    rw [Finset.sum_mul, Complex.exp_sum]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [diagonal_apply_eq, ← hw ρ (σ ρ) rfl c, mul_assoc, Complex.exp_int_mul]
    rfl)
  have hQ : ∀ u ∈ GinfC V, ∀ y, FrIs θ V rfl X x u y → Q y = φ (g * u) := fun u hu y h => by
    rw [Q1 y (U1 u y h), hF u hu y h]
  refine ⟨Q, GlobalTheory.T.differentiableOn_frames_of_killedNilpotentDerivative _ _ X la Q Q2 fun y hy => ?_, Q2, hQ⟩
  obtain ⟨u, hu, h⟩ := U2 y hy
  have hs : DifferentiableAt ℝ (fun Y : LieN V => φ (g * u * expInf θ V Y)) 0 :=
    (((isSmoothInf_iff φ).1 ((smooth_iff R φ).1 hφ.1) (g * u)).differentiable (by simp)) 0
  let L : Frame X.Ψ V.rank →L[ℝ] LieN V := LinearMap.toContinuousLinearMap (toLie R x σ)
  have hL : ∀ Z, L Z = toLie R x σ Z := fun _ => rfl
  have hv : ∀ Z ∈ unitLie X, ∀ ρ, (toLie R x σ Z ρ).1 = x ρ * mat Z (σ ρ) * (x ρ)⁻¹ := fun Z hZ ρ => by
    rw [toLie_val, conjAt_unitLie R hx σ hZ]
    module
  have hI : ∀ Z ∈ unitLie X, toLie R x σ (Complex.I • Z) = 0 := fun Z hZ => funext fun ρ => Subtype.ext (by
    rw [toLie_I, conjAt_unitLie R hx σ hZ, sub_self, smul_zero]; rfl)
  have key : ∀ Z ∈ unitLie X, Q (rmul y (expFr Z)) = φ (g * u * expInf θ V (L Z)) := by
    intro Z hZ
    have he := isExpFam_expInf R (toLie R x σ Z)
    rw [mul_assoc]
    refine hQ _ (mul_mem hu he.1) _ (frMul u y _ _ h fun ρ => (he.2 ρ).trans ?_)
    refine (congrArg NormedSpace.exp (hv Z hZ ρ)).trans ?_
    rw [Matrix.exp_conj _ _ ((isUnit_iff_isUnit_det _).2 (hxu ρ))]
    rfl
  have h0 : (0 : Frame X.Ψ V.rank) ∈ unitLie X := fun τ => by
    have : mat (0 : Frame X.Ψ V.rank) τ = 0 := rfl
    simp [this]
  refine ⟨(fderiv ℝ (fun Y : LieN V => φ (g * u * expInf θ V Y)) 0).comp L, ?_, ?_⟩
  · have hs' : HasFDerivAt (fun Y : LieN V => φ (g * u * expInf θ V Y))
        (fderiv ℝ (fun Y : LieN V => φ (g * u * expInf θ V Y)) 0) (L 0) := by
      rw [map_zero]; exact hs.hasFDerivAt
    have h1 := hs'.comp (0 : Frame X.Ψ V.rank) L.hasFDerivAt
    exact h1.hasFDerivWithinAt.congr key (key 0 h0)
  · intro τ c d hcd Z hZ Z' hZ' e
    obtain ⟨ρ, rfl⟩ := σsurj τ
    have e1 : toLie R x σ Z = toLie R x σ (unitFr (σ ρ) c d) := by rw [← e, map_add, hI Z' hZ', add_zero]
    have e2 : toLie R x σ Z' = -toLie R x σ (Complex.I • unitFr (σ ρ) c d) := by
      rw [← e, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul, map_add, hI Z hZ, map_neg, zero_add, neg_neg]
    have at1 : ∀ Y : LieN V, (∀ ρ', ρ' ≠ ρ → (Y ρ').1 = 0) → Y = atPlace V ρ ⟨(Y ρ).1, (Y ρ).2⟩ := by
      intro Y hY
      funext ρ'
      by_cases cc : ρ' = ρ
      · subst cc; simp only [atPlace, Pi.single_eq_same]; rfl
      · simp only [atPlace, Pi.single_eq_of_ne cc]; exact Subtype.ext (hY ρ' cc)
    have z : ∀ ρ', ρ' ≠ ρ → mat (unitFr (σ ρ) c d) (σ ρ') = 0 := fun ρ' cc => by
      rw [mat_unitFr, if_neg fun e => cc (σinj e)]
    have z' : mat (unitFr (σ ρ) c d) (σ ρ) = Matrix.single c d 1 := by rw [mat_unitFr, if_pos rfl]
    have hneg : ∀ (Y : LieN V) ρ', ((-Y) ρ').1 = -(Y ρ').1 := fun _ _ => rfl
    have a1 := at1 (toLie R x σ Z) fun ρ' cc => by rw [e1, toLie_val, z ρ' cc]; simp [conjAt]
    have a2 := at1 (toLie R x σ Z') fun ρ' cc => by rw [e2, hneg, toLie_I, z ρ' cc]; simp [conjAt]
    have hk := congrFun (hφ.2.1 ρ c d hcd) (g * u)
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hL, hL, a1, a2, fderiv_atPlace R _ hs,
      fderiv_atPlace R _ hs]
    have v1 : (toLie R x σ Z ρ).1 = (1 / 2 : ℂ) • (x ρ * Matrix.single c d 1 * (x ρ)⁻¹ +
        conjAt V ρ (x ρ * Matrix.single c d 1 * (x ρ)⁻¹)) := by rw [e1, toLie_val, z']
    have v2 : (toLie R x σ Z' ρ).1 = (1 / (2 * Complex.I) : ℂ) • (x ρ * Matrix.single c d 1 * (x ρ)⁻¹ -
        conjAt V ρ (x ρ * Matrix.single c d 1 * (x ρ)⁻¹)) := by
      rw [e2, hneg, toLie_I, z', ← neg_smul]
      congr 1
      field_simp
      simp
    change Rder θ V ρ (toLie R x σ Z ρ).1 φ _ + _ * Rder θ V ρ (toLie R x σ Z' ρ).1 φ _ = 0
    rw [v1, v2]
    exact hk

end GlobalTheory.HolRead.AdExt
