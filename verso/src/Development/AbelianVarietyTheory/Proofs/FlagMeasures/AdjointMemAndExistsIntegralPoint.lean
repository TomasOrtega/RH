import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.RatElt

/- English proof (translation)
Simplify using `only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply, mul_assoc]`.
-/
theorem hform_eq {E : Type} [CommRing E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) : Formalism.UG.hform (starRingEnd E) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply,
    mul_assoc]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, conjTranspose_apply, starRingEnd_apply]`.
-/
theorem cT_eq {E : Type} [CommRing E] [StarRing E] {n : ℕ} (M : Matrix (Fin n) (Fin n) E) :
    Formalism.UG.cT (starRingEnd E) M = Mᴴ := by
  ext i j
  simp [Formalism.UG.cT, conjTranspose_apply, starRingEnd_apply]

/- English proof (translation)
Establish `hc : Formalism.UG.cT τ (g.map f) = (Formalism.UG.cT σ g).map f`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, hf]`. Rewrite using `[hc, ← Matrix.map_mul, ← Matrix.map_mul, h]`.
-/
theorem unitary_map {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (σ : A →+* A) (τ : B →+* B)
    (f : A →+* B) (hf : ∀ e, τ (f e) = f (σ e)) (J g : Matrix (Fin n) (Fin n) A)
    (h : Formalism.UG.cT σ g * J * g = J) : Formalism.UG.cT τ (g.map f) * J.map f * g.map f = J.map f := by
  have hc : Formalism.UG.cT τ (g.map f) = (Formalism.UG.cT σ g).map f := by
    ext i j
    simp [Formalism.UG.cT, hf]
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, h]

/- English proof (translation)
Establish `hUJ : Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * γ = I.J` using `hγ`. Establish `hγH : (γ : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * γ = I.J` using `by rwa [cT_eq] at hUJ`. Set `γA : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))` to `Units.map (RingHom.mapMatrix (Formalism.UG.inclE (F := I.F) (Af I.F))).toMonoidHom γ`. Establish `hγA : (γA : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F` using `I.F) (Af I.F)) := rfl`. Establish `hA : γA ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F)`.

Unfold `Formalism.UG.UPts`. Use `show Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (γA : Matrix (Fin I.n) (Fin I.n) _) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * γA = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))`. Rewrite using `[hγA]`. Conclude with `unitary_map (starRingEnd I.E) _ _ (fun e => Formalism.UG.P.csDual_sig_incl I.cm.sig e) _ _ hUJ`. Set `Mu : ∀ v, (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ` to `fun v => (I.P_unit v).unit⁻¹ * Units.map (RingHom.mapMatrix (I.φ v)).toMonoidHom γ * (I.P_unit v).unit`.

Establish `hMu : ∀ v, (Mu v : Matrix (Fin I.n) (Fin I.n) ℂ) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v`. Introduce `v`. Simplify using `only [Mu, Units.val_mul, Matrix.coe_units_inv, IsUnit.unit_spec]`. Both sides reduce to the same expression. Establish `hU : ∀ v, Mu v ∈ Formalism.REAL.UJ (I.ε v)`.

Introduce `v`. Use `show Formalism.REAL.inUJ (I.ε v) (Mu v : Matrix (Fin I.n) (Fin I.n) ℂ)`. Unfold `Formalism.REAL.inUJ`. Use `set Q := I.P v with hQdef`. Use `set G := (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) with hGdef`.

Establish `hQ : Q * Q⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))`. Establish `hQH : Q⁻¹ᴴ * Qᴴ = 1` using `by rw [← Matrix.conjTranspose_mul, hQ, Matrix.conjTranspose_one]`. Establish `hGH : Gᴴ = (γ : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ.map (I.φ v)`. Use extensionality with `i j`. Simplify using `only [G, conjTranspose_apply, Matrix.map_apply]`.

Rewrite using `[I.cm.cmUnram.2.1 (I.φ v)]`. Both sides reduce to the same expression. Establish `hGJG : Gᴴ * (I.J.map (I.φ v) * (G * Q)) = I.J.map (I.φ v) * Q`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hGH, hGdef, ← Matrix.map_mul, ← Matrix.map_mul, hγH]`. Rewrite using `[hMu, ← I.P_spec v, ← hQdef, ← hGdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc Q⁻¹ᴴ Qᴴ, hQH, Matrix.one_mul, ← Matrix.mul_assoc Q Q⁻¹, hQ, Matrix.one_mul, hGJG]`. Conclude with `⟨⟨fun v => ⟨Mu v, hU v⟩, ⟨γA, hA⟩⟩, fun v => hMu v, hγA⟩`.
-/
theorem exists_point (I : AutInst) (γ : GL (Fin I.n) I.E)
    (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) : ∃ a : I.GA,
      (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  have hUJ : Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * γ = I.J := hγ
  have hγH : (γ : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * γ = I.J := by rwa [cT_eq] at hUJ
  let γA : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)) :=
    Units.map (RingHom.mapMatrix (Formalism.UG.inclE (F := I.F) (Af I.F))).toMonoidHom γ
  have hγA : (γA : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) =
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := rfl
  have hA : γA ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) := by
    unfold Formalism.UG.UPts
    show Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (γA : Matrix (Fin I.n) (Fin I.n) _) *
        I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * γA = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))
    rw [hγA]
    exact unitary_map (starRingEnd I.E) _ _ (fun e => Formalism.UG.P.csDual_sig_incl I.cm.sig e) _ _ hUJ

  let Mu : ∀ v, (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ := fun v =>
    (I.P_unit v).unit⁻¹ * Units.map (RingHom.mapMatrix (I.φ v)).toMonoidHom γ * (I.P_unit v).unit
  have hMu : ∀ v, (Mu v : Matrix (Fin I.n) (Fin I.n) ℂ) =
      (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
    intro v
    simp only [Mu, Units.val_mul, Matrix.coe_units_inv, IsUnit.unit_spec]
    rfl
  have hU : ∀ v, Mu v ∈ Formalism.REAL.UJ (I.ε v) := by
    intro v
    show Formalism.REAL.inUJ (I.ε v) (Mu v : Matrix (Fin I.n) (Fin I.n) ℂ)
    unfold Formalism.REAL.inUJ
    set Q := I.P v with hQdef
    set G := (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) with hGdef
    have hQ : Q * Q⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))
    have hQH : Q⁻¹ᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQ, Matrix.conjTranspose_one]
    have hGH : Gᴴ = (γ : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ.map (I.φ v) := by
      ext i j
      simp only [G, conjTranspose_apply, Matrix.map_apply]
      rw [I.cm.cmUnram.2.1 (I.φ v)]
      rfl
    have hGJG : Gᴴ * (I.J.map (I.φ v) * (G * Q)) = I.J.map (I.φ v) * Q := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGH, hGdef, ← Matrix.map_mul, ← Matrix.map_mul, hγH]
    rw [hMu, ← I.P_spec v, ← hQdef, ← hGdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q⁻¹ᴴ Qᴴ, hQH, Matrix.one_mul, ← Matrix.mul_assoc Q Q⁻¹, hQ, Matrix.one_mul, hGJG]
  exact ⟨⟨fun v => ⟨Mu v, hU v⟩, ⟨γA, hA⟩⟩, fun v => hMu v, hγA⟩

/- English proof (translation)
Introduce `y hy`. Take `⟨-, -, -, hdual, -⟩` from `GlobalTheory.PointLattice.lamX_selfDual I x`. Rewrite using `[hdual]`. Introduce `z hz`. Establish `hJ : I.J * I.J⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr I.J_det)`.

Establish `key : Formalism.UG.hform (starRingEnd I.E) I.J z ((I.J⁻¹ * Tᴴ * I.J) *ᵥ y) = Formalism.UG.hform (starRingEnd I.E) I.J (T *ᵥ z) y`. Establish `hM : I.J * (I.J⁻¹ * Tᴴ * I.J) = Tᴴ * I.J`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, Matrix.one_mul]`. Rewrite using `[hform_eq, hform_eq, Matrix.mulVec_mulVec, hM, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]`. Rewrite using `[key]`.

Conclude with `(hdual y).1 hy _ (hT z hz)`.
-/
theorem adj_mem (I : AutInst) (x : I.GA) (T : Matrix (Fin I.n) (Fin I.n) I.E)
    (hT : ∀ y ∈ lamX I x, T *ᵥ y ∈ lamX I x) : ∀ y ∈ lamX I x, (I.J⁻¹ * Tᴴ * I.J) *ᵥ y ∈ lamX I x := by
  intro y hy
  obtain ⟨-, -, -, hdual, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I x
  rw [hdual]
  intro z hz
  have hJ : I.J * I.J⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr I.J_det)
  have key : Formalism.UG.hform (starRingEnd I.E) I.J z ((I.J⁻¹ * Tᴴ * I.J) *ᵥ y) =
      Formalism.UG.hform (starRingEnd I.E) I.J (T *ᵥ z) y := by
    have hM : I.J * (I.J⁻¹ * Tᴴ * I.J) = Tᴴ * I.J := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, Matrix.one_mul]
    rw [hform_eq, hform_eq, Matrix.mulVec_mulVec, hM, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.star_mulVec]
  rw [key]
  exact (hdual y).1 hy _ (hT z hz)

/- English proof (translation)
Use `set g : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)) := (xf : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) with hg`. Establish `hL : I.Lf = Formalism.UG.latS (F` using `I.F) (Af I.F) (IntAf I.F I.E) I.L := by`. Unfold `AutInst.Lf lamAf Formalism.UG.latS`. Rewrite using `[Set.image_eq_range]`. Both sides reduce to the same expression.

Establish `hfin : Module.Finite (𝓞 I.E) I.L` using `Module.Finite.iff_fg.mpr I.L_fg`. Establish `hrec` using `Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds I.F I.E (Fin I.n) I.L hfin I.L_span g`. Establish `hglob : Formalism.UG.CS.globLat g I.L = lamX I (1, xf)` using `(GlobalTheory.PointLattice.lamX_eq_globLat I (1, xf)).symm`. Rewrite `hrec` using `[hglob]`. Establish `hspan : ∀ w ∈ Submodule.span (IntAf I.F I.E) ((fun y : Fin I.n → I.E => fun i => Formalism.UG.inclE (F` using `I.F) (Af I.F) (y i)) '' (lamX I (1, xf) : Set (Fin I.n → I.E))), δ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *ᵥ w ∈ Submodule.span (IntAf I.F I.E) ((fun y : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) '' (lamX I (1, xf) : Set (Fin I.n → I.E))) := by`.

Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨y, hy, rfl⟩` from `hw`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨δ *ᵥ y, hδ y hy, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec _ _ _ _`. Consider the case `zero => simp`. Consider the case `add w₁ w₂ _ _ h₁ h₂`.

Rewrite using `[Matrix.mulVec_add]`. Conclude with `add_mem h₁ h₂`. Consider the case `smul s w _ h`. Rewrite using `[Matrix.mulVec_smul]`. Conclude with `Submodule.smul_mem _ s h`.

Establish `hu` using `(hrec ((g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ x)).2 (by`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, ← hL]`. Conclude with `hx)`. Establish `h2` using `(hrec _).1 (hspan _ hu)`. Rewrite `h2` using `[← hL]`.

Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Conclude with `h2`.
-/
private lemma inv_mul_map_inclE_of_mem_lf (I : AutInst) (xf : I.Gf) (δ : Matrix (Fin I.n) (Fin I.n) I.E)
    (hδ : ∀ y ∈ lamX I (1, xf), δ *ᵥ y ∈ lamX I (1, xf))
    (x : Fin I.n → (TensorProduct I.F I.E (Af I.F))) (hx : x ∈ I.Lf) :
    ((((xf : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)))⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * δ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * ((xf : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F)))) *ᵥ x ∈ I.Lf := by
  set g : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)) := (xf : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) with hg
  have hL : I.Lf = Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
    unfold AutInst.Lf lamAf Formalism.UG.latS
    rw [Set.image_eq_range]
    rfl
  have hfin : Module.Finite (𝓞 I.E) I.L := Module.Finite.iff_fg.mpr I.L_fg
  have hrec := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds I.F I.E (Fin I.n) I.L hfin I.L_span g
  have hglob : Formalism.UG.CS.globLat g I.L = lamX I (1, xf) := (GlobalTheory.PointLattice.lamX_eq_globLat I (1, xf)).symm
  rw [hglob] at hrec

  have hspan : ∀ w ∈ Submodule.span (IntAf I.F I.E) ((fun y : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ''
        (lamX I (1, xf) : Set (Fin I.n → I.E))),
      δ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *ᵥ w ∈ Submodule.span (IntAf I.F I.E) ((fun y : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ''
        (lamX I (1, xf) : Set (Fin I.n → I.E))) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      apply Submodule.subset_span
      refine ⟨δ *ᵥ y, hδ y hy, ?_⟩
      funext i
      exact RingHom.map_mulVec _ _ _ _
    | zero => simp
    | add w₁ w₂ _ _ h₁ h₂ =>
      rw [Matrix.mulVec_add]
      exact add_mem h₁ h₂
    | smul s w _ h =>
      rw [Matrix.mulVec_smul]
      exact Submodule.smul_mem _ s h
  have hu := (hrec ((g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ x)).2 (by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, ← hL]
    exact hx)
  have h2 := (hrec _).1 (hspan _ hu)
  rw [← hL] at h2
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact h2

/- English proof (translation)
Introduce `I xf`. Use `⟨fun T hT => adj_mem I (1, xf) T hT, ?_⟩` and prove the remaining obligations. Introduce `γ hγJ hγL`. Establish `hdet : γ.det ≠ 0`. Introduce `h0`.

Establish `h1` using `congrArg Matrix.det hγJ`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_mul, h0, mul_zero]`. Conclude with `I.J_det h1.symm`. Set `γu : GL (Fin I.n) I.E` to `Matrix.nonsingInvUnit γ (isUnit_iff_ne_zero.mpr hdet)`. Establish `hγu : (γu : Matrix (Fin I.n) (Fin I.n) I.E) = γ` using `rfl`.

Establish `hmemUJ : γu ∈ Formalism.UG.UJ (starRingEnd I.E) I.J` using `by show Formalism.UG.cT (starRingEnd I.E) (γu : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * γu = I.J`. Rewrite using `[cT_eq, hγu]`. Conclude with `hγJ`. Take `⟨a, ha1, ha2⟩` from `exists_point I γu hmemUJ`. Use `⟨a.1, ⟨a, ⟨γu, hmemUJ, ha1, ha2⟩, rfl, ?_⟩, ha1⟩` and prove the remaining obligations.

Establish `hδγ : (I.J⁻¹ * γᴴ * I.J) * γ = 1`. Rewrite using `[show (I.J⁻¹ * γᴴ * I.J) * γ = I.J⁻¹ * (γᴴ * I.J * γ) by simp only [Matrix.mul_assoc], hγJ, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr I.J_det)]`. Establish `hδγA : (I.J⁻¹ * γᴴ * I.J).map (Formalism.UG.inclE (F` using `I.F) (Af I.F)) * γ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) = 1 := by`. Rewrite using `[← Matrix.map_mul, hδγ]`. Simplify using the standard rewrite rules.

Establish `ha2' : ((a.2 : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) = γ.map (Formalism.UG.inclE (F` using `I.F) (Af I.F)) := by`. Rewrite using `[← hγu]`. Conclude with `ha2`. Use `set g : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)) := (xf : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) with hg`. Establish `hmat : (((xf⁻¹ * a.2 * xf : I.Gf) : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) = ((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * γ.map (Forma …` using `I.F) (Af I.F)) * (g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) := by`.

Simplify using `only [Subgroup.coe_mul, InvMemClass.coe_inv, Units.val_mul]`. Rewrite using `[ha2']`. Establish `hprod : (((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * (I.J⁻¹ * γᴴ * I.J).map (Formalism.UG.inclE (F` using `I.F) (Af I.F)) * (g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F)))) * (((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * γ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * (g : Matrix (Fin I.n) (F …`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = 1 := by rw [Units.mul_inv, Matrix.mul_one, hδγA, Matrix.mul_one, Units.inv_mul]`. Use `show ((xf⁻¹ * a.2 * xf : I.Gf) : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) ∈ Formalism.UG.stabGL I.Lf`. Unfold `Formalism.UG.stabGL`. Introduce `x`. Use `show x ∈ I.Lf ↔ (((xf⁻¹ * a.2 * xf : I.Gf) : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ x ∈ I.Lf`.

Rewrite using `[hmat]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `inv_mul_map_inclE_of_mem_lf I xf γ hγL x hx`. Introduce `hx`.

Establish `h1` using `inv_mul_map_inclE_of_mem_lf I xf (I.J⁻¹ * γᴴ * I.J) (adj_mem I (1, xf) γ hγL) _ hx`. Rewrite `h1` using `[Matrix.mulVec_mulVec, hprod, Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem adj_mem_and_exists_latGroup : ∀ (I : AutInst) (xf : I.Gf), (∀ T : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ lamX I (1, xf), T *ᵥ y ∈ lamX I (1, xf)) → ∀ y ∈ lamX I (1, xf), (I.J⁻¹ * Tᴴ * I.J) *ᵥ y ∈ lamX I (1, xf)) ∧ ∀ γ : Matrix (Fin I.n) (Fin I.n) I.E, γᴴ * I.J * γ = I.J → (∀ y ∈ lamX I (1, xf), γ *ᵥ y ∈ lamX I (1, xf)) → ∃ g ∈ latGroup I xf, ∀ v, uMat (g v) = (I.P v)⁻¹ * γ.map (I.φ v) * I.P v := by
  intro I xf
  refine ⟨fun T hT => adj_mem I (1, xf) T hT, ?_⟩
  intro γ hγJ hγL
  have hdet : γ.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hγJ
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
    exact I.J_det h1.symm
  let γu : GL (Fin I.n) I.E := Matrix.nonsingInvUnit γ (isUnit_iff_ne_zero.mpr hdet)
  have hγu : (γu : Matrix (Fin I.n) (Fin I.n) I.E) = γ := rfl
  have hmemUJ : γu ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := by
    show Formalism.UG.cT (starRingEnd I.E) (γu : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * γu = I.J
    rw [cT_eq, hγu]
    exact hγJ
  obtain ⟨a, ha1, ha2⟩ := exists_point I γu hmemUJ
  refine ⟨a.1, ⟨a, ⟨γu, hmemUJ, ha1, ha2⟩, rfl, ?_⟩, ha1⟩
  have hδγ : (I.J⁻¹ * γᴴ * I.J) * γ = 1 := by
    rw [show (I.J⁻¹ * γᴴ * I.J) * γ = I.J⁻¹ * (γᴴ * I.J * γ) by simp only [Matrix.mul_assoc], hγJ,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr I.J_det)]
  have hδγA : (I.J⁻¹ * γᴴ * I.J).map (Formalism.UG.inclE (F := I.F) (Af I.F)) * γ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) = 1 := by
    rw [← Matrix.map_mul, hδγ]
    simp
  have ha2' : ((a.2 : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) = γ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
    rw [← hγu]
    exact ha2
  set g : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)) := (xf : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) with hg
  have hmat : (((xf⁻¹ * a.2 * xf : I.Gf) : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) =
      ((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * γ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * (g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) := by
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, Units.val_mul]
    rw [ha2']
  have hprod : (((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * (I.J⁻¹ * γᴴ * I.J).map (Formalism.UG.inclE (F := I.F) (Af I.F)) * (g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F)))) *
      (((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * γ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * (g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F)))) = 1 := by
    calc _ = ((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * ((I.J⁻¹ * γᴴ * I.J).map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
            ((g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * ((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F)))) * γ.map (Formalism.UG.inclE (F := I.F) (Af I.F))) * (g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Units.mul_inv, Matrix.mul_one, hδγA, Matrix.mul_one, Units.inv_mul]
  show ((xf⁻¹ * a.2 * xf : I.Gf) : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) ∈ Formalism.UG.stabGL I.Lf
  unfold Formalism.UG.stabGL
  intro x
  show x ∈ I.Lf ↔ (((xf⁻¹ * a.2 * xf : I.Gf) : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ x ∈ I.Lf
  rw [hmat]
  constructor
  · intro hx
    exact inv_mul_map_inclE_of_mem_lf I xf γ hγL x hx
  · intro hx
    have h1 := inv_mul_map_inclE_of_mem_lf I xf (I.J⁻¹ * γᴴ * I.J) (adj_mem I (1, xf) γ hγL) _ hx
    rwa [Matrix.mulVec_mulVec, hprod, Matrix.one_mulVec] at h1

end GlobalTheory.RadCov.RatElt
