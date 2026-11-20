import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoFibInv

noncomputable section

namespace PI.VolStabSW.TopoMuInv

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [SecondCountableTopology R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem smul_apply (h : HA R σ J) {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) (x : Fin n) :
    (h • X) x = ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ X x := rfl

/- English proof (translation)
Establish `hg : Formalism.UG.cT (sigR R σ) ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J` using `h.2`. Establish `key : ∀ u v : Fin M → R ⊗[F] E, hR R σ J u v = (fun i => sigR R σ (u i)) ⬝ᵥ (JR R J *ᵥ v)`. Introduce `u v`. Simplify using `only [hR, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]`. Rewrite using `[key, key]`.

Establish `e1 : (fun i => sigR R σ ((((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x) i)) = (((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map (sigR R σ)) *ᵥ (fun i => sigR R σ (x i))`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec _ _ _ i`. Rewrite using `[e1, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`. Use `show _ ⬝ᵥ ((Formalism.UG.cT (sigR R σ) ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E))) *ᵥ y) = _`.

Rewrite using `[hg]`.
-/
private theorem hR_mat_mulVec_mulVec (h : HA R σ J) (x y : Fin M → R ⊗[F] E) :
    hR R σ J (((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x) (((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y) = hR R σ J x y := by
  have hg : Formalism.UG.cT (sigR R σ) ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J := h.2
  have key : ∀ u v : Fin M → R ⊗[F] E, hR R σ J u v = (fun i => sigR R σ (u i)) ⬝ᵥ (JR R J *ᵥ v) := by
    intro u v
    simp only [hR, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [key, key]
  have e1 : (fun i => sigR R σ ((((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x) i)) =
      (((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map (sigR R σ)) *ᵥ (fun i => sigR R σ (x i)) := by
    funext i; exact RingHom.map_mulVec _ _ _ i
  rw [e1, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  show _ ⬝ᵥ ((Formalism.UG.cT (sigR R σ) ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E))) *ᵥ y) = _
  rw [hg]

/- English proof (translation)
Unfold `BR`. Simplify using `only [smul_apply, hR_mat_mulVec_mulVec]`.
-/
theorem BR_smul (h : HA R σ J) {n : ℕ} (X Y : Fin n → Fin M → R ⊗[F] E) :
    BR R σ J (h • X) (h • Y) = BR R σ J X Y := by

  unfold BR
  simp only [smul_apply, hR_mat_mulVec_mulVec]

/- English proof (translation)
Use `conv_lhs => rw [← smul_inv_smul h Y]`. Conclude with `BR_smul R σ J h X (h⁻¹ • Y)`.
-/
theorem BR_smul_left (h : HA R σ J) {n : ℕ} (X Y : Fin n → Fin M → R ⊗[F] E) :
    BR R σ J (h • X) Y = BR R σ J X (h⁻¹ • Y) := by

  conv_lhs => rw [← smul_inv_smul h Y]
  exact BR_smul R σ J h X (h⁻¹ • Y)

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [smul_apply, Pi.neg_apply, Matrix.mulVec_neg]`.
-/
theorem smul_neg' (h : HA R σ J) {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    h • (-X) = -(h • X) := by

  funext x
  simp only [smul_apply, Pi.neg_apply, Matrix.mulVec_neg]

def smulAddEquiv (h : HA R σ J) (n : ℕ) :
    (Fin n → Fin M → R ⊗[F] E) ≃+ (Fin n → Fin M → R ⊗[F] E) where
  toEquiv := MulAction.toPerm h
  map_add' X Y := by
    funext x
    change ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ (X x + Y x) = _
    rw [mulVec_add]
    rfl

/- English proof (translation)
Set `e` to `PI.VolStabSW.smulHomeo R σ (a := n) J h`. Set `em` to `e.toMeasurableEquiv`. Establish `hmap : μ.map (fun X => h • X) = μ.map em` using `rfl`. Establish `: μ.IsAddHaarMeasure` using `hμ.1`. Use `⟨?_, fun Φ hc hcs hI z => ?_⟩` and prove the remaining obligations.

Conclude with `(smulAddEquiv R σ J h n).isAddHaarMeasure_map μ e.continuous e.symm.continuous`. Rewrite `hI`, the goal using `[hmap]`. Set `Fh : (Fin n → Fin M → R ⊗[F] E) → ℂ` to `fun w => ∫ x, Φ (h • x) * ψR (BR R σ J x w) ∂μ`. Establish `hin : ∀ y, ∫ x, Φ x * ψR (BR R σ J x y) ∂(μ.map em) = Fh (h⁻¹ • y)` using `fun y => by`. Rewrite using `[integral_map_equiv]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Use `show Φ (h • x) * ψR (BR R σ J (h • x) y) = Φ (h • x) * ψR (BR R σ J x (h⁻¹ • y))`. Rewrite using `[BR_smul_left]`. Establish `hI' : Integrable Fh μ`. Rewrite `hI` using `[integrable_map_equiv]`.

Use `hI.congr (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Use `show ∫ x, Φ x * ψR (BR R σ J x (h • y)) ∂(μ.map em) = Fh y`. Rewrite using `[hin, inv_smul_smul]`. Establish `key` using `hμ.2 (fun x => Φ (h • x)) (hc.comp e.continuous) (hcs.comp_homeomorph e) hI' (h⁻¹ • z)`. Rewrite using `[integral_map_equiv]`.

Establish `e3 : (fun y => (∫ x, Φ x * ψR (BR R σ J x (em y)) ∂(μ.map em)) * ψR (BR R σ J (em y) z)) = fun y => Fh y * ψR (BR R σ J y (h⁻¹ • z))`. Use function extensionality and compare the values at `y`. Use `show (∫ x, Φ x * ψR (BR R σ J x (h • y)) ∂(μ.map em)) * ψR (BR R σ J (h • y) z) = _`. Rewrite using `[hin, inv_smul_smul, BR_smul_left]`. Rewrite using `[e3]`.

Use `key.trans ?_` and prove the remaining obligations. Use `show Φ (h • -(h⁻¹ • z)) = Φ (-z)`. Rewrite using `[smul_neg', smul_inv_smul]`.
-/
theorem selfDual_map (ψR : R → ℂ) {n : ℕ} (μ : Measure (Fin n → Fin M → R ⊗[F] E))
    (hμ : SdW F E σ M J R ψR n μ) (h : HA R σ J) :
    SdW F E σ M J R ψR n (μ.map (fun X => h • X)) := by
  let e := PI.VolStabSW.smulHomeo R σ (a := n) J h
  let em := e.toMeasurableEquiv
  have hmap : μ.map (fun X => h • X) = μ.map em := rfl
  have : μ.IsAddHaarMeasure := hμ.1
  refine ⟨?_, fun Φ hc hcs hI z => ?_⟩
  · exact (smulAddEquiv R σ J h n).isAddHaarMeasure_map μ e.continuous e.symm.continuous
  rw [hmap] at hI ⊢
  let Fh : (Fin n → Fin M → R ⊗[F] E) → ℂ := fun w =>
    ∫ x, Φ (h • x) * ψR (BR R σ J x w) ∂μ
  have hin : ∀ y, ∫ x, Φ x * ψR (BR R σ J x y) ∂(μ.map em) = Fh (h⁻¹ • y) := fun y => by
    rw [integral_map_equiv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Φ (h • x) * ψR (BR R σ J (h • x) y) = Φ (h • x) * ψR (BR R σ J x (h⁻¹ • y))
    rw [BR_smul_left]
  have hI' : Integrable Fh μ := by
    rw [integrable_map_equiv] at hI
    refine hI.congr (Filter.Eventually.of_forall fun y => ?_)
    show ∫ x, Φ x * ψR (BR R σ J x (h • y)) ∂(μ.map em) = Fh y
    rw [hin, inv_smul_smul]
  have key := hμ.2 (fun x => Φ (h • x)) (hc.comp e.continuous) (hcs.comp_homeomorph e) hI'
    (h⁻¹ • z)
  rw [integral_map_equiv]
  have e3 : (fun y => (∫ x, Φ x * ψR (BR R σ J x (em y)) ∂(μ.map em)) *
      ψR (BR R σ J (em y) z)) = fun y => Fh y * ψR (BR R σ J y (h⁻¹ • z)) := by
    funext y
    show (∫ x, Φ x * ψR (BR R σ J x (h • y)) ∂(μ.map em)) * ψR (BR R σ J (h • y) z) = _
    rw [hin, inv_smul_smul, BR_smul_left]
  rw [e3]
  refine key.trans ?_
  show Φ (h • -(h⁻¹ • z)) = Φ (-z)
  rw [smul_neg', smul_inv_smul]

end PI.VolStabSW.TopoMuInv

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμ h`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Conclude with `(hU F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ).1 _ _ (TopoMuInv.selfDual_map (Ainf F) σ J (psiInf F ψ) μinf hμ h) hμ`.
-/
theorem muInvInf_of (hU : SdUniq) : MuInvInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμ h
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact (hU F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ).1 _ _
    (TopoMuInv.selfDual_map (Ainf F) σ J (psiInf F ψ) μinf hμ h) hμ

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμ h`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Conclude with `((hU F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ).2.2 v).1 _ _ (TopoMuInv.selfDual_map (Fv F v) σ J (psiV F ψ v) μv hμ h) hμ`.
-/
theorem muInvV_of (hU : SdUniq) : MuInvV := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμ h
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact ((hU F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ).2.2 v).1 _ _
    (TopoMuInv.selfDual_map (Fv F v) σ J (psiV F ψ v) μv hμ h) hμ

/- English proof (translation)
The claim follows from `nuInv_of_steps hD hC hP (muInvInf_of hU) (muInvV_of hU)`.
-/
theorem nuInv_of_pin (hD : DetAdm) (hC : CompG) (hP : FibPin) (hU : SdUniq) : NuInv :=
  nuInv_of_steps hD hC hP (muInvInf_of hU) (muInvV_of hU)

end PI.VolStabSW
