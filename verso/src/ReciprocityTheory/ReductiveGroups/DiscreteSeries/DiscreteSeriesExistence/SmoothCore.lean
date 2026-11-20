import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.VectorComplexifiedDerivativeCommutator
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.LieOperatorConjHolds

noncomputable section

open Finset Matrix Filter Topology
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Alg

variable {ε : Fin n → Bool}

/- English proof (translation)
The claim follows from `Formalism.REAL.lie_algebra_add_mem_matrix hX hY`.
-/
theorem smc_inG_add {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y) : inG ε (X + Y) :=
  Formalism.REAL.lie_algebra_add_mem_matrix hX hY

/- English proof (translation)
Simplify using `using smd_inG_add_smul (inG_zero' ε) hX r`. Use `where inG_zero' (ε : Fin n → Bool) : inG ε (0 : Matrix (Fin n) (Fin n) ℂ) := by simp [inG]`.
-/
theorem smc_inG_rsmul {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (r : ℝ) : inG ε ((r : ℂ) • X) := by
  simpa using smd_inG_add_smul (inG_zero' ε) hX r
where inG_zero' (ε : Fin n → Bool) : inG ε (0 : Matrix (Fin n) (Fin n) ℂ) := by simp [inG]

/- English proof (translation)
The claim follows from `Formalism.REAL.complex_parts_mem_lie_algebra_holds n ε Z`.
-/
theorem smc_cpart (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (S7.cpart1 ε Z) ∧ inG ε (S7.cpart2 ε Z) ∧ Z = S7.cpart1 ε Z + Complex.I • S7.cpart2 ε Z ∧
      (inG ε Z → S7.cpart1 ε Z = Z ∧ S7.cpart2 ε Z = 0) :=
  Formalism.REAL.complex_parts_mem_lie_algebra_holds n ε Z

/- English proof (translation)
The claim follows from `Formalism.REAL.complex_parts_unique hP hQ`.
-/
theorem smc_cpart_unique {P Q : Matrix (Fin n) (Fin n) ℂ} (hP : inG ε P) (hQ : inG ε Q) :
    S7.cpart1 ε (P + Complex.I • Q) = P ∧ S7.cpart2 ε (P + Complex.I • Q) = Q :=
  Formalism.REAL.complex_parts_unique hP hQ

/- English proof (translation)
The claim follows from `Formalism.REAL.p0auxiliary_cpart1_add ε Z W`.
-/
theorem smc_cpart1_add (Z W : Matrix (Fin n) (Fin n) ℂ) :
    S7.cpart1 ε (Z + W) = S7.cpart1 ε Z + S7.cpart1 ε W := Formalism.REAL.p0auxiliary_cpart1_add ε Z W

/- English proof (translation)
The claim follows from `Formalism.REAL.p0auxiliary_cpart1_real ε x Z`.
-/
theorem smc_cpart1_real (x : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    S7.cpart1 ε ((x : ℂ) • Z) = (x : ℂ) • S7.cpart1 ε Z := Formalism.REAL.p0auxiliary_cpart1_real ε x Z

/- English proof (translation)
The claim follows from `Formalism.REAL.p0auxiliary_cpart1_I ε Z`.
-/
theorem smc_cpart1_I (Z : Matrix (Fin n) (Fin n) ℂ) :
    S7.cpart1 ε (Complex.I • Z) = -S7.cpart2 ε Z := Formalism.REAL.p0auxiliary_cpart1_I ε Z

end Alg

section Calc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Establish `hγ` using `Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X`. Establish `hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g`. Simplify using `[NormedSpace.exp_zero]`. Establish `hFd : DifferentiableAt ℝ F g` using `(hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)`. Establish `hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0` using `hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm`.

Use `hcomp.congr_of_eventuallyEq ?_` and prove the remaining obligations. Establish `hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U` using `hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)`. Use `filter_upwards [hmem] with t ht`. Conclude with `hfF _ ht (smd_inUJ_mul hgJ (exp_smul_mem_UJset hX t))`.
-/
theorem hasDerivAt_rdV_ext {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)}
    {g X : Matrix (Fin n) (Fin n) ℂ} (hU : IsOpen U) (hg : g ∈ U) (hgJ : inUJ ε g) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ h ∈ U, inUJ ε h → f h = F h) (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by
  have hγ := Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  refine hcomp.congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
  filter_upwards [hmem] with t ht
  exact hfF _ ht (smd_inUJ_mul hgJ (exp_smul_mem_UJset hX t))

/- English proof (translation)
The claim follows from `(hasDerivAt_rdV_ext hU hg hgJ hF hfF hX).deriv`.
-/
theorem rdV_eq_fderiv {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)}
    {g X : Matrix (Fin n) (Fin n) ℂ} (hU : IsOpen U) (hg : g ∈ U) (hgJ : inUJ ε g) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ h ∈ U, inUJ ε h → f h = F h) (hX : inG ε X) :
    S7.RdV X f g = fderiv ℝ F g (g * X) :=
  (hasDerivAt_rdV_ext hU hg hgJ hF hfF hX).deriv

/- English proof (translation)
Take `⟨U, F, hU, hgU, hF, hfF⟩` from `hf g hg`. Rewrite using `[rdV_eq_fderiv hU hgU hg hF hfF hX]`. Conclude with `hasDerivAt_rdV_ext hU hgU hg hF hfF hX`.
-/
theorem hasDerivAt_rdV {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (S7.RdV X f g) 0 := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  rw [rdV_eq_fderiv hU hgU hg hF hfF hX]
  exact hasDerivAt_rdV_ext hU hgU hg hF hfF hX

/- English proof (translation)
Unfold `S7.RdV`. Use `congr 1`. Use function extensionality and compare the values at `t`. Conclude with `h _ (smd_inUJ_mul hg (exp_smul_mem_UJset hX t))`.
-/
theorem rdV_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) : S7.RdV X f g = S7.RdV X f' g := by
  unfold S7.RdV
  congr 1
  funext t
  exact h _ (smd_inUJ_mul hg (exp_smul_mem_UJset hX t))

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, F, hU, h1, hF, hfF⟩` from `hf g₀ hg₀`. Take `⟨U', F', hU', h1', hF', hfF'⟩` from `hf' g₀ hg₀`. Use `⟨U ∩ U', fun g => F g + F' g, hU.inter hU', ⟨h1, h1'⟩, (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), fun g hg hJ => ?_⟩` and prove the remaining obligations. Use `show f g + f' g = F g + F' g`.

Rewrite using `[hfF g hg.1 hJ, hfF' g hg.2 hJ]`.
-/
theorem smoothOnGV_add {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f)
    (hf' : S7.SmoothOnGV ε f') : S7.SmoothOnGV ε (fun g => f g + f' g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, h1, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', h1', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun g => F g + F' g, hU.inter hU', ⟨h1, h1'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), fun g hg hJ => ?_⟩
  show f g + f' g = F g + F' g
  rw [hfF g hg.1 hJ, hfF' g hg.2 hJ]

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, F, hU, h1, hF, hfF⟩` from `hf g₀ hg₀`. Use `⟨U, fun g => c • F g, hU, h1, hF.const_smul c, fun g hg hJ => ?_⟩` and prove the remaining obligations. Use `show c • f g = c • F g`. Rewrite using `[hfF g hg hJ]`.
-/
theorem smoothOnGV_smul (c : ℂ) {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f) :
    S7.SmoothOnGV ε (fun g => c • f g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, h1, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun g => c • F g, hU, h1, hF.const_smul c, fun g hg hJ => ?_⟩
  show c • f g = c • F g
  rw [hfF g hg hJ]

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, F, hU, hg₀U, hF, hfF⟩` from `hf g₀ hg₀`. Use `⟨U, fun k => fderiv ℝ F k (k * X), hU, hg₀U, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hF.fderiv_of_isOpen (m := ∞) hU Formalism.REAL.withTop_enat_infty_add_one_le_infty`. Establish `h2 : ContDiffOn ℝ ∞ (fun k : Matrix (Fin n) (Fin n) ℂ => k * X) U` using `(Formalism.REAL.mulRightRealCLM X).contDiff.contDiffOn`.

Conclude with `h1.clm_apply h2`. Introduce `k hk hkJ`. Conclude with `rdV_eq_fderiv hU hk hkJ hF hfF hX`.
-/
theorem smoothOnGV_rdV {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) : S7.SmoothOnGV ε (S7.RdV X f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun k => fderiv ℝ F k (k * X), hU, hg₀U, ?_, ?_⟩
  · have h1 := hF.fderiv_of_isOpen (m := ∞) hU Formalism.REAL.withTop_enat_infty_add_one_le_infty
    have h2 : ContDiffOn ℝ ∞ (fun k : Matrix (Fin n) (Fin n) ℂ => k * X) U :=
      (Formalism.REAL.mulRightRealCLM X).contDiff.contDiffOn
    exact h1.clm_apply h2
  · intro k hk hkJ
    exact rdV_eq_fderiv hU hk hkJ hF hfF hX

/- English proof (translation)
The claim follows from `((hasDerivAt_rdV hf hg hX).add ((hasDerivAt_rdV hf' hg hX).const_smul c)).deriv`.
-/
theorem rdV_add_smul_fun {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f)
    (hf' : S7.SmoothOnGV ε f') (c : ℂ) {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) :
    S7.RdV X (fun h => f h + c • f' h) g = S7.RdV X f g + c • S7.RdV X f' g :=
  ((hasDerivAt_rdV hf hg hX).add ((hasDerivAt_rdV hf' hg hX).const_smul c)).deriv

/- English proof (translation)
The claim follows from `(((φ.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) (hasDerivAt_rdV hf hg hX)).deriv`.
-/
theorem rdV_clm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (φ : E →L[ℂ] E')
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f) {X g : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (hg : inUJ ε g) : S7.RdV X (fun x => φ (f x)) g = φ (S7.RdV X f g) :=
  (((φ.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) (hasDerivAt_rdV hf hg hX)).deriv

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, F, hU, hg₀U, hF, hfF⟩` from `hf g₀ hg₀`. Use `⟨U, fun x => φ (F x), hU, hg₀U, (φ.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩` and prove the remaining obligations. Introduce `k hk hkJ`. Use `show φ (f k) = φ (F k)`.

Rewrite using `[hfF k hk hkJ]`.
-/
theorem smoothOnGV_clm {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (φ : E →L[ℂ] E')
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f) : S7.SmoothOnGV ε (fun x => φ (f x)) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun x => φ (F x), hU, hg₀U, (φ.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩
  intro k hk hkJ
  show φ (f k) = φ (F k)
  rw [hfF k hk hkJ]

end Calc

section Orbit

variable {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem isSmoothVecU_iff {v : H} : IsSmoothVecU ε σ v ↔ S7.SmoothOnGV ε (fun g => σ g v) := Iff.rfl

/- English proof (translation)
Simplify using `only [dS, S7.RdV, Matrix.one_mul]`.
-/
theorem dS_eq_rdV (X : Matrix (Fin n) (Fin n) ℂ) (v : H) : dS σ X v = S7.RdV X (fun g => σ g v) 1 := by
  simp only [dS, S7.RdV, Matrix.one_mul]

/- English proof (translation)
Establish `h` using `hasDerivAt_dS hσ hX hv`. Establish `h2 : HasDerivAt (fun t : ℝ => σ g (σ (NormedSpace.exp ((t : ℂ) • X)) v)) (σ g (dS σ X v)) 0` using `((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h`. Establish `e : (fun t : ℝ => σ (g * NormedSpace.exp ((t : ℂ) • X)) v) = fun t : ℝ => σ g (σ (NormedSpace.exp ((t : ℂ) • X)) v)`. Use function extensionality and compare the values at `t`. Rewrite using `[hσ.1.2 g hg _ (exp_smul_mem_UJset hX t)]`.

Both sides reduce to the same expression. Use `show _ = deriv (fun t : ℝ => σ (g * NormedSpace.exp ((t : ℂ) • X)) v) 0`. Rewrite using `[e]`. Conclude with `h2.deriv.symm`.
-/
theorem orbit_dS (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {v : H}
    (hv : IsSmoothVecU ε σ v) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    σ g (dS σ X v) = S7.RdV X (fun h => σ h v) g := by
  have h := hasDerivAt_dS hσ hX hv
  have h2 : HasDerivAt (fun t : ℝ => σ g (σ (NormedSpace.exp ((t : ℂ) • X)) v)) (σ g (dS σ X v)) 0 :=
    ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have e : (fun t : ℝ => σ (g * NormedSpace.exp ((t : ℂ) • X)) v) =
      fun t : ℝ => σ g (σ (NormedSpace.exp ((t : ℂ) • X)) v) := by
    funext t
    rw [hσ.1.2 g hg _ (exp_smul_mem_UJset hX t)]
    rfl
  show _ = deriv (fun t : ℝ => σ (g * NormedSpace.exp ((t : ℂ) • X)) v) 0
  rw [e]
  exact h2.deriv.symm

/- English proof (translation)
Rewrite using `[map_add, map_smul, orbit_dS hσ (smc_cpart Z).1 hv hg, orbit_dS hσ (smc_cpart Z).2.1 hv hg]`. Both sides reduce to the same expression.
-/
theorem orbit_ecV (hσ : IsURepOn (UJset ε) σ) (Z : Matrix (Fin n) (Fin n) ℂ) {v : H}
    (hv : IsSmoothVecU ε σ v) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    σ g (dS σ (S7.cpart1 ε Z) v + Complex.I • dS σ (S7.cpart2 ε Z) v) = S7.EcV ε Z (fun h => σ h v) g := by
  rw [map_add, map_smul, orbit_dS hσ (smc_cpart Z).1 hv hg, orbit_dS hσ (smc_cpart Z).2.1 hv hg]
  rfl

end Orbit

end ReciprocityTheory.ChartRestriction.DS
