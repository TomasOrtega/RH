import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.AnaHpartUnique

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `n H E _ _ f F U g X hH hU hg hgH hF hfF hX`. Unfold `RdV`. Establish `hγ` using `hasDerivAt_mul_exp_smul_zero g X`. Establish `hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g`. Simplify using `[NormedSpace.exp_zero]`.

Establish `hFd : DifferentiableAt ℝ F g` using `(hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)`. Establish `hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0` using `hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm`. Establish `hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0] (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))`. Establish `hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U` using `hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)`. Use `filter_upwards [hmem] with t ht`.

Conclude with `hfF _ ht (ana_mul hgH (ana_expt hH hX t))`. Rewrite using `[hev.deriv_eq]`. Conclude with `hcomp.deriv`.
-/
theorem rd_extension_h : RdExtH := by
  intro n H E _ _ f F U g X hH hU hg hgH hF hfF hX
  unfold RdV
  have hγ := hasDerivAt_mul_exp_smul_zero g X
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
    filter_upwards [hmem] with t ht
    exact hfF _ ht (ana_mul hgH (ana_expt hH hX t))
  rw [hev.deriv_eq]
  exact hcomp.deriv

/- English proof (translation)
Unfold `SmoothLin`. Introduce `n H E _ _ f f' c hf hf'`. Unfold `SmoothOnH at *`. Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, hfF⟩` from `hf g₀ hg₀`.

Take `⟨U', F', hU', hgU', hF', hfF'⟩` from `hf' g₀ hg₀`. Use `⟨U ∩ U', fun x => F x + c • F' x, hU.inter hU', ⟨hgU, hgU'⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hF.mono Set.inter_subset_left).add ((hF'.mono Set.inter_subset_right).const_smul c)`. Introduce `g hg hgH`. Simplify using `only [hfF g hg.1 hgH, hfF' g hg.2 hgH]`.
-/
theorem smooth_linear' : SmoothLin := by
  unfold SmoothLin
  intro n H E _ _ f f' c hf hf'
  unfold SmoothOnH at *
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun x => F x + c • F' x, hU.inter hU', ⟨hgU, hgU'⟩, ?_, ?_⟩
  · exact (hF.mono Set.inter_subset_left).add ((hF'.mono Set.inter_subset_right).const_smul c)
  · intro g hg hgH
    simp only [hfF g hg.1 hgH, hfF' g hg.2 hgH]

/- English proof (translation)
Unfold `SmoothLocal`. Introduce `n H E _ _ f f' hff hf`. Unfold `SmoothOnH at *`. Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, hfF⟩` from `hf g₀ hg₀`.

Conclude with `⟨U, F, hU, hgU, hF, fun g hg hgH => (hff g hgH).symm.trans (hfF g hg hgH)⟩`.
-/
theorem smooth_local : SmoothLocal := by
  unfold SmoothLocal
  intro n H E _ _ f f' hff hf
  unfold SmoothOnH at *
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  exact ⟨U, F, hU, hgU, hF, fun g hg hgH => (hff g hgH).symm.trans (hfF g hg hgH)⟩

/- English proof (translation)
Unfold `SmoothRight`. Introduce `n H E _ _ f s hH hs hf`. Unfold `SmoothOnH at *`. Establish `hL : ContDiff ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => x * s)`. Establish `h` using `(LinearMap.mulRight ℝ s).toContinuousLinearMap.contDiff (n := ∞)`.

Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Use `first`. Consider the case `rfl`. Consider the case `simp`.

Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, hfF⟩` from `hf (g₀ * s) (ana_mul hg₀ hs)`. Use `⟨(fun x => x * s) ⁻¹' U, fun x => F (x * s), hU.preimage hL.continuous, hgU, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hF.comp hL.contDiffOn (fun x hx => hx)`. Introduce `g hg hgH`.

Conclude with `hfF (g * s) hg (ana_mul hgH hs)`.
-/
theorem smooth_right' : SmoothRight := by
  unfold SmoothRight
  intro n H E _ _ f s hH hs hf
  unfold SmoothOnH at *
  have hL : ContDiff ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => x * s) := by
    have h := (LinearMap.mulRight ℝ s).toContinuousLinearMap.contDiff (n := ∞)
    convert h using 1
    funext x
    first
    | rfl
    | simp
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (g₀ * s) (ana_mul hg₀ hs)
  refine ⟨(fun x => x * s) ⁻¹' U, fun x => F (x * s), hU.preimage hL.continuous, hgU, ?_, ?_⟩
  · exact hF.comp hL.contDiffOn (fun x hx => hx)
  · intro g hg hgH
    exact hfF (g * s) hg (ana_mul hgH hs)

section Rd

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, F, hU, hg₀U, hF, hfF⟩` from `hf g₀ hg₀`. Use `⟨U, fun k => fderiv ℝ F k (k * X), hU, hg₀U, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hF.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty`. Establish `h2 : ContDiffOn ℝ ∞ (fun k : Matrix (Fin n) (Fin n) ℂ => k * X) U` using `(mulRightRealCLM X).contDiff.contDiffOn`.

Conclude with `h1.clm_apply h2`. Introduce `k hk hkH`. Conclude with `rd_extension_h n H E f F U k X hH hU hk hkH hF hfF hX`.
-/
lemma ana_rdSmooth (hH : HInvol H) {f : Matrix (Fin n) (Fin n) ℂ → E} {X : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnH H f) (hX : inLH H X) : SmoothOnH H (RdV X f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun k => fderiv ℝ F k (k * X), hU, hg₀U, ?_, ?_⟩
  · have h1 := hF.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty
    have h2 : ContDiffOn ℝ ∞ (fun k : Matrix (Fin n) (Fin n) ℂ => k * X) U :=
      (mulRightRealCLM X).contDiff.contDiffOn
    exact h1.clm_apply h2
  · intro k hk hkH
    exact rd_extension_h n H E f F U k X hH hU hk hkH hF hfF hX

/- English proof (translation)
Take `⟨U, F, hU, hgU, hF, hfF⟩` from `hf g hg`. Take `⟨U', F', hU', hgU', hF', hfF'⟩` from `hf' g hg`. Establish `hd1 : DifferentiableAt ℝ F g` using `by first`. Consider the case `exact (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)`. Consider the case `exact (hF.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp)`.

Consider the case `exact (hF.differentiableOn le_top).differentiableAt (hU.mem_nhds hgU)`. Establish `hd2 : DifferentiableAt ℝ F' g` using `by first`. Consider the case `exact (hF'.differentiableOn (by simp)).differentiableAt (hU'.mem_nhds hgU')`. Consider the case `exact (hF'.contDiffAt (hU'.mem_nhds hgU')).differentiableAt (by simp)`. Consider the case `exact (hF'.differentiableOn le_top).differentiableAt (hU'.mem_nhds hgU')`.

Establish `e0` using `rd_extension_h n H E (fun x => f x + c • f' x) (fun x => F x + c • F' x) (U ∩ U') g X hH (hU.inter hU') ⟨hgU, hgU'⟩ hg ((hF.mono Set.inter_subset_left).add ((hF'.mono Set.inter_subset_right).const_smul c)) (fun h hh hhH => by simp only [hfF h hh.1 hhH, hfF' h hh.2 hhH]) hX`. Rewrite using `[e0, rd_extension_h n H E f F U g X hH hU hgU hg hF hfF hX, rd_extension_h n H E f' F' U' g X hH hU' hgU' hg hF' hfF' hX,`. Use the proof step `]`. Establish `hD : HasFDerivAt (fun x => F x + c • F' x) (fderiv ℝ F g + c • fderiv ℝ F' g) g` using `hd1.hasFDerivAt.add (hd2.hasFDerivAt.const_smul c)`. Rewrite using `[hD.fderiv]`.

Use `first`. Consider the case `rfl`. Consider the case `simp`.
-/
lemma ana_rdLin (hH : HInvol H) {f f' : Matrix (Fin n) (Fin n) ℂ → E} (c : ℂ)
    {X g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnH H f) (hf' : SmoothOnH H f') (hX : inLH H X)
    (hg : inUH H g) : RdV X (fun x => f x + c • f' x) g = RdV X f g + c • RdV X f' g := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g hg
  have hd1 : DifferentiableAt ℝ F g := by
    first
    | exact (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
    | exact (hF.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp)
    | exact (hF.differentiableOn le_top).differentiableAt (hU.mem_nhds hgU)
  have hd2 : DifferentiableAt ℝ F' g := by
    first
    | exact (hF'.differentiableOn (by simp)).differentiableAt (hU'.mem_nhds hgU')
    | exact (hF'.contDiffAt (hU'.mem_nhds hgU')).differentiableAt (by simp)
    | exact (hF'.differentiableOn le_top).differentiableAt (hU'.mem_nhds hgU')
  have e0 := rd_extension_h n H E (fun x => f x + c • f' x) (fun x => F x + c • F' x) (U ∩ U') g X hH
    (hU.inter hU') ⟨hgU, hgU'⟩ hg
    ((hF.mono Set.inter_subset_left).add ((hF'.mono Set.inter_subset_right).const_smul c))
    (fun h hh hhH => by simp only [hfF h hh.1 hhH, hfF' h hh.2 hhH]) hX
  rw [e0, rd_extension_h n H E f F U g X hH hU hgU hg hF hfF hX,
    rd_extension_h n H E f' F' U' g X hH hU' hgU' hg hF' hfF' hX,
]
  have hD : HasFDerivAt (fun x => F x + c • F' x) (fderiv ℝ F g + c • fderiv ℝ F' g) g :=
    hd1.hasFDerivAt.add (hd2.hasFDerivAt.const_smul c)
  rw [hD.fderiv]
  first
  | rfl
  | simp

/- English proof (translation)
Take `⟨U, F, hU, hgU, hF, hfF⟩` from `hf g hg`. Rewrite using `[rd_extension_h n H E f F U g (A + B) hH hU hgU hg hF hfF (ana_add hA hB), rd_extension_h n H E f F U g (A) hH hU hgU hg hF hfF (hA), rd_extension_h n H E f F U g (B) hH hU hgU hg hF hfF (hB), Matrix.mul_add, map_add]`.
-/
lemma ana_rdAdd (hH : HInvol H) {f : Matrix (Fin n) (Fin n) ℂ → E} {A B g : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnH H f) (hA : inLH H A) (hB : inLH H B) (hg : inUH H g) :
    RdV (A + B) f g = RdV A f g + RdV B f g := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  rw [rd_extension_h n H E f F U g (A + B) hH hU hgU hg hF hfF (ana_add hA hB), rd_extension_h n H E f F U g (A) hH hU hgU hg hF hfF (hA), rd_extension_h n H E f F U g (B) hH hU hgU hg hF hfF (hB), Matrix.mul_add, map_add]

/- English proof (translation)
Take `⟨U, F, hU, hgU, hF, hfF⟩` from `hf g hg`. Rewrite using `[rd_extension_h n H E f F U g (A - B) hH hU hgU hg hF hfF (ana_sub hA hB), rd_extension_h n H E f F U g (A) hH hU hgU hg hF hfF (hA), rd_extension_h n H E f F U g (B) hH hU hgU hg hF hfF (hB), Matrix.mul_sub, map_sub]`.
-/
lemma ana_rdSub (hH : HInvol H) {f : Matrix (Fin n) (Fin n) ℂ → E} {A B g : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnH H f) (hA : inLH H A) (hB : inLH H B) (hg : inUH H g) :
    RdV (A - B) f g = RdV A f g - RdV B f g := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  rw [rd_extension_h n H E f F U g (A - B) hH hU hgU hg hF hfF (ana_sub hA hB), rd_extension_h n H E f F U g (A) hH hU hgU hg hF hfF (hA), rd_extension_h n H E f F U g (B) hH hU hgU hg hF hfF (hB), Matrix.mul_sub, map_sub]

/- English proof (translation)
Unfold `RdV`. Use `congr 1`. Use function extensionality and compare the values at `t`. Conclude with `hff _ (ana_mul hg (ana_expt hH hX t))`.
-/
lemma ana_rdLocal (hH : HInvol H) {f f' : Matrix (Fin n) (Fin n) ℂ → E} {X g : Matrix (Fin n) (Fin n) ℂ}
    (hff : ∀ x, inUH H x → f x = f' x) (hX : inLH H X) (hg : inUH H g) : RdV X f g = RdV X f' g := by
  unfold RdV
  congr 1
  funext t
  exact hff _ (ana_mul hg (ana_expt hH hX t))

end Rd

/- English proof (translation)
Unfold `EabHLocal`. Introduce `n H E _ _ f f' a b g hH hff hg`. Unfold `EabH`. Rewrite using `[ana_rdLocal hH hff (ana_hpartMem hH _).1 hg, ana_rdLocal hH hff (ana_hpartMem hH _).2.1 hg]`.
-/
theorem eab_h_local : EabHLocal := by
  unfold EabHLocal
  intro n H E _ _ f f' a b g hH hff hg
  unfold EabH
  rw [ana_rdLocal hH hff (ana_hpartMem hH _).1 hg, ana_rdLocal hH hff (ana_hpartMem hH _).2.1 hg]

/- English proof (translation)
Unfold `EabHSmooth`. Introduce `n H E _ _ f a b hH hf`. Unfold `EabH`. Conclude with `smooth_linear' n H E _ _ Complex.I (ana_rdSmooth hH hf (ana_hpartMem hH _).1) (ana_rdSmooth hH hf (ana_hpartMem hH _).2.1)`.
-/
theorem eab_h_smooth : EabHSmooth := by
  unfold EabHSmooth
  intro n H E _ _ f a b hH hf
  unfold EabH
  exact smooth_linear' n H E _ _ Complex.I (ana_rdSmooth hH hf (ana_hpartMem hH _).1)
    (ana_rdSmooth hH hf (ana_hpartMem hH _).2.1)

/- English proof (translation)
Unfold `EabHLin`. Introduce `n H E _ _ f f' c a b g hH hf hf' hg`. Unfold `EabH`. Rewrite using `[ana_rdLin hH c hf hf' (ana_hpartMem hH _).1 hg, ana_rdLin hH c hf hf' (ana_hpartMem hH _).2.1 hg]`. Rewrite using `[smul_add, smul_add, smul_comm Complex.I c]`.

Normalize the expressions using the abelian group laws.
-/
theorem eab_h_linear : EabHLin := by
  unfold EabHLin
  intro n H E _ _ f f' c a b g hH hf hf' hg
  unfold EabH
  rw [ana_rdLin hH c hf hf' (ana_hpartMem hH _).1 hg, ana_rdLin hH c hf hf' (ana_hpartMem hH _).2.1 hg]
  rw [smul_add, smul_add, smul_comm Complex.I c]
  abel

end AAInvW
