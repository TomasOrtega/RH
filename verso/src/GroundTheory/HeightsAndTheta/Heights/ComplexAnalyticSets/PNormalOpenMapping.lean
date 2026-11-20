import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLinearNoetherNormalization
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalLocallyIrreducible
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicIsolatedFibreOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalOpenMapping
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Metric Matrix

/- English proof (translation)
Unfold `GroundTheory.Heights₂.Heights.ComplexSets.pullback`. Express the relevant statement in the definitionally equal form `(aeval z : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) (aeval (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A) P) = _`. Rewrite using `[← AlgHom.comp_apply, MvPolynomial.comp_aeval]`. Establish `hlin : (fun i => (aeval z : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A i)) = A *ᵥ z`. Use function extensionality and compare the values at `i`.

Simplify using `[GroundTheory.Heights₂.Heights.ComplexSets.linPoly, Matrix.mulVec, dotProduct]`. Rewrite using `[hlin]`. Both sides reduce to the same expression.
-/
theorem eval_pullback_eq {n k : ℕ} (A : Matrix (Fin k) (Fin n) ℂ) (P : MvPolynomial (Fin k) ℂ)
    (z : Fin n → ℂ) : eval z (GroundTheory.Heights₂.Heights.ComplexSets.pullback A P) = eval (A *ᵥ z) P := by
  unfold GroundTheory.Heights₂.Heights.ComplexSets.pullback
  change (aeval z : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) (aeval (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A) P) = _
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have hlin : (fun i => (aeval z : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A i))
      = A *ᵥ z := by
    funext i
    simp [GroundTheory.Heights₂.Heights.ComplexSets.linPoly, Matrix.mulVec, dotProduct]
  rw [hlin]
  rfl

/- English proof (translation)
Use `by_contra! h`. Apply `hP` to reduce the goal to its premises. Establish `han : AnalyticOnNhd ℂ (fun y : Fin k → ℂ => eval y P) Set.univ` using `AnalyticOnNhd.eval_mvPolynomial P`. Establish `hz : (fun y : Fin k → ℂ => eval y P) =ᶠ[𝓝 a] 0` using `Filter.mem_of_superset hN (fun y hy => h y hy)`. Establish `h0` using `han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ a) hz`.

Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `y`. Simplify using `using h0 (Set.mem_univ y)`.
-/
theorem exists_eval_ne_zero_of_mem_nhds {k : ℕ} {P : MvPolynomial (Fin k) ℂ} (hP : P ≠ 0)
    {a : Fin k → ℂ} {N : Set (Fin k → ℂ)} (hN : N ∈ 𝓝 a) : ∃ y ∈ N, eval y P ≠ 0 := by
  by_contra! h
  apply hP
  have han : AnalyticOnNhd ℂ (fun y : Fin k → ℂ => eval y P) Set.univ :=
    AnalyticOnNhd.eval_mvPolynomial P
  have hz : (fun y : Fin k → ℂ => eval y P) =ᶠ[𝓝 a] 0 :=
    Filter.mem_of_superset hN (fun y hy => h y hy)
  have h0 := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ a) hz
  apply MvPolynomial.funext
  intro y
  simpa using h0 (Set.mem_univ y)

/- English proof (translation)
Take `⟨A, hA⟩` from `hLNN n k I hdim`. Take `⟨P, hP0, hPcov⟩` from `hDC n k I A hI hdim hA`. Use `set X := zeroSetIn I with hXdef`. Use `set Lc : (Fin n → ℂ) →L[ℂ] (Fin k → ℂ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin A) with hLcdef`. Establish `hLcA : ∀ z, Lc z = A *ᵥ z` using `fun z => rfl`.

Use `set w₀ := φ u₀ with hw₀`. Use `set a₀ := A *ᵥ w₀ with ha₀`. Use `set g : (Fin k → ℂ) → Fin k → ℂ := fun v => A *ᵥ φ v with hg`. Establish `hgd : DifferentiableOn ℂ g U` using `Lc.differentiable.comp_differentiableOn hφ`. Establish `hw₀X : w₀ ∈ X` using `hmaps hu₀`.

Establish `hfin : (GroundTheory.Heights₂.Heights.ComplexSets.fibre I A a₀).Finite` using `(hFB n k I A hI hdim hA a₀).2.1`. Use `set W₀ : Set (Fin n → ℂ) := ((GroundTheory.Heights₂.Heights.ComplexSets.fibre I A a₀) \ {w₀})ᶜ with hW₀`. Establish `hW₀o : IsOpen W₀` using `(hfin.subset Set.sdiff_subset).isClosed.isOpen_compl`. Establish `hw₀W₀ : w₀ ∈ W₀` using `fun h => h.2 rfl`. Establish `hφc : ContinuousAt φ u₀` using `(hφ.differentiableAt (hU.mem_nhds hu₀)).continuousAt`.

Take `⟨r, hr0, hrU⟩ : ∃ r > 0, closedBall u₀ r ⊆ U ∩ φ ⁻¹' W₀` from `Metric.nhds_basis_closedBall.mem_iff.1 (Filter.inter_mem (hU.mem_nhds hu₀) (hφc.preimage_mem_nhds (hW₀o.mem_nhds hw₀W₀)))`. Use `set K := closedBall u₀ r with hK`. Use `set V := ball u₀ r with hV`. Establish `hKU : K ⊆ U` using `fun v hv => (hrU hv).1`. Establish `hKc : IsCompact K` using `isCompact_closedBall u₀ r`.

Establish `hφK : ContinuousOn φ K` using `hφ.continuousOn.mono hKU`. Establish `hgK : ContinuousOn g K` using `Lc.continuous.comp_continuousOn hφK`. Establish `hVK : V ⊆ K` using `ball_subset_closedBall`. Establish `hiso : ∀ v ∈ K, g v = a₀ → v = u₀`. Introduce `v hv hgv`.

Establish `h1 : φ v ∈ GroundTheory.Heights₂.Heights.ComplexSets.fibre I A a₀` using `⟨hmaps (hKU hv), hgv⟩`. Establish `h3 : φ v = w₀`. Assume the negation of the conclusion as `hne`. Conclude with `(hrU hv).2 ⟨h1, hne⟩`. Conclude with `hinj (hKU hv) hu₀ h3`.

Establish `hSK : sphere u₀ r ⊆ K` using `sphere_subset_closedBall`. Establish `hgS : IsCompact (g '' sphere u₀ r)` using `(isCompact_sphere u₀ r).image_of_continuousOn (hgK.mono hSK)`. Establish `ha₀S : a₀ ∉ g '' sphere u₀ r`. Introduce and unpack `⟨v, hv, hgv⟩`. Establish `h` using `hiso v (hSK hv) hgv`.

Rewrite `hv` using `[h, mem_sphere, dist_self]`. Conclude with `hr0.ne hv`. Take `⟨ε, hε, hεS⟩ : ∃ ε > 0, ball a₀ ε ⊆ (g '' sphere u₀ r)ᶜ` from `Metric.isOpen_iff.1 hgS.isClosed.isOpen_compl a₀ ha₀S`. Establish `hcl : ∀ x, A *ᵥ x ∈ ball a₀ ε → x ∈ closure (φ '' V) → x ∈ φ '' V`. Introduce `x hxD hx`.

Establish `hKimg : IsCompact (φ '' K)` using `hKc.image_of_continuousOn hφK`. Take `⟨v, hvK, rfl⟩ : x ∈ φ '' K` from `hKimg.isClosed.closure_subset (closure_mono (Set.image_mono hVK) hx)`. Use `⟨v, ?_, rfl⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hvV`. Establish `hvS : v ∈ sphere u₀ r`.

Rewrite using `[mem_sphere]`. Rewrite `hvK` using `[mem_closedBall]`. Rewrite `hvV` using `[mem_ball, not_lt]`. Conclude with `le_antisymm hvK hvV`. Conclude with `hεS hxD ⟨v, hvS, rfl⟩`.

Use `set h := GroundTheory.Heights₂.Heights.ComplexSets.pullback A P with hh`. Establish `hevh : ∀ z, eval z h = eval (A *ᵥ z) P` using `fun z => eval_pullback_eq A P z`. Establish `hhI : h ∉ I`. Introduce `hmem`. Apply `hP0` to reduce the goal to its premises.

Apply `hA.injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use `show (Ideal.Quotient.mkₐ ℂ I) h = 0`. Rewrite using `[Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hmem`.

Establish `hND : (fun z => A *ᵥ z) ⁻¹' ball a₀ ε ∈ 𝓝 w₀` using `Lc.continuous.continuousAt.preimage_mem_nhds (ball_mem_nhds a₀ hε)`. Take `⟨B, hBo, hw₀B, hBD, hconn, hdense⟩` from `hNLI (Fin n) I h w₀ hI hic hhI hw₀X _ hND`. Use `set C := (X ∩ B) \ {z | eval z h = 0} with hC`. Establish `hop : ∀ v ∈ V, eval (g v) P ≠ 0 → ∃ W' : Set (Fin n → ℂ), IsOpen W' ∧ φ v ∈ W' ∧ X ∩ W' ⊆ φ '' V`. Introduce `v hv hPv`.

Establish `hvU : v ∈ U` using `hKU (hVK hv)`. Establish `hfib : φ v ∈ GroundTheory.Heights₂.Heights.ComplexSets.fibre I A (g v)` using `⟨hmaps hvU, rfl⟩`. Take `⟨-, -, hsec⟩` from `hPcov (g v) hPv`. Take `⟨O, W, s, hOo, hgvO, hWo, hvW, -, -, hsA, hXW⟩` from `hsec (φ v) hfib`. Establish `hφV : ContinuousOn φ V` using `hφK.mono hVK`.

Establish `hgV : ContinuousOn g V` using `hgK.mono hVK`. Use `set V1 := (V ∩ φ ⁻¹' W) ∩ (V ∩ g ⁻¹' O) with hV1`. Establish `hV1o : IsOpen V1` using `(hφV.isOpen_inter_preimage isOpen_ball hWo).inter (hgV.isOpen_inter_preimage isOpen_ball hOo)`. Establish `hv1 : v ∈ V1` using `⟨⟨hv, hvW⟩, ⟨hv, hgvO⟩⟩`. Establish `hrep : ∀ v' ∈ V1, φ v' = s (g v')`.

Introduce `v' hv'`. Establish `hmem : φ v' ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet I ∩ W` using `⟨hmaps (hKU (hVK hv'.1.1)), hv'.1.2⟩`. Rewrite `hmem` using `[hXW]`. Take `⟨o, ho, hso⟩` from `hmem`. Establish `hgo : g v' = o` using `by show A *ᵥ φ v' = o`.

Rewrite using `[← hso]`. Conclude with `hsA o ho`. Rewrite using `[hgo, hso]`. Establish `hginj : Set.InjOn g V1`. Introduce `v1 h1 v2 h2 he`.

Apply `hinj (hKU (hVK h1.1.1)) (hKU (hVK h2.1.1))` to reduce the goal to its premises. Rewrite using `[hrep v1 h1, hrep v2 h2, he]`. Establish `hgV1d : DifferentiableOn ℂ g V1` using `hgd.mono (fun x hx => hKU (hVK hx.1.1))`. Establish `himo : IsOpen (g '' V1)`. Rewrite using `[isOpen_iff_mem_nhds]`.

Introduce and unpack `_ ⟨v', hv', rfl⟩`. Conclude with `hIFO k V1 g v' hV1o hv' hgV1d ⟨V1, hV1o.mem_nhds hv', fun x _ hx he => hginj hx hv' he⟩ V1 (hV1o.mem_nhds hv')`. Use `⟨W ∩ (fun z => A *ᵥ z) ⁻¹' (g '' V1), hWo.inter (himo.preimage Lc.continuous), ⟨hvW, v, hv1, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `z ⟨hzX, hzW, v', hv', hv'z⟩`. Establish `hmem : z ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet I ∩ W` using `⟨hzX, hzW⟩`.

Rewrite `hmem` using `[hXW]`. Take `⟨o, ho, rfl⟩` from `hmem`. Establish `hgo : g v' = o` using `hv'z.trans (hsA o ho)`. Conclude with `⟨v', hv'.1.1, by rw [hrep v' hv', hgo]⟩`. Use `set Uo : Set (Fin n → ℂ) := ⋃₀ {W | IsOpen W ∧ X ∩ W ⊆ φ '' V} with hUo`.

Establish `hUoo : IsOpen Uo` using `isOpen_sUnion (fun W hW => hW.1)`. Establish `hUoX : X ∩ Uo ⊆ φ '' V`. Introduce and unpack `z ⟨hzX, W, hW, hzW⟩`. Conclude with `hW.2 ⟨hzX, hzW⟩`. Establish `hCX : ∀ z ∈ C, z ∈ X ∧ z ∈ B ∧ eval (A *ᵥ z) P ≠ 0` using `fun z hz => ⟨hz.1.1, hz.1.2, fun h0 => hz.2 ((hevh z).trans h0)⟩`.

Establish `hCin : ∀ z ∈ C, z ∈ φ '' V → z ∈ Uo`. Introduce and unpack `z hz ⟨v, hv, rfl⟩`. Take `⟨W', hW'o, hvW', hW'⟩` from `hop v hv (hCX _ hz).2.2`. Conclude with `⟨W', ⟨hW'o, hW'⟩, hvW'⟩`. Choose the witnesses or unpack the hypotheses as in `⟨z₁, hz₁C, hz₁V⟩ : ∃ z ∈ C, z ∈ φ '' V := by`.

Establish `hV2 : V ∩ φ ⁻¹' B ∈ 𝓝 u₀` using `Filter.inter_mem (ball_mem_nhds u₀ hr0) (hφc.preimage_mem_nhds (hBo.mem_nhds hw₀B))`. Establish `himg : g '' (V ∩ φ ⁻¹' B) ∈ 𝓝 a₀` using `hIFO k U g u₀ hU hu₀ hgd ⟨K, closedBall_mem_nhds u₀ hr0, fun v hv _ he => hiso v hv he⟩ _ hV2`. Take `⟨y, ⟨v, hv, rfl⟩, hy⟩` from `exists_eval_ne_zero_of_mem_nhds hP0 himg`. Conclude with `⟨φ v, ⟨⟨hmaps (hKU (hVK hv.1)), hv.2⟩, fun h0 => hy ((hevh _).symm.trans h0)⟩, v, hv.1, rfl⟩`. Establish `hCsub : C ⊆ Uo`.

Establish `hsplit : C ⊆ Uo ∪ (closure (φ '' V))ᶜ`. Introduce `z hz`. Distinguish the cases in `hzc : z ∈ closure (φ '' V)`. Conclude with `Or.inl (hCin z hz (hcl z (hBD (hCX z hz).2.1) hzc))`. Conclude with `Or.inr hzc`.

Assume the negation of the conclusion as `hns`. Take `⟨z, hzC, hzU⟩` from `Set.not_subset.1 hns`. Take `⟨z', hz'C, hz'U, hz'c⟩` from `hconn Uo (closure (φ '' V))ᶜ hUoo isClosed_closure.isOpen_compl hsplit ⟨z₁, hz₁C, hCin z₁ hz₁C hz₁V⟩ ⟨z, hzC, (hsplit hzC).resolve_left hzU⟩`. Conclude with `hz'c (subset_closure (hUoX ⟨(hCX z' hz'C).1, hz'U⟩))`. Use `⟨B, hBo, hw₀B, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Establish `hxcl : x ∈ closure (φ '' V)` using `closure_mono (fun z hz => hUoX ⟨(hCX z hz).1, hCsub hz⟩) (hdense hx)`. Take `⟨v, hv, hvx⟩` from `hcl x (hBD hx.2) hxcl`. Conclude with `⟨v, hKU (hVK hv), hvx⟩`.
-/
theorem normalOpenMapping_local_fin
    (hNLI : NormalLocallyIrreducible.Statement)
    (hLNN : GroundTheory.Heights₂.Heights.ComplexSets.LinearNoetherNormalization.Statement)
    (hFB : GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.Statement)
    (hDC : GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.Statement)
    (hIFO : HolomorphicIsolatedFibreOpen.Statement)
    {n k : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (U : Set (Fin k → ℂ)) (φ : (Fin k → ℂ) → Fin n → ℂ)
    (hI : I.IsPrime) (hic : IsIntegrallyClosed (MvPolynomial (Fin n) ℂ ⧸ I))
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) = (k : ℕ)) (hU : IsOpen U)
    (hφ : DifferentiableOn ℂ φ U) (hinj : Set.InjOn φ U) (hmaps : Set.MapsTo φ U (zeroSetIn I))
    (u₀ : Fin k → ℂ) (hu₀ : u₀ ∈ U) :
    ∃ B : Set (Fin n → ℂ), IsOpen B ∧ φ u₀ ∈ B ∧ zeroSetIn I ∩ B ⊆ φ '' U := by
  classical

  obtain ⟨A, hA⟩ := hLNN n k I hdim
  obtain ⟨P, hP0, hPcov⟩ := hDC n k I A hI hdim hA
  set X := zeroSetIn I with hXdef
  set Lc : (Fin n → ℂ) →L[ℂ] (Fin k → ℂ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin A) with hLcdef
  have hLcA : ∀ z, Lc z = A *ᵥ z := fun z => rfl
  set w₀ := φ u₀ with hw₀
  set a₀ := A *ᵥ w₀ with ha₀
  set g : (Fin k → ℂ) → Fin k → ℂ := fun v => A *ᵥ φ v with hg
  have hgd : DifferentiableOn ℂ g U := Lc.differentiable.comp_differentiableOn hφ
  have hw₀X : w₀ ∈ X := hmaps hu₀

  have hfin : (GroundTheory.Heights₂.Heights.ComplexSets.fibre I A a₀).Finite := (hFB n k I A hI hdim hA a₀).2.1
  set W₀ : Set (Fin n → ℂ) := ((GroundTheory.Heights₂.Heights.ComplexSets.fibre I A a₀) \ {w₀})ᶜ with hW₀
  have hW₀o : IsOpen W₀ := (hfin.subset Set.sdiff_subset).isClosed.isOpen_compl
  have hw₀W₀ : w₀ ∈ W₀ := fun h => h.2 rfl
  have hφc : ContinuousAt φ u₀ := (hφ.differentiableAt (hU.mem_nhds hu₀)).continuousAt

  obtain ⟨r, hr0, hrU⟩ : ∃ r > 0, closedBall u₀ r ⊆ U ∩ φ ⁻¹' W₀ :=
    Metric.nhds_basis_closedBall.mem_iff.1
      (Filter.inter_mem (hU.mem_nhds hu₀) (hφc.preimage_mem_nhds (hW₀o.mem_nhds hw₀W₀)))
  set K := closedBall u₀ r with hK
  set V := ball u₀ r with hV
  have hKU : K ⊆ U := fun v hv => (hrU hv).1
  have hKc : IsCompact K := isCompact_closedBall u₀ r
  have hφK : ContinuousOn φ K := hφ.continuousOn.mono hKU
  have hgK : ContinuousOn g K := Lc.continuous.comp_continuousOn hφK
  have hVK : V ⊆ K := ball_subset_closedBall
  have hiso : ∀ v ∈ K, g v = a₀ → v = u₀ := by
    intro v hv hgv
    have h1 : φ v ∈ GroundTheory.Heights₂.Heights.ComplexSets.fibre I A a₀ := ⟨hmaps (hKU hv), hgv⟩
    have h3 : φ v = w₀ := by
      by_contra hne
      exact (hrU hv).2 ⟨h1, hne⟩
    exact hinj (hKU hv) hu₀ h3

  have hSK : sphere u₀ r ⊆ K := sphere_subset_closedBall
  have hgS : IsCompact (g '' sphere u₀ r) := (isCompact_sphere u₀ r).image_of_continuousOn (hgK.mono hSK)
  have ha₀S : a₀ ∉ g '' sphere u₀ r := by
    rintro ⟨v, hv, hgv⟩
    have h := hiso v (hSK hv) hgv
    rw [h, mem_sphere, dist_self] at hv
    exact hr0.ne hv
  obtain ⟨ε, hε, hεS⟩ : ∃ ε > 0, ball a₀ ε ⊆ (g '' sphere u₀ r)ᶜ :=
    Metric.isOpen_iff.1 hgS.isClosed.isOpen_compl a₀ ha₀S

  have hcl : ∀ x, A *ᵥ x ∈ ball a₀ ε → x ∈ closure (φ '' V) → x ∈ φ '' V := by
    intro x hxD hx
    have hKimg : IsCompact (φ '' K) := hKc.image_of_continuousOn hφK
    obtain ⟨v, hvK, rfl⟩ : x ∈ φ '' K :=
      hKimg.isClosed.closure_subset (closure_mono (Set.image_mono hVK) hx)
    refine ⟨v, ?_, rfl⟩
    by_contra hvV
    have hvS : v ∈ sphere u₀ r := by
      rw [mem_sphere]
      rw [mem_closedBall] at hvK
      rw [mem_ball, not_lt] at hvV
      exact le_antisymm hvK hvV
    exact hεS hxD ⟨v, hvS, rfl⟩

  set h := GroundTheory.Heights₂.Heights.ComplexSets.pullback A P with hh
  have hevh : ∀ z, eval z h = eval (A *ᵥ z) P := fun z => eval_pullback_eq A P z
  have hhI : h ∉ I := by
    intro hmem
    apply hP0
    apply hA.injective
    rw [map_zero]
    show (Ideal.Quotient.mkₐ ℂ I) h = 0
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  have hND : (fun z => A *ᵥ z) ⁻¹' ball a₀ ε ∈ 𝓝 w₀ :=
    Lc.continuous.continuousAt.preimage_mem_nhds (ball_mem_nhds a₀ hε)
  obtain ⟨B, hBo, hw₀B, hBD, hconn, hdense⟩ := hNLI (Fin n) I h w₀ hI hic hhI hw₀X _ hND
  set C := (X ∩ B) \ {z | eval z h = 0} with hC

  have hop : ∀ v ∈ V, eval (g v) P ≠ 0 →
      ∃ W' : Set (Fin n → ℂ), IsOpen W' ∧ φ v ∈ W' ∧ X ∩ W' ⊆ φ '' V := by
    intro v hv hPv
    have hvU : v ∈ U := hKU (hVK hv)
    have hfib : φ v ∈ GroundTheory.Heights₂.Heights.ComplexSets.fibre I A (g v) := ⟨hmaps hvU, rfl⟩
    obtain ⟨-, -, hsec⟩ := hPcov (g v) hPv
    obtain ⟨O, W, s, hOo, hgvO, hWo, hvW, -, -, hsA, hXW⟩ := hsec (φ v) hfib
    have hφV : ContinuousOn φ V := hφK.mono hVK
    have hgV : ContinuousOn g V := hgK.mono hVK
    set V1 := (V ∩ φ ⁻¹' W) ∩ (V ∩ g ⁻¹' O) with hV1
    have hV1o : IsOpen V1 :=
      (hφV.isOpen_inter_preimage isOpen_ball hWo).inter (hgV.isOpen_inter_preimage isOpen_ball hOo)
    have hv1 : v ∈ V1 := ⟨⟨hv, hvW⟩, ⟨hv, hgvO⟩⟩
    have hrep : ∀ v' ∈ V1, φ v' = s (g v') := by
      intro v' hv'
      have hmem : φ v' ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet I ∩ W :=
        ⟨hmaps (hKU (hVK hv'.1.1)), hv'.1.2⟩
      rw [hXW] at hmem
      obtain ⟨o, ho, hso⟩ := hmem
      have hgo : g v' = o := by
        show A *ᵥ φ v' = o
        rw [← hso]
        exact hsA o ho
      rw [hgo, hso]
    have hginj : Set.InjOn g V1 := by
      intro v1 h1 v2 h2 he
      apply hinj (hKU (hVK h1.1.1)) (hKU (hVK h2.1.1))
      rw [hrep v1 h1, hrep v2 h2, he]
    have hgV1d : DifferentiableOn ℂ g V1 := hgd.mono (fun x hx => hKU (hVK hx.1.1))
    have himo : IsOpen (g '' V1) := by
      rw [isOpen_iff_mem_nhds]
      rintro _ ⟨v', hv', rfl⟩
      exact hIFO k V1 g v' hV1o hv' hgV1d
        ⟨V1, hV1o.mem_nhds hv', fun x _ hx he => hginj hx hv' he⟩ V1 (hV1o.mem_nhds hv')
    refine ⟨W ∩ (fun z => A *ᵥ z) ⁻¹' (g '' V1), hWo.inter (himo.preimage Lc.continuous),
      ⟨hvW, v, hv1, rfl⟩, ?_⟩
    rintro z ⟨hzX, hzW, v', hv', hv'z⟩
    have hmem : z ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet I ∩ W := ⟨hzX, hzW⟩
    rw [hXW] at hmem
    obtain ⟨o, ho, rfl⟩ := hmem
    have hgo : g v' = o := hv'z.trans (hsA o ho)
    exact ⟨v', hv'.1.1, by rw [hrep v' hv', hgo]⟩

  set Uo : Set (Fin n → ℂ) := ⋃₀ {W | IsOpen W ∧ X ∩ W ⊆ φ '' V} with hUo
  have hUoo : IsOpen Uo := isOpen_sUnion (fun W hW => hW.1)
  have hUoX : X ∩ Uo ⊆ φ '' V := by
    rintro z ⟨hzX, W, hW, hzW⟩
    exact hW.2 ⟨hzX, hzW⟩
  have hCX : ∀ z ∈ C, z ∈ X ∧ z ∈ B ∧ eval (A *ᵥ z) P ≠ 0 :=
    fun z hz => ⟨hz.1.1, hz.1.2, fun h0 => hz.2 ((hevh z).trans h0)⟩
  have hCin : ∀ z ∈ C, z ∈ φ '' V → z ∈ Uo := by
    rintro z hz ⟨v, hv, rfl⟩
    obtain ⟨W', hW'o, hvW', hW'⟩ := hop v hv (hCX _ hz).2.2
    exact ⟨W', ⟨hW'o, hW'⟩, hvW'⟩

  obtain ⟨z₁, hz₁C, hz₁V⟩ : ∃ z ∈ C, z ∈ φ '' V := by
    have hV2 : V ∩ φ ⁻¹' B ∈ 𝓝 u₀ :=
      Filter.inter_mem (ball_mem_nhds u₀ hr0) (hφc.preimage_mem_nhds (hBo.mem_nhds hw₀B))
    have himg : g '' (V ∩ φ ⁻¹' B) ∈ 𝓝 a₀ :=
      hIFO k U g u₀ hU hu₀ hgd ⟨K, closedBall_mem_nhds u₀ hr0, fun v hv _ he => hiso v hv he⟩ _ hV2
    obtain ⟨y, ⟨v, hv, rfl⟩, hy⟩ := exists_eval_ne_zero_of_mem_nhds hP0 himg
    exact ⟨φ v, ⟨⟨hmaps (hKU (hVK hv.1)), hv.2⟩, fun h0 => hy ((hevh _).symm.trans h0)⟩, v, hv.1, rfl⟩

  have hCsub : C ⊆ Uo := by
    have hsplit : C ⊆ Uo ∪ (closure (φ '' V))ᶜ := by
      intro z hz
      by_cases hzc : z ∈ closure (φ '' V)
      · exact Or.inl (hCin z hz (hcl z (hBD (hCX z hz).2.1) hzc))
      · exact Or.inr hzc
    by_contra hns
    obtain ⟨z, hzC, hzU⟩ := Set.not_subset.1 hns
    obtain ⟨z', hz'C, hz'U, hz'c⟩ := hconn Uo (closure (φ '' V))ᶜ hUoo isClosed_closure.isOpen_compl hsplit
      ⟨z₁, hz₁C, hCin z₁ hz₁C hz₁V⟩ ⟨z, hzC, (hsplit hzC).resolve_left hzU⟩
    exact hz'c (subset_closure (hUoX ⟨(hCX z' hz'C).1, hz'U⟩))

  refine ⟨B, hBo, hw₀B, ?_⟩
  intro x hx
  have hxcl : x ∈ closure (φ '' V) :=
    closure_mono (fun z hz => hUoX ⟨(hCX z hz).1, hCsub hz⟩) (hdense hx)
  obtain ⟨v, hv, hvx⟩ := hcl x (hBD hx.2) hxcl
  exact ⟨v, hKU (hVK hv), hvx⟩

/- English proof (translation)
Introduce `σ _ I k U φ hI hic hdim hU hφ hinj hmaps`. Use `set n := Fintype.card σ`. Set `e : σ ≃ Fin n` to `Fintype.equivFin σ`. Set `R : MvPolynomial σ ℂ ≃+* MvPolynomial (Fin n) ℂ` to `(MvPolynomial.renameEquiv ℂ e).toRingEquiv`. Set `I' : Ideal (MvPolynomial (Fin n) ℂ)` to `I.map (R : MvPolynomial σ ℂ →+* MvPolynomial (Fin n) ℂ)`.

Establish `hI' : I'.IsPrime`. Use `hI` as an intermediate fact. Conclude with `Ideal.map_isPrime_of_equiv R`. Set `Q : (MvPolynomial σ ℂ ⧸ I) ≃+* (MvPolynomial (Fin n) ℂ ⧸ I')` to `Ideal.quotientEquiv I I' R rfl`. Establish `hic' : IsIntegrallyClosed (MvPolynomial (Fin n) ℂ ⧸ I')`.

Use `hic` as an intermediate fact. Conclude with `IsIntegrallyClosed.of_equiv Q`. Establish `hdim' : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I') = (k : ℕ)`. Rewrite using `[← ringKrullDim_eq_of_ringEquiv Q, hdim]`. Establish `hR : ∀ p : MvPolynomial σ ℂ, R p = rename e p` using `fun p => rfl`.

Establish `hmem : ∀ x : Fin n → ℂ, x ∈ zeroSetIn I' ↔ x ∘ e ∈ zeroSetIn I`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx q hq`. Establish `h1` using `hx (R q) (Ideal.mem_map_of_mem _ hq)`.

Rewrite `h1` using `[hR, MvPolynomial.eval_rename]`. Then use the resulting hypothesis. Introduce `hx q hq`. Take `⟨p, hp, rfl⟩` from `(Ideal.mem_map_of_equiv R q).1 hq`. Rewrite using `[hR, MvPolynomial.eval_rename]`. Conclude with `hx p hp`.

Use `set φ' : (Fin k → ℂ) → Fin n → ℂ := fun t j => φ t (e.symm j) with hφ'`. Establish `hφ'e : ∀ t, φ' t ∘ e = φ t` using `fun t => by`. Use function extensionality and compare the values at `i`. Simplify using `[φ']`. Establish `hφ'd : DifferentiableOn ℂ φ' U` using `differentiableOn_pi.2 (fun j => (differentiableOn_pi.1 hφ) (e.symm j))`.

Establish `hinj' : Set.InjOn φ' U`. Introduce `a ha b hb hab`. Apply `hinj ha hb` to reduce the goal to its premises. Rewrite using `[← hφ'e a, ← hφ'e b, hab]`. Establish `hmaps' : Set.MapsTo φ' U (zeroSetIn I')`.

Introduce `t ht`. Rewrite using `[hmem, hφ'e]`. Conclude with `hmaps ht`. Establish `key : ∀ u ∈ U, ∃ B : Set (Fin n → ℂ), IsOpen B ∧ φ' u ∈ B ∧ zeroSetIn I' ∩ B ⊆ φ' '' U` using `fun u hu => normalOpenMapping_local_fin hNLI hLNN hFB hDC hIFO I' U φ' hI' hic' hdim' hU hφ'd hinj' hmaps' u hu`. Use `choose! Bf hBo hBm hBs using key`.

Set `T : (σ → ℂ) → Fin n → ℂ` to `fun z j => z (e.symm j)`. Establish `hTc : Continuous T` using `continuous_pi (fun j => continuous_apply (e.symm j))`. Use `⟨T ⁻¹' (⋃ u ∈ U, Bf u), (isOpen_biUnion (fun u hu => hBo u hu)).preimage hTc, ?_⟩` and prove the remaining obligations. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, hu, rfl⟩`. Conclude with `⟨hmaps hu, Set.mem_iUnion₂.2 ⟨u, hu, hBm u hu⟩⟩`. Introduce and unpack `⟨hzX, hzO⟩`. Take `⟨u, hu, hzu⟩` from `Set.mem_iUnion₂.1 hzO`. Establish `hTe : T z ∘ e = z`.

Use function extensionality and compare the values at `i`. Simplify using `[T]`. Establish `hz' : T z ∈ zeroSetIn I'`. Rewrite using `[hmem, hTe]`. Conclude with `hzX`.

Take `⟨v, hv, hvz⟩` from `hBs u hu ⟨hz', hzu⟩`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Rewrite using `[← hφ'e v, hvz, hTe]`.
-/
theorem NormalOpenMapping.proof
    (hNLI : NormalLocallyIrreducible.Statement)
    (hLNN : GroundTheory.Heights₂.Heights.ComplexSets.LinearNoetherNormalization.Statement)
    (hFB : GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.Statement)
    (hDC : GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.Statement)
    (hIFO : HolomorphicIsolatedFibreOpen.Statement) :
    NormalOpenMapping.Statement := by
  intro σ _ I k U φ hI hic hdim hU hφ hinj hmaps
  classical

  set n := Fintype.card σ
  let e : σ ≃ Fin n := Fintype.equivFin σ
  let R : MvPolynomial σ ℂ ≃+* MvPolynomial (Fin n) ℂ := (MvPolynomial.renameEquiv ℂ e).toRingEquiv
  let I' : Ideal (MvPolynomial (Fin n) ℂ) := I.map (R : MvPolynomial σ ℂ →+* MvPolynomial (Fin n) ℂ)
  have hI' : I'.IsPrime := by
    have := hI
    exact Ideal.map_isPrime_of_equiv R
  let Q : (MvPolynomial σ ℂ ⧸ I) ≃+* (MvPolynomial (Fin n) ℂ ⧸ I') := Ideal.quotientEquiv I I' R rfl
  have hic' : IsIntegrallyClosed (MvPolynomial (Fin n) ℂ ⧸ I') := by
    have := hic
    exact IsIntegrallyClosed.of_equiv Q
  have hdim' : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I') = (k : ℕ) := by
    rw [← ringKrullDim_eq_of_ringEquiv Q, hdim]
  have hR : ∀ p : MvPolynomial σ ℂ, R p = rename e p := fun p => rfl
  have hmem : ∀ x : Fin n → ℂ, x ∈ zeroSetIn I' ↔ x ∘ e ∈ zeroSetIn I := by
    intro x
    constructor
    · intro hx q hq
      have h1 := hx (R q) (Ideal.mem_map_of_mem _ hq)
      rwa [hR, MvPolynomial.eval_rename] at h1
    · intro hx q hq
      obtain ⟨p, hp, rfl⟩ := (Ideal.mem_map_of_equiv R q).1 hq
      rw [hR, MvPolynomial.eval_rename]
      exact hx p hp

  set φ' : (Fin k → ℂ) → Fin n → ℂ := fun t j => φ t (e.symm j) with hφ'
  have hφ'e : ∀ t, φ' t ∘ e = φ t := fun t => by
    funext i
    simp [φ']
  have hφ'd : DifferentiableOn ℂ φ' U :=
    differentiableOn_pi.2 (fun j => (differentiableOn_pi.1 hφ) (e.symm j))
  have hinj' : Set.InjOn φ' U := by
    intro a ha b hb hab
    apply hinj ha hb
    rw [← hφ'e a, ← hφ'e b, hab]
  have hmaps' : Set.MapsTo φ' U (zeroSetIn I') := by
    intro t ht
    rw [hmem, hφ'e]
    exact hmaps ht
  have key : ∀ u ∈ U, ∃ B : Set (Fin n → ℂ), IsOpen B ∧ φ' u ∈ B ∧ zeroSetIn I' ∩ B ⊆ φ' '' U :=
    fun u hu => normalOpenMapping_local_fin hNLI hLNN hFB hDC hIFO I' U φ' hI' hic' hdim' hU hφ'd hinj'
      hmaps' u hu
  choose! Bf hBo hBm hBs using key

  let T : (σ → ℂ) → Fin n → ℂ := fun z j => z (e.symm j)
  have hTc : Continuous T := continuous_pi (fun j => continuous_apply (e.symm j))
  refine ⟨T ⁻¹' (⋃ u ∈ U, Bf u), (isOpen_biUnion (fun u hu => hBo u hu)).preimage hTc, ?_⟩
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨hmaps hu, Set.mem_iUnion₂.2 ⟨u, hu, hBm u hu⟩⟩
  · rintro ⟨hzX, hzO⟩
    obtain ⟨u, hu, hzu⟩ := Set.mem_iUnion₂.1 hzO
    have hTe : T z ∘ e = z := by
      funext i
      simp [T]
    have hz' : T z ∈ zeroSetIn I' := by
      rw [hmem, hTe]
      exact hzX
    obtain ⟨v, hv, hvz⟩ := hBs u hu ⟨hz', hzu⟩
    refine ⟨v, hv, ?_⟩
    rw [← hφ'e v, hvz, hTe]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
