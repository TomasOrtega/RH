import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerKAvgNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactAverageKFiniteFiniteRank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HCModIrred

open GlobalTheory.TypeSum Formalism.REAL Formalism.MainNotions.S
open scoped InnerProductSpace

section Model

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

/- English proof (translation)
Take `⟨c1, c2, c3, c4⟩` from `kCoef_kAvg n ε H σ h.1`. Establish `havgW : ∀ e : KG ε → ℂ, Continuous e → ∀ x ∈ W, kAvg ε σ e x ∈ W`. Introduce `e he x hx`. Take `⟨S, hS, hxS, hKS⟩` from `hW x hx`. Use `haveI := hS`.

Use `haveI : FiniteDimensional ℂ (S ⊓ W : Submodule ℂ H) := Submodule.finiteDimensional_inf_left S W`. Establish `hKSW : IsKStableOn ε σ (S ⊓ W)` using `fun g hg y hy => Submodule.mem_inf.2 ⟨hKS g hg y (Submodule.mem_inf.1 hy).1, hK g hg y (Submodule.mem_inf.1 hy).2⟩`. Conclude with `(Submodule.mem_inf.1 (c4 e he _ inferInstance hKSW x (Submodule.mem_inf.2 ⟨hxS, hx⟩))).2`. Establish `hrange : ∀ e : KG ε → ℂ, KFinFun ε e → Continuous e → ∀ w, kAvg ε σ e w ∈ W`. Introduce `e he hc w`.

Take `⟨m, b, c, -, -, -, hbc⟩` from `kAvg_finite_rank n ε H σ h e he`. Take `⟨Q, hQ⟩` from `c3 e hc`. Set `F : Submodule ℂ H` to `Submodule.span ℂ (Set.range b)`. Use `haveI : FiniteDimensional ℂ F := FiniteDimensional.span_of_finite ℂ (Set.finite_range b)`. Use `haveI : FiniteDimensional ℂ (W ⊓ F : Submodule ℂ H) := Submodule.finiteDimensional_inf_right W F`.

Establish `hcl : IsClosed (Q ⁻¹' ((W ⊓ F : Submodule ℂ H) : Set H))` using `(Submodule.closed_of_finiteDimensional _).preimage Q.continuous`. Establish `hsub : (W : Set H) ⊆ Q ⁻¹' ((W ⊓ F : Submodule ℂ H) : Set H)`. Introduce `x hx`. Use `Submodule.mem_inf.2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hQ]`.

Conclude with `havgW e hc x hx`. Rewrite using `[hQ, hbc]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Use `closure_minimal hsub hcl (hd w)` as an intermediate fact. Rewrite using `[← hQ]`.

Conclude with `(Submodule.mem_inf.1 this).1`. Take `⟨S, hS, hvS, hKS⟩` from `hv`. Use `haveI := hS`. Use `haveI : FiniteDimensional ℂ (S ⊓ W : Submodule ℂ H) := Submodule.finiteDimensional_inf_left S W`. Take `⟨w, hw, y, hy, hvwy⟩` from `(S ⊓ W).exists_add_mem_mem_orthogonal v`.

Establish `hyS : y ∈ S`. Use `S.sub_mem hvS (Submodule.mem_inf.1 hw).1` as an intermediate fact. Rewrite `this` using `[hvwy, add_sub_cancel_left]`. Then use the resulting hypothesis. Establish `hy0 : y = 0`. Assume the negation of the conclusion as `hy0`.

Establish `hk` using `c1 y ⟨S, hS, hyS, hKS⟩`. Establish `hc : Continuous fun k : KG ε => star ⟪y, σ (toMK k) y⟫_ℂ`. Take `⟨F, -, h1, h2, -⟩` from `hk`. Conclude with `h2 _ h1`. Conclude with `c2 y hy0 (Submodule.inner_left_of_mem_orthogonal (Submodule.mem_inf.2 ⟨c4 _ hc S hS hKS y hyS, hrange _ hk hc y⟩) hy)`.

Rewrite using `[hvwy, hy0, add_zero]`. Conclude with `(Submodule.mem_inf.1 hw).2`.
-/
theorem mem_of_dense (h : Std ε σ) {W : Submodule ℂ H} (hd : Dense (W : Set H))
    (hW : ∀ w ∈ W, IsKFin ε σ w) (hK : ∀ k ∈ Kset ε, ∀ w ∈ W, σ k w ∈ W) {v : H} (hv : IsKFin ε σ v) :
    v ∈ W := by
  obtain ⟨c1, c2, c3, c4⟩ := kCoef_kAvg n ε H σ h.1
  have havgW : ∀ e : KG ε → ℂ, Continuous e → ∀ x ∈ W, kAvg ε σ e x ∈ W := by
    intro e he x hx
    obtain ⟨S, hS, hxS, hKS⟩ := hW x hx
    haveI := hS
    haveI : FiniteDimensional ℂ (S ⊓ W : Submodule ℂ H) := Submodule.finiteDimensional_inf_left S W
    have hKSW : IsKStableOn ε σ (S ⊓ W) := fun g hg y hy =>
      Submodule.mem_inf.2 ⟨hKS g hg y (Submodule.mem_inf.1 hy).1, hK g hg y (Submodule.mem_inf.1 hy).2⟩
    exact (Submodule.mem_inf.1 (c4 e he _ inferInstance hKSW x (Submodule.mem_inf.2 ⟨hxS, hx⟩))).2
  have hrange : ∀ e : KG ε → ℂ, KFinFun ε e → Continuous e → ∀ w, kAvg ε σ e w ∈ W := by
    intro e he hc w
    obtain ⟨m, b, c, -, -, -, hbc⟩ := kAvg_finite_rank n ε H σ h e he
    obtain ⟨Q, hQ⟩ := c3 e hc
    let F : Submodule ℂ H := Submodule.span ℂ (Set.range b)
    haveI : FiniteDimensional ℂ F := FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
    haveI : FiniteDimensional ℂ (W ⊓ F : Submodule ℂ H) := Submodule.finiteDimensional_inf_right W F
    have hcl : IsClosed (Q ⁻¹' ((W ⊓ F : Submodule ℂ H) : Set H)) :=
      (Submodule.closed_of_finiteDimensional _).preimage Q.continuous
    have hsub : (W : Set H) ⊆ Q ⁻¹' ((W ⊓ F : Submodule ℂ H) : Set H) := by
      intro x hx
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · rw [hQ]; exact havgW e hc x hx
      · rw [hQ, hbc]
        exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have := closure_minimal hsub hcl (hd w)
    rw [← hQ]
    exact (Submodule.mem_inf.1 this).1
  obtain ⟨S, hS, hvS, hKS⟩ := hv
  haveI := hS
  haveI : FiniteDimensional ℂ (S ⊓ W : Submodule ℂ H) := Submodule.finiteDimensional_inf_left S W
  obtain ⟨w, hw, y, hy, hvwy⟩ := (S ⊓ W).exists_add_mem_mem_orthogonal v
  have hyS : y ∈ S := by
    have := S.sub_mem hvS (Submodule.mem_inf.1 hw).1
    rwa [hvwy, add_sub_cancel_left] at this
  have hy0 : y = 0 := by
    by_contra hy0
    have hk := c1 y ⟨S, hS, hyS, hKS⟩
    have hc : Continuous fun k : KG ε => star ⟪y, σ (toMK k) y⟫_ℂ := by
      obtain ⟨F, -, h1, h2, -⟩ := hk
      exact h2 _ h1
    exact c2 y hy0 (Submodule.inner_left_of_mem_orthogonal
      (Submodule.mem_inf.2 ⟨c4 _ hc S hS hKS y hyS, hrange _ hk hc y⟩) hy)
  rw [hvwy, hy0, add_zero]
  exact (Submodule.mem_inf.1 hw).2

/- English proof (translation)
Establish `hXl : X ∈ GlobalTheory.SmoothGlob.lieSet ε` using `hXg`. Establish `hsplit : ∀ s t : ℝ, NormedSpace.exp (s • X) = NormedSpace.exp (t • X) * NormedSpace.exp ((s - t) • X)`. Introduce `s t`. Rewrite using `[← Matrix.exp_add_of_commute _ _ ((Commute.refl X).smul_left t |>.smul_right (s - t))]`. Use `congr 1`.

Rewrite using `[← add_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hderiv : ∀ v, IsKFin ε σ v → ∀ t : ℝ, HasDerivAt (fun s : ℝ => σ (NormedSpace.exp (s • X)) v) (σ (NormedSpace.exp (t • X)) (dRep σ X v)) t`. Introduce `v hv t`.

Establish `han` using `(hHC.analytic hU hI hv).analytic_exp (one_mem_UJ ε) hXg 0`. Simplify using `only [one_mul] at han`. Establish `h0 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp (s • X)) v) (dRep σ X v) 0` using `han.differentiableAt.hasDerivAt`. Establish `h1 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s - t) • X)) v) (dRep σ X v) t`. Use `HasDerivAt.comp_sub_const (f := fun s : ℝ => σ (NormedSpace.exp (s • X)) v) t t (by rw [sub_self]; exact h0)` as an intermediate fact.

Conclude with `this`. Establish `h2` using `((σ (NormedSpace.exp (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1`. Use `h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Use `show σ (NormedSpace.exp (s • X)) v = σ (NormedSpace.exp (t • X)) (σ (NormedSpace.exp ((s - t) • X)) v)`. Rewrite using `[hsplit s t, sigma_mul hU (exp_mem_UJ hXl t) (exp_mem_UJ hXl (s - t))]`.

Establish `hmem : ∀ k : ℕ, (dRep σ X)^[k] a ∈ W`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact ha`. Consider the case `succ k ih => rw [Function.iterate_succ_apply']`.

Conclude with `hX _ ih`. Set `f : ℕ → ℝ → ℂ` to `fun k s => ⟪y, σ (NormedSpace.exp (s • X)) ((dRep σ X)^[k] a)⟫_ℂ`. Establish `hf : ∀ k s, HasDerivAt (f k) (f (k + 1) s) s`. Introduce `k s`. Establish `h` using `((innerSL ℂ y).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hderiv _ (hW _ (hmem k)) s)`.

Simplify using `only [f, Function.iterate_succ_apply']`. Conclude with `h`. Establish `hit : ∀ k, iteratedDeriv k (f 0) = f k`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => simp`. Consider the case `succ k ih => rw [iteratedDeriv_succ, ih]`. Use function extensionality and compare the values at `s`. Conclude with `(hf k s).deriv`. Establish `hA : AnalyticOnNhd ℝ (f 0) Set.univ`.

Introduce `s _`. Use `((hHC.analytic hU hI (hW a ha)).clm ((innerSL ℂ y).restrictScalars ℝ)).analytic_exp (one_mem_UJ ε) hXg s` as an intermediate fact. Simplify using `only [one_mul] at this`. Conclude with `this`. Establish `h0 : ∀ k, f k 0 = 0`.

Introduce `k`. Simplify using `only [f, zero_smul, NormedSpace.exp_zero, sigma_one hU]`. Conclude with `Submodule.inner_left_of_mem_orthogonal (hmem k) hy`. Establish `htop : analyticOrderAt (f 0) 0 = ⊤`. Rewrite using `[ENat.eq_top_iff_forall_ge]`.

Introduce `m`. Rewrite using `[natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hA 0 trivial)]`. Introduce `i _`. Rewrite using `[hit, h0]`. Conclude with `hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) (analyticOrderAt_eq_top.mp htop) (Set.mem_univ t)`.
-/
theorem inner_exp_eq_zero (hHC : GlobalTheory.Published.HarishChandraModules) (hU : IsURepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) {W : Submodule ℂ H} (hW : ∀ w ∈ W, IsKFin ε σ w)
    {X : Matrix (Fin n) (Fin n) ℂ} (hXg : inG ε X) (hX : ∀ w ∈ W, dRep σ X w ∈ W)
    {a : H} (ha : a ∈ W) {y : H} (hy : y ∈ Wᗮ) (t : ℝ) :
    ⟪y, σ (NormedSpace.exp (t • X)) a⟫_ℂ = 0 := by
  have hXl : X ∈ GlobalTheory.SmoothGlob.lieSet ε := hXg
  have hsplit : ∀ s t : ℝ, NormedSpace.exp (s • X) = NormedSpace.exp (t • X) * NormedSpace.exp ((s - t) • X) := by
    intro s t
    rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl X).smul_left t |>.smul_right (s - t))]
    congr 1
    rw [← add_smul]; congr 1; ring
  have hderiv : ∀ v, IsKFin ε σ v → ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => σ (NormedSpace.exp (s • X)) v) (σ (NormedSpace.exp (t • X)) (dRep σ X v)) t := by
    intro v hv t
    have han := (hHC.analytic hU hI hv).analytic_exp (one_mem_UJ ε) hXg 0
    simp only [one_mul] at han
    have h0 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp (s • X)) v) (dRep σ X v) 0 :=
      han.differentiableAt.hasDerivAt
    have h1 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s - t) • X)) v) (dRep σ X v) t := by
      have := HasDerivAt.comp_sub_const (f := fun s : ℝ => σ (NormedSpace.exp (s • X)) v) t t (by rw [sub_self]; exact h0)
      exact this
    have h2 := ((σ (NormedSpace.exp (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show σ (NormedSpace.exp (s • X)) v = σ (NormedSpace.exp (t • X)) (σ (NormedSpace.exp ((s - t) • X)) v)
    rw [hsplit s t, sigma_mul hU (exp_mem_UJ hXl t) (exp_mem_UJ hXl (s - t))]
  have hmem : ∀ k : ℕ, (dRep σ X)^[k] a ∈ W := by
    intro k
    induction k with
    | zero => exact ha
    | succ k ih => rw [Function.iterate_succ_apply']; exact hX _ ih
  let f : ℕ → ℝ → ℂ := fun k s => ⟪y, σ (NormedSpace.exp (s • X)) ((dRep σ X)^[k] a)⟫_ℂ
  have hf : ∀ k s, HasDerivAt (f k) (f (k + 1) s) s := by
    intro k s
    have h := ((innerSL ℂ y).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hderiv _ (hW _ (hmem k)) s)
    simp only [f, Function.iterate_succ_apply']
    exact h
  have hit : ∀ k, iteratedDeriv k (f 0) = f k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [iteratedDeriv_succ, ih]; funext s; exact (hf k s).deriv
  have hA : AnalyticOnNhd ℝ (f 0) Set.univ := by
    intro s _
    have := ((hHC.analytic hU hI (hW a ha)).clm ((innerSL ℂ y).restrictScalars ℝ)).analytic_exp (one_mem_UJ ε) hXg s
    simp only [one_mul] at this
    exact this
  have h0 : ∀ k, f k 0 = 0 := by
    intro k
    simp only [f, zero_smul, NormedSpace.exp_zero, sigma_one hU]
    exact Submodule.inner_left_of_mem_orthogonal (hmem k) hy
  have htop : analyticOrderAt (f 0) 0 = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro m
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hA 0 trivial)]
    intro i _
    rw [hit, h0]
  exact hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0)
    (analyticOrderAt_eq_top.mp htop) (Set.mem_univ t)

/- English proof (translation)
Establish `hexp : ∀ X, inG ε X → ∀ x ∈ W.topologicalClosure, σ (NormedSpace.exp X) x ∈ W.topologicalClosure`. Introduce `X hXg x hx`. Establish `hW1 : ∀ a ∈ W, σ (NormedSpace.exp X) a ∈ W.topologicalClosure`. Introduce `a ha`. Rewrite using `[← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]`.

Introduce `y hy`. Use `inner_exp_eq_zero hHC hU hI hW hXg (hX X hXg) ha hy 1` as an intermediate fact. Rewrite `this` using `[one_smul]`. Then use the resulting hypothesis. Establish `hcl : IsClosed ((σ (NormedSpace.exp X)) ⁻¹' (W.topologicalClosure : Set H))` using `(Submodule.isClosed_topologicalClosure _).preimage (ContinuousLinearMap.continuous _)`. Conclude with `closure_minimal (fun a ha => hW1 a ha) hcl hx`.

Establish `hKc : ∀ k ∈ Kset ε, ∀ x ∈ W.topologicalClosure, σ k x ∈ W.topologicalClosure` using `fun k hk x hx => map_mem_closure (σ k).continuous hx (hK k hk)`. Establish `hinv : ∀ g ∈ UJset ε, ∀ x ∈ W.topologicalClosure, σ g x ∈ W.topologicalClosure`. Introduce `g hg x hx`. Take `⟨k, P, hk, hP, rfl⟩` from `(Formalism.REAL.polar_decomposition_holds n ε).1 g hg`. Establish `hPl : P ∈ GlobalTheory.SmoothGlob.lieSet ε` using `hP.1`.

Establish `hPe : NormedSpace.exp P ∈ UJset ε` using `by simpa using exp_mem_UJ hPl 1`. Rewrite using `[sigma_mul hU (K_le_UJ hk) hPe]`. Conclude with `hKc k hk _ (hexp P hP.1 x hx)`. Break down `hI _ (Submodule.isClosed_topologicalClosure W) hinv with h | h` into its components or cases. Conclude with `absurd (le_bot_iff.1 (h ▸ W.le_topologicalClosure)) h0`.

Conclude with `Submodule.dense_iff_topologicalClosure_eq_top.2 h`.
-/
theorem dense_of_stable (hHC : GlobalTheory.Published.HarishChandraModules) (hU : IsURepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) {W : Submodule ℂ H} (hW : ∀ w ∈ W, IsKFin ε σ w)
    (hX : ∀ X, inG ε X → ∀ w ∈ W, dRep σ X w ∈ W) (hK : ∀ k ∈ Kset ε, ∀ w ∈ W, σ k w ∈ W) (h0 : W ≠ ⊥) :
    Dense (W : Set H) := by
  have hexp : ∀ X, inG ε X → ∀ x ∈ W.topologicalClosure, σ (NormedSpace.exp X) x ∈ W.topologicalClosure := by
    intro X hXg x hx
    have hW1 : ∀ a ∈ W, σ (NormedSpace.exp X) a ∈ W.topologicalClosure := by
      intro a ha
      rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
      intro y hy
      have := inner_exp_eq_zero hHC hU hI hW hXg (hX X hXg) ha hy 1
      rwa [one_smul] at this
    have hcl : IsClosed ((σ (NormedSpace.exp X)) ⁻¹' (W.topologicalClosure : Set H)) :=
      (Submodule.isClosed_topologicalClosure _).preimage (ContinuousLinearMap.continuous _)
    exact closure_minimal (fun a ha => hW1 a ha) hcl hx
  have hKc : ∀ k ∈ Kset ε, ∀ x ∈ W.topologicalClosure, σ k x ∈ W.topologicalClosure := fun k hk x hx =>
    map_mem_closure (σ k).continuous hx (hK k hk)
  have hinv : ∀ g ∈ UJset ε, ∀ x ∈ W.topologicalClosure, σ g x ∈ W.topologicalClosure := by
    intro g hg x hx
    obtain ⟨k, P, hk, hP, rfl⟩ := (Formalism.REAL.polar_decomposition_holds n ε).1 g hg
    have hPl : P ∈ GlobalTheory.SmoothGlob.lieSet ε := hP.1
    have hPe : NormedSpace.exp P ∈ UJset ε := by simpa using exp_mem_UJ hPl 1
    rw [sigma_mul hU (K_le_UJ hk) hPe]
    exact hKc k hk _ (hexp P hP.1 x hx)
  rcases hI _ (Submodule.isClosed_topologicalClosure W) hinv with h | h
  · exact absurd (le_bot_iff.1 (h ▸ W.le_topologicalClosure)) h0
  · exact Submodule.dense_iff_topologicalClosure_eq_top.2 h

end Model

open Formalism.IndefR.Mult in

/- English proof (translation)
Introduce `hHC D V S M τ W hWk hX hK h0`. Take `⟨hc, -, hU, hI, -⟩` from `M.ds τ`. Use `haveI := hc`. Establish `hfr : IsUnit (M.fr τ)` using `M.fr_unit τ`. Establish `hd` using `(Matrix.isUnit_iff_isUnit_det _).1 hfr`.

Establish `hW : ∀ w ∈ W, IsKFin (M.ε τ) (M.σ τ) w` using `fun w hw => hWk hw`. Establish `hX' : ∀ X, inG (M.ε τ) X → ∀ w ∈ W, dRep (M.σ τ) X w ∈ W`. Introduce `X hXg w hw`. Establish `hXg' : Xᴴ * Jm (M.ε τ) + Jm (M.ε τ) * X = 0` using `hXg`. Establish `hmem : (M.fr τ)⁻¹ * X * M.fr τ ∈ lieAt V τ` using `by show ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * gramAt D V τ + gramAt D V τ * ((M.fr τ)⁻¹ * X * M.fr τ) = 0`.

Rewrite using `[← M.fr_gram τ]`. Establish `h1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1`. Rewrite using `[← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`.

Use `_ = (M.fr τ)ᴴ * (Xᴴ * Jm (M.ε τ) + Jm (M.ε τ) * X) * M.fr τ := by`. Rewrite using `[h1, Matrix.mul_nonsing_inv _ hd]`. Simplify using `only [Matrix.mul_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]`. Use `_ = 0 := by rw [hXg']; simp`. Establish `e : dRep (M.rep τ) ((M.fr τ)⁻¹ * X * M.fr τ) w = dRep (M.σ τ) X w`.

Unfold `dRep`. Use `congr 1`. Use function extensionality and compare the values at `t`. Rewrite using `[DSModel.rep, GlobalTheory.SmVec.exp_conj_inv hfr X t]`. Use `congr 2`.

Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]`. Rewrite using `[← e]`. Conclude with `hX _ hmem w hw`. Establish `hK' : ∀ k ∈ Kset (M.ε τ), ∀ w ∈ W, M.σ τ k w ∈ W`. Introduce `k hk w hw`.

Establish `e : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]`. Establish `hm : (M.fr τ)⁻¹ * k * M.fr τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ` using `by show M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)`. Rewrite using `[e]`. Conclude with `hk`.

Use `hK _ hm w hw` as an intermediate fact. Rewrite `this` using `[DSModel.rep, e]`. Then use the resulting hypothesis. Establish `hdense` using `dense_of_stable hHC hU hI hW hX' hK' h0`. Establish `hstd` using `GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)`. Introduce `v hv`.

Conclude with `mem_of_dense hstd hdense hW hK' hv`.
-/
theorem kFin_le_of_stable : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : DSModel V S) (τ : D.what₂.Tau) (W : Submodule ℂ (M.H τ)), W ≤ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ →
    (∀ X ∈ lieAt V τ, ∀ w ∈ W, dRep (M.rep τ) X w ∈ W) →
    (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ, ∀ w ∈ W, M.rep τ k w ∈ W) → W ≠ ⊥ → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ W := by
  intro hHC D V S M τ W hWk hX hK h0
  obtain ⟨hc, -, hU, hI, -⟩ := M.ds τ
  haveI := hc
  have hfr : IsUnit (M.fr τ) := M.fr_unit τ
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hfr
  have hW : ∀ w ∈ W, IsKFin (M.ε τ) (M.σ τ) w := fun w hw => hWk hw
  have hX' : ∀ X, inG (M.ε τ) X → ∀ w ∈ W, dRep (M.σ τ) X w ∈ W := by
    intro X hXg w hw
    have hXg' : Xᴴ * Jm (M.ε τ) + Jm (M.ε τ) * X = 0 := hXg
    have hmem : (M.fr τ)⁻¹ * X * M.fr τ ∈ lieAt V τ := by
      show ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * gramAt D V τ + gramAt D V τ * ((M.fr τ)⁻¹ * X * M.fr τ) = 0
      rw [← M.fr_gram τ]
      have h1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
        rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]
      calc ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Jm (M.ε τ) * M.fr τ) +
            (M.fr τ)ᴴ * Jm (M.ε τ) * M.fr τ * ((M.fr τ)⁻¹ * X * M.fr τ)
          = (M.fr τ)ᴴ * Xᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Jm (M.ε τ) * M.fr τ +
            (M.fr τ)ᴴ * Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * X * M.fr τ := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = (M.fr τ)ᴴ * (Xᴴ * Jm (M.ε τ) + Jm (M.ε τ) * X) * M.fr τ := by
            rw [h1, Matrix.mul_nonsing_inv _ hd]
            simp only [Matrix.mul_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = 0 := by rw [hXg']; simp
    have e : dRep (M.rep τ) ((M.fr τ)⁻¹ * X * M.fr τ) w = dRep (M.σ τ) X w := by
      unfold dRep
      congr 1
      funext t
      rw [DSModel.rep, GlobalTheory.SmVec.exp_conj_inv hfr X t]
      congr 2
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    rw [← e]
    exact hX _ hmem w hw
  have hK' : ∀ k ∈ Kset (M.ε τ), ∀ w ∈ W, M.σ τ k w ∈ W := by
    intro k hk w hw
    have e : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    have hm : (M.fr τ)⁻¹ * k * M.fr τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ := by
      show M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)
      rw [e]; exact hk
    have := hK _ hm w hw
    rwa [DSModel.rep, e] at this
  have hdense := dense_of_stable hHC hU hI hW hX' hK' h0
  have hstd := GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)
  intro v hv
  exact mem_of_dense hstd hdense hW hK' hv

end GlobalTheory.HCModIrred

end
