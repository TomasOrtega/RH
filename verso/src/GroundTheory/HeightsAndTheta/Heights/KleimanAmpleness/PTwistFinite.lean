import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistFiniteness.CoeffPsiMulSingle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial AddMonoidAlgebra TwistFin

universe u w

/- English proof (translation)
Introduce `S _ _ Ω _ _ N x G B r η hx _ hgen`. Take `⟨M0, -, hG⟩` from `hE S Ω N x Ω G.toSubFamily G.fg`. Take `⟨n0, d0, g0, -, hspan⟩` from `M0.fg`. Choose the witnesses or unpack the hypotheses as in `⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Conclude with `hx (funext h)`. Establish `hfin : Module.Finite (Sy S r) (cohom (tgraded x η S n0 d0 g0) 0 0)` using `hSF (Sy S r) N _ (tgraded x η S n0 d0 g0) inferInstance 0 0`. Set `Γ : Set (Amb x η)` to `{γ | ∃ (b : ℕ) (s : Ω), s ∈ (G.twist (B.pow b)).secs ∧ γ = (toA x η).symm (single ((0 : ℤ), (b : ℤ)) s)}`. Establish `hΓ : Γ ⊆ LinearMap.range (readChartH0 x η S n0 d0 g0 i0 hi0)`.

Introduce and unpack `_ ⟨b, s, hs, rfl⟩`. Use `mem_range_readChartH0 x η S n0 d0 g0 i0 hi0 _ fun I hI => ?_` and prove the remaining obligations. Use `chart_pre x η S M0 G B hgen hG hspan I hI b ?_` and prove the remaining obligations. Rewrite `hs` using `[SubSystem.secs, Submodule.mem_iInf]`. Conclude with `hs (toChart x I hI)`.

Establish `hfg : (Submodule.span (Sy S r) Γ).FG`. Establish `: IsNoetherian (Sy S r) (LinearMap.range (readChartH0 x η S n0 d0 g0 i0 hi0))` using `isNoetherian_of_fg_of_noetherian _ (Module.Finite.iff_fg.mp inferInstance)`. Conclude with `isNoetherian_submodule.mp this _ (Submodule.span_le.mpr hΓ)`. Take `⟨t, ht⟩` from `hfg`. Take `⟨T, hTΓ, htT⟩` from `Submodule.subset_span_finite_of_subset_span (R := Sy S r) (s := Γ) (t := t) (by rw [← ht]; exact Submodule.subset_span)`.

Establish `hle : Submodule.span (Sy S r) Γ ≤ Submodule.span (Sy S r) (T : Set (Amb x η))`. Rewrite using `[← ht, Submodule.span_le]`. Conclude with `htT`. Establish `hT : ∀ γ : T, ∃ (b : ℕ) (s : Ω), s ∈ (G.twist (B.pow b)).secs ∧ (γ : Amb x η) = (toA x η).symm (single ((0 : ℤ), (b : ℤ)) s)` using `fun γ => hTΓ γ.2`. Use `choose bT sT hsT hγT using hT`.

Set `e` to `T.equivFin`. Use `⟨T.card, fun k => bT (e.symm k), fun k => sT (e.symm k), fun k => hsT _, ?_⟩` and prove the remaining obligations. Introduce `b s hs`. Establish `hmem : (toA x η).symm (single ((0 : ℤ), (b : ℤ)) s) ∈ Submodule.span (Sy S r) (T : Set (Amb x η))` using `hle (Submodule.subset_span ⟨b, s, hs, rfl⟩)`. Take `⟨c, -, hc⟩` from `Submodule.mem_span_finset.mp hmem`.

Establish `hcoef` using `congrArg (fun a => (toA x η a).coeff ((0 : ℤ), (b : ℤ))) hc`. Simplify using `only [AddEquiv.apply_symm_apply, map_sum, toA_smulSy, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, coeff_single, Finsupp.single_eq_same] at hcoef`. Rewrite using `[← hcoef]`. Use `Submodule.sum_mem _ fun γ hγ => ?_` and prove the remaining obligations. Establish `h1 : toA x η γ = single ((0 : ℤ), ((bT ⟨γ, hγ⟩ : ℕ) : ℤ)) (sT ⟨γ, hγ⟩)`.

Use `congrArg (toA x η) (hγT ⟨γ, hγ⟩)` as an intermediate fact. Rewrite `this` using `[AddEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Rewrite using `[h1, coeff_psi_mul_single]`. Use `Submodule.sum_mem _ fun d _ => ?_` and prove the remaining obligations. Use `split_ifs with hdb`.

Use `Submodule.subset_span ⟨e ⟨γ, hγ⟩, homogeneousComponent d (c γ), d, homogeneousComponent_isHomogeneous _ _, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Equiv.symm_apply_apply]`. Conclude with `hdb`. Simplify using `only [Equiv.symm_apply_apply]`. Conclude with `zero_mem _`.
-/
theorem TwistFinite.proof (hE : Extension.Statement.{u, w, w}) (hSF : SerreFinite.Statement.{u, w}) :
    TwistFinite.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x G B r η hx _ hgen
  classical
  obtain ⟨M0, -, hG⟩ := hE S Ω N x Ω G.toSubFamily G.fg
  obtain ⟨n0, d0, g0, -, hspan⟩ := M0.fg
  obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have hfin : Module.Finite (Sy S r) (cohom (tgraded x η S n0 d0 g0) 0 0) :=
    hSF (Sy S r) N _ (tgraded x η S n0 d0 g0) inferInstance 0 0
  let Γ : Set (Amb x η) := {γ | ∃ (b : ℕ) (s : Ω), s ∈ (G.twist (B.pow b)).secs ∧
    γ = (toA x η).symm (single ((0 : ℤ), (b : ℤ)) s)}
  have hΓ : Γ ⊆ LinearMap.range (readChartH0 x η S n0 d0 g0 i0 hi0) := by
    rintro _ ⟨b, s, hs, rfl⟩
    refine mem_range_readChartH0 x η S n0 d0 g0 i0 hi0 _ fun I hI => ?_
    refine chart_pre x η S M0 G B hgen hG hspan I hI b ?_
    rw [SubSystem.secs, Submodule.mem_iInf] at hs
    exact hs (toChart x I hI)
  have hfg : (Submodule.span (Sy S r) Γ).FG := by
    have : IsNoetherian (Sy S r) (LinearMap.range (readChartH0 x η S n0 d0 g0 i0 hi0)) :=
      isNoetherian_of_fg_of_noetherian _ (Module.Finite.iff_fg.mp inferInstance)
    exact isNoetherian_submodule.mp this _ (Submodule.span_le.mpr hΓ)
  obtain ⟨t, ht⟩ := hfg
  obtain ⟨T, hTΓ, htT⟩ := Submodule.subset_span_finite_of_subset_span
    (R := Sy S r) (s := Γ) (t := t) (by rw [← ht]; exact Submodule.subset_span)
  have hle : Submodule.span (Sy S r) Γ ≤ Submodule.span (Sy S r) (T : Set (Amb x η)) := by
    rw [← ht, Submodule.span_le]
    exact htT
  have hT : ∀ γ : T, ∃ (b : ℕ) (s : Ω), s ∈ (G.twist (B.pow b)).secs ∧
      (γ : Amb x η) = (toA x η).symm (single ((0 : ℤ), (b : ℤ)) s) := fun γ => hTΓ γ.2
  choose bT sT hsT hγT using hT
  let e := T.equivFin
  refine ⟨T.card, fun k => bT (e.symm k), fun k => sT (e.symm k), fun k => hsT _, ?_⟩
  intro b s hs
  have hmem : (toA x η).symm (single ((0 : ℤ), (b : ℤ)) s) ∈
      Submodule.span (Sy S r) (T : Set (Amb x η)) :=
    hle (Submodule.subset_span ⟨b, s, hs, rfl⟩)
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hmem
  have hcoef := congrArg (fun a => (toA x η a).coeff ((0 : ℤ), (b : ℤ))) hc
  simp only [AddEquiv.apply_symm_apply, map_sum, toA_smulSy, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, coeff_single, Finsupp.single_eq_same] at hcoef
  rw [← hcoef]
  refine Submodule.sum_mem _ fun γ hγ => ?_
  have h1 : toA x η γ = single ((0 : ℤ), ((bT ⟨γ, hγ⟩ : ℕ) : ℤ)) (sT ⟨γ, hγ⟩) := by
    have := congrArg (toA x η) (hγT ⟨γ, hγ⟩)
    rwa [AddEquiv.apply_symm_apply] at this
  rw [h1, coeff_psi_mul_single]
  refine Submodule.sum_mem _ fun d _ => ?_
  split_ifs with hdb
  · refine Submodule.subset_span ⟨e ⟨γ, hγ⟩, homogeneousComponent d (c γ), d,
      homogeneousComponent_isHomogeneous _ _, ?_, ?_⟩
    · simp only [Equiv.symm_apply_apply]
      exact hdb
    · simp only [Equiv.symm_apply_apply]
  · exact zero_mem _

end GroundTheory.Heights₂.Heights.Kleiman
