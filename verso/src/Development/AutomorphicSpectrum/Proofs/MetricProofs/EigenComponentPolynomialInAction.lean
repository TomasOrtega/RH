import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.EigFormula

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
The claim follows from `(RingHom.injective_iff_ker_eq_bot _).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => by simpa using hn))`.
-/
theorem emb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s :=
  (RingHom.injective_iff_ker_eq_bot _).2
    (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => by simpa using hn))

def extend (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (K := E) (emb_injective s)

/- English proof (translation)
The claim follows from `RingHom.ext fun x => by rw [RingHom.comp_apply, extend, IsFractionRing.lift_algebraMap]`.
-/
theorem extend_comp (s : 𝓞 E →+* ℂ) : (extend s).comp (algebraMap (𝓞 E) E) = s :=
  RingHom.ext fun x => by rw [RingHom.comp_apply, extend, IsFractionRing.lift_algebraMap]

def chr (t : E →+* ℂ) : 𝓞 E →* ℂ := ((t.comp (algebraMap (𝓞 E) E) : 𝓞 E →+* ℂ) : 𝓞 E →* ℂ)

/- English proof (translation)
Introduce `t t' h` and use `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => DFunLike.congr_fun h x)`.
-/
theorem chr_injective : Function.Injective (chr (E := E)) := fun t t' h =>
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => DFunLike.congr_fun h x)

/- English proof (translation)
Assume the negation of the conclusion as `h`. Take `⟨φ, hφ0, hφ⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 h)`. Apply `hφ0` to reduce the goal to its premises. Establish `li` using `(linearIndependent_monoidHom (𝓞 E) ℂ).comp (chr (E := E)) chr_injective`. Establish `hc` using `Fintype.linearIndependent_iff.1 li (fun t => φ fun j => if t = j then 1 else 0) (by`.

Use function extensionality and compare the values at `a`. Establish `h0 : φ (fun t : E →+* ℂ => t (algebraMap (𝓞 E) E a)) = 0` using `hφ (Submodule.subset_span ⟨a, rfl⟩)`. Rewrite `h0` using `[LinearMap.pi_apply_eq_sum_univ φ]`. Simplify `h0)` using `[chr, Finset.sum_apply, mul_comm]`. Use `LinearMap.ext fun w => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.pi_apply_eq_sum_univ φ w]`. Simplify using `only [hc, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]`.
-/
theorem span_eq_top :
    Submodule.span ℂ (Set.range fun (a : 𝓞 E) (t : E →+* ℂ) => t (algebraMap (𝓞 E) E a)) = ⊤ := by
  classical
  by_contra h
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 h)
  apply hφ0
  have li := (linearIndependent_monoidHom (𝓞 E) ℂ).comp (chr (E := E)) chr_injective
  have hc := Fintype.linearIndependent_iff.1 li
    (fun t => φ fun j => if t = j then 1 else 0) (by
      funext a
      have h0 : φ (fun t : E →+* ℂ => t (algebraMap (𝓞 E) E a)) = 0 :=
        hφ (Submodule.subset_span ⟨a, rfl⟩)
      rw [LinearMap.pi_apply_eq_sum_univ φ] at h0
      simpa [chr, Finset.sum_apply, mul_comm] using h0)
  refine LinearMap.ext fun w => ?_
  rw [LinearMap.pi_apply_eq_sum_univ φ w]
  simp only [hc, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]

open Classical in

/- English proof (translation)
Establish `hmem : (fun t : E →+* ℂ => if t = extend s then (1 : ℂ) else 0) ∈ Submodule.span ℂ (Set.range fun (a : 𝓞 E) (t : E →+* ℂ) => t (algebraMap (𝓞 E) E a))`. Rewrite using `[span_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨f, hf⟩` from `Finsupp.mem_span_range_iff_exists_finsupp.1 hmem`. Use `⟨f.support.card, fun i => (f.support.equivFin.symm i).1, fun i => f (f.support.equivFin.symm i).1, fun t => ?_⟩` and prove the remaining obligations.

Establish `ht` using `congrFun hf t`. Rewrite `ht` using `[Finsupp.sum, Finset.sum_apply]`. Rewrite using `[← ht]`. Use `(Equiv.sum_comp f.support.equivFin.symm (fun x : f.support => f x.1 * t (algebraMap (𝓞 E) E x.1))).trans ?_` and prove the remaining obligations. Conclude with `Finset.sum_coe_sort f.support (fun x => f x * t (algebraMap (𝓞 E) E x))`.
-/
theorem exists_coeffs (s : 𝓞 E →+* ℂ) : ∃ (N : ℕ) (a : Fin N → 𝓞 E) (c : Fin N → ℂ),
    ∀ t : E →+* ℂ, ∑ i, c i * t (algebraMap (𝓞 E) E (a i)) = if t = extend s then 1 else 0 := by
  have hmem : (fun t : E →+* ℂ => if t = extend s then (1 : ℂ) else 0) ∈
      Submodule.span ℂ (Set.range fun (a : 𝓞 E) (t : E →+* ℂ) => t (algebraMap (𝓞 E) E a)) := by
    rw [span_eq_top]; trivial
  obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
  refine ⟨f.support.card, fun i => (f.support.equivFin.symm i).1,
    fun i => f (f.support.equivFin.symm i).1, fun t => ?_⟩
  have ht := congrFun hf t
  rw [Finsupp.sum, Finset.sum_apply] at ht
  rw [← ht]
  refine (Equiv.sum_comp f.support.equivFin.symm
    (fun x : f.support => f x.1 * t (algebraMap (𝓞 E) E x.1))).trans ?_
  exact Finset.sum_coe_sort f.support (fun x => f x * t (algebraMap (𝓞 E) E x))

/- English proof (translation)
Introduce `E _ _ _ s`. Take `⟨N, a, c, h⟩` from `exists_coeffs s`. Use `⟨N, a, c, ?_⟩` and prove the remaining obligations. Introduce `g Λ _ _ R z`. Take `⟨-, -, hs, hsum, -⟩` from `GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R`.

Establish `hB : ∀ (b : 𝓞 E) (t : E →+* ℂ), R.B b (eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z) = t (algebraMap (𝓞 E) E b) • eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z`. Introduce `b t`. Establish `hm` using `(hs (t.comp (algebraMap (𝓞 E) E))).1 z`. Simplify using `only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker] at hm`. Use `hm b` as an intermediate fact.

Simplify `this` using `[sub_eq_zero]`. Establish `hz : ∀ b : 𝓞 E, R.B b z = ∑ t : E →+* ℂ, t (algebraMap (𝓞 E) E b) • eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z`. Introduce `b`. Use `conv_lhs => rw [← hsum z]`. Rewrite using `[map_sum]`.

Conclude with `Finset.sum_congr rfl fun t _ => hB b t`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[extend_comp]`. Use `_ = ∑ t : E →+* ℂ, (∑ i, c i * t (algebraMap (𝓞 E) E (a i))) • eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by`. Simplify using `only [h]`.

Use `_ = ∑ i, c i • ∑ t : E →+* ℂ, t (algebraMap (𝓞 E) E (a i)) • eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by`. Simplify using `only [Finset.sum_smul, Finset.smul_sum, mul_smul]`. Conclude with `Finset.sum_comm`. Use `_ = ∑ i, c i • R.B (a i) z := by simp only [hz]`.
-/
theorem eigComp_eq_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (s : 𝓞 E →+* ℂ),
    ∃ (N : ℕ) (a : Fin N → 𝓞 E) (c : Fin N → ℂ), ∀ (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ]
      (R : RiemLat E g Λ) (z : Fin g → ℂ), eigComp R.B s z = ∑ i, c i • R.B (a i) z := by
  classical
  intro E _ _ _ s
  obtain ⟨N, a, c, h⟩ := exists_coeffs s
  refine ⟨N, a, c, ?_⟩
  intro g Λ _ _ R z
  obtain ⟨-, -, hs, hsum, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  have hB : ∀ (b : 𝓞 E) (t : E →+* ℂ), R.B b (eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z) =
      t (algebraMap (𝓞 E) E b) • eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
    intro b t
    have hm := (hs (t.comp (algebraMap (𝓞 E) E))).1 z
    simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker] at hm
    have := hm b
    simpa [sub_eq_zero] using this
  have hz : ∀ b : 𝓞 E, R.B b z = ∑ t : E →+* ℂ,
      t (algebraMap (𝓞 E) E b) • eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
    intro b
    conv_lhs => rw [← hsum z]
    rw [map_sum]
    exact Finset.sum_congr rfl fun t _ => hB b t
  calc eigComp R.B s z
      = ∑ t : E →+* ℂ, (if t = extend s then (1 : ℂ) else 0) •
          eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
        simp [extend_comp]
    _ = ∑ t : E →+* ℂ, (∑ i, c i * t (algebraMap (𝓞 E) E (a i))) •
          eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
        simp only [h]
    _ = ∑ i, c i • ∑ t : E →+* ℂ, t (algebraMap (𝓞 E) E (a i)) •
          eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
        simp only [Finset.sum_smul, Finset.smul_sum, mul_smul]
        exact Finset.sum_comm
    _ = ∑ i, c i • R.B (a i) z := by simp only [hz]

end GlobalTheory.CompanionTheory.Ar.Cusp.EigFormula
