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
A detailed English derivation is pending.
-/
theorem emb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s :=
  (RingHom.injective_iff_ker_eq_bot _).2
    (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => by simpa using hn))

def extend (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (K := E) (emb_injective s)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem extend_comp (s : 𝓞 E →+* ℂ) : (extend s).comp (algebraMap (𝓞 E) E) = s :=
  RingHom.ext fun x => by rw [RingHom.comp_apply, extend, IsFractionRing.lift_algebraMap]

def chr (t : E →+* ℂ) : 𝓞 E →* ℂ := ((t.comp (algebraMap (𝓞 E) E) : 𝓞 E →+* ℂ) : 𝓞 E →* ℂ)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem chr_injective : Function.Injective (chr (E := E)) := fun t t' h =>
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => DFunLike.congr_fun h x)

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
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
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Check the elementary cases of the proposition. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
