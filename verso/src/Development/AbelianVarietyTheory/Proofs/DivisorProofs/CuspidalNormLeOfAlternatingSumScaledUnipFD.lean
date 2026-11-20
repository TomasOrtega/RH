import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff
open scoped NumberField.AdeleRing

namespace GlobalTheory.CuspTail

/- English proof (translation)
Introduce `E _ _ _ a r hr hra φ hinv hcusp hφ M hM x m B hB`. Use `haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm`. Use `haveI : Countable (ratN E a r) := by`. Establish `: ((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)) = Set.range (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r))` using `AddMonoidHom.coe_range _`. Express the relevant statement in the definitionally equal form `Countable (((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)))`.

Rewrite using `[this]`. Conclude with `(Set.countable_range _).to_subtype`. Use `set D := GroundTheory.Automorphic.scaledUnipFD E a r M with hDdef`. Use `set ν := GroundTheory.Automorphic.AutomorphicForm.unipMeasure E a r`. Establish `hD : IsAddFundamentalDomain (ratN E a r) D ν` using `GroundTheory.Automorphic.isAddFundamentalDomain_scaledUnipFD hM`.

Establish `hD1 : ν D = 1` using `GroundTheory.Automorphic.unipMeasure_scaledUnipFD hM`. Use `set H : (BlockIx a r → Ad E) → ℂ := fun s => φ (unip s * x) with hH`. Establish `hunip : (unip : (BlockIx a r → Ad E) → GA E a) = (GroundTheory.Automorphic.AutomorphicForm.unipGL (n` using `a) (r := r) (R := Ad E)) :=`. Use function extensionality and compare the values at `fun X => Units.ext rfl`. Establish `hcont : Continuous H`.

Use `hφ.comp (Continuous.mul ?_ continuous_const)` and prove the remaining obligations. Rewrite using `[hunip]`. Conclude with `GroundTheory.Automorphic.AutomorphicForm.continuous_unipGL`. Establish `hper : ∀ ξ ∈ ratN E a r, ∀ s, H (ξ + s) = H s`. Introduce and unpack `_ ⟨e, rfl⟩ s`.

Express the relevant statement in the definitionally equal form `φ (unip ((fun p => algebraMap E (Ad E) (e p)) + s) * x) = φ (unip s * x)`. Rewrite using `[unip_add, unip_algebraMap, mul_assoc, hinv]`. Take `⟨C, hC, hDC⟩` from `GroundTheory.Automorphic.CuspidalSpectrum.exists_isCompact_superset_scaledUnipFD (K := E) (n := a) r hM`. Establish `hint : ∀ t, IntegrableOn (fun y => H (t + y)) D ν` using `fun t => ((hcont.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact hC).mono_set hDC`. Establish `hmean : ∫ y in D, H y ∂ν = 0` using `hcusp r hr hra ν D inferInstance hD x`.

Establish `hB' : ∀ y : Fin m → BlockIx a r → Ad E, (∀ i, y i ∈ D) → ‖GroundTheory.Automorphic.altSum m H y 0‖ ≤ B`. Introduce `y hy`. Rewrite using `[GroundTheory.Automorphic.altSum_eq_sum]`. Simplify `hB y hy` using `[H, zero_add, zsmul_eq_mul]`. Establish `h0` using `GroundTheory.Automorphic.norm_le_of_forall_altSum_le hD hD1 m H hper hint hmean B hB'`.

Establish `hu0 : (unip (0 : BlockIx a r → Ad E) : GA E a) = 1`. Establish `h` using `unip_add (0 : BlockIx a r → Ad E) 0`. Rewrite `h` using `[add_zero]`. Simplify using `using h`. Establish `hH0 : H 0 = φ x` using `by simp only [H, hu0, one_mul]`.

Rewrite `h0` using `[hH0]`. Then use the resulting hypothesis.
-/
theorem norm_le_of_altSum_scaledUnipFD : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ), 0 < r → r < a →
    ∀ φ : GA E a → ℂ, (∀ γ g, φ (ratGL E a γ * g) = φ g) → IsCuspidal φ → Continuous φ →
    ∀ M : ℕ, 0 < M → ∀ (x : GA E a) (m : ℕ) (B : ℝ),
      (∀ y : Fin m → BlockIx a r → Ad E, (∀ i, y i ∈ GroundTheory.Automorphic.scaledUnipFD E a r M) →
        ‖∑ ε : Fin m → Bool, (GroundTheory.Automorphic.altSign ε : ℂ) * φ (unip (GroundTheory.Automorphic.altPoint y ε) * x)‖ ≤ B) →
      ‖φ x‖ ≤ B := by
  intro E _ _ _ a r hr hra φ hinv hcusp hφ M hM x m B hB
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (ratN E a r) := by
    have : ((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)) = Set.range
        (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) := AddMonoidHom.coe_range _
    change Countable (((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)))
    rw [this]; exact (Set.countable_range _).to_subtype
  set D := GroundTheory.Automorphic.scaledUnipFD E a r M with hDdef
  set ν := GroundTheory.Automorphic.AutomorphicForm.unipMeasure E a r
  have hD : IsAddFundamentalDomain (ratN E a r) D ν :=
    GroundTheory.Automorphic.isAddFundamentalDomain_scaledUnipFD hM
  have hD1 : ν D = 1 := GroundTheory.Automorphic.unipMeasure_scaledUnipFD hM
  set H : (BlockIx a r → Ad E) → ℂ := fun s => φ (unip s * x) with hH
  have hunip : (unip : (BlockIx a r → Ad E) → GA E a) =
      (GroundTheory.Automorphic.AutomorphicForm.unipGL (n := a) (r := r) (R := Ad E)) :=
    funext fun X => Units.ext rfl
  have hcont : Continuous H := by
    refine hφ.comp (Continuous.mul ?_ continuous_const)
    rw [hunip]
    exact GroundTheory.Automorphic.AutomorphicForm.continuous_unipGL
  have hper : ∀ ξ ∈ ratN E a r, ∀ s, H (ξ + s) = H s := by
    rintro _ ⟨e, rfl⟩ s
    change φ (unip ((fun p => algebraMap E (Ad E) (e p)) + s) * x) = φ (unip s * x)
    rw [unip_add, unip_algebraMap, mul_assoc, hinv]
  obtain ⟨C, hC, hDC⟩ :=
    GroundTheory.Automorphic.CuspidalSpectrum.exists_isCompact_superset_scaledUnipFD (K := E) (n := a) r hM
  have hint : ∀ t, IntegrableOn (fun y => H (t + y)) D ν :=
    fun t => ((hcont.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact
      hC).mono_set hDC
  have hmean : ∫ y in D, H y ∂ν = 0 :=
    hcusp r hr hra ν D inferInstance hD x
  have hB' : ∀ y : Fin m → BlockIx a r → Ad E, (∀ i, y i ∈ D) →
      ‖GroundTheory.Automorphic.altSum m H y 0‖ ≤ B := by
    intro y hy
    rw [GroundTheory.Automorphic.altSum_eq_sum]
    simpa [H, zero_add, zsmul_eq_mul] using hB y hy
  have h0 := GroundTheory.Automorphic.norm_le_of_forall_altSum_le hD hD1 m H hper hint hmean B hB'
  have hu0 : (unip (0 : BlockIx a r → Ad E) : GA E a) = 1 := by
    have h := unip_add (0 : BlockIx a r → Ad E) 0
    rw [add_zero] at h
    simpa using h
  have hH0 : H 0 = φ x := by simp only [H, hu0, one_mul]
  rwa [hH0] at h0

end GlobalTheory.CuspTail
