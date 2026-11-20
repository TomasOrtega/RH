import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

/- English proof (translation)
Introduce `k Ω _ _ _ _ _ l _ O _ _ _ _ _ e ψ U`. Use `⟨fun U' h => ?_, fun h => ?_⟩` and prove the remaining obligations. Establish `hle : H0U (rho l e ψ) U ≤ H0U (rho l e ψ) U'` using `fun m hm => (mem_riemannRochSpace_iff_regularAt_everywhere _ _).2 fun g => (mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 hm ⟨g.1, h g.2⟩`. Conclude with `Module.length_le_of_injective _ (Submodule.inclusion_injective hle)`. Take `⟨-, -, -, -, -, h0', -, hval, -⟩` from `dvrFacts l O`.

Distinguish the cases in `ht : KStar.TotallyRealRoots.nu l (U.map (cycZ k Ω l)) e = ⊤`. Rewrite using `[ht, ENat.top_mul h0']`. Conclude with `le_top`. Take `⟨n, hn⟩` from `ENat.ne_top_iff_exists.mp ht`. Establish `hle : H0U (rho l e ψ) U ≤ LinearMap.ker (((l : O) ^ n) • (LinearMap.id : QO l O →ₗ[O] QO l O))`.

Introduce `m hm`. Establish `h1 : m ∈ KStar.TotallyRealRoots.twistInvOver l O (QO l O) (U.map (cycZ k Ω l)) e`. Rewrite using `[KStar.TotallyRealRoots.mem_twistInvOver]`. Introduce and unpack `u ⟨g, hg, rfl⟩`. Establish `h2 : rho l e ψ g⁻¹ m = m` using `(mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 hm ⟨g⁻¹, U.inv_mem hg⟩`.

Establish `h3 : ψ g = 1` using `h hg`. Rewrite `h2` using `[rho_eq, scalRep_apply, MonoidHom.inv_apply, map_inv, inv_inv, Psi, MonoidHom.mul_apply, h3, mul_one, zpow_natCast, MonoidHom.pow_apply, Units.val_pow_eq_pow_val]`. Conclude with `h2`. Rewrite `h1` using `[KStar.TotallyRealRoots.twistInvOver_eq_torsionBy _ hn.symm, Submodule.mem_torsionBy_iff]`. Conclude with `h1`.

Use `(Module.length_le_of_injective _ (Submodule.inclusion_injective hle)).trans ?_` and prove the remaining obligations. Rewrite using `[(qoFacts l O).2.2.2, IsDiscreteValuationRing.addVal_pow, nsmul_eq_mul, ← hn, hval]`.
-/
theorem UpperTheory.V.Chr.h0Nu :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (e : ℕ) (ψ : G k Ω →* Oˣ) (U : Subgroup (G k Ω)),
          (∀ U' : Subgroup (G k Ω), U' ≤ U → h0 l e ψ U ≤ h0 l e ψ U') ∧
          (U ≤ ψ.ker → h0 l e ψ U ≤ KStar.TotallyRealRoots.nu l (U.map (cycZ k Ω l)) e * eO l O) := by
  intro k Ω _ _ _ _ _ l _ O _ _ _ _ _ e ψ U
  refine ⟨fun U' h => ?_, fun h => ?_⟩
  · have hle : H0U (rho l e ψ) U ≤ H0U (rho l e ψ) U' := fun m hm =>
      (mem_riemannRochSpace_iff_regularAt_everywhere _ _).2 fun g => (mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 hm ⟨g.1, h g.2⟩
    exact Module.length_le_of_injective _ (Submodule.inclusion_injective hle)
  · obtain ⟨-, -, -, -, -, h0', -, hval, -⟩ := dvrFacts l O
    by_cases ht : KStar.TotallyRealRoots.nu l (U.map (cycZ k Ω l)) e = ⊤
    · rw [ht, ENat.top_mul h0']
      exact le_top
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp ht
    have hle : H0U (rho l e ψ) U ≤
        LinearMap.ker (((l : O) ^ n) • (LinearMap.id : QO l O →ₗ[O] QO l O)) := by
      intro m hm
      have h1 : m ∈ KStar.TotallyRealRoots.twistInvOver l O (QO l O) (U.map (cycZ k Ω l)) e := by
        rw [KStar.TotallyRealRoots.mem_twistInvOver]
        rintro u ⟨g, hg, rfl⟩
        have h2 : rho l e ψ g⁻¹ m = m := (mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 hm ⟨g⁻¹, U.inv_mem hg⟩
        have h3 : ψ g = 1 := h hg
        rw [rho_eq, scalRep_apply, MonoidHom.inv_apply, map_inv, inv_inv, Psi, MonoidHom.mul_apply, h3, mul_one,
          zpow_natCast, MonoidHom.pow_apply, Units.val_pow_eq_pow_val] at h2
        exact h2
      rw [KStar.TotallyRealRoots.twistInvOver_eq_torsionBy _ hn.symm, Submodule.mem_torsionBy_iff] at h1
      exact h1
    refine (Module.length_le_of_injective _ (Submodule.inclusion_injective hle)).trans ?_
    rw [(qoFacts l O).2.2.2, IsDiscreteValuationRing.addVal_pow, nsmul_eq_mul, ← hn, hval]
