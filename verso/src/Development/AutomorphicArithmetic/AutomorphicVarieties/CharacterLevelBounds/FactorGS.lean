import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

/- English proof (translation)
Introduce `k Ω _ _ _ _ _ l _ O _ _ _ _ _ N _ e ψ hker S hS`. Establish `hψopen : IsOpen (ψ.ker : Set (G k Ω))` using `Subgroup.isOpen_mono hker (clsFacts k Ω N).1`. Establish `hcyc : IsClosed ((cycZ k Ω l).ker : Set (G k Ω))`. Rewrite using `[MonoidHom.coe_ker]`. Conclude with `isClosed_singleton.preimage (contTw k Ω l).1`.

Establish `hNS : NS Ω S ≤ ψ.ker ⊓ (cycZ k Ω l).ker`. Unfold `NS`. Use `Subgroup.topologicalClosure_minimal _ ?_ ((Subgroup.isClosed_of_isOpen _ hψopen).inter hcyc)` and prove the remaining obligations. Use `Subgroup.normalClosure_le_normal ?_` and prove the remaining obligations. Introduce `σ hσ`.

Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq] at hσ`. Take `⟨v, hv, A, hA, hσ⟩` from `hσ`. Establish `hvS : v ∉ Above k (l * N)`. Rewrite using `[← hS]`. Conclude with `hv`.

Establish `hmem : ∀ m : ℕ, m ∣ l * N → ¬ A.valuation (m : Ω) < 1`. Introduce `m hm hlt`. Apply `hvS` to reduce the goal to its premises. Establish `hx` using `(hA (m : 𝓞 k)).1 (by simpa using hlt)`. Take `⟨c, hc⟩` from `hm`.

Use `show ((l * N : ℕ) : 𝓞 k) ∈ v.asIdeal`. Rewrite using `[hc, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ hx`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `hker ((clsFacts k Ω N).2.2.2.2 A (hmem N (dvd_mul_left N l)) hσ)`.

Conclude with `(places k Ω l A).2.2.2 (hmem l (dvd_mul_right l N)) hσ`. Establish `hP : NS Ω S ≤ (Psi l e ψ)⁻¹.ker`. Introduce `σ hσ`. Establish `h1 : ψ σ = 1` using `(hNS hσ).1`. Establish `h2 : cycZ k Ω l σ = 1` using `(hNS hσ).2`.

Rewrite using `[MonoidHom.mem_ker]`. Unfold `Psi chiO`. Simplify using `[h1, h2]`. Use `⟨QuotientGroup.lift (NS Ω S) (Psi l e ψ)⁻¹ hP, MonoidHom.ext fun σ => rfl, ?_⟩` and prove the remaining obligations. Establish `heq : (Psi l e ψ)⁻¹ = ψ⁻¹ * chiO k Ω l O ^ (-(e : ℤ))`.

Unfold `Psi`. Rewrite using `[mul_inv, mul_comm, zpow_neg]`. Establish `hopen : IsOpen ((ψ⁻¹).ker : Set (G k Ω))`. Use `hψopen using 2` and compare the differences between its conclusion and the goal. Use extensionality with `σ`.

Simplify using the standard rewrite rules. Establish `hG` using `(contTw k Ω l).2.2 O ψ⁻¹ (-(e : ℤ)) hopen`. Rewrite `hG` using `[← heq]`. Unfold `ReciprocityTheory.Gal.ContAction at hG ⊢`. Rewrite using `[← ((QuotientGroup.isOpenQuotientMap_mk (N := NS Ω S)).prodMap (IsOpenQuotientMap.id (X := QO l O))).continuous_comp_iff]`.

Conclude with `hG`.
-/
theorem UpperTheory.V.Chr.factorGS :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (N : ℕ) [NeZero N] (e : ℕ) (ψ : G k Ω →* Oˣ), (cls k Ω N).ker ≤ ψ.ker →
          ∀ S : Set (HeightOneSpectrum (𝓞 k)), S = Above k (l * N) →
          ∃ θ : GS Ω S →* Oˣ, θ.comp (toGS Ω S) = (Psi l e ψ)⁻¹ ∧ ContAction (twist₂ l θ) := by
  intro k Ω _ _ _ _ _ l _ O _ _ _ _ _ N _ e ψ hker S hS
  have hψopen : IsOpen (ψ.ker : Set (G k Ω)) := Subgroup.isOpen_mono hker (clsFacts k Ω N).1
  have hcyc : IsClosed ((cycZ k Ω l).ker : Set (G k Ω)) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage (contTw k Ω l).1
  have hNS : NS Ω S ≤ ψ.ker ⊓ (cycZ k Ω l).ker := by
    unfold NS
    refine Subgroup.topologicalClosure_minimal _ ?_ ((Subgroup.isClosed_of_isOpen _ hψopen).inter hcyc)
    refine Subgroup.normalClosure_le_normal ?_
    intro σ hσ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hσ
    obtain ⟨v, hv, A, hA, hσ⟩ := hσ
    have hvS : v ∉ Above k (l * N) := by
      rw [← hS]
      exact hv
    have hmem : ∀ m : ℕ, m ∣ l * N → ¬ A.valuation (m : Ω) < 1 := by
      intro m hm hlt
      apply hvS
      have hx := (hA (m : 𝓞 k)).1 (by simpa using hlt)
      obtain ⟨c, hc⟩ := hm
      show ((l * N : ℕ) : 𝓞 k) ∈ v.asIdeal
      rw [hc, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ hx
    refine ⟨?_, ?_⟩
    · exact hker ((clsFacts k Ω N).2.2.2.2 A (hmem N (dvd_mul_left N l)) hσ)
    · exact (places k Ω l A).2.2.2 (hmem l (dvd_mul_right l N)) hσ
  have hP : NS Ω S ≤ (Psi l e ψ)⁻¹.ker := by
    intro σ hσ
    have h1 : ψ σ = 1 := (hNS hσ).1
    have h2 : cycZ k Ω l σ = 1 := (hNS hσ).2
    rw [MonoidHom.mem_ker]
    unfold Psi chiO
    simp [h1, h2]
  refine ⟨QuotientGroup.lift (NS Ω S) (Psi l e ψ)⁻¹ hP, MonoidHom.ext fun σ => rfl, ?_⟩
  have heq : (Psi l e ψ)⁻¹ = ψ⁻¹ * chiO k Ω l O ^ (-(e : ℤ)) := by
    unfold Psi
    rw [mul_inv, mul_comm, zpow_neg]
  have hopen : IsOpen ((ψ⁻¹).ker : Set (G k Ω)) := by
    convert hψopen using 2
    ext σ
    simp
  have hG := (contTw k Ω l).2.2 O ψ⁻¹ (-(e : ℤ)) hopen
  rw [← heq] at hG
  unfold ReciprocityTheory.Gal.ContAction at hG ⊢
  rw [← ((QuotientGroup.isOpenQuotientMap_mk (N := NS Ω S)).prodMap (IsOpenQuotientMap.id (X := QO l O))).continuous_comp_iff]
  exact hG
