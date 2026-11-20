import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsAddConjTransposeEq
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NkCountLocF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SigmaCountPosBasis

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Take `⟨b, hbL, hb⟩` from `LocalSpans.exists_basis_locF hA₀ h𝔭`. Take `⟨H, hH, -⟩` from `LocF.exists_gram hA₀i b hbL`. Establish `hd'` using `LocF.aniso_of_totPosDef hd`. Establish `key : ∀ A : Submodule (𝓞 K) V, A = locF 𝔭 (integralBasisSpans.spanO b) → ∀ k : ℕ, eA h A 𝔭 + 1 ≤ k → ∀ X : Module.End (𝓞 K) (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)), (∀ x y x' y' : ↥A, Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) → Submodule.Quotient.mk y' = X ( …`. Introduce and unpack `_ rfl k hk X hX`.

Conclude with `HU.exists_isom_lift_basis hK hF hs hd' b hH h𝔭 (HU.isE_eA hK hF hd' b h𝔭) hk X hX`. Conclude with `key _ hb.symm k hk X hX`.
-/
theorem exists_isom_lift (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ k)
    (X : Module.End (𝓞 K) (↥(locF 𝔭 A₀) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 A₀))))
    (hX : ∀ x y x' y' : ↥(locF 𝔭 A₀), Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = X (Submodule.Quotient.mk y) →
      CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V))) :
    ∃ g ∈ autSub h (locF 𝔭 A₀), ∀ x x' : ↥(locF 𝔭 A₀), Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
      g x - x' ∈ ((extP K 𝔭) ^ (k - eA h (locF 𝔭 A₀) 𝔭) • (locF 𝔭 A₀) : Submodule (𝓞 K) V) := by
  obtain ⟨b, hbL, hb⟩ := LocalSpans.exists_basis_locF hA₀ h𝔭
  obtain ⟨H, hH, -⟩ := LocF.exists_gram hA₀i b hbL
  have hd' := LocF.aniso_of_totPosDef hd
  have key : ∀ A : Submodule (𝓞 K) V, A = locF 𝔭 (integralBasisSpans.spanO b) → ∀ k : ℕ, eA h A 𝔭 + 1 ≤ k →
      ∀ X : Module.End (𝓞 K) (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)),
      (∀ x y x' y' : ↥A, Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
        Submodule.Quotient.mk y' = X (Submodule.Quotient.mk y) →
        CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V))) →
      ∃ g ∈ autSub h A, ∀ x x' : ↥A, Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
        g x - x' ∈ ((extP K 𝔭) ^ (k - eA h A 𝔭) • A : Submodule (𝓞 K) V) := by
    rintro _ rfl k hk X hX
    exact HU.exists_isom_lift_basis hK hF hs hd' b hH h𝔭 (HU.isE_eA hK hF hd' b h𝔭) hk X hX
  exact key _ hb.symm k hk X hX

/- English proof (translation)
Take `⟨b, hbL, hb⟩` from `LocalSpans.exists_basis_locF hA₀ h𝔭`. Take `⟨H, hH, -⟩` from `LocF.exists_gram hA₀i b hbL`. Establish `hd'` using `LocF.aniso_of_totPosDef hd`. Establish `: Fact (IsFixF K F)` using `⟨hF⟩`. Rewrite `hj`, the goal using `[← hb]`.

Establish `h1` using `HU.sigmaCount_succ_basis hK hs hd' b hH h𝔭 (HU.isE_eA hK hF hd' b h𝔭) hj`. Rewrite `h1` using `[Fintype.card_fin]`. Then use the resulting hypothesis.
-/
theorem sigmaCount_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {j : ℕ} (hj : eA h (locF 𝔭 A₀) 𝔭 ≤ j) :
    sigmaCount h (locF 𝔭 A₀) 𝔭 (j + 1) = Ideal.absNorm 𝔭 ^ (finrank K V ^ 2) * sigmaCount h (locF 𝔭 A₀) 𝔭 j := by
  obtain ⟨b, hbL, hb⟩ := LocalSpans.exists_basis_locF hA₀ h𝔭
  obtain ⟨H, hH, -⟩ := LocF.exists_gram hA₀i b hbL
  have hd' := LocF.aniso_of_totPosDef hd
  have : Fact (IsFixF K F) := ⟨hF⟩
  rw [← hb] at hj ⊢
  have h1 := HU.sigmaCount_succ_basis hK hs hd' b hH h𝔭 (HU.isE_eA hK hF hd' b h𝔭) hj
  rwa [Fintype.card_fin] at h1

/- English proof (translation)
Take `⟨b, hbL, hb⟩` from `LocalSpans.exists_basis_locF hA₀ h𝔭`. Take `⟨H, hH, -⟩` from `LocF.exists_gram hA₀i b hbL`. Establish `hd'` using `LocF.aniso_of_totPosDef hd`. Establish `: Fact (IsFixF K F)` using `⟨hF⟩`. Rewrite `hk`, the goal using `[← hb]`.

Establish `he` using `HU.isE_eA hK hF hd' b h𝔭`. Generalize the expression as in `eA h (locF 𝔭 (Submodule.span (𝓞 K) (Set.range b))) 𝔭 = e at hk he ⊢`. Take `⟨j, rfl⟩ : ∃ j, k = j + e` from `⟨k - e, by omega⟩`. Rewrite using `[Nat.add_sub_cancel]`. Conclude with `HU.akCount_eq_mul_basis hK hs hd' b hH h𝔭 he (by omega) (by omega)`.
-/
theorem akCount_eq_redCount_mul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : 2 * eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ k) :
    akCount h (locF 𝔭 A₀) 𝔭 k =
      redCount h (locF 𝔭 A₀) 𝔭 (k - eA h (locF 𝔭 A₀) 𝔭) * sigmaCount h (locF 𝔭 A₀) 𝔭 (eA h (locF 𝔭 A₀) 𝔭) := by
  obtain ⟨b, hbL, hb⟩ := LocalSpans.exists_basis_locF hA₀ h𝔭
  obtain ⟨H, hH, -⟩ := LocF.exists_gram hA₀i b hbL
  have hd' := LocF.aniso_of_totPosDef hd
  have : Fact (IsFixF K F) := ⟨hF⟩
  rw [← hb] at hk ⊢
  have he := HU.isE_eA hK hF hd' b h𝔭
  generalize eA h (locF 𝔭 (Submodule.span (𝓞 K) (Set.range b))) 𝔭 = e at hk he ⊢
  obtain ⟨j, rfl⟩ : ∃ j, k = j + e := ⟨k - e, by omega⟩
  rw [Nat.add_sub_cancel]
  exact HU.akCount_eq_mul_basis hK hs hd' b hH h𝔭 he (by omega) (by omega)

/- English proof (translation)
Take `⟨b, hbL, hb⟩` from `LocalSpans.exists_basis_locF hA₀ h𝔭`. Take `⟨H, hH, -⟩` from `LocF.exists_gram hA₀i b hbL`. Establish `hd'` using `LocF.aniso_of_totPosDef hd`. Establish `: Fact (IsFixF K F)` using `⟨hF⟩`. Rewrite `hj`, the goal using `[← hb]`.

Establish `he` using `HU.isE_eA hK hF hd' b h𝔭`. Generalize the expression as in `eA h (locF 𝔭 (Submodule.span (𝓞 K) (Set.range b))) 𝔭 = e at hj he ⊢`. Establish `h1` using `HU.akCount_eq_mul_basis hK hs hd' b hH h𝔭 he (by omega : e ≤ j + 1) (by omega)`. Establish `h2` using `HU.akCount_eq_mul_basis hK hs hd' b hH h𝔭 (he.mono (Nat.le_succ e)) (by omega : e + 1 ≤ j) (by omega)`. Establish `h3` using `HU.sigmaCount_succ_basis hK hs hd' b hH h𝔭 he (le_refl e)`.

Establish `h4` using `HU.sigmaCount_pos_basis h b hH h𝔭 e`. Rewrite `h3` using `[Fintype.card_fin]`. Rewrite `h1` using `[show j + 1 + e = j + (e + 1) by omega, h2, h3]`. Apply `Nat.eq_of_mul_eq_mul_right h4` to reduce the goal to its premises. Rewrite using `[← h1]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem redCount_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {j : ℕ} (hj : eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ j) :
    redCount h (locF 𝔭 A₀) 𝔭 (j + 1) = Ideal.absNorm 𝔭 ^ (finrank K V ^ 2) * redCount h (locF 𝔭 A₀) 𝔭 j := by
  obtain ⟨b, hbL, hb⟩ := LocalSpans.exists_basis_locF hA₀ h𝔭
  obtain ⟨H, hH, -⟩ := LocF.exists_gram hA₀i b hbL
  have hd' := LocF.aniso_of_totPosDef hd
  have : Fact (IsFixF K F) := ⟨hF⟩
  rw [← hb] at hj ⊢
  have he := HU.isE_eA hK hF hd' b h𝔭
  generalize eA h (locF 𝔭 (Submodule.span (𝓞 K) (Set.range b))) 𝔭 = e at hj he ⊢
  have h1 := HU.akCount_eq_mul_basis hK hs hd' b hH h𝔭 he (by omega : e ≤ j + 1) (by omega)
  have h2 := HU.akCount_eq_mul_basis hK hs hd' b hH h𝔭 (he.mono (Nat.le_succ e)) (by omega : e + 1 ≤ j)
    (by omega)
  have h3 := HU.sigmaCount_succ_basis hK hs hd' b hH h𝔭 he (le_refl e)
  have h4 := HU.sigmaCount_pos_basis h b hH h𝔭 e
  rw [Fintype.card_fin] at h3
  rw [show j + 1 + e = j + (e + 1) by omega, h2, h3] at h1
  apply Nat.eq_of_mul_eq_mul_right h4
  rw [← h1]
  ring

end Formalism.HermitianLattices.Ext.L3
