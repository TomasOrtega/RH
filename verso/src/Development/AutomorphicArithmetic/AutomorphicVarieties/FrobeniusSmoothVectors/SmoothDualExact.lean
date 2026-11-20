import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrSMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IrrOfConn

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Introduce `l _ O _ _ _ _ F C₀ n hF hn S p hp`. Take `⟨h1, h2⟩` from `hp`. Set `ξ : S.A →+* p.asIdeal.ResidueField` to `algebraMap S.A p.asIdeal.ResidueField`. Establish `hk : RingHom.ker ξ = p.asIdeal` using `Ideal.ker_algebraMap_residueField _`. Establish `hz : ∀ c ∈ maximalIdeal O, ξ.comp (algebraMap O S.A) c = 0`.

Introduce `c hc`. Establish `hm : algebraMap O S.B c ∈ S.mB` using `by show algebraMap O S.R c ∈ maximalIdeal S.R`. Conclude with `map_nonunit (algebraMap O S.R) c hc`. Establish `: algebraMap O S.A c ∈ p.asIdeal` using `h1 hm`. Rewrite `this` using `[← hk]`.

Conclude with `this`. Set `φ : ResidueField O →+* p.asIdeal.ResidueField` to `Ideal.Quotient.lift (maximalIdeal O) (ξ.comp (algebraMap O S.A)) hz`. Use `⟨p.asIdeal.ResidueField, inferInstance, φ.toAlgebra, ξ, hk, ?_, ?_⟩` and prove the remaining obligations. Use `letI := φ.toAlgebra`. Use `⟨?_, fun c => rfl⟩` and prove the remaining obligations.

Rewrite using `[hk]`. Conclude with `Ideal.map_le_iff_le_comap.2 h1`. Break down `(types hF hn S _ ξ).2 (by rw [hk]; exact h1) with h | h` into its components or cases. Rewrite `h` using `[hk]`. Conclude with `absurd h h2`.

Conclude with `h`.
-/
theorem UpperTheory.smoothDual_exact :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (S : Space O F n), ∀ p ∈ S.BB, ∃ (K : Type) (_ : Field K) (_ : Algebra (ResidueField O) K) (ξ : S.A →+* K), RingHom.ker ξ = p.asIdeal ∧ S.FPt ξ ∧ S.u.triM ≤ RingHom.ker ξ := by
  intro l _ O _ _ _ _ F C₀ n hF hn S p hp
  obtain ⟨h1, h2⟩ := hp
  let ξ : S.A →+* p.asIdeal.ResidueField := algebraMap S.A p.asIdeal.ResidueField
  have hk : RingHom.ker ξ = p.asIdeal := Ideal.ker_algebraMap_residueField _
  have hz : ∀ c ∈ maximalIdeal O, ξ.comp (algebraMap O S.A) c = 0 := by
    intro c hc
    have hm : algebraMap O S.B c ∈ S.mB := by
      show algebraMap O S.R c ∈ maximalIdeal S.R
      exact map_nonunit (algebraMap O S.R) c hc
    have : algebraMap O S.A c ∈ p.asIdeal := h1 hm
    rw [← hk] at this
    exact this
  let φ : ResidueField O →+* p.asIdeal.ResidueField :=
    Ideal.Quotient.lift (maximalIdeal O) (ξ.comp (algebraMap O S.A)) hz
  refine ⟨p.asIdeal.ResidueField, inferInstance, φ.toAlgebra, ξ, hk, ?_, ?_⟩
  · letI := φ.toAlgebra
    refine ⟨?_, fun c => rfl⟩
    rw [hk]
    exact Ideal.map_le_iff_le_comap.2 h1
  · rcases (types hF hn S _ ξ).2 (by rw [hk]; exact h1) with h | h
    · rw [hk] at h
      exact absurd h h2
    · exact h
