import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BoxDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

/- English proof (translation)
Establish `h` using `hA ((l : ℕ) : 𝓞 ℚ)`. Simplify using `using h`.
-/
private theorem valuation_natCast_lt_one_iff_mem_asIdeal {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ)
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)) (hA : IsPlaceOver A v) :
    A.valuation (l : Ω) < 1 ↔ ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  have h := hA ((l : ℕ) : 𝓞 ℚ)
  simpa using h

/- English proof (translation)
Introduce `Ω _ _ _ l _ S A v₀ hS hA hv₀ H _ hH M _ hM`. Establish `hker : (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).ker = NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))`. Simplify using `[toGS, QuotientGroup.ker_mk']`. Establish `hin : ∀ (B : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 ℚ)), w ∉ (S : Set (HeightOneSpectrum (𝓞 ℚ))) → IsPlaceOver B w → (Ine (F` using `ℚ) B : Set (G ℚ Ω)) ⊆ NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) := by`. Introduce `B w hw hB g hg`.

Apply `Subgroup.le_topologicalClosure` to reduce the goal to its premises. Apply `Subgroup.subset_normalClosure` to reduce the goal to its premises. Simplify using `only [Set.mem_iUnion]`. Conclude with `⟨w, hw, B, hB, hg⟩`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Prove the components needed by the constructor for the conclusion. Rewrite using `[hker]`. Apply `Subgroup.topologicalClosure_minimal _ _ hM` to reduce the goal to its premises. Apply `Subgroup.normalClosure_le_normal` to reduce the goal to its premises.

Introduce `g hg`. Simplify using `only [Set.mem_iUnion] at hg`. Take `⟨w, hw, B, hB, hgB⟩` from `hg`. Establish `hgI : g ∈ Ine (F` using `ℚ) B := hgB`. Apply `h g` to reduce the goal to its premises.

Use `⟨B, ?_, hgI, ?_⟩` and prove the remaining obligations. Rewrite using `[valuation_natCast_lt_one_iff_mem_asIdeal l B w hB]`. Introduce `hl`. Conclude with `hw (by simpa using hS w hl)`. Apply `hH` to reduce the goal to its premises.

Rewrite using `[hker]`. Conclude with `hin B w hw hB hgI`. Introduce `v hv g hg`. Rewrite `hg` using `[Subgroup.mem_inf]`. Apply `h g` to reduce the goal to its premises.

Use `⟨A v, ?_, hg.1, hg.2⟩` and prove the remaining obligations. Rewrite using `[valuation_natCast_lt_one_iff_mem_asIdeal l (A v) v.1 (hA v), hv₀]`. Conclude with `hv`. Introduce and unpack `⟨h1, h2⟩ g ⟨B, hBl, hgB, hgH⟩`. Distinguish the cases in `hBt : B = ⊤`.

Substitute `hBt` using the available equality. Rewrite `hgB` using `[(Kum.placeDict ℚ Ω).1]`. Rewrite `hgB` using `[Subgroup.mem_bot]`. Substitute `hgB` using the available equality. Conclude with `M.one_mem`.

Take `⟨w, hw⟩` from `(Kum.placeDict ℚ Ω).2.1 B hBt`. Distinguish the cases in `hwS : w ∈ (S : Set (HeightOneSpectrum (𝓞 ℚ)))`. Set `u : S` to `⟨w, hwS⟩`. Establish `hu0 : u ≠ v₀`. Introduce `hu`.

Rewrite `hu` using `[← hv₀ u]`. Conclude with `hBl ((valuation_natCast_lt_one_iff_mem_asIdeal l B w hw).2 hu)`. Take `⟨σ, hσ⟩` from `exists_smul_eq_of_isPlaceOver (hA u) hw`. Rewrite `hgB` using `[← hσ]`. Establish `hc : σ⁻¹ * g * σ ∈ Ine (F` using `ℚ) (A u) := ((ML.placeBasic Ω).2.2.2.2.2.2.2.2.2 (A u) σ).2.1 g |>.1 hgB`.

Establish `hcH : σ⁻¹ * g * σ ∈ H`. Use `‹H.Normal›.conj_mem g hgH σ⁻¹` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Establish `hcM` using `h2 u hu0 (Subgroup.mem_inf.2 ⟨hc, hcH⟩)`. Use `‹M.Normal›.conj_mem _ hcM σ` as an intermediate fact.

Simplify `this` using `[mul_assoc]`. Apply `h1` to reduce the goal to its premises. Rewrite using `[hker]`. Conclude with `hin B w hwS hw hgB`.
-/
theorem UpperTheory.inertia_le_normal_iff_ker_le_and_inertia_le :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (A : S → ValuationSubring Ω) (v₀ : S), ContainsAbove S l → (∀ v, IsPlaceOver (A v) v.1) →
          (∀ v : S, ((l : ℕ) : 𝓞 ℚ) ∈ v.1.asIdeal ↔ v = v₀) → ∀ (H : Subgroup (G ℚ Ω)) [H.Normal], (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).ker ≤ H →
          ∀ (M : Subgroup (G ℚ Ω)) [M.Normal], IsClosed (M : Set (G ℚ Ω)) →
          ((∀ g, (∃ A' : ValuationSubring Ω, ¬ A'.valuation (l : Ω) < 1 ∧ g ∈ Ine (F := ℚ) A' ∧ g ∈ H) → g ∈ M) ↔
            ((toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).ker ≤ M ∧ ∀ v : S, v ≠ v₀ → Ine (F := ℚ) (A v) ⊓ H ≤ M)) := by
  intro Ω _ _ _ l _ S A v₀ hS hA hv₀ H _ hH M _ hM
  have hker : (toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))).ker = NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) := by
    simp [toGS, QuotientGroup.ker_mk']
  have hin : ∀ (B : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 ℚ)), w ∉ (S : Set (HeightOneSpectrum (𝓞 ℚ))) →
      IsPlaceOver B w → (Ine (F := ℚ) B : Set (G ℚ Ω)) ⊆ NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) := by
    intro B w hw hB g hg
    apply Subgroup.le_topologicalClosure
    apply Subgroup.subset_normalClosure
    simp only [Set.mem_iUnion]
    exact ⟨w, hw, B, hB, hg⟩
  constructor
  · intro h
    constructor
    · rw [hker]
      apply Subgroup.topologicalClosure_minimal _ _ hM
      apply Subgroup.normalClosure_le_normal
      intro g hg
      simp only [Set.mem_iUnion] at hg
      obtain ⟨w, hw, B, hB, hgB⟩ := hg
      have hgI : g ∈ Ine (F := ℚ) B := hgB
      apply h g
      refine ⟨B, ?_, hgI, ?_⟩
      · rw [valuation_natCast_lt_one_iff_mem_asIdeal l B w hB]
        intro hl
        exact hw (by simpa using hS w hl)
      · apply hH
        rw [hker]
        exact hin B w hw hB hgI
    · intro v hv g hg
      rw [Subgroup.mem_inf] at hg
      apply h g
      refine ⟨A v, ?_, hg.1, hg.2⟩
      rw [valuation_natCast_lt_one_iff_mem_asIdeal l (A v) v.1 (hA v), hv₀]
      exact hv
  · rintro ⟨h1, h2⟩ g ⟨B, hBl, hgB, hgH⟩
    by_cases hBt : B = ⊤
    · subst hBt
      rw [(Kum.placeDict ℚ Ω).1] at hgB
      rw [Subgroup.mem_bot] at hgB
      subst hgB
      exact M.one_mem
    obtain ⟨w, hw⟩ := (Kum.placeDict ℚ Ω).2.1 B hBt
    by_cases hwS : w ∈ (S : Set (HeightOneSpectrum (𝓞 ℚ)))
    · let u : S := ⟨w, hwS⟩
      have hu0 : u ≠ v₀ := by
        intro hu
        rw [← hv₀ u] at hu
        exact hBl ((valuation_natCast_lt_one_iff_mem_asIdeal l B w hw).2 hu)
      obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (hA u) hw
      rw [← hσ] at hgB
      have hc : σ⁻¹ * g * σ ∈ Ine (F := ℚ) (A u) := ((ML.placeBasic Ω).2.2.2.2.2.2.2.2.2 (A u) σ).2.1 g |>.1 hgB
      have hcH : σ⁻¹ * g * σ ∈ H := by
        have := ‹H.Normal›.conj_mem g hgH σ⁻¹
        simpa [mul_assoc] using this
      have hcM := h2 u hu0 (Subgroup.mem_inf.2 ⟨hc, hcH⟩)
      have := ‹M.Normal›.conj_mem _ hcM σ
      simpa [mul_assoc] using this
    · apply h1
      rw [hker]
      exact hin B w hwS hw hgB
