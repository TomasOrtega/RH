import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.LevelRes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc
open scoped Pointwise

/- English proof (translation)
Take `⟨B, hB⟩` from `(exists_isPlaceOver Ω w : ∃ B : ValuationSubring Ω, IsPlaceOver B w)`. Establish `hB' : IsPlaceOver B (w.under (𝓞 F))` using `fun x => by`. Rewrite using `[IsScalarTower.algebraMap_apply F K Ω]`. Conclude with `hB (algebraMap (𝓞 F) (𝓞 K) x)`. Take `⟨g, rfl⟩` from `exists_smul_eq_of_isPlaceOver (F := F) hB' hA`.

Establish `hm : ∀ x, x ∈ B ↔ g x ∈ g • B` using `fun x => ValuationSubring.smul_mem_pointwise_smul_iff.symm`. Establish `hv : ∀ y, (g • B).valuation (g y) < 1 ↔ B.valuation y < 1` using `fun y => by`. Rewrite using `[valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, ← hm, ← hm, map_eq_zero_iff _ g.injective]`. Establish `hD : ∀ s ∈ Dec (F` using `K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) (g • B) := fun s hs => by`. Establish `h1 : res F Ω K s • B = B` using `hs`.

Use `show (g * res F Ω K s * g⁻¹) • g • B = g • B`. Rewrite using `[mul_smul, mul_smul, inv_smul_smul, h1]`. Use `⟨B, g, hB, hm, hD, fun s hs => ⟨hD s hs.1, fun x hx => ?_⟩⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `g.surjective x`. Establish `e : (g * res F Ω K s * g⁻¹) (g y) = g (s y)` using `by show g (s (g.symm (g y))) = _`.

Rewrite using `[AlgEquiv.symm_apply_apply]`. Rewrite using `[e, ← map_sub, hv]`. Conclude with `hs.2 y ((B.valuation_le_one_iff _).2 ((hm y).2 (((g • B).valuation_le_one_iff _).1 hx)))`.
-/
private theorem move {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    (w : HeightOneSpectrum (𝓞 K)) {A : ValuationSubring Ω} (hA : IsPlaceOver A (w.under (𝓞 F))) :
    ∃ (B : ValuationSubring Ω) (g : G F Ω), IsPlaceOver B w ∧ (∀ x, x ∈ B ↔ g x ∈ A) ∧
      (∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) A) ∧
      ∀ s ∈ Ine (F := K) B, g * res F Ω K s * g⁻¹ ∈ Ine (F := F) A := by
  obtain ⟨B, hB⟩ := (exists_isPlaceOver Ω w : ∃ B : ValuationSubring Ω, IsPlaceOver B w)
  have hB' : IsPlaceOver B (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F K Ω]
    exact hB (algebraMap (𝓞 F) (𝓞 K) x)
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hB' hA
  have hm : ∀ x, x ∈ B ↔ g x ∈ g • B := fun x => ValuationSubring.smul_mem_pointwise_smul_iff.symm
  have hv : ∀ y, (g • B).valuation (g y) < 1 ↔ B.valuation y < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, ← hm, ← hm, map_eq_zero_iff _ g.injective]
  have hD : ∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) (g • B) := fun s hs => by
    have h1 : res F Ω K s • B = B := hs
    show (g * res F Ω K s * g⁻¹) • g • B = g • B
    rw [mul_smul, mul_smul, inv_smul_smul, h1]
  refine ⟨B, g, hB, hm, hD, fun s hs => ⟨hD s hs.1, fun x hx => ?_⟩⟩
  obtain ⟨y, rfl⟩ := g.surjective x
  have e : (g * res F Ω K s * g⁻¹) (g y) = g (s y) := by
    show g (s (g.symm (g y))) = _
    rw [AlgEquiv.symm_apply_apply]
  rw [e, ← map_sub, hv]
  exact hs.2 y ((B.valuation_le_one_iff _).2 ((hm y).2 (((g • B).valuation_le_one_iff _).1 hx)))

/- English proof (translation)
Express the relevant statement in the definitionally equal form `algebraMap (𝓞 F) (𝓞 L) _ ∈ w.asIdeal ↔ _`. Rewrite using `[map_natCast]`.
-/
private theorem nat_mem_under {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (l : ℕ)
    (w : HeightOneSpectrum (𝓞 L)) : ((l : ℕ) : 𝓞 F) ∈ (w.under (𝓞 F)).asIdeal ↔ ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  change algebraMap (𝓞 F) (𝓞 L) _ ∈ w.asIdeal ↔ _
  rw [map_natCast]

/- English proof (translation)
Rewrite using `[map_mul, map_mul, map_inv, mul_inv_cancel_comm]`.
-/
private theorem char_conj {Γ C : Type} [Group Γ] [CommGroup C] (χ : Γ →* C) (g s : Γ) : χ (g * s * g⁻¹) = χ s := by
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

/- English proof (translation)
Rewrite using `[map_mul, map_mul, map_inv]`. Use `group`.
-/
private theorem rep_conj {Γ C : Type} [Group Γ] [Group C] (r : Γ →* C) (P : C) (g s : Γ) :
    P * r g * r s * (P * r g)⁻¹ = P * r (g * s * g⁻¹) * P⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  group

/- English proof (translation)
Introduce `F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ n M m r H`. Use `haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic`. Establish `hres : Continuous (res F Ω K : G K Ω →* G F Ω)` using `continuous_restrictScalarsHom F K Ω`. Establish `hK : ∀ χ : G F Ω →* (Qbar l)ˣ, KillsMu M χ → KillsMu M (χ.comp (res F Ω K))` using `fun χ h s hs => h _ hs`. Use `⟨H.cont.comp hres, fun w hw => ?_, fun w hw => ?_⟩` and prove the remaining obligations.

Take `⟨A, hA, χ, hχ, P, hP⟩` from `H.away (w.under (𝓞 F)) (fun h => hw ((nat_mem_under l w).1 h))`. Take `⟨B, g, hB, -, -, hI⟩` from `move w hA`. Use `⟨B, hB, fun i => (χ i).comp (res F Ω K), fun i => hK _ (hχ i), P * r g, fun s hs => ?_⟩` and prove the remaining obligations. Establish `h` using `hP _ (hI s hs)`. Simplify using `only [char_conj] at h`.

Rewrite using `[MonoidHom.comp_apply, rep_conj]`. Conclude with `h`. Take `⟨A, hA, κ, χ, hχ, ⟨P, hP⟩, hκ⟩` from `H.above (w.under (𝓞 F)) ((nat_mem_under l w).2 hw)`. Take `⟨B, g, hB, -, hD, hI⟩` from `move w hA`. Set `d : ↥(Dec (F` to `K) B) →* ↥(Dec (F := F) A) := (((MulAut.conj g).toMonoidHom.comp (res F Ω K)).comp (Dec (F := K) B).subtype).codRestrict _ fun s => hD s s.2`.

Establish `hd : ∀ s, (d s : G F Ω) = g * res F Ω K s * g⁻¹` using `fun _ => rfl`. Use `⟨B, hB, fun i => (κ i).comp d, fun i => (χ i).comp (res F Ω K), fun i => hK _ (hχ i), ⟨P * r g, fun s => ?_⟩, fun i s hs => ?_⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.comp_apply, rep_conj]`. Conclude with `hP (d s)`. Establish `h` using `hκ i (d s) (hI s hs)`.

Rewrite `h` using `[hd, char_conj, char_conj]`. Conclude with `h`.
-/
theorem UpperTheory.V.Lev.levelFRes :
    UpperTheory.V.Lev.LevelFRes := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ n M m r H
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  have hres : Continuous (res F Ω K : G K Ω →* G F Ω) := continuous_restrictScalarsHom F K Ω
  have hK : ∀ χ : G F Ω →* (Qbar l)ˣ, KillsMu M χ → KillsMu M (χ.comp (res F Ω K)) :=
    fun χ h s hs => h _ hs
  refine ⟨H.cont.comp hres, fun w hw => ?_, fun w hw => ?_⟩
  · obtain ⟨A, hA, χ, hχ, P, hP⟩ := H.away (w.under (𝓞 F)) (fun h => hw ((nat_mem_under l w).1 h))
    obtain ⟨B, g, hB, -, -, hI⟩ := move w hA
    refine ⟨B, hB, fun i => (χ i).comp (res F Ω K), fun i => hK _ (hχ i), P * r g, fun s hs => ?_⟩
    have h := hP _ (hI s hs)
    simp only [char_conj] at h
    rw [MonoidHom.comp_apply, rep_conj]
    exact h
  · obtain ⟨A, hA, κ, χ, hχ, ⟨P, hP⟩, hκ⟩ := H.above (w.under (𝓞 F)) ((nat_mem_under l w).2 hw)
    obtain ⟨B, g, hB, -, hD, hI⟩ := move w hA
    let d : ↥(Dec (F := K) B) →* ↥(Dec (F := F) A) :=
      (((MulAut.conj g).toMonoidHom.comp (res F Ω K)).comp (Dec (F := K) B).subtype).codRestrict _
        fun s => hD s s.2
    have hd : ∀ s, (d s : G F Ω) = g * res F Ω K s * g⁻¹ := fun _ => rfl
    refine ⟨B, hB, fun i => (κ i).comp d, fun i => (χ i).comp (res F Ω K), fun i => hK _ (hχ i),
      ⟨P * r g, fun s => ?_⟩, fun i s hs => ?_⟩
    · rw [MonoidHom.comp_apply, rep_conj]
      exact hP (d s)
    · have h := hκ i (d s) (hI s hs)
      rw [hd, char_conj, char_conj] at h
      exact h
