import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.NRows

open Pointwise

/- English proof (translation)
Establish `m : ∀ y : Ω, y ∈ g • A ↔ (g⁻¹ : G F Ω) y ∈ A` using `fun y => by`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]`. Establish `m' : ∀ y : Ω, (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : G F Ω) y) < 1` using `fun y => by`. Rewrite using `[valuation_lt_one_iff', valuation_lt_one_iff', m, m, map_inv₀, map_eq_zero_iff _ (g⁻¹ : G F Ω).injective]`. Establish `c : ∀ x : Ω, (g⁻¹ : G F Ω) (g x) = x` using `fun x => by show (g⁻¹ * g) x = x`.

Simplify using the standard rewrite rules. Use `⟨?_, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h : σ • g • A = g • A` using `hσ.1 show (g⁻¹ * σ * g) • A = A`. Rewrite using `[mul_smul, mul_smul, h, inv_smul_smul]`. Establish `hx' : (g • A).valuation (g x) ≤ 1`.

Rewrite using `[ValuationSubring.valuation_le_one_iff, m, c]`. Conclude with `(A.valuation_le_one_iff x).1 hx`. Establish `h` using `(m' _).1 (hσ.2 _ hx')`. Rewrite `h` using `[map_sub, c]`. Conclude with `h`.
-/
theorem ine_conj_of_smul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {g σ : G F Ω} (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  have m : ∀ y : Ω, y ∈ g • A ↔ (g⁻¹ : G F Ω) y ∈ A := fun y => by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  have m' : ∀ y : Ω, (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : G F Ω) y) < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', m, m, map_inv₀,
      map_eq_zero_iff _ (g⁻¹ : G F Ω).injective]
  have c : ∀ x : Ω, (g⁻¹ : G F Ω) (g x) = x := fun x => by
    show (g⁻¹ * g) x = x
    simp
  refine ⟨?_, fun x hx => ?_⟩
  · have h : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, m, c]
      exact (A.valuation_le_one_iff x).1 hx
    have h := (m' _).1 (hσ.2 _ hx')
    rw [map_sub, c] at h
    exact h

/- English proof (translation)
Introduce `D htie hadm hLGC i r hr`. Take `⟨-, -, hGal⟩` from `htie`. Establish `hl : (D.nd.l i).Prime` using `Fact.out`. Establish `key : ∀ x, ∃ P Pa, D.naut.ptV i P = some x ∧ IsBCV D.nd D.naut i P Pa` using `fun x => by`. Take `⟨P, hP⟩` from `D.naut.pt_surj i x`.

Take `⟨Pa, hPa⟩` from `hadm i P`. Conclude with `⟨P, Pa, hP, hPa⟩`. Establish `hunr : ∀ P Pa w, IsBCV D.nd D.naut i P Pa → w ∉ D.nd.Q i → (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → w ∉ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) → D.naut.unr (isoLoc D.nd D.naut Pa w)`. Introduce `P Pa w hB hQ hg hp`. Distinguish the cases in `hs : IsSplitPl D.host w`.

Rewrite using `[hB.2.2.2.1 w hs]`. Conclude with `D.naut.locV_unr i P w hs hQ hg hp`. Conclude with `(hB.2.2.2.2.1 w hs).1`. Use `⟨fun w hw => ⟨fun hl0 hl1 x => ?_, fun _ x hm => ?_⟩, fun x w hwl hwS hwQ => ?_⟩` and prove the remaining obligations. Take `⟨P, Pa, hP, hB⟩` from `key x`.

Establish `h` using `(hLGC i x P Pa hP hB _ (hr x)).2 w hw`. Use `⟨(hGal.1 i _ _ w hw (hr x).1).2 ⟨h.1, ?_⟩, fun τ hτ => h.2.2 τ hτ⟩` and prove the remaining obligations. Rewrite using `[h.2.1, D.naut.unr_tw]`. Use `hunr P Pa w hB (fun hq => D.nd.SQ_l i w (Or.inr hq) hw) (fun k => ?_) ?_` and prove the remaining obligations. Establish `hk : D.nd.l i ≠ D.host.g k` using `by fin_cases k`.

Conclude with `hl0`. Conclude with `hl1`. Conclude with `SumRepresentations.not_over_of_ne hl (D.host.g_prime k) hk hw`. Use `split_ifs with hpd`. Conclude with `SumRepresentations.not_over_of_ne hl D.host.pde'_prime (hpd ▸ D.host.pde_ne) hw`.

Conclude with `SumRepresentations.not_over_of_ne hl D.host.pde_prime hpd hw`. Take `⟨P, Pa, hP, hB⟩` from `key x`. Establish `h` using `(hLGC i x P Pa hP hB _ (hr x)).2 w hw`. Use `(hGal.2.1 i _ _ w hw (hr x).1).2 ⟨h.1, ?_⟩` and prove the remaining obligations. Rewrite using `[h.2.1, D.naut.monomial_twist_iff]`.

Conclude with `hm P Pa hP hB`. Take `⟨P, Pa, hP, hB⟩` from `key x`. Establish `h` using `(hLGC i x P Pa hP hB _ (hr x)).1 w hwl`. Establish `hS : ¬ ((w ∈ placesOver D.host.E (D.host.g 0) ∨ w ∈ placesOver D.host.E (D.host.g 1) ∨ w ∈ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde)) ∧ w ∉ placesOver D.host.E (D.nd.l i))` using `fun hh => hwS ((D.nd.S_def i w).2 hh)`. Establish `hu : D.naut.unr (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w)`.

Rewrite using `[h, D.naut.unr_tw]`. Use `hunr P Pa w hB hwQ (fun k hk => hS ⟨?_, hwl⟩) (fun hk => hS ⟨Or.inr (Or.inr hk), hwl⟩)` and prove the remaining obligations. Use `fin_cases k`. Conclude with `Or.inl hk`. Conclude with `Or.inr (Or.inl hk)`.

Establish `h1` using `(D.naut.wdOf_unr i _ w hwl (hr x).1).1 hu`. Introduce `A hA σ hσ`. Take `⟨g, hg⟩` from `exists_smul_eq_of_isPlaceOver (D.nd.plOm.2 w) hA`. Establish `hσ' : σ ∈ Ine (F` using `D.host.E) (g • D.nd.plOm.1 w) := by rw [hg]; exact hσ`. Establish `h2` using `h1 _ (ine_conj_of_smul hσ')`.

Establish `h3 : mapRep (iotaOQ D.nd D.naut i) (r x) σ = 1`. Establish `e : σ = g * (g⁻¹ * σ * g) * g⁻¹` using `by group`. Rewrite using `[e, map_mul, map_mul, h2, mul_one, ← map_mul, mul_inv_cancel, map_one]`. Apply `Units.ext` to reduce the goal to its premises. Establish `h4` using `congrArg (fun u : GL (Fin D.R.nV) (Qbar (D.nd.l i)) => u.val) h3`.

Simplify using `only [mapRep, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one] at h4`. Use `Matrix.map_injective (SumRepresentations.iotaOQ_injective D.nd D.naut i) ?_` and prove the remaining obligations. Use `show (r x σ).val.map (iotaOQ D.nd D.naut i) = (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (iotaOQ D.nd D.naut i)`. Rewrite using `[Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `h4`.
-/
theorem crys_unram_of_lgc : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → (∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))), (∀ x, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (mapRep (iotaOQ D.nd D.naut i) (r x))) → (∀ w ∈ placesOver D.host.E (D.nd.l i),
      (D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → ∀ x, D.naut.IsCrysW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
        ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) ∧
      ((D.nd.l i = D.host.g 0 ∨ D.nd.l i = D.host.g 1) → ∀ x,
        (∀ P Pa, D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → D.naut.mono0 (isoLoc D.nd D.naut Pa w)) →
        D.naut.IsPotCrysW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w)) ∧
    ∀ x w, w ∉ placesOver D.host.E (D.nd.l i) → w ∉ D.nd.S i → w ∉ D.nd.Q i → UnramAt (F := D.host.E) (r x) w := by
  intro D htie hadm hLGC i r hr
  obtain ⟨-, -, hGal⟩ := htie
  have hl : (D.nd.l i).Prime := Fact.out
  have key : ∀ x, ∃ P Pa, D.naut.ptV i P = some x ∧ IsBCV D.nd D.naut i P Pa := fun x => by
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := hadm i P
    exact ⟨P, Pa, hP, hPa⟩
  have hunr : ∀ P Pa w, IsBCV D.nd D.naut i P Pa → w ∉ D.nd.Q i →
      (∀ k, w ∉ placesOver D.host.E (D.host.g k)) →
      w ∉ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) →
      D.naut.unr (isoLoc D.nd D.naut Pa w) := by
    intro P Pa w hB hQ hg hp
    by_cases hs : IsSplitPl D.host w
    · rw [hB.2.2.2.1 w hs]
      exact D.naut.locV_unr i P w hs hQ hg hp
    · exact (hB.2.2.2.2.1 w hs).1
  refine ⟨fun w hw => ⟨fun hl0 hl1 x => ?_, fun _ x hm => ?_⟩, fun x w hwl hwS hwQ => ?_⟩
  · obtain ⟨P, Pa, hP, hB⟩ := key x
    have h := (hLGC i x P Pa hP hB _ (hr x)).2 w hw
    refine ⟨(hGal.1 i _ _ w hw (hr x).1).2 ⟨h.1, ?_⟩, fun τ hτ => h.2.2 τ hτ⟩
    rw [h.2.1, D.naut.unr_tw]
    refine hunr P Pa w hB (fun hq => D.nd.SQ_l i w (Or.inr hq) hw) (fun k => ?_) ?_
    · have hk : D.nd.l i ≠ D.host.g k := by
        fin_cases k
        · exact hl0
        · exact hl1
      exact SumRepresentations.not_over_of_ne hl (D.host.g_prime k) hk hw
    · split_ifs with hpd
      · exact SumRepresentations.not_over_of_ne hl D.host.pde'_prime (hpd ▸ D.host.pde_ne) hw
      · exact SumRepresentations.not_over_of_ne hl D.host.pde_prime hpd hw
  · obtain ⟨P, Pa, hP, hB⟩ := key x
    have h := (hLGC i x P Pa hP hB _ (hr x)).2 w hw
    refine (hGal.2.1 i _ _ w hw (hr x).1).2 ⟨h.1, ?_⟩
    rw [h.2.1, D.naut.monomial_twist_iff]
    exact hm P Pa hP hB
  · obtain ⟨P, Pa, hP, hB⟩ := key x
    have h := (hLGC i x P Pa hP hB _ (hr x)).1 w hwl
    have hS : ¬ ((w ∈ placesOver D.host.E (D.host.g 0) ∨ w ∈ placesOver D.host.E (D.host.g 1) ∨
        w ∈ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde)) ∧
        w ∉ placesOver D.host.E (D.nd.l i)) := fun hh => hwS ((D.nd.S_def i w).2 hh)
    have hu : D.naut.unr (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) := by
      rw [h, D.naut.unr_tw]
      refine hunr P Pa w hB hwQ (fun k hk => hS ⟨?_, hwl⟩) (fun hk => hS ⟨Or.inr (Or.inr hk), hwl⟩)
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
    have h1 := (D.naut.wdOf_unr i _ w hwl (hr x).1).1 hu
    intro A hA σ hσ
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (D.nd.plOm.2 w) hA
    have hσ' : σ ∈ Ine (F := D.host.E) (g • D.nd.plOm.1 w) := by rw [hg]; exact hσ
    have h2 := h1 _ (ine_conj_of_smul hσ')
    have h3 : mapRep (iotaOQ D.nd D.naut i) (r x) σ = 1 := by
      have e : σ = g * (g⁻¹ * σ * g) * g⁻¹ := by group
      rw [e, map_mul, map_mul, h2, mul_one, ← map_mul, mul_inv_cancel, map_one]
    apply Units.ext
    have h4 := congrArg (fun u : GL (Fin D.R.nV) (Qbar (D.nd.l i)) => u.val) h3
    simp only [mapRep, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one] at h4
    refine Matrix.map_injective (SumRepresentations.iotaOQ_injective D.nd D.naut i) ?_
    show (r x σ).val.map (iotaOQ D.nd D.naut i) = (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (iotaOQ D.nd D.naut i)
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact h4

end GlobalTheory.NRows
