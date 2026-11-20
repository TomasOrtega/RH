import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.FlCoeMul

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S
open ValuativeRel

/- English proof (translation)
Use `haveI : Nontrivial E := by`. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Establish `h1` using `L.rank`. Establish `h2` using `Module.finrank_zero_of_subsingleton (R := F) (M := E)`.

Use linear arithmetic over natural numbers and integers. Conclude with `(algebraMap F E).injective`.
-/
theorem fl_inj {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) : Function.Injective (algebraMap F E) := by
  haveI : Nontrivial E := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have h1 := L.rank
    have h2 := Module.finrank_zero_of_subsingleton (R := F) (M := E)
    omega
  exact (algebraMap F E).injective

/- English proof (translation)
Use `haveI : Nontrivial E := by`. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Establish `h1` using `L.rank`. Establish `h2` using `Module.finrank_zero_of_subsingleton (R := F) (M := E)`.

Use linear arithmetic over natural numbers and integers. Introduce `hn0`. Rewrite `hn` using `[hn0]`. Establish `hcj : L.cj x ≠ 0` using `fun h => hx0 ((map_eq_zero_iff L.cj L.cj.injective).mp h)`. Establish `hu : IsUnit (x * L.cj x)` using `(hE x hx0).mul (hE _ hcj)`.

Apply `hu.ne_zero` to reduce the goal to its premises. Rewrite using `[← hn]`. Simplify using the standard rewrite rules.
-/
theorem fl_norm_ne {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hE : ∀ x : E, x ≠ 0 → IsUnit x)
    {x : E} (hx0 : x ≠ 0) (n : 𝒪[F]) (hn : algebraMap F E n = x * L.cj x) : n ≠ 0 := by
  haveI : Nontrivial E := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have h1 := L.rank
    have h2 := Module.finrank_zero_of_subsingleton (R := F) (M := E)
    omega
  intro hn0
  rw [hn0] at hn
  have hcj : L.cj x ≠ 0 := fun h => hx0 ((map_eq_zero_iff L.cj L.cj.injective).mp h)
  have hu : IsUnit (x * L.cj x) := (hE x hx0).mul (hE _ hcj)
  apply hu.ne_zero
  rw [← hn]
  simp

/- English proof (translation)
Use `haveI := hl`. Establish `key : ∀ n : 𝒪[F], ∀ x ∈ L.O, x ≠ 0 → algebraMap F E n = x * L.cj x → ∃ k : ℕ, ∃ u ∈ L.O, (∃ w ∈ L.O, u * w = 1) ∧ x = algebraMap F E ϖ ^ k * u`. Introduce `n`. Use `WellFounded.induction (wellFounded_dvdNotUnit (α := 𝒪[F])) (C := fun n : 𝒪[F] => ∀ x ∈ L.O, x ≠ 0 → algebraMap F E n = x * L.cj x → ∃ k : ℕ, ∃ u ∈ L.O, (∃ w ∈ L.O, u * w = 1) ∧ x = algebraMap F E ϖ ^ k * u) n ?_` and prove the remaining obligations. Introduce `n ih x hx hx0 hn`.

Distinguish the cases in `hdiv : ∃ z ∈ L.O, x = algebraMap F E ϖ * z`. Take `⟨z, hz, rfl⟩` from `hdiv`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hx0`.

Take `⟨n', hn'⟩` from `fl_norm L hinj hz`. Establish `hcj : L.cj (algebraMap F E ϖ) = algebraMap F E ϖ` using `L.cj.commutes _`. Establish `heq : n = n' * (ϖ * ϖ)`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show ((n' * (ϖ * ϖ) : 𝒪[F]) : F) = (n' : F) * ((ϖ : F) * (ϖ : F)) from rfl, map_mul, map_mul]`. Establish `hdvd : DvdNotUnit n' n`. Use `⟨fl_norm_ne L hE hz0 n' hn', ϖ * ϖ, ?_, heq⟩` and prove the remaining obligations. Rewrite using `[IsUnit.mul_iff]`.

Conclude with `fun h => hϖ.not_isUnit h.1`. Take `⟨k, u, hu, hw, hzu⟩` from `ih n' hdvd z hz hz0 hn'`. Conclude with `⟨k + 1, u, hu, hw, by rw [hzu, pow_succ]; ring⟩`. Take `⟨y, hy, hxy⟩` from `fl_local L hl hE hinj ϖ hϖ x hx hdiv`. Conclude with `⟨0, x, hx, ⟨y, hy, hxy⟩, by simp⟩`.

Introduce `x hx hx0`. Take `⟨n, hn⟩` from `fl_norm L hinj hx`. Conclude with `key n x hx hx0 hn`.
-/
theorem fl_fact {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (hE : ∀ x : E, x ≠ 0 → IsUnit x) (hinj : Function.Injective (algebraMap F E))
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) :
    ∀ x ∈ L.O, x ≠ 0 → ∃ k : ℕ, ∃ u ∈ L.O, (∃ w ∈ L.O, u * w = 1) ∧ x = algebraMap F E ϖ ^ k * u := by
  haveI := hl
  have key : ∀ n : 𝒪[F], ∀ x ∈ L.O, x ≠ 0 → algebraMap F E n = x * L.cj x →
      ∃ k : ℕ, ∃ u ∈ L.O, (∃ w ∈ L.O, u * w = 1) ∧ x = algebraMap F E ϖ ^ k * u := by
    intro n
    refine WellFounded.induction (wellFounded_dvdNotUnit (α := 𝒪[F]))
      (C := fun n : 𝒪[F] => ∀ x ∈ L.O, x ≠ 0 → algebraMap F E n = x * L.cj x →
        ∃ k : ℕ, ∃ u ∈ L.O, (∃ w ∈ L.O, u * w = 1) ∧ x = algebraMap F E ϖ ^ k * u) n ?_
    intro n ih x hx hx0 hn
    by_cases hdiv : ∃ z ∈ L.O, x = algebraMap F E ϖ * z
    · obtain ⟨z, hz, rfl⟩ := hdiv
      have hz0 : z ≠ 0 := by
        rintro rfl
        simp at hx0
      obtain ⟨n', hn'⟩ := fl_norm L hinj hz
      have hcj : L.cj (algebraMap F E ϖ) = algebraMap F E ϖ := L.cj.commutes _
      have heq : n = n' * (ϖ * ϖ) := by
        apply Subtype.ext
        apply hinj
        calc algebraMap F E (n : F) = algebraMap F E ϖ * z * L.cj (algebraMap F E ϖ * z) := hn
          _ = (z * L.cj z) * (algebraMap F E ϖ * algebraMap F E ϖ) := by rw [map_mul, hcj]; ring
          _ = algebraMap F E n' * (algebraMap F E ϖ * algebraMap F E ϖ) := by rw [hn']
          _ = algebraMap F E ((n' * (ϖ * ϖ) : 𝒪[F]) : F) := by
            rw [show ((n' * (ϖ * ϖ) : 𝒪[F]) : F) = (n' : F) * ((ϖ : F) * (ϖ : F)) from rfl, map_mul, map_mul]
      have hdvd : DvdNotUnit n' n := by
        refine ⟨fl_norm_ne L hE hz0 n' hn', ϖ * ϖ, ?_, heq⟩
        rw [IsUnit.mul_iff]
        exact fun h => hϖ.not_isUnit h.1
      obtain ⟨k, u, hu, hw, hzu⟩ := ih n' hdvd z hz hz0 hn'
      exact ⟨k + 1, u, hu, hw, by rw [hzu, pow_succ]; ring⟩
    · obtain ⟨y, hy, hxy⟩ := fl_local L hl hE hinj ϖ hϖ x hx hdiv
      exact ⟨0, x, hx, ⟨y, hy, hxy⟩, by simp⟩
  intro x hx hx0
  obtain ⟨n, hn⟩ := fl_norm L hinj hx
  exact key n x hx hx0 hn

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ L hl _ hE ϖ hϖ`. Establish `hinj` using `fl_inj L`. Conclude with `⟨fl_local L hl hE hinj ϖ hϖ, fl_den L, fl_fact L hl hE hinj ϖ hϖ⟩`.
-/
theorem local_density_integral : FLocO := by
  intro F E _ _ _ _ _ _ L hl _ hE ϖ hϖ
  have hinj := fl_inj L
  exact ⟨fl_local L hl hE hinj ϖ hϖ, fl_den L, fl_fact L hl hE hinj ϖ hϖ⟩

end PI.UnitaryGroupMassFormula.CntFormula
