import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemAdjoinOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitSigmaEqMulHilbert90InvAlg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KappaSumZeroAndStableSumMulZeroOfNotIntegral

namespace GlobalTheory.UnitLemma.TwistUnitAny

open GlobalTheory.UnitLemma Polynomial

variable {K : UQ}

/- English proof (translation)
Use `set R := (algebraMap K.O K.E).range with hR`. Use `set T := Algebra.trace K.E B.A with hT`. Establish `hεT : ∀ a, T (ε * a) ∈ R ↔ T a ∈ R`. Introduce `a`. Break down `hε with rfl | rfl` into its components or cases.

Rewrite using `[one_mul]`. Rewrite using `[neg_one_mul, map_neg, neg_mem_iff]`. Establish `hsym : ∀ a b : B.A, T (β * x * a * B.σ b) ∈ R ↔ T (β * x * (B.g * b) * B.σ a) ∈ R`. Introduce `a b`. Rewrite using `[← TwistUnit.trace_σ_mem B (β * x * a * B.σ b), show B.σ (β * x * a * B.σ b) = ε * (β * x * (B.g * b) * B.σ a) by`.

Rewrite using `[map_mul, map_mul, map_mul, hβ, hx, B.σ_σ]`. Use the proof step `ring, hεT]`. Simplify using `only [InvAlg.herm, ← hT, ← hR] at hU`. Establish `h1 : ∀ y ∈ L, B.σ B.g * y ∈ L`. Introduce `y hy`.

Rewrite using `[hU]`. Introduce `y' hy'`. Rewrite using `[hsym, show β * x * (B.g * (B.σ B.g * y)) * B.σ y' = β * x * y * B.σ y' by`. Take the linear combination `(β * x * y * B.σ y') * hg]`. Conclude with `(hU y').1 hy' y hy`.

Introduce `y hy`. Rewrite using `[hU]`. Introduce `y' hy'`. Establish `hb : B.σ B.g * (B.σ B.g * y') ∈ L` using `h1 _ (h1 y' hy')`. Use `(hU _).1 hb y hy` as an intermediate fact.

Rewrite `this` using `[hsym]`. Rewrite using `[show β * x * y' * B.σ (B.g * y) = β * x * (B.g * (B.σ B.g * (B.σ B.g * y'))) * B.σ y by`. Rewrite using `[map_mul]`. Take the linear combination `(-(β * x * y' * B.σ B.g * B.σ y)) * hg]`. Conclude with `this`.
-/
theorem stable_of_unimodular (B : InvAlg K) (hg : B.g * B.σ B.g = 1) (ε : B.A) (hε : ε = 1 ∨ ε = -1)
    (β x : B.A) (hβ : B.σ β = β * (ε * B.g)) (hx : B.σ x = x) (L : Submodule K.O B.A)
    (hU : ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm (β * x) y z ∈ (algebraMap K.O K.E).range) :
    ∀ y ∈ L, B.g * y ∈ L := by
  set R := (algebraMap K.O K.E).range with hR
  set T := Algebra.trace K.E B.A with hT
  have hεT : ∀ a, T (ε * a) ∈ R ↔ T a ∈ R := by
    intro a
    rcases hε with rfl | rfl
    · rw [one_mul]
    · rw [neg_one_mul, map_neg, neg_mem_iff]
  have hsym : ∀ a b : B.A, T (β * x * a * B.σ b) ∈ R ↔ T (β * x * (B.g * b) * B.σ a) ∈ R := by
    intro a b
    rw [← TwistUnit.trace_σ_mem B (β * x * a * B.σ b),
      show B.σ (β * x * a * B.σ b) = ε * (β * x * (B.g * b) * B.σ a) by
        rw [map_mul, map_mul, map_mul, hβ, hx, B.σ_σ]; ring, hεT]
  simp only [InvAlg.herm, ← hT, ← hR] at hU
  have h1 : ∀ y ∈ L, B.σ B.g * y ∈ L := by
    intro y hy
    rw [hU]
    intro y' hy'
    rw [hsym, show β * x * (B.g * (B.σ B.g * y)) * B.σ y' = β * x * y * B.σ y' by
      linear_combination (β * x * y * B.σ y') * hg]
    exact (hU y').1 hy' y hy
  intro y hy
  rw [hU]
  intro y' hy'
  have hb : B.σ B.g * (B.σ B.g * y') ∈ L := h1 _ (h1 y' hy')
  have := (hU _).1 hb y hy
  rw [hsym] at this
  rw [show β * x * y' * B.σ (B.g * y) = β * x * (B.g * (B.σ B.g * (B.σ B.g * y'))) * B.σ y by
    rw [map_mul]; linear_combination (-(β * x * y' * B.σ B.g * B.σ y)) * hg]
  exact this

/- English proof (translation)
Introduce `K B hg hs ε hε`. Distinguish the cases in `hi : IsIntegral K.O B.g`. Conclude with `TwistUnit.twisted_unit_eq_unit K B hg hs hi ε hε`. Apply the tactic sequence `have hσε : B.σ ε = ε := by rcases hε with rfl | rfl <;> simp`. Apply the tactic sequence `have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp`.

Establish `hu : (ε * B.g) * B.σ (ε * B.g) = 1`. Rewrite using `[map_mul, hσε]`. Take the linear combination `B.g * B.σ B.g * hεε + hg`. Take `⟨β₀, hβ⟩` from `GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma K B (ε * B.g) hu`. Use `⟨β₀, hβ, fun x hx => ?_⟩` and prove the remaining obligations.

Use extensionality with `L`. Simplify using `only [Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hLat, hU⟩`. Conclude with `absurd (isIntegral_of_isLat_stable L hLat B.g (stable_of_unimodular B hg ε hε β₀ x hβ hx L hU)) hi`.

Introduce and unpack `⟨hLat, h2, -⟩`. Conclude with `absurd (isIntegral_of_isLat_stable L hLat B.g h2) hi`.
-/
theorem twisted_unit_eq_unit_any : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable →
    ∀ ε : B.A, (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧
      ∀ x : B.Aˣ, B.σ (x : B.A) = x →
        {L : Submodule K.O B.A | GlobalTheory.UnitLemma.IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L,
          B.herm ((β₀ : B.A) * x) y z ∈ (algebraMap K.O K.E).range} = B.X x := by
  intro K B hg hs ε hε
  by_cases hi : IsIntegral K.O B.g
  · exact TwistUnit.twisted_unit_eq_unit K B hg hs hi ε hε
  have hσε : B.σ ε = ε := by rcases hε with rfl | rfl <;> simp
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hu : (ε * B.g) * B.σ (ε * B.g) = 1 := by
    rw [map_mul, hσε]; linear_combination B.g * B.σ B.g * hεε + hg
  obtain ⟨β₀, hβ⟩ := GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma K B (ε * B.g) hu
  refine ⟨β₀, hβ, fun x hx => ?_⟩
  ext L
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hLat, hU⟩
    exact absurd (isIntegral_of_isLat_stable L hLat B.g
      (stable_of_unimodular B hg ε hε β₀ x hβ hx L hU)) hi
  · rintro ⟨hLat, h2, -⟩
    exact absurd (isIntegral_of_isLat_stable L hLat B.g h2) hi

end GlobalTheory.UnitLemma.TwistUnitAny
