import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryModuleStandardOpensIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoverChartSmoothNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraClosurePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopDegreeCoefficientFormAndEqOnTopFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRegularFormsOfWedgePairingPerfectStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

/- English proof (translation)
Introduce `k _ _ F K _ _ _ _ _ _ d x hc τ hτ I hI p q hpq y hy`. Take `⟨-, hfr, hsm⟩` from `GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hc I hI`. Establish `hrk : Module.finrank K Ω[K⁄k] = d`. Take `⟨b, -⟩` from `hc.exists_basis`. Rewrite using `[Module.finrank_eq_card_basis b, Fintype.card_fin]`.

Establish `htop` using `(GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms k F K d x hc).2 τ hτ`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `GlobalTheory.T.mem_regularForms_of_wedge_pairing_perfect k K (rB k K x I) d p q hrk hpq y hy fun a ha => ?_` and prove the remaining obligations. Establish `haG : a ∈ ⋀[K]^p Ω[K⁄k]` using `((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p q).2.1 a ha).2.2.1`.

Establish `hay : a * y ∈ ⋀[K]^d Ω[K⁄k]` using `hpq ▸ SetLike.mul_mem_graded haG hy`. Establish `hz : ∀ b ∈ rB k K x I, Algebra.trace F K (τ (a * y) * b) ∈ omA k x I`. Introduce `b hb`. Establish `hba : b • a ∈ omB k K (rB k K x I) p` using `((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p q).2.1 a ha).2.2.2 b hb`. Establish `e : τ (a * y) * b = τ ((b • a) * y)`.

Rewrite using `[smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]`. Rewrite using `[e]`. Conclude with `h _ hba`. Take `⟨y', hy', e'⟩` from `(GlobalTheory.T.complementaryModule_standardOpens_iff k F K d x hc τ hτ I hI (τ (a * y))).1 hz`. Establish `hy'G : y' ∈ ⋀[K]^d Ω[K⁄k]` using `((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) d q).2.1 y' hy').2.2.1`.

Rewrite using `[htop _ hay, ← e', ← htop _ hy'G]`. Conclude with `hy'`. Introduce `h a ha`. Establish `hay : a * y ∈ omB k K (rB k K x I) d` using `hpq ▸ (GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p q).1 a ha y h`. Use `(GlobalTheory.T.complementaryModule_standardOpens_iff k F K d x hc τ hτ I hI (τ (a * y))).2 ⟨a * y, hay, rfl⟩ 1 (Subalgebra.one_mem _)` as an intermediate fact.

Rewrite `this` using `[mul_one]`. Then use the resulting hypothesis.
-/
theorem twistedDual_omB : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ p q : ℕ, p + q = d → ∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ omB k K (rB k K x I) p, Algebra.trace F K (τ (a * y)) ∈ omA k x I) ↔ y ∈ omB k K (rB k K x I) q := by
  intro k _ _ F K _ _ _ _ _ _ d x hc τ hτ I hI p q hpq y hy
  obtain ⟨-, hfr, hsm⟩ := GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hc I hI
  have hrk : Module.finrank K Ω[K⁄k] = d := by
    obtain ⟨b, -⟩ := hc.exists_basis
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have htop := (GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms k F K d x hc).2 τ hτ
  constructor
  · intro h
    refine GlobalTheory.T.mem_regularForms_of_wedge_pairing_perfect k K (rB k K x I) d p q hrk hpq y hy fun a ha => ?_
    have haG : a ∈ ⋀[K]^p Ω[K⁄k] := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p q).2.1 a ha).2.2.1
    have hay : a * y ∈ ⋀[K]^d Ω[K⁄k] := hpq ▸ SetLike.mul_mem_graded haG hy
    have hz : ∀ b ∈ rB k K x I, Algebra.trace F K (τ (a * y) * b) ∈ omA k x I := by
      intro b hb
      have hba : b • a ∈ omB k K (rB k K x I) p := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p q).2.1 a ha).2.2.2 b hb
      have e : τ (a * y) * b = τ ((b • a) * y) := by
        rw [smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]
      rw [e]
      exact h _ hba
    obtain ⟨y', hy', e'⟩ := (GlobalTheory.T.complementaryModule_standardOpens_iff k F K d x hc τ hτ I hI (τ (a * y))).1 hz
    have hy'G : y' ∈ ⋀[K]^d Ω[K⁄k] := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) d q).2.1 y' hy').2.2.1
    rw [htop _ hay, ← e', ← htop _ hy'G]
    exact hy'
  · intro h a ha
    have hay : a * y ∈ omB k K (rB k K x I) d := hpq ▸ (GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p q).1 a ha y h
    have := (GlobalTheory.T.complementaryModule_standardOpens_iff k F K d x hc τ hτ I hI (τ (a * y))).2 ⟨a * y, hay, rfl⟩ 1 (Subalgebra.one_mem _)
    rwa [mul_one] at this

end GlobalTheory.PD

/- English proof (translation)
The claim follows from `GlobalTheory.PD.twistedDual_omB`.
-/
example : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (τ : DR k K →ₗ[K] K), IsTop k K x τ → ∀ I : Finset (Fin (d + 1)), I.Nonempty → ∀ p q : ℕ, p + q = d → ∀ y ∈ ⋀[K]^q Ω[K⁄k], (∀ a ∈ omB k K (rB k K x I) p, Algebra.trace F K (τ (a * y)) ∈ omA k x I) ↔ y ∈ omB k K (rB k K x I) q := GlobalTheory.PD.twistedDual_omB
