import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TransvectionPeriodicity
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.EqCovol

/- English proof (translation)
Introduce `E _ _ _ r X Δ hle hidx`. Establish `hT : ∃ T : Finset (GL (Fin r) E), ∀ g ∈ X.Γ, ∃ t ∈ T, t⁻¹ * g ∈ Δ`. Use `letI := Subgroup.fintypeOfIndexNeZero hidx`. Use `⟨Finset.univ.image (fun q : X.Γ ⧸ Δ.subgroupOf X.Γ => ((Quotient.out q : X.Γ) : GL (Fin r) E)), ?_⟩` and prove the remaining obligations. Introduce `g hg`.

Use `set q : X.Γ ⧸ Δ.subgroupOf X.Γ := QuotientGroup.mk (⟨g, hg⟩ : X.Γ) with hq`. Use `⟨((Quotient.out q : X.Γ) : GL (Fin r) E), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩` and prove the remaining obligations. Establish `h : ((Quotient.out q : X.Γ) : X.Γ ⧸ Δ.subgroupOf X.Γ) = QuotientGroup.mk (⟨g, hg⟩ : X.Γ)` using `QuotientGroup.out_eq' q`. Establish `h2` using `QuotientGroup.eq.mp h`. Rewrite `h2` using `[Subgroup.mem_subgroupOf]`.

Simplify using `using h2`. Take `⟨T, hT⟩` from `hT`. Take `⟨S, hS⟩` from `X.Γ_index`. Use `⟨{ X with Γ := Δ Γ_stab := fun γ hγ => X.Γ_stab γ (hle hγ) Γ_index := ⟨(S ×ˢ T).image (fun p => p.1 * p.2), by` and prove the remaining obligations. Introduce `γ hγ`.

Take `⟨s, hs, h1⟩` from `hS γ hγ`. Take `⟨t, ht, h2⟩` from `hT _ h1`. Use `⟨s * t, Finset.mem_image.mpr ⟨(s, t), Finset.mem_product.mpr ⟨hs, ht⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_inv_rev, mul_assoc]`. Conclude with `h2⟩`.

Use `Γ_free := fun γ hγ => X.Γ_free γ (hle hγ)`. Use `χ_mul := fun la γ hγ γ' hγ' => X.χ_mul la γ (hle hγ) γ' (hle hγ')`. Use `χ_add := fun la la' γ hγ => X.χ_add la la' γ (hle hγ)`. Use `χ_fin := fun la => by`. Take `⟨n, hn, h⟩` from `X.χ_fin la`.

Conclude with `⟨n, hn, fun γ hγ => h γ (hle hγ)⟩`. Use `m := X.m * (Δ.relIndex X.Γ).factorial`. Use `m_pos := Nat.mul_pos X.m_pos (Nat.factorial_pos _)`. Use `transv := by`. Introduce `ξ hξ hiso s hs hint`.

Take `⟨γ, hγ, hmat⟩` from `X.transv ξ hξ hiso s hs hint`. Use `⟨γ ^ (Δ.relIndex X.Γ).factorial, (Subgroup.mem_inf.mp (Subgroup.pow_mem_of_relIndex_ne_zero_of_dvd hidx hγ (fun k hk hk' => Nat.dvd_factorial hk hk'))).1, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_pow_eq_pow_val, hmat, TransvectionPeriodicity.transvMat_pow X.Gm hiso]`. Use `congr 1`. Use `push_cast`.

Use `ring }, rfl, rfl, rfl, rfl⟩`.
-/
theorem exists_data_of_le_relIndex_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)), Δ ≤ X.Γ → Δ.relIndex X.Γ ≠ 0 →
    ∃ P : Data E r, P.Ψ = X.Ψ ∧ P.Gm = X.Gm ∧ P.p0 = X.p0 ∧ P.Γ = Δ := by
  intro E _ _ _ r X Δ hle hidx
  classical
  have hT : ∃ T : Finset (GL (Fin r) E), ∀ g ∈ X.Γ, ∃ t ∈ T, t⁻¹ * g ∈ Δ := by
    letI := Subgroup.fintypeOfIndexNeZero hidx
    refine ⟨Finset.univ.image
      (fun q : X.Γ ⧸ Δ.subgroupOf X.Γ => ((Quotient.out q : X.Γ) : GL (Fin r) E)), ?_⟩
    intro g hg
    set q : X.Γ ⧸ Δ.subgroupOf X.Γ := QuotientGroup.mk (⟨g, hg⟩ : X.Γ) with hq
    refine ⟨((Quotient.out q : X.Γ) : GL (Fin r) E),
      Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have h : ((Quotient.out q : X.Γ) : X.Γ ⧸ Δ.subgroupOf X.Γ) = QuotientGroup.mk (⟨g, hg⟩ : X.Γ) :=
      QuotientGroup.out_eq' q
    have h2 := QuotientGroup.eq.mp h
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  obtain ⟨T, hT⟩ := hT
  obtain ⟨S, hS⟩ := X.Γ_index
  refine ⟨{ X with
    Γ := Δ
    Γ_stab := fun γ hγ => X.Γ_stab γ (hle hγ)
    Γ_index := ⟨(S ×ˢ T).image (fun p => p.1 * p.2), by
      intro γ hγ
      obtain ⟨s, hs, h1⟩ := hS γ hγ
      obtain ⟨t, ht, h2⟩ := hT _ h1
      refine ⟨s * t, Finset.mem_image.mpr ⟨(s, t), Finset.mem_product.mpr ⟨hs, ht⟩, rfl⟩, ?_⟩
      rw [mul_inv_rev, mul_assoc]
      exact h2⟩
    Γ_free := fun γ hγ => X.Γ_free γ (hle hγ)
    χ_mul := fun la γ hγ γ' hγ' => X.χ_mul la γ (hle hγ) γ' (hle hγ')
    χ_add := fun la la' γ hγ => X.χ_add la la' γ (hle hγ)
    χ_fin := fun la => by
      obtain ⟨n, hn, h⟩ := X.χ_fin la
      exact ⟨n, hn, fun γ hγ => h γ (hle hγ)⟩
    m := X.m * (Δ.relIndex X.Γ).factorial
    m_pos := Nat.mul_pos X.m_pos (Nat.factorial_pos _)
    transv := by
      intro ξ hξ hiso s hs hint
      obtain ⟨γ, hγ, hmat⟩ := X.transv ξ hξ hiso s hs hint
      refine ⟨γ ^ (Δ.relIndex X.Γ).factorial,
        (Subgroup.mem_inf.mp (Subgroup.pow_mem_of_relIndex_ne_zero_of_dvd hidx hγ
          (fun k hk hk' => Nat.dvd_factorial hk hk'))).1, ?_⟩
      rw [Units.val_pow_eq_pow_val, hmat, TransvectionPeriodicity.transvMat_pow X.Gm hiso]
      congr 1
      push_cast
      ring }, rfl, rfl, rfl, rfl⟩

end GlobalTheory.EqCovol
