import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

/- English proof (translation)
Introduce `f N P hP hhom`. Establish `key : ∀ (R : RootRing f N) (β : Fin f × Fin N →₀ ℕ), IsBlockAlternating f N R → R.IsHomogeneous (topDegree f N) → coeff β R ≠ 0 → (∀ τ, Function.Injective fun i : Fin N => β (τ, i)) ∧ ∀ τ i, β (τ, i) < N`. Introduce `R β hR hRh hβ`. Establish `hinj` using `h2 f N R β hR hβ`. Use `⟨hinj, ?_⟩` and prove the remaining obligations.

Establish `hdeg : β.degree = topDegree f N`. Assume the negation of the conclusion as `hne`. Conclude with `hβ (hRh.coeff_eq_zero hne)`. Rewrite `hdeg` using `[Finsupp.degree_eq_sum, Fintype.sum_prod_type, topDegree]`. Use `set K := N * (N - 1) / 2`.

Establish `hge : ∀ τ, K ≤ ∑ i, β (τ, i)` using `fun τ => (h3 N _ (hinj τ)).1`. Establish `hsplit : ∑ τ : Fin f, ∑ i, β (τ, i) = ∑ _τ : Fin f, K + ∑ τ : Fin f, (∑ i, β (τ, i) - K)`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun τ _ => (Nat.add_sub_of_le (hge τ)).symm`. Rewrite `hsplit` using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hdeg]`.

Establish `hz : ∑ τ : Fin f, (∑ i, β (τ, i) - K) = 0` using `by omega`. Introduce `τ i`. Establish `hτ` using `(Finset.sum_eq_zero_iff.mp hz) τ (Finset.mem_univ _)`. Conclude with `(h3 N _ (hinj τ)).2 (le_antisymm (by omega) (hge τ)) i`. Establish `hΔ` using `isBlockAlternating_blockVandermonde f N`.

Take `⟨α₁, hα₁⟩` from `MvPolynomial.ne_zero_iff.mp (Flag.blockVandermonde_ne_zero f N)`. Use `set e : ℚ := coeff α₁ P / coeff α₁ (blockVandermonde f N)`. Use `set Q := P - C e * blockVandermonde f N with hQ`. Establish `hQalt : IsBlockAlternating f N Q`. Introduce `w`.

Simplify using `only [hQ, map_sub, map_mul, algHom_C, hP w, hΔ w, smul_sub, mul_smul_comm, MvPolynomial.algebraMap_eq]`. Establish `hQhom : Q.IsHomogeneous (topDegree f N)` using `hhom.sub ((h5 f N).C_mul e)`. Establish `hQα₁ : coeff α₁ Q = 0`. Simplify using `only [hQ, coeff_sub, coeff_C_mul, e]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `hQ0 : Q = 0`. Assume the negation of the conclusion as `hne`. Take `⟨α, hα⟩` from `MvPolynomial.ne_zero_iff.mp hne`. Take `⟨hinjα, hltα⟩` from `key Q α hQalt hQhom hα`.

Take `⟨hinj₁, hlt₁⟩` from `key _ α₁ hΔ (h5 f N) hα₁`. Take `⟨w, hw⟩` from `h4 f N α α₁ hltα hlt₁ hinjα hinj₁`. Establish `hα₁eq : (Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2)) = α₁`. Use extensionality with `p`. Simplify using `[hw]`.

Establish `hc` using `h1 f N w Q α`. Rewrite `hc` using `[hα₁eq, hQα₁, hQalt w, coeff_smul, smul_eq_mul]`. Establish `hs : blockSign f N w ≠ 0`. Introduce `h0`. Use `Flag.blockSign_mul_self f N w` as an intermediate fact.

Rewrite `this` using `[h0, zero_mul]`. Conclude with `zero_ne_one this`. Conclude with `hα ((mul_eq_zero.mp hc).resolve_left hs)`. Conclude with `⟨e, sub_eq_zero.mp hQ0⟩`.
-/
theorem FlagAltTopDegree.proof (h1 : FlagCoeffBlockPermute.Statement)
    (h2 : FlagAltCoeffInjective.Statement) (h3 : FlagInjSumBound.Statement)
    (h4 : FlagStaircaseOrbit.Statement) (h5 : FlagVandermondeHomogeneous.Statement) :
    FlagAltTopDegree.Statement := by
  intro f N P hP hhom

  have key : ∀ (R : RootRing f N) (β : Fin f × Fin N →₀ ℕ), IsBlockAlternating f N R →
      R.IsHomogeneous (topDegree f N) → coeff β R ≠ 0 →
      (∀ τ, Function.Injective fun i : Fin N => β (τ, i)) ∧ ∀ τ i, β (τ, i) < N := by
    intro R β hR hRh hβ
    have hinj := h2 f N R β hR hβ
    refine ⟨hinj, ?_⟩
    have hdeg : β.degree = topDegree f N := by
      by_contra hne; exact hβ (hRh.coeff_eq_zero hne)
    rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type, topDegree] at hdeg
    set K := N * (N - 1) / 2
    have hge : ∀ τ, K ≤ ∑ i, β (τ, i) := fun τ => (h3 N _ (hinj τ)).1
    have hsplit : ∑ τ : Fin f, ∑ i, β (τ, i) =
        ∑ _τ : Fin f, K + ∑ τ : Fin f, (∑ i, β (τ, i) - K) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun τ _ => (Nat.add_sub_of_le (hge τ)).symm
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hdeg] at hsplit
    have hz : ∑ τ : Fin f, (∑ i, β (τ, i) - K) = 0 := by omega
    intro τ i
    have hτ := (Finset.sum_eq_zero_iff.mp hz) τ (Finset.mem_univ _)
    exact (h3 N _ (hinj τ)).2 (le_antisymm (by omega) (hge τ)) i
  have hΔ := isBlockAlternating_blockVandermonde f N
  obtain ⟨α₁, hα₁⟩ := MvPolynomial.ne_zero_iff.mp (Flag.blockVandermonde_ne_zero f N)
  set e : ℚ := coeff α₁ P / coeff α₁ (blockVandermonde f N)
  set Q := P - C e * blockVandermonde f N with hQ
  have hQalt : IsBlockAlternating f N Q := by
    intro w
    simp only [hQ, map_sub, map_mul, algHom_C, hP w, hΔ w, smul_sub, mul_smul_comm,
      MvPolynomial.algebraMap_eq]
  have hQhom : Q.IsHomogeneous (topDegree f N) := hhom.sub ((h5 f N).C_mul e)
  have hQα₁ : coeff α₁ Q = 0 := by
    simp only [hQ, coeff_sub, coeff_C_mul, e]
    field_simp
    ring
  have hQ0 : Q = 0 := by
    by_contra hne
    obtain ⟨α, hα⟩ := MvPolynomial.ne_zero_iff.mp hne
    obtain ⟨hinjα, hltα⟩ := key Q α hQalt hQhom hα
    obtain ⟨hinj₁, hlt₁⟩ := key _ α₁ hΔ (h5 f N) hα₁
    obtain ⟨w, hw⟩ := h4 f N α α₁ hltα hlt₁ hinjα hinj₁
    have hα₁eq : (Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2)) = α₁ := by
      ext p; simp [hw]
    have hc := h1 f N w Q α
    rw [hα₁eq, hQα₁, hQalt w, coeff_smul, smul_eq_mul] at hc
    have hs : blockSign f N w ≠ 0 := by
      intro h0; have := Flag.blockSign_mul_self f N w; rw [h0, zero_mul] at this; exact zero_ne_one this
    exact hα ((mul_eq_zero.mp hc).resolve_left hs)
  exact ⟨e, sub_eq_zero.mp hQ0⟩

end

end RestTerms

end GroundTheory.Heights₂.Heights
