import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomsDvrCardEqFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeLatticeElementPropertyStatement
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

/- English proof (translation)
Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a l => rw [hf, hg]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem eq_of_isTheta_of_isTheta {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]
    {σ : Λ →+* O} {f g : RL p O Λ →+* O} (hf : IsTheta σ f) (hg : IsTheta σ g) : f = g := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a l => rw [hf, hg]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ τ`. Use `haveI : NoZeroDivisors O := hv.hom_inj.noZeroDivisors _ (map_zero _) (map_mul _)`. Use `haveI : Nontrivial O := by`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nontrivial_iff_subsingleton]`.

Conclude with `(Fact.out : ¬IsUnit (p : O)) (isUnit_of_subsingleton _)`. Use `haveI : Finite (Λ →+* O) := (GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ).1`. Use `letI : Fintype (Λ →+* O) := Fintype.ofFinite _`. Establish `hsurj` using `(GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε).2.2.2.1`. Establish `hl : ∀ σ : Λ →+* O, σ ≠ τ → ∃ l : Λ, σ l ≠ τ l`.

Introduce `σ h`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `h (RingHom.ext hc)`. Use `choose! l hl using hl`.

Use `choose a ha using fun σ : Λ →+* O => hsurj (σ (l σ))`. Set `S : Finset (Λ →+* O)` to `Finset.univ.filter (· ≠ τ)`. Set `fac : (Λ →+* O) → RL p O Λ` to `fun σ => (1 : Ainf p O) ⊗ₜ[ℤ_[p]] l σ - a σ ⊗ₜ[ℤ_[p]] (1 : Λ)`. Establish `hfac : ∀ (ρ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta ρ f → ∀ σ, f (fac σ) = ρ (l σ) - σ (l σ)`. Introduce `ρ f hf σ`.

Simplify using `only [fac]`. Rewrite using `[map_sub, hf, hf, ha, map_one, map_one, one_mul, mul_one]`. Use `⟨∏ σ ∈ S, fac σ, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `f hf`. Rewrite using `[map_prod]`.

Use `Finset.prod_ne_zero_iff.mpr fun σ hσ => ?_` and prove the remaining obligations. Rewrite using `[hfac τ f hf σ]`. Establish `hστ : σ ≠ τ` using `(Finset.mem_filter.mp hσ).2`. Conclude with `sub_ne_zero.mpr (hl σ hστ).symm`. Introduce `σ f hστ hf`.

Rewrite using `[map_prod]`. Use `Finset.prod_eq_zero (i := σ) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hστ⟩) ?_` and prove the remaining obligations. Rewrite using `[hfac σ f hf σ, sub_self]`. Introduce `f hf r hr`. Apply `GlobalTheory.T.relative_lattice_element_property p C v O hv ε hε Λ` to reduce the goal to its premises.

Introduce `σ g hg`. Distinguish the cases in `hστ : σ = τ`. Substitute `hστ` using the available equality. Rewrite using `[eq_of_isTheta_of_isTheta hg hf, map_mul, hr, mul_zero]`. Rewrite using `[map_mul, map_prod]`.

Rewrite using `[Finset.prod_eq_zero (i := σ) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hστ⟩) (by rw [hfac σ g hg σ, sub_self]), zero_mul]`.
-/
theorem exists_sep_theta : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ τ : Λ →+* O, ∃ s : RL p O Λ, (∀ f, IsTheta τ f → f s ≠ 0) ∧ (∀ σ f, σ ≠ τ → IsTheta σ f → f s = 0) ∧ ∀ f, IsTheta τ f → ∀ r, f r = 0 → (inA (xi ε) : RL p O Λ) ∣ s * r := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ τ
  haveI : NoZeroDivisors O := hv.hom_inj.noZeroDivisors _ (map_zero _) (map_mul _)
  haveI : Nontrivial O := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact (Fact.out : ¬IsUnit (p : O)) (isUnit_of_subsingleton _)
  haveI : Finite (Λ →+* O) := (GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ).1
  letI : Fintype (Λ →+* O) := Fintype.ofFinite _
  have hsurj := (GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε).2.2.2.1
  have hl : ∀ σ : Λ →+* O, σ ≠ τ → ∃ l : Λ, σ l ≠ τ l := by
    intro σ h
    by_contra hc
    push_neg at hc
    exact h (RingHom.ext hc)
  classical
  choose! l hl using hl
  choose a ha using fun σ : Λ →+* O => hsurj (σ (l σ))
  let S : Finset (Λ →+* O) := Finset.univ.filter (· ≠ τ)
  let fac : (Λ →+* O) → RL p O Λ := fun σ => (1 : Ainf p O) ⊗ₜ[ℤ_[p]] l σ - a σ ⊗ₜ[ℤ_[p]] (1 : Λ)
  have hfac : ∀ (ρ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta ρ f → ∀ σ, f (fac σ) = ρ (l σ) - σ (l σ) := by
    intro ρ f hf σ
    simp only [fac]
    rw [map_sub, hf, hf, ha, map_one, map_one, one_mul, mul_one]
  refine ⟨∏ σ ∈ S, fac σ, ?_, ?_, ?_⟩
  · intro f hf
    rw [map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun σ hσ => ?_
    rw [hfac τ f hf σ]
    have hστ : σ ≠ τ := (Finset.mem_filter.mp hσ).2
    exact sub_ne_zero.mpr (hl σ hστ).symm
  · intro σ f hστ hf
    rw [map_prod]
    refine Finset.prod_eq_zero (i := σ) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hστ⟩) ?_
    rw [hfac σ f hf σ, sub_self]
  · intro f hf r hr
    apply GlobalTheory.T.relative_lattice_element_property p C v O hv ε hε Λ
    intro σ g hg
    by_cases hστ : σ = τ
    · subst hστ
      rw [eq_of_isTheta_of_isTheta hg hf, map_mul, hr, mul_zero]
    · rw [map_mul, map_prod]
      rw [Finset.prod_eq_zero (i := σ) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hστ⟩)
        (by rw [hfac σ g hg σ, sub_self]), zero_mul]

end GlobalTheory.DetInv
