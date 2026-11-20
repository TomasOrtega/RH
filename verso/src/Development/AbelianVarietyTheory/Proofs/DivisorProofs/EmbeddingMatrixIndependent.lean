import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomsDvrCardEqFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicRingHomEqCanonical
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ hv Λ _ _ _ _ _ _ d b c hc`. Take `⟨hfin, hcard⟩` from `GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ`. Use `haveI : Fintype (Λ →+* O) := Fintype.ofFinite _`. Establish `hd : Module.finrank ℤ_[p] Λ = d`. Rewrite using `[Module.finrank_eq_card_basis b, Fintype.card_fin]`.

Set `ι : ℤ_[p] →+* C` to `(algebraMap O C).comp (padicToO p O)`. Set `w : (Λ →+* O) → (Fin d → C)` to `fun σ j => algebraMap O C (σ (b j))`. Establish `hlin : ∀ σ : Λ →+* O, ∀ z : ℤ_[p], ∀ x : Λ, algebraMap O C (σ (z • x)) = ι z * algebraMap O C (σ x)`. Introduce `σ z x`. Rewrite using `[Algebra.smul_def, map_mul, map_mul]`.

Use `congr 1`. Establish `hu` using `GlobalTheory.padicToO_unique p O (σ.comp (algebraMap ℤ_[p] Λ))`. Use `RingHom.congr_fun hu z` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`. Rewrite using `[this]`.

Both sides reduce to the same expression. Establish `hind : LinearIndependent C w`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `a ha`. Establish `hcol : ∀ j, ∑ σ, a σ * algebraMap O C (σ (b j)) = 0`.

Introduce `j`. Use `congrFun ha j` as an intermediate fact. Simplify `this` using `[w, Finset.sum_apply, smul_eq_mul]`. Establish `hall : ∀ x : Λ, ∑ σ, a σ * algebraMap O C (σ x) = 0`. Introduce `x`.

Establish `hx : ∀ σ : Λ →+* O, algebraMap O C (σ x) = ∑ j, ι (b.repr x j) * algebraMap O C (σ (b j))`. Introduce `σ`. Use `conv_lhs => rw [← b.sum_repr x]`. Rewrite using `[map_sum, map_sum]`. Conclude with `Finset.sum_congr rfl (fun j _ => hlin σ _ _)`.

Repeatedly rewrite using `[hx, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero (fun j _ => ?_)` and prove the remaining obligations. Establish `: ∑ σ, a σ * (ι (b.repr x j) * algebraMap O C (σ (b j))) = ι (b.repr x j) * ∑ σ, a σ * algebraMap O C (σ (b j))`. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl (fun σ _ => by ring)`. Rewrite using `[this, hcol j, mul_zero]`. Set `τ : (Λ →+* O) → (Λ →* C)` to `fun σ => ((algebraMap O C).comp σ).toMonoidHom`. Establish `hτ : Function.Injective τ`. Introduce `σ σ' h`.

Use extensionality with `x`. Conclude with `hv.hom_inj (DFunLike.congr_fun h x)`. Establish `hD` using `(linearIndependent_monoidHom Λ C).comp τ hτ`. Rewrite `hD` using `[Fintype.linearIndependent_iff]`. Apply `hD a` to reduce the goal to its premises.

Use function extensionality and compare the values at `x`. Simplify `hall x` using `[τ, Finset.sum_apply]`. Break down `Nat.eq_zero_or_pos d with hd0 | hdpos` into its components or cases. Substitute `hd0` using the available equality. Use function extensionality and compare the values at `j`.

Conclude with `j.elim0`. Use `haveI : Nonempty (Λ →+* O) := (Nat.card_pos_iff.mp (by rw [hcard, hd]; exact hdpos)).1`. Establish `hspan : Submodule.span C (Set.range w) = ⊤`. Apply `hind.span_eq_top_of_card_eq_finrank` to reduce the goal to its premises. Rewrite using `[Module.finrank_fin_fun, ← Nat.card_eq_fintype_card, hcard, hd]`.

Set `f : (Fin d → C) →ₗ[C] C` to `∑ j, c j • LinearMap.proj j`. Establish `hf : f = 0`. Apply `LinearMap.ext_on_range hspan` to reduce the goal to its premises. Introduce `σ`. Use `hc σ` as an intermediate fact.

Simplify `this` using `[f, w, LinearMap.sum_apply, smul_eq_mul]`. Use function extensionality and compare the values at `j`. Use `LinearMap.congr_fun hf (Pi.single j 1)` as an intermediate fact. Simplify `this` using `[f, LinearMap.sum_apply, Pi.single_apply]`.
-/
theorem embedding_matrix_independent : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[p] Λ) (c : Fin d → C), (∀ σ : Λ →+* O, ∑ j, c j * algebraMap O C (σ (b j)) = 0) → c = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ hv Λ _ _ _ _ _ _ d b c hc
  classical
  obtain ⟨hfin, hcard⟩ := GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ
  haveI : Fintype (Λ →+* O) := Fintype.ofFinite _
  have hd : Module.finrank ℤ_[p] Λ = d := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  let ι : ℤ_[p] →+* C := (algebraMap O C).comp (padicToO p O)
  let w : (Λ →+* O) → (Fin d → C) := fun σ j => algebraMap O C (σ (b j))
  have hlin : ∀ σ : Λ →+* O, ∀ z : ℤ_[p], ∀ x : Λ,
      algebraMap O C (σ (z • x)) = ι z * algebraMap O C (σ x) := by
    intro σ z x
    rw [Algebra.smul_def, map_mul, map_mul]
    congr 1
    have hu := GlobalTheory.padicToO_unique p O (σ.comp (algebraMap ℤ_[p] Λ))
    have := RingHom.congr_fun hu z
    simp only [RingHom.comp_apply] at this
    rw [this]
    rfl
  have hind : LinearIndependent C w := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have hcol : ∀ j, ∑ σ, a σ * algebraMap O C (σ (b j)) = 0 := by
      intro j
      have := congrFun ha j
      simpa [w, Finset.sum_apply, smul_eq_mul] using this
    have hall : ∀ x : Λ, ∑ σ, a σ * algebraMap O C (σ x) = 0 := by
      intro x
      have hx : ∀ σ : Λ →+* O, algebraMap O C (σ x)
          = ∑ j, ι (b.repr x j) * algebraMap O C (σ (b j)) := by
        intro σ
        conv_lhs => rw [← b.sum_repr x]
        rw [map_sum, map_sum]
        exact Finset.sum_congr rfl (fun j _ => hlin σ _ _)
      simp_rw [hx, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      have : ∑ σ, a σ * (ι (b.repr x j) * algebraMap O C (σ (b j)))
          = ι (b.repr x j) * ∑ σ, a σ * algebraMap O C (σ (b j)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun σ _ => by ring)
      rw [this, hcol j, mul_zero]
    let τ : (Λ →+* O) → (Λ →* C) := fun σ => ((algebraMap O C).comp σ).toMonoidHom
    have hτ : Function.Injective τ := by
      intro σ σ' h
      ext x
      exact hv.hom_inj (DFunLike.congr_fun h x)
    have hD := (linearIndependent_monoidHom Λ C).comp τ hτ
    rw [Fintype.linearIndependent_iff] at hD
    apply hD a
    funext x
    simpa [τ, Finset.sum_apply] using hall x
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    funext j
    exact j.elim0
  haveI : Nonempty (Λ →+* O) := (Nat.card_pos_iff.mp (by rw [hcard, hd]; exact hdpos)).1
  have hspan : Submodule.span C (Set.range w) = ⊤ := by
    apply hind.span_eq_top_of_card_eq_finrank
    rw [Module.finrank_fin_fun, ← Nat.card_eq_fintype_card, hcard, hd]
  let f : (Fin d → C) →ₗ[C] C := ∑ j, c j • LinearMap.proj j
  have hf : f = 0 := by
    apply LinearMap.ext_on_range hspan
    intro σ
    have := hc σ
    simpa [f, w, LinearMap.sum_apply, smul_eq_mul] using this
  funext j
  have := LinearMap.congr_fun hf (Pi.single j 1)
  simpa [f, LinearMap.sum_apply, Pi.single_apply] using this

end GlobalTheory
