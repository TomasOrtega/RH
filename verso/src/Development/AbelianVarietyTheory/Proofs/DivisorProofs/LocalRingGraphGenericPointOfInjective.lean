import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgEquivFractionFieldOfLocalRingOfVarietyPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTranscendenceBasisOverConstEqOfAlgEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeOfLocalRingOfVarietyPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfVarietyPointTensorGraphLocalizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphLocalRingRegularParamsAndDimStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormsGraphLocalRingFreelyGeneratedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

open GlobalTheory.DiagLoc in

/- English proof (translation)
Introduce `K κ κ' L _ _ _ _ _ _ _ _ _ _ _ n k k' x τ' R π ρ hx hτ' hz hπc hπf hπi hRf hR hκ' hk`. Take `⟨e, he⟩` from `GlobalTheory.T.exists_algEquiv_fractionField_of_localRingOfVarietyPoint R π hR hπc hπf hπi`. Take `⟨z, hz⟩` from `hz`. Take `rfl : n = k` from `GlobalTheory.T.card_transcendenceBasisOverConst_eq_of_algEquiv e n k x z hx hz`. Establish `hK : Algebra.EssFiniteType ℂ K` using `GlobalTheory.T.essFiniteType_of_localRingOfVarietyPoint R hR`.

Take `⟨O', hO'⟩` from `hκ'`. Establish `hκ'f : Algebra.EssFiniteType ℂ κ'` using `GlobalTheory.T.essFiniteType_of_localRingOfVarietyPoint O' hO'`. Use `set σ : K →ₐ[ℂ] κ' := ρ.comp e.toAlgHom with hσ`. Establish `hQ : IsLocModel (algebraMap ℂ L) (loc L σ)` using `GlobalTheory.T.isLocalRingOfVarietyPoint_tensorGraphLocalization σ hK hκ'f`. Take `⟨hm, hdim⟩` from `GlobalTheory.T.graphLocalRing_regular_params_and_dim (L := L) σ n x hK hκ'f hx`.

Establish `hsum : ∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), algebraMap (K ⊗[ℂ] κ') L (∑ i, (a i : K) ⊗ₜ[ℂ] b i) = ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)` using `fun l a b => map_sum _ _ _`. Establish `hprod : ∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ') (∑ i, (a i : K) ⊗ₜ[ℂ] b i) = ∑ i, ρ (π (a i)) * b i`. Introduce `l a b`. Simplify using `[map_sum, σ, he]`. Use `⟨loc L σ, hQ, fun i => toLoc L σ (x i ⊗ₜ[ℂ] 1 - 1 ⊗ₜ[ℂ] σ (x i)), hm, hdim, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `g hg`. Use `⟨toLoc L σ (g ⊗ₜ 1), ?_, rfl⟩` and prove the remaining obligations. Use `IsUnit.map _ ?_` and prove the remaining obligations. Conclude with `((IsUnit.mk0 g hg).map (Algebra.TensorProduct.includeLeft (R := ℂ) (S := ℂ) (B := κ')))`. Introduce `b hb`.

Use `⟨toLoc L σ (1 ⊗ₜ b), ?_, rfl⟩` and prove the remaining obligations. Use `IsUnit.map _ ?_` and prove the remaining obligations. Conclude with `((IsUnit.mk0 b hb).map (Algebra.TensorProduct.includeRight (R := ℂ) (A := K)))`. Introduce `l a b hne`. Use `⟨toLoc L σ (∑ i, (a i : K) ⊗ₜ[ℂ] b i), ?_, ?_⟩` and prove the remaining obligations.

Establish `hs : (∑ i, (a i : K) ⊗ₜ[ℂ] b i) ∈ (ker σ).primeCompl`. Introduce `hmem`. Conclude with `hne ((hprod l a b).symm.trans hmem)`. Conclude with `IsLocalization.map_units (loc L σ) (⟨_, hs⟩ : (ker σ).primeCompl)`. Simplify using `only [coe_toLoc]`.

Conclude with `hsum l a b`. Introduce `M l a b hJ`. Use `⟨toLoc L σ (∑ i, (a i : K) ⊗ₜ[ℂ] b i), by simp only [coe_toLoc]; exact hsum l a b, ?_⟩` and prove the remaining obligations. Set `E : K ⊗[ℂ] κ' ≃ₐ[ℂ] κ ⊗[ℂ] κ'` to `Algebra.TensorProduct.congr e AlgEquiv.refl`. Establish `hE : (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')).comp E.toAlgHom = Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ')`.

Apply `Algebra.TensorProduct.ext'` to reduce the goal to its premises. Introduce `g b`. Simplify using `[E, σ]`. Establish `hker : ker σ = (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))).comap (E : K ⊗[ℂ] κ' →+* κ ⊗[ℂ] κ')`. Use extensionality with `s`.

Simplify using `only [mem_ker, Ideal.mem_comap, RingHom.mem_ker]`. Rewrite using `[← hE]`. Both sides reduce to the same expression. Establish `hEs : E (∑ i, (a i : K) ⊗ₜ[ℂ] b i) = ∑ i, π (a i) ⊗ₜ[ℂ] b i`. Simplify using `[E, he]`.

Establish `hmem : (∑ i, (a i : K) ⊗ₜ[ℂ] b i) ∈ ker σ ^ M`. Establish `h1 : (∑ i, (a i : K) ⊗ₜ[ℂ] b i) = E.symm (∑ i, π (a i) ⊗ₜ[ℂ] b i)`. Rewrite using `[← hEs, AlgEquiv.symm_apply_apply]`. Establish `h2` using `Ideal.mem_map_of_mem (E.symm : κ ⊗[ℂ] κ' →+* K ⊗[ℂ] κ') hJ`. Establish `h3 : (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))).comap (E : K ⊗[ℂ] κ' →+* κ ⊗[ℂ] κ') = (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))).map (E.symm : κ ⊗[ℂ] κ' →+* K ⊗[ℂ] κ')`.

Use extensionality with `s`. Rewrite using `[Ideal.mem_comap, Ideal.mem_map_iff_of_surjective (E.symm : κ ⊗[ℂ] κ' →+* K ⊗[ℂ] κ') E.symm.surjective]`. Prove the components needed by the constructor for the conclusion. Introduce `hs`. Conclude with `⟨E s, hs, by simp⟩`.

Introduce and unpack `⟨t, ht, rfl⟩`. Simplify using `using ht`. Rewrite using `[h1, hker, h3, ← Ideal.map_pow]`. Conclude with `h2`. Use `Ideal.mem_map_of_mem (toLoc L σ) hmem` as an intermediate fact.

Rewrite `this` using `[Ideal.map_pow, map_ker]`. Conclude with `this`. Use `⟨_, 1, GlobalTheory.T.topForms_graphLocalRing_freelyGenerated σ n k' x τ' hQ.const_mem hK hκ'f hx hτ', isUnit_one, ?_⟩` and prove the remaining obligations. Rewrite using `[Submonoid.coe_one, one_smul]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp`.
-/
theorem localRing_graph_of_injective : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  Function.Injective π → (∀ g : K, ∃ a b : R, (b : K) ≠ 0 ∧ g * b = a) →
  IsLocModel (algebraMap ℂ K) R → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → 1 ≤ k →
  ∃ (Q : Subring L) (hQ : IsLocModel (algebraMap ℂ L) Q), letI := hQ.isLocalRing; ∃ z : Fin k → Q,
    IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) ∧ ringKrullDim Q = k ∧
    (∀ g : K, g ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1)) ∧
    (∀ b : κ', b ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      ∃ q : Q, IsUnit q ∧ (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) ∧
    (∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
      ∃ q : Q, (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ∧ q ∈ IsLocalRing.maximalIdeal Q ^ M) ∧
    ∃ (y : Fin (k' + n) → Q) (q : Q), IsFreeGen Q (dForm ((algebraMap ℂ L).codRestrict Q hQ.const_mem) y) ∧ IsUnit q ∧
      dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
        (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1))) = (q : L) • dForm (algebraMap ℂ L) (fun i => (y i : L)) := by
  intro K κ κ' L _ _ _ _ _ _ _ _ _ _ _ n k k' x τ' R π ρ hx hτ' hz hπc hπf hπi hRf hR hκ' hk
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_algEquiv_fractionField_of_localRingOfVarietyPoint R π hR hπc hπf hπi
  obtain ⟨z, hz⟩ := hz
  obtain rfl : n = k := GlobalTheory.T.card_transcendenceBasisOverConst_eq_of_algEquiv e n k x z hx hz
  have hK : Algebra.EssFiniteType ℂ K := GlobalTheory.T.essFiniteType_of_localRingOfVarietyPoint R hR
  obtain ⟨O', hO'⟩ := hκ'
  have hκ'f : Algebra.EssFiniteType ℂ κ' := GlobalTheory.T.essFiniteType_of_localRingOfVarietyPoint O' hO'
  set σ : K →ₐ[ℂ] κ' := ρ.comp e.toAlgHom with hσ
  have hQ : IsLocModel (algebraMap ℂ L) (loc L σ) := GlobalTheory.T.isLocalRingOfVarietyPoint_tensorGraphLocalization σ hK hκ'f
  obtain ⟨hm, hdim⟩ := GlobalTheory.T.graphLocalRing_regular_params_and_dim (L := L) σ n x hK hκ'f hx
  have hsum : ∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'),
      algebraMap (K ⊗[ℂ] κ') L (∑ i, (a i : K) ⊗ₜ[ℂ] b i) =
        ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i) := fun l a b => map_sum _ _ _
  have hprod : ∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'),
      Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ') (∑ i, (a i : K) ⊗ₜ[ℂ] b i) =
        ∑ i, ρ (π (a i)) * b i := by
    intro l a b
    simp [map_sum, σ, he]
  refine ⟨loc L σ, hQ, fun i => toLoc L σ (x i ⊗ₜ[ℂ] 1 - 1 ⊗ₜ[ℂ] σ (x i)), hm, hdim, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    refine ⟨toLoc L σ (g ⊗ₜ 1), ?_, rfl⟩
    refine IsUnit.map _ ?_
    exact ((IsUnit.mk0 g hg).map (Algebra.TensorProduct.includeLeft (R := ℂ) (S := ℂ) (B := κ')))
  · intro b hb
    refine ⟨toLoc L σ (1 ⊗ₜ b), ?_, rfl⟩
    refine IsUnit.map _ ?_
    exact ((IsUnit.mk0 b hb).map (Algebra.TensorProduct.includeRight (R := ℂ) (A := K)))
  · intro l a b hne
    refine ⟨toLoc L σ (∑ i, (a i : K) ⊗ₜ[ℂ] b i), ?_, ?_⟩
    · have hs : (∑ i, (a i : K) ⊗ₜ[ℂ] b i) ∈ (ker σ).primeCompl := by
        intro hmem
        exact hne ((hprod l a b).symm.trans hmem)
      exact IsLocalization.map_units (loc L σ) (⟨_, hs⟩ : (ker σ).primeCompl)
    · simp only [coe_toLoc]
      exact hsum l a b
  · intro M l a b hJ
    refine ⟨toLoc L σ (∑ i, (a i : K) ⊗ₜ[ℂ] b i), by simp only [coe_toLoc]; exact hsum l a b, ?_⟩
    let E : K ⊗[ℂ] κ' ≃ₐ[ℂ] κ ⊗[ℂ] κ' := Algebra.TensorProduct.congr e AlgEquiv.refl
    have hE : (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')).comp E.toAlgHom =
        Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ') := by
      apply Algebra.TensorProduct.ext'
      intro g b
      simp [E, σ]
    have hker : ker σ = (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))).comap
        (E : K ⊗[ℂ] κ' →+* κ ⊗[ℂ] κ') := by
      ext s
      simp only [mem_ker, Ideal.mem_comap, RingHom.mem_ker]
      rw [← hE]
      rfl
    have hEs : E (∑ i, (a i : K) ⊗ₜ[ℂ] b i) = ∑ i, π (a i) ⊗ₜ[ℂ] b i := by
      simp [E, he]
    have hmem : (∑ i, (a i : K) ⊗ₜ[ℂ] b i) ∈ ker σ ^ M := by
      have h1 : (∑ i, (a i : K) ⊗ₜ[ℂ] b i) = E.symm (∑ i, π (a i) ⊗ₜ[ℂ] b i) := by
        rw [← hEs, AlgEquiv.symm_apply_apply]
      have h2 := Ideal.mem_map_of_mem (E.symm : κ ⊗[ℂ] κ' →+* K ⊗[ℂ] κ') hJ
      have h3 : (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))).comap
          (E : K ⊗[ℂ] κ' →+* κ ⊗[ℂ] κ') =
          (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))).map
          (E.symm : κ ⊗[ℂ] κ' →+* K ⊗[ℂ] κ') := by
        ext s
        rw [Ideal.mem_comap, Ideal.mem_map_iff_of_surjective (E.symm : κ ⊗[ℂ] κ' →+* K ⊗[ℂ] κ')
          E.symm.surjective]
        constructor
        · intro hs
          exact ⟨E s, hs, by simp⟩
        · rintro ⟨t, ht, rfl⟩
          simpa using ht
      rw [h1, hker, h3, ← Ideal.map_pow]
      exact h2
    have := Ideal.mem_map_of_mem (toLoc L σ) hmem
    rw [Ideal.map_pow, map_ker] at this
    exact this
  · refine ⟨_, 1, GlobalTheory.T.topForms_graphLocalRing_freelyGenerated σ n k' x τ' hQ.const_mem hK hκ'f hx hτ', isUnit_one, ?_⟩
    rw [Submonoid.coe_one, one_smul]
    congr 1
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

end GlobalTheory.FieldPair
