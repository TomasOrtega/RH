import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.TransportLoc

variable {G G' : Type} [Group G] [Group G']

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_twCent_iff (e : G ≃* G') (θ : G →* G) (θ' : G' →* G') (h : ∀ x, e (θ x) = θ' (e x)) (d x : G) :
    x ∈ twCent θ d ↔ e x ∈ twCent θ' (e d) := by
  show x * d = d * θ x ↔ e x * e d = e d * θ' (e x)
  rw [← h, ← map_mul, ← map_mul, e.injective.eq_iff]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem map_twConj (e : G ≃* G') (θ : G →* G) (θ' : G' →* G') (h : ∀ x, e (θ x) = θ' (e x)) (d y : G) :
    e (y⁻¹ * d * θ y) = (e y)⁻¹ * e d * θ' (e y) := by
  simp only [map_mul, map_inv, h]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.
-/
theorem twConj_mul (θ : G →* G) (d t w : G) (ht : t ∈ twCent θ d) :
    (t * w)⁻¹ * d * θ (t * w) = w⁻¹ * d * θ w := by
  have ht' : t * d = d * θ t := ht
  rw [map_mul, _root_.mul_inv_rev]
  calc w⁻¹ * t⁻¹ * d * (θ t * θ w) = w⁻¹ * t⁻¹ * (d * θ t) * θ w := by group
    _ = w⁻¹ * d * θ w := by rw [← ht']; group

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finite_support (e : G ≃* G') (θ : G →* G) (θ' : G' →* G')
    (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ)
    (hθ : ∀ x, e (θ x) = θ' (e x)) (hK : ∀ x, x ∈ K ↔ e x ∈ K') (hf : ∀ x, f x = f' (e x))
    (hfin : {q : DoubleCoset.Quotient (twCent θ' (e d) : Set G') (K' : Set G') |
      ∃ k ∈ K', f' ((Quotient.out q * k)⁻¹ * e d * θ' (Quotient.out q * k)) ≠ 0}.Finite) :
    {q : DoubleCoset.Quotient (twCent θ d : Set G) (K : Set G) |
      ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * d * θ (Quotient.out q * k)) ≠ 0}.Finite := by
  refine Set.Finite.of_injOn
    (f := fun q : DoubleCoset.Quotient (twCent θ d : Set G) (K : Set G) =>
      DoubleCoset.mk (twCent θ' (e d)) K' (e (Quotient.out q))) ?_ ?_ hfin
  · rintro q ⟨k, hk, hne⟩
    obtain ⟨t, k₁, ht₀, hk₁, hout⟩ := DoubleCoset.mk_out_eq_mul (twCent θ' (e d)) K' (e (Quotient.out q))
    refine ⟨k₁⁻¹ * e k, K'.mul_mem (K'.inv_mem hk₁) ((hK k).1 hk), ?_⟩
    have hmul : Quotient.out (DoubleCoset.mk (twCent θ' (e d)) K' (e (Quotient.out q))) *
        (k₁⁻¹ * e k) = t * e (Quotient.out q * k) := by
      rw [hout, map_mul]; group
    simp only []
    rw [hmul, twConj_mul θ' (e d) t _ ht₀, ← map_twConj e θ θ' hθ, ← hf]
    exact hne
  · intro q₁ _ q₂ _ heq
    obtain ⟨t', ht', k', hk', hy⟩ := (DoubleCoset.eq _ _ _ _).1 heq
    have h₂ : Quotient.out q₂ = e.symm t' * Quotient.out q₁ * e.symm k' := by
      apply e.injective
      simp only [map_mul, e.apply_symm_apply]
      exact hy
    have ht : e.symm t' ∈ twCent θ d := by
      rw [mem_twCent_iff e θ θ' hθ, e.apply_symm_apply]; exact ht'
    have hk : e.symm k' ∈ K := by
      rw [hK, e.apply_symm_apply]; exact hk'
    rw [← DoubleCoset.out_eq' _ _ q₁, ← DoubleCoset.out_eq' _ _ q₂]
    exact (DoubleCoset.eq _ _ _ _).2 ⟨_, ht, _, hk, h₂⟩

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem index_ne_zero (e : G ≃* G') (K : Subgroup G) (K' : Subgroup G') (hK : ∀ x, x ∈ K ↔ e x ∈ K')
    (u : K → ℂ) (u' : K' → ℂ) (hu : ∀ k : K, u k = u' ⟨e k, (hK k).1 k.2⟩)
    (h : (rStab u').index ≠ 0) : (rStab u).index ≠ 0 := by
  let φ : K →* K' :=
    { toFun := fun k => ⟨e k, (hK k).1 k.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hφ : Function.Surjective φ := fun k' =>
    ⟨⟨e.symm k', by rw [hK, e.apply_symm_apply]; exact k'.2⟩, by ext; simp [φ]⟩
  have hu' : ∀ k : K, u k = u' (φ k) := hu
  have hstab : rStab u = (rStab u').comap φ := by
    ext k
    constructor
    · intro hk x'
      obtain ⟨x, rfl⟩ := hφ x'
      show u' (φ x * φ k) = u' (φ x)
      rw [← map_mul, ← hu', ← hu']
      exact hk x
    · intro hk x
      show u (x * k) = u x
      rw [hu', hu', map_mul]
      exact hk (φ x)
  rw [hstab, Subgroup.index_comap_of_surjective _ hφ]
  exact h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem mem_conj_iff (e : G ≃* G') (K : Subgroup G) (K' : Subgroup G') (hK : ∀ x, x ∈ K ↔ e x ∈ K') (y x : G) :
    x ∈ K.map (MulAut.conj y).toMonoidHom ↔ e x ∈ K'.map (MulAut.conj (e y)).toMonoidHom := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨e k, (hK k).1 hk, by simp [MulAut.conj_apply]⟩
  · rintro ⟨k', hk', h⟩
    refine ⟨e.symm k', by rw [SetLike.mem_coe, hK, e.apply_symm_apply]; exact hk', ?_⟩
    apply e.injective
    rw [← h]
    simp [MulAut.conj_apply]

variable [TopologicalSpace G] [TopologicalSpace G']

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isCompact_closure_zpowers_iff (e : G ≃ₜ* G') (t : G) :
    IsCompact (closure (Subgroup.zpowers t : Set G)) ↔
      IsCompact (closure (Subgroup.zpowers (e t) : Set G')) := by
  have h : (Subgroup.zpowers (e t) : Set G') = e.toHomeomorph '' (Subgroup.zpowers t : Set G) := by
    have := MonoidHom.map_zpowers e.toMulEquiv.toMonoidHom t
    exact (congrArg (fun S : Subgroup G' => (S : Set G')) this).symm
  rw [h, ← e.toHomeomorph.image_closure, e.toHomeomorph.isCompact_image]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem map_cptPart (e : G ≃ₜ* G') (T : Subgroup G) (T' : Subgroup G') (hT : ∀ x, x ∈ T ↔ e x ∈ T') :
    (cptPart T).map e.toMulEquiv.toMonoidHom = cptPart T' := by
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  ext t'
  constructor
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    exact ⟨(hT t).1 ht, (isCompact_closure_zpowers_iff e t).1 hc⟩
  · rintro ⟨ht', hc⟩
    refine ⟨e.symm t', ⟨?_, ?_⟩, e.apply_symm_apply t'⟩
    · rw [hT]; simpa using ht'
    · rw [isCompact_closure_zpowers_iff e]; simpa using hc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem locConds_of_equiv : ∀ {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (e : G ≃ₜ* G') (θ : G →* G) (θ' : G' →* G')
  (K : Subgroup G) (K' : Subgroup G') (d : G) (f : G → ℂ) (f' : G' → ℂ), (∀ x, e (θ x) = θ' (e x)) → (∀ x, x ∈ K ↔ e x ∈ K') →
  (∀ x, f x = f' (e x)) → LocConds θ' K' (e d) f' → LocConds θ K d f := by
  intro G G' _ _ _ _ e θ θ' K K' d f f' hθ hK hf h
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  have hθm : ∀ x, e.toMulEquiv (θ x) = θ' (e.toMulEquiv x) := hθ
  have hKm : ∀ x, x ∈ K ↔ e.toMulEquiv x ∈ K' := hK
  have hfm : ∀ x, f x = f' (e.toMulEquiv x) := hf
  have hT : ∀ x, x ∈ twCent θ d ↔ e.toMulEquiv x ∈ twCent θ' (e.toMulEquiv d) :=
    mem_twCent_iff e.toMulEquiv θ θ' hθm d
  refine ⟨?_, ?_, finite_support e.toMulEquiv θ θ' K K' d f f' hθm hKm hfm h₃, ?_⟩
  · intro x hx y hy
    apply e.toMulEquiv.injective
    rw [map_mul, map_mul]
    exact h₁ _ ((hT x).1 hx) _ ((hT y).1 hy)
  · intro y
    refine index_ne_zero e.toMulEquiv K K' hKm _ _ ?_ (h₂ (e y))
    intro k
    have := map_twConj e.toMulEquiv θ θ' hθm d (y * k)
    rw [hfm, this, map_mul]
    rfl
  · intro y
    obtain ⟨ha, hb⟩ := h₄ (e y)
    have hB := map_cptPart e (twCent θ d) (twCent θ' (e d)) hT
    have hA : twCent θ d ⊓ K.map (MulAut.conj y).toMonoidHom =
        (twCent θ' (e d) ⊓ K'.map (MulAut.conj (e y)).toMonoidHom).comap e.toMulEquiv.toMonoidHom := by
      ext x
      rw [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_inf]
      exact and_congr (hT x) (mem_conj_iff e.toMulEquiv K K' hKm y x)
    constructor
    · rw [hA]
      intro x hx
      have hx' := ha hx
      rw [← hB] at hx'
      obtain ⟨z, hz, hzx⟩ := hx'
      rwa [← e.toMulEquiv.injective hzx]
    · rw [hA, Subgroup.relIndex_comap, hB]
      exact hb

end GlobalTheory.CompanionTheory.TransportLoc

end
