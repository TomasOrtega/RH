import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongOfCongOnFixed
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne Pointwise

namespace GlobalTheory.InertiaLift

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w _ L ψ hψ hL`. Use `letI : TopologicalSpace (IntCl E Ω) := ⊥`. Use `haveI : DiscreteTopology (IntCl E Ω) := ⟨rfl⟩`. Use `haveI := continuousSMul_intCl E Ω`. Set `H` to `L.fixingSubgroup`.

Establish `hH : IsClosed (H : Set (Ω ≃ₐ[E] Ω))`. Establish `e : (H : Set (Ω ≃ₐ[E] Ω)) = ⋂ x : L, ((MulAction.stabilizer (Ω ≃ₐ[E] Ω) (x : Ω) : Subgroup (Ω ≃ₐ[E] Ω)) : Set (Ω ≃ₐ[E] Ω))`. Use extensionality with `σ`. Simplify using `only [Set.mem_iInter, SetLike.mem_coe, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`.

Conclude with `⟨fun h x => h x x.2, fun h x hx => h ⟨x, hx⟩⟩`. Rewrite using `[e]`. Conclude with `isClosed_iInter fun x => (MulAction.stabilizer (Ω ≃ₐ[E] Ω) (x : Ω)).isClosed_of_isOpen (stabilizer_isOpen_of_isIntegral (K := E) (x : Ω))`. Use `haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact`. Set `Q` to `primeBelow (F := E) A`.

Set `R'` to `FixedPoints.subalgebra (𝓞 E) (IntCl E Ω) H`. Establish `hR' : ∀ b : R', ∀ k ∈ H, k • (b : IntCl E Ω) = b` using `fun b k hk => b.2 ⟨k, hk⟩`. Establish `: SMulCommClass H R' (IntCl E Ω)` using `⟨fun k r b => by`. Express the relevant statement in the definitionally equal form `(k : Ω ≃ₐ[E] Ω) • ((r : IntCl E Ω) * b) = (r : IntCl E Ω) * (k : Ω ≃ₐ[E] Ω) • b`. Rewrite using `[smul_mul', hR' r k k.2]⟩`.

Establish `: Algebra.IsInvariant R' (IntCl E Ω) H` using `⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩`. Establish `: Q.LiesOver (Q.under R')` using `⟨rfl⟩`. Establish `hψQ : ψ • Q = Q`. Establish `h1 : ψ • A = A` using `hψ`. Rewrite using `[← primeBelow_smul, h1]`.

Establish `hfix : ∀ r : R', ψ • (r : IntCl E Ω) - r ∈ Q`. Introduce `r`. Establish `hrL : ((r : IntCl E Ω) : Ω) ∈ L`. Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]`. Introduce `f hf`.

Conclude with `congrArg Subtype.val (hR' r f hf)`. Conclude with `hL _ hrL (isIntegral_int_of_isIntegral (r : IntCl E Ω).2)`. Set `φ : (IntCl E Ω ⧸ Q) ≃ₐ[R' ⧸ Q.under R'] (IntCl E Ω ⧸ Q)` to `AlgEquiv.ofRingEquiv (f := Ideal.quotientEquiv Q Q (MulSemiringAction.toRingEquiv (Ω ≃ₐ[E] Ω) (IntCl E Ω) ψ) hψQ.symm) (fun r => by`. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective r`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk Q (ψ • (r : IntCl E Ω)) = Ideal.Quotient.mk Q (r : IntCl E Ω)`.

Rewrite using `[Ideal.Quotient.eq]`. Conclude with `hfix r)`. Take `⟨⟨v, hvQ⟩, hv⟩` from `Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H) (Q.under R') Q φ`. Use `⟨ψ * (v : Ω ≃ₐ[E] Ω)⁻¹, GlobalTheory.InertiaMovesRoot.mem_Ine_of_cong fun b => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1 : Ideal.Quotient.mk Q ((v : Ω ≃ₐ[E] Ω) • ((v : Ω ≃ₐ[E] Ω)⁻¹ • b)) = Ideal.Quotient.mk Q (ψ • ((v : Ω ≃ₐ[E] Ω)⁻¹ • b))` using `DFunLike.congr_fun hv (Ideal.Quotient.mk Q ((v : Ω ≃ₐ[E] Ω)⁻¹ • b))`.

Rewrite `h1` using `[smul_inv_smul, eq_comm, Ideal.Quotient.eq]`. Rewrite using `[mul_smul]` and apply the resulting hypothesis. Establish `hv' : ((v : Ω ≃ₐ[E] Ω)⁻¹) x = x` using `(IntermediateField.mem_fixingSubgroup_iff L _).mp (H.inv_mem v.2) x hx`. Rewrite using `[AlgEquiv.mul_apply, hv']`.
-/
theorem exists_mem_Ine_eq_on : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w →
    ∀ (L : IntermediateField E Ω) (ψ : G E Ω), ψ ∈ Dec (F := E) A →
    (∀ x ∈ L, IsIntegral ℤ x → A.valuation (ψ x - x) < 1) →
    ∃ ι ∈ Ine (F := E) A, ∀ x ∈ L, ι x = ψ x := by
  intro E Ω _ _ _ _ _ A w _ L ψ hψ hL
  letI : TopologicalSpace (IntCl E Ω) := ⊥
  haveI : DiscreteTopology (IntCl E Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl E Ω
  let H := L.fixingSubgroup
  have hH : IsClosed (H : Set (Ω ≃ₐ[E] Ω)) := by
    have e : (H : Set (Ω ≃ₐ[E] Ω)) = ⋂ x : L, ((MulAction.stabilizer (Ω ≃ₐ[E] Ω) (x : Ω) :
        Subgroup (Ω ≃ₐ[E] Ω)) : Set (Ω ≃ₐ[E] Ω)) := by
      ext σ
      simp only [Set.mem_iInter, SetLike.mem_coe, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      rw [IntermediateField.mem_fixingSubgroup_iff]
      exact ⟨fun h x => h x x.2, fun h x hx => h ⟨x, hx⟩⟩
    rw [e]
    exact isClosed_iInter fun x =>
      (MulAction.stabilizer (Ω ≃ₐ[E] Ω) (x : Ω)).isClosed_of_isOpen
        (stabilizer_isOpen_of_isIntegral (K := E) (x : Ω))
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  let Q := primeBelow (F := E) A
  let R' := FixedPoints.subalgebra (𝓞 E) (IntCl E Ω) H
  have hR' : ∀ b : R', ∀ k ∈ H, k • (b : IntCl E Ω) = b := fun b k hk => b.2 ⟨k, hk⟩
  have : SMulCommClass H R' (IntCl E Ω) := ⟨fun k r b => by
    change (k : Ω ≃ₐ[E] Ω) • ((r : IntCl E Ω) * b) = (r : IntCl E Ω) * (k : Ω ≃ₐ[E] Ω) • b
    rw [smul_mul', hR' r k k.2]⟩
  have : Algebra.IsInvariant R' (IntCl E Ω) H := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  have : Q.LiesOver (Q.under R') := ⟨rfl⟩
  have hψQ : ψ • Q = Q := by
    have h1 : ψ • A = A := hψ
    rw [← primeBelow_smul, h1]
  have hfix : ∀ r : R', ψ • (r : IntCl E Ω) - r ∈ Q := by
    intro r
    have hrL : ((r : IntCl E Ω) : Ω) ∈ L := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
      intro f hf
      exact congrArg Subtype.val (hR' r f hf)
    exact hL _ hrL (isIntegral_int_of_isIntegral (r : IntCl E Ω).2)
  let φ : (IntCl E Ω ⧸ Q) ≃ₐ[R' ⧸ Q.under R'] (IntCl E Ω ⧸ Q) := AlgEquiv.ofRingEquiv
    (f := Ideal.quotientEquiv Q Q (MulSemiringAction.toRingEquiv (Ω ≃ₐ[E] Ω) (IntCl E Ω) ψ)
      hψQ.symm)
    (fun r => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      change Ideal.Quotient.mk Q (ψ • (r : IntCl E Ω)) = Ideal.Quotient.mk Q (r : IntCl E Ω)
      rw [Ideal.Quotient.eq]
      exact hfix r)
  obtain ⟨⟨v, hvQ⟩, hv⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H)
    (Q.under R') Q φ
  refine ⟨ψ * (v : Ω ≃ₐ[E] Ω)⁻¹, GlobalTheory.InertiaMovesRoot.mem_Ine_of_cong fun b => ?_, fun x hx => ?_⟩
  · have h1 : Ideal.Quotient.mk Q ((v : Ω ≃ₐ[E] Ω) • ((v : Ω ≃ₐ[E] Ω)⁻¹ • b)) =
        Ideal.Quotient.mk Q (ψ • ((v : Ω ≃ₐ[E] Ω)⁻¹ • b)) :=
      DFunLike.congr_fun hv (Ideal.Quotient.mk Q ((v : Ω ≃ₐ[E] Ω)⁻¹ • b))
    rw [smul_inv_smul, eq_comm, Ideal.Quotient.eq] at h1
    rwa [mul_smul]
  · have hv' : ((v : Ω ≃ₐ[E] Ω)⁻¹) x = x :=
      (IntermediateField.mem_fixingSubgroup_iff L _).mp (H.inv_mem v.2) x hx
    rw [AlgEquiv.mul_apply, hv']

end GlobalTheory.InertiaLift
