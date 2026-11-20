import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdHomeoSymmApplySnd
open MeasureTheory

namespace GlobalTheory.Cusp.Shear

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isFundamentalDomain_image_prod : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) (hle : N' ≤ N), (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
      (Λ : AddSubgroup V) (s : V → G) (π : N → V)
      (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
      (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N'),
      (∀ v w, s (v + w) = s v * s w) → (∀ v ∈ Λ, s v ∈ Γ) → (∀ a : N, (a : G) ∈ Γ → π a ∈ Λ) →
      ∀ (A : Set N') (B : Set V), MeasurableSet A → MeasurableSet B →
      (∀ m : N', ∃! δ : Γ.subgroupOf N', (δ : N') * m ∈ A) → (∀ v : V, ∃! w : Λ, (w : V) + v ∈ B) →
      ∀ ν : MeasureTheory.Measure N, MeasureTheory.IsFundamentalDomain (Γ.subgroupOf N)
        (GlobalTheory.Cusp.Shear.prodHomeo hle hs hsc hπc hπmul hπs hker '' (A ×ˢ B)) ν := by
  intro G _ _ _ _ _ _ Γ N N' hle hn V _ _ _ _ _ Λ s π hs hsc hπc hπmul hπs hker hsadd hsΓ hπΓ
    A B hAm hBm hA hB ν
  set e := prodHomeo hle hs hsc hπc hπmul hπs hker with he
  have himg : e '' (A ×ˢ B) = e.symm ⁻¹' (A ×ˢ B) := by
    ext n; constructor
    · rintro ⟨z, hz, rfl⟩; simpa using hz
    · intro h; exact ⟨e.symm n, h, by simp⟩
  have efst : ∀ n : N, (((e.symm n).1 : N') : G) = (n : G) * (s (π n))⁻¹ := fun n => rfl
  have esnd : ∀ n : N, (e.symm n).2 = π n := fun n => rfl
  refine IsFundamentalDomain.mk' ?_ ?_
  · rw [himg]; exact (e.symm.continuous.measurable (hAm.prod hBm)).nullMeasurableSet
  · intro x
    have hmemS : ∀ n : N, n ∈ e '' (A ×ˢ B) ↔ (e.symm n).1 ∈ A ∧ (e.symm n).2 ∈ B := by
      intro n; rw [himg]; rfl
    have hfst : ∀ g : N, (((e.symm (g * x)).1 : N') : G) =
        (g : G) * (s (π g))⁻¹ * (s (π g) * ((x : G) * (s (π x))⁻¹) * (s (π g))⁻¹) := by
      intro g
      rw [efst, hπmul, hsadd]
      simp only [Subgroup.coe_mul]
      group
    have hsnd : ∀ g : N, (e.symm (g * x)).2 = π g + π x := fun g => by rw [esnd, hπmul]
    let c : V → N' := fun w => ⟨s w * ((x : G) * (s (π x))⁻¹) * (s w)⁻¹,
      hn (s w) (hs w) _ (mul_inv_mem hs hπmul hπs hker x)⟩
    obtain ⟨w, hwB, hwu⟩ := hB (π x)
    obtain ⟨δ, hδA, hδu⟩ := hA (c w)
    have hδΓ : ((δ : N') : G) ∈ Γ := Subgroup.mem_subgroupOf.1 δ.2
    let γ0 : Γ.subgroupOf N := ⟨⟨((δ : N') : G) * s w, N.mul_mem (hle (δ : N').2) (hs w)⟩,
      Subgroup.mem_subgroupOf.2 (Γ.mul_mem hδΓ (hsΓ w w.2))⟩
    have hπγ0 : π (γ0 : N) = w := by
      have h : (γ0 : N) = ⟨((δ : N') : G), hle (δ : N').2⟩ * ⟨s w, hs w⟩ := rfl
      rw [h, hπmul, hπs ⟨s w, hs w⟩ w rfl, (hker _).2 (δ : N').2, zero_add]
    refine ⟨γ0, ?_, ?_⟩
    · show (γ0 : N) * x ∈ _
      rw [hmemS, hsnd, hπγ0]
      refine ⟨?_, hwB⟩
      have h : (e.symm ((γ0 : N) * x)).1 = (δ : N') * c w := by
        apply Subtype.ext
        rw [hfst, hπγ0]
        show ((δ : N') : G) * s w * (s w)⁻¹ * _ = ((δ : N') : G) * (s w * ((x : G) * (s (π x))⁻¹) * (s w)⁻¹)
        group
      rw [h]; exact hδA
    · intro γ hγ
      have hγ' : (γ : N) * x ∈ e '' (A ×ˢ B) := hγ
      rw [hmemS, hsnd] at hγ'
      obtain ⟨hγA, hγB⟩ := hγ'
      have hγΓ : ((γ : N) : G) ∈ Γ := Subgroup.mem_subgroupOf.1 γ.2
      have hw : (⟨π (γ : N), hπΓ γ hγΓ⟩ : Λ) = w := hwu _ hγB
      have hwv : π (γ : N) = w := congrArg Subtype.val hw
      have hδN' : ((γ : N) : G) * (s w)⁻¹ ∈ N' := hwv ▸ mul_inv_mem hs hπmul hπs hker γ
      let δγ : Γ.subgroupOf N' := ⟨⟨((γ : N) : G) * (s w)⁻¹, hδN'⟩,
        Subgroup.mem_subgroupOf.2 (Γ.mul_mem hγΓ (Γ.inv_mem (hsΓ w w.2)))⟩
      have h : (δγ : N') * c w = (e.symm ((γ : N) * x)).1 := by
        apply Subtype.ext
        rw [hfst, hwv]
        rfl
      have hδe : δγ = δ := hδu δγ (by show (δγ : N') * c w ∈ A; rw [h]; exact hγA)
      have hv : ((γ : N) : G) * (s w)⁻¹ = ((δ : N') : G) := by
        rw [← hδe]
      apply Subtype.ext; apply Subtype.ext
      show ((γ : N) : G) = ((δ : N') : G) * s w
      rw [← hv]; group

end GlobalTheory.Cusp.Shear
