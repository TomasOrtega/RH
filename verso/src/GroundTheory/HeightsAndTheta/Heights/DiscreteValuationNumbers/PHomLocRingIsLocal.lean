import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsHomLocRingLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Separate the alternatives or extract the components of the hypothesis. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem HomLocRingIsLocal.proof (h : HomLocRingMem.Statement.{u}) : HomLocRingIsLocal.Statement.{u} := by
  intro R _ K _ ι P W _ hW hPW
  let F := FractionRing (MRing ι R ⧸ P)
  let φ : MRing ι R →+* F := (algebraMap (MRing ι R ⧸ P) F).comp (Ideal.Quotient.mk P)
  have hφ : ∀ a, φ a = 0 ↔ a ∈ P := by
    intro a
    simp only [φ, RingHom.comp_apply]
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hne : ∀ a, a ∉ W → φ a ≠ 0 := fun a ha h0 => ha (hPW ((hφ a).1 h0))
  have key : ∀ (b : K → ℕ) (f g : MRing ι R), IsMultiHomog f b → IsMultiHomog g b → g ∉ W →
      ∀ hz : φ f / φ g ∈ homLocRing P W, IsUnit (⟨_, hz⟩ : homLocRing P W) ↔ f ∉ W := by
    intro b f g hf hg hgW hz
    constructor
    · rintro ⟨u, hu⟩ hfW
      obtain ⟨b', f', g', -, -, hg'W, hw⟩ :=
        (h R K ι P W hW hPW ((u⁻¹ : (homLocRing P W)ˣ) : homLocRing P W)).1 (u⁻¹ : (homLocRing P W)ˣ).1.2
      have h1 : (φ f / φ g) * (φ f' / φ g') = 1 := by
        have e := congrArg Subtype.val u.mul_inv
        rw [Subring.coe_mul, hu, Subring.coe_one] at e
        rw [← e]
        congr 1
        exact hw.symm
      have h2 : φ (f * f' - g * g') = 0 := by
        rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (hne g hgW) (hne g' hg'W))] at h1
        rw [map_sub, map_mul, map_mul, h1, sub_self]
      have h3 : f * f' - g * g' ∈ W := hPW ((hφ _).1 h2)
      have h4 : g * g' ∈ W := by
        have := W.sub_mem (W.mul_mem_right f' hfW) h3
        simpa using this
      rcases hW.mem_or_mem h4 with h5 | h5
      exacts [hgW h5, hg'W h5]
    · intro hfW
      have hgf : φ g / φ f ∈ homLocRing P W := Subring.subset_closure ⟨b, g, f, hg, hf, hfW, rfl⟩
      refine IsUnit.of_mul_eq_one ⟨_, hgf⟩ ?_
      apply Subtype.ext
      rw [Subring.coe_mul, Subring.coe_one]
      rw [div_mul_div_comm, mul_comm (φ f) (φ g)]
      exact div_self (mul_ne_zero (hne g hgW) (hne f hfW))
  refine ⟨?_, key⟩
  have hnu : ∀ z : homLocRing P W, ¬ IsUnit z → ∃ (b : K → ℕ) (f g : MRing ι R),
      IsMultiHomog f b ∧ IsMultiHomog g b ∧ g ∉ W ∧ f ∈ W ∧ (z : F) = φ f / φ g := by
    intro z hz
    obtain ⟨b, f, g, hf, hg, hgW, hzfg⟩ := (h R K ι P W hW hPW z).1 z.2
    refine ⟨b, f, g, hf, hg, hgW, ?_, hzfg⟩
    by_contra hfW
    have hmem : φ f / φ g ∈ homLocRing P W := hzfg ▸ z.2
    have e : z = ⟨_, hmem⟩ := Subtype.ext hzfg
    exact hz (e ▸ (key b f g hf hg hgW hmem).2 hfW)
  refine IsLocalRing.of_nonunits_add ?_
  intro x y hx hy
  obtain ⟨b₁, f₁, g₁, hf₁, hg₁, hg₁W, hf₁W, hx'⟩ := hnu x hx
  obtain ⟨b₂, f₂, g₂, hf₂, hg₂, hg₂W, hf₂W, hy'⟩ := hnu y hy
  have hnum : IsMultiHomog (f₁ * g₂ + f₂ * g₁) (b₁ + b₂) :=
    IsWeightedHomogeneous.add (IsWeightedHomogeneous.mul hf₁ hg₂)
      (by rw [add_comm]; exact IsWeightedHomogeneous.mul hf₂ hg₁)
  have hden : IsMultiHomog (g₁ * g₂) (b₁ + b₂) := IsWeightedHomogeneous.mul hg₁ hg₂
  have hdenW : g₁ * g₂ ∉ W := fun h5 => (hW.mem_or_mem h5).elim hg₁W hg₂W
  have hsum : ((x + y : homLocRing P W) : F) = φ (f₁ * g₂ + f₂ * g₁) / φ (g₁ * g₂) := by
    rw [Subring.coe_add, hx', hy', div_add_div _ _ (hne g₁ hg₁W) (hne g₂ hg₂W), map_add, map_mul, map_mul,
      map_mul, mul_comm (φ g₁) (φ f₂)]
  have hmem : φ (f₁ * g₂ + f₂ * g₁) / φ (g₁ * g₂) ∈ homLocRing P W := hsum ▸ (x + y).2
  have e : x + y = ⟨_, hmem⟩ := Subtype.ext hsum
  rw [mem_nonunits_iff, e, key (b₁ + b₂) _ _ hnum hden hdenW hmem, not_not]
  exact W.add_mem (W.mul_mem_right _ hf₁W) (W.mul_mem_right _ hf₂W)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
