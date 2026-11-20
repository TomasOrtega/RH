import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Express the relevant assertion in an equivalent form by its definition.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Apply function extensionality and compare values at an arbitrary argument. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Normalize the expressions using the abelian group laws. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.

Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Reduce the conclusion to the remaining proof obligations.

Express the relevant assertion in an equivalent form by its definition. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem fnMap_h2_bijective (C : Type 1) [Category.{0} C] (K : Cx C) (h11 : K.M1.Ac1) (h12 : K.M1.Ac2)
    (h20 : K.M2.Ac0) (h21 : K.M2.Ac1) (h30 : K.M3.Ac0) : Function.Bijective K.fnMap.h2 := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
    change (QuotientAddGroup.mk (K.fnMap.z2 a) : (Cx.single K.M0).H2) = 0 at hc
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range] at hc
    obtain ⟨⟨f, ω0⟩, hf⟩ := hc
    have hz : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''),
        K.M0.map ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ = a.1.1 T T' T'' φ ψ := by
      intro T T' T'' φ ψ
      have := congrArg (fun x => x.1 T T' T'' φ ψ) hf
      simp [Cx.D1, Cx.fnMap, CxMap.z2, CxMap.p2] at this
      exact this
    have ha := a.2
    obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
    obtain ⟨ω, hω⟩ := h11 (fun T T' φ => a.1.2.1 T T' φ + K.d0 T' (f T T' φ)) (by
      intro T T' T'' φ ψ
      rw [ha2 T T' T'' φ ψ, ← hz T T' T'' φ ψ]
      simp only [map_add, map_sub, K.diffZero_natural]
      abel)
    have hη : (fun T => a.1.2.2 T - K.d1 T (ω T)) = 0 := by
      apply h20
      intro T T' φ
      have e := hω T T' φ
      have e2 : a.1.2.1 T T' φ = ω T' - K.M1.map φ (ω T) - K.d0 T' (f T T' φ) := by
        rw [← e]; abel
      rw [ha3 T T' φ, e2]
      simp only [map_sub, K.diffOne_diffZero, K.diffOne_natural]
      abel
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]
    refine ⟨(f, ω), ?_⟩
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext T T' T'' φ ψ
      exact hz T T' T'' φ ψ
    · funext T T' φ
      have e := hω T T' φ
      change ω T' - K.M1.map φ (ω T) - K.d0 T' (f T T' φ) = _
      rw [← e]; abel
    · funext T
      have e := congrFun hη T
      change K.d1 T (ω T) = _
      simp only [Pi.zero_apply, sub_eq_zero] at e
      exact e.symm
  · intro c
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨hb1, -, -, -⟩ := b.2
    obtain ⟨f, hf⟩ := h12 (fun T T' T'' φ ψ => K.d0 T'' (b.1.1 T T' T'' φ ψ)) (by
      intro T T' T'' T''' φ ψ χ
      rw [← K.diffZero_natural, ← map_add, hb1, map_add])
    obtain ⟨g, hg⟩ := h21 (fun T T' φ => K.d1 T' (-f T T' φ)) (by
      intro T T' T'' φ ψ
      have e := hf T T' T'' φ ψ
      have e2 : f T T'' (φ ≫ ψ) = K.M1.map ψ (f T T' φ) + f T' T'' ψ - K.d0 T'' (b.1.1 T T' T'' φ ψ) := by
        rw [e]; abel
      rw [e2]
      simp only [map_neg, map_add, map_sub, K.diffOne_diffZero, K.diffOne_natural]
      abel)
    have h3 : (fun T => K.d2 T (g T)) = 0 := by
      apply h30
      intro T T' φ
      have e := hg T T' φ
      have e2 : g T' = K.M2.map φ (g T) + K.d1 T' (-f T T' φ) := by rw [e]; abel
      rw [e2, map_add, K.diffTwo_comp_diffOne, add_zero, K.diffTwo_natural]
    let a : K.Z2 := ⟨(b.1.1, fun T T' φ => -f T T' φ, g), by
      refine ⟨hb1, fun T T' T'' φ ψ => ?_, fun T T' φ => ?_, fun T => ?_⟩
      · rw [hf T T' T'' φ ψ]; simp only [map_neg, map_sub, map_add]; abel
      · have e := hg T T' φ
        change g T' = K.M2.map φ (g T) + K.d1 T' (-f T T' φ)
        rw [e]; abel
      · exact congrFun h3 T⟩
    refine ⟨QuotientAddGroup.mk a, ?_⟩
    change (QuotientAddGroup.mk (K.fnMap.z2 a) : (Cx.single K.M0).H2) = QuotientAddGroup.mk b
    congr 1
