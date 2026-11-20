import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PAwayHeightOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Consider separately whether the proposition holds or fails. Supply the required witnesses or components. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Both sides reduce to the same expression.

Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem ChartBundlesAgree.lat_le (hHOI : HeightOneIntersection.Statement)
    {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
    {E : Type} [AddCommGroup E] [Module Ω E] (B B' : ChartBundle o x r E) (i : τ) (hi : x i ≠ 0)
    (hN : IsNoetherianRing (chartRing o x i)) (hIC : IsIntegrallyClosed (chartRing o x i))
    (h1 : ∀ v ∈ B.lat i, ∃ s : chartRing o x i, s ≠ 0 ∧ (s : Ω) • v ∈ B'.lat i)
    (hq : ∀ q : Ideal (chartRing o x i), q.IsPrime → q.height = 1 → ∀ v : E,
      (∃ s : chartRing o x i, s ∉ q ∧ (s : Ω) • v ∈ B.lat i) →
        ∃ s : chartRing o x i, s ∉ q ∧ (s : Ω) • v ∈ B'.lat i) :
    B.lat i ≤ B'.lat i := by
  intro v hv
  let A := chartRing o x i
  let J : Ideal A :=
    { carrier := {a | (a : Ω) • v ∈ B'.lat i}
      add_mem' := fun {a b} ha hb => by
        change ((a + b : A) : Ω) • v ∈ B'.lat i
        rw [Subalgebra.coe_add, add_smul]
        exact add_mem ha hb
      zero_mem' := by
        change ((0 : A) : Ω) • v ∈ B'.lat i
        rw [Subalgebra.coe_zero, zero_smul]
        exact zero_mem _
      smul_mem' := fun c a ha => by
        change ((c * a : A) : Ω) • v ∈ B'.lat i
        rw [Subalgebra.coe_mul, mul_smul]
        exact B'.stable i c c.2 _ ha }
  have hJ : ∀ a : A, a ∈ J ↔ (a : Ω) • v ∈ B'.lat i := fun _ => Iff.rfl
  obtain ⟨k, f, c, hf, hc, hsum, hb⟩ := B'.frame i hi
  have hfJ : ∀ l, (⟨f l, hf l⟩ : A) ∈ J.radical := by
    intro l
    obtain ⟨b, hli, hsp, hiff⟩ := hb l
    obtain ⟨n, hn⟩ : ∃ n : ℕ, f l ^ n • v ∈ B'.lat i := by
      by_cases hf0 : f l = 0
      · exact ⟨1, by rw [hf0, pow_one, zero_smul]; exact zero_mem _⟩
      · let bs := Module.Basis.mk hli (by rw [hsp])
        have hbs : ∀ q, bs q = b q := fun q => Module.Basis.mk_apply hli _ q
        let a := bs.equivFun v

        have coord : ∀ t : A, (t : Ω) • v ∈ B'.lat i →
            ∀ q, ∃ n : ℕ, f l ^ n * ((t : Ω) * a q) ∈ A := by
          intro t ht q
          obtain ⟨a', ha', he⟩ := (hiff ((t : Ω) • v)).1 ⟨0, by rw [pow_zero, one_smul]; exact ht⟩
          have e1 : bs.equivFun ((t : Ω) • v) = a' := by
            rw [he]
            simp_rw [← hbs]
            rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
          have e2 : a' q = (t : Ω) * a q := by
            rw [← e1, LinearEquiv.map_smul]
            rfl
          rw [← e2]
          exact ha' q
        refine (hiff v).2 ⟨a, fun q => ?_, ?_⟩
        · have hh : (⟨f l, hf l⟩ : A) ≠ 0 := fun e => hf0 (congrArg Subtype.val e)
          obtain ⟨m, g, hg⟩ := mem_away_of_heightOne hHOI A Ω Subtype.val_injective
            ⟨f l, hf l⟩ hh (a q)
            (by
              obtain ⟨s, hs0, hs⟩ := h1 v hv
              obtain ⟨n, hn⟩ := coord s hs q
              refine ⟨s, hs0, n, ⟨_, hn⟩, ?_⟩
              change f l ^ n * (s : Ω) * a q = f l ^ n * ((s : Ω) * a q)
              ring)
            (fun P hP hP1 _ => by
              have hv1 : ∃ s : A, s ∉ P ∧ (s : Ω) • v ∈ B.lat i :=
                ⟨1, fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h), by
                  rw [OneMemClass.coe_one, one_smul]; exact hv⟩
              obtain ⟨t, htP, ht⟩ := hq P hP hP1 v hv1
              obtain ⟨n, hn⟩ := coord t ht q
              refine ⟨t, htP, n, ⟨_, hn⟩, ?_⟩
              change f l ^ n * (t : Ω) * a q = f l ^ n * ((t : Ω) * a q)
              ring)
          refine ⟨m, ?_⟩
          have hg' : f l ^ m * a q = (g : Ω) := hg
          rw [hg']
          exact g.2
        · rw [← bs.sum_equivFun v]
          simp_rw [hbs]
          rfl
    exact ⟨n, (hJ _).2 (by rw [SubmonoidClass.coe_pow]; exact hn)⟩
  have h1J : (1 : A) ∈ J.radical := by
    have e : (1 : A) = ∑ l, (⟨c l, hc l⟩ : A) * ⟨f l, hf l⟩ := by
      apply Subtype.ext
      rw [OneMemClass.coe_one, ← hsum, AddSubmonoidClass.coe_finsetSum]
      rfl
    rw [e]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hfJ l)
  have hJtop : J = ⊤ := Ideal.radical_eq_top.1 ((Ideal.eq_top_iff_one _).2 h1J)
  have h1 : (1 : A) ∈ J := hJtop ▸ Submodule.mem_top
  have h1' := (hJ 1).1 h1
  rwa [OneMemClass.coe_one, one_smul] at h1'

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem ChartBundlesAgree.proof (hHOI : HeightOneIntersection.Statement) :
    ChartBundlesAgree.Statement := by
  intro o _ Ω _ _ τ x r E _ _ B B' i hi hN hIC h1 h2 hq
  exact le_antisymm
    (ChartBundlesAgree.lat_le hHOI B B' i hi hN hIC h1 fun q hq' hq1 v => (hq q hq' hq1 v).1)
    (ChartBundlesAgree.lat_le hHOI B' B i hi hN hIC h2 fun q hq' hq1 v => (hq q hq' hq1 v).2)

end

end GroundTheory.Heights₂.Heights.Model
