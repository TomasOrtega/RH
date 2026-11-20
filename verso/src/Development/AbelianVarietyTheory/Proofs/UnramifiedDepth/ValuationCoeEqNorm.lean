import Mathlib
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.DualLattices.ExistsPrimitiveRoot

open Ideal

namespace GlobalTheory.PadicComplexHost

variable (p : ℕ) [hp : Fact p.Prime]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem valuation_coe_eq_norm (x : ℂ_[p]) : ((Valued.v x : NNReal) : ℝ) = ‖x‖ := by
  rw [PadicComplex.norm_eq_norm, Valued.v.norm_def, PadicComplex.RankOne.hom_eq_embedding,
    Valuation.embedding_restrict]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem norm_p : ‖((p : ℕ) : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [← valuation_coe_eq_norm, PadicComplex.valuation_p]; simp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem inv_p_lt_one : (p : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. A detailed English derivation is pending.
-/
theorem mem_iff_norm (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [← valuation_coe_eq_norm]
  change Valued.v x ≤ 1 ↔ _
  exact_mod_cast Iff.rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem not_isUnit_p : ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p]) := by
  intro h
  have h1 := (PadicComplexInt.integers p).one_of_isUnit h
  rw [map_natCast] at h1
  have h2 := valuation_coe_eq_norm p ((p : ℕ) : ℂ_[p])
  rw [h1, norm_p] at h2
  have := inv_p_lt_one p
  rw [← h2] at this
  simp at this

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem smodEq_iff (n : ℕ) (x y : 𝓞_ℂ_[p]) :
    x ≡ y [SMOD ((span {((p : ℕ) : 𝓞_ℂ_[p])}) ^ n • ⊤ : Submodule 𝓞_ℂ_[p] 𝓞_ℂ_[p])] ↔
      ‖(x : ℂ_[p]) - (y : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ n := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
    Ideal.mem_span_singleton, (PadicComplexInt.integers p).dvd_iff_le, map_pow, map_natCast,
    ← norm_p, ← norm_pow, ← valuation_coe_eq_norm, ← valuation_coe_eq_norm, NNReal.coe_le_coe]
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tendsto_inv_p_pow :
    Filter.Tendsto (fun n : ℕ => (p : ℝ)⁻¹ ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_p_lt_one p)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem isHausdorff : IsHausdorff (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] := by
  refine ⟨fun x hx => ?_⟩
  have h : ∀ n : ℕ, ‖(x : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ n := fun n => by
    simpa using (smodEq_iff p n x 0).1 (hx n)
  have h0 : ‖(x : ℂ_[p])‖ ≤ 0 :=
    ge_of_tendsto (tendsto_inv_p_pow p) (Filter.Eventually.of_forall h)
  exact Subtype.ext (norm_le_zero_iff.1 h0)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem isPrecomplete : IsPrecomplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] := by
  refine ⟨fun f hf => ?_⟩
  have h : ∀ {m n : ℕ}, m ≤ n → ‖(f m : ℂ_[p]) - (f n : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ m :=
    fun hmn => (smodEq_iff p _ _ _).1 (hf hmn)
  have hc : CauchySeq fun n => (f n : ℂ_[p]) := by
    refine cauchySeq_of_le_geometric (p : ℝ)⁻¹ 1 (inv_p_lt_one p) fun n => ?_
    rw [dist_eq_norm, one_mul]
    exact h (Nat.le_succ n)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  have hm : ∀ m : ℕ, ‖(f m : ℂ_[p]) - L‖ ≤ (p : ℝ)⁻¹ ^ m := fun m =>
    le_of_tendsto ((tendsto_const_nhds.sub hL).norm)
      ((Filter.eventually_ge_atTop m).mono fun n hn => h hn)
  have hLO : L ∈ 𝓞_ℂ_[p] := by
    rw [mem_iff_norm]
    exact le_of_tendsto hL.norm
      (Filter.Eventually.of_forall fun n => (mem_iff_norm p _).1 (f n).2)
  exact ⟨⟨L, hLO⟩, fun n => (smodEq_iff p n _ _).2 (hm n)⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isAdicComplete : IsAdicComplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] :=
  { isHausdorff p, isPrecomplete p with }

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem main : ∀ (p : ℕ) [Fact p.Prime], ∃ (_ : Fact ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p])) (_ : IsAdicComplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p])
    (ε : PreTilt 𝓞_ℂ_[p] p), (Valued.v : Valuation ℂ_[p] NNReal).Integers 𝓞_ℂ_[p] ∧
      IsPrimitiveRoot (((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm ε).untilt) p := by
  intro p _
  have h1 : Fact ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p]) := ⟨not_isUnit_p p⟩
  have h2 := isAdicComplete p
  obtain ⟨ε, hε⟩ := ReciprocityTheory.PGsh.exists_eps (p := p) ℂ_[p] Valued.v 𝓞_ℂ_[p]
    (PadicComplexInt.integers p)
  exact ⟨h1, h2, ε, PadicComplexInt.integers p, hε⟩

end GlobalTheory.PadicComplexHost
