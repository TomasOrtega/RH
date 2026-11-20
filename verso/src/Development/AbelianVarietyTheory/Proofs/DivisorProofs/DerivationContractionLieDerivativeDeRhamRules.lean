import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] (v : Derivation R B B)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem indLeft {P : DR R B → Prop} (h : ∀ b : B, P (algebraMap B _ b)) (ha : ∀ x y, P x → P y → P (x + y))
    (hm : ∀ (ω : Ω[B⁄R]) x, P x → P (ι1 ω * x)) (x : DR R B) : P x :=
  CliffordAlgebra.left_induction (P := P) 0 h ha (fun x m hx ↦ hm m x hx) x

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem ctr_algebraMap (b : B) : ctr v (algebraMap B (DR R B) b) = 0 := by
  simp [ctr]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem ctr_ι (ω : Ω[B⁄R]) : ctr v (ι1 ω) = algebraMap B (DR R B) (v.liftKaehlerDifferential ω) := by
  simp [ctr]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ctr_ι_mul (ω : Ω[B⁄R]) (x : DR R B) :
    ctr v (ι1 ω * x) = v.liftKaehlerDifferential ω • x - ι1 ω * ctr v x :=
  CliffordAlgebra.contractLeft_ι_mul _ _ _

/- English proof (translation)
Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Normalize the expressions using the abelian group laws.

Treat this case separately. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.
-/
theorem ctr_mul (x y : DR R B) : ctr v (x * y) = ctr v x * y + sgn x * ctr v y := by
  induction x using indLeft with
  | h b =>
    rw [← Algebra.smul_def, map_smul, ctr_algebraMap, zero_mul, zero_add, AlgHom.commutes, Algebra.smul_def]
  | ha x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, map_add, add_mul, add_mul]; abel
  | hm ω x ih =>
    rw [mul_assoc, ctr_ι_mul, ih, ctr_ι_mul, map_mul, sgn_ι]
    simp only [mul_add, sub_mul, smul_mul_assoc, mul_assoc, neg_mul]
    abel

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ctr_ctr (x : DR R B) : ctr v (ctr v x) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft _ _

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.
-/
theorem ctr_sgn (x : DR R B) : ctr v (sgn x) = -sgn (ctr v x) := by
  induction x using indLeft with
  | h b => rw [AlgHom.commutes, ctr_algebraMap, map_zero, neg_zero]
  | ha x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add, neg_add]
  | hm ω x ih =>
    rw [map_mul, sgn_ι, neg_mul, map_neg, ctr_ι_mul, ih, ctr_ι_mul, map_sub, map_smul, map_mul, sgn_ι, mul_neg, neg_mul]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Split into cases according to the possible forms of the given data. Treat this case separately.

Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Treat this case separately.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem ctr_mem_pred {n : ℕ} {x : DR R B} (hx : x ∈ ⋀[B]^n Ω[B⁄R]) : ctr v x ∈ ⋀[B]^(n - 1) Ω[B⁄R] := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap b => rw [ctr_algebraMap]; exact zero_mem _
  | add x y i _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mem_mul m hm i x hx ih =>
    obtain ⟨ω, rfl⟩ := hm
    change ctr v (ι1 ω * x) ∈ _
    rw [ctr_ι_mul, Nat.succ_sub_one]
    refine sub_mem (Submodule.smul_mem _ _ hx) ?_
    cases i with
    | zero =>
      change x ∈ LinearMap.range _ ^ 0 at hx
      rw [pow_zero] at hx
      obtain ⟨b, rfl⟩ := Submodule.mem_one.1 hx
      rw [ctr_algebraMap, mul_zero]; exact zero_mem _
    | succ k =>
      have := mul_mem (ι_mem ω) ih
      rwa [Nat.add_sub_cancel, add_comm] at this

/- English proof (translation)
Simplify to obtain the desired conclusion from the available facts.
-/
theorem ctr_mem {j : ℕ} {x : DR R B} (hx : x ∈ ⋀[B]^(j + 1) Ω[B⁄R]) : ctr v x ∈ ⋀[B]^j Ω[B⁄R] := by
  simpa using ctr_mem_pred v hx

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lie_apply (x : DR R B) : lie v x = dDR R B (ctr v x) + ctr v (dDR R B x) := rfl

/- English proof (translation)
Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.
-/
theorem lie_mul (x y : DR R B) : lie v (x * y) = lie v x * y + x * lie v y := by
  simp only [lie_apply, ctr_mul, dDR_mul, map_add, ctr_sgn, dDR_sgn, sgn_sgn, map_neg, neg_mul, add_mul, mul_add]
  abel

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem lie_algebraMap (b : B) : lie v (algebraMap B (DR R B) b) = algebraMap B (DR R B) (v b) := by
  rw [lie_apply, ctr_algebraMap, map_zero, zero_add, dDR_algebraMap, ctr_ι,
    Derivation.liftKaehlerDifferential_comp_D]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem lie_D (b : B) : lie v (ι1 (D R B b)) = ι1 (D R B (v b)) := by
  rw [lie_apply, ctr_ι, Derivation.liftKaehlerDifferential_comp_D, dDR_algebraMap, dDR_D, map_zero, add_zero]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem lie_dDR (x : DR R B) : lie v (dDR R B x) = dDR R B (lie v x) := by
  rw [lie_apply, lie_apply, dDR_dDR, map_zero, add_zero, map_add, dDR_dDR, zero_add]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem lie_ctr (x : DR R B) : lie v (ctr v x) = ctr v (lie v x) := by
  rw [lie_apply, lie_apply, ctr_ctr, map_zero, zero_add, map_add, ctr_ctr, add_zero]

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Treat this case separately.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lie_mem {j : ℕ} {x : DR R B} (hx : x ∈ ⋀[B]^j Ω[B⁄R]) : lie v x ∈ ⋀[B]^j Ω[B⁄R] := by
  cases j with
  | zero =>
    have hx' := hx
    change x ∈ LinearMap.range _ ^ 0 at hx'
    rw [pow_zero] at hx'
    obtain ⟨b, rfl⟩ := Submodule.mem_one.1 hx'
    rw [lie_algebraMap]
    change _ ∈ LinearMap.range _ ^ 0
    rw [pow_zero]; exact Submodule.algebraMap_mem _
  | succ k =>
    rw [lie_apply]
    exact add_mem (dDR_mem (ctr_mem v hx)) (ctr_mem v (dDR_mem hx))

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem ctr_lie_rules : (∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (v : Derivation R B B), (∀ b, ctr v (algebraMap B (DR R B) b) = 0) ∧ (∀ ω, ctr v (ι1 ω) = algebraMap B (DR R B) (v.liftKaehlerDifferential ω)) ∧ (∀ x y, ctr v (x * y) = ctr v x * y + sgn x * ctr v y) ∧ (∀ x, ctr v (ctr v x) = 0) ∧ (∀ x, ctr v (sgn x) = -sgn (ctr v x)) ∧ ∀ (j : ℕ), ∀ x ∈ ⋀[B]^(j + 1) Ω[B⁄R], ctr v x ∈ ⋀[B]^j Ω[B⁄R]) ∧ ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (v : Derivation R B B), (∀ x y, lie v (x * y) = lie v x * y + x * lie v y) ∧ (∀ b, lie v (algebraMap B (DR R B) b) = algebraMap B (DR R B) (v b)) ∧ (∀ b, lie v (ι1 (D R B b)) = ι1 (D R B (v b))) ∧ (∀ x, lie v (dDR R B x) = dDR R B (lie v x)) ∧ (∀ x, lie v (ctr v x) = ctr v (lie v x)) ∧ ∀ (j : ℕ), ∀ x ∈ ⋀[B]^j Ω[B⁄R], lie v x ∈ ⋀[B]^j Ω[B⁄R] :=
  ⟨fun _ _ _ _ _ v ↦ ⟨ctr_algebraMap v, ctr_ι v, ctr_mul v, ctr_ctr v, ctr_sgn v, fun _ _ hx ↦ ctr_mem v hx⟩,
    fun _ _ _ _ _ v ↦ ⟨lie_mul v, lie_algebraMap v, lie_D v, lie_dDR v, lie_ctr v, fun _ _ hx ↦ lie_mem v hx⟩⟩

end GlobalTheory.PDForm
