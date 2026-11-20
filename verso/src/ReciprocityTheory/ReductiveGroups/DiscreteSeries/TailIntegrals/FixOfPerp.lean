import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.LinIndToLp

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

variable {k r : ℕ}

def sigI (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩

def sgnI (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sigI_val (i : Fin (2 * r + k + 1)) :
    (sigI k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem hpk_apply (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = sigI k r i then sgnI k r i else 0 := by
  unfold Hpk sgnI
  simp only [Fin.ext_iff, sigI_val]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem sig_sig (i : Fin (2 * r + k + 1)) : sigI k r (sigI k r i) = i := by
  apply Fin.ext; rw [sigI_val, sigI_val]; split_ifs <;> omega

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem sgn_sig (i : Fin (2 * r + k + 1)) : sgnI k r (sigI k r i) = sgnI k r i := by
  unfold sgnI; rw [sigI_val]; split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem sgn_mul_self (i : Fin (2 * r + k + 1)) : sgnI k r i * sgnI k r i = 1 := by
  unfold sgnI; split_ifs <;> norm_num

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem star_sgn (i : Fin (2 * r + k + 1)) : star (sgnI k r i) = sgnI k r i := by
  unfold sgnI; split_ifs <;> simp

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = sgnI k r i * v (sigI k r i) := by
  simp only [mulVec, dotProduct, hpk_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.
-/
theorem hpk_invol (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  funext i; rw [hpk_mulVec, hpk_mulVec, sig_sig, sgn_sig, ← mul_assoc, sgn_mul_self, one_mul]

abbrev EE (k r : ℕ) := EuclideanSpace ℂ (Fin (2 * r + k + 1))

def HE (k r : ℕ) : EE k r →ₗ[ℂ] EE k r := Matrix.toEuclideanLin (Hpk k r)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HE_apply (x : EE k r) : HE k r x = WithLp.toLp 2 (Hpk k r *ᵥ x.ofLp) := Matrix.toEuclideanLin_apply _ _

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem HE_HE (x : EE k r) : HE k r (HE k r x) = x := by
  rw [HE_apply, HE_apply, WithLp.ofLp_toLp, hpk_invol]

def sigE (k r : ℕ) : Fin (2 * r + k + 1) ≃ Fin (2 * r + k + 1) := ⟨sigI k r, sigI k r, sig_sig, sig_sig⟩

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem HE_adj (x y : EE k r) : inner ℂ (HE k r x) y = inner ℂ x (HE k r y) := by
  simp only [HE_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, hpk_mulVec, Pi.star_apply]
  refine Fintype.sum_equiv (sigE k r) _ _ (fun i => ?_)
  simp only [sigE, Equiv.coe_fn_mk, sig_sig, sgn_sig, star_mul', star_sgn]; ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem herm_eq (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = inner ℂ (WithLp.toLp 2 w : EE k r) (HE k r (WithLp.toLp 2 v)) := by
  rw [HE_apply, EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, WithLp.ofLp_toLp, herm,
    dotProduct_comm]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Evaluate the numerical expressions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation.

Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Apply the first step, then apply the next step to every resulting obligation. Rewrite the indicated hypotheses using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem fix_of_perp (c : Fin (r + 1) → EE k r) (hc : Orthonormal ℂ c)
    (hiso : ∀ a b, inner ℂ (c a) (HE k r (c b)) = 0) (x : EE k r)
    (hx1 : ∀ a, inner ℂ (c a) x = 0) (hx2 : ∀ a, inner ℂ (HE k r (c a)) x = 0) : HE k r x = x := by
  set Vm : Submodule ℂ (EE k r) := LinearMap.ker (HE k r + LinearMap.id) with hVm
  set d : Fin (r + 1) → EE k r := fun a => c a - HE k r (c a) with hd
  have hdV : ∀ a, d a ∈ Vm := fun a => by
    simp only [hVm, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, hd, map_sub, HE_HE]; abel
  have hdd : ∀ a b, inner ℂ (d a) (d b) = if a = b then 2 else 0 := by
    intro a b
    simp only [hd, inner_sub_left, inner_sub_right, HE_adj, HE_HE, hiso, orthonormal_iff_ite.1 hc]
    split_ifs <;> norm_num
  have hind : LinearIndependent ℂ d := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun a h => ?_) (fun a b hab => ?_)
    · have := hdd a a; rw [h, inner_zero_left, if_pos rfl] at this; norm_num at this
    · show inner ℂ (d a) (d b) = 0
      rw [hdd, if_neg hab]
  have hfin : Module.finrank ℂ Vm ≤ r + 1 := by
    let idx : Fin (r + 1) → Fin (2 * r + k + 1) := fun a =>
      ⟨if a.val < r then a.val else r + k, by split_ifs <;> omega⟩
    let π : Vm →ₗ[ℂ] (Fin (r + 1) → ℂ) :=
      { toFun := fun v a => (v : EE k r).ofLp (idx a)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective π := by
      refine (injective_iff_map_eq_zero π).2 fun v hv => ?_
      have hx : ∀ i, sgnI k r i * (v : EE k r).ofLp (sigI k r i) = -(v : EE k r).ofLp i := by
        intro i
        have h1 := v.2
        simp only [hVm, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply] at h1
        have h2 := congrArg (fun z : EE k r => z.ofLp i) h1
        simp only [HE_apply, WithLp.ofLp_add, WithLp.ofLp_toLp, Pi.add_apply, hpk_mulVec, WithLp.ofLp_zero,
          Pi.zero_apply] at h2
        linear_combination h2
      have h0 : ∀ i : Fin (2 * r + k + 1), i.val < r → (v : EE k r).ofLp i = 0 := by
        intro i hi
        have := congrFun hv ⟨i.val, by omega⟩
        have e : idx ⟨i.val, by omega⟩ = i := Fin.ext (by simp [idx, hi])
        change (v : EE k r).ofLp (idx ⟨i.val, by omega⟩) = 0 at this
        rwa [e] at this
      have hrk : ∀ i : Fin (2 * r + k + 1), i.val = r + k → (v : EE k r).ofLp i = 0 := by
        intro i hi
        have := congrFun hv ⟨r, by omega⟩
        have e : idx ⟨r, by omega⟩ = i := Fin.ext (by simp [idx, hi])
        change (v : EE k r).ofLp (idx ⟨r, by omega⟩) = 0 at this
        rwa [e] at this
      have hall : ∀ i, (v : EE k r).ofLp i = 0 := by
        intro i
        by_cases h1 : i.val < r
        · exact h0 i h1
        by_cases h2 : i.val = r + k
        · exact hrk i h2
        have hs := hx i
        by_cases h3 : i.val < r + k
        · have e1 : sigI k r i = i := Fin.ext (by rw [sigI_val]; split_ifs <;> omega)
          have e2 : sgnI k r i = 1 := by unfold sgnI; rw [if_neg h2]
          rw [e1, e2, one_mul] at hs
          have h4 : (2 : ℂ) * (v : EE k r).ofLp i = 0 := by linear_combination hs
          simpa using h4
        · have e3 : (sigI k r i).val < r := by rw [sigI_val]; split_ifs <;> omega
          rw [h0 _ e3, mul_zero] at hs
          exact neg_eq_zero.1 hs.symm
      apply Subtype.ext
      show (v : EE k r) = 0
      ext i
      simpa using hall i
    simpa using LinearMap.finrank_le_finrank_of_injective hinj
  have hspan : Submodule.span ℂ (Set.range d) = Vm := by
    apply Submodule.eq_of_le_of_finrank_le
    · rw [Submodule.span_le]; rintro _ ⟨a, rfl⟩; exact hdV a
    · rw [finrank_span_eq_card hind, Fintype.card_fin]; exact hfin
  have heV : x - HE k r x ∈ Vm := by
    simp only [hVm, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, map_sub, HE_HE]; abel
  rw [← hspan] at heV
  obtain ⟨coef, hcoef⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 heV
  have hxd : ∀ a, inner ℂ x (d a) = 0 := fun a => by
    rw [hd, inner_sub_right, inner_eq_zero_symm.1 (hx1 a), inner_eq_zero_symm.1 (hx2 a), sub_zero]
  have hxe : inner ℂ x (x - HE k r x) = 0 := by
    rw [← hcoef, inner_sum]; exact Finset.sum_eq_zero fun a _ => by rw [inner_smul_right, hxd, mul_zero]
  have h1 : inner ℂ (HE k r x) (x - HE k r x) = -inner ℂ x (x - HE k r x) := by
    simp only [HE_adj, map_sub, HE_HE, inner_sub_right]; ring
  have hee : inner ℂ (x - HE k r x) (x - HE k r x) = 0 := by
    rw [inner_sub_left, h1, hxe]; ring
  have := inner_self_eq_zero.1 hee
  rw [sub_eq_zero] at this; exact this.symm

end ReciprocityTheory.ChartRestriction.DS.Xi.GS
