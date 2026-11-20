import Mathlib
import Formalism.PeriodIntegrals.ScRefExists

noncomputable section

open NumberField Formalism.MainNotions.S
open scoped TensorProduct

namespace PI.ScRefExists.GlueA

variable (I : Formalism.MainNotions.S.AutInst)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem inclE_tmul (a : I.E) : Formalism.UG.inclE (F := I.F) (Af I.F) a = a ⊗ₜ[I.F] (1 : Af I.F) := rfl

/- English proof (translation)
Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem star_int (t : 𝓞 I.E) : star (t : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range := by
  have h : IsIntegral ℤ (star (t : I.E)) :=
    (NumberField.RingOfIntegers.isIntegral_coe t).map (starRingEnd I.E).toIntAlgHom
  exact ⟨⟨star (t : I.E), h⟩, rfl⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem inclE_mem {a : I.E} (ha : a ∈ (algebraMap (𝓞 I.E) I.E).range) :
    Formalism.UG.inclE (F := I.F) (Af I.F) a ∈ IntAf I.F I.E := by
  rw [inclE_tmul]
  exact Subring.subset_closure (Set.mem_union_left _ ⟨⟨a, ha⟩, rfl⟩)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem inclE_mem' (t : 𝓞 I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) (t : I.E) ∈ IntAf I.F I.E := inclE_mem I ⟨t, rfl⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem sigA_inclE (a : I.E) :
    sigA I (Formalism.UG.inclE (F := I.F) (Af I.F) a) = Formalism.UG.inclE (F := I.F) (Af I.F) (star a) := by
  rw [inclE_tmul, inclE_tmul]
  first
    | exact Algebra.TensorProduct.map_tmul _ _ _ _
    | rfl

/- English proof (translation)
Establish an intermediate fact. Treat this case separately. Treat this case separately. Proceed by induction. Treat this case separately.

Treat this case separately. Treat this case separately.
-/
theorem sigA_sigA (x : (I.E ⊗[I.F] Af I.F)) : sigA I (sigA I x) = x := by
  have e : ∀ (c : I.E) (d : Af I.F), sigA I (c ⊗ₜ[I.F] d) = star c ⊗ₜ[I.F] d := fun c d => by
    first
      | exact Algebra.TensorProduct.map_tmul _ _ _ _
      | rfl
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b => rw [e, e, star_star]
  | add y z hy hz => rw [map_add, map_add, hy, hz]

/- English proof (translation)
Establish an intermediate fact. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sigA_mem {x : (I.E ⊗[I.F] Af I.F)} (hx : x ∈ IntAf I.F I.E) : sigA I x ∈ IntAf I.F I.E := by
  have e1 : ∀ r : Af I.F, sigA I ((1 : I.E) ⊗ₜ[I.F] r) = (1 : I.E) ⊗ₜ[I.F] r := fun r => by
    first
      | simp only [sigA, Formalism.UG.sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.map_tmul, map_one, AlgHom.coe_id, id_eq]
      | (show Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) ((1 : I.E) ⊗ₜ[I.F] r) = _
         rw [Algebra.TensorProduct.map_tmul, map_one]
         rfl)
      | simp [sigA, Formalism.UG.sigR]
  have h : IntAf I.F I.E ≤ (IntAf I.F I.E).comap (sigA I) := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro y (⟨⟨e, he⟩, rfl⟩ | ⟨⟨r, hr⟩, rfl⟩)
    · show sigA I (e ⊗ₜ[I.F] (1 : Af I.F)) ∈ IntAf I.F I.E
      rw [← inclE_tmul, sigA_inclE]
      obtain ⟨t, rfl⟩ := he
      exact inclE_mem I (star_int I t)
    · show sigA I ((1 : I.E) ⊗ₜ[I.F] (r : Af I.F)) ∈ IntAf I.F I.E
      rw [e1]
      exact Subring.subset_closure (Set.mem_union_right _ ⟨⟨r, hr⟩, rfl⟩)
  exact h hx

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem natCast_eq (m : ℕ) : (m : (I.E ⊗[I.F] Af I.F)) = Formalism.UG.inclE (F := I.F) (Af I.F) (m : I.E) := by
  rw [map_natCast]

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hA_add_left (x y z : VA I) : hA I (x + y) z = hA I x z + hA I y z := by
  simp only [hA, Formalism.UG.hform, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, map_add]
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hA_add_right (x y z : VA I) : hA I x (y + z) = hA I x y + hA I x z := by
  simp only [hA, Formalism.UG.hform, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply]
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hA_smul_left (c : (I.E ⊗[I.F] Af I.F)) (x y : VA I) : hA I (c • x) y = sigA I c * hA I x y := by
  simp only [hA, Formalism.UG.hform, sigA, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hA_smul_right (c : (I.E ⊗[I.F] Af I.F)) (x y : VA I) : hA I x (c • y) = c * hA I x y := by
  simp only [hA, Formalism.UG.hform, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hA_zero_left (y : VA I) : hA I 0 y = 0 := by
  simp [hA, Formalism.UG.hform]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hA_zero_right (x : VA I) : hA I x 0 = 0 := by
  simp [hA, Formalism.UG.hform]

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hA_neg_left (x y : VA I) : hA I (-x) y = - hA I x y := by
  simp only [hA, Formalism.UG.hform, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.neg_apply, map_neg]
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hA_neg_right (x y : VA I) : hA I x (-y) = - hA I x y := by
  simp only [hA, Formalism.UG.hform, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.neg_apply]
  ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem incl_apply (x : Fin I.n → I.E) (i : Fin I.n) :
    incl I x i = Formalism.UG.inclE (F := I.F) (Af I.F) (x i) := rfl

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem incl_add (x y : Fin I.n → I.E) : incl I (x + y) = incl I x + incl I y := by
  funext i
  simp only [incl, Pi.add_apply, map_add]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem incl_sub (x y : Fin I.n → I.E) : incl I (x - y) = incl I x - incl I y := by
  funext i
  simp only [incl, Pi.sub_apply, map_sub]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem incl_neg (x : Fin I.n → I.E) : incl I (-x) = - incl I x := by
  funext i
  simp only [incl, Pi.neg_apply, map_neg]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem incl_zero : incl I 0 = 0 := by
  funext i
  simp only [incl, Pi.zero_apply, map_zero]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem incl_smul (c : I.E) (x : Fin I.n → I.E) :
    incl I (c • x) = Formalism.UG.inclE (F := I.F) (Af I.F) c • incl I x := by
  funext i
  simp only [incl, Pi.smul_apply, smul_eq_mul, map_mul]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem incl_nsmul (m : ℕ) (x : Fin I.n → I.E) : incl I (m • x) = (m : (I.E ⊗[I.F] Af I.F)) • incl I x := by
  funext i
  simp only [incl, Pi.smul_apply, nsmul_eq_mul, smul_eq_mul, map_mul, map_natCast]

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem hA_incl (x y : Fin I.n → I.E) :
    hA I (incl I x) (incl I y) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  simp only [hA, Formalism.UG.hform, incl, Matrix.map_apply, map_sum, map_mul, starRingEnd_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := sigA_inclE I (x i)
  simp only [sigA] at h
  rw [h]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem incl_mem_Lf {x : Fin I.n → I.E} (hx : x ∈ I.L) : incl I x ∈ I.Lf := Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hG_int {x y : Fin I.n → I.E} (hx : x ∈ I.L) (hy : y ∈ I.L) :
    Formalism.UG.hform (starRingEnd I.E) I.J x y ∈ (algebraMap (𝓞 I.E) I.E).range := (I.L_dual y).mp hy x hx

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem smul_mem_Lf {c : (I.E ⊗[I.F] Af I.F)} (hc : c ∈ IntAf I.F I.E) {x : VA I} (hx : x ∈ I.Lf) : c • x ∈ I.Lf := Submodule.smul_mem _ (⟨c, hc⟩ : IntAf I.F I.E) hx

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Proceed by induction. Treat this case separately.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result.

Treat this case separately. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hA_Lf {x y : VA I} (hx : x ∈ I.Lf) (hy : y ∈ I.Lf) : hA I x y ∈ IntAf I.F I.E := by
  have key : ∀ a ∈ I.L, ∀ w ∈ I.Lf, hA I (incl I a) w ∈ IntAf I.F I.E := by
    intro a ha w hw
    change w ∈ Submodule.span (IntAf I.F I.E) _ at hw
    induction hw using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨⟨b, hb⟩, rfl⟩ := hz
        show hA I (incl I a) (incl I b) ∈ IntAf I.F I.E
        rw [hA_incl]
        exact inclE_mem I (hG_int I ha hb)
    | zero => rw [hA_zero_right]; exact zero_mem _
    | add u v _ _ hu hv => rw [hA_add_right]; exact add_mem hu hv
    | smul c u _ hu =>
        show hA I (incl I a) ((c : I.E ⊗[I.F] Af I.F) • u) ∈ IntAf I.F I.E
        rw [hA_smul_right]
        exact mul_mem c.2 hu
  change x ∈ Submodule.span (IntAf I.F I.E) _ at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨⟨a, ha⟩, rfl⟩ := hz
      exact key a ha y hy
  | zero => rw [hA_zero_left]; exact zero_mem _
  | add u v _ _ hu hv => rw [hA_add_left]; exact add_mem hu hv
  | smul c u _ hu =>
      show hA I ((c : I.E ⊗[I.F] Af I.F) • u) y ∈ IntAf I.F I.E
      rw [hA_smul_left]
      exact mul_mem (sigA_mem I c.2) hu

end PI.ScRefExists.GlueA

end
