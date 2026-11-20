import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.IsSemisimpleRing
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.ContinuousQZ

noncomputable section

open Matrix GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Four.Alg

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Four

variable {k : Type} [Field k] {n : ℕ}

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem qZ_add (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x y : Matrix (Fin n) (Fin n) k) :
    qZ Z (x + y) = qZ Z x + qZ Z y := by
  funext i
  simp [qZ, mul_add, trace_add]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem qZ_sub (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x y : Matrix (Fin n) (Fin n) k) :
    qZ Z (x - y) = qZ Z x - qZ Z y := by
  funext i
  simp [qZ, mul_sub, trace_sub]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem qZ_smul (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (a : k) (x : Matrix (Fin n) (Fin n) k) :
    qZ Z (a • x) = a • qZ Z x := by
  funext i
  simp [qZ, mul_smul_comm, trace_smul]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem trace_eq_zero_of_qZ (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {d : Matrix (Fin n) (Fin n) k}
    (h : qZ Z d = 0) {b : Matrix (Fin n) (Fin n) k} (hb : b ∈ Z) : trace (b * d) = 0 := by
  have e : (∑ i, (Module.finBasis k Z).repr ⟨b, hb⟩ i • ((Module.finBasis k Z i : Z) : Matrix (Fin n) (Fin n) k)) = b := by
    have h1 := congrArg Subtype.val ((Module.finBasis k Z).sum_repr ⟨b, hb⟩)
    rw [AddSubmonoidClass.coe_finset_sum] at h1
    simp only [SetLike.val_smul] at h1
    exact h1
  rw [← e, Finset.sum_mul, trace_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [smul_mul_assoc, trace_smul]
  have := congrFun h i
  simp only [qZ, Pi.zero_apply] at this
  rw [this, smul_zero]

variable [CharZero k]

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem qZ_inj {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) {c c' : Matrix (Fin n) (Fin n) k}
    (hc : c ∈ Z) (hc' : c' ∈ Z) (h : qZ Z c = qZ Z c') : c = c' := by
  have h0 : qZ Z (c - c') = 0 := by rw [qZ_sub, h, sub_self]
  exact sub_eq_zero.1 (trZ_nondeg hZ (Z.sub_mem hc hc') fun b hb => trace_eq_zero_of_qZ Z h0 hb)

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem qZ_surj {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) (y : Fin (Module.finrank k Z) → k) :
    ∃ c ∈ Z, qZ Z c = y := by
  let Q : Z →ₗ[k] (Fin (Module.finrank k Z) → k) :=
    { toFun := fun c => qZ Z c
      map_add' := fun a b => qZ_add Z a b
      map_smul' := fun a b => qZ_smul Z a b }
  have hinj : Function.Injective Q := fun a b h => Subtype.ext (qZ_inj hZ a.2 b.2 h)
  have hsurj : Function.Surjective Q :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨c, hc⟩ := hsurj y
  exact ⟨c, c.2, hc⟩

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem piZ_spec {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) (x : Matrix (Fin n) (Fin n) k) :
    piZ Z x ∈ Z ∧ qZ Z (piZ Z x) = qZ Z x := by
  have h := qZ_surj hZ (qZ Z x)
  unfold piZ
  rw [dif_pos h]
  exact h.choose_spec

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem piZ_mem {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) (x : Matrix (Fin n) (Fin n) k) :
    piZ Z x ∈ Z := (piZ_spec hZ x).1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem qZ_piZ {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) (x : Matrix (Fin n) (Fin n) k) :
    qZ Z (piZ Z x) = qZ Z x := (piZ_spec hZ x).2

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem piZ_eq {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) {x c : Matrix (Fin n) (Fin n) k}
    (hc : c ∈ Z) (h : qZ Z c = qZ Z x) : piZ Z x = c :=
  qZ_inj hZ (piZ_mem hZ x) hc ((qZ_piZ hZ x).trans h.symm)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem piZ_of_mem {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) {c : Matrix (Fin n) (Fin n) k}
    (hc : c ∈ Z) : piZ Z c = c := piZ_eq hZ hc rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem piZ_add {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) (x y : Matrix (Fin n) (Fin n) k) :
    piZ Z (x + y) = piZ Z x + piZ Z y :=
  piZ_eq hZ (Z.add_mem (piZ_mem hZ x) (piZ_mem hZ y)) (by rw [qZ_add, qZ_add, qZ_piZ hZ, qZ_piZ hZ])

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem piZ_sub {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) (x y : Matrix (Fin n) (Fin n) k) :
    piZ Z (x - y) = piZ Z x - piZ Z y :=
  piZ_eq hZ (Z.sub_mem (piZ_mem hZ x) (piZ_mem hZ y)) (by rw [qZ_sub, qZ_sub, qZ_piZ hZ, qZ_piZ hZ])

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem piZ_smul {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) (a : k) (x : Matrix (Fin n) (Fin n) k) :
    piZ Z (a • x) = a • piZ Z x :=
  piZ_eq hZ (Z.smul_mem (piZ_mem hZ x) a) (by rw [qZ_smul, qZ_smul, qZ_piZ hZ])

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem piZ_eq_sum {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) :
    ∃ cb : Fin (Module.finrank k Z) → Matrix (Fin n) (Fin n) k, ∀ x, piZ Z x = ∑ i, qZ Z x i • cb i := by
  choose cb hcb hq using fun i => qZ_surj hZ (Pi.single i 1)
  refine ⟨cb, fun x => piZ_eq hZ (Z.sum_mem fun i _ => Z.smul_mem (hcb i) _) ?_⟩
  funext j
  have : qZ Z (∑ i, qZ Z x i • cb i) = ∑ i, qZ Z x i • qZ Z (cb i) := by
    funext l
    simp [qZ, Finset.mul_sum, trace_sum, mul_smul_comm, trace_smul, Finset.sum_apply]
  rw [this]
  simp [hq, Finset.sum_apply, Pi.single_apply]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem continuous_piZ {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) : Continuous (piZ Z) := by
  obtain ⟨cb, hcb⟩ := piZ_eq_sum hZ
  have : piZ Z = fun x => ∑ i, qZ Z x i • cb i := funext hcb
  rw [this]
  exact continuous_finset_sum _ fun i _ => ((continuous_apply i).comp (continuous_qZ Z)).smul continuous_const

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem sig_sig {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) (s t : kˣ) (hst : (s : k) * t = 1)
    (p : Sp k n) : sig Z s (sig Z t p) = p := by
  have hp : piZ Z (sig Z t p).1 = piZ Z p.1 := by
    simp only [sig]
    rw [piZ_add hZ, piZ_smul hZ, piZ_sub hZ, piZ_of_mem hZ (piZ_mem hZ _), sub_self, smul_zero, add_zero]
  ext : 1
  · simp only [sig] at hp ⊢
    rw [hp, add_sub_cancel_left, smul_smul, hst, one_smul, add_sub_cancel]
  · rfl

def sigH {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) (t : kˣ) : Sp k n ≃ₜ Sp k n where
  toFun := sig Z t
  invFun := sig Z t⁻¹
  left_inv p := sig_sig hZ t⁻¹ t (by simp) p
  right_inv p := sig_sig hZ t t⁻¹ (by simp) p
  continuous_toFun := by
    have h := continuous_piZ hZ
    show Continuous fun p : Sp k n => (piZ Z p.1 + ((t : kˣ) : k) • (p.1 - piZ Z p.1), p.2)
    exact ((h.comp continuous_fst).add ((continuous_const (y := ((t : kˣ) : k))).smul
      (continuous_fst.sub (h.comp continuous_fst)))).prodMk continuous_snd
  continuous_invFun := by
    have h := continuous_piZ hZ
    show Continuous fun p : Sp k n => (piZ Z p.1 + ((t⁻¹ : kˣ) : k) • (p.1 - piZ Z p.1), p.2)
    exact ((h.comp continuous_fst).add ((continuous_const (y := ((t⁻¹ : kˣ) : k))).smul
      (continuous_fst.sub (h.comp continuous_fst)))).prodMk continuous_snd

omit [CharZero k] in
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem act_act (g h : GL (Fin n) k) (p : Sp k n) : act g (act h p) = act (g * h) p := by
  simp only [act, _root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec, mul_assoc]

omit [CharZero k] in

def actH (g : GL (Fin n) k) : Sp k n ≃ₜ Sp k n where
  toFun := act g
  invFun := act g⁻¹
  left_inv p := by rw [act_act, inv_mul_cancel]; simp [act]
  right_inv p := by rw [act_act, mul_inv_cancel]; simp [act]
  continuous_toFun := ((continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const).prodMk
    (continuous_const.matrix_mulVec continuous_snd)
  continuous_invFun := ((continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const).prodMk
    (continuous_const.matrix_mulVec continuous_snd)

omit [CharZero k] in
/- English proof (translation)
Supply the required witnesses or components.
-/
theorem comp_mem {f : Sp k n → ℂ} (hf : f ∈ supportedIn (Set.univ : Set (Sp k n))) (e : Sp k n ≃ₜ Sp k n) :
    (fun q => f (e q)) ∈ supportedIn (Set.univ : Set (Sp k n)) :=
  ⟨⟨hf.1.1.comp_continuous e.continuous, hf.1.2.comp_homeomorph e⟩, Set.subset_univ _⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem compP : CompP (k := k) := by
  intro n Z hZ
  refine ⟨fun t f hf => comp_mem hf (sigH hZ t), fun g f hf => comp_mem hf (actH g), ?_, ?_⟩
  · rintro t ⟨x, v⟩ ⟨hx, -⟩
    refine ⟨fun a ha => ?_, Set.mem_univ _⟩
    have hc : a * piZ Z x = piZ Z x * a := hZ.1 _ ha _ (piZ_mem hZ x)
    have hx' : a * x = x * a := hx a ha
    simp only [sig, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, hc, hx']
  · rintro g hg ⟨x, v⟩ ⟨hx, -⟩
    refine ⟨fun a ha => ?_, Set.mem_univ _⟩
    have h1 : a * g.val = g.val * a := hg a ha
    have h2 : g⁻¹.val * a = a * g⁻¹.val := by
      calc g⁻¹.val * a = g⁻¹.val * a * (g.val * g⁻¹.val) := by rw [Units.mul_inv, mul_one]
        _ = g⁻¹.val * (a * g.val) * g⁻¹.val := by simp only [mul_assoc]
        _ = g⁻¹.val * (g.val * a) * g⁻¹.val := by rw [h1]
        _ = a * g⁻¹.val := by rw [← mul_assoc, Units.inv_mul, one_mul]
    show a * (g.val * x * g⁻¹.val) = g.val * x * g⁻¹.val * a
    rw [← mul_assoc, ← mul_assoc, h1, mul_assoc g.val a x, hx a ha, mul_assoc, mul_assoc, mul_assoc, h2]
    simp only [mul_assoc]

end PositivityTheory.RgUd.T.Nil.Four.Alg
