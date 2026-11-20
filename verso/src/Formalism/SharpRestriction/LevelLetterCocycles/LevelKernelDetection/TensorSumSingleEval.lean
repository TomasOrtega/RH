import Formalism.SharpRestriction.LevelLetterCocycles.FinalLevelsOf

noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

section Free

variable {LL D ι : Type} [Field LL] [AddCommGroup D] [Module LL D] [Fintype ι] [DecidableEq ι]

def evK (i : ι) : (ι → LL) ⊗[LL] D →ₗ[LL] D :=
  (TensorProduct.lid LL D).toLinearMap ∘ₗ LinearMap.rTensor D (LinearMap.proj i)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem evaluation_tmul (i : ι) (b : ι → LL) (d : D) : evK i (b ⊗ₜ[LL] d) = b i • d := by
  simp [evK]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately.
-/
theorem evaluation_smul (i : ι) (a : ι → LL) (z : (ι → LL) ⊗[LL] D) :
    evK i (a • z) = a i • evK i z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b d =>
    rw [TensorProduct.smul_tmul', evaluation_tmul, evaluation_tmul, smul_eq_mul, Pi.mul_apply,
      mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Rewrite the conclusion repeatedly using the stated equalities. Treat this case separately. Simplify using the standard rewrite rules.
-/
theorem tensor_sum_single_eval (z : (ι → LL) ⊗[LL] D) :
    z = ∑ i, (Pi.single i (1 : LL) : ι → LL) ⊗ₜ[LL] evK i z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b d =>
    have hb : ∑ i, b i • (Pi.single i (1 : LL) : ι → LL) = b := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    simp_rw [evaluation_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, hb]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Proceed by induction.

Treat this case separately. Extract witnesses or component facts from the available result. Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Treat this case separately.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_baseChange_iff (X : Submodule LL D) (z : (ι → LL) ⊗[LL] D) :
    z ∈ X.baseChange (ι → LL) ↔ ∀ i, evK i z ∈ X := by
  constructor
  · intro h i
    have h' : z ∈ Submodule.span (ι → LL)
        ((X.map (TensorProduct.mk LL (ι → LL) D 1) : Submodule LL _) : Set ((ι → LL) ⊗[LL] D)) := by
      rw [← Submodule.baseChange_eq_span]; exact h
    clear h
    induction h' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, hm, rfl⟩ := hx
      simpa [evaluation_tmul] using hm
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact X.add_mem hx hy
    | smul a x _ hx => rw [evaluation_smul]; exact X.smul_mem _ hx
  · intro h
    rw [tensor_sum_single_eval z]
    exact Submodule.sum_mem _ fun i _ => Submodule.tmul_mem_baseChange_of_mem _ (h i)

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem xi_iff (X : ℤ → Submodule LL D) (f : Amb LL (ι → LL) D) :
    f ∈ Xi (ι → LL) X ↔ ∀ i k, evK i (cf f k) ∈ X k := by
  change (∀ k, cf f k ∈ (X k).baseChange (ι → LL)) ↔ _
  simp only [mem_baseChange_iff]
  exact forall_comm

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem xi_unit_tp (X : ℤ → Submodule LL D) (hX : Monotone X) (a b : PowerSeries (ι → LL)) (hab : a * b = 1)
    (g : ℤ) (f : Amb LL (ι → LL) D) :
    (HahnSeries.ofPowerSeries ℤ (ι → LL) a * tp (ι → LL) g) • f ∈ Xi (ι → LL) X ↔
      f ∈ Xi (ι → LL) (fun i => X (i + g)) := by
  rw [mul_smul, ← xi_shift_holds LL (ι → LL) D X g f]
  constructor
  · intro h
    have h2 := xi_module_structure LL (ι → LL) D X hX b _ h
    rwa [← mul_smul, ← map_mul, show b * a = 1 by rw [mul_comm]; exact hab, map_one, one_smul] at h2
  · intro h
    exact xi_module_structure LL (ι → LL) D X hX a _ h

end Free

end Formalism.MainNotions.N.Ln03.K8
