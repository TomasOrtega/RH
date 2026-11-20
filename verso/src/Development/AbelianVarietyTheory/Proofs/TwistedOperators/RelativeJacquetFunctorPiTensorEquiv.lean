import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeJacquetPiExteriorTensorEquivNormalized

open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory.JacPiTensor (qlift mk_qlift descend descend_mk)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RelJacTensor

section Spec

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  (e' : ∀ i, (Σ j, c i j) ≃ m i) {X : α → Type} [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a))

/- English proof (translation)
Rewrite using `[piTensor_tprod]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = a`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem piTensor_mulSingle (a : α) (g : GL (m a) k) (x : ∀ j, X j) :
    piTensor ρ (Pi.mulSingle a g) (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ (Function.update x a (ρ a g (x a))) := by
  rw [piTensor_tprod]
  congr 1
  funext j
  by_cases h : j = a
  · subst h
    simp
  · simp [h]

def qf : MultilinearMap ℂ X (Jacquet (piTensor ρ) (relUnip k e')) :=
  (twKer (piTensor ρ) (relUnip k e') 1).mkQ.compMultilinearMap (PiTensorProduct.tprod ℂ)

/- English proof (translation)
Unfold `twKer at hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨n, y, rfl⟩` from `hz`. Establish `hu : (Pi.mulSingle (M` using `fun a => GL (m a) k) i (n : GL (m i) k)) ∈ relUnip k e' := by`.

Simplify using `only [relUnip, Subgroup.mem_pi]`. Introduce `j _`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `using n.2`.

Rewrite using `[Pi.mulSingle_eq_of_ne h]`. Conclude with `one_mem _`. Establish `h1 : PiTensorProduct.tprod ℂ (Function.update v i (ρ i (n : GL (m i) k) y)) = piTensor ρ (Pi.mulSingle (M` using `fun a => GL (m a) k) i (n : GL (m i) k)) (PiTensorProduct.tprod ℂ (Function.update v i y)) := by`. Rewrite using `[piTensor_mulSingle]`. Simplify using the standard rewrite rules.

Rewrite using `[qf, LinearMap.compMultilinearMap_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, MonoidHom.one_apply, Units.val_one, one_smul, MultilinearMap.map_update_sub, h1]`. Conclude with `Submodule.subset_span ⟨⟨_, hu⟩, PiTensorProduct.tprod ℂ (Function.update v i y), by simp⟩`. Consider the case `zero => simp [qf]`. Consider the case `add z z' _ _ hz hz' => rw [MultilinearMap.map_update_add, hz, hz', add_zero]`. Consider the case `smul r z _ hz => rw [MultilinearMap.map_update_smul, hz, smul_zero]`.
-/
theorem qf_update (v : ∀ a, X a) (i : α) (w : X i)
    (hw : w ∈ twKer (ρ i) (unipRad k (e' i)) 1) : qf e' ρ (Function.update v i w) = 0 := by
  unfold twKer at hw
  induction hw using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨n, y, rfl⟩ := hz
    have hu : (Pi.mulSingle (M := fun a => GL (m a) k) i (n : GL (m i) k)) ∈ relUnip k e' := by
      simp only [relUnip, Subgroup.mem_pi]
      intro j _
      by_cases h : j = i
      · subst h
        simpa using n.2
      · rw [Pi.mulSingle_eq_of_ne h]
        exact one_mem _
    have h1 : PiTensorProduct.tprod ℂ (Function.update v i (ρ i (n : GL (m i) k) y)) =
        piTensor ρ (Pi.mulSingle (M := fun a => GL (m a) k) i (n : GL (m i) k))
          (PiTensorProduct.tprod ℂ (Function.update v i y)) := by
      rw [piTensor_mulSingle]
      simp
    rw [qf, LinearMap.compMultilinearMap_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      MonoidHom.one_apply, Units.val_one, one_smul, MultilinearMap.map_update_sub, h1]
    exact Submodule.subset_span ⟨⟨_, hu⟩, PiTensorProduct.tprod ℂ (Function.update v i y), by simp⟩
  | zero => simp [qf]
  | add z z' _ _ hz hz' => rw [MultilinearMap.map_update_add, hz, hz', add_zero]
  | smul r z _ hz => rw [MultilinearMap.map_update_smul, hz, smul_zero]

end Spec

section Spec2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  (e' : ∀ i, (Σ j, c i j) ≃ m i) {X : α → Type} [∀ a, AddCommGroup (X a)]
  [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a))

def qmap : (⨂[ℂ] a, X a) →ₗ[ℂ] ⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a)) :=
  PiTensorProduct.map fun a => (twKer (ρ a) (unipRad k (e' a)) 1).mkQ

/- English proof (translation)
Simplify using `only [qmap, PiTensorProduct.map_tprod, Submodule.mkQ_apply]`.
-/
theorem qmap_tprod (x : ∀ a, X a) :
    qmap e' ρ (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ fun a => (Submodule.Quotient.mk (x a) : Jacquet (ρ a) (unipRad k (e' a))) := by
  simp only [qmap, PiTensorProduct.map_tprod, Submodule.mkQ_apply]

/- English proof (translation)
Establish `hu' : ∀ a, u a ∈ unipRad k (e' a)`. Introduce `a`. Establish `h` using `hu`. Simplify using `only [relUnip, Subgroup.mem_pi] at h`. Conclude with `h a (Set.mem_univ a)`.

Use `PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)` and prove the remaining obligations. Simplify using `only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, piTensor_tprod, qmap_tprod]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[Submodule.Quotient.eq]`.

Conclude with `Submodule.subset_span ⟨⟨u a, hu' a⟩, x a, by simp⟩`.
-/
theorem qmap_comp (u : ∀ a, GL (m a) k) (hu : u ∈ relUnip k e') :
    qmap e' ρ ∘ₗ piTensor ρ u = qmap e' ρ := by
  have hu' : ∀ a, u a ∈ unipRad k (e' a) := by
    intro a
    have h := hu
    simp only [relUnip, Subgroup.mem_pi] at h
    exact h a (Set.mem_univ a)
  refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, piTensor_tprod, qmap_tprod]
  congr 1
  funext a
  rw [Submodule.Quotient.eq]
  exact Submodule.subset_span ⟨⟨u a, hu' a⟩, x a, by simp⟩

/- English proof (translation)
Rewrite using `[twKer, Submodule.span_le]`. Introduce and unpack `_ ⟨n, y, rfl⟩`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, MonoidHom.one_apply, Units.val_one, one_smul, map_sub, sub_eq_zero]`. Conclude with `LinearMap.congr_fun (qmap_comp e' ρ (n : ∀ a, GL (m a) k) n.2) y`.
-/
theorem twKer_le_ker : twKer (piTensor ρ) (relUnip k e') 1 ≤ LinearMap.ker (qmap e' ρ) := by
  rw [twKer, Submodule.span_le]
  rintro _ ⟨n, y, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, MonoidHom.one_apply, Units.val_one, one_smul, map_sub,
    sub_eq_zero]
  exact LinearMap.congr_fun (qmap_comp e' ρ (n : ∀ a, GL (m a) k) n.2) y

def fwd : Jacquet (piTensor ρ) (relUnip k e') →ₗ[ℂ] ⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a)) :=
  (twKer (piTensor ρ) (relUnip k e') 1).liftQ (qmap e' ρ) (twKer_le_ker e' ρ)

def bwd : (⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a))) →ₗ[ℂ] Jacquet (piTensor ρ) (relUnip k e') :=
  PiTensorProduct.lift (descend (qf e' ρ) (qf_update e' ρ))

/- English proof (translation)
Rewrite using `[bwd, PiTensorProduct.lift.tprod]`. Both sides reduce to the same expression.
-/
theorem bwd_tprod (q : ∀ a, Jacquet (ρ a) (unipRad k (e' a))) :
    bwd e' ρ (PiTensorProduct.tprod ℂ q) = Submodule.Quotient.mk (PiTensorProduct.tprod ℂ
      fun i => qlift (fun a => twKer (ρ a) (unipRad k (e' a)) 1) i (q i)) := by
  rw [bwd, PiTensorProduct.lift.tprod]
  rfl

/- English proof (translation)
Rewrite using `[bwd, PiTensorProduct.lift.tprod, descend_mk]`. Both sides reduce to the same expression.
-/
theorem bwd_tprod_mk (x : ∀ a, X a) :
    bwd e' ρ (PiTensorProduct.tprod ℂ fun a => (Submodule.Quotient.mk (x a) : Jacquet (ρ a) (unipRad k (e' a)))) =
      Submodule.Quotient.mk (PiTensorProduct.tprod ℂ x) := by
  rw [bwd, PiTensorProduct.lift.tprod, descend_mk]
  rfl

/- English proof (translation)
Rewrite using `[fwd, Submodule.liftQ_apply, qmap_tprod]`.
-/
theorem fwd_mk_tprod' (x : ∀ a, X a) :
    fwd e' ρ (Submodule.Quotient.mk (PiTensorProduct.tprod ℂ x)) =
      PiTensorProduct.tprod ℂ fun a => (Submodule.Quotient.mk (x a) : Jacquet (ρ a) (unipRad k (e' a))) := by
  rw [fwd, Submodule.liftQ_apply, qmap_tprod]

def jacEquiv : Jacquet (piTensor ρ) (relUnip k e') ≃ₗ[ℂ] ⨂[ℂ] a, Jacquet (ρ a) (unipRad k (e' a)) :=
  LinearEquiv.ofLinear (fwd e' ρ) (bwd e' ρ)
    (by
      refine PiTensorProduct.ext (MultilinearMap.ext fun q => ?_)
      rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, bwd_tprod, fwd_mk_tprod']
      simp only [mk_qlift, LinearMap.compMultilinearMap_apply, LinearMap.id_apply])
    (by
      refine Submodule.linearMap_qext _ (PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))
      rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        fwd_mk_tprod', bwd_tprod_mk, LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.id_apply,
        Submodule.mkQ_apply])

/- English proof (translation)
Use `⟨Representation.Equiv.mk (jacEquiv e' ρ) fun g => ?_⟩` and prove the remaining obligations. Use `Submodule.linearMap_qext _ (PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))` and prove the remaining obligations. Simplify using `only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe, jacEquiv, LinearEquiv.ofLinear_apply, relJac_mk, piTensor_tprod, relEmb_apply, map_smul, fwd_mk_tprod', jac_mk, MultilinearMap.map_smul_univ, relDeltaHalf_apply]`. Use `congr 1`. Rewrite using `[← Finset.prod_inv_distrib, Units.coe_prod]`.
-/
theorem relJac_piTensor :
    Nonempty ((relJac e' (piTensor ρ)).Equiv (piTensor fun a => jac (e' a) (ρ a))) := by
  refine ⟨Representation.Equiv.mk (jacEquiv e' ρ) fun g => ?_⟩
  refine Submodule.linearMap_qext _ (PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
    LinearEquiv.coe_coe, jacEquiv, LinearEquiv.ofLinear_apply, relJac_mk, piTensor_tprod, relEmb_apply,
    map_smul, fwd_mk_tprod', jac_mk, MultilinearMap.map_smul_univ, relDeltaHalf_apply]
  congr 1
  rw [← Finset.prod_inv_distrib, Units.coe_prod]

end Spec2

/- English proof (translation)
Introduce `k _ _ _ _ α β _ _ _ m _ _ c _ _ f X _ _ ρ`. Conclude with `relJac_piTensor f ρ`.
-/
theorem relJac_piTensor_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] [LinearOrder β]
    (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    (f : ∀ i, (Σ j, c i j) ≃ m i) (X : α → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (ρ : ∀ i, Representation ℂ (GL (m i) k) (X i)),
    Nonempty ((relJac f (piTensor ρ)).Equiv (piTensor fun i => jac (f i) (ρ i))) := by
  intro k _ _ _ _ α β _ _ _ m _ _ c _ _ f X _ _ ρ
  classical
  exact relJac_piTensor f ρ

end GlobalTheory.RelJacTensor
