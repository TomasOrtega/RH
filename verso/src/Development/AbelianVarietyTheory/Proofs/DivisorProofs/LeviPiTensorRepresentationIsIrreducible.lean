import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockEmbeddingFactors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviTensorBlockExt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SpanRangeEqTopOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleOuterTprod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentsSimpleFDRepFiniteFinsumEqOne

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV GlobalTheory.HcIrr

namespace GlobalTheory.HcIrr

section General

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
  [∀ i, Module ℂ (V i)]

/- English proof (translation)
Reduce the argument to an intermediate assertion. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem map_mem_of_position_stable (W : Submodule ℂ (PiTensorProduct ℂ V))
    (h : ∀ (c : ι) (f : V c →ₗ[ℂ] V c), ∀ x ∈ W, PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) c f) x ∈ W)
    (f : ∀ i, V i →ₗ[ℂ] V i) : ∀ x ∈ W, PiTensorProduct.map f x ∈ W := by
  suffices H : ∀ S : Finset ι, ∀ x ∈ W,
      PiTensorProduct.map (fun c => if c ∈ S then f c else LinearMap.id) x ∈ W by
    intro x hx
    simpa using H Finset.univ x hx
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro x hx
    simpa [PiTensorProduct.map_id] using hx
  | insert a S ha ih =>
    intro x hx
    have e : (fun c => if c ∈ insert a S then f c else (LinearMap.id : V c →ₗ[ℂ] V c)) = fun c =>
        (Function.update (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) a (f a)) c ∘ₗ
          (if c ∈ S then f c else LinearMap.id) := by
      funext c
      by_cases hc : c = a
      · subst hc
        simp [ha]
      · simp [hc, Function.update_of_ne]
    rw [e, PiTensorProduct.map_comp]
    exact h a (f a) _ (ih x hx)

/- English proof (translation)
Establish an intermediate fact. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem position_stable_of_span {c : ι} {G : Type} [Group G] (ρ : Representation ℂ G (V c))
    (hs : Submodule.span ℂ (Set.range ρ) = ⊤) (W : Submodule ℂ (PiTensorProduct ℂ V))
    (h : ∀ g : G, ∀ x ∈ W, PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) c (ρ g)) x ∈ W)
    (f : V c →ₗ[ℂ] V c) : ∀ x ∈ W, PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) c f) x ∈ W := by
  have hf : f ∈ Submodule.span ℂ (Set.range ρ) := hs ▸ Submodule.mem_top
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, rfl⟩ := hf
    exact h g
  | zero =>
    intro x _
    have := PiTensorProduct.map_update_smul (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) c (0 : ℂ)
      LinearMap.id
    rw [zero_smul, zero_smul] at this
    rw [this]
    simp
  | add u v _ _ hu hv =>
    intro x hx
    rw [PiTensorProduct.map_update_add, LinearMap.add_apply]
    exact add_mem (hu x hx) (hv x hx)
  | smul a u _ hu =>
    intro x hx
    rw [PiTensorProduct.map_update_smul, LinearMap.smul_apply]
    exact W.smul_mem _ (hu x hx)

/- English proof (translation)
Consider separately whether the proposition holds or fails. Prove the first alternative. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Introduce a local definition for the expression.

Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eq_bot_or_top_of_map_stable [∀ i, FiniteDimensional ℂ (V i)]
    (W : Submodule ℂ (PiTensorProduct ℂ V))
    (h : ∀ f : ∀ i, V i →ₗ[ℂ] V i, ∀ x ∈ W, PiTensorProduct.map f x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  let e := fun c => Module.finBasis ℂ (V c)
  let B := Basis.piTensorProduct e
  obtain ⟨I, hI⟩ : ∃ I, B.repr x I ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx0 (B.repr.map_eq_zero_iff.1 (Finsupp.ext hc))
  have hJ : ∀ J, B J ∈ W := by
    intro J
    let f : ∀ c, V c →ₗ[ℂ] V c := fun c => ((e c).coord (I c)).smulRight (e c (J c))
    have hf : PiTensorProduct.map f = (B.coord I).smulRight (B J) := by
      refine B.ext fun p => ?_
      have hc : ∀ c, f c (e c (p c)) = (if p c = I c then (1 : ℂ) else 0) • e c (J c) := by
        intro c
        simp [f, Finsupp.single_apply]
      have hq : (∏ c, if p c = I c then (1 : ℂ) else 0) = if p = I then 1 else 0 := by
        rw [Finset.prod_ite_zero]
        simp [funext_iff]
      rw [LinearMap.smulRight_apply, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      simp only [B, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod, hc,
        MultilinearMap.map_smul_univ, hq]
    have hm := h f x hx
    rw [hf, LinearMap.smulRight_apply, Module.Basis.coord_apply] at hm
    exact (W.smul_mem_iff hI).1 hm
  refine eq_top_iff.2 ?_
  rw [← B.span_eq]
  exact Submodule.span_le.2 (by rintro _ ⟨J, rfl⟩; exact hJ J)

/- English proof (translation)
Introduce a local definition for the expression. Supply the required witnesses or components.
-/
theorem nontrivial_piTensorProduct [∀ i, FiniteDimensional ℂ (V i)] [∀ i, Nontrivial (V i)] :
    Nontrivial (PiTensorProduct ℂ V) := by
  let B := Basis.piTensorProduct fun c => Module.finBasis ℂ (V c)
  exact ⟨B fun c => ⟨0, Module.finrank_pos⟩, 0, B.ne_zero _⟩

end General

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative.

Prove the second alternative. A detailed English derivation is pending.
-/
theorem leviTensor_isIrreducible : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ)
    (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
    (∀ c, Simple (lam c)) → (leviTensor b lam).IsIrreducible := by
  intro K _ _ _ r s b lam hs
  have hirr := fun c => GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple (lam c) (hs c)
  have hspan := fun c => GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ (lam c).ρ (hirr c)
  haveI : ∀ c, Nontrivial (lam c : Type) := fun c =>
    GlobalTheory.OuterTensor.nontrivial_of_isIrreducible _ (hirr c)
  haveI : Nontrivial (PiTensorProduct ℂ (fun c => (lam c : Type))) := nontrivial_piTensorProduct
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule h :
      (⊥ : Submodule ℂ (PiTensorProduct ℂ (fun c => (lam c : Type)))) = ⊤)
  have hstable : ∀ (c : Fin s) (f : (lam c : Type) →ₗ[ℂ] (lam c : Type)), ∀ x ∈ S.toSubmodule,
      PiTensorProduct.map (Function.update
        (fun c' => (LinearMap.id : (lam c' : Type) →ₗ[ℂ] (lam c' : Type))) c f) x ∈ S.toSubmodule := by
    intro c
    refine position_stable_of_span (lam c).ρ (hspan c) S.toSubmodule fun g x hx => ?_
    rw [← leviTensor_blockExt b lam c g]
    exact S.apply_mem_toSubmodule _ hx
  rcases eq_bot_or_top_of_map_stable S.toSubmodule (map_mem_of_position_stable _ hstable) with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

end GlobalTheory.HcIrr
