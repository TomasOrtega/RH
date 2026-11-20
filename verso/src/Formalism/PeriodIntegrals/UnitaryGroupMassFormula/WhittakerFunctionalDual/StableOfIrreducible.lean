import Mathlib
import Formalism.PeriodIntegrals.WhitFunctDual

namespace PI.WhitFunctDualWork

open Formalism.L2.SG.GGMirabolic

/- English proof (translation)
Use `h` as an intermediate fact. Use `⟨?_, fun W hW => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hnt`. Rewrite `hnt` using `[not_nontrivial_iff_subsingleton]`. Apply `(bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)` to reduce the goal to its premises.

Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Use `show (⊥ : Submodule ℂ V) = ⊤`. Use extensionality with `x`. Simplify using `[Subsingleton.elim x 0]`. Break down `IsSimpleOrder.eq_bot_or_eq_top (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation π) with h1 | h1` into its components or cases.

Conclude with `Or.inl (congrArg Subrepresentation.toSubmodule h1)`. Conclude with `Or.inr (congrArg Subrepresentation.toSubmodule h1)`.
-/
theorem stable_of_irreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (h : π.IsIrreducible) :
    Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, π g x ∈ W) → W = ⊥ ∨ W = ⊤ := by
  have := h
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    show (⊥ : Submodule ℂ V) = ⊤
    ext x
    simp [Subsingleton.elim x 0]
  · rcases IsSimpleOrder.eq_bot_or_eq_top
        (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation π) with h1 | h1
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h1)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)

/- English proof (translation)
Take `⟨hnt, hst⟩` from `stable_of_irreducible π h`. Use `⟨Module.nontrivial_of_finrank_pos (by rw [Subspace.dual_finrank_eq]; exact Module.finrank_pos), fun W hW => ?_⟩` and prove the remaining obligations. Establish `hU : ∀ g, ∀ v ∈ W.dualCoannihilator, π g v ∈ W.dualCoannihilator`. Introduce `g v hv`. Rewrite `hv`, the goal using `[Submodule.mem_dualCoannihilator]`.

Introduce `f hf`. Simplify `hv _ (hW g⁻¹ f hf)` using `[Representation.dual_apply, Module.Dual.transpose_apply]`. Establish `hW' : W = W.dualCoannihilator.dualAnnihilator` using `Subspace.dualCoannihilator_dualAnnihilator_eq.symm`. Break down `hst _ hU with h0 | h0` into its components or cases. Use `right`.

Rewrite using `[hW', h0, Submodule.dualAnnihilator_bot]`. Use `left`. Rewrite using `[hW', h0, Submodule.dualAnnihilator_top]`.
-/
theorem isIrr_dual {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (π : Representation ℂ G V) (h : π.IsIrreducible) :
    Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.IsIrr (Representation.dual π) := by
  obtain ⟨hnt, hst⟩ := stable_of_irreducible π h
  refine ⟨Module.nontrivial_of_finrank_pos (by rw [Subspace.dual_finrank_eq]; exact Module.finrank_pos),
    fun W hW => ?_⟩
  have hU : ∀ g, ∀ v ∈ W.dualCoannihilator, π g v ∈ W.dualCoannihilator := by
    intro g v hv
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro f hf
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using hv _ (hW g⁻¹ f hf)
  have hW' : W = W.dualCoannihilator.dualAnnihilator :=
    Subspace.dualCoannihilator_dualAnnihilator_eq.symm
  rcases hst _ hU with h0 | h0
  · right
    rw [hW', h0, Submodule.dualAnnihilator_bot]
  · left
    rw [hW', h0, Submodule.dualAnnihilator_top]

/- English proof (translation)
Unfold `Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselEdge`. Apply the tactic sequence `constructor <;> intro h <;> omega`.
-/
theorem besselEdge_zero (i j : ℕ) : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselEdge 0 0 i j ↔ j = i + 1 := by
  unfold Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselEdge
  constructor <;> intro h <;> omega

/- English proof (translation)
Introduce `u`. Use `beta_reduce`. Take `⟨hdiag, hlow, -⟩` from `u.2`. Establish `huni : IsUni k (u : GL (Fin k) F)` using `⟨hdiag, hlow⟩`. Establish `hp : psiU ψ₀ (u : GL (Fin k) F) ≠ 0`.

Introduce `h0`. Establish `h3` using `AddChar.map_add_eq_mul ψ₀ (superdiag k ((u : GL (Fin k) F) : Matrix (Fin k) (Fin k) F)) (-superdiag k ((u : GL (Fin k) F) : Matrix (Fin k) (Fin k) F))`. Rewrite `h3` using `[add_neg_cancel, AddChar.map_zero_eq_one]`. Unfold `psiU at h0`. Rewrite `h3` using `[h0, zero_mul]`.

Conclude with `one_ne_zero h3`. Establish `hchar : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselChar ψ₀⁻¹ 0 0 k (u : GL (Fin k) F) = (psiU ψ₀ (u : GL (Fin k) F))⁻¹`. Unfold `Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselChar psiU superdiag`. Rewrite using `[AddChar.inv_apply, AddChar.map_neg_eq_inv]`. Use `congr 2`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hij : (j : ℕ) = (i : ℕ) + 1 <;> simp [hij, besselEdge_zero]`. Use extensionality with `v`. Establish `hinv : π (u : GL (Fin k) F) (π ((u : GL (Fin k) F)⁻¹) v) = v`. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`.

Establish `hw` using `hℓ (u : GL (Fin k) F) huni (π ((u : GL (Fin k) F)⁻¹) v)`. Rewrite `hw` using `[hinv]`. Rewrite using `[Representation.dual_apply, LinearMap.smul_apply, hchar, smul_eq_mul, Module.Dual.transpose_apply, LinearMap.comp_apply, hw, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]`.
-/
theorem whit_mem {F : Type} [Field F] [Fintype F] {k : ℕ} (ψ₀ : AddChar F ℂ) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin k) F) V)
    (ℓ : Module.Dual ℂ V) (hℓ : IsWhit ψ₀ π ℓ) :
    ℓ ∈ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0 := by
  intro u
  beta_reduce
  obtain ⟨hdiag, hlow, -⟩ := u.2
  have huni : IsUni k (u : GL (Fin k) F) := ⟨hdiag, hlow⟩
  have hp : psiU ψ₀ (u : GL (Fin k) F) ≠ 0 := by
    intro h0
    have h3 := AddChar.map_add_eq_mul ψ₀ (superdiag k ((u : GL (Fin k) F) : Matrix (Fin k) (Fin k) F))
      (-superdiag k ((u : GL (Fin k) F) : Matrix (Fin k) (Fin k) F))
    rw [add_neg_cancel, AddChar.map_zero_eq_one] at h3
    unfold psiU at h0
    rw [h0, zero_mul] at h3
    exact one_ne_zero h3
  have hchar : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselChar ψ₀⁻¹ 0 0 k (u : GL (Fin k) F) =
      (psiU ψ₀ (u : GL (Fin k) F))⁻¹ := by
    unfold Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselChar psiU superdiag
    rw [AddChar.inv_apply, AddChar.map_neg_eq_inv]
    congr 2
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : (j : ℕ) = (i : ℕ) + 1 <;> simp [hij, besselEdge_zero]
  ext v
  have hinv : π (u : GL (Fin k) F) (π ((u : GL (Fin k) F)⁻¹) v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hw := hℓ (u : GL (Fin k) F) huni (π ((u : GL (Fin k) F)⁻¹) v)
  rw [hinv] at hw
  rw [Representation.dual_apply, LinearMap.smul_apply, hchar, smul_eq_mul,
    Module.Dual.transpose_apply, LinearMap.comp_apply, hw, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]

/- English proof (translation)
Introduce `hGG F _ _ k ψ₀ hψ V _ _ _ π hπ ℓ₁ ℓ₂ h1 h2 hne`. Establish `hψ' : ψ₀⁻¹ ≠ 1` using `inv_ne_one.mpr hψ`. Establish `hirr` using `isIrr_dual π hπ`. Establish `hdim` using `hGG F (Module.Dual ℂ V) k ψ₀⁻¹ (Representation.dual π) hψ' hirr`. Establish `m1 : ℓ₁ ∈ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0` using `whit_mem ψ₀ π ℓ₁ h1`.

Establish `m2 : ℓ₂ ∈ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0` using `whit_mem ψ₀ π ℓ₂ h2`. Establish `hne' : (⟨ℓ₁, m1⟩ : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0) ≠ 0` using `fun h0 => hne (congrArg Subtype.val h0)`. Establish `hpos : 0 < Module.finrank ℂ (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0)` using `Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne'⟩`. Take `⟨c, hc⟩` from `(finrank_eq_one_iff_of_nonzero' _ hne').mp (le_antisymm hdim hpos) ⟨ℓ₂, m2⟩`. Conclude with `⟨c, (congrArg Subtype.val hc).symm⟩`.
-/
theorem whitFunctDual_main : PI.WhitFunctDual := by
  intro hGG F _ _ k ψ₀ hψ V _ _ _ π hπ ℓ₁ ℓ₂ h1 h2 hne
  have hψ' : ψ₀⁻¹ ≠ 1 := inv_ne_one.mpr hψ
  have hirr := isIrr_dual π hπ
  have hdim := hGG F (Module.Dual ℂ V) k ψ₀⁻¹ (Representation.dual π) hψ' hirr
  have m1 : ℓ₁ ∈ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0 := whit_mem ψ₀ π ℓ₁ h1
  have m2 : ℓ₂ ∈ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0 := whit_mem ψ₀ π ℓ₂ h2
  have hne' : (⟨ℓ₁, m1⟩ : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0) ≠ 0 :=
    fun h0 => hne (congrArg Subtype.val h0)
  have hpos : 0 < Module.finrank ℂ (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.besselSpace (Representation.dual π) ψ₀⁻¹ 0 0) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne'⟩
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne').mp (le_antisymm hdim hpos) ⟨ℓ₂, m2⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

end PI.WhitFunctDualWork
