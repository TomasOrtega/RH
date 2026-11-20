import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility

open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

section

variable {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/- English proof (translation)
Unfold `Representation.IsIrreducible`. Use `{ exists_pair_ne := ⟨⊥, ⊤, fun heq => ?_⟩, eq_bot_or_eq_top := fun W => ?_ }` and prove the remaining obligations. Establish `h1` using `congrArg Subrepresentation.toSubmodule heq`. Conclude with `bot_ne_top (show (⊥ : Submodule ℂ V) = ⊤ from h1)`. Take `⟨S, hS⟩` from `W`.

Break down `h S (fun g x hx => hS g hx) with h1 | h1` into its components or cases. Use `left`. Substitute `h1` using the available equality. Both sides reduce to the same expression. Use `right`.

Substitute `h1` using the available equality. Both sides reduce to the same expression.
-/
theorem isIrreducible_of [Nontrivial V] (ρ : Representation ℂ G V)
    (h : ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤) :
    ρ.IsIrreducible := by
  unfold Representation.IsIrreducible
  refine { exists_pair_ne := ⟨⊥, ⊤, fun heq => ?_⟩, eq_bot_or_eq_top := fun W => ?_ }
  · have h1 := congrArg Subrepresentation.toSubmodule heq
    exact bot_ne_top (show (⊥ : Submodule ℂ V) = ⊤ from h1)
  · obtain ⟨S, hS⟩ := W
    rcases h S (fun g x hx => hS g hx) with h1 | h1
    · left
      subst h1
      rfl
    · right
      subst h1
      rfl

/- English proof (translation)
Use `set T : Module.End ℂ V := ∑ g, a g • ρ g with hT`. Establish `hcomm : ∀ k, ρ k * T = T * ρ k`. Introduce `k`. Rewrite using `[hT, Finset.mul_sum, Finset.sum_mul]`. Use `Fintype.sum_equiv (MulAut.conj k).toEquiv _ _ (fun g => ?_)` and prove the remaining obligations.

Simplify using `only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, ha, mul_smul_comm, smul_mul_assoc, ← map_mul, inv_mul_cancel_right]`. Take `⟨μ, hμ⟩` from `Module.End.exists_eigenvalue T`. Use `⟨μ, ?_⟩` and prove the remaining obligations. Establish `hW : ∀ g, ∀ x ∈ Module.End.eigenspace T μ, ρ g x ∈ Module.End.eigenspace T μ`. Introduce `g x hx`.

Rewrite `hx`, the goal using `[Module.End.mem_eigenspace_iff]`. Rewrite using `[← Module.End.mul_apply, ← hcomm g, Module.End.mul_apply, hx, map_smul]`. Break down `h _ hW with h0 | h0` into its components or cases. Use `exfalso first`. Consider the case `exact Module.End.hasEigenvalue_iff.1 hμ h0`.

Consider the case `exact hμ h0`. Consider the case `(obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector`. Establish `hv1` using `hv.1`. Rewrite `hv1` using `[h0]`. Conclude with `hv.2 ((Submodule.mem_bot ℂ).1 hv1))`.

Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Establish `hx : x ∈ Module.End.eigenspace T μ`. Rewrite using `[h0]`. Conclude with `Submodule.mem_top`. Rewrite `hx` using `[Module.End.mem_eigenspace_iff]`.

Rewrite using `[hx]`. Simplify using the standard rewrite rules.
-/
theorem schur_scalar [Nontrivial V] (ρ : Representation ℂ G V)
    (h : ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤)
    (a : G → ℂ) (ha : ∀ g k, a (k * g * k⁻¹) = a g) :
    ∃ μ : ℂ, (∑ g, a g • ρ g) = μ • (1 : Module.End ℂ V) := by
  set T : Module.End ℂ V := ∑ g, a g • ρ g with hT
  have hcomm : ∀ k, ρ k * T = T * ρ k := by
    intro k
    rw [hT, Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (MulAut.conj k).toEquiv _ _ (fun g => ?_)
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, ha, mul_smul_comm,
      smul_mul_assoc, ← map_mul, inv_mul_cancel_right]
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  refine ⟨μ, ?_⟩
  have hW : ∀ g, ∀ x ∈ Module.End.eigenspace T μ, ρ g x ∈ Module.End.eigenspace T μ := by
    intro g x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [← Module.End.mul_apply, ← hcomm g, Module.End.mul_apply, hx, map_smul]
  rcases h _ hW with h0 | h0
  · exfalso
    first
      | exact Module.End.hasEigenvalue_iff.1 hμ h0
      | exact hμ h0
      | (obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
         have hv1 := hv.1
         rw [h0] at hv1
         exact hv.2 ((Submodule.mem_bot ℂ).1 hv1))
  · refine LinearMap.ext fun x => ?_
    have hx : x ∈ Module.End.eigenspace T μ := by
      rw [h0]
      exact Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hx
    rw [hx]
    simp

/- English proof (translation)
Take `⟨μ, hμ⟩` from `schur_scalar ρ h a ha`. Use `⟨μ, fun k => ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg (fun T : Module.End ℂ V => LinearMap.trace ℂ V (T * ρ k)) hμ`. Simplify using `only [Finset.sum_mul, smul_mul_assoc, ← map_mul, map_sum, map_smul, one_mul, smul_eq_mul] at h2`. Conclude with `h2`.
-/
theorem conv_char [Nontrivial V] (ρ : Representation ℂ G V)
    (h : ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤)
    (a : G → ℂ) (ha : ∀ g k, a (k * g * k⁻¹) = a g) :
    ∃ μ : ℂ, ∀ k, ∑ g, a g * ρ.character (g * k) = μ * ρ.character k := by
  obtain ⟨μ, hμ⟩ := schur_scalar ρ h a ha
  refine ⟨μ, fun k => ?_⟩
  have h2 := congrArg (fun T : Module.End ℂ V => LinearMap.trace ℂ V (T * ρ k)) hμ
  simp only [Finset.sum_mul, smul_mul_assoc, ← map_mul, map_sum, map_smul, one_mul, smul_eq_mul] at h2
  exact h2

/- English proof (translation)
Rewrite using `[Finset.sum_mul_sum]`. Establish `key : ∀ g, ∑ h, (A g • MonoidAlgebra.of ℂ G g) * (B h • MonoidAlgebra.of ℂ G h) = ∑ k, (A g * B (g⁻¹ * k)) • MonoidAlgebra.of ℂ G k`. Introduce `g`. Use `Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => ?_)` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulLeft, inv_mul_cancel_left, smul_mul_smul_comm, ← map_mul]`.

Rewrite using `[Finset.sum_congr rfl (fun g _ => key g), Finset.sum_comm]`. Repeatedly rewrite using `[Finset.sum_smul]`.
-/
theorem sum_of_mul_sum_of (A B : G → ℂ) :
    (∑ g, A g • MonoidAlgebra.of ℂ G g) * (∑ g, B g • MonoidAlgebra.of ℂ G g) =
      ∑ k, (∑ g, A g * B (g⁻¹ * k)) • MonoidAlgebra.of ℂ G k := by
  rw [Finset.sum_mul_sum]
  have key : ∀ g, ∑ h, (A g • MonoidAlgebra.of ℂ G g) * (B h • MonoidAlgebra.of ℂ G h) =
      ∑ k, (A g * B (g⁻¹ * k)) • MonoidAlgebra.of ℂ G k := by
    intro g
    refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => ?_)
    simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, smul_mul_smul_comm, ← map_mul]
  rw [Finset.sum_congr rfl (fun g _ => key g), Finset.sum_comm]
  simp_rw [Finset.sum_smul]

end

/- English proof (translation)
Establish `ha : ∀ g k : G, ρ.character (k * g * k⁻¹)⁻¹ = ρ.character g⁻¹`. Introduce `g k`. Simplify `ρ.char_conj g⁻¹ k` using `[mul_assoc]`. Take `⟨μ, hconv⟩` from `conv_char σ h (fun g => ρ.character g⁻¹) ha`. Establish `hone : σ.character 1 = (Module.finrank ℂ W : ℂ)` using `by first`.

Consider the case `exact σ.char_one`. Consider the case `(unfold Representation.character; simp)`. Use `⟨μ, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hconv 1`. Simplify using `only [mul_one, hone] at h1`.

Conclude with `h1.symm`. Unfold `centralIdem`. Rewrite using `[sum_of_mul_sum_of, Finset.smul_sum]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[smul_smul]`.

Use `congr 1`. Establish `hcm : ∀ g : G, σ.character (k⁻¹ * g) = σ.character (g * k⁻¹)` using `fun g => by`. Simplify `(σ.char_conj (k⁻¹ * g) g).symm` using `[mul_assoc]`. Establish `e1 : ∀ g : G, ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * ρ.character g⁻¹) * ((Module.finrank ℂ W : ℂ) / (Fintype.card G : ℂ) * σ.character (g⁻¹ * k)⁻¹) = ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * ((Module.finrank ℂ W : ℂ) / (Fintype.card G : ℂ))) * (ρ.character g …`. Introduce `g`.

Rewrite using `[mul_inv_rev, inv_inv, hcm]`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.mul_sum, hconv k⁻¹]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem centralIdem_mul {G V W : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (h : ∀ U : Submodule ℂ W, (∀ g, ∀ x ∈ U, σ g x ∈ U) → U = ⊥ ∨ U = ⊤) :
    ∃ μ : ℂ, μ * (Module.finrank ℂ W : ℂ) = ∑ g, ρ.character g⁻¹ * σ.character g ∧
      centralIdem ρ * centralIdem σ =
        ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * μ) • centralIdem σ := by
  have ha : ∀ g k : G, ρ.character (k * g * k⁻¹)⁻¹ = ρ.character g⁻¹ := by
    intro g k
    simpa [mul_assoc] using ρ.char_conj g⁻¹ k
  obtain ⟨μ, hconv⟩ := conv_char σ h (fun g => ρ.character g⁻¹) ha
  have hone : σ.character 1 = (Module.finrank ℂ W : ℂ) := by
    first
      | exact σ.char_one
      | (unfold Representation.character; simp)
  refine ⟨μ, ?_, ?_⟩
  · have h1 := hconv 1
    simp only [mul_one, hone] at h1
    exact h1.symm
  · unfold centralIdem
    rw [sum_of_mul_sum_of, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [smul_smul]
    congr 1
    have hcm : ∀ g : G, σ.character (k⁻¹ * g) = σ.character (g * k⁻¹) := fun g => by
      simpa [mul_assoc] using (σ.char_conj (k⁻¹ * g) g).symm
    have e1 : ∀ g : G, ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * ρ.character g⁻¹) *
        ((Module.finrank ℂ W : ℂ) / (Fintype.card G : ℂ) * σ.character (g⁻¹ * k)⁻¹) =
        ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * ((Module.finrank ℂ W : ℂ) / (Fintype.card G : ℂ))) *
        (ρ.character g⁻¹ * σ.character (g * k⁻¹)) := by
      intro g
      rw [mul_inv_rev, inv_inv, hcm]
      ring
    calc _ = ∑ g, ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) *
            ((Module.finrank ℂ W : ℂ) / (Fintype.card G : ℂ))) *
            (ρ.character g⁻¹ * σ.character (g * k⁻¹)) := Finset.sum_congr rfl (fun g _ => e1 g)
      _ = _ := by
        rw [← Finset.mul_sum, hconv k⁻¹]
        ring

/- English proof (translation)
Establish `hc : ∀ h : G, ρ.character (k⁻¹ * (h * k)) = ρ.character h` using `by first`. Consider the case `exact fun h => by simpa [mul_assoc] using ρ.char_conj h k⁻¹`. Consider the case `(intro h; unfold Representation.character; done)`. Unfold `centralIdem`. Rewrite using `[Finset.sum_mul, Finset.mul_sum]`.

Use `Fintype.sum_equiv (MulAut.conj k⁻¹).toEquiv _ _ (fun g => ?_)` and prove the remaining obligations. Simplify using `only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv, smul_mul_assoc, mul_smul_comm, ← map_mul, mul_inv_rev, mul_assoc, hc, mul_inv_cancel_left]`.
-/
theorem centralIdem_comm_of {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (k : G) :
    centralIdem ρ * MonoidAlgebra.of ℂ G k = MonoidAlgebra.of ℂ G k * centralIdem ρ := by
  have hc : ∀ h : G, ρ.character (k⁻¹ * (h * k)) = ρ.character h := by
    first
      | exact fun h => by simpa [mul_assoc] using ρ.char_conj h k⁻¹
      | (intro h; unfold Representation.character; done)
  unfold centralIdem
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Fintype.sum_equiv (MulAut.conj k⁻¹).toEquiv _ _ (fun g => ?_)
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv, smul_mul_assoc,
    mul_smul_comm, ← map_mul, mul_inv_rev, mul_assoc, hc, mul_inv_cancel_left]

/- English proof (translation)
Introduce `G V _ _ _ _ _ _ ρ h`. Prove the components needed by the constructor for the conclusion. Take `⟨μ, h1, h2⟩` from `centralIdem_mul ρ ρ h`. Establish `hirr : ρ.IsIrreducible` using `isIrreducible_of ρ h`. Establish `hc0 : (Fintype.card G : ℂ) ≠ 0` using `by exact_mod_cast Fintype.card_ne_zero`.

Establish `: Invertible (Nat.card G : ℂ)` using `invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)`. Establish `horth` using `Representation.char_orthonormal ρ ρ`. Rewrite `horth` using `[if_pos ⟨Representation.Equiv.refl ρ⟩, Nat.card_eq_fintype_card]`. Establish `h3 : ∑ g, ρ.character g⁻¹ * ρ.character g = (Fintype.card G : ℂ)`. Establish `: ∑ g, ρ.character g⁻¹ * ρ.character g = ∑ g, ρ.character g * ρ.character g⁻¹` using `Finset.sum_congr rfl fun g _ => mul_comm _ _`.

Rewrite using `[this]`. Clear denominators, using `at horth` for the nonvanishing conditions. Simplify using `using horth`. Rewrite using `[h2]`. Establish `h4 : (Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * μ = 1`.

Rewrite `h1` using `[h3]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_comm]`. Conclude with `h1`. Rewrite using `[h4, one_smul]`.

Introduce `x`. Proceed by induction on `x using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => rw [mul_add, add_mul, ha, hb]`. Consider the case `single g c`.

Establish `: MonoidAlgebra.single g c = c • MonoidAlgebra.of ℂ G g`. Simplify using `[MonoidAlgebra.of_apply]`. Rewrite using `[this, mul_smul_comm, smul_mul_assoc, centralIdem_comm_of]`.
-/
theorem central_idempotent_holds : CentralIdempotent := by
  intro G V _ _ _ _ _ _ ρ h
  constructor
  · obtain ⟨μ, h1, h2⟩ := centralIdem_mul ρ ρ h
    have hirr : ρ.IsIrreducible := isIrreducible_of ρ h
    have hc0 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have : Invertible (Nat.card G : ℂ) :=
      invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
    have horth := Representation.char_orthonormal ρ ρ
    rw [if_pos ⟨Representation.Equiv.refl ρ⟩, Nat.card_eq_fintype_card] at horth
    have h3 : ∑ g, ρ.character g⁻¹ * ρ.character g = (Fintype.card G : ℂ) := by
      have : ∑ g, ρ.character g⁻¹ * ρ.character g = ∑ g, ρ.character g * ρ.character g⁻¹ :=
        Finset.sum_congr rfl fun g _ => mul_comm _ _
      rw [this]
      field_simp at horth
      simpa using horth
    rw [h2]
    have h4 : (Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * μ = 1 := by
      rw [h3] at h1
      field_simp
      rw [mul_comm]; exact h1
    rw [h4, one_smul]
  · intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [mul_add, add_mul, ha, hb]
    | single g c =>
      have : MonoidAlgebra.single g c = c • MonoidAlgebra.of ℂ G g := by
        simp [MonoidAlgebra.of_apply]
      rw [this, mul_smul_comm, smul_mul_assoc, centralIdem_comm_of]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
