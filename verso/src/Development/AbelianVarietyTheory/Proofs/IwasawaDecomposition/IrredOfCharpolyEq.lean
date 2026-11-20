import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.IrreducibilityOfTheoremThree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyMonoidAlgebraLiftEqOfCharpolyEq
open Formalism.MainNotions.N

noncomputable section

namespace GlobalTheory.BrauerNesbittIrr

open Matrix

variable {k Γ : Type} [Field k] [Group Γ] {a : ℕ}

abbrev matHom (ρ : Γ →* GL (Fin a) k) : Γ →* Matrix (Fin a) (Fin a) k := (Units.coeHom _).comp ρ

abbrev liftRep (ρ : Γ →* GL (Fin a) k) : MonoidAlgebra k Γ →ₐ[k] Matrix (Fin a) (Fin a) k :=
  MonoidAlgebra.lift k (Matrix (Fin a) (Fin a) k) Γ (matHom ρ)

/- English proof (translation)
Proceed by induction on `α using MonoidAlgebra.induction_linear with`. Consider the case `zero => intro x _`. Simplify using `[W.zero_mem]`. Consider the case `add p q hp hq => intro x hx`. Rewrite using `[map_add, add_mulVec]`.

Conclude with `W.add_mem (hp x hx) (hq x hx)`. Consider the case `single g c`. Introduce `x hx`. Rewrite using `[MonoidAlgebra.lift_single, Matrix.smul_mulVec]`. Conclude with `W.smul_mem c (hW g x hx)`.
-/
theorem liftRep_mem (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k))
    (hW : ∀ g, ∀ x ∈ W, (ρ g : Matrix (Fin a) (Fin a) k) *ᵥ x ∈ W) (α : MonoidAlgebra k Γ) :
    ∀ x ∈ W, liftRep ρ α *ᵥ x ∈ W := by
  induction α using MonoidAlgebra.induction_linear with
  | zero => intro x _; simp [W.zero_mem]
  | add p q hp hq => intro x hx; rw [map_add, add_mulVec]; exact W.add_mem (hp x hx) (hq x hx)
  | single g c =>
    intro x hx
    rw [MonoidAlgebra.lift_single, Matrix.smul_mulVec]
    exact W.smul_mem c (hW g x hx)

/- English proof (translation)
Use `haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩`. Establish `hirr : IsIrrSub ρ ⊤` using `⟨top_ne_bot, fun g v _ => Submodule.mem_top, fun W' _ hinv => h W' hinv⟩`. Establish `hs` using `GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub ρ hirr`. Introduce `X`. Establish `hle : Submodule.span k (Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat ρ)) ≤ LinearMap.range (liftRep ρ).toLinearMap`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `⟨MonoidAlgebra.single g 1, by simp⟩`. Take `⟨α, hα⟩` from `hle (hs ▸ Submodule.mem_top : X ∈ _)`. Conclude with `⟨α, hα⟩`.
-/
theorem liftRep_surjective [IsAlgClosed k] (ρ : Γ →* GL (Fin a) k) (ha : 0 < a)
    (h : ∀ W : Submodule k (Fin a → k), (∀ g, ∀ x ∈ W, (ρ g : Matrix (Fin a) (Fin a) k) *ᵥ x ∈ W) →
      W = ⊥ ∨ W = ⊤) :
    Function.Surjective (liftRep ρ) := by
  haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  have hirr : IsIrrSub ρ ⊤ := ⟨top_ne_bot, fun g v _ => Submodule.mem_top,
    fun W' _ hinv => h W' hinv⟩
  have hs := GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub ρ hirr
  intro X
  have hle : Submodule.span k (Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat ρ)) ≤
      LinearMap.range (liftRep ρ).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact ⟨MonoidAlgebra.single g 1, by simp⟩
  obtain ⟨α, hα⟩ := hle (hs ▸ Submodule.mem_top : X ∈ _)
  exact ⟨α, hα⟩

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨hb, ht⟩` from `hne`. Establish `hcp : ∀ α, (liftRep ρ α).charpoly = (liftRep ρ' α).charpoly` using `GlobalTheory.charpoly_lift_eq_of_charpoly_eq a (matHom ρ) (matHom ρ') hc`. Establish `hdet : ∀ α, (liftRep ρ α).det = (liftRep ρ' α).det` using `fun α => by`.

Rewrite using `[det_eq_sign_charpoly_coeff, det_eq_sign_charpoly_coeff, hcp]`. Take `⟨w, hw, hw0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hb`. Establish `ha : 0 < a`. Break down `Nat.eq_zero_or_pos a with h | h` into its components or cases. Substitute `h` using the available equality.

Conclude with `absurd (Subsingleton.elim w 0) hw0`. Conclude with `h`. Use `haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩`. Establish `hsurj` using `liftRep_surjective ρ' ha h'`. Set `S : Set (Matrix (Fin a) (Fin a) k)` to `{X | ∃ α, (∀ x ∈ W, liftRep ρ α *ᵥ x = 0) ∧ liftRep ρ' α = X}`.

Set `I : TwoSidedIdeal (Matrix (Fin a) (Fin a) k)` to `TwoSidedIdeal.mk' S ⟨0, fun x _ => by simp, by simp⟩ (by`. Introduce and unpack `_ _ ⟨α, hα, rfl⟩ ⟨β, hβ, rfl⟩`. Conclude with `⟨α + β, fun x hx => by rw [map_add, add_mulVec, hα x hx, hβ x hx, add_zero], map_add _ _ _⟩)`. Use the proof step `(by`. Introduce and unpack `_ ⟨α, hα, rfl⟩`.

Conclude with `⟨-α, fun x hx => by rw [map_neg, neg_mulVec, hα x hx, neg_zero], map_neg _ _⟩)`. Use the proof step `(by`. Introduce and unpack `X _ ⟨α, hα, rfl⟩`. Take `⟨β, rfl⟩` from `hsurj X`. Conclude with `⟨β * α, fun x hx => by rw [map_mul, ← mulVec_mulVec, hα x hx, mulVec_zero], map_mul _ _ _⟩)`.

Use the proof step `(by`. Introduce and unpack `_ Y ⟨α, hα, rfl⟩`. Take `⟨β, rfl⟩` from `hsurj Y`. Conclude with `⟨α * β, fun x hx => by`. Rewrite using `[map_mul, ← mulVec_mulVec, hα _ (liftRep_mem ρ W hW β x hx)], map_mul _ _ _⟩)`.

Establish `hmem : ∀ X, X ∈ I ↔ X ∈ S` using `fun X => TwoSidedIdeal.mem_mk' _ _ _ _ _ _ X`. Break down `IsSimpleOrder.eq_bot_or_eq_top I with hI | hI` into its components or cases. Establish `h0 : ∀ α, (∀ x ∈ W, liftRep ρ α *ᵥ x = 0) → liftRep ρ' α = 0` using `fun α hα => by`. Establish `: liftRep ρ' α ∈ I` using `(hmem _).2 ⟨α, hα, rfl⟩`. Rewrite `this` using `[hI]`.

Conclude with `(TwoSidedIdeal.mem_bot _).1 this`. Set `ψ : MonoidAlgebra k Γ →ₗ[k] (Fin (Module.finrank k W) → Fin a → k)` to `{ toFun := fun α i => liftRep ρ α *ᵥ ((Module.finBasis k W i : W) : Fin a → k) map_add' := fun α β => by funext i; simp [add_mulVec] map_smul' := fun c α => by funext i; simp [Matrix.smul_mulVec] }`. Establish `hker : LinearMap.ker ψ ≤ LinearMap.ker (liftRep ρ').toLinearMap`. Introduce `α hα`. Rewrite `hα`, the goal using `[LinearMap.mem_ker]`.

Apply `h0 α` to reduce the goal to its premises. Introduce `x hx`. Establish `hf : (Matrix.toLin' (liftRep ρ α)).comp W.subtype = 0` using `(Module.finBasis k W).ext fun i => by`. Use `congrFun hα i` as an intermediate fact. Simplify `this` using `[ψ]`.

Use `LinearMap.congr_fun hf ⟨x, hx⟩` as an intermediate fact. Simplify using `using this`. Establish `hrange : LinearMap.range (liftRep ρ').toLinearMap = ⊤` using `LinearMap.range_eq_top.2 hsurj`. Set `q` to `(LinearMap.ker ψ).liftQ (liftRep ρ').toLinearMap hker`. Establish `hq : LinearMap.range q = ⊤` using `by rw [Submodule.range_liftQ, hrange]`.

Use `haveI : FiniteDimensional k (MonoidAlgebra k Γ ⧸ LinearMap.ker ψ) := LinearEquiv.finiteDimensional (ψ.quotKerEquivRange).symm`. Establish `h1 : Module.finrank k (Matrix (Fin a) (Fin a) k) ≤ Module.finrank k (MonoidAlgebra k Γ ⧸ LinearMap.ker ψ)`. Use `LinearMap.finrank_range_le q` as an intermediate fact. Rewrite `this` using `[hq, finrank_top]`. Then use the resulting hypothesis. Establish `h2 : Module.finrank k (MonoidAlgebra k Γ ⧸ LinearMap.ker ψ) ≤ Module.finrank k W * a`.

Rewrite using `[ψ.quotKerEquivRange.finrank_eq]`. Use `(Submodule.finrank_le _).trans (le_of_eq ?_)` and prove the remaining obligations. Use `first`. Consider the case `simp [Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card]`. Consider the case `rw [Module.finrank_pi_fintype]`.

Simplify using the standard rewrite rules. Consider the case `simp [Module.finrank_pi]`. Establish `h3 : Module.finrank k W < a`. Use `Submodule.finrank_lt ht` as an intermediate fact. Simplify using `using this`.

Rewrite `h1` using `[Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h1 : (1 : Matrix (Fin a) (Fin a) k) ∈ I` using `by rw [hI]; exact TwoSidedIdeal.mem_top _`. Take `⟨κ, hκ, hκ1⟩` from `(hmem _).1 h1`. Establish `h0 : (liftRep ρ κ).det = 0` using `Matrix.exists_mulVec_eq_zero_iff.1 ⟨w, hw0, hκ w hw⟩`.

Rewrite `h0` using `[hdet, hκ1, det_one]`. Conclude with `one_ne_zero h0`.
-/
theorem irred_of_charpoly_eq [IsAlgClosed k] (ρ ρ' : Γ →* GL (Fin a) k)
    (hc : ∀ g, (ρ g : Matrix (Fin a) (Fin a) k).charpoly = (ρ' g : Matrix (Fin a) (Fin a) k).charpoly)
    (h' : ∀ W : Submodule k (Fin a → k), (∀ g, ∀ x ∈ W, (ρ' g : Matrix (Fin a) (Fin a) k) *ᵥ x ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (W : Submodule k (Fin a → k)) (hW : ∀ g, ∀ x ∈ W, (ρ g : Matrix (Fin a) (Fin a) k) *ᵥ x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_contra hne
  push_neg at hne
  obtain ⟨hb, ht⟩ := hne
  have hcp : ∀ α, (liftRep ρ α).charpoly = (liftRep ρ' α).charpoly :=
    GlobalTheory.charpoly_lift_eq_of_charpoly_eq a (matHom ρ) (matHom ρ') hc
  have hdet : ∀ α, (liftRep ρ α).det = (liftRep ρ' α).det := fun α => by
    rw [det_eq_sign_charpoly_coeff, det_eq_sign_charpoly_coeff, hcp]
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; exact absurd (Subsingleton.elim w 0) hw0
    · exact h
  haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  have hsurj := liftRep_surjective ρ' ha h'
  let S : Set (Matrix (Fin a) (Fin a) k) :=
    {X | ∃ α, (∀ x ∈ W, liftRep ρ α *ᵥ x = 0) ∧ liftRep ρ' α = X}
  let I : TwoSidedIdeal (Matrix (Fin a) (Fin a) k) := TwoSidedIdeal.mk' S
    ⟨0, fun x _ => by simp, by simp⟩
    (by
      rintro _ _ ⟨α, hα, rfl⟩ ⟨β, hβ, rfl⟩
      exact ⟨α + β, fun x hx => by rw [map_add, add_mulVec, hα x hx, hβ x hx, add_zero],
        map_add _ _ _⟩)
    (by
      rintro _ ⟨α, hα, rfl⟩
      exact ⟨-α, fun x hx => by rw [map_neg, neg_mulVec, hα x hx, neg_zero], map_neg _ _⟩)
    (by
      rintro X _ ⟨α, hα, rfl⟩
      obtain ⟨β, rfl⟩ := hsurj X
      exact ⟨β * α, fun x hx => by rw [map_mul, ← mulVec_mulVec, hα x hx, mulVec_zero],
        map_mul _ _ _⟩)
    (by
      rintro _ Y ⟨α, hα, rfl⟩
      obtain ⟨β, rfl⟩ := hsurj Y
      exact ⟨α * β, fun x hx => by
        rw [map_mul, ← mulVec_mulVec, hα _ (liftRep_mem ρ W hW β x hx)], map_mul _ _ _⟩)
  have hmem : ∀ X, X ∈ I ↔ X ∈ S := fun X => TwoSidedIdeal.mem_mk' _ _ _ _ _ _ X
  rcases IsSimpleOrder.eq_bot_or_eq_top I with hI | hI
  · have h0 : ∀ α, (∀ x ∈ W, liftRep ρ α *ᵥ x = 0) → liftRep ρ' α = 0 := fun α hα => by
      have : liftRep ρ' α ∈ I := (hmem _).2 ⟨α, hα, rfl⟩
      rw [hI] at this
      exact (TwoSidedIdeal.mem_bot _).1 this
    let ψ : MonoidAlgebra k Γ →ₗ[k] (Fin (Module.finrank k W) → Fin a → k) :=
      { toFun := fun α i => liftRep ρ α *ᵥ ((Module.finBasis k W i : W) : Fin a → k)
        map_add' := fun α β => by funext i; simp [add_mulVec]
        map_smul' := fun c α => by funext i; simp [Matrix.smul_mulVec] }
    have hker : LinearMap.ker ψ ≤ LinearMap.ker (liftRep ρ').toLinearMap := by
      intro α hα
      rw [LinearMap.mem_ker] at hα ⊢
      apply h0 α
      intro x hx
      have hf : (Matrix.toLin' (liftRep ρ α)).comp W.subtype = 0 :=
        (Module.finBasis k W).ext fun i => by
          have := congrFun hα i
          simpa [ψ] using this
      have := LinearMap.congr_fun hf ⟨x, hx⟩
      simpa using this
    have hrange : LinearMap.range (liftRep ρ').toLinearMap = ⊤ := LinearMap.range_eq_top.2 hsurj
    let q := (LinearMap.ker ψ).liftQ (liftRep ρ').toLinearMap hker
    have hq : LinearMap.range q = ⊤ := by rw [Submodule.range_liftQ, hrange]
    haveI : FiniteDimensional k (MonoidAlgebra k Γ ⧸ LinearMap.ker ψ) :=
      LinearEquiv.finiteDimensional (ψ.quotKerEquivRange).symm
    have h1 : Module.finrank k (Matrix (Fin a) (Fin a) k) ≤
        Module.finrank k (MonoidAlgebra k Γ ⧸ LinearMap.ker ψ) := by
      have := LinearMap.finrank_range_le q
      rwa [hq, finrank_top] at this
    have h2 : Module.finrank k (MonoidAlgebra k Γ ⧸ LinearMap.ker ψ) ≤
        Module.finrank k W * a := by
      rw [ψ.quotKerEquivRange.finrank_eq]
      refine (Submodule.finrank_le _).trans (le_of_eq ?_)
      first
        | simp [Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card]
        | rw [Module.finrank_pi_fintype]; simp
        | simp [Module.finrank_pi]
    have h3 : Module.finrank k W < a := by
      have := Submodule.finrank_lt ht
      simpa using this
    rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at h1
    nlinarith
  · have h1 : (1 : Matrix (Fin a) (Fin a) k) ∈ I := by rw [hI]; exact TwoSidedIdeal.mem_top _
    obtain ⟨κ, hκ, hκ1⟩ := (hmem _).1 h1
    have h0 : (liftRep ρ κ).det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨w, hw0, hκ w hw⟩
    rw [hdet, hκ1, det_one] at h0
    exact one_ne_zero h0

/- English proof (translation)
Introduce `ℓ _ a ρ ρ' hc h' W hW`. Conclude with `irred_of_charpoly_eq ρ ρ' hc (fun W hW => h' W fun g _ x hx => hW g x hx) W (fun g x hx => hW g (Subgroup.mem_top g) x hx)`.
-/
theorem litBNIrr (Γ : Type) [Group Γ] : LitBNIrr Γ := by
  intro ℓ _ a ρ ρ' hc h' W hW
  exact irred_of_charpoly_eq ρ ρ' hc (fun W hW => h' W fun g _ x hx => hW g x hx) W
    (fun g x hx => hW g (Subgroup.mem_top g) x hx)

end GlobalTheory.BrauerNesbittIrr

end
