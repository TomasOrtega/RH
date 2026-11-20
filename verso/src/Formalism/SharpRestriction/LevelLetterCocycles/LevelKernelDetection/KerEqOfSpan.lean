import Mathlib
import Formalism.DistinguishedUnitIdeals.UnivPart

noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.ExponentWindows

abbrev GrQ {LL D : Type} [Field LL] [AddCommGroup D] [Module LL D] (F : ℤ → Submodule LL D) : Type :=
  ↥(Submodule.pi Set.univ fun k : ℤ => F (-k)) ⧸
    ((Submodule.pi Set.univ fun k : ℤ => F (1 - k)).comap (Submodule.pi Set.univ fun k : ℤ => F (-k)).subtype)

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Introduce a local definition for the expression.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem finrank_grQ {LL D : Type} [Field LL] [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
    (F : ℤ → Submodule LL D) (hF : IsFilt F) :
    FiniteDimensional LL (GrQ F) ∧ Module.finrank LL (GrQ F) = Module.finrank LL D := by
  classical
  obtain ⟨hanti, ⟨lo, hlo⟩, ⟨b, hb⟩⟩ := hF
  set a : ℤ := min lo (b - 1) with ha_def
  have hab : a < b := by omega
  have htop : ∀ i, i ≤ a → F i = ⊤ := fun i hi => top_unique (hlo ▸ hanti (le_trans hi (min_le_left _ _)))
  have hbot : ∀ i, b ≤ i → F i = ⊥ := fun i hi => eq_bot_iff.2 (hb ▸ hanti hi)
  set N : ℕ := (b - a).toNat with hN
  let S : Finset ℤ := (Finset.range N).image fun j : ℕ => 1 - b + j
  have hmemS : ∀ k : ℤ, k ∈ S ↔ 1 - b ≤ k ∧ k ≤ -a := by
    intro k
    simp only [S, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; omega
    · intro h; exact ⟨(k - (1 - b)).toNat, by omega, by omega⟩
  let P0 := Submodule.pi Set.univ fun k : ℤ => F (-k)
  let P1 := Submodule.pi Set.univ fun k : ℤ => F (1 - k)
  have memP0 : ∀ (x : P0) (k : ℤ), (x : ℤ → D) k ∈ F (-k) :=
    fun x k => (Submodule.mem_pi.1 x.2) k (Set.mem_univ _)
  let Qk : ℤ → Type := fun k => ↥(F (-k)) ⧸ (F (1 - k)).comap (F (-k)).subtype
  let φ : P0 →ₗ[LL] ∀ k : S, Qk k :=
    LinearMap.pi fun k => (Submodule.mkQ _) ∘ₗ
      ((LinearMap.proj (R := LL) (φ := fun _ : ℤ => D) (k : ℤ)) ∘ₗ P0.subtype).codRestrict (F (-(k : ℤ)))
        (fun x => memP0 x (k : ℤ))
  have hφ : ∀ (x : P0) (k : S), φ x k =
      (Submodule.Quotient.mk (⟨(x : ℤ → D) k, memP0 x k⟩ : ↥(F (-(k : ℤ)))) : Qk k) := fun x k => rfl
  have hker : LinearMap.ker φ = P1.comap P0.subtype := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_pi]
    constructor
    · intro hx k _
      show (x : ℤ → D) k ∈ F (1 - k)
      by_cases hk : k ∈ S
      · have := congrFun hx ⟨k, hk⟩
        rw [hφ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at this
        exact this
      · rw [hmemS] at hk
        rcases not_and_or.1 hk with h | h
        · have h0 : (x : ℤ → D) k ∈ F (-k) := memP0 x k
          rw [hbot (-k) (by omega)] at h0
          rw [(Submodule.mem_bot LL).1 h0]
          exact Submodule.zero_mem _
        · rw [htop (1 - k) (by omega)]
          exact Submodule.mem_top
    · intro hx
      funext k
      rw [hφ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact hx (k : ℤ) (Set.mem_univ _)
  have hsurj : Function.Surjective φ := by
    intro y
    have hy : ∀ k : S, ∃ z : ↥(F (-(k : ℤ))), (Submodule.Quotient.mk z : Qk k) = y k :=
      fun k => Submodule.Quotient.mk_surjective _ (y k)
    choose z hz using hy
    refine ⟨⟨fun k => if h : k ∈ S then (z ⟨k, h⟩ : D) else 0, ?_⟩, ?_⟩
    · rw [Submodule.mem_pi]
      intro k _
      by_cases h : k ∈ S
      · simp only [dif_pos h]; exact (z ⟨k, h⟩).2
      · simp only [dif_neg h]; exact Submodule.zero_mem _
    · funext k
      rw [hφ, ← hz k]
      congr 1
      apply Subtype.ext
      simp [k.2]
  let e : GrQ F ≃ₗ[LL] ∀ k : S, Qk k :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hsurj)
  have hFD : FiniteDimensional LL (GrQ F) := LinearEquiv.finiteDimensional e.symm
  refine ⟨hFD, ?_⟩
  have hle : ∀ k : ℤ, F (1 - k) ≤ F (-k) := fun k => hanti (by omega)
  have hQk : ∀ k : ℤ, (Module.finrank LL (Qk k) : ℤ) =
      (Module.finrank LL (F (-k)) : ℤ) - Module.finrank LL (F (1 - k)) := by
    intro k
    have h1 := Submodule.finrank_quotient_add_finrank ((F (1 - k)).comap (F (-k)).subtype)
    have h2 : Module.finrank LL ((F (1 - k)).comap (F (-k)).subtype) = Module.finrank LL (F (1 - k)) :=
      (Submodule.comapSubtypeEquivOfLe (hle k)).finrank_eq
    simp only [Qk]
    omega
  rw [e.finrank_eq, Module.finrank_pi_fintype]
  have hsum : ((∑ k : S, Module.finrank LL (Qk k) : ℕ) : ℤ) = Module.finrank LL D := by
    push_cast
    rw [Finset.sum_coe_sort S (fun k => (Module.finrank LL (Qk k) : ℤ))]
    simp only [S]
    rw [Finset.sum_image (fun i _ j _ h => by exact_mod_cast (add_left_cancel h : ((i : ℤ)) = j))]
    simp only [hQk]
    have hrw : ∀ j : ℕ, ((Module.finrank LL (F (-(1 - b + (j : ℤ)))) : ℤ) -
        Module.finrank LL (F (1 - (1 - b + (j : ℤ))))) =
        (Module.finrank LL (F (b - ((j + 1 : ℕ) : ℤ))) : ℤ) - Module.finrank LL (F (b - ((j : ℕ) : ℤ))) := by
      intro j
      rw [show -(1 - b + (j : ℤ)) = b - ((j + 1 : ℕ) : ℤ) by push_cast; ring,
        show 1 - (1 - b + (j : ℤ)) = b - ((j : ℕ) : ℤ) by ring]
    simp only [hrw]
    rw [Finset.sum_range_sub (fun j : ℕ => (Module.finrank LL (F (b - (j : ℤ))) : ℤ)) N]
    have h1 : b - ((N : ℕ) : ℤ) = a := by omega
    rw [h1, Nat.cast_zero, sub_zero, htop a le_rfl, hbot b le_rfl, finrank_top, finrank_bot]
    rfl
  exact_mod_cast hsum

end Formalism.MainNotions.N.Ln03.K8
