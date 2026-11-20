import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp

open Matrix Topology

namespace GlobalTheory.JSW.Cut

/- English proof (translation)
Take `⟨T, hT⟩` from `h`. Set `U₁ : Subgroup (GL (Fin n) F)` to `{ carrier := {u | u ∈ U ∧ ∀ k ∈ T.support, k⁻¹ * u * k ∈ U} one_mem' := ⟨one_mem _, fun k _ => by simpa using one_mem U⟩ mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun k hk => by`. Use `mul_mem (ha.2 k hk) (hb.2 k hk)` as an intermediate fact. Simplify `this⟩` using `[mul_assoc]`. Use the proof step `inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun k hk => by`.

Use `inv_mem (ha.2 k hk)` as an intermediate fact. Simplify `this⟩ }` using `[mul_assoc]`. Use `⟨U₁, fun u hu => hu.1, ?_, T, ?_⟩` and prove the remaining obligations. Establish `: (U₁ : Set (GL (Fin n) F)) = (U : Set (GL (Fin n) F)) ∩ ⋂ k ∈ T.support, (fun u : GL (Fin n) F => k⁻¹ * u * k) ⁻¹' (U : Set (GL (Fin n) F))`. Use extensionality with `u`.

Simplify using `only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `hU.inter (isOpen_biInter_finset fun k _ => hU.preimage ((continuous_const.mul continuous_id).mul continuous_const))`. Introduce and unpack `f hf hfU g ⟨a, ha, u, hu, rfl⟩`.

Establish `h1 : act T f (a * u) = act T f a`. Unfold `act`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Establish `e : a * u * k = a * k * (k⁻¹ * u * k)` using `by group`. Simplify using `only`.

Rewrite using `[e, hfU _ (hu.2 k hk)]`. Rewrite using `[h1, hT f hf hfU a ha]`. Distinguish the cases in `hx : a ∈ X`. Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem (hX a hx u hu.1), hfU u hu.1]`. Establish `hx' : a * u ∉ X` using `fun h' => hx (by simpa using hX _ h' u⁻¹ (inv_mem hu.1))`.

Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']`.
-/
theorem cuts_mul_open_subgroup {F : Type} [NormedField F] (ψ : AddChar F ℂ) {n : ℕ}
    (U : Subgroup (GL (Fin n) F)) (hU : IsOpen (U : Set (GL (Fin n) F))) (X A : Set (GL (Fin n) F))
    (hX : ∀ x ∈ X, ∀ u ∈ U, x * u ∈ X) (h : Cuts ψ (U : Set (GL (Fin n) F)) X A) :
    ∃ U₁ : Subgroup (GL (Fin n) F), U₁ ≤ U ∧ IsOpen (U₁ : Set (GL (Fin n) F)) ∧
      Cuts ψ (U : Set (GL (Fin n) F)) X {g | ∃ a ∈ A, ∃ u ∈ U₁, g = a * u} := by
  obtain ⟨T, hT⟩ := h
  let U₁ : Subgroup (GL (Fin n) F) :=
    { carrier := {u | u ∈ U ∧ ∀ k ∈ T.support, k⁻¹ * u * k ∈ U}
      one_mem' := ⟨one_mem _, fun k _ => by simpa using one_mem U⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun k hk => by
        have := mul_mem (ha.2 k hk) (hb.2 k hk)
        simpa [mul_assoc] using this⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun k hk => by
        have := inv_mem (ha.2 k hk)
        simpa [mul_assoc] using this⟩ }
  refine ⟨U₁, fun u hu => hu.1, ?_, T, ?_⟩
  · have : (U₁ : Set (GL (Fin n) F)) = (U : Set (GL (Fin n) F)) ∩
        ⋂ k ∈ T.support, (fun u : GL (Fin n) F => k⁻¹ * u * k) ⁻¹' (U : Set (GL (Fin n) F)) := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
      rfl
    rw [this]
    exact hU.inter (isOpen_biInter_finset fun k _ =>
      hU.preimage ((continuous_const.mul continuous_id).mul continuous_const))
  · rintro f hf hfU g ⟨a, ha, u, hu, rfl⟩
    have h1 : act T f (a * u) = act T f a := by
      unfold act
      refine Finset.sum_congr rfl fun k hk => ?_
      have e : a * u * k = a * k * (k⁻¹ * u * k) := by group
      simp only
      rw [e, hfU _ (hu.2 k hk)]
    rw [h1, hT f hf hfU a ha]
    by_cases hx : a ∈ X
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hX a hx u hu.1), hfU u hu.1]
    · have hx' : a * u ∉ X := fun h' => hx (by simpa using hX _ h' u⁻¹ (inv_mem hu.1))
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']

end GlobalTheory.JSW.Cut
