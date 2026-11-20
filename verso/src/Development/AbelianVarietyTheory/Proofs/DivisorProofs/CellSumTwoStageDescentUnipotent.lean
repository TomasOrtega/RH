import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

open Classical in

/- English proof (translation)
Establish `hS : ∀ (T : X → Prop) [DecidablePred T], (∑ᶠ x, if T x then f x else 0) = ∑ x ∈ hf.toFinset, if T x then f x else 0`. Introduce `T _`. Use `finsum_eq_sum_of_support_subset _ fun x hx => ?_` and prove the remaining obligations. Simplify using `only [Set.Finite.coe_toFinset, Function.mem_support]`. Introduce `h0`.

Conclude with `hx (by simp [h0])`. Establish `hfin : ∀ x, (Function.support fun y => if R y x then f x else 0).Finite`. Introduce `x`. Use `Set.Subsingleton.finite fun y hy y' hy' => hu x y y' ?_ ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h; exact hy (by simp [h])`.

Assume the negation of the conclusion as `h; exact hy' (by simp [h])`. Simplify using `only [hS]`. Prove the components needed by the constructor for the conclusion. Use `(hf.biUnion fun x _ => hfin x).subset fun y hy => ?_` and prove the remaining obligations. Take `⟨x, hx, hx'⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hy`.

Conclude with `Set.mem_biUnion (hf.mem_toFinset.1 hx) hx'`. Rewrite using `[finsum_sum_comm _ _ fun x _ => hfin x]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Distinguish the cases in `hx : Q x`. Take `⟨y, hy⟩` from `(hQ x).1 hx`.

Rewrite using `[finsum_eq_single _ y, if_pos hx, if_pos hy]`. Introduce `y' hy'`. Conclude with `if_neg fun h => hy' (hu x y' y h hy)`. Rewrite using `[if_neg hx]`. Use `symm`.

Conclude with `finsum_eq_zero_of_forall_eq_zero fun y => if_neg fun h => hx ((hQ x).2 ⟨y, h⟩)`.
-/
theorem finsum_partition {X Y : Type} (f : X → ℂ) (Q : X → Prop) (R : Y → X → Prop)
    (hf : (Function.support f).Finite) (hQ : ∀ x, Q x ↔ ∃ y, R y x)
    (hu : ∀ x y y', R y x → R y' x → y = y') :
    (Function.support fun y => ∑ᶠ x, if R y x then f x else 0).Finite ∧
      (∑ᶠ x, if Q x then f x else 0) = ∑ᶠ y, ∑ᶠ x, if R y x then f x else 0 := by
  have hS : ∀ (T : X → Prop) [DecidablePred T],
      (∑ᶠ x, if T x then f x else 0) = ∑ x ∈ hf.toFinset, if T x then f x else 0 := by
    intro T _
    refine finsum_eq_sum_of_support_subset _ fun x hx => ?_
    simp only [Set.Finite.coe_toFinset, Function.mem_support]
    intro h0
    exact hx (by simp [h0])
  have hfin : ∀ x, (Function.support fun y => if R y x then f x else 0).Finite := by
    intro x
    refine Set.Subsingleton.finite fun y hy y' hy' => hu x y y' ?_ ?_
    · by_contra h; exact hy (by simp [h])
    · by_contra h; exact hy' (by simp [h])
  simp only [hS]
  constructor
  · refine (hf.biUnion fun x _ => hfin x).subset fun y hy => ?_
    obtain ⟨x, hx, hx'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
    exact Set.mem_biUnion (hf.mem_toFinset.1 hx) hx'
  · rw [finsum_sum_comm _ _ fun x _ => hfin x]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : Q x
    · obtain ⟨y, hy⟩ := (hQ x).1 hx
      rw [finsum_eq_single _ y, if_pos hx, if_pos hy]
      intro y' hy'
      exact if_neg fun h => hy' (hu x y' y h hy)
    · rw [if_neg hx]
      symm
      exact finsum_eq_zero_of_forall_eq_zero fun y => if_neg fun h => hx ((hQ x).2 ⟨y, h⟩)

/- English proof (translation)
Introduce `G A _ _ K N N' ι h g hf hle hN hdec hK hconj`. Establish `key` using `finsum_partition (fun x : G ⧸ K => h x.out) (fun x => ∃ u ∈ N, ∃ k ∈ K, x.out = g * u * k) (fun (y : A ⧸ K.comap ι) x => ∃ u ∈ N', ∃ k ∈ K, x.out = g * ι y.out * u * k) hf ?_ ?_`. Unfold `cellSum`. Use `key` and compare the differences between its conclusion and the goal. Introduce `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, k, hk, e⟩`. Take `⟨a, u', hu', rfl⟩` from `hdec u hu`. Take `⟨⟨u₀, hu₀⟩, e₀⟩` from `QuotientGroup.mk_out_eq_mul (K.comap ι) a`. Use `⟨QuotientGroup.mk a, ι u₀⁻¹ * u' * (ι u₀⁻¹)⁻¹, hconj _ _ hu', ι u₀⁻¹ * k, K.mul_mem (by rw [map_inv]; exact K.inv_mem hu₀) hk, ?_⟩` and prove the remaining obligations.

Rewrite using `[e, e₀]`. Simplify using `only [map_mul, map_inv]`. Use `group`. Introduce and unpack `⟨y, u, hu, k, hk, e⟩`. Conclude with `⟨ι y.out * u, N.mul_mem (hN _) (hle hu), k, hk, by rw [e]; group⟩`.

Introduce and unpack `x y y' ⟨u₁, hu₁, k₁, hk₁, e₁⟩ ⟨u₂, hu₂, k₂, hk₂, e₂⟩`. Establish `e : ι y.out * u₁ * k₁ = ι y'.out * u₂ * k₂`. Apply `mul_left_cancel (a := g)` to reduce the goal to its premises. Use `e₁.symm.trans e₂` as an intermediate fact. Simplify `this` using `only [mul_assoc]`.

Use `set b := y'.out⁻¹ * y.out with hb`. Establish `hb' : ι b ∈ K`. Use `hK b (ι b⁻¹ * u₂⁻¹ * (ι b⁻¹)⁻¹ * u₁) (N'.mul_mem (hconj _ _ (N'.inv_mem hu₂)) hu₁) ?_` and prove the remaining obligations. Establish `: ι b * (ι b⁻¹ * u₂⁻¹ * (ι b⁻¹)⁻¹ * u₁) = k₂ * k₁⁻¹`. Establish `e' : ι y.out * u₁ = ι y'.out * u₂ * k₂ * k₁⁻¹` using `by rw [← e]; group`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hb, map_mul, map_inv]`. Use `group`. Use `_ = _ := by rw [e']; group`. Rewrite using `[this]`.

Conclude with `K.mul_mem hk₂ (K.inv_mem hk₁)`. Rewrite using `[← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' y']`. Conclude with `(QuotientGroup.eq.2 hb').symm`.
-/
theorem descent : GlobalTheory.SatakeWeyl.Descent := by
  intro G A _ _ K N N' ι h g hf hle hN hdec hK hconj
  have key := finsum_partition (fun x : G ⧸ K => h x.out)
    (fun x => ∃ u ∈ N, ∃ k ∈ K, x.out = g * u * k)
    (fun (y : A ⧸ K.comap ι) x => ∃ u ∈ N', ∃ k ∈ K, x.out = g * ι y.out * u * k) hf ?_ ?_
  · unfold cellSum
    convert key
  · intro x
    constructor
    · rintro ⟨u, hu, k, hk, e⟩
      obtain ⟨a, u', hu', rfl⟩ := hdec u hu
      obtain ⟨⟨u₀, hu₀⟩, e₀⟩ := QuotientGroup.mk_out_eq_mul (K.comap ι) a
      refine ⟨QuotientGroup.mk a, ι u₀⁻¹ * u' * (ι u₀⁻¹)⁻¹, hconj _ _ hu', ι u₀⁻¹ * k,
        K.mul_mem (by rw [map_inv]; exact K.inv_mem hu₀) hk, ?_⟩
      rw [e, e₀]
      simp only [map_mul, map_inv]
      group
    · rintro ⟨y, u, hu, k, hk, e⟩
      exact ⟨ι y.out * u, N.mul_mem (hN _) (hle hu), k, hk, by rw [e]; group⟩
  · rintro x y y' ⟨u₁, hu₁, k₁, hk₁, e₁⟩ ⟨u₂, hu₂, k₂, hk₂, e₂⟩
    have e : ι y.out * u₁ * k₁ = ι y'.out * u₂ * k₂ := by
      apply mul_left_cancel (a := g)
      have := e₁.symm.trans e₂
      simpa only [mul_assoc] using this
    set b := y'.out⁻¹ * y.out with hb
    have hb' : ι b ∈ K := by
      refine hK b (ι b⁻¹ * u₂⁻¹ * (ι b⁻¹)⁻¹ * u₁) (N'.mul_mem (hconj _ _ (N'.inv_mem hu₂)) hu₁) ?_
      have : ι b * (ι b⁻¹ * u₂⁻¹ * (ι b⁻¹)⁻¹ * u₁) = k₂ * k₁⁻¹ := by
        have e' : ι y.out * u₁ = ι y'.out * u₂ * k₂ * k₁⁻¹ := by rw [← e]; group
        calc _ = u₂⁻¹ * (ι y'.out)⁻¹ * (ι y.out * u₁) := by
              simp only [hb, map_mul, map_inv]; group
          _ = _ := by rw [e']; group
      rw [this]
      exact K.mul_mem hk₂ (K.inv_mem hk₁)
    rw [← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' y']
    exact (QuotientGroup.eq.2 hb').symm

end GlobalTheory.SatakeWeyl
