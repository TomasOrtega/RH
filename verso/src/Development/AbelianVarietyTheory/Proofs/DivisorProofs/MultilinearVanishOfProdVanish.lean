import Mathlib

open Finset Function

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Introduce `D s c f hconst hx`. Break down `s.eq_empty_or_nonempty with rfl | ⟨d₀, hd₀⟩` into its components or cases. Simplify using the standard rewrite rules.

Establish `hf : ∀ d ∈ s, f d = f d₀` using `fun d hd =>`. Use function extensionality and compare the values at `fun i => hconst i (Finset.notMem_empty i) d hd d₀ hd₀`. Establish `hsum : ∑ d ∈ s, c d • P (f d) = (∑ d ∈ s, c d) • P (f d₀)`. Rewrite using `[Finset.sum_smul]; exact Finset.sum_congr rfl fun d hd => by rw [hf d hd]`. Establish `hx' : ∀ x : ∀ i, X i, (∑ d ∈ s, c d) * ∏ i, (f d₀ i : X i → K) (x i) = 0`.

Introduce `x`. Rewrite using `[Finset.sum_mul, ← hx x]`. Conclude with `Finset.sum_congr rfl fun d hd => by rw [hf d hd]`. Rewrite using `[hsum]`. Distinguish the cases in `hc : ∑ d ∈ s, c d = 0`.

Rewrite using `[hc, zero_smul]`. Assume the negation of the conclusion as `hne`. Establish `hex : ∀ i, ∃ t : X i, (f d₀ i : X i → K) t ≠ 0`. Introduce `i`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Apply `hne` to reduce the goal to its premises. Establish `h0 : f d₀ i = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `t`.

Simplify using `using h t`. Rewrite using `[P.map_coord_zero i h0, smul_zero]`. Use `choose x hxne using hex`. Establish `h1` using `hx' x`. Rewrite `h1` using `[mul_eq_zero]`.

Break down `h1 with h | h` into its components or cases. Conclude with `hc h`. Conclude with `(Finset.prod_ne_zero_iff.mpr fun i _ => hxne i) h`. Consider the case `insert i₀ S hi₀ ih`. Introduce `D s c f hconst hx`.

Set `W : Submodule K (A i₀)` to `Submodule.span K (↑(s.image fun d => f d i₀))`. Set `b` to `Module.finBasis K W`. Establish `hmem : ∀ d ∈ s, f d i₀ ∈ W` using `fun d hd => Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨d, hd, rfl⟩)`. Set `a : D → Fin (Module.finrank K W) → K` to `fun d l => if hd : d ∈ s then b.repr ⟨f d i₀, hmem d hd⟩ l else 0`. Establish `hexp : ∀ d ∈ s, f d i₀ = ∑ l, a d l • (b l : A i₀)`.

Introduce `d hd`. Establish `h` using `congrArg Subtype.val (b.sum_repr ⟨f d i₀, hmem d hd⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h`. Simplify using `only [a, dif_pos hd]`. Conclude with `h.symm`.

Establish `hP : ∀ d ∈ s, P (f d) = ∑ l, a d l • P (update (f d) i₀ (b l))`. Introduce `d hd`. Establish `e : f d = update (f d) i₀ (∑ l, a d l • (b l : A i₀))`. Rewrite using `[← hexp d hd, update_eq_self]`. Rewrite using `[e, P.map_update_sum]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[P.map_update_smul, update_idem]`. Establish `hsplit : ∀ (g : ∀ i, A i) (y : ∀ i, X i), ∏ i, (g i : X i → K) (y i) = (g i₀ : X i₀ → K) (y i₀) * ∏ i ∈ univ.erase i₀, (g i : X i → K) (y i)` using `fun g y => (Finset.mul_prod_erase univ (fun i => (g i : X i → K) (y i)) (mem_univ i₀)).symm`. Establish `hupd : ∀ (g : ∀ i, A i) (v : A i₀) (y : ∀ i, X i), ∏ i ∈ univ.erase i₀, (update g i₀ v i : X i → K) (y i) = ∏ i ∈ univ.erase i₀, (g i : X i → K) (y i)` using `fun g v y => Finset.prod_congr rfl fun i hi => by rw [update_of_ne (Finset.ne_of_mem_erase hi)]`. Establish `hupdx : ∀ (g : ∀ i, A i) (y : ∀ i, X i) (t : X i₀), ∏ i ∈ univ.erase i₀, (g i : X i → K) (update y i₀ t i) = ∏ i ∈ univ.erase i₀, (g i : X i → K) (y i)` using `fun g y t => Finset.prod_congr rfl fun i hi => by rw [update_of_ne (Finset.ne_of_mem_erase hi)]`.

Establish `hli : LinearIndependent K (fun l => ((b l : A i₀) : X i₀ → K))` using `b.linearIndependent.map' ((A i₀).subtype ∘ₗ W.subtype) (LinearMap.ker_eq_bot_of_injective (Subtype.val_injective.comp Subtype.val_injective))`. Establish `hB : ∀ (x : ∀ i, X i) (l : Fin (Module.finrank K W)), ∑ d ∈ s, c d * a d l * ∏ i ∈ univ.erase i₀, (f d i : X i → K) (x i) = 0`. Introduce `x`. Use `Fintype.linearIndependent_iff.mp hli _ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `t`.

Establish `h` using `hx (update x i₀ t)`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]`. Rewrite using `[← h]`. Simplify using `only [Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Rewrite using `[hsplit, hupdx, update_self, hexp d hd]`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `hstep : ∑ d ∈ s, c d • P (f d) = ∑ l, ∑ d ∈ s, (c d * a d l) • P (update (f d) i₀ (b l))`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Rewrite using `[hP d hd, Finset.smul_sum]`. Simplify using `only [mul_smul]`.

Rewrite using `[hstep]`. Use `Finset.sum_eq_zero fun l _ => ih s (fun d => c d * a d l) (fun d => update (f d) i₀ (b l)) ?_ ?_` and prove the remaining obligations. Introduce `i hi d hd d' hd'`. Distinguish the cases in `h : i = i₀`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `only [update_of_ne h]`. Conclude with `hconst i (by simp [h, hi]) d hd d' hd'`. Introduce `x`. Establish `h` using `hB x l`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[hsplit, hupd, update_self]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = 0 := by rw [h, mul_zero]`.
-/
theorem multilinear_vanish_of_prod_vanish_of_agree_off_finset {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {X : ι → Type} (A : ∀ i, Submodule K (X i → K)) {M : Type} [AddCommGroup M]
    [Module K M] (P : MultilinearMap K (fun i => A i) M) (S : Finset ι) :
    ∀ {D : Type} (s : Finset D) (c : D → K) (f : D → ∀ i, A i),
      (∀ i ∉ S, ∀ d ∈ s, ∀ d' ∈ s, f d i = f d' i) →
      (∀ x : ∀ i, X i, ∑ d ∈ s, c d * ∏ i, (f d i : X i → K) (x i) = 0) →
      ∑ d ∈ s, c d • P (f d) = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    intro D s c f hconst hx
    rcases s.eq_empty_or_nonempty with rfl | ⟨d₀, hd₀⟩
    · simp
    have hf : ∀ d ∈ s, f d = f d₀ := fun d hd =>
      funext fun i => hconst i (Finset.notMem_empty i) d hd d₀ hd₀
    have hsum : ∑ d ∈ s, c d • P (f d) = (∑ d ∈ s, c d) • P (f d₀) := by
      rw [Finset.sum_smul]; exact Finset.sum_congr rfl fun d hd => by rw [hf d hd]
    have hx' : ∀ x : ∀ i, X i, (∑ d ∈ s, c d) * ∏ i, (f d₀ i : X i → K) (x i) = 0 := by
      intro x; rw [Finset.sum_mul, ← hx x]
      exact Finset.sum_congr rfl fun d hd => by rw [hf d hd]
    rw [hsum]
    by_cases hc : ∑ d ∈ s, c d = 0
    · rw [hc, zero_smul]
    · by_contra hne
      have hex : ∀ i, ∃ t : X i, (f d₀ i : X i → K) t ≠ 0 := by
        intro i
        by_contra h
        push_neg at h
        apply hne
        have h0 : f d₀ i = 0 := by
          apply Subtype.ext
          funext t
          simpa using h t
        rw [P.map_coord_zero i h0, smul_zero]
      choose x hxne using hex
      have h1 := hx' x
      rw [mul_eq_zero] at h1
      rcases h1 with h | h
      · exact hc h
      · exact (Finset.prod_ne_zero_iff.mpr fun i _ => hxne i) h
  | insert i₀ S hi₀ ih =>
    intro D s c f hconst hx
    classical
    let W : Submodule K (A i₀) := Submodule.span K (↑(s.image fun d => f d i₀))
    let b := Module.finBasis K W
    have hmem : ∀ d ∈ s, f d i₀ ∈ W := fun d hd =>
      Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨d, hd, rfl⟩)
    let a : D → Fin (Module.finrank K W) → K := fun d l =>
      if hd : d ∈ s then b.repr ⟨f d i₀, hmem d hd⟩ l else 0
    have hexp : ∀ d ∈ s, f d i₀ = ∑ l, a d l • (b l : A i₀) := by
      intro d hd
      have h := congrArg Subtype.val (b.sum_repr ⟨f d i₀, hmem d hd⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      simp only [a, dif_pos hd]
      exact h.symm
    have hP : ∀ d ∈ s, P (f d) = ∑ l, a d l • P (update (f d) i₀ (b l)) := by
      intro d hd
      have e : f d = update (f d) i₀ (∑ l, a d l • (b l : A i₀)) := by
        rw [← hexp d hd, update_eq_self]
      rw [e, P.map_update_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [P.map_update_smul, update_idem]

    have hsplit : ∀ (g : ∀ i, A i) (y : ∀ i, X i), ∏ i, (g i : X i → K) (y i) =
        (g i₀ : X i₀ → K) (y i₀) * ∏ i ∈ univ.erase i₀, (g i : X i → K) (y i) := fun g y =>
      (Finset.mul_prod_erase univ (fun i => (g i : X i → K) (y i)) (mem_univ i₀)).symm
    have hupd : ∀ (g : ∀ i, A i) (v : A i₀) (y : ∀ i, X i),
        ∏ i ∈ univ.erase i₀, (update g i₀ v i : X i → K) (y i) =
          ∏ i ∈ univ.erase i₀, (g i : X i → K) (y i) := fun g v y =>
      Finset.prod_congr rfl fun i hi => by rw [update_of_ne (Finset.ne_of_mem_erase hi)]
    have hupdx : ∀ (g : ∀ i, A i) (y : ∀ i, X i) (t : X i₀),
        ∏ i ∈ univ.erase i₀, (g i : X i → K) (update y i₀ t i) =
          ∏ i ∈ univ.erase i₀, (g i : X i → K) (y i) := fun g y t =>
      Finset.prod_congr rfl fun i hi => by rw [update_of_ne (Finset.ne_of_mem_erase hi)]
    have hli : LinearIndependent K (fun l => ((b l : A i₀) : X i₀ → K)) :=
      b.linearIndependent.map' ((A i₀).subtype ∘ₗ W.subtype)
        (LinearMap.ker_eq_bot_of_injective (Subtype.val_injective.comp Subtype.val_injective))

    have hB : ∀ (x : ∀ i, X i) (l : Fin (Module.finrank K W)),
        ∑ d ∈ s, c d * a d l * ∏ i ∈ univ.erase i₀, (f d i : X i → K) (x i) = 0 := by
      intro x
      refine Fintype.linearIndependent_iff.mp hli _ ?_
      funext t
      have h := hx (update x i₀ t)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h]
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [hsplit, hupdx, update_self, hexp d hd]
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    have hstep : ∑ d ∈ s, c d • P (f d) =
        ∑ l, ∑ d ∈ s, (c d * a d l) • P (update (f d) i₀ (b l)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [hP d hd, Finset.smul_sum]
      simp only [mul_smul]
    rw [hstep]
    refine Finset.sum_eq_zero fun l _ => ih s (fun d => c d * a d l)
      (fun d => update (f d) i₀ (b l)) ?_ ?_
    · intro i hi d hd d' hd'
      by_cases h : i = i₀
      · subst h; simp
      · simp only [update_of_ne h]
        exact hconst i (by simp [h, hi]) d hd d' hd'
    · intro x
      have h := hB x l
      calc ∑ d ∈ s, c d * a d l * ∏ i, (update (f d) i₀ (b l) i : X i → K) (x i)
          = ((b l : A i₀) : X i₀ → K) (x i₀) *
              ∑ d ∈ s, c d * a d l * ∏ i ∈ univ.erase i₀, (f d i : X i → K) (x i) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [hsplit, hupd, update_self]
            ring
        _ = 0 := by rw [h, mul_zero]

/- English proof (translation)
The claim follows from `multilinear_vanish_of_prod_vanish_of_agree_off_finset A P univ s c f (fun i hi => absurd (mem_univ i) hi) hx`.
-/
theorem multilinear_vanish_of_prod_vanish {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {X : ι → Type} (A : ∀ i, Submodule K (X i → K)) {M : Type} [AddCommGroup M]
    [Module K M] (P : MultilinearMap K (fun i => A i) M) {D : Type} (s : Finset D) (c : D → K)
    (f : D → ∀ i, A i)
    (hx : ∀ x : ∀ i, X i, ∑ d ∈ s, c d * ∏ i, (f d i : X i → K) (x i) = 0) :
    ∑ d ∈ s, c d • P (f d) = 0 :=
  multilinear_vanish_of_prod_vanish_of_agree_off_finset A P univ s c f (fun i hi => absurd (mem_univ i) hi) hx

end GlobalTheory
