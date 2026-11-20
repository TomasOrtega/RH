import Mathlib

/- English proof (translation)
Introduce `O R K _ _ _ _ _ _ y hfin`. Take `⟨t', ht'⟩` from `hfin.fg_top`. Establish `hsurj : Function.Surjective y.rangeRestrict` using `y.rangeRestrict_surjective`. Take `⟨σ, hσ⟩` from `hsurj.hasRightInverse`. Take `⟨g, hg⟩ : (RingHom.ker y).FG` from `IsNoetherian.noetherian _`.

Set `t : Finset R` to `t'.image σ`. Establish `h1 : ∀ a : R, ∃ b ∈ Submodule.span O (↑t : Set R), a - b ∈ RingHom.ker y`. Introduce `a`. Establish `hm : Submodule.map y.rangeRestrict.toLinearMap (Submodule.span O (↑t : Set R)) = ⊤`. Rewrite using `[Submodule.map_span, eq_top_iff, ← ht']`.

Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce `z hz`. Conclude with `⟨σ z, Finset.mem_coe.2 (Finset.mem_image_of_mem σ hz), hσ z⟩`. Establish `hz : y.rangeRestrict a ∈ Submodule.map y.rangeRestrict.toLinearMap (Submodule.span O (↑t : Set R))`. Rewrite using `[hm]`.

Conclude with `Submodule.mem_top`. Take `⟨b, hb, hab⟩` from `hz`. Use `⟨b, hb, ?_⟩` and prove the remaining obligations. Establish `hab' : y b = y a` using `congrArg Subtype.val hab`. Rewrite using `[RingHom.mem_ker, map_sub, hab', sub_self]`.

Set `s : Finset R` to `t ∪ Finset.image₂ (· * ·) t g`. Establish `h2 : ∀ x ∈ g, ∀ b ∈ Submodule.span O (↑t : Set R), b * x ∈ Submodule.span O (↑s : Set R)`. Introduce `x hx b hb`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem z hz`.

Conclude with `Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image₂_of_mem hz hx)))`. Consider the case `zero => rw [zero_mul]`. Conclude with `zero_mem _`. Consider the case `add u v _ _ hu hv => rw [add_mul]`. Conclude with `add_mem hu hv`.

Consider the case `smul c u _ hu => rw [smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ c hu`. Establish `h3 : ∀ x ∈ Ideal.span (↑g : Set R), ∀ r : R, ∃ b ∈ Submodule.span O (↑s : Set R), r * x - b ∈ RingHom.ker y ^ (2 : ℕ)`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem z hz`. Introduce `r`. Take `⟨b, hb, hrb⟩` from `h1 r`. Use `⟨b * z, h2 z hz b hb, ?_⟩` and prove the remaining obligations. Establish `hzI : z ∈ RingHom.ker y`.

Rewrite using `[← hg]`. Conclude with `Ideal.subset_span hz`. Rewrite using `[← sub_mul, pow_two]`. Conclude with `Ideal.mul_mem_mul hrb hzI`. Consider the case `zero => intro r; exact ⟨0, zero_mem _, by rw [mul_zero, sub_zero]; exact zero_mem _⟩`.

Consider the case `add u v _ _ hu hv`. Introduce `r`. Take `⟨b, hb, hb'⟩` from `hu r`. Take `⟨c, hc, hc'⟩` from `hv r`. Use `⟨b + c, add_mem hb hc, ?_⟩` and prove the remaining obligations.

Establish `e : r * (u + v) - (b + c) = (r * u - b) + (r * v - c)` using `by ring`. Rewrite using `[e]`. Conclude with `add_mem hb' hc'`. Consider the case `smul c u _ hu`. Introduce `r`.

Rewrite using `[smul_eq_mul, ← mul_assoc]`. Conclude with `hu (r * c)`. Use `⟨s, fun a => ?_⟩` and prove the remaining obligations. Take `⟨b, hb, hab⟩` from `h1 a`. Take `⟨c, hc, hc'⟩` from `h3 (a - b) (by rw [hg]; exact hab) 1`.

Use `⟨b + c, add_mem (Submodule.span_mono ?_ hb) hc, ?_⟩` and prove the remaining obligations. Conclude with `Finset.coe_subset.2 Finset.subset_union_left`. Establish `e : a - (b + c) = 1 * (a - b) - c` using `by ring`. Rewrite using `[e]`. Conclude with `hc'`.
-/
theorem UpperTheory.Reformulated.B.Ra7.exists_span_mod_sq :
    ∀ {O R K : Type} [inst : CommRing O]
    [inst_1 : CommRing R] [inst_2 : Algebra O R] [IsNoetherianRing R] [inst_4 : CommRing K] [inst_5 : Algebra O K]
    (y : R →ₐ[O] K),
    Module.Finite O ↥y.range →
      ∃ (s : Finset R), ∀ (a : R), ∃ b ∈ Submodule.span O (↑s : Set R), a - b ∈ RingHom.ker y ^ (2 : ℕ) := by
  intro O R K _ _ _ _ _ _ y hfin
  classical
  obtain ⟨t', ht'⟩ := hfin.fg_top
  have hsurj : Function.Surjective y.rangeRestrict := y.rangeRestrict_surjective
  obtain ⟨σ, hσ⟩ := hsurj.hasRightInverse
  obtain ⟨g, hg⟩ : (RingHom.ker y).FG := IsNoetherian.noetherian _
  let t : Finset R := t'.image σ
  have h1 : ∀ a : R, ∃ b ∈ Submodule.span O (↑t : Set R), a - b ∈ RingHom.ker y := by
    intro a
    have hm : Submodule.map y.rangeRestrict.toLinearMap (Submodule.span O (↑t : Set R)) = ⊤ := by
      rw [Submodule.map_span, eq_top_iff, ← ht']
      apply Submodule.span_mono
      intro z hz
      exact ⟨σ z, Finset.mem_coe.2 (Finset.mem_image_of_mem σ hz), hσ z⟩
    have hz : y.rangeRestrict a ∈
        Submodule.map y.rangeRestrict.toLinearMap (Submodule.span O (↑t : Set R)) := by
      rw [hm]; exact Submodule.mem_top
    obtain ⟨b, hb, hab⟩ := hz
    refine ⟨b, hb, ?_⟩
    have hab' : y b = y a := congrArg Subtype.val hab
    rw [RingHom.mem_ker, map_sub, hab', sub_self]
  let s : Finset R := t ∪ Finset.image₂ (· * ·) t g
  have h2 : ∀ x ∈ g, ∀ b ∈ Submodule.span O (↑t : Set R),
      b * x ∈ Submodule.span O (↑s : Set R) := by
    intro x hx b hb
    induction hb using Submodule.span_induction with
    | mem z hz =>
      exact Submodule.subset_span (Finset.mem_coe.2
        (Finset.mem_union_right _ (Finset.mem_image₂_of_mem hz hx)))
    | zero => rw [zero_mul]; exact zero_mem _
    | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
    | smul c u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hu
  have h3 : ∀ x ∈ Ideal.span (↑g : Set R), ∀ r : R,
      ∃ b ∈ Submodule.span O (↑s : Set R), r * x - b ∈ RingHom.ker y ^ (2 : ℕ) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      intro r
      obtain ⟨b, hb, hrb⟩ := h1 r
      refine ⟨b * z, h2 z hz b hb, ?_⟩
      have hzI : z ∈ RingHom.ker y := by
        rw [← hg]; exact Ideal.subset_span hz
      rw [← sub_mul, pow_two]
      exact Ideal.mul_mem_mul hrb hzI
    | zero => intro r; exact ⟨0, zero_mem _, by rw [mul_zero, sub_zero]; exact zero_mem _⟩
    | add u v _ _ hu hv =>
      intro r
      obtain ⟨b, hb, hb'⟩ := hu r
      obtain ⟨c, hc, hc'⟩ := hv r
      refine ⟨b + c, add_mem hb hc, ?_⟩
      have e : r * (u + v) - (b + c) = (r * u - b) + (r * v - c) := by ring
      rw [e]; exact add_mem hb' hc'
    | smul c u _ hu =>
      intro r
      rw [smul_eq_mul, ← mul_assoc]
      exact hu (r * c)
  refine ⟨s, fun a => ?_⟩
  obtain ⟨b, hb, hab⟩ := h1 a
  obtain ⟨c, hc, hc'⟩ := h3 (a - b) (by rw [hg]; exact hab) 1
  refine ⟨b + c, add_mem (Submodule.span_mono ?_ hb) hc, ?_⟩
  · exact Finset.coe_subset.2 Finset.subset_union_left
  · have e : a - (b + c) = 1 * (a - b) - c := by ring
    rw [e]; exact hc'
