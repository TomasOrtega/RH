import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot

noncomputable section
open IsLocalRing UpperTheory.Et

/- English proof (translation)
Establish `hx' : x ∈ I • (⊤ : Submodule A D)`. Rewrite using `[Ideal.smul_top_eq_map]`. Conclude with `hx`. Use `Submodule.smul_induction_on (p := fun y => β.repr y i ∈ I) hx' ?_ ?_` and prove the remaining obligations. Introduce `a ha n _`.

Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul]`. Conclude with `I.mul_mem_right _ ha`. Introduce `y z hy hz`. Rewrite using `[map_add, Finsupp.add_apply]`. Conclude with `I.add_mem hy hz`.
-/
private theorem coord_mem_of_mem {A D ι : Type} [CommRing A] [CommRing D] [Algebra A D]
    (β : Module.Basis ι A D) (I : Ideal A) {x : D} (hx : x ∈ I.map (algebraMap A D)) (i : ι) :
    β.repr x i ∈ I := by
  have hx' : x ∈ I • (⊤ : Submodule A D) := by
    rw [Ideal.smul_top_eq_map]
    exact hx
  refine Submodule.smul_induction_on (p := fun y => β.repr y i ∈ I) hx' ?_ ?_
  · intro a ha n _
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact I.mul_mem_right _ ha
  · intro y z hy hz
    rw [map_add, Finsupp.add_apply]
    exact I.add_mem hy hz

/- English proof (translation)
Establish `hs : ↑(β.repr x).support ⊆ W` using `(β.mem_span_image).1 hW`. Rewrite using `[← β.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]`. Use `Submodule.sum_mem _ (fun i hi => ?_)` and prove the remaining obligations. Conclude with `Submodule.smul_mem_smul (hc i) (Submodule.subset_span ⟨i, hs hi, rfl⟩)`.
-/
private theorem mem_smul_span_of_coord {A D ι : Type} [CommRing A] [CommRing D] [Algebra A D]
    (β : Module.Basis ι A D) (I : Ideal A) (W : Set ι) {x : D}
    (hW : x ∈ Submodule.span A (β '' W)) (hc : ∀ i, β.repr x i ∈ I) :
    x ∈ I • Submodule.span A (β '' W) := by
  have hs : ↑(β.repr x).support ⊆ W := (β.mem_span_image).1 hW
  rw [← β.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ (fun i hi => ?_)
  exact Submodule.smul_mem_smul (hc i) (Submodule.subset_span ⟨i, hs hi, rfl⟩)

/- English proof (translation)
Rewrite using `[← β.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]`. Use `Ideal.sum_mem _ (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hc i))`.
-/
private theorem mem_map_of_coord {A D ι : Type} [CommRing A] [CommRing D] [Algebra A D]
    (β : Module.Basis ι A D) (I : Ideal A) {x : D} (hc : ∀ i, β.repr x i ∈ I) :
    x ∈ I.map (algebraMap A D) := by
  rw [← β.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Ideal.sum_mem _ (fun i _ => ?_)
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hc i))

/- English proof (translation)
Introduce `A D _ _ _ T hF hC I`. Take `⟨ι, β, U, V, hU, hV⟩` from `hC`. Use `set J := I.map (algebraMap A D) with hJ`. Set `q` to `Ideal.Quotient.mkₐ A J`. Establish `hq : ∀ z, q z = Ideal.Quotient.mk J z` using `fun z => rfl`.

Establish `hsurj : Function.Surjective (Ideal.Quotient.mk J)` using `Ideal.Quotient.mk_surjective`. Establish `h1 : Ideal.Quotient.mk J T.t * Ideal.Quotient.mk J T.s = 1`. Rewrite using `[← map_mul, T.ts, map_one]`. Set `T' : TC A (D ⧸ J)` to `{ B := T.B.map q C := T.C.map q t := Ideal.Quotient.mk J T.t s := Ideal.Quotient.mk J T.s ts := h1 tB := Subalgebra.mem_map.2 ⟨T.t, T.tB, rfl⟩ sC := Subalgebra.mem_map.2 ⟨T.s, T.sC, rfl⟩ locB := by`. Introduce `y`.

Take `⟨x, rfl⟩` from `hsurj y`. Take `⟨k, hk⟩` from `T.locB x`. Conclude with `⟨k, Subalgebra.mem_map.2 ⟨_, hk, by rw [hq, map_mul, map_pow]⟩⟩`. Use `locC := by`. Introduce `y`.

Take `⟨x, rfl⟩` from `hsurj y`. Take `⟨k, hk⟩` from `T.locC x`. Conclude with `⟨k, Subalgebra.mem_map.2 ⟨_, hk, by rw [hq, map_mul, map_pow]⟩⟩ }`. Use `⟨T', ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨X, hX1, hX2⟩` from `hF`.

Use `⟨X.image q, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hy`. Conclude with `Subalgebra.mem_map.2 ⟨x, hX1 x hx, rfl⟩`. Introduce `b hb`.

Take `⟨b0, hb0, rfl⟩` from `Subalgebra.mem_map.1 hb`. Establish `hm` using `Submodule.mem_map_of_mem (f := q.toLinearMap) (hX2 b0 hb0)`. Rewrite `hm` using `[Submodule.map_span]`. Use `Submodule.span_mono ?_ hm` and prove the remaining obligations. Introduce and unpack `_ ⟨y, ⟨x, hx, i, rfl⟩, rfl⟩`.

Use `⟨q x, Finset.mem_image.2 ⟨x, hx, rfl⟩, i, ?_⟩` and prove the remaining obligations. Use `show q (T.t ^ i * x) = Ideal.Quotient.mk J T.t ^ i * q x`. Rewrite using `[map_mul, map_pow]`. Both sides reduce to the same expression. Introduce `j y hy`.

Take `⟨hyB, hyC⟩` from `Submodule.mem_inf.1 hy`. Take `⟨b, hb, rfl⟩` from `Subalgebra.mem_map.1 hyB`. Take `⟨c, hc, hce⟩` from `Subalgebra.mem_map.1 (Submodule.mem_comap.1 hyC)`. Establish `hw : T.t ^ j * c ∈ Submodule.span A (β '' V j)`. Rewrite using `[← (hV j).1, Submodule.mem_comap, LinearMap.mulLeft_apply, ← mul_assoc, ← mul_pow, mul_comm T.s, T.ts, one_pow, one_mul]`.

Conclude with `hc`. Establish `hbw : b - T.t ^ j * c ∈ J`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_pow, ← hq c, hce]`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk J b - Ideal.Quotient.mk J T.t ^ j * (Ideal.Quotient.mk J T.s ^ j * Ideal.Quotient.mk J b) = 0`. Rewrite using `[← mul_assoc, ← mul_pow, h1, one_pow, one_mul, sub_self]`.

Establish `hcoord` using `coord_mem_of_mem β I hbw`. Establish `hbU : ↑(β.repr b).support ⊆ U` using `β.mem_span_image.1 (by rw [← hU]; exact hb)`. Establish `hwV : ↑(β.repr (T.t ^ j * c)).support ⊆ V j` using `β.mem_span_image.1 hw`. Use `set f := Finsupp.filter (· ∈ V j) (β.repr b) with hf`. Establish `hrx : β.repr (β.repr.symm f) = f` using `β.repr.apply_symm_apply f`.

Use `⟨β.repr.symm f, Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show β.repr.symm f ∈ Subalgebra.toSubmodule T.B`. Rewrite using `[hU, β.mem_span_image, hrx]`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_coe, hf, Finsupp.support_filter, Finset.mem_filter]`.

Conclude with `hbU hi.1`. Use `show β.repr.symm f ∈ Submodule.comap (LinearMap.mulLeft A (T.s ^ j)) (Subalgebra.toSubmodule T.C)`. Rewrite using `[(hV j).1, β.mem_span_image, hrx]`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_coe, hf, Finsupp.support_filter, Finset.mem_filter]`.

Conclude with `hi.2`. Use `Ideal.Quotient.eq.2 (mem_map_of_coord β I (fun i => ?_))` and prove the remaining obligations. Rewrite using `[map_sub, Finsupp.sub_apply, hrx, hf, Finsupp.filter_apply]`. Distinguish the cases in `hi : i ∈ V j`. Rewrite using `[if_pos hi, sub_self]`.

Conclude with `I.zero_mem`. Rewrite using `[if_neg hi, zero_sub]`. Establish `hw0 : β.repr (T.t ^ j * c) i = 0` using `Finsupp.notMem_support_iff.1 (fun h => hi (hwV h))`. Establish `hci` using `hcoord i`. Rewrite `hci` using `[map_sub, Finsupp.sub_apply, hw0, sub_zero]`.

Conclude with `I.neg_mem hci`. Introduce `j x hx`. Take `⟨hxB, hxC⟩` from `Submodule.mem_inf.1 hx`. Use `Submodule.mem_inf.2 ⟨Subalgebra.mem_map.2 ⟨x, hxB, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show Ideal.Quotient.mk J T.s ^ j * Ideal.Quotient.mk J x ∈ T.C.map q`.

Conclude with `Subalgebra.mem_map.2 ⟨T.s ^ j * x, hxC, by rw [hq, map_mul, map_pow]⟩`. Introduce `x hx hxJ`. Establish `hxs : x ∈ Submodule.span A (β '' U)` using `by rw [← hU]; exact hx`. Rewrite using `[hU]`. Conclude with `mem_smul_span_of_coord β I U hxs (coord_mem_of_mem β I hxJ)`.

Introduce `x hx hxJ`. Establish `hC0 : Subalgebra.toSubmodule T.C = Submodule.span A (β '' V 0)`. Rewrite using `[← (hV 0).1, pow_zero, LinearMap.mulLeft_one, Submodule.comap_id]`. Establish `hxs : x ∈ Submodule.span A (β '' V 0)` using `by rw [← hC0]; exact hx`. Rewrite using `[hC0]`.

Conclude with `mem_smul_span_of_coord β I (V 0) hxs (coord_mem_of_mem β I hxJ)`.
-/
theorem UpperTheory.exists_twoChart_quotient_of_finite_coord :
    ∀ (A D : Type) [CommRing A] [CommRing D] [Algebra A D] (T : TC A D), T.Fin → T.Coord → ∀ I : Ideal A, ∃ T' : TC A (D ⧸ I.map (algebraMap A D)), T'.Fin ∧ T'.t = Ideal.Quotient.mk _ T.t ∧ T'.s = Ideal.Quotient.mk _ T.s ∧
      (∀ j, ∀ y ∈ T'.S j, ∃ x ∈ T.S j, Ideal.Quotient.mk _ x = y) ∧ (∀ j, ∀ x ∈ T.S j, Ideal.Quotient.mk _ x ∈ T'.S j) ∧
      (∀ x ∈ T.B, x ∈ I.map (algebraMap A D) → x ∈ I • Subalgebra.toSubmodule T.B) ∧ ∀ x ∈ T.C, x ∈ I.map (algebraMap A D) → x ∈ I • Subalgebra.toSubmodule T.C := by
  classical
  intro A D _ _ _ T hF hC I
  obtain ⟨ι, β, U, V, hU, hV⟩ := hC
  set J := I.map (algebraMap A D) with hJ
  let q := Ideal.Quotient.mkₐ A J
  have hq : ∀ z, q z = Ideal.Quotient.mk J z := fun z => rfl
  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  have h1 : Ideal.Quotient.mk J T.t * Ideal.Quotient.mk J T.s = 1 := by
    rw [← map_mul, T.ts, map_one]
  let T' : TC A (D ⧸ J) :=
    { B := T.B.map q
      C := T.C.map q
      t := Ideal.Quotient.mk J T.t
      s := Ideal.Quotient.mk J T.s
      ts := h1
      tB := Subalgebra.mem_map.2 ⟨T.t, T.tB, rfl⟩
      sC := Subalgebra.mem_map.2 ⟨T.s, T.sC, rfl⟩
      locB := by
        intro y
        obtain ⟨x, rfl⟩ := hsurj y
        obtain ⟨k, hk⟩ := T.locB x
        exact ⟨k, Subalgebra.mem_map.2 ⟨_, hk, by rw [hq, map_mul, map_pow]⟩⟩
      locC := by
        intro y
        obtain ⟨x, rfl⟩ := hsurj y
        obtain ⟨k, hk⟩ := T.locC x
        exact ⟨k, Subalgebra.mem_map.2 ⟨_, hk, by rw [hq, map_mul, map_pow]⟩⟩ }
  refine ⟨T', ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · obtain ⟨X, hX1, hX2⟩ := hF
    refine ⟨X.image q, ?_, ?_⟩
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact Subalgebra.mem_map.2 ⟨x, hX1 x hx, rfl⟩
    · intro b hb
      obtain ⟨b0, hb0, rfl⟩ := Subalgebra.mem_map.1 hb
      have hm := Submodule.mem_map_of_mem (f := q.toLinearMap) (hX2 b0 hb0)
      rw [Submodule.map_span] at hm
      refine Submodule.span_mono ?_ hm
      rintro _ ⟨y, ⟨x, hx, i, rfl⟩, rfl⟩
      refine ⟨q x, Finset.mem_image.2 ⟨x, hx, rfl⟩, i, ?_⟩
      show q (T.t ^ i * x) = Ideal.Quotient.mk J T.t ^ i * q x
      rw [map_mul, map_pow]
      rfl
  · intro j y hy
    obtain ⟨hyB, hyC⟩ := Submodule.mem_inf.1 hy
    obtain ⟨b, hb, rfl⟩ := Subalgebra.mem_map.1 hyB
    obtain ⟨c, hc, hce⟩ := Subalgebra.mem_map.1 (Submodule.mem_comap.1 hyC)
    have hw : T.t ^ j * c ∈ Submodule.span A (β '' V j) := by
      rw [← (hV j).1, Submodule.mem_comap, LinearMap.mulLeft_apply, ← mul_assoc, ← mul_pow,
        mul_comm T.s, T.ts, one_pow, one_mul]
      exact hc
    have hbw : b - T.t ^ j * c ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_pow, ← hq c, hce]
      change Ideal.Quotient.mk J b - Ideal.Quotient.mk J T.t ^ j *
        (Ideal.Quotient.mk J T.s ^ j * Ideal.Quotient.mk J b) = 0
      rw [← mul_assoc, ← mul_pow, h1, one_pow, one_mul, sub_self]
    have hcoord := coord_mem_of_mem β I hbw
    have hbU : ↑(β.repr b).support ⊆ U := β.mem_span_image.1 (by rw [← hU]; exact hb)
    have hwV : ↑(β.repr (T.t ^ j * c)).support ⊆ V j := β.mem_span_image.1 hw
    set f := Finsupp.filter (· ∈ V j) (β.repr b) with hf
    have hrx : β.repr (β.repr.symm f) = f := β.repr.apply_symm_apply f
    refine ⟨β.repr.symm f, Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · show β.repr.symm f ∈ Subalgebra.toSubmodule T.B
      rw [hU, β.mem_span_image, hrx]
      intro i hi
      rw [Finset.mem_coe, hf, Finsupp.support_filter, Finset.mem_filter] at hi
      exact hbU hi.1
    · show β.repr.symm f ∈ Submodule.comap (LinearMap.mulLeft A (T.s ^ j)) (Subalgebra.toSubmodule T.C)
      rw [(hV j).1, β.mem_span_image, hrx]
      intro i hi
      rw [Finset.mem_coe, hf, Finsupp.support_filter, Finset.mem_filter] at hi
      exact hi.2
    · refine Ideal.Quotient.eq.2 (mem_map_of_coord β I (fun i => ?_))
      rw [map_sub, Finsupp.sub_apply, hrx, hf, Finsupp.filter_apply]
      by_cases hi : i ∈ V j
      · rw [if_pos hi, sub_self]
        exact I.zero_mem
      · rw [if_neg hi, zero_sub]
        have hw0 : β.repr (T.t ^ j * c) i = 0 := Finsupp.notMem_support_iff.1 (fun h => hi (hwV h))
        have hci := hcoord i
        rw [map_sub, Finsupp.sub_apply, hw0, sub_zero] at hci
        exact I.neg_mem hci
  · intro j x hx
    obtain ⟨hxB, hxC⟩ := Submodule.mem_inf.1 hx
    refine Submodule.mem_inf.2 ⟨Subalgebra.mem_map.2 ⟨x, hxB, rfl⟩, ?_⟩
    show Ideal.Quotient.mk J T.s ^ j * Ideal.Quotient.mk J x ∈ T.C.map q
    exact Subalgebra.mem_map.2 ⟨T.s ^ j * x, hxC, by rw [hq, map_mul, map_pow]⟩
  · intro x hx hxJ
    have hxs : x ∈ Submodule.span A (β '' U) := by rw [← hU]; exact hx
    rw [hU]
    exact mem_smul_span_of_coord β I U hxs (coord_mem_of_mem β I hxJ)
  · intro x hx hxJ
    have hC0 : Subalgebra.toSubmodule T.C = Submodule.span A (β '' V 0) := by
      rw [← (hV 0).1, pow_zero, LinearMap.mulLeft_one, Submodule.comap_id]
    have hxs : x ∈ Submodule.span A (β '' V 0) := by rw [← hC0]; exact hx
    rw [hC0]
    exact mem_smul_span_of_coord β I (V 0) hxs (coord_mem_of_mem β I hxJ)

end
