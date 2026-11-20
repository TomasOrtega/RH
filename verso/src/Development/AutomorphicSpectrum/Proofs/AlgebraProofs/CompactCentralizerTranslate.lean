import Mathlib

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.CommAlg

open AddMonoidAlgebra in

/- English proof (translation)
Introduce `k X A _ _ _ _ _ φ _`. Take `⟨u, hu⟩ : ∃ u : X → A, ∀ x, u x = φ (AddMonoidAlgebra.single x 1)` from `⟨_, fun _ => rfl⟩`. Establish `hmul : ∀ x y, u (x + y) = u x * u y`. Introduce `x y`. Rewrite using `[hu, hu, hu, ← map_mul, AddMonoidAlgebra.single_mul_single, one_mul]`.

Establish `hzero : u 0 = 1`. Rewrite using `[hu, ← AddMonoidAlgebra.one_def, map_one]`. Establish `hinv : ∀ x, u x * u (-x) = 1`. Introduce `x`. Rewrite using `[← hmul, add_neg_cancel, hzero]`.

Establish `hgl : ∀ x, IsGroupLikeElem k (u x)` using `fun x => by`. Rewrite using `[hu]`. Conclude with `(AddMonoidAlgebra.isGroupLikeElem_single_one (R := k) (A := k) x).map φ`. Set `Y : AddSubgroup X` to `{ carrier := {x | u x = 1} zero_mem' := hzero add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_ofPred_eq] at ha hb ⊢`.

Rewrite using `[hmul, ha, hb, one_mul]`. Use the proof step `neg_mem' := fun {a} ha => by`. Simplify using `only [Set.mem_ofPred_eq] at ha ⊢`. Simplify `hinv a }` using `[ha]`. Establish `hY : ∀ x, x ∈ Y ↔ u x = 1` using `fun _ => Iff.rfl`.

Use `⟨Y, ?_⟩` and prove the remaining obligations. Establish `hker : ∀ f, f ∈ RingHom.ker (φ : AddMonoidAlgebra k X →+* A) ↔ φ f = 0` using `fun f => RingHom.mem_ker`. Establish `hle : Ideal.span {f | ∃ y ∈ Y, f = AddMonoidAlgebra.single y (1 : k) - 1} ≤ RingHom.ker (φ : AddMonoidAlgebra k X →+* A)`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Rewrite using `[SetLike.mem_coe, hker, map_sub, map_one, ← hu, (hY y).mp hy, sub_self]`. Use `le_antisymm ?_ hle` and prove the remaining obligations. Introduce `f hf`. Rewrite `hf` using `[hker]`. Set `r : X → X` to `fun x => (QuotientAddGroup.mk x : X ⧸ Y).out`.

Establish `hr : ∀ x, (QuotientAddGroup.mk (r x) : X ⧸ Y) = QuotientAddGroup.mk x` using `fun x => Quotient.out_eq _`. Establish `hcoset : ∀ x (c : k), AddMonoidAlgebra.single x c - AddMonoidAlgebra.single (r x) c ∈ Ideal.span {f | ∃ y ∈ Y, f = AddMonoidAlgebra.single y (1 : k) - 1}`. Introduce `x c`. Establish `e : AddMonoidAlgebra.single x c - AddMonoidAlgebra.single (r x) c = AddMonoidAlgebra.single (r x) c * (AddMonoidAlgebra.single (-(r x) + x) 1 - 1)`. Rewrite using `[mul_sub, mul_one, AddMonoidAlgebra.single_mul_single, mul_one, add_neg_cancel_left]`.

Rewrite using `[e]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, QuotientAddGroup.eq.mp (hr x), rfl⟩)`. Take `⟨G, hG⟩ : ∃ G : AddMonoidAlgebra k X, G = f.coeff.sum (fun x c => AddMonoidAlgebra.single (r x) c)` from `⟨_, rfl⟩`. Establish `hfG : f - G ∈ Ideal.span {f | ∃ y ∈ Y, f = AddMonoidAlgebra.single y (1 : k) - 1}`. Establish `e : f - G = f.coeff.sum (fun x c => AddMonoidAlgebra.single x c - AddMonoidAlgebra.single (r x) c)`.

Rewrite using `[Finsupp.sum_sub, AddMonoidAlgebra.sum_coeff_single, hG]`. Rewrite using `[e]`. Unfold `Finsupp.sum`. Conclude with `Ideal.sum_mem _ (fun x _ => hcoset x _)`. Establish `hφ : ∀ g : AddMonoidAlgebra k X, φ g = Finsupp.linearCombination k u g.coeff`.

Introduce `g`. Use `conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single g]`. Rewrite using `[map_finsuppSum, Finsupp.linearCombination_apply]`. Use `Finsupp.sum_congr (fun x _ => ?_)` and prove the remaining obligations. Rewrite using `[hu, show AddMonoidAlgebra.single x (g.coeff x) = g.coeff x • AddMonoidAlgebra.single x (1 : k) by rw [AddMonoidAlgebra.smul_single', mul_one], map_smul]`.

Establish `hG0 : φ G = 0`. Establish `h1 : φ (f - G) = 0` using `(hker _).mp (hle hfG)`. Rewrite `h1` using `[map_sub, hf, zero_sub, neg_eq_zero]`. Conclude with `h1`. Establish `hinj : Set.InjOn u (Set.range r)`.

Introduce and unpack `_ ⟨x, rfl⟩ _ ⟨x', rfl⟩ h`. Establish `hm : -(r x) + r x' ∈ Y`. Rewrite using `[hY, hmul]`. Establish `h2 : u (-(r x)) * u (r x) = 1`. Rewrite using `[mul_comm]`.

Conclude with `hinv _`. Rewrite using `[← h]`. Conclude with `h2`. Establish `e1 : (QuotientAddGroup.mk (r x) : X ⧸ Y) = QuotientAddGroup.mk (r x')` using `QuotientAddGroup.eq.mpr hm`. Establish `e2 : (QuotientAddGroup.mk x : X ⧸ Y) = QuotientAddGroup.mk x'` using `(hr x).symm.trans (e1.trans (hr x'))`.

Use `show (QuotientAddGroup.mk x : X ⧸ Y).out = (QuotientAddGroup.mk x' : X ⧸ Y).out`. Rewrite using `[e2]`. Establish `hli : LinearIndepOn k u (Set.range r)`. Rewrite using `[linearIndepOn_iff_image hinj]`. Use `(linearIndepOn_isGroupLikeElem (R := k) (A := A)).mono ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨_, ⟨x, rfl⟩, rfl⟩`. Conclude with `hgl (r x)`. Establish `hsupp : G.coeff ∈ Finsupp.supported k k (Set.range r)`. Rewrite using `[hG, AddMonoidAlgebra.coeff_finsuppSum]`. Unfold `Finsupp.sum`.

Conclude with `Submodule.sum_mem _ (fun x _ => Finsupp.single_mem_supported k _ (Set.mem_range_self x))`. Establish `hGc : G.coeff = 0`. Rewrite `hli` using `[linearIndepOn_iff]`. Conclude with `hli _ hsupp (by rw [← hφ]; exact hG0)`. Establish `hGz : G = 0` using `AddMonoidAlgebra.coeff_injective hGc`.

Simplify `hfG` using `[hGz]`.
-/
theorem ker_eq_span_single_sub_one :
    ∀ (k X A : Type) [Field k] [AddCommGroup X] [CommRing A] [Nontrivial A] [Bialgebra k A]
      (φ : AddMonoidAlgebra k X →ₐc[k] A), Function.Surjective φ →
      ∃ Y : AddSubgroup X, RingHom.ker (φ : AddMonoidAlgebra k X →+* A) =
        Ideal.span {f | ∃ y ∈ Y, f = AddMonoidAlgebra.single y (1 : k) - 1} := by
  intro k X A _ _ _ _ _ φ _
  classical
  obtain ⟨u, hu⟩ : ∃ u : X → A, ∀ x, u x = φ (AddMonoidAlgebra.single x 1) := ⟨_, fun _ => rfl⟩
  have hmul : ∀ x y, u (x + y) = u x * u y := by
    intro x y
    rw [hu, hu, hu, ← map_mul, AddMonoidAlgebra.single_mul_single, one_mul]
  have hzero : u 0 = 1 := by
    rw [hu, ← AddMonoidAlgebra.one_def, map_one]
  have hinv : ∀ x, u x * u (-x) = 1 := by
    intro x
    rw [← hmul, add_neg_cancel, hzero]
  have hgl : ∀ x, IsGroupLikeElem k (u x) := fun x => by
    rw [hu]
    exact (AddMonoidAlgebra.isGroupLikeElem_single_one (R := k) (A := k) x).map φ
  let Y : AddSubgroup X :=
    { carrier := {x | u x = 1}
      zero_mem' := hzero
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [hmul, ha, hb, one_mul]
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        simpa [ha] using hinv a }
  have hY : ∀ x, x ∈ Y ↔ u x = 1 := fun _ => Iff.rfl
  refine ⟨Y, ?_⟩
  have hker : ∀ f, f ∈ RingHom.ker (φ : AddMonoidAlgebra k X →+* A) ↔ φ f = 0 :=
    fun f => RingHom.mem_ker
  have hle : Ideal.span {f | ∃ y ∈ Y, f = AddMonoidAlgebra.single y (1 : k) - 1} ≤
      RingHom.ker (φ : AddMonoidAlgebra k X →+* A) := by
    rw [Ideal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, hker, map_sub, map_one, ← hu, (hY y).mp hy, sub_self]
  refine le_antisymm ?_ hle
  intro f hf
  rw [hker] at hf
  let r : X → X := fun x => (QuotientAddGroup.mk x : X ⧸ Y).out
  have hr : ∀ x, (QuotientAddGroup.mk (r x) : X ⧸ Y) = QuotientAddGroup.mk x :=
    fun x => Quotient.out_eq _
  have hcoset : ∀ x (c : k), AddMonoidAlgebra.single x c - AddMonoidAlgebra.single (r x) c ∈
      Ideal.span {f | ∃ y ∈ Y, f = AddMonoidAlgebra.single y (1 : k) - 1} := by
    intro x c
    have e : AddMonoidAlgebra.single x c - AddMonoidAlgebra.single (r x) c =
        AddMonoidAlgebra.single (r x) c * (AddMonoidAlgebra.single (-(r x) + x) 1 - 1) := by
      rw [mul_sub, mul_one, AddMonoidAlgebra.single_mul_single, mul_one, add_neg_cancel_left]
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, QuotientAddGroup.eq.mp (hr x), rfl⟩)
  obtain ⟨G, hG⟩ : ∃ G : AddMonoidAlgebra k X,
      G = f.coeff.sum (fun x c => AddMonoidAlgebra.single (r x) c) := ⟨_, rfl⟩
  have hfG : f - G ∈ Ideal.span {f | ∃ y ∈ Y, f = AddMonoidAlgebra.single y (1 : k) - 1} := by
    have e : f - G = f.coeff.sum
        (fun x c => AddMonoidAlgebra.single x c - AddMonoidAlgebra.single (r x) c) := by
      rw [Finsupp.sum_sub, AddMonoidAlgebra.sum_coeff_single, hG]
    rw [e]
    unfold Finsupp.sum
    exact Ideal.sum_mem _ (fun x _ => hcoset x _)
  have hφ : ∀ g : AddMonoidAlgebra k X, φ g = Finsupp.linearCombination k u g.coeff := by
    intro g
    conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single g]
    rw [map_finsuppSum, Finsupp.linearCombination_apply]
    refine Finsupp.sum_congr (fun x _ => ?_)
    rw [hu, show AddMonoidAlgebra.single x (g.coeff x) =
      g.coeff x • AddMonoidAlgebra.single x (1 : k) by rw [AddMonoidAlgebra.smul_single', mul_one],
      map_smul]
  have hG0 : φ G = 0 := by
    have h1 : φ (f - G) = 0 := (hker _).mp (hle hfG)
    rw [map_sub, hf, zero_sub, neg_eq_zero] at h1
    exact h1
  have hinj : Set.InjOn u (Set.range r) := by
    rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩ h
    have hm : -(r x) + r x' ∈ Y := by
      rw [hY, hmul]
      have h2 : u (-(r x)) * u (r x) = 1 := by
        rw [mul_comm]
        exact hinv _
      rw [← h]
      exact h2
    have e1 : (QuotientAddGroup.mk (r x) : X ⧸ Y) = QuotientAddGroup.mk (r x') :=
      QuotientAddGroup.eq.mpr hm
    have e2 : (QuotientAddGroup.mk x : X ⧸ Y) = QuotientAddGroup.mk x' :=
      (hr x).symm.trans (e1.trans (hr x'))
    show (QuotientAddGroup.mk x : X ⧸ Y).out = (QuotientAddGroup.mk x' : X ⧸ Y).out
    rw [e2]
  have hli : LinearIndepOn k u (Set.range r) := by
    rw [linearIndepOn_iff_image hinj]
    refine (linearIndepOn_isGroupLikeElem (R := k) (A := A)).mono ?_
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact hgl (r x)
  have hsupp : G.coeff ∈ Finsupp.supported k k (Set.range r) := by
    rw [hG, AddMonoidAlgebra.coeff_finsuppSum]
    unfold Finsupp.sum
    exact Submodule.sum_mem _ (fun x _ => Finsupp.single_mem_supported k _ (Set.mem_range_self x))
  have hGc : G.coeff = 0 := by
    rw [linearIndepOn_iff] at hli
    exact hli _ hsupp (by rw [← hφ]; exact hG0)
  have hGz : G = 0 := AddMonoidAlgebra.coeff_injective hGc
  simpa [hGz] using hfG

end GlobalTheory.CompanionTheory.CommAlg
