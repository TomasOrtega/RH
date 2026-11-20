import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.StabLat

open Formalism.MainNotions.S.LocNG Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.BridgeLemma

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

/- English proof (translation)
Introduce `x hx`. Unfold `HermSp.X at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨a, rfl⟩ := hx`. Conclude with `h a`.

Consider the case `zero => rw [H.h_herm 0 _, H.h_zero_left, map_zero]`. Consider the case `add x y _ _ hx hy => rw [H.h_herm (x + y) _, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm, hx, hy, add_zero]`. Consider the case `smul c x _ hx => rw [H.h_herm (c • x) _, H.h_smul_left, map_mul, ← H.h_herm, hx, mul_zero]`.
-/
theorem perpX_of (Fr : FrameD H r) {k : V} (h : ∀ a : Fin r, H.h k (Fr.f a.castSucc) = 0) :
    k ∈ H.perp (H.X Fr.f) := by
  intro x hx
  unfold HermSp.X at hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h a
  | zero => rw [H.h_herm 0 _, H.h_zero_left, map_zero]
  | add x y _ _ hx hy => rw [H.h_herm (x + y) _, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm, hx, hy, add_zero]
  | smul c x _ hx => rw [H.h_herm (c • x) _, H.h_smul_left, map_mul, ← H.h_herm, hx, mul_zero]

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨a, rfl⟩`.
-/
theorem e_mem_X (Fr : FrameD H r) (a : Fin r) : Fr.e a ∈ H.X Fr.f :=
  Submodule.subset_span ⟨a, rfl⟩

/- English proof (translation)
Establish `h0 : ∀ a, H.h y (Fr.e a) = 0` using `fun a => hy _ (e_mem_X Fr a)`. Establish `e : y - Fr.prF y = ∑ a, H.h y (Fr.es a) • Fr.e a`. Unfold `FrameD.prF`. Simplify using `only [h0, zero_smul, Finset.sum_const_zero, sub_zero, sub_sub_cancel]`. Rewrite using `[e]`.

Conclude with `Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (e_mem_X Fr a))`.
-/
theorem sub_prF_mem (Fr : FrameD H r) {y : V} (hy : y ∈ H.perp (H.X Fr.f)) : y - Fr.prF y ∈ H.X Fr.f := by
  have h0 : ∀ a, H.h y (Fr.e a) = 0 := fun a => hy _ (e_mem_X Fr a)
  have e : y - Fr.prF y = ∑ a, H.h y (Fr.es a) • Fr.e a := by
    unfold FrameD.prF
    simp only [h0, zero_smul, Finset.sum_const_zero, sub_zero, sub_sub_cancel]
  rw [e]
  exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (e_mem_X Fr a))

/- English proof (translation)
The claim follows from `perpX_of Fr (fun a => ng_prF_e (Fr := Fr) y a)`.
-/
theorem prF_mem_perp (Fr : FrameD H r) (y : V) : Fr.prF y ∈ H.perp (H.X Fr.f) :=
  perpX_of Fr (fun a => ng_prF_e (Fr := Fr) y a)

/- English proof (translation)
Unfold `HermSp.mkW`. Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Conclude with `h`.
-/
theorem mkW_eq (Fr : FrameD H r) {x y : ↥(H.perp (H.X Fr.f))} (h : (x : V) - y ∈ H.X Fr.f) :
    H.mkW Fr.f x = H.mkW Fr.f y := by
  unfold HermSp.mkW
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact h

/- English proof (translation)
Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨fun a => ?_, fun a => ?_, ⟨Fr.prF (Fr.prF y), prF_mem_perp Fr _⟩, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[ng_prF_es]`. Conclude with `M.L.O.zero_mem`. Rewrite using `[ng_prF_e]`.

Conclude with `M.L.O.zero_mem`. Establish `e : H.mkW Fr.f ⟨Fr.prF (Fr.prF y), prF_mem_perp Fr _⟩ = H.mkW Fr.f ⟨y, hy⟩`. Apply `mkW_eq` to reduce the goal to its premises. Establish `h1` using `sub_prF_mem Fr hy`. Establish `h2` using `sub_prF_mem Fr (prF_mem_perp Fr y)`.

Establish `: Fr.prF (Fr.prF y) - y = -((y - Fr.prF y) + (Fr.prF y - Fr.prF (Fr.prF y)))` using `by abel`. Rewrite using `[show ((⟨Fr.prF (Fr.prF y), prF_mem_perp Fr _⟩ : ↥(H.perp (H.X Fr.f))) : V) = Fr.prF (Fr.prF y) from rfl, show ((⟨y, hy⟩ : ↥(H.perp (H.X Fr.f))) : V) = y from rfl, this]`. Conclude with `Submodule.neg_mem _ (Submodule.add_mem _ h1 h2)`. Rewrite using `[e]`. Conclude with `hyL`.
-/
theorem prF_mem_LamStd (Fr : FrameD H r) {L : Submodule M.L.O (H.Wb Fr.f)} {y : V}
    (hy : y ∈ H.perp (H.X Fr.f)) (hyL : H.mkW Fr.f ⟨y, hy⟩ ∈ L) : Fr.prF y ∈ Fr.LamStd L := by
  apply Submodule.subset_span
  refine ⟨fun a => ?_, fun a => ?_, ⟨Fr.prF (Fr.prF y), prF_mem_perp Fr _⟩, rfl, ?_⟩
  · rw [ng_prF_es]; exact M.L.O.zero_mem
  · rw [ng_prF_e]; exact M.L.O.zero_mem
  · have e : H.mkW Fr.f ⟨Fr.prF (Fr.prF y), prF_mem_perp Fr _⟩ = H.mkW Fr.f ⟨y, hy⟩ := by
      apply mkW_eq
      have h1 := sub_prF_mem Fr hy
      have h2 := sub_prF_mem Fr (prF_mem_perp Fr y)
      have : Fr.prF (Fr.prF y) - y = -((y - Fr.prF y) + (Fr.prF y - Fr.prF (Fr.prF y))) := by abel
      rw [show ((⟨Fr.prF (Fr.prF y), prF_mem_perp Fr _⟩ : ↥(H.perp (H.X Fr.f))) : V) = Fr.prF (Fr.prF y) from rfl,
        show ((⟨y, hy⟩ : ↥(H.perp (H.X Fr.f))) : V) = y from rfl, this]
      exact Submodule.neg_mem _ (Submodule.add_mem _ h1 h2)
    rw [e]; exact hyL

variable {P : FPair H r}

/- English proof (translation)
Rewrite using `[H.h_herm (u + y) k, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]`.
-/
theorem h_add_right' (k u y : V) : H.h k (u + y) = H.h k u + H.h k y := by
  rw [H.h_herm (u + y) k, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]

/- English proof (translation)
Establish `ht'` using `ht`. Take `⟨_, _, ⟨n, hn, -, hL⟩, _, _⟩` from `ht'`. Establish `hN` using `mem_NSet_of_mem_N P.A hn`. Use `((d.hL.2.1 ⟨k, hkp⟩).2) (fun y hyL => ?_)` and prove the remaining obligations. Establish `hy` using `y.2`.

Establish `hyL' : H.mkW P.A.f ⟨(y : V), hy⟩ ∈ d.L` using `hyL`. Establish `h0` using `prF_mem_LamStd P.A hy hyL'`. Establish `hny : n (P.A.prF y) ∈ t.abelian₂` using `by rw [hL]; exact ⟨_, h0, rfl⟩`. Establish `hint` using `ng_term_int ht hk hny`. Establish `hu : n (P.A.prF y) - y ∈ H.X P.A.f`.

Establish `h1` using `hN.2.2 _ (prF_mem_perp P.A (y : V))`. Establish `h2` using `sub_prF_mem P.A hy`. Establish `: n (P.A.prF y) - y = (n (P.A.prF y) - P.A.prF y) - ((y : V) - P.A.prF y)` using `by abel`. Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ h1 h2`.

Establish `e : n (P.A.prF y) = (n (P.A.prF y) - y) + y` using `by abel`. Rewrite `hint` using `[e, h_add_right', hkp _ hu, zero_add]`. Conclude with `hint`.
-/
theorem cls_mem {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) {k : V} (hk : k ∈ t.abelian₂)
    (hkp : k ∈ H.perp (H.X P.A.f)) : H.mkW P.A.f ⟨k, hkp⟩ ∈ d.L := by
  have ht' := ht
  obtain ⟨_, _, ⟨n, hn, -, hL⟩, _, _⟩ := ht'
  have hN := mem_NSet_of_mem_N P.A hn
  refine ((d.hL.2.1 ⟨k, hkp⟩).2) (fun y hyL => ?_)
  have hy := y.2
  have hyL' : H.mkW P.A.f ⟨(y : V), hy⟩ ∈ d.L := hyL
  have h0 := prF_mem_LamStd P.A hy hyL'
  have hny : n (P.A.prF y) ∈ t.abelian₂ := by rw [hL]; exact ⟨_, h0, rfl⟩
  have hint := ng_term_int ht hk hny
  have hu : n (P.A.prF y) - y ∈ H.X P.A.f := by
    have h1 := hN.2.2 _ (prF_mem_perp P.A (y : V))
    have h2 := sub_prF_mem P.A hy
    have : n (P.A.prF y) - y = (n (P.A.prF y) - P.A.prF y) - ((y : V) - P.A.prF y) := by abel
    rw [this]; exact Submodule.sub_mem _ h1 h2
  have e : n (P.A.prF y) = (n (P.A.prF y) - y) + y := by abel
  rw [e, h_add_right', hkp _ hu, zero_add] at hint
  exact hint

/- English proof (translation)
Establish `ht'` using `ht`. Take `⟨_, _, ⟨n, hn, -, hL⟩, _, _⟩` from `ht'`. Establish `hN` using `mem_NSet_of_mem_N P.A hn`. Establish `hkp` using `ng_orth_perp P.A ho.1`. Establish `h0` using `prF_mem_LamStd P.A hkp hkL`.

Establish `hny : n (P.A.prF k) ∈ t.abelian₂` using `by rw [hL]; exact ⟨_, h0, rfl⟩`. Take `⟨m0, hm0, hk', hko⟩` from `ng_term_split hP ht hny`. Establish `hXle : H.X P.A.f ≤ Submodule.span E (Set.range (Sum.elim P.A.f P.B.f))`. Unfold `HermSp.X`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `Submodule.subset_span ⟨Sum.inl a.castSucc, rfl⟩`. Establish `hx : n (P.A.prF k) - k ∈ H.X P.A.f`. Establish `h1` using `hN.2.2 _ (prF_mem_perp P.A k)`. Establish `h2` using `sub_prF_mem P.A hkp`.

Establish `: n (P.A.prF k) - k = (n (P.A.prF k) - P.A.prF k) - (k - P.A.prF k)` using `by abel`. Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ h1 h2`. Establish `hz : k - (n (P.A.prF k) - m0) = 0`. Use `ng_zero (H := H) (Sum.elim P.A.f P.B.f) ?_ ?_ ?_` and prove the remaining obligations.

Rewrite using `[ng_gram_base]`. Conclude with `IsUnit.mul (IsUnit.pow _ isUnit_one.neg) (ng_G_unit (by`. Introduce `h0`. Take `⟨_, y, _, hy⟩` from `hP.2.1`. Rewrite `hy` using `[h0, zero_mul]`.

Use `Formalism.MainNotions.LocalModelPeriodLattices.nontrivial_E M.L` as an intermediate fact. Conclude with `zero_ne_one hy))`. Establish `e : k - (n (P.A.prF k) - m0) = m0 - (n (P.A.prF k) - k)` using `by abel`. Rewrite using `[e]`. Conclude with `Submodule.sub_mem _ (ng_span_base ht hm0) (hXle hx)`.

Introduce and unpack `(b | b)`. Rewrite using `[Sum.elim_inl, h_sub_left, ho.1, hko.1, sub_zero]`. Rewrite using `[Sum.elim_inr, h_sub_left, ho.2, hko.2, sub_zero]`. Rewrite using `[sub_eq_zero.1 hz]`. Conclude with `hk'`.
-/
theorem mem_of_cls (hP : P.PrimeTo) {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) {k : V}
    (ho : NgOrth P k) (hkL : H.mkW P.A.f ⟨k, ng_orth_perp P.A ho.1⟩ ∈ d.L) : k ∈ t.abelian₂ := by
  have ht' := ht
  obtain ⟨_, _, ⟨n, hn, -, hL⟩, _, _⟩ := ht'
  have hN := mem_NSet_of_mem_N P.A hn
  have hkp := ng_orth_perp P.A ho.1
  have h0 := prF_mem_LamStd P.A hkp hkL
  have hny : n (P.A.prF k) ∈ t.abelian₂ := by rw [hL]; exact ⟨_, h0, rfl⟩
  obtain ⟨m0, hm0, hk', hko⟩ := ng_term_split hP ht hny
  have hXle : H.X P.A.f ≤ Submodule.span E (Set.range (Sum.elim P.A.f P.B.f)) := by
    unfold HermSp.X
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span ⟨Sum.inl a.castSucc, rfl⟩
  have hx : n (P.A.prF k) - k ∈ H.X P.A.f := by
    have h1 := hN.2.2 _ (prF_mem_perp P.A k)
    have h2 := sub_prF_mem P.A hkp
    have : n (P.A.prF k) - k = (n (P.A.prF k) - P.A.prF k) - (k - P.A.prF k) := by abel
    rw [this]; exact Submodule.sub_mem _ h1 h2
  have hz : k - (n (P.A.prF k) - m0) = 0 := by
    refine ng_zero (H := H) (Sum.elim P.A.f P.B.f) ?_ ?_ ?_
    · rw [ng_gram_base]
      exact IsUnit.mul (IsUnit.pow _ isUnit_one.neg) (ng_G_unit (by
        intro h0
        obtain ⟨_, y, _, hy⟩ := hP.2.1
        rw [h0, zero_mul] at hy
        have := Formalism.MainNotions.LocalModelPeriodLattices.nontrivial_E M.L
        exact zero_ne_one hy))
    · have e : k - (n (P.A.prF k) - m0) = m0 - (n (P.A.prF k) - k) := by abel
      rw [e]
      exact Submodule.sub_mem _ (ng_span_base ht hm0) (hXle hx)
    · rintro (b | b)
      · rw [Sum.elim_inl, h_sub_left, ho.1, hko.1, sub_zero]
      · rw [Sum.elim_inr, h_sub_left, ho.2, hko.2, sub_zero]
  rw [sub_eq_zero.1 hz]; exact hk'

/- English proof (translation)
Unfold `FPair.UW0 at hg`. Proceed by induction on `hg using Subgroup.closure_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `one => exact ⟨fun x y => rfl, fun b => ⟨rfl, rfl⟩⟩`. Consider the case `mul x y _ _ hx hy`.

Use `⟨fun u v => ?_, fun b => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use `show H.h (x (y u)) (x (y v)) = H.h u v`. Rewrite using `[hx.1, hy.1]`. Use `show x (y (P.A.f b)) = P.A.f b`. Rewrite using `[(hy.2 b).1, (hx.2 b).1]`.

Use `show x (y (P.B.f b)) = P.B.f b`. Rewrite using `[(hy.2 b).2, (hx.2 b).2]`. Consider the case `inv x _ hx`. Establish `e : ∀ u, x ((x⁻¹ : V ≃ₗ[E] V) u) = u` using `fun u => LinearEquiv.apply_symm_apply x u`. Use `⟨fun u v => ?_, fun b => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[← hx.1, e, e]`. Use `conv_lhs => rw [← (hx.2 b).1]`. Conclude with `LinearEquiv.symm_apply_apply x _`. Use `conv_lhs => rw [← (hx.2 b).2]`. Conclude with `LinearEquiv.symm_apply_apply x _`.
-/
theorem complementUnitary_isUnitary_fixes_frames {g : V ≃ₗ[E] V} (hg : g ∈ P.UW0) :
    IsUnitary H g ∧ ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b := by
  unfold FPair.UW0 at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨fun x y => rfl, fun b => ⟨rfl, rfl⟩⟩
  | mul x y _ _ hx hy =>
    refine ⟨fun u v => ?_, fun b => ⟨?_, ?_⟩⟩
    · show H.h (x (y u)) (x (y v)) = H.h u v
      rw [hx.1, hy.1]
    · show x (y (P.A.f b)) = P.A.f b
      rw [(hy.2 b).1, (hx.2 b).1]
    · show x (y (P.B.f b)) = P.B.f b
      rw [(hy.2 b).2, (hx.2 b).2]
  | inv x _ hx =>
    have e : ∀ u, x ((x⁻¹ : V ≃ₗ[E] V) u) = u := fun u => LinearEquiv.apply_symm_apply x u
    refine ⟨fun u v => ?_, fun b => ⟨?_, ?_⟩⟩
    · rw [← hx.1, e, e]
    · conv_lhs => rw [← (hx.2 b).1]
      exact LinearEquiv.symm_apply_apply x _
    · conv_lhs => rw [← (hx.2 b).2]
      exact LinearEquiv.symm_apply_apply x _

/- English proof (translation)
Establish `hf` using `ng_term_f ht`. Establish `hM : Submodule.span M.L.O (Set.range (Sum.elim t.f t.f')) ≤ t.abelian₂`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Break down `j with b | b` into its components or cases.

Conclude with `(hf b).1`. Conclude with `(hf b).2`. Establish `hfixME : ∀ x ∈ Submodule.span E (Set.range (Sum.elim P.A.f P.B.f)), g x = x`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨j, rfl⟩` from `hx`. Break down `j with b | b` into its components or cases. Conclude with `(hfix b).1`. Conclude with `(hfix b).2`.

Consider the case `zero => exact map_zero g`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy]`. Consider the case `smul c x _ hx => rw [map_smul, hx]`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Take `⟨m0, hm0, hk, hko⟩` from `ng_term_split hP ht hv`.

Use `show g v ∈ t.abelian₂`. Establish `e : g v = m0 + g (v - m0)`. Rewrite using `[map_sub, hfixME m0 (ng_span_base ht hm0)]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Use `t.abelian₂.add_mem (hM hm0) ?_` and prove the remaining obligations. Establish `hgo : NgOrth P (g (v - m0))`. Prove the components needed by the constructor for the conclusion. Introduce `b`. Rewrite using `[← (hfix b).1, hU, hko.1]`.

Introduce `b`. Rewrite using `[← (hfix b).2, hU, hko.2]`. Apply `mem_of_cls hP ht hgo` to reduce the goal to its premises. Conclude with `hmov ⟨v - m0, ng_orth_perp P.A hko.1⟩ _ rfl (cls_mem ht hk _)`.
-/
theorem img_le (hP : P.PrimeTo) {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) {g : V ≃ₗ[E] V}
    (hU : IsUnitary H g) (hfix : ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b)
    (hmov : ∀ x y : ↥(H.perp (H.X P.A.f)), (y : V) = g x → H.mkW P.A.f x ∈ d.L → H.mkW P.A.f y ∈ d.L) :
    img g t.abelian₂ ≤ t.abelian₂ := by
  have hf := ng_term_f ht
  have hM : Submodule.span M.L.O (Set.range (Sum.elim t.f t.f')) ≤ t.abelian₂ := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rcases j with b | b
    · exact (hf b).1
    · exact (hf b).2
  have hfixME : ∀ x ∈ Submodule.span E (Set.range (Sum.elim P.A.f P.B.f)), g x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rcases j with b | b
      · exact (hfix b).1
      · exact (hfix b).2
    | zero => exact map_zero g
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨m0, hm0, hk, hko⟩ := ng_term_split hP ht hv
  show g v ∈ t.abelian₂
  have e : g v = m0 + g (v - m0) := by
    rw [map_sub, hfixME m0 (ng_span_base ht hm0)]; abel
  rw [e]
  refine t.abelian₂.add_mem (hM hm0) ?_
  have hgo : NgOrth P (g (v - m0)) := by
    constructor
    · intro b; rw [← (hfix b).1, hU, hko.1]
    · intro b; rw [← (hfix b).2, hU, hko.2]
  apply mem_of_cls hP ht hgo
  exact hmov ⟨v - m0, ng_orth_perp P.A hko.1⟩ _ rfl (cls_mem ht hk _)

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M _ V _ _ H r k P _ _ hP d τ ht`. Unfold `Datum.Stab`. Rewrite using `[Subgroup.closure_le]`. Introduce and unpack `g ⟨hg, hmv⟩`. Take `⟨hU, hfix⟩` from `complementUnitary_isUnitary_fixes_frames hg`.

Rewrite using `[SetLike.mem_coe, ng_mem_Aut]`. Establish `e : ∀ u, g ((g⁻¹ : V ≃ₗ[E] V) u) = u` using `fun u => LinearEquiv.apply_symm_apply g u`. Establish `h1` using `img_le hP ht hU hfix (fun x y hxy hx => (hmv.1 x y hxy).1 hx)`. Establish `hU' : IsUnitary H g⁻¹` using `fun u v => by rw [← hU, e, e]`. Establish `hfix' : ∀ b, (g⁻¹ : V ≃ₗ[E] V) (P.A.f b) = P.A.f b ∧ (g⁻¹ : V ≃ₗ[E] V) (P.B.f b) = P.B.f b` using `fun b => by`.

Prove the components needed by the constructor for the conclusion. Use `conv_lhs => rw [← (hfix b).1]`. Conclude with `LinearEquiv.symm_apply_apply g _`. Use `conv_lhs => rw [← (hfix b).2]`. Conclude with `LinearEquiv.symm_apply_apply g _`.

Establish `h2` using `img_le hP ht hU' hfix' (fun x y hxy hx => by`. Use `(hmv.1 y x ?_).2 hx` and prove the remaining obligations. Rewrite using `[hxy]`. Conclude with `(e x).symm)`. Use `le_antisymm h1 ?_` and prove the remaining obligations.

Establish `h3` using `ng_img_mono g h2`. Rewrite `h3` using `[← ng_img_mul, mul_inv_cancel, ng_img_one]`. Then use the resulting hypothesis.
-/
theorem stab_le_aut : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → P.PrimeTo → ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → LocNG.Datum.Stab d ≤ LocNG.Aut τ.abelian₂ := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r k P _ _ hP d τ ht
  unfold Datum.Stab
  rw [Subgroup.closure_le]
  rintro g ⟨hg, hmv⟩
  obtain ⟨hU, hfix⟩ := complementUnitary_isUnitary_fixes_frames hg
  rw [SetLike.mem_coe, ng_mem_Aut]
  have e : ∀ u, g ((g⁻¹ : V ≃ₗ[E] V) u) = u := fun u => LinearEquiv.apply_symm_apply g u
  have h1 := img_le hP ht hU hfix (fun x y hxy hx => (hmv.1 x y hxy).1 hx)
  have hU' : IsUnitary H g⁻¹ := fun u v => by rw [← hU, e, e]
  have hfix' : ∀ b, (g⁻¹ : V ≃ₗ[E] V) (P.A.f b) = P.A.f b ∧ (g⁻¹ : V ≃ₗ[E] V) (P.B.f b) = P.B.f b := fun b => by
    constructor
    · conv_lhs => rw [← (hfix b).1]
      exact LinearEquiv.symm_apply_apply g _
    · conv_lhs => rw [← (hfix b).2]
      exact LinearEquiv.symm_apply_apply g _
  have h2 := img_le hP ht hU' hfix' (fun x y hxy hx => by
    refine (hmv.1 y x ?_).2 hx
    rw [hxy]; exact (e x).symm)
  refine le_antisymm h1 ?_
  have h3 := ng_img_mono g h2
  rwa [← ng_img_mul, mul_inv_cancel, ng_img_one] at h3

end GlobalTheory.HL.StabLat
