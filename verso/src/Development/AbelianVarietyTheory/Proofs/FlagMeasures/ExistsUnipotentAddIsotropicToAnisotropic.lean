import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOnto
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

noncomputable section

namespace GlobalTheory.LocOver.ZStep

open GlobalTheory.LocOver.UnipOnto

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

def eichG (x v : V) (c : E) (w : V) : V :=
  w + H.h w v • x - H.h w x • v + (c * H.h w x) • x

def eichGL (x v : V) (c : E) : V →ₗ[E] V where
  toFun := eichG H x v c
  map_add' y y' := by
    simp only [eichG, H.h_add_left, add_smul, mul_add]; abel
  map_smul' a y := by
    simp only [eichG, H.h_smul_left, RingHom.id_apply]; module

/- English proof (translation)
Simplify using `only [eichG, H.h_add_left, h_sub_left, H.h_smul_left]`.
-/
lemma eichG_hL (x v : V) (c : E) (y w : V) : H.h (eichG H x v c y) w =
    H.h y w + H.h y v * H.h x w - H.h y x * H.h v w + c * H.h y x * H.h x w := by
  simp only [eichG, H.h_add_left, h_sub_left, H.h_smul_left]

/- English proof (translation)
Simplify using `only [eichG, h_add_right, h_sub_right, h_smul_right, map_mul]`.
-/
lemma eichG_hR (x v : V) (c : E) (w y : V) : H.h w (eichG H x v c y) =
    H.h w y + M.L.cj (H.h y v) * H.h w x - M.L.cj (H.h y x) * H.h w v +
      M.L.cj c * M.L.cj (H.h y x) * H.h w x := by
  simp only [eichG, h_add_right, h_sub_right, h_smul_right, map_mul]

variable {H}

/- English proof (translation)
Establish `hvx : H.h v x = 0` using `by rw [h_right, hxv, map_zero]`. Establish `e1 : H.h x y' = M.L.cj (H.h y' x)` using `h_right H x y'`. Establish `e2 : H.h v y' = M.L.cj (H.h y' v)` using `h_right H v y'`. Simplify using `only [eichG_hL, eichG_hR]`. Rewrite using `[hxx, hxv, hvx, e1, e2]`.

Take the linear combination `(H.h y x * M.L.cj (H.h y' x)) * hc`.
-/
lemma eichG_isom {x v : V} {c : E} (hxx : H.h x x = 0) (hxv : H.h x v = 0)
    (hc : c + M.L.cj c + H.h v v = 0) (y y' : V) :
    H.h (eichG H x v c y) (eichG H x v c y') = H.h y y' := by
  have hvx : H.h v x = 0 := by rw [h_right, hxv, map_zero]
  have e1 : H.h x y' = M.L.cj (H.h y' x) := h_right H x y'
  have e2 : H.h v y' = M.L.cj (H.h y' v) := h_right H v y'
  simp only [eichG_hL, eichG_hR]
  rw [hxx, hxv, hvx, e1, e2]
  linear_combination (H.h y x * M.L.cj (H.h y' x)) * hc

/- English proof (translation)
Establish `hvx : H.h v x = 0` using `by rw [h_right, hxv, map_zero]`. Establish `e1 : H.h (eichG H (-x) v c' w) v = H.h w v + H.h w x * H.h v v`. Rewrite using `[eichG_hL, h_neg_left, h_neg_right, hxv]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : H.h (eichG H (-x) v c' w) x = H.h w x`.

Rewrite using `[eichG_hL, h_neg_left, h_neg_right, hxx, hvx]`. Expand and normalize the polynomial expressions, which then agree. Establish `key : eichG H x v c (eichG H (-x) v c' w) - w = ((c + c' + H.h v v) * H.h w x) • x`. Unfold `eichG at e1 e2 ⊢`. Rewrite using `[e1, e2, h_neg_right]`.

Use `module`. Rewrite `key` using `[hc, zero_mul, zero_smul, sub_eq_zero]`. Conclude with `key`.
-/
lemma eichG_inv {x v : V} {c c' : E} (hxx : H.h x x = 0) (hxv : H.h x v = 0)
    (hc : c + c' + H.h v v = 0) (w : V) :
    eichG H x v c (eichG H (-x) v c' w) = w := by
  have hvx : H.h v x = 0 := by rw [h_right, hxv, map_zero]
  have e1 : H.h (eichG H (-x) v c' w) v = H.h w v + H.h w x * H.h v v := by
    rw [eichG_hL, h_neg_left, h_neg_right, hxv]; ring
  have e2 : H.h (eichG H (-x) v c' w) x = H.h w x := by
    rw [eichG_hL, h_neg_left, h_neg_right, hxx, hvx]; ring
  have key : eichG H x v c (eichG H (-x) v c' w) - w = ((c + c' + H.h v v) * H.h w x) • x := by
    unfold eichG at e1 e2 ⊢
    rw [e1, e2, h_neg_right]
    module
  rw [hc, zero_mul, zero_smul, sub_eq_zero] at key
  exact key

/- English proof (translation)
The claim follows from `Λ.smul_mem ⟨α, hα⟩ hv`.
-/
lemma smul_memO {Λ : Submodule M.L.O V} {α : E} (hα : α ∈ M.L.O) {v : V} (hv : v ∈ Λ) : α • v ∈ Λ :=
  Λ.smul_mem ⟨α, hα⟩ hv

/- English proof (translation)
Introduce `g hg`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem g hg => exact hs g hg`. Consider the case `zero => rw [H.h_zero_left]`. Conclude with `M.L.O.zero_mem`.

Consider the case `add a b _ _ ha hb => rw [H.h_add_left]`. Conclude with `M.L.O.add_mem ha hb`. Consider the case `smul α a _ ha => show H.h ((α : E) • a) u ∈ M.L.O`. Rewrite using `[H.h_smul_left]`. Conclude with `M.L.O.mul_mem α.2 ha`.
-/
lemma span_h_left {s : Set V} {u : V} (hs : ∀ g ∈ s, H.h g u ∈ M.L.O) :
    ∀ g ∈ Submodule.span M.L.O s, H.h g u ∈ M.L.O := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg => exact hs g hg
  | zero => rw [H.h_zero_left]; exact M.L.O.zero_mem
  | add a b _ _ ha hb => rw [H.h_add_left]; exact M.L.O.add_mem ha hb
  | smul α a _ ha =>
    show H.h ((α : E) • a) u ∈ M.L.O
    rw [H.h_smul_left]; exact M.L.O.mul_mem α.2 ha

/- English proof (translation)
Introduce `u hu`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem u hu => exact hs u hu`. Consider the case `zero => rw [h_zero_right]`. Conclude with `M.L.O.zero_mem`.

Consider the case `add a b _ _ ha hb => rw [h_add_right]`. Conclude with `M.L.O.add_mem ha hb`. Consider the case `smul α a _ ha => show H.h g ((α : E) • a) ∈ M.L.O`. Rewrite using `[h_smul_right]`. Conclude with `M.L.O.mul_mem (GlobalTheory.UnramOrder.cj_mem M.L α.2) ha`.
-/
lemma span_h_right {s : Set V} {g : V} (hs : ∀ u ∈ s, H.h g u ∈ M.L.O) :
    ∀ u ∈ Submodule.span M.L.O s, H.h g u ∈ M.L.O := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu => exact hs u hu
  | zero => rw [h_zero_right]; exact M.L.O.zero_mem
  | add a b _ _ ha hb => rw [h_add_right]; exact M.L.O.add_mem ha hb
  | smul α a _ ha =>
    show H.h g ((α : E) • a) ∈ M.L.O
    rw [h_smul_right]; exact M.L.O.mul_mem (GlobalTheory.UnramOrder.cj_mem M.L α.2) ha

/- English proof (translation)
Introduce `w hw`. Unfold `eichG`. Use `Λ.add_mem (Λ.sub_mem (Λ.add_mem hw (smul_memO (hgv w hw) hxL)) (smul_memO (hgx w hw) hvL)) (smul_memO (M.L.O.mul_mem hc (hgx w hw)) hxL)` and prove the remaining obligations.
-/
lemma eichG_maps {Λ : Submodule M.L.O V} {x v : V} {c : E} (hc : c ∈ M.L.O) (hxL : x ∈ Λ) (hvL : v ∈ Λ)
    (hgx : ∀ g ∈ Λ, H.h g x ∈ M.L.O) (hgv : ∀ g ∈ Λ, H.h g v ∈ M.L.O) :
    ∀ w ∈ Λ, eichG H x v c w ∈ Λ := by
  intro w hw
  unfold eichG
  refine Λ.add_mem (Λ.sub_mem (Λ.add_mem hw (smul_memO (hgv w hw) hxL)) (smul_memO (hgx w hw) hvL))
    (smul_memO (M.L.O.mul_mem hc (hgx w hw)) hxL)

end GlobalTheory.LocOver.ZStep

namespace GlobalTheory.LocOver.ZStep

open GlobalTheory.LocOver.UnipOnto

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ} (Fr : FrameD H r)

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨a, rfl⟩`.
-/
lemma e_mem_X (a : Fin r) : Fr.f a.castSucc ∈ H.X Fr.f := Submodule.subset_span ⟨a, rfl⟩

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem u hu => exact Submodule.subset_span hu`. Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => exact Submodule.add_mem _ ha hb`. Consider the case `smul α a _ ha => exact Submodule.smul_mem _ (α : E) ha`.
-/
lemma spanO_le_X {x : V} (hx : x ∈ Submodule.span M.L.O (Set.range fun a : Fin r => Fr.f a.castSucc)) :
    x ∈ H.X Fr.f := by
  induction hx using Submodule.span_induction with
  | mem u hu => exact Submodule.subset_span hu
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul α a _ ha => exact Submodule.smul_mem _ (α : E) ha

/- English proof (translation)
Use `Submodule.subset_span ⟨fun b => ?_, fun b => ?_, ⟨0, ?_, by simp⟩⟩` and prove the remaining obligations. Rewrite using `[Fr.h_es]`. Use `split_ifs`. Conclude with `M.L.O.one_mem`. Conclude with `M.L.O.zero_mem`.

Rewrite using `[FrameD.e, Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last a))]`. Conclude with `M.L.O.zero_mem`. Establish `h2 : ∀ b, H.h (Fr.f a.castSucc) (Fr.e b) = 0` using `fun b => Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last a))`. Simplify using `only [FrameD.prF, Fr.h_es, h2, zero_smul, Finset.sum_const_zero, sub_zero, ite_smul, one_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Simplify using `[FrameD.e]`.
-/
lemma e_mem_LamStd (L : Submodule M.L.O (H.Wb Fr.f)) (a : Fin r) : Fr.f a.castSucc ∈ Fr.LamStd L := by
  refine Submodule.subset_span ⟨fun b => ?_, fun b => ?_, ⟨0, ?_, by simp⟩⟩
  · rw [Fr.h_es]; split_ifs
    · exact M.L.O.one_mem
    · exact M.L.O.zero_mem
  · rw [FrameD.e, Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last a))]; exact M.L.O.zero_mem
  · have h2 : ∀ b, H.h (Fr.f a.castSucc) (Fr.e b) = 0 := fun b => Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last a))
    simp only [FrameD.prF, Fr.h_es, h2, zero_smul, Finset.sum_const_zero, sub_zero, ite_smul, one_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp [FrameD.e]

end GlobalTheory.LocOver.ZStep

namespace GlobalTheory.LocOver.ZStep

open GlobalTheory.LocOver.UnipOnto

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hOK V _ _ H r Fr L hL y hyL hzy hyes x hx`. Use `letI := hOK.loc`. Use `haveI := hOK.char0`. Establish `hyX : ∀ w ∈ H.X Fr.f, H.h w (y : V) = 0` using `fun w hw => by rw [h_right, y.2 w hw, map_zero]`. Establish `hxX : x ∈ H.X Fr.f` using `spanO_le_X Fr hx`.

Establish `hxx : H.h x x = 0` using `X_iso Fr x hxX x hxX`. Establish `hxy : H.h x y = 0` using `hyX x hxX`. Establish `hnx : H.h (-x) (-x) = 0` using `by rw [h_neg_left, h_neg_right, neg_neg, hxx]`. Establish `hny : H.h (-x) y = 0` using `by rw [h_neg_left, hxy, neg_zero]`. Establish `hyy : H.h (y : V) y ∈ M.L.O` using `(hL.2.1 y).1 hyL y hyL`.

Take `⟨t, ht⟩` from `GlobalTheory.UnramOrder.exists_int_of_fixed M.L hyy (H.h_herm _ _).symm`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[F]`. Take `⟨c, hcO, hc⟩` from `(GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ).1 (-t)`. Establish `hc1 : c + M.L.cj c + H.h (y : V) y = 0`. Rewrite using `[hc, ht, ← map_add]`.

Simplify using the standard rewrite rules. Establish `hc2 : M.L.cj c + c + H.h (y : V) y = 0` using `by rw [← hc1]; ring`. Establish `hcjO : M.L.cj c ∈ M.L.O` using `GlobalTheory.UnramOrder.cj_mem M.L hcO`. Set `n : V ≃ₗ[E] V` to `LinearEquiv.ofLinear (ZStep.eichGL H x y c) (ZStep.eichGL H (-x) y (M.L.cj c)) (LinearMap.ext fun w => ZStep.eichG_inv hxx hxy hc1 w) (LinearMap.ext fun w => by`. Use `ZStep.eichG_inv (c := M.L.cj c) (c' := c) hnx hny hc2 w` as an intermediate fact.

Rewrite `this` using `[neg_neg]`. Conclude with `this)`. Establish `hn : ∀ w, n w = ZStep.eichG H x y c w` using `fun w => rfl`. Use `set Λ := Fr.LamStd L with hΛ`. Establish `heL : ∀ a : Fin r, Fr.f a.castSucc ∈ Λ` using `fun a => e_mem_LamStd Fr L a`.

Establish `hxL : x ∈ Λ`. Use `Submodule.span_le.2 ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `heL a`. Establish `hyLam : (y : V) ∈ Λ`.

Use `Submodule.subset_span ⟨fun a => by rw [hyes a]; exact M.L.O.zero_mem, fun a => by rw [show H.h (y : V) (Fr.e a) = 0 from y.2 _ (e_mem_X Fr a)]; exact M.L.O.zero_mem, ⟨y, ?_, hyL⟩⟩` and prove the remaining obligations. Establish `h2 : ∀ a, H.h (y : V) (Fr.e a) = 0` using `fun a => y.2 _ (e_mem_X Fr a)`. Simplify using `[FrameD.prF, hyes, h2]`. Establish `hgen : ∀ g ∈ {v | (∀ a, H.h v (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h v (Fr.e a) ∈ M.L.O) ∧ ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF v ∧ H.mkW Fr.f w ∈ L}, H.h g y ∈ M.L.O ∧ H.h g x ∈ M.L.O`. Introduce and unpack `g ⟨hges, hge, w, hw, hwL⟩`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hpr : H.h (Fr.prF g) y = H.h g y`. Establish `h1 : ∀ a, H.h (Fr.es a) (y : V) = 0` using `fun a => by rw [h_right, hyes a, map_zero]`. Establish `h2 : ∀ a, H.h (Fr.e a) (y : V) = 0` using `fun a => hyX _ (e_mem_X Fr a)`. Simplify using `only [FrameD.prF, h_sub_left]`.

Rewrite using `[show H.h (∑ a, H.h g (Fr.es a) • Fr.e a) (y : V) = UnipOnto.lf H (y : V) (∑ a, H.h g (Fr.es a) • Fr.e a) from rfl, show H.h (∑ a, H.h g (Fr.e a) • Fr.es a) (y : V) = UnipOnto.lf H (y : V) (∑ a, H.h g (Fr.e a) • Fr.es a) from rfl, map_sum, map_sum]`. Simplify using `[UnipOnto.lf, H.h_smul_left, h1, h2]`. Rewrite using `[← hpr, ← hw]`. Conclude with `(hL.2.1 w).1 hwL y hyL`. Use `span_h_right (s := Set.range fun a : Fin r => Fr.f a.castSucc) ?_ x hx` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `hge a`. Establish `hgy : ∀ g ∈ Λ, H.h g y ∈ M.L.O` using `span_h_left fun g hg => (hgen g hg).1`. Establish `hgx : ∀ g ∈ Λ, H.h g x ∈ M.L.O` using `span_h_left fun g hg => (hgen g hg).2`. Establish `hgnx : ∀ g ∈ Λ, H.h g (-x) ∈ M.L.O` using `fun g hg => by`.

Rewrite using `[h_neg_right]`. Conclude with `M.L.O.neg_mem (hgx g hg)`. Establish `hmap` using `eichG_maps hcO hxL hyLam hgx hgy`. Establish `hmap'` using `eichG_maps hcjO (Λ.neg_mem hxL) hyLam hgnx hgy`. Use `⟨n, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[N_eq] show n ∈ NU H Fr.f`. Use `⟨fun w w' => eichG_isom hxx hxy hc1 w w', fun a => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Establish `h1 : H.h (Fr.f a.castSucc) y = 0` using `hyX _ (e_mem_X Fr a)`. Establish `h2 : H.h (Fr.f a.castSucc) x = 0` using `X_iso Fr _ (e_mem_X Fr a) x hxX`. Rewrite using `[hn]`.

Simplify using `only [eichG, h1, h2, zero_smul, mul_zero, add_zero, sub_zero, sub_self]`. Conclude with `Submodule.zero_mem _`. Establish `h2 : H.h v x = 0` using `hv x hxX`. Rewrite using `[hn]`. Establish `: eichG H x y c v - v = H.h v y • x` using `by simp [eichG, h2]`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hxX`. Rewrite using `[hn]`. Establish `hzx : H.h (Fr.f (Fin.last r)) x = 0` using `z_X Fr x hxX`. Simplify using `[eichG, hzy, hzx]`.

Introduce `w hw`. Rewrite using `[hn]`. Establish `h1 : H.h w y = 0` using `hyX w hw`. Establish `h2 : H.h w x = 0` using `X_iso Fr w hw x hxX`. Simplify using `[eichG, h1, h2]`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Conclude with `hmap w hw`. Introduce `w hw`. Conclude with `⟨eichG H (-x) y (M.L.cj c) w, hmap' w hw, eichG_inv hxx hxy hc1 w⟩`.
-/
theorem zstep : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V]
    (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)), Fr.IsInner L →
    ∀ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L → H.h (Fr.f (Fin.last r)) (y : V) = 1 →
    (∀ a, H.h (y : V) (Fr.es a) = 0) →
    ∀ x ∈ Submodule.span M.L.O (Set.range fun a : Fin r => Fr.f a.castSucc),
    ∃ n ∈ Fr.N, n (Fr.f (Fin.last r)) = Fr.f (Fin.last r) + x ∧ (∀ w ∈ H.X Fr.f, n w = w) ∧
      img n (Fr.LamStd L) = Fr.LamStd L := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H r Fr L hL y hyL hzy hyes x hx
  letI := hOK.loc
  haveI := hOK.char0

  have hyX : ∀ w ∈ H.X Fr.f, H.h w (y : V) = 0 := fun w hw => by rw [h_right, y.2 w hw, map_zero]
  have hxX : x ∈ H.X Fr.f := spanO_le_X Fr hx
  have hxx : H.h x x = 0 := X_iso Fr x hxX x hxX
  have hxy : H.h x y = 0 := hyX x hxX
  have hnx : H.h (-x) (-x) = 0 := by rw [h_neg_left, h_neg_right, neg_neg, hxx]
  have hny : H.h (-x) y = 0 := by rw [h_neg_left, hxy, neg_zero]

  have hyy : H.h (y : V) y ∈ M.L.O := (hL.2.1 y).1 hyL y hyL
  obtain ⟨t, ht⟩ := GlobalTheory.UnramOrder.exists_int_of_fixed M.L hyy (H.h_herm _ _).symm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨c, hcO, hc⟩ := (GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ).1 (-t)
  have hc1 : c + M.L.cj c + H.h (y : V) y = 0 := by
    rw [hc, ht, ← map_add]
    simp
  have hc2 : M.L.cj c + c + H.h (y : V) y = 0 := by rw [← hc1]; ring
  have hcjO : M.L.cj c ∈ M.L.O := GlobalTheory.UnramOrder.cj_mem M.L hcO

  let n : V ≃ₗ[E] V := LinearEquiv.ofLinear (ZStep.eichGL H x y c) (ZStep.eichGL H (-x) y (M.L.cj c))
    (LinearMap.ext fun w => ZStep.eichG_inv hxx hxy hc1 w)
    (LinearMap.ext fun w => by
      have := ZStep.eichG_inv (c := M.L.cj c) (c' := c) hnx hny hc2 w
      rw [neg_neg] at this
      exact this)
  have hn : ∀ w, n w = ZStep.eichG H x y c w := fun w => rfl

  set Λ := Fr.LamStd L with hΛ
  have heL : ∀ a : Fin r, Fr.f a.castSucc ∈ Λ := fun a => e_mem_LamStd Fr L a
  have hxL : x ∈ Λ := by
    refine Submodule.span_le.2 ?_ hx
    rintro _ ⟨a, rfl⟩
    exact heL a
  have hyLam : (y : V) ∈ Λ := by
    refine Submodule.subset_span ⟨fun a => by rw [hyes a]; exact M.L.O.zero_mem,
      fun a => by rw [show H.h (y : V) (Fr.e a) = 0 from y.2 _ (e_mem_X Fr a)]; exact M.L.O.zero_mem, ⟨y, ?_, hyL⟩⟩
    have h2 : ∀ a, H.h (y : V) (Fr.e a) = 0 := fun a => y.2 _ (e_mem_X Fr a)
    simp [FrameD.prF, hyes, h2]

  have hgen : ∀ g ∈ {v | (∀ a, H.h v (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h v (Fr.e a) ∈ M.L.O) ∧
      ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF v ∧ H.mkW Fr.f w ∈ L},
      H.h g y ∈ M.L.O ∧ H.h g x ∈ M.L.O := by
    rintro g ⟨hges, hge, w, hw, hwL⟩
    refine ⟨?_, ?_⟩
    · have hpr : H.h (Fr.prF g) y = H.h g y := by
        have h1 : ∀ a, H.h (Fr.es a) (y : V) = 0 := fun a => by rw [h_right, hyes a, map_zero]
        have h2 : ∀ a, H.h (Fr.e a) (y : V) = 0 := fun a => hyX _ (e_mem_X Fr a)
        simp only [FrameD.prF, h_sub_left]
        rw [show H.h (∑ a, H.h g (Fr.es a) • Fr.e a) (y : V) = UnipOnto.lf H (y : V) (∑ a, H.h g (Fr.es a) • Fr.e a) from rfl,
          show H.h (∑ a, H.h g (Fr.e a) • Fr.es a) (y : V) = UnipOnto.lf H (y : V) (∑ a, H.h g (Fr.e a) • Fr.es a) from rfl,
          map_sum, map_sum]
        simp [UnipOnto.lf, H.h_smul_left, h1, h2]
      rw [← hpr, ← hw]
      exact (hL.2.1 w).1 hwL y hyL
    · refine span_h_right (s := Set.range fun a : Fin r => Fr.f a.castSucc) ?_ x hx
      rintro _ ⟨a, rfl⟩
      exact hge a
  have hgy : ∀ g ∈ Λ, H.h g y ∈ M.L.O := span_h_left fun g hg => (hgen g hg).1
  have hgx : ∀ g ∈ Λ, H.h g x ∈ M.L.O := span_h_left fun g hg => (hgen g hg).2
  have hgnx : ∀ g ∈ Λ, H.h g (-x) ∈ M.L.O := fun g hg => by
    rw [h_neg_right]; exact M.L.O.neg_mem (hgx g hg)
  have hmap := eichG_maps hcO hxL hyLam hgx hgy
  have hmap' := eichG_maps hcjO (Λ.neg_mem hxL) hyLam hgnx hgy
  refine ⟨n, ?_, ?_, ?_, ?_⟩
  · rw [N_eq]
    show n ∈ NU H Fr.f
    refine ⟨fun w w' => eichG_isom hxx hxy hc1 w w', fun a => ?_, fun v hv => ?_⟩
    · have h1 : H.h (Fr.f a.castSucc) y = 0 := hyX _ (e_mem_X Fr a)
      have h2 : H.h (Fr.f a.castSucc) x = 0 := X_iso Fr _ (e_mem_X Fr a) x hxX
      rw [hn]
      simp only [eichG, h1, h2, zero_smul, mul_zero, add_zero, sub_zero, sub_self]
      exact Submodule.zero_mem _
    · have h2 : H.h v x = 0 := hv x hxX
      rw [hn]
      have : eichG H x y c v - v = H.h v y • x := by simp [eichG, h2]
      rw [this]
      exact Submodule.smul_mem _ _ hxX
  · rw [hn]
    have hzx : H.h (Fr.f (Fin.last r)) x = 0 := z_X Fr x hxX
    simp [eichG, hzy, hzx]
  · intro w hw
    rw [hn]
    have h1 : H.h w y = 0 := hyX w hw
    have h2 : H.h w x = 0 := X_iso Fr w hw x hxX
    simp [eichG, h1, h2]
  · apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hmap w hw
    · intro w hw
      exact ⟨eichG H (-x) y (M.L.cj c) w, hmap' w hw, eichG_inv hxx hxy hc1 w⟩

end GlobalTheory.LocOver.ZStep
