import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

noncomputable section

namespace GlobalTheory.InnerRead

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

def hL (y : V) : V →+ E := ⟨⟨fun x => H.h x y, H.h_zero_left y⟩, fun x x' => H.h_add_left x x' y⟩

/- English proof (translation)
Rewrite using `[H.h_herm (y + z) x, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]`.
-/
lemma h_add_right (x y z : V) : H.h x (y + z) = H.h x y + H.h x z := by
  rw [H.h_herm (y + z) x, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]

/- English proof (translation)
Rewrite using `[H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm]`.
-/
lemma h_smul_right (c : E) (x y : V) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm]

/- English proof (translation)
Use `h_smul_right H 0 x 0` as an intermediate fact. Simplify using `using this`.
-/
lemma h_zero_right (x : V) : H.h x 0 = 0 := by
  have := h_smul_right H 0 x 0
  simpa using this

/- English proof (translation)
The claim follows from `map_sub (hL H z) x y`.
-/
lemma h_sub_left (x y z : V) : H.h (x - y) z = H.h x z - H.h y z := map_sub (hL H z) x y

/- English proof (translation)
The claim follows from `map_sum (hL H y) u s`.
-/
lemma h_sum_left {ι : Type} (s : Finset ι) (u : ι → V) (y : V) :
    H.h (∑ i ∈ s, u i) y = ∑ i ∈ s, H.h (u i) y := map_sum (hL H y) u s

/- English proof (translation)
Unfold `HermSp.mkW`. Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Simplify using `using h`.
-/
lemma mkW_eq {r : ℕ} {f : Fin (r + 1) → V} (x y : ↥(H.perp (H.X f))) (h : (x : V) - y ∈ H.X f) :
    H.mkW f x = H.mkW f y := by
  unfold HermSp.mkW
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  simpa using h

def Good (X : Submodule E V) (u : V ≃ₗ[E] V) : Prop :=
  IsUnitary H u ∧ ∀ v ∈ H.perp X, u v - v ∈ X

/- English proof (translation)
Introduce `x hx`. Use `X.add_mem (hu.2 x (hX hx)) hx` as an intermediate fact. Simplify using `using this`.
-/
lemma good_map_le {X : Submodule E V} {u : V ≃ₗ[E] V} (hX : X ≤ H.perp X) (hu : Good H X u) :
    ∀ x ∈ X, u x ∈ X := by
  intro x hx
  have := X.add_mem (hu.2 x (hX hx)) hx
  simpa using this

/- English proof (translation)
Introduce `v hv`. Use `(H.perp X).add_mem (hX (hu.2 v hv)) hv` as an intermediate fact. Simplify using `using this`.
-/
lemma good_perp {X : Submodule E V} {u : V ≃ₗ[E] V} (hX : X ≤ H.perp X) (hu : Good H X u) :
    ∀ v ∈ H.perp X, u v ∈ H.perp X := by
  intro v hv
  have := (H.perp X).add_mem (hX (hu.2 v hv)) hv
  simpa using this

/- English proof (translation)
Use `⟨fun x y => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Use `hu.1 (u.symm x) (u.symm y)` as an intermediate fact. Simplify using `only [LinearEquiv.apply_symm_apply] at this`. Conclude with `this.symm`. Establish `hv' : u.symm v ∈ H.perp X`.

Introduce `x hx`. Use `hu.1 (u.symm v) x` as an intermediate fact. Rewrite `this` using `[LinearEquiv.apply_symm_apply]`. Rewrite using `[← this]`. Conclude with `hv _ (good_map_le H hX hu x hx)`.

Use `X.neg_mem (hu.2 _ hv')` as an intermediate fact. Rewrite `this` using `[LinearEquiv.apply_symm_apply, neg_sub]`. Conclude with `this`.
-/
lemma good_inv {X : Submodule E V} {u : V ≃ₗ[E] V} (hX : X ≤ H.perp X) (hu : Good H X u) :
    Good H X u⁻¹ := by
  refine ⟨fun x y => ?_, fun v hv => ?_⟩
  · have := hu.1 (u.symm x) (u.symm y)
    simp only [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  have hv' : u.symm v ∈ H.perp X := by
    intro x hx
    have := hu.1 (u.symm v) x
    rw [LinearEquiv.apply_symm_apply] at this
    rw [← this]
    exact hv _ (good_map_le H hX hu x hx)
  have := X.neg_mem (hu.2 _ hv')
  rw [LinearEquiv.apply_symm_apply, neg_sub] at this
  exact this

/- English proof (translation)
Use `⟨fun x y => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `H.h (u (w x)) (u (w y)) = _`. Rewrite using `[hu.1, hw.1]`. Express the relevant statement in the definitionally equal form `u (w v) - v ∈ X`. Establish `e : u (w v) - v = (u (w v) - w v) + (w v - v)` using `by abel`.

Rewrite using `[e]`. Conclude with `X.add_mem (hu.2 _ (good_perp H hX hw v hv)) (hw.2 v hv)`.
-/
lemma good_mul {X : Submodule E V} {u w : V ≃ₗ[E] V} (hX : X ≤ H.perp X) (hu : Good H X u)
    (hw : Good H X w) : Good H X (u * w) := by
  refine ⟨fun x y => ?_, fun v hv => ?_⟩
  · change H.h (u (w x)) (u (w y)) = _
    rw [hu.1, hw.1]
  · change u (w v) - v ∈ X
    have e : u (w v) - v = (u (w v) - w v) + (w v - v) := by abel
    rw [e]
    exact X.add_mem (hu.2 _ (good_perp H hX hw v hv)) (hw.2 v hv)

variable {H} {r : ℕ} (Fr : FrameD H r)

/- English proof (translation)
The claim follows from `Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last a))`.
-/
lemma h_ee (a b : Fin r) : H.h (Fr.e a) (Fr.e b) = 0 :=
  Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last a))

/- English proof (translation)
The claim follows from `Fr.h_es a b`.
-/
lemma h_e_es (a b : Fin r) : H.h (Fr.e a) (Fr.es b) = if a = b then 1 else 0 := Fr.h_es a b

/- English proof (translation)
Rewrite using `[H.h_herm (Fr.e b) (Fr.es a), h_e_es]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma h_es_e (a b : Fin r) : H.h (Fr.es a) (Fr.e b) = if b = a then 1 else 0 := by
  rw [H.h_herm (Fr.e b) (Fr.es a), h_e_es]
  split_ifs <;> simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv a`. Conclude with `hv _ (Submodule.subset_span ⟨a, rfl⟩)`. Introduce `h x hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`. Conclude with `h a`. Consider the case `zero => exact h_zero_right H v`. Consider the case `add x y _ _ hx hy => rw [h_add_right, hx, hy, add_zero]`.

Consider the case `smul c x _ hx => rw [h_smul_right, hx, mul_zero]`.
-/
lemma mem_perp_iff (v : V) : v ∈ H.perp (H.X Fr.f) ↔ ∀ a, H.h v (Fr.e a) = 0 := by
  constructor
  · intro hv a
    exact hv _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact h a
    | zero => exact h_zero_right H v
    | add x y _ _ hx hy => rw [h_add_right, hx, hy, add_zero]
    | smul c x _ hx => rw [h_smul_right, hx, mul_zero]

/- English proof (translation)
Introduce `x hx`. Rewrite using `[mem_perp_iff]`. Introduce `a`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨b, rfl⟩` from `hx`. Conclude with `h_ee Fr b a`. Consider the case `zero => exact H.h_zero_left _`. Consider the case `add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]`. Consider the case `smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]`.
-/
lemma X_le_perp : H.X Fr.f ≤ H.perp (H.X Fr.f) := by
  intro x hx
  rw [mem_perp_iff]
  intro a
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    exact h_ee Fr b a
  | zero => exact H.h_zero_left _
  | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]

/- English proof (translation)
Unfold `FrameD.prF`. Rewrite using `[h_sub_left, h_sub_left, h_sum_left, h_sum_left]`. Simplify using `only [H.h_smul_left, h_ee, h_es_e, mul_zero, Finset.sum_const_zero, mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma prF_e (v : V) (b : Fin r) : H.h (Fr.prF v) (Fr.e b) = 0 := by
  unfold FrameD.prF
  rw [h_sub_left, h_sub_left, h_sum_left, h_sum_left]
  simp only [H.h_smul_left, h_ee, h_es_e, mul_zero, Finset.sum_const_zero, mul_ite, mul_one,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

/- English proof (translation)
Unfold `FrameD.prF`. Rewrite using `[h_sub_left, h_sub_left, h_sum_left, h_sum_left]`. Simplify using `only [H.h_smul_left, h_e_es, Fr.h_ss, mul_zero, Finset.sum_const_zero, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma prF_es (v : V) (b : Fin r) : H.h (Fr.prF v) (Fr.es b) = 0 := by
  unfold FrameD.prF
  rw [h_sub_left, h_sub_left, h_sum_left, h_sum_left]
  simp only [H.h_smul_left, h_e_es, Fr.h_ss, mul_zero, Finset.sum_const_zero, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/- English proof (translation)
The claim follows from `(mem_perp_iff Fr _).2 (prF_e Fr v)`.
-/
lemma prF_perp (v : V) : Fr.prF v ∈ H.perp (H.X Fr.f) := (mem_perp_iff Fr _).2 (prF_e Fr v)

/- English proof (translation)
Unfold `FrameD.prF`. Simplify using `only [H.h_add_left, add_smul, Finset.sum_add_distrib]`. Normalize the expressions using the abelian group laws.
-/
lemma prF_add (x y : V) : Fr.prF (x + y) = Fr.prF x + Fr.prF y := by
  unfold FrameD.prF
  simp only [H.h_add_left, add_smul, Finset.sum_add_distrib]
  abel

/- English proof (translation)
Unfold `FrameD.prF`. Simplify using `only [smul_sub, Finset.smul_sum, smul_smul, H.h_smul_left]`.
-/
lemma prF_smul (c : E) (x : V) : Fr.prF (c • x) = c • Fr.prF x := by
  unfold FrameD.prF
  simp only [smul_sub, Finset.smul_sum, smul_smul, H.h_smul_left]

/- English proof (translation)
Unfold `FrameD.prF`. Simplify using `[h1, h2]`.
-/
lemma prF_of (v : V) (h1 : ∀ a, H.h v (Fr.es a) = 0) (h2 : ∀ a, H.h v (Fr.e a) = 0) :
    Fr.prF v = v := by
  unfold FrameD.prF
  simp [h1, h2]

/- English proof (translation)
Establish `h2` using `(mem_perp_iff Fr v).1 hv`. Establish `e : v - Fr.prF v = ∑ a, H.h v (Fr.es a) • Fr.e a + ∑ a, H.h v (Fr.e a) • Fr.es a`. Unfold `FrameD.prF`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Simplify using `only [h2, zero_smul, Finset.sum_const_zero, add_zero]`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`.
-/
lemma sub_prF_mem (v : V) (hv : v ∈ H.perp (H.X Fr.f)) : v - Fr.prF v ∈ H.X Fr.f := by
  have h2 := (mem_perp_iff Fr v).1 hv
  have e : v - Fr.prF v = ∑ a, H.h v (Fr.es a) • Fr.e a + ∑ a, H.h v (Fr.e a) • Fr.es a := by
    unfold FrameD.prF; abel
  rw [e]
  simp only [h2, zero_smul, Finset.sum_const_zero, add_zero]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/- English proof (translation)
Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hxΛ, rfl⟩`. Establish `hQ : ∀ v ∈ Fr.LamStd L, H.mkW Fr.f ⟨Fr.prF v, prF_perp Fr v⟩ ∈ L`. Introduce `v hv`.

Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨-, -, w, hw, hwL⟩` from `hv`. Establish `e : (⟨Fr.prF v, prF_perp Fr v⟩ : ↥(H.perp (H.X Fr.f))) = w` using `Subtype.ext hw.symm`. Rewrite using `[e]`.

Conclude with `hwL`. Consider the case `zero`. Establish `e : (⟨Fr.prF 0, prF_perp Fr 0⟩ : ↥(H.perp (H.X Fr.f))) = 0` using `Subtype.ext (by simpa using prF_smul Fr 0 0)`. Rewrite using `[e, map_zero]`. Conclude with `L.zero_mem`.

Consider the case `add x y _ _ hx hy`. Establish `e : (⟨Fr.prF (x + y), prF_perp Fr _⟩ : ↥(H.perp (H.X Fr.f))) = ⟨Fr.prF x, prF_perp Fr x⟩ + ⟨Fr.prF y, prF_perp Fr y⟩` using `Subtype.ext (prF_add Fr x y)`. Rewrite using `[e, map_add]`. Conclude with `L.add_mem hx hy`. Consider the case `smul c x _ hx`.

Establish `e : (⟨Fr.prF (c • x), prF_perp Fr _⟩ : ↥(H.perp (H.X Fr.f))) = (c : E) • ⟨Fr.prF x, prF_perp Fr x⟩` using `Subtype.ext (prF_smul Fr (c : E) x)`. Rewrite using `[e, map_smul]`. Conclude with `L.smul_mem c hx`. Use `hQ x hxΛ` as an intermediate fact. Rewrite using `[mkW_eq H ⟨Fr.prF x, prF_perp Fr x⟩ x (by` and apply the resulting hypothesis.

Use `(H.X Fr.f).neg_mem (sub_prF_mem Fr x x.2)` as an intermediate fact. Simplify using `using this)] at this`. Introduce `hw`. Take `⟨x0, rfl⟩` from `Submodule.mkQ_surjective _ w`. Use `⟨⟨Fr.prF x0, prF_perp Fr x0⟩, ?_, ?_⟩` and prove the remaining obligations.

Establish `hp : Fr.prF (Fr.prF x0) = Fr.prF x0` using `prF_of Fr _ (prF_es Fr x0) (prF_e Fr x0)`. Use `Submodule.subset_span ⟨fun a => ?_, fun a => ?_, ⟨Fr.prF x0, prF_perp Fr x0⟩, hp.symm, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `H.h (Fr.prF x0) (Fr.es a) ∈ _`. Rewrite using `[prF_es]`. Conclude with `zero_mem _`.

Express the relevant statement in the definitionally equal form `H.h (Fr.prF x0) (Fr.e a) ∈ _`. Rewrite using `[prF_e]`. Conclude with `zero_mem _`. Rewrite using `[mkW_eq H ⟨Fr.prF x0, prF_perp Fr x0⟩ x0 (by`. Use `(H.X Fr.f).neg_mem (sub_prF_mem Fr x0 x0.2)` as an intermediate fact.

Simplify using `using this)]`. Conclude with `hw`. Use `(H.X Fr.f).neg_mem (sub_prF_mem Fr x0 x0.2) show H.mkW Fr.f _ = H.mkW Fr.f x0` as an intermediate fact. Conclude with `mkW_eq H _ _ (by simpa using this)`.
-/
theorem Lset_LamStd (L : Submodule M.L.O (H.Wb Fr.f)) :
    H.Lset (Fr.LamStd L) Fr.f = (L : Set (H.Wb Fr.f)) := by
  ext w
  constructor
  · rintro ⟨x, hxΛ, rfl⟩
    have hQ : ∀ v ∈ Fr.LamStd L, H.mkW Fr.f ⟨Fr.prF v, prF_perp Fr v⟩ ∈ L := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨-, -, w, hw, hwL⟩ := hv
        have e : (⟨Fr.prF v, prF_perp Fr v⟩ : ↥(H.perp (H.X Fr.f))) = w := Subtype.ext hw.symm
        rw [e]; exact hwL
      | zero =>
        have e : (⟨Fr.prF 0, prF_perp Fr 0⟩ : ↥(H.perp (H.X Fr.f))) = 0 :=
          Subtype.ext (by simpa using prF_smul Fr 0 0)
        rw [e, map_zero]; exact L.zero_mem
      | add x y _ _ hx hy =>
        have e : (⟨Fr.prF (x + y), prF_perp Fr _⟩ : ↥(H.perp (H.X Fr.f))) =
            ⟨Fr.prF x, prF_perp Fr x⟩ + ⟨Fr.prF y, prF_perp Fr y⟩ := Subtype.ext (prF_add Fr x y)
        rw [e, map_add]; exact L.add_mem hx hy
      | smul c x _ hx =>
        have e : (⟨Fr.prF (c • x), prF_perp Fr _⟩ : ↥(H.perp (H.X Fr.f))) =
            (c : E) • ⟨Fr.prF x, prF_perp Fr x⟩ := Subtype.ext (prF_smul Fr (c : E) x)
        rw [e, map_smul]
        exact L.smul_mem c hx
    have := hQ x hxΛ
    rwa [mkW_eq H ⟨Fr.prF x, prF_perp Fr x⟩ x (by
      have := (H.X Fr.f).neg_mem (sub_prF_mem Fr x x.2); simpa using this)] at this
  · intro hw
    obtain ⟨x0, rfl⟩ := Submodule.mkQ_surjective _ w
    refine ⟨⟨Fr.prF x0, prF_perp Fr x0⟩, ?_, ?_⟩
    · have hp : Fr.prF (Fr.prF x0) = Fr.prF x0 := prF_of Fr _ (prF_es Fr x0) (prF_e Fr x0)
      refine Submodule.subset_span ⟨fun a => ?_, fun a => ?_, ⟨Fr.prF x0, prF_perp Fr x0⟩, hp.symm, ?_⟩
      · change H.h (Fr.prF x0) (Fr.es a) ∈ _; rw [prF_es]; exact zero_mem _
      · change H.h (Fr.prF x0) (Fr.e a) ∈ _; rw [prF_e]; exact zero_mem _
      · rw [mkW_eq H ⟨Fr.prF x0, prF_perp Fr x0⟩ x0 (by
          have := (H.X Fr.f).neg_mem (sub_prF_mem Fr x0 x0.2); simpa using this)]
        exact hw
    · have := (H.X Fr.f).neg_mem (sub_prF_mem Fr x0 x0.2)
      show H.mkW Fr.f _ = H.mkW Fr.f x0
      exact mkW_eq H _ _ (by simpa using this)

/- English proof (translation)
Establish `hX` using `X_le_perp Fr`. Unfold `FrameD.N at hg`. Proceed by induction on `hg using Subgroup.closure_induction with`. Consider the case `mem x hx => exact ⟨hx.1, hx.2.2⟩`. Consider the case `one => exact ⟨fun x y => rfl, fun v _ => by simp⟩`.

Consider the case `mul x y _ _ hx hy => exact good_mul H hX hx hy`. Consider the case `inv x _ hx => exact good_inv H hX hx`.
-/
lemma good_of_mem_N {g : V ≃ₗ[E] V} (hg : g ∈ Fr.N) : Good H (H.X Fr.f) g := by
  have hX := X_le_perp Fr
  unfold FrameD.N at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact ⟨hx.1, hx.2.2⟩
  | one => exact ⟨fun x y => rfl, fun v _ => by simp⟩
  | mul x y _ _ hx hy => exact good_mul H hX hx hy
  | inv x _ hx => exact good_inv H hX hx

/- English proof (translation)
Unfold `img`. Rewrite using `[Submodule.mem_map]`. Both sides reduce to the same expression.
-/
lemma mem_img (u : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) (x : V) :
    x ∈ img u Λ ↔ ∃ y ∈ Λ, u y = x := by
  unfold img
  rw [Submodule.mem_map]
  rfl

/- English proof (translation)
Establish `hX` using `X_le_perp Fr`. Establish `g1` using `good_of_mem_N Fr hu`. Establish `g2` using `good_inv H hX g1`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hxΛ, rfl⟩`. Take `⟨y, hy, hyx⟩` from `(mem_img u Λ x).1 hxΛ`. Establish `hyp : y ∈ H.perp (H.X Fr.f)`. Use `good_perp H hX g2 (x : V) x.2` as an intermediate fact. Rewrite `this` using `[← hyx]`.

Express the relevant statement in the definitionally equal form `u.symm (u y) ∈ _ at this`. Rewrite `this` using `[LinearEquiv.symm_apply_apply]`. Then use the resulting hypothesis. Use `⟨⟨y, hyp⟩, hy, (mkW_eq H _ _ ?_).symm⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(x : V) - y ∈ _`. Rewrite using `[← hyx]`.

Conclude with `g1.2 y hyp`. Introduce and unpack `⟨y, hyΛ, rfl⟩`. Conclude with `⟨⟨u y, good_perp H hX g1 y y.2⟩, (mem_img u Λ _).2 ⟨y, hyΛ, rfl⟩, mkW_eq H _ _ (g1.2 y y.2)⟩`.
-/
theorem Lset_img {u : V ≃ₗ[E] V} (hu : u ∈ Fr.N) (Λ : Submodule M.L.O V) :
    H.Lset (img u Λ) Fr.f = H.Lset Λ Fr.f := by
  have hX := X_le_perp Fr
  have g1 := good_of_mem_N Fr hu
  have g2 := good_inv H hX g1
  ext w
  constructor
  · rintro ⟨x, hxΛ, rfl⟩
    obtain ⟨y, hy, hyx⟩ := (mem_img u Λ x).1 hxΛ
    have hyp : y ∈ H.perp (H.X Fr.f) := by
      have := good_perp H hX g2 (x : V) x.2
      rw [← hyx] at this
      change u.symm (u y) ∈ _ at this
      rwa [LinearEquiv.symm_apply_apply] at this
    refine ⟨⟨y, hyp⟩, hy, (mkW_eq H _ _ ?_).symm⟩
    change (x : V) - y ∈ _
    rw [← hyx]
    exact g1.2 y hyp
  · rintro ⟨y, hyΛ, rfl⟩
    exact ⟨⟨u y, good_perp H hX g1 y y.2⟩, (mem_img u Λ _).2 ⟨y, hyΛ, rfl⟩,
      mkW_eq H _ _ (g1.2 y y.2)⟩

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M V _ _ H r P d τ hτ`. Take `⟨-, -, ⟨n, hn, -, hΛ⟩, ⟨n', hn', -, hΛ'⟩, -⟩` from `hτ`. Prove the components needed by the constructor for the conclusion. Rewrite using `[hΛ, Lset_img P.A hn, Lset_LamStd]`. Rewrite using `[hΛ', Lset_img P.B hn', Lset_LamStd]`.
-/
theorem datum_eq_Lset : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ) (P : LocNG.FPair H r) (d : LocNG.Datum P) (τ : Loc.Term V M r), LocNG.IsTermOver P d τ → (d.L : Set (H.Wb P.A.f)) = H.Lset τ.abelian₂ P.A.f ∧ (d.L' : Set (H.Wb P.B.f)) = H.Lset τ.abelian₂ P.B.f := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r P d τ hτ
  obtain ⟨-, -, ⟨n, hn, -, hΛ⟩, ⟨n', hn', -, hΛ'⟩, -⟩ := hτ
  constructor
  · rw [hΛ, Lset_img P.A hn, Lset_LamStd]
  · rw [hΛ', Lset_img P.B hn', Lset_LamStd]

end GlobalTheory.InnerRead
