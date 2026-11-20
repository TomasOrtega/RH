import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordUnip

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `_ u hu`. Rewrite `hu` using `[h0, Submodule.mem_bot]`.

Conclude with `⟨0, by rw [h0]; exact Submodule.zero_mem _, by rw [hu, map_zero]⟩`. Consider the case `succ i ih`. Introduce `hi u hu`. Take `⟨w, hw, hgw⟩` from `ih (by omega) (g u - u) (hg i (by omega) u hu)`. Use `⟨u - w, Submodule.sub_mem _ hu (hm i hw), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sub, hgw]`. Normalize the expressions using the abelian group laws.
-/
private lemma flag_iff_lemma {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] (A : ℕ → Submodule E V)
    (h0 : A 0 = ⊥) (hm : ∀ j, A j ≤ A (j + 1)) (r : ℕ) (g : V ≃ₗ[E] V)
    (hg : ∀ j, j < r → ∀ v ∈ A (j + 1), g v - v ∈ A j) :
    ∀ j, j ≤ r → ∀ u ∈ A j, ∃ w ∈ A j, g w = u := by
  intro j
  induction j with
  | zero =>
    intro _ u hu
    rw [h0, Submodule.mem_bot] at hu
    exact ⟨0, by rw [h0]; exact Submodule.zero_mem _, by rw [hu, map_zero]⟩
  | succ i ih =>
    intro hi u hu
    obtain ⟨w, hw, hgw⟩ := ih (by omega) (g u - u) (hg i (by omega) u hu)
    refine ⟨u - w, Submodule.sub_mem _ hu (hm i hw), ?_⟩
    rw [map_sub, hgw]
    abel

/- English proof (translation)
Introduce `j hj v`. Prove the components needed by the constructor for the conclusion. Introduce `hv`. Take `⟨w, hw, hgw⟩` from `flag_iff_lemma A h0 hm r g hg j hj (g v) hv`. Rewrite using `[← g.injective hgw]`.

Conclude with `hw`. Introduce `hv`. Consider the cases of `j with`. Consider the case `zero`. Rewrite `hv`, the goal using `[h0, Submodule.mem_bot]`.

Rewrite using `[hv, map_zero]`. Consider the case `succ i`. Establish `hd` using `hg i (by omega) v hv`. Establish `h2 : g v = (g v - v) + v` using `by abel`. Rewrite using `[h2]`.

Conclude with `Submodule.add_mem _ (hm i hd) hv`.
-/
lemma flag_iff {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] (A : ℕ → Submodule E V)
    (h0 : A 0 = ⊥) (hm : ∀ j, A j ≤ A (j + 1)) (r : ℕ) (g : V ≃ₗ[E] V)
    (hg : ∀ j, j < r → ∀ v ∈ A (j + 1), g v - v ∈ A j) :
    ∀ j, j ≤ r → ∀ v, g v ∈ A j ↔ v ∈ A j := by
  intro j hj v
  constructor
  · intro hv
    obtain ⟨w, hw, hgw⟩ := flag_iff_lemma A h0 hm r g hg j hj (g v) hv
    rw [← g.injective hgw]
    exact hw
  · intro hv
    cases j with
    | zero =>
      rw [h0, Submodule.mem_bot] at hv ⊢
      rw [hv, map_zero]
    | succ i =>
      have hd := hg i (by omega) v hv
      have h2 : g v = (g v - v) + v := by abel
      rw [h2]
      exact Submodule.add_mem _ (hm i hd) hv

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

/- English proof (translation)
Simplify using `[Frames.spanTo]`.
-/
lemma spanTo_zero (S : Frames M.L r k) (f : Fin (r + 1) → S.V) : S.spanTo f 0 = ⊥ := by
  simp [Frames.spanTo]

/- English proof (translation)
Unfold `Frames.spanTo`. Apply `Submodule.span_mono` to reduce the goal to its premises. Apply `Set.image_mono` to reduce the goal to its premises. Introduce `i hi`. Simplify using `only [Set.mem_ofPred_eq] at hi ⊢`.

Use linear arithmetic over natural numbers and integers.
-/
lemma spanTo_mono (S : Frames M.L r k) (f : Fin (r + 1) → S.V) (j : ℕ) :
    S.spanTo f j ≤ S.spanTo f (j + 1) := by
  unfold Frames.spanTo
  apply Submodule.span_mono
  apply Set.image_mono
  intro i hi
  simp only [Set.mem_ofPred_eq] at hi ⊢
  omega

/- English proof (translation)
Establish `mu : ∀ (A B : Submodule E S.V) (g : S.GLV), g ∈ unipOn A B ↔ (∀ v, g v ∈ A ↔ v ∈ A) ∧ ∀ v ∈ A, g v - v ∈ B` using `fun _ _ _ => Iff.rfl`. Establish `mi : g ∈ isomG M.L S.Hm ↔ ∀ x y, S.h (g x) (g y) = S.h x y` using `Iff.rfl`. Establish `mp : ∀ (Y : Submodule E S.V) (v : S.V), v ∈ perp M.L S.Hm Y ↔ ∀ y ∈ Y, S.h v y = 0` using `fun _ _ => Iff.rfl`. Simplify using `only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf, mu, mi]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨hiso, hu⟩, hp⟩`. Conclude with `⟨hiso, fun j hj v hv => (hu ⟨j, hj⟩).2 v hv, hp.2⟩`. Introduce and unpack `⟨hiso, hu, hp⟩`. Establish `hfl` using `flag_iff (S.spanTo f) (spanTo_zero S f) (spanTo_mono S f) r g hu`. Use `⟨⟨hiso, fun j => ⟨hfl (j + 1) j.isLt, hu j j.isLt⟩⟩, ?_, hp⟩` and prove the remaining obligations.

Establish `hX` using `hfl r le_rfl`. Introduce `v`. Rewrite using `[mp, mp]`. Prove the components needed by the constructor for the conclusion. Introduce `hv y hy`.

Rewrite using `[← hiso v y]`. Conclude with `hv (g y) ((hX y).2 hy)`. Introduce `hv y hy`. Establish `hy' : g.symm y ∈ S.spanTo f r` using `(hX _).1 (by simpa using hy)`. Use `hv (g.symm y) hy'` as an intermediate fact.

Rewrite `this` using `[← hiso v (g.symm y), LinearEquiv.apply_symm_apply]`. Conclude with `this`.
-/
lemma mem_Nof (S : Frames M.L r k) (f : Fin (r + 1) → S.V) (g : S.GLV) :
    g ∈ S.Nof f ↔ (∀ x y, S.h (g x) (g y) = S.h x y) ∧
      (∀ j, j < r → ∀ v ∈ S.spanTo f (j + 1), g v - v ∈ S.spanTo f j) ∧
      ∀ v ∈ perp M.L S.Hm (S.spanTo f r), g v - v ∈ S.spanTo f r := by
  have mu : ∀ (A B : Submodule E S.V) (g : S.GLV),
      g ∈ unipOn A B ↔ (∀ v, g v ∈ A ↔ v ∈ A) ∧ ∀ v ∈ A, g v - v ∈ B := fun _ _ _ => Iff.rfl
  have mi : g ∈ isomG M.L S.Hm ↔ ∀ x y, S.h (g x) (g y) = S.h x y := Iff.rfl
  have mp : ∀ (Y : Submodule E S.V) (v : S.V), v ∈ perp M.L S.Hm Y ↔ ∀ y ∈ Y, S.h v y = 0 :=
    fun _ _ => Iff.rfl
  simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf, mu, mi]
  constructor
  · rintro ⟨⟨hiso, hu⟩, hp⟩
    exact ⟨hiso, fun j hj v hv => (hu ⟨j, hj⟩).2 v hv, hp.2⟩
  · rintro ⟨hiso, hu, hp⟩
    have hfl := flag_iff (S.spanTo f) (spanTo_zero S f) (spanTo_mono S f) r g hu
    refine ⟨⟨hiso, fun j => ⟨hfl (j + 1) j.isLt, hu j j.isLt⟩⟩, ?_, hp⟩
    have hX := hfl r le_rfl
    intro v
    rw [mp, mp]
    constructor
    · intro hv y hy
      rw [← hiso v y]
      exact hv (g y) ((hX y).2 hy)
    · intro hv y hy
      have hy' : g.symm y ∈ S.spanTo f r := (hX _).1 (by simpa using hy)
      have := hv (g.symm y) hy'
      rw [← hiso v (g.symm y), LinearEquiv.apply_symm_apply] at this
      exact this

section Frame

variable (S : Frames M.L r k) (e : V ≃ₗ[E] S.V) (Fr : LocNG.FrameD H r) (f : Fin (r + 1) → S.V)

/- English proof (translation)
Unfold `LocNG.FrameD.Fj HermSp.X`. Use `congr 1`. Use extensionality with `v`. Simplify using `[LocNG.FrameD.e]`.
-/
lemma Fj_r : Fr.Fj r = H.X Fr.f := by
  unfold LocNG.FrameD.Fj HermSp.X
  congr 1
  ext v
  simp [LocNG.FrameD.e]

/- English proof (translation)
Establish `hs : S.spanTo f j = (Fr.Fj j).map (e : V →ₗ[E] S.V)`. Unfold `Frames.spanTo LocNG.FrameD.Fj`. Rewrite using `[Submodule.map_span]`. Use `congr 1`. Use extensionality with `y`.

Simplify using `only [Set.mem_image, Set.mem_ofPred_eq, LinearEquiv.coe_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, hi, rfl⟩`. Use `⟨Fr.e ⟨i, by omega⟩, ⟨⟨i, by omega⟩, hi, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hf]`.

Both sides reduce to the same expression. Introduce and unpack `⟨_, ⟨a, ha, rfl⟩, rfl⟩`. Conclude with `⟨a.castSucc, by simpa using ha, by rw [hf]; rfl⟩`. Rewrite using `[hs, Submodule.mem_map_equiv]`. Simplify using the standard rewrite rules.
-/
lemma mem_Fj (hf : ∀ a, f a = e (Fr.f a)) (j : ℕ) (hj : j ≤ r) (x : V) :
    x ∈ Fr.Fj j ↔ e x ∈ S.spanTo f j := by
  have hs : S.spanTo f j = (Fr.Fj j).map (e : V →ₗ[E] S.V) := by
    unfold Frames.spanTo LocNG.FrameD.Fj
    rw [Submodule.map_span]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨Fr.e ⟨i, by omega⟩, ⟨⟨i, by omega⟩, hi, rfl⟩, ?_⟩
      rw [hf]
      rfl
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a.castSucc, by simpa using ha, by rw [hf]; rfl⟩
  rw [hs, Submodule.mem_map_equiv]
  simp

/- English proof (translation)
Rewrite using `[← Fj_r Fr]`. Conclude with `mem_Fj S e Fr f hf r le_rfl x`.
-/
lemma mem_X (hf : ∀ a, f a = e (Fr.f a)) (x : V) : x ∈ H.X Fr.f ↔ e x ∈ S.spanTo f r := by
  rw [← Fj_r Fr]
  exact mem_Fj S e Fr f hf r le_rfl x

/- English proof (translation)
Establish `hX` using `mem_X S e Fr f hf`. Express the relevant statement in the definitionally equal form `(∀ y ∈ H.X Fr.f, H.h x y = 0) ↔ ∀ y ∈ S.spanTo f r, S.h (e x) y = 0`. Prove the components needed by the constructor for the conclusion. Introduce `h y hy`. Use `h (e.symm y) ((hX _).2 (by simpa using hy))` as an intermediate fact.

Rewrite `this` using `[← he, e.apply_symm_apply]`. Conclude with `this`. Introduce `h y hy`. Rewrite using `[← he]`. Conclude with `h (e y) ((hX y).1 hy)`.
-/
lemma mem_perp (he : ∀ x y, S.h (e x) (e y) = H.h x y) (hf : ∀ a, f a = e (Fr.f a)) (x : V) :
    x ∈ H.perp (H.X Fr.f) ↔ e x ∈ perp M.L S.Hm (S.spanTo f r) := by
  have hX := mem_X S e Fr f hf
  change (∀ y ∈ H.X Fr.f, H.h x y = 0) ↔ ∀ y ∈ S.spanTo f r, S.h (e x) y = 0
  constructor
  · intro h y hy
    have := h (e.symm y) ((hX _).2 (by simpa using hy))
    rw [← he, e.apply_symm_apply] at this
    exact this
  · intro h y hy
    rw [← he]
    exact h (e y) ((hX y).1 hy)

/- English proof (translation)
Rewrite using `[mem_Nof]`. Simplify using `only [LocNG.FrameD.NSet, Set.mem_ofPred_eq, LocNG.IsUnitary]`. Establish `hgS : ∀ v w, S.h (g' (e v)) (g' (e w)) = H.h (g v) (g w)` using `fun v w => by rw [hg, hg, he]`. Establish `hsub : ∀ v, g' (e v) - e v = e (g v - v)` using `fun v => by rw [hg, map_sub]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hu, hfl, hp⟩`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y`. Take `⟨v, rfl⟩` from `e.surjective x`. Take `⟨w, rfl⟩` from `e.surjective y`.

Rewrite using `[hgS, he]`. Conclude with `hu v w`. Introduce `j hj x hx`. Take `⟨v, rfl⟩` from `e.surjective x`. Rewrite using `[hsub, ← mem_Fj S e Fr f hf j (by omega)]`.

Use `hfl (j + 1) (by omega) v ((mem_Fj S e Fr f hf (j + 1) (by omega) v).2 hx)` as an intermediate fact. Simplify using `using this`. Introduce `x hx`. Take `⟨v, rfl⟩` from `e.surjective x`. Rewrite using `[hsub, ← mem_X S e Fr f hf]`.

Conclude with `hp v ((mem_perp S e Fr f he hf v).2 hx)`. Introduce and unpack `⟨hu, hfl, hp⟩`. Use `⟨fun v w => ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hgS, ← he]`. Conclude with `hu _ _`.

Introduce `j hj v hv`. Consider the cases of `j with`. Consider the case `zero`. Establish `h0` using `(mem_Fj S e Fr f hf 0 (Nat.zero_le _) v).1 hv`. Rewrite `h0` using `[spanTo_zero, Submodule.mem_bot]`.

Establish `hv0 : v = 0` using `e.injective (by rw [h0, map_zero])`. Substitute `hv0` using the available equality. Simplify using the standard rewrite rules. Consider the case `succ i`. Rewrite using `[Nat.add_sub_cancel, mem_Fj S e Fr f hf i (by omega), ← hsub]`.

Conclude with `hfl i (by omega) (e v) ((mem_Fj S e Fr f hf (i + 1) hj v).1 hv)`. Introduce `v hv`. Rewrite using `[mem_X S e Fr f hf, ← hsub]`. Conclude with `hp (e v) ((mem_perp S e Fr f he hf v).1 hv)`.
-/
lemma mem_NSet (he : ∀ x y, S.h (e x) (e y) = H.h x y) (hf : ∀ a, f a = e (Fr.f a))
    (g : V ≃ₗ[E] V) (g' : S.GLV) (hg : ∀ v, g' (e v) = e (g v)) :
    g ∈ Fr.NSet ↔ g' ∈ S.Nof f := by
  rw [mem_Nof]
  simp only [LocNG.FrameD.NSet, Set.mem_ofPred_eq, LocNG.IsUnitary]
  have hgS : ∀ v w, S.h (g' (e v)) (g' (e w)) = H.h (g v) (g w) := fun v w => by rw [hg, hg, he]
  have hsub : ∀ v, g' (e v) - e v = e (g v - v) := fun v => by rw [hg, map_sub]
  constructor
  · rintro ⟨hu, hfl, hp⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x y
      obtain ⟨v, rfl⟩ := e.surjective x
      obtain ⟨w, rfl⟩ := e.surjective y
      rw [hgS, he]
      exact hu v w
    · intro j hj x hx
      obtain ⟨v, rfl⟩ := e.surjective x
      rw [hsub, ← mem_Fj S e Fr f hf j (by omega)]
      have := hfl (j + 1) (by omega) v ((mem_Fj S e Fr f hf (j + 1) (by omega) v).2 hx)
      simpa using this
    · intro x hx
      obtain ⟨v, rfl⟩ := e.surjective x
      rw [hsub, ← mem_X S e Fr f hf]
      exact hp v ((mem_perp S e Fr f he hf v).2 hx)
  · rintro ⟨hu, hfl, hp⟩
    refine ⟨fun v w => ?_, ?_, ?_⟩
    · rw [← hgS, ← he]
      exact hu _ _
    · intro j hj v hv
      cases j with
      | zero =>
        have h0 := (mem_Fj S e Fr f hf 0 (Nat.zero_le _) v).1 hv
        rw [spanTo_zero, Submodule.mem_bot] at h0
        have hv0 : v = 0 := e.injective (by rw [h0, map_zero])
        subst hv0
        simp
      | succ i =>
        rw [Nat.add_sub_cancel, mem_Fj S e Fr f hf i (by omega), ← hsub]
        exact hfl i (by omega) (e v) ((mem_Fj S e Fr f hf (i + 1) hj v).1 hv)
    · intro v hv
      rw [mem_X S e Fr f hf, ← hsub]
      exact hp (e v) ((mem_perp S e Fr f he hf v).1 hv)

end Frame

variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)

/- English proof (translation)
Simplify using `[Coord.grp]`.
-/
lemma grp_apply (g : V ≃ₗ[E] V) (v : V) : c.grp g (c.e v) = c.e (g v) := by
  simp [Coord.grp]

/- English proof (translation)
Establish `hset : Fr.NSet = {g | c.grp g ∈ S.Nof f}`. Use extensionality with `g`. Conclude with `mem_NSet S c.e Fr f c.h_eq hf g (c.grp g) (grp_apply c g)`. Establish `hsub : Fr.N = (S.Nof f).comap c.grp.toMonoidHom`. Rewrite using `[LocNG.FrameD.N, hset]`.

Conclude with `Subgroup.closure_eq ((S.Nof f).comap c.grp.toMonoidHom)`. Rewrite using `[hsub]`. Both sides reduce to the same expression.
-/
lemma mem_N (Fr : LocNG.FrameD H r) (f : Fin (r + 1) → S.V) (hf : ∀ a, f a = c.e (Fr.f a))
    (g : V ≃ₗ[E] V) : g ∈ Fr.N ↔ c.grp g ∈ S.Nof f := by
  have hset : Fr.NSet = {g | c.grp g ∈ S.Nof f} := by
    ext g
    exact mem_NSet S c.e Fr f c.h_eq hf g (c.grp g) (grp_apply c g)
  have hsub : Fr.N = (S.Nof f).comap c.grp.toMonoidHom := by
    rw [LocNG.FrameD.N, hset]
    exact Subgroup.closure_eq ((S.Nof f).comap c.grp.toMonoidHom)
  rw [hsub]
  rfl

/- English proof (translation)
Unfold `LocNG.theta Frames.th`. Break down `hs : M.split with _ | g` into its components or cases. Simplify using `[c.gg_none hs]`. Take `⟨h1, h2⟩` from `c.gg_some g hs`. Simplify using `[h1, h2]`.
-/
lemma theta_eq (c : Coord P S) : LocNG.theta M = S.th := by
  unfold LocNG.theta Frames.th
  rcases hs : M.split with _ | g
  · simp [c.gg_none hs]
  · obtain ⟨h1, h2⟩ := c.gg_some g hs
    simp [h1, h2]

/- English proof (translation)
Unfold `LocNG.FrameD.psiN LocNG.FrameD.psiOf LocNG.FrameD.coefSum Frames.psiOf Frames.coef`. Simplify using `only [hf, hes, grp_apply, c.h_eq, theta_eq c]`.
-/
lemma psi_eq (Fr : LocNG.FrameD H r) (f : Fin (r + 1) → S.V) (es : Fin r → S.V)
    (hf : ∀ a, f a = c.e (Fr.f a)) (hes : ∀ a, es a = c.e (Fr.es a)) (g : V ≃ₗ[E] V) :
    Fr.psiN (LocNG.theta M) g = S.psiOf f es (c.grp g) := by
  unfold LocNG.FrameD.psiN LocNG.FrameD.psiOf LocNG.FrameD.coefSum Frames.psiOf Frames.coef
  simp only [hf, hes, grp_apply, c.h_eq, theta_eq c]

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M _ V _ _ H r k P S c`. Use `⟨theta_eq c, fun g => mem_N c P.A S.f c.f_eq g, fun g => mem_N c P.B S.f' c.f'_eq g, ?_, fun g => ⟨psi_eq c P.A S.f S.es c.f_eq c.es_eq g, psi_eq c P.B S.f' S.es' c.f'_eq c.es'_eq g⟩, fun x => mem_X S c.e P.A S.f c.f_eq x, fun x => mem_X S c.e P.B S.f' c.f'_eq x, fun x => mem_per …` and prove the remaining obligations. Introduce `g`. Rewrite using `[LocNG.FPair.St, Frames.St, Subgroup.mem_inf, Subgroup.mem_inf, mem_N c P.A S.f c.f_eq, mem_N c P.B S.f' c.f'_eq]`. Both sides reduce to the same expression.
-/
theorem transport : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), LocNG.theta M = S.th ∧ (∀ g, g ∈ P.A.N ↔ c.grp g ∈ S.N) ∧ (∀ g, g ∈ P.B.N ↔ c.grp g ∈ S.N') ∧ (∀ g, g ∈ P.St ↔ c.grp g ∈ S.St) ∧ (∀ g, P.A.psiN (LocNG.theta M) g = S.psi (c.grp g) ∧ P.B.psiN (LocNG.theta M) g = S.psi' (c.grp g)) ∧ (∀ x, x ∈ H.X P.A.f ↔ c.e x ∈ S.X) ∧ (∀ x, x ∈ H.X P.B.f ↔ c.e x ∈ S.X') ∧ (∀ x, x ∈ H.perp (H.X P.A.f) ↔ c.e x ∈ perp M.L S.Hm S.X) ∧ ∀ x, x ∈ H.perp (H.X P.B.f) ↔ c.e x ∈ perp M.L S.Hm S.X' := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r k P S c
  refine ⟨theta_eq c, fun g => mem_N c P.A S.f c.f_eq g, fun g => mem_N c P.B S.f' c.f'_eq g, ?_,
    fun g => ⟨psi_eq c P.A S.f S.es c.f_eq c.es_eq g, psi_eq c P.B S.f' S.es' c.f'_eq c.es'_eq g⟩,
    fun x => mem_X S c.e P.A S.f c.f_eq x, fun x => mem_X S c.e P.B S.f' c.f'_eq x,
    fun x => mem_perp S c.e P.A S.f c.h_eq c.f_eq x, fun x => mem_perp S c.e P.B S.f' c.h_eq c.f'_eq x⟩
  intro g
  rw [LocNG.FPair.St, Frames.St, Subgroup.mem_inf, Subgroup.mem_inf, mem_N c P.A S.f c.f_eq,
    mem_N c P.B S.f' c.f'_eq]
  rfl

end GlobalTheory.HL.CoordUnip
