import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameCoordinatesTransportInnerLattices
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportInnerLattices
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermOverFrameCoordinates

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical Pointwise

noncomputable section

namespace GlobalTheory.LocOver.TermLat

open GlobalTheory.HL

section Mat

variable {E : Type} [CommRing E] {m : ℕ}

/- English proof (translation)
Use `set e := Fin.castLE hl with he`. Establish `hsub : ∀ (X Y : Matrix (Fin m) (Fin m) E), (∀ (i j : Fin l) (p : Fin m), l ≤ (p : ℕ) → X (e i) p * Y p (e j) = 0) → (X * Y).submatrix e e = X.submatrix e e * Y.submatrix e e`. Introduce `X Y hXY`. Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`.

Use `symm`. Use `Fintype.sum_of_injective e (Fin.castLE_injective hl) _ _ ?_ ?_` and prove the remaining obligations. Introduce `p hp`. Apply `hXY i j p` to reduce the goal to its premises. Assume the negation of the conclusion as `hlt`.

Use `push_neg at hlt`. Conclude with `hp ⟨⟨p, hlt⟩, rfl⟩`. Introduce `p`. Both sides reduce to the same expression. Establish `hdA : (A.submatrix e e).det = 1`.

Rewrite using `[Matrix.det_of_lowerTriangular (A.submatrix e e) (fun i j hij => hA _ _ (by exact OrderDual.toDual_lt_toDual.1 hij))]`. Simplify using `[hA1]`. Establish `hdB : (B.submatrix e e).det = 1`. Rewrite using `[Matrix.det_of_upperTriangular (show (B.submatrix e e).BlockTriangular id from fun i j hij => hB _ _ (by exact hij))]`. Simplify using `[hB1]`.

Rewrite using `[hsub (A * Z) B (fun i j p hp => by`. Rewrite using `[hB p (e j) (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le j.2 hp)), mul_zero]),`. Use `hsub A Z (fun i j p hp => by`. Rewrite using `[hA (e i) p (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le i.2 hp)), zero_mul]),`. Use the proof step `Matrix.det_mul, Matrix.det_mul, hdA, hdB, one_mul, mul_one]`.
-/
theorem minor_tri (A B Z : Matrix (Fin m) (Fin m) E) (hA : ∀ i j, i < j → A i j = 0) (hA1 : ∀ i, A i i = 1)
    (hB : ∀ i j, j < i → B i j = 0) (hB1 : ∀ i, B i i = 1) {l : ℕ} (hl : l ≤ m) :
    ((A * Z * B).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  set e := Fin.castLE hl with he
  have hsub : ∀ (X Y : Matrix (Fin m) (Fin m) E),
      (∀ (i j : Fin l) (p : Fin m), l ≤ (p : ℕ) → X (e i) p * Y p (e j) = 0) →
      (X * Y).submatrix e e = X.submatrix e e * Y.submatrix e e := by
    intro X Y hXY
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective e (Fin.castLE_injective hl) _ _ ?_ ?_
    · intro p hp
      apply hXY i j p
      by_contra hlt
      push_neg at hlt
      exact hp ⟨⟨p, hlt⟩, rfl⟩
    · intro p
      rfl
  have hdA : (A.submatrix e e).det = 1 := by
    rw [Matrix.det_of_lowerTriangular (A.submatrix e e)
      (fun i j hij => hA _ _ (by exact OrderDual.toDual_lt_toDual.1 hij))]
    simp [hA1]
  have hdB : (B.submatrix e e).det = 1 := by
    rw [Matrix.det_of_upperTriangular
      (show (B.submatrix e e).BlockTriangular id from fun i j hij => hB _ _ (by exact hij))]
    simp [hB1]
  rw [hsub (A * Z) B (fun i j p hp => by
      rw [hB p (e j) (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le j.2 hp)), mul_zero]),
    hsub A Z (fun i j p hp => by
      rw [hA (e i) p (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le i.2 hp)), zero_mul]),
    Matrix.det_mul, Matrix.det_mul, hdA, hdB, one_mul, mul_one]

end Mat

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

/- English proof (translation)
Rewrite `hx`, the goal using `[M.L.O_def]`. Conclude with `hx.map M.L.cj`.
-/
theorem cj_mem {x : E} (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := by
  rw [M.L.O_def] at hx ⊢
  exact hx.map M.L.cj

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_empty]`. Conclude with `H.h_zero_left y`. Introduce `a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, ih]`.
-/
theorem h_sum_left {ι : Type} (s : Finset ι) (u : ι → V) (y : V) :
    H.h (∑ i ∈ s, u i) y = ∑ i ∈ s, H.h (u i) y := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty]
    exact H.h_zero_left y
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, ih]

/- English proof (translation)
Rewrite using `[H.h_herm, h_sum_left, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[H.h_smul_left, map_mul, ← H.h_herm]`.
-/
theorem h_right_sum {ι : Type} [Fintype ι] (a : ι → E) (u : ι → V) (x : V) :
    H.h x (∑ i, a i • u i) = ∑ i, M.L.cj (a i) * H.h x (u i) := by
  rw [H.h_herm, h_sum_left, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [H.h_smul_left, map_mul, ← H.h_herm]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [HermSp.Zhat, Matrix.mul_apply, Matrix.of_apply, hg, hg']`. Rewrite using `[h_sum_left]`. Simplify using `only [H.h_smul_left, h_right_sum, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem zhat_change (f f' g g' : Fin (r + 1) → V) (s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hg : ∀ j, g j = ∑ i, s i j • f i) (hg' : ∀ j, g' j = ∑ i, s' i j • f' i) :
    H.Zhat g g' = (Matrix.of fun a c => M.L.cj (s c a)) * H.Zhat f f' * s' := by
  ext a b
  simp only [HermSp.Zhat, Matrix.mul_apply, Matrix.of_apply, hg, hg']
  rw [h_sum_left]
  simp only [H.h_smul_left, h_right_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Unfold `HermSp.Dl`. Use `split_ifs with hl`. Rewrite using `[zhat_change f f' g g' s s' hg hg']`. Conclude with `minor_tri _ _ _ (fun i j hij => by simp [h0 j i hij]) (fun i => by simp [h1]) h0' h1' hl`. Both sides reduce to the same expression.
-/
theorem dl_change (f f' g g' : Fin (r + 1) → V) (s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (h0 : ∀ i j, j < i → s i j = 0) (h1 : ∀ i, s i i = 1) (h0' : ∀ i j, j < i → s' i j = 0)
    (h1' : ∀ i, s' i i = 1) (hg : ∀ j, g j = ∑ i, s i j • f i) (hg' : ∀ j, g' j = ∑ i, s' i j • f' i)
    (l : ℕ) : H.Dl g g' l = H.Dl f f' l := by
  unfold HermSp.Dl
  split_ifs with hl
  · rw [zhat_change f f' g g' s s' hg hg']
    exact minor_tri _ _ _ (fun i j hij => by simp [h0 j i hij]) (fun i => by simp [h1]) h0' h1' hl
  · rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨w, hw, hwv⟩` from `Submodule.mem_map.1 h`. Rewrite using `[← c.e.injective hwv]` and apply the resulting hypothesis. Introduce `h`.

Conclude with `Submodule.mem_map.2 ⟨v, h, rfl⟩`.
-/
private theorem e_mem_lat_iff {P : FPair H r} {S : Frames M.L r k} (c : Coord P S) (Λ : Submodule M.L.O V) (v : V) :
    c.e v ∈ c.lat Λ ↔ v ∈ Λ := by
  constructor
  · intro h
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.1 h
    rwa [← c.e.injective hwv]
  · intro h
    exact Submodule.mem_map.2 ⟨v, h, rfl⟩

section Coordinates

variable {P : FPair H r} {S : Frames M.L r k} (c : Coord P S)

include c in

/- English proof (translation)
Take `⟨⟨hfg, hsp⟩, hd⟩` from `h`. Establish `hmem : ∀ v, c.e v ∈ c.lat Λ ↔ v ∈ Λ` using `e_mem_lat_iff c Λ`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Submodule.fg_of_fg_map_injective ((c.e : V →ₗ[E] S.V).restrictScalars M.L.O) c.e.injective hfg`. Apply `Submodule.map_injective_of_injective (f := (c.e : V →ₗ[E] S.V)) c.e.injective` to reduce the goal to its premises.

Rewrite using `[Submodule.map_top, LinearEquiv.range, ← Submodule.span_image]`. Conclude with `hsp`. Introduce `x`. Rewrite using `[← hmem x, ← hd (c.e x)]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx y hy`. Establish `h1` using `hx (c.e y) ((hmem y).2 hy)`. Establish `h2 : hf M.L S.Hm (c.e y) (c.e x) = H.h y x` using `c.h_eq y x`. Rewrite `h1` using `[h2]`. Rewrite using `[H.h_herm]`.

Conclude with `cj_mem h1`. Introduce `hx w hw`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.1 hw`. Establish `h2 : hf M.L S.Hm (c.e y) (c.e x) = H.h y x` using `c.h_eq y x`. Use `show hf M.L S.Hm (c.e y) (c.e x) ∈ M.L.O`.

Rewrite using `[h2, H.h_herm]`. Conclude with `cj_mem (hx y hy)`.
-/
theorem selfDual_of (Λ : Submodule M.L.O V) (h : IsSD M.L S.Hm (c.lat Λ)) : H.IsSelfDual Λ := by
  obtain ⟨⟨hfg, hsp⟩, hd⟩ := h
  have hmem : ∀ v, c.e v ∈ c.lat Λ ↔ v ∈ Λ := e_mem_lat_iff c Λ
  refine ⟨?_, ?_, ?_⟩
  · exact Submodule.fg_of_fg_map_injective ((c.e : V →ₗ[E] S.V).restrictScalars M.L.O) c.e.injective hfg
  · apply Submodule.map_injective_of_injective (f := (c.e : V →ₗ[E] S.V)) c.e.injective
    rw [Submodule.map_top, LinearEquiv.range, ← Submodule.span_image]
    exact hsp
  · intro x
    rw [← hmem x, ← hd (c.e x)]
    constructor
    · intro hx y hy
      have h1 := hx (c.e y) ((hmem y).2 hy)
      have h2 : hf M.L S.Hm (c.e y) (c.e x) = H.h y x := c.h_eq y x
      rw [h2] at h1
      rw [H.h_herm]
      exact cj_mem h1
    · intro hx w hw
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hw
      have h2 : hf M.L S.Hm (c.e y) (c.e x) = H.h y x := c.h_eq y x
      show hf M.L S.Hm (c.e y) (c.e x) ∈ M.L.O
      rw [h2, H.h_herm]
      exact cj_mem (hx y hy)

/- English proof (translation)
Rewrite using `[Coord.inn, e_mem_lat_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨z, hz, rfl⟩` from `Submodule.mem_map.1 h`. Conclude with `⟨z.2, hz⟩`.

Introduce and unpack `⟨hv, hL⟩`. Conclude with `Submodule.mem_map.2 ⟨⟨v, hv⟩, hL, rfl⟩`.
-/
private theorem e_mem_inn_iff_exists_mkW_mem (c : Coord P S) (f : Fin (r + 1) → V) (L : Submodule M.L.O (H.Wb f)) (v : V) :
    c.e v ∈ c.inn f L ↔ ∃ hv : v ∈ H.perp (H.X f), H.mkW f ⟨v, hv⟩ ∈ L := by
  rw [Coord.inn, e_mem_lat_iff]
  constructor
  · intro h
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 h
    exact ⟨z.2, hz⟩
  · rintro ⟨hv, hL⟩
    exact Submodule.mem_map.2 ⟨⟨v, hv⟩, hL, rfl⟩

/- English proof (translation)
Establish `key : ∀ x : V, c.e x ∈ c.inn f L ↔ ∃ y ∈ c.lat Λ, y ∈ perp M.L S.Hm (S.spanTo g r) ∧ y - c.e x ∈ S.spanTo g r`. Introduce `x`. Rewrite using `[h3, e]`. Conclude with `TermBasic.inner_smul S hn (c.e x)`. Use extensionality with `w`.

Take `⟨x0, rfl⟩` from `Submodule.mkQ_surjective _ w`. Simplify using `only [HermSp.Lset, Set.mem_setOf_eq, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce `hw`. Take `⟨y, hy, hyp, hyx⟩` from `(key x0).1 ((e_mem_inn_iff_exists_mkW_mem c f L x0).2 ⟨x0.2, hw⟩)`.

Take `⟨v, hv, rfl⟩` from `Submodule.mem_map.1 hy`. Establish `hvp : v ∈ H.perp (H.X f)` using `(hp v).2 hyp`. Establish `hdiff : v - (x0 : V) ∈ H.X f` using `(hX _).2 (by rw [map_sub]; exact hyx)`. Use `⟨⟨v, hvp⟩, hv, ?_⟩` and prove the remaining obligations. Conclude with `(Submodule.Quotient.eq _).2 hdiff`.

Introduce and unpack `⟨x, hxΛ, hxw⟩`. Rewrite using `[← hxw]`. Establish `hx` using `(key x).2 ⟨c.e x, (e_mem_lat_iff c Λ x).2 hxΛ, (hp x).1 x.2, by simp⟩`. Take `⟨_, hL⟩` from `(e_mem_inn_iff_exists_mkW_mem c f L x).1 hx`. Conclude with `hL`.
-/
theorem lset_of (f : Fin (r + 1) → V) (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (hX : ∀ x, x ∈ H.X f ↔ c.e x ∈ S.spanTo g r)
    (hp : ∀ x, x ∈ H.perp (H.X f) ↔ c.e x ∈ perp M.L S.Hm (S.spanTo g r))
    (L : Submodule M.L.O (H.Wb f)) (Λ : Submodule M.L.O V) (n : V ≃ₗ[E] V) (hn : c.grp n ∈ S.Nof g)
    (e : c.lat Λ = c.grp n • S.stdLat g gs (c.inn f L))
    (h3 : ∀ x, x ∈ c.inn f L ↔ ∃ y ∈ S.stdLat g gs (c.inn f L),
      y ∈ perp M.L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r) :
    (L : Set (H.Wb f)) = H.Lset Λ f := by
  have key : ∀ x : V, c.e x ∈ c.inn f L ↔
      ∃ y ∈ c.lat Λ, y ∈ perp M.L S.Hm (S.spanTo g r) ∧ y - c.e x ∈ S.spanTo g r := by
    intro x
    rw [h3, e]
    exact TermBasic.inner_smul S hn (c.e x)
  ext w
  obtain ⟨x0, rfl⟩ := Submodule.mkQ_surjective _ w
  simp only [HermSp.Lset, Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · intro hw
    obtain ⟨y, hy, hyp, hyx⟩ := (key x0).1 ((e_mem_inn_iff_exists_mkW_mem c f L x0).2 ⟨x0.2, hw⟩)
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hy
    have hvp : v ∈ H.perp (H.X f) := (hp v).2 hyp
    have hdiff : v - (x0 : V) ∈ H.X f := (hX _).2 (by rw [map_sub]; exact hyx)
    refine ⟨⟨v, hvp⟩, hv, ?_⟩
    exact (Submodule.Quotient.eq _).2 hdiff
  · rintro ⟨x, hxΛ, hxw⟩
    rw [← hxw]
    have hx := (key x).2 ⟨c.e x, (e_mem_lat_iff c Λ x).2 hxΛ, (hp x).1 x.2, by simp⟩
    obtain ⟨_, hL⟩ := (e_mem_inn_iff_exists_mkW_mem c f L x).1 hx
    exact hL

/- English proof (translation)
Simplify using `only [Frames.Nof, Subgroup.mem_inf] at hm`. Conclude with `hm.1.1`.
-/
private theorem mem_isomG_of_mem_Nof_frames {S : Frames M.L r k} (g : Fin (r + 1) → S.V) {m : S.GLV} (hm : m ∈ S.Nof g) :
    m ∈ isomG M.L S.Hm := by
  simp only [Frames.Nof, Subgroup.mem_inf] at hm
  exact hm.1.1

/- English proof (translation)
Establish `hI : c.grp n ∈ isomG M.L S.Hm` using `mem_isomG_of_mem_Nof_frames g hn`. Establish `h1` using `(show ∀ a b, hf M.L S.Hm (c.grp n a) (c.grp n b) = hf M.L S.Hm a b from hI) (c.e x) (c.e y)`. Rewrite `h1` using `[CoordUnip.grp_apply, CoordUnip.grp_apply]`. Establish `h2 : hf M.L S.Hm (c.e (n x)) (c.e (n y)) = H.h (n x) (n y)` using `c.h_eq (n x) (n y)`. Establish `h3 : hf M.L S.Hm (c.e x) (c.e y) = H.h x y` using `c.h_eq x y`.

Rewrite using `[← h2, ← h3]`. Conclude with `h1`.
-/
theorem isom_of (g : Fin (r + 1) → S.V) {n : V ≃ₗ[E] V} (hn : c.grp n ∈ S.Nof g) (x y : V) :
    H.h (n x) (n y) = H.h x y := by
  have hI : c.grp n ∈ isomG M.L S.Hm := mem_isomG_of_mem_Nof_frames g hn
  have h1 := (show ∀ a b, hf M.L S.Hm (c.grp n a) (c.grp n b) = hf M.L S.Hm a b from hI) (c.e x) (c.e y)
  rw [CoordUnip.grp_apply, CoordUnip.grp_apply] at h1
  have h2 : hf M.L S.Hm (c.e (n x)) (c.e (n y)) = H.h (n x) (n y) := c.h_eq (n x) (n y)
  have h3 : hf M.L S.Hm (c.e x) (c.e y) = H.h x y := c.h_eq x y
  rw [← h2, ← h3]
  exact h1

/- English proof (translation)
Establish `hfr : ∀ b, c.grp n (g b) = c.e (n (Fr.f b))` using `fun b => by rw [hgf, CoordUnip.grp_apply]`. Unfold `HermSp.IsFrame HermSp.Prim`. Use `⟨⟨?_, ?_, ?_⟩, ?_, ?_, hT, hT0⟩` and prove the remaining obligations. Introduce `a`. Establish `ha : c.e (n (Fr.f a)) ∈ c.lat Λ` using `((htr _).2 (Submodule.subset_span ⟨a, a.2, hfr a⟩)).1`.

Conclude with `(e_mem_lat_iff c Λ _).1 ha`. Establish `hli' : LinearIndependent E Fr.f`. Establish `h1 : LinearIndependent E ((c.e : V →ₗ[E] S.V) ∘ Fr.f)`. Use `hli using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `a`.

Conclude with `(hgf a).symm`. Conclude with `LinearIndependent.of_comp _ h1`. Conclude with `hli'.map' (n : V →ₗ[E] V) n.ker`. Introduce `x hx hxs`. Establish `hxS : c.e x ∈ S.spanTo g (r + 1)`.

Establish `h1` using `Submodule.apply_mem_span_image_of_mem_span (c.e : V →ₗ[E] S.V) hxs`. Use `Submodule.span_le.2 ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨b, rfl⟩, rfl⟩`. Use `show c.e (n (Fr.f b)) ∈ S.spanTo g (r + 1)`. Rewrite using `[← hfr b]`.

Conclude with `(TermBasic.map_mem_iff hg hn (r + 1) (g b)).2 (TermBasic.self_mem S g b.2)`. Establish `h2` using `(htr (c.e x)).1 ⟨(e_mem_lat_iff c Λ x).2 hx, hxS⟩`. Establish `h3` using `Submodule.apply_mem_span_image_of_mem_span ((c.e.symm : S.V →ₗ[E] V).restrictScalars M.L.O) h2`. Establish `h4 : ((c.e.symm : S.V →ₗ[E] V).restrictScalars M.L.O) (c.e x) = x` using `c.e.symm_apply_apply x`. Rewrite `h3` using `[h4]`.

Use `Submodule.span_mono ?_ h3` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨b, _, rfl⟩, rfl⟩`. Conclude with `⟨b, by simp [hfr]⟩`. Introduce `a b hab show H.h (n (Fr.f a)) (n (Fr.f b)) = 0`. Rewrite using `[isom_of c g hn]`.

Conclude with `Fr.h_iso a b hab`. Use `show H.h (n (Fr.f (Fin.last r))) (n (Fr.f (Fin.last r))) = -algebraMap F E Fr.T`. Rewrite using `[isom_of c g hn]`. Conclude with `Fr.h_zz`.
-/
theorem frame_of (Fr : FrameD H r) (g : Fin (r + 1) → S.V) (hgf : ∀ a, g a = c.e (Fr.f a))
    (hg : ∀ a (j : Fin r), hf M.L S.Hm (g a) (g j.castSucc) = 0) (hli : LinearIndependent E g)
    (n : V ≃ₗ[E] V) (hn : c.grp n ∈ S.Nof g) (Λ : Submodule M.L.O V)
    (htr : ∀ x, (x ∈ c.lat Λ ∧ x ∈ S.spanTo g (r + 1)) ↔
      x ∈ Submodule.span M.L.O ((fun b => c.grp n (g b)) '' {i | (i : ℕ) < r + 1}))
    (hT : Fr.T ∈ 𝒪[F]) (hT0 : Fr.T ≠ 0) : H.IsFrame Λ r (fun b => n (Fr.f b)) Fr.T := by
  have hfr : ∀ b, c.grp n (g b) = c.e (n (Fr.f b)) := fun b => by rw [hgf, CoordUnip.grp_apply]
  unfold HermSp.IsFrame HermSp.Prim
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, hT, hT0⟩
  · intro a
    have ha : c.e (n (Fr.f a)) ∈ c.lat Λ :=
      ((htr _).2 (Submodule.subset_span ⟨a, a.2, hfr a⟩)).1
    exact (e_mem_lat_iff c Λ _).1 ha
  · have hli' : LinearIndependent E Fr.f := by
      have h1 : LinearIndependent E ((c.e : V →ₗ[E] S.V) ∘ Fr.f) := by
        convert hli using 1
        funext a
        exact (hgf a).symm
      exact LinearIndependent.of_comp _ h1
    exact hli'.map' (n : V →ₗ[E] V) n.ker
  · intro x hx hxs
    have hxS : c.e x ∈ S.spanTo g (r + 1) := by
      have h1 := Submodule.apply_mem_span_image_of_mem_span (c.e : V →ₗ[E] S.V) hxs
      refine Submodule.span_le.2 ?_ h1
      rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
      show c.e (n (Fr.f b)) ∈ S.spanTo g (r + 1)
      rw [← hfr b]
      exact (TermBasic.map_mem_iff hg hn (r + 1) (g b)).2 (TermBasic.self_mem S g b.2)
    have h2 := (htr (c.e x)).1 ⟨(e_mem_lat_iff c Λ x).2 hx, hxS⟩
    have h3 := Submodule.apply_mem_span_image_of_mem_span
      ((c.e.symm : S.V →ₗ[E] V).restrictScalars M.L.O) h2
    have h4 : ((c.e.symm : S.V →ₗ[E] V).restrictScalars M.L.O) (c.e x) = x := c.e.symm_apply_apply x
    rw [h4] at h3
    refine Submodule.span_mono ?_ h3
    rintro _ ⟨_, ⟨b, _, rfl⟩, rfl⟩
    exact ⟨b, by simp [hfr]⟩
  · intro a b hab
    show H.h (n (Fr.f a)) (n (Fr.f b)) = 0
    rw [isom_of c g hn]
    exact Fr.h_iso a b hab
  · show H.h (n (Fr.f (Fin.last r))) (n (Fr.f (Fin.last r))) = -algebraMap F E Fr.T
    rw [isom_of c g hn]
    exact Fr.h_zz

include c in

/- English proof (translation)
Apply `c.e.injective` to reduce the goal to its premises. Rewrite using `[← CoordUnip.grp_apply c n (Fr.f j), ← hgf j, hs j, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hgf i]`.
-/
theorem change_of (Fr : FrameD H r) (g : Fin (r + 1) → S.V) (hgf : ∀ a, g a = c.e (Fr.f a))
    (n : V ≃ₗ[E] V) (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hs : ∀ j, c.grp n (g j) = ∑ i, s i j • g i) (j : Fin (r + 1)) :
    n (Fr.f j) = ∑ i, s i j • Fr.f i := by
  apply c.e.injective
  rw [← CoordUnip.grp_apply c n (Fr.f j), ← hgf j, hs j, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hgf i]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[TermBasic.mem_smul]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.1 hx`.

Take `⟨z, hz, rfl⟩` from `Submodule.mem_map.1 hy`. Conclude with `⟨c.e z, (e_mem_lat_iff c Λ z).2 hz, CoordUnip.grp_apply c m z⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Take `⟨z, hz, rfl⟩` from `Submodule.mem_map.1 hy`. Use `Submodule.mem_map.2 ⟨m z, Submodule.mem_map.2 ⟨z, hz, rfl⟩, ?_⟩` and prove the remaining obligations.

Conclude with `(CoordUnip.grp_apply c m z).symm`.
-/
private theorem lat_img_eq_grp_smul_lat (c : Coord P S) (m : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) :
    c.lat (img m Λ) = c.grp m • c.lat Λ := by
  ext x
  rw [TermBasic.mem_smul]
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
    exact ⟨c.e z, (e_mem_lat_iff c Λ z).2 hz, CoordUnip.grp_apply c m z⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
    refine Submodule.mem_map.2 ⟨m z, Submodule.mem_map.2 ⟨z, hz, rfl⟩, ?_⟩
    exact (CoordUnip.grp_apply c m z).symm

/- English proof (translation)
Use `haveI := hM.loc`. Use `haveI := hM.char0`. Unfold `LocNG.FPair.RelG at hP`. Take `⟨-, hD, hG, -, -, -, hN⟩` from `hP`. Unfold `LocNG.FPair.NormsOK at hN`.

Take `⟨hTA, hA0, hTB, hB0, hNg⟩` from `hN`. Unfold `IsTermOver at ht`. Take `⟨hT, hT', ⟨n, hn, hfA, hLam⟩, ⟨n', hn', hfB, hLam'⟩, hgg⟩` from `ht`. Establish `tr` using `CoordUnip.transport M hM H r k P S c`. Establish `trA` using `CoordInnerFst.transport M hM H r k P S c`.

Establish `trB` using `CoordInnerSnd.transport M hM H r k P S c`. Establish `hli` using `(FrameBasic.main M.L r k S).1`. Establish `hnS : c.grp n ∈ S.Nof S.f` using `(tr.2.1 n).1 hn`. Establish `hnS' : c.grp n' ∈ S.Nof S.f'` using `(tr.2.2.1 n').1 hn'`. Establish `hinA : S.IsInner S.f S.es (c.inn P.A.f d.L)` using `(trA.2.1 d.L).1 d.hL`.

Establish `hinB : S.IsInner S.f' S.es' (c.inn P.B.f d.L')` using `(trB.2.1 d.L').1 d.hL'`. Establish `spA` using `StdLat.stdLat_spec M.L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩) _ hinA`. Establish `spB` using `StdLat.stdLat_spec M.L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) _ hinB`. Establish `hlatA : c.lat t.abelian₂ = c.grp n • S.stdLat S.f S.es (c.inn P.A.f d.L)`. Rewrite using `[hLam, lat_img_eq_grp_smul_lat, trA.2.2.2 d.L]`.

Establish `hlatB : c.lat t.abelian₂ = c.grp n' • S.stdLat S.f' S.es' (c.inn P.B.f d.L')`. Rewrite using `[hLam', lat_img_eq_grp_smul_lat, trB.2.2.2 d.L']`. Establish `hgA : ∀ a (j : Fin r), hf M.L S.Hm (S.f a) (S.f j.castSucc) = 0` using `fun a j => by`. Rewrite using `[S.gram]`. Conclude with `if_neg fun h => (Fin.castSucc_lt_last j).ne h.2`.

Establish `hgB : ∀ a (j : Fin r), hf M.L S.Hm (S.f' a) (S.f' j.castSucc) = 0` using `fun a j => by`. Rewrite using `[S.gram']`. Conclude with `if_neg fun h => (Fin.castSucc_lt_last j).ne h.2`. Establish `hfrA : H.IsFrame t.abelian₂ r t.f t.T`. Rewrite using `[hfA, hT]`.

Conclude with `frame_of c P.A S.f c.f_eq hgA (by simpa using hli.comp Sum.inl Sum.inl_injective) n hnS t.abelian₂ (fun x => by rw [hlatA]; exact TermBasic.trace_smul hgA hnS (spA.2.1 (r + 1) le_rfl) x) hTA hA0`. Establish `hfrB : H.IsFrame t.abelian₂ r t.f' t.T'`. Rewrite using `[hfB, hT']`. Conclude with `frame_of c P.B S.f' c.f'_eq hgB (by simpa using hli.comp Sum.inr Sum.inr_injective) n' hnS' t.abelian₂ (fun x => by rw [hlatB]; exact TermBasic.trace_smul hgB hnS' (spB.2.1 (r + 1) le_rfl) x) hTB hB0`. Take `⟨s, ⟨hs0, hs1⟩, hs⟩` from `FrameOnto.exists_matrix S S.f S.T S.gram (c.grp n) hnS`.

Take `⟨s', ⟨hs0', hs1'⟩, hs'⟩` from `FrameOnto.exists_matrix S S.f' S.T' S.gram' (c.grp n') hnS'`. Establish `hDl : ∀ l, H.Dl t.f t.f' l = H.Dl P.A.f P.B.f l` using `fun l => dl_change P.A.f P.B.f t.f t.f' s s' hs0 hs1 hs0' hs1' (fun j => by rw [hfA]; exact change_of c P.A S.f c.f_eq n s hs j) (fun j => by rw [hfB]; exact change_of c P.B S.f' c.f'_eq n' s' hs' j) l`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `HermSp.IsTerm`. Use `⟨?_, hfrA, hfrB, ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `selfDual_of c t.abelian₂ (by rw [hlatA]; exact TermBasic.isSD_smul S (mem_isomG_of_mem_Nof_frames S.f hnS) spA.1)`. Rewrite using `[hDl]`. Conclude with `hD`. Rewrite using `[show H.Gdet t.f t.f' t.T t.T' = H.Gdet P.A.f P.B.f P.A.T P.B.T by`. Simplify using `only [HermSp.Gdet, hDl, hT, hT']]`.

Conclude with `hG`. Introduce `g hg`. Take `⟨hu, hc⟩` from `hNg g hg`. Use `⟨?_, ?_, (hgg g hg).1⟩` and prove the remaining obligations. Rewrite using `[hT, hT']`.

Conclude with `hu`. Rewrite using `[hT, hT']`. Conclude with `hc`. Conclude with `lset_of c P.A.f S.f S.es tr.2.2.2.2.2.1 tr.2.2.2.2.2.2.2.1 d.L t.abelian₂ n hnS hlatA spA.2.2`. Conclude with `lset_of c P.B.f S.f' S.es' tr.2.2.2.2.2.2.1 tr.2.2.2.2.2.2.2.2 d.L' t.abelian₂ n' hnS' hlatB spB.2.2`.
-/
theorem term_over (hM : M.OK) (c : Coord P S) (hP : P.RelG (theta M)) (d : Datum P) (t : Term V M r)
    (ht : IsTermOver P d t) :
    H.IsTerm t ∧ (d.L : Set (H.Wb P.A.f)) = H.Lset t.abelian₂ P.A.f ∧
      (d.L' : Set (H.Wb P.B.f)) = H.Lset t.abelian₂ P.B.f := by
  haveI := hM.loc
  haveI := hM.char0
  unfold LocNG.FPair.RelG at hP
  obtain ⟨-, hD, hG, -, -, -, hN⟩ := hP
  unfold LocNG.FPair.NormsOK at hN
  obtain ⟨hTA, hA0, hTB, hB0, hNg⟩ := hN
  unfold IsTermOver at ht
  obtain ⟨hT, hT', ⟨n, hn, hfA, hLam⟩, ⟨n', hn', hfB, hLam'⟩, hgg⟩ := ht
  have tr := CoordUnip.transport M hM H r k P S c
  have trA := CoordInnerFst.transport M hM H r k P S c
  have trB := CoordInnerSnd.transport M hM H r k P S c
  have hli := (FrameBasic.main M.L r k S).1
  have hnS : c.grp n ∈ S.Nof S.f := (tr.2.1 n).1 hn
  have hnS' : c.grp n' ∈ S.Nof S.f' := (tr.2.2.1 n').1 hn'
  have hinA : S.IsInner S.f S.es (c.inn P.A.f d.L) := (trA.2.1 d.L).1 d.hL
  have hinB : S.IsInner S.f' S.es' (c.inn P.B.f d.L') := (trB.2.1 d.L').1 d.hL'
  have spA := StdLat.stdLat_spec M.L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩) _ hinA
  have spB := StdLat.stdLat_spec M.L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) _ hinB
  have hlatA : c.lat t.abelian₂ = c.grp n • S.stdLat S.f S.es (c.inn P.A.f d.L) := by
    rw [hLam, lat_img_eq_grp_smul_lat, trA.2.2.2 d.L]
  have hlatB : c.lat t.abelian₂ = c.grp n' • S.stdLat S.f' S.es' (c.inn P.B.f d.L') := by
    rw [hLam', lat_img_eq_grp_smul_lat, trB.2.2.2 d.L']
  have hgA : ∀ a (j : Fin r), hf M.L S.Hm (S.f a) (S.f j.castSucc) = 0 := fun a j => by
    rw [S.gram]
    exact if_neg fun h => (Fin.castSucc_lt_last j).ne h.2
  have hgB : ∀ a (j : Fin r), hf M.L S.Hm (S.f' a) (S.f' j.castSucc) = 0 := fun a j => by
    rw [S.gram']
    exact if_neg fun h => (Fin.castSucc_lt_last j).ne h.2
  have hfrA : H.IsFrame t.abelian₂ r t.f t.T := by
    rw [hfA, hT]
    exact frame_of c P.A S.f c.f_eq hgA (by simpa using hli.comp Sum.inl Sum.inl_injective) n hnS t.abelian₂
      (fun x => by rw [hlatA]; exact TermBasic.trace_smul hgA hnS (spA.2.1 (r + 1) le_rfl) x) hTA hA0
  have hfrB : H.IsFrame t.abelian₂ r t.f' t.T' := by
    rw [hfB, hT']
    exact frame_of c P.B S.f' c.f'_eq hgB (by simpa using hli.comp Sum.inr Sum.inr_injective) n' hnS' t.abelian₂
      (fun x => by rw [hlatB]; exact TermBasic.trace_smul hgB hnS' (spB.2.1 (r + 1) le_rfl) x) hTB hB0
  obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := FrameOnto.exists_matrix S S.f S.T S.gram (c.grp n) hnS
  obtain ⟨s', ⟨hs0', hs1'⟩, hs'⟩ := FrameOnto.exists_matrix S S.f' S.T' S.gram' (c.grp n') hnS'
  have hDl : ∀ l, H.Dl t.f t.f' l = H.Dl P.A.f P.B.f l := fun l =>
    dl_change P.A.f P.B.f t.f t.f' s s' hs0 hs1 hs0' hs1'
      (fun j => by rw [hfA]; exact change_of c P.A S.f c.f_eq n s hs j)
      (fun j => by rw [hfB]; exact change_of c P.B S.f' c.f'_eq n' s' hs' j) l
  refine ⟨?_, ?_, ?_⟩
  · unfold HermSp.IsTerm
    refine ⟨?_, hfrA, hfrB, ?_, ?_, ?_⟩
    · exact selfDual_of c t.abelian₂ (by rw [hlatA]; exact TermBasic.isSD_smul S (mem_isomG_of_mem_Nof_frames S.f hnS) spA.1)
    · rw [hDl]
      exact hD
    · rw [show H.Gdet t.f t.f' t.T t.T' = H.Gdet P.A.f P.B.f P.A.T P.B.T by
        simp only [HermSp.Gdet, hDl, hT, hT']]
      exact hG
    · intro g hg
      obtain ⟨hu, hc⟩ := hNg g hg
      refine ⟨?_, ?_, (hgg g hg).1⟩
      · rw [hT, hT']
        exact hu
      · rw [hT, hT']
        exact hc
  · exact lset_of c P.A.f S.f S.es tr.2.2.2.2.2.1 tr.2.2.2.2.2.2.2.1 d.L t.abelian₂ n hnS hlatA spA.2.2
  · exact lset_of c P.B.f S.f' S.es' tr.2.2.2.2.2.2.1 tr.2.2.2.2.2.2.2.2 d.L' t.abelian₂ n' hnS' hlatB spB.2.2

end Coordinates

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M hM V _ _ H r k P hdim hP`. Take `⟨S, ⟨c⟩⟩` from `CoordExist.exists_coord M hM H r k P hdim hP`. Use `⟨fun d t ht => term_over hM c hP d t ht, ?_⟩` and prove the remaining obligations. Introduce `d d' t t' ht ht' hA hB hio`. Take `⟨-, hdA, hdB⟩` from `term_over hM c hP d t ht`.

Take `⟨-, hdA', hdB'⟩` from `term_over hM c hP d' t' ht'`. Establish `h1 : d.L = d'.L` using `SetLike.coe_injective (by rw [hdA, hdA', hA])`. Establish `h2 : d.L' = d'.L'` using `SetLike.coe_injective (by rw [hdB, hdB', hB])`. Establish `h3 : d.io = d'.io`. Consider the cases of `hs : M.split with`.

Consider the case `none => rw [d.io_L hs, d'.io_L hs]`. Consider the case `some g`. Establish `e1` using `ht`. Establish `e2` using `ht'`. Unfold `IsTermOver at e1 e2`.

Rewrite using `[← (e1.2.2.2.2 g hs).2, ← (e2.2.2.2.2 g hs).2]`. Conclude with `hio g hs`. Break down `d with ⟨L1, L1', hL1, hL1', io1, hio1⟩` into its components or cases. Break down `d' with ⟨L2, L2', hL2, hL2', io2, hio2⟩` into its components or cases. Simplify using `only at h1 h2 h3`.

Substitute `h1 h2 h3` using the available equality. Both sides reduce to the same expression.
-/
theorem datum_of_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → (∀ (d : Datum P) (t : Term V M r), IsTermOver P d t → H.IsTerm t ∧ (d.L : Set (H.Wb P.A.f)) = H.Lset t.abelian₂ P.A.f ∧ (d.L' : Set (H.Wb P.B.f)) = H.Lset t.abelian₂ P.B.f) ∧ ∀ (d d' : Datum P) (t t' : Term V M r), IsTermOver P d t → IsTermOver P d' t' → H.Lset t.abelian₂ P.A.f = H.Lset t'.abelian₂ P.A.f → H.Lset t.abelian₂ P.B.f = H.Lset t'.abelian₂ P.B.f → (∀ g, M.split = some g → H.iotaGraph g ⟨t.abelian₂, P.A.f, P.B.f, t.T, t.T'⟩ = H.iotaGraph g ⟨t'.abelian₂, P.A.f, P.B.f, t'.T, t'.T'⟩) → d = d' := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hdim hP
  obtain ⟨S, ⟨c⟩⟩ := CoordExist.exists_coord M hM H r k P hdim hP
  refine ⟨fun d t ht => term_over hM c hP d t ht, ?_⟩
  intro d d' t t' ht ht' hA hB hio
  obtain ⟨-, hdA, hdB⟩ := term_over hM c hP d t ht
  obtain ⟨-, hdA', hdB'⟩ := term_over hM c hP d' t' ht'
  have h1 : d.L = d'.L := SetLike.coe_injective (by rw [hdA, hdA', hA])
  have h2 : d.L' = d'.L' := SetLike.coe_injective (by rw [hdB, hdB', hB])
  have h3 : d.io = d'.io := by
    cases hs : M.split with
    | none => rw [d.io_L hs, d'.io_L hs]
    | some g =>
      have e1 := ht
      have e2 := ht'
      unfold IsTermOver at e1 e2
      rw [← (e1.2.2.2.2 g hs).2, ← (e2.2.2.2.2 g hs).2]
      exact hio g hs
  rcases d with ⟨L1, L1', hL1, hL1', io1, hio1⟩
  rcases d' with ⟨L2, L2', hL2, hL2', io2, hio2⟩
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

end GlobalTheory.LocOver.TermLat
