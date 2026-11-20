import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaAddSubMemPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStablePrismHomComp

open GlobalTheory.Prism GlobalTheory.BSP CategoryTheory

namespace GlobalTheory.BSP.PoUniv

variable {l : ℕ} {R : Type} [CommRing R]

def deltaLocus {A B : Type} [CommRing A] [CommRing B] (D : Delta l A) (D' : Delta l B) (c : A →+* B) :
    Subring A where
  carrier := {x | c (D.δ x) = D'.δ (c x)}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    simp [D.δ_mul, D'.δ_mul, ha, hb]
  one_mem' := by simp [D.δ_one, D'.δ_one]
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    simp [D.δ_add, D'.δ_add, ha, hb]
  zero_mem' := by simp [D.δ_zero, D'.δ_zero]
  neg_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    have e1 := congrArg c (D.δ_add a (-a))
    have e2 := D'.δ_add (c a) (-c a)
    rw [add_neg_cancel, D.δ_zero] at e1
    rw [add_neg_cancel, D'.δ_zero] at e2
    simp only [map_zero, map_sub, map_add, map_sum, map_mul, map_pow, map_natCast, map_neg, ha] at e1 ⊢
    linear_combination e2 - e1

open CategoryTheory in
/- English proof (translation)
Establish `hw : CommRingCat.ofHom f ≫ CommRingCat.ofHom u = CommRingCat.ofHom g ≫ CommRingCat.ofHom v`. Rewrite using `[← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, huv]`. Conclude with `⟨(hP.desc (W := CommRingCat.of W) _ _ hw).hom, congrArg CommRingCat.Hom.hom (hP.inl_desc (W := CommRingCat.of W) _ _ hw), congrArg CommRingCat.Hom.hom (hP.inr_desc (W := CommRingCat.of W) _ _ hw)⟩`.
-/
private lemma exists_ringHom_of_isPushout {A X Y P W : Type} [CommRing A] [CommRing X]
    [CommRing Y] [CommRing P] [CommRing W] {f : A →+* X} {g : A →+* Y} {i : X →+* P}
    {j : Y →+* P}
    (hP : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom i)
      (CommRingCat.ofHom j)) (u : X →+* W) (v : Y →+* W) (huv : u.comp f = v.comp g) :
    ∃ w : P →+* W, w.comp i = u ∧ w.comp j = v := by
  have hw : CommRingCat.ofHom f ≫ CommRingCat.ofHom u =
      CommRingCat.ofHom g ≫ CommRingCat.ofHom v := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, huv]
  exact ⟨(hP.desc (W := CommRingCat.of W) _ _ hw).hom,
    congrArg CommRingCat.Hom.hom (hP.inl_desc (W := CommRingCat.of W) _ _ hw),
    congrArg CommRingCat.Hom.hom (hP.inr_desc (W := CommRingCat.of W) _ _ hw)⟩

open CategoryTheory in
/- English proof (translation)
Establish `h` using `hP.hom_ext (W := CommRingCat.of W) (k := CommRingCat.ofHom u) (l := CommRingCat.ofHom v) (by rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hi]) (by rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hj])`. Conclude with `congrArg CommRingCat.Hom.hom h`.
-/
private lemma ringHom_eq_of_isPushout_of_comp_eq {A X Y P W : Type} [CommRing A] [CommRing X] [CommRing Y]
    [CommRing P] [CommRing W] {f : A →+* X} {g : A →+* Y} {i : X →+* P} {j : Y →+* P}
    (hP : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom i)
      (CommRingCat.ofHom j)) {u v : P →+* W} (hi : u.comp i = v.comp i)
    (hj : u.comp j = v.comp j) : u = v := by
  have h := hP.hom_ext (W := CommRingCat.of W) (k := CommRingCat.ofHom u)
    (l := CommRingCat.ofHom v) (by rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hi])
    (by rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hj])
  exact congrArg CommRingCat.Hom.hom h

open CategoryTheory in
/- English proof (translation)
Use `Ideal.Quotient.ringHom_ext ?_` and prove the remaining obligations. Use extensionality with `x`. Simplify using `only [RingHom.comp_apply, _root_.GlobalTheory.BSP.qmap_mk]`. Both sides reduce to the same expression.
-/
private lemma factorPow_comp_qmap_eq_qmap_comp_factorPow {l : ℕ} {R : Type} [CommRing R]
    {P P' : _root_.GlobalTheory.Prism.Obj l R} (f : _root_.GlobalTheory.Prism.Hom P P') {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI P') hle).comp
        (_root_.GlobalTheory.BSP.qmap f n) =
      (_root_.GlobalTheory.BSP.qmap f m).comp
        (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI P) hle) := by
  refine Ideal.Quotient.ringHom_ext ?_
  ext x
  simp only [RingHom.comp_apply, _root_.GlobalTheory.BSP.qmap_mk]
  rfl

open CategoryTheory in
/- English proof (translation)
Rewrite using `[IsHausdorff.eq_iff_smodEq (I := I)]`. Introduce `n`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]`. Conclude with `hxy n`.
-/
private lemma eq_of_forall_mk_pow_eq_of_isHausdorff {A : Type} [CommRing A] (I : Ideal A) [IsHausdorff I A]
    {x y : A} (hxy : ∀ n, Ideal.Quotient.mk (I ^ n) x = Ideal.Quotient.mk (I ^ n) y) :
    x = y := by
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
  exact hxy n

open CategoryTheory in
/- English proof (translation)
Establish `hcomm : i.comp f = j.comp g` using `congrArg CommRingCat.Hom.hom hP.w`. Take `⟨r, hr1, hr2⟩` from `exists_ringHom_of_isPushout hP (i.codRestrict T hi) (j.codRestrict T hj) (by`. Use extensionality with `z`. Conclude with `RingHom.congr_fun hcomm z)`. Establish `hid : T.subtype.comp r = RingHom.id P`.

Use `ringHom_eq_of_isPushout_of_comp_eq hP ?_ ?_` and prove the remaining obligations. Use extensionality with `x show ((r (i x) : T) : P) = i x`. Rewrite using `[← RingHom.comp_apply, hr1]`. Both sides reduce to the same expression. Use extensionality with `y show ((r (j y) : T) : P) = j y`.

Rewrite using `[← RingHom.comp_apply, hr2]`. Both sides reduce to the same expression. Establish `hp : T.subtype (r p) = p` using `RingHom.congr_fun hid p`. Rewrite using `[← hp]`. Conclude with `(r p).2`.
-/
private lemma mem_subring_of_isPushout_of_maps_mem {A X Y P : Type} [CommRing A] [CommRing X] [CommRing Y]
    [CommRing P] {f : A →+* X} {g : A →+* Y} {i : X →+* P} {j : Y →+* P}
    (hP : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom i)
      (CommRingCat.ofHom j)) (T : Subring P) (hi : ∀ x, i x ∈ T) (hj : ∀ y, j y ∈ T)
    (p : P) : p ∈ T := by
  have hcomm : i.comp f = j.comp g := congrArg CommRingCat.Hom.hom hP.w
  obtain ⟨r, hr1, hr2⟩ := exists_ringHom_of_isPushout hP (i.codRestrict T hi)
    (j.codRestrict T hj) (by
      ext z
      exact RingHom.congr_fun hcomm z)
  have hid : T.subtype.comp r = RingHom.id P := by
    refine ringHom_eq_of_isPushout_of_comp_eq hP ?_ ?_
    · ext x
      show ((r (i x) : T) : P) = i x
      rw [← RingHom.comp_apply, hr1]
      rfl
    · ext y
      show ((r (j y) : T) : P) = j y
      rw [← RingHom.comp_apply, hr2]
      rfl
  have hp : T.subtype (r p) = p := RingHom.congr_fun hid p
  rw [← hp]
  exact (r p).2

open CategoryTheory in

/- English proof (translation)
Use `haveI : IsAdicComplete (_root_.GlobalTheory.BSP.adI Q) Q.A := Q.complete`. Establish `hex : ∀ m, ∃ ψ : C'.A ⧸ _root_.GlobalTheory.BSP.adI C' ^ m →+* Q.A ⧸ _root_.GlobalTheory.BSP.adI Q ^ m, ψ.comp (_root_.GlobalTheory.BSP.qmap k' m) = _root_.GlobalTheory.BSP.qmap a m ∧ ψ.comp (_root_.GlobalTheory.BSP.qmap h' m) = _root_.GlobalTheory.BSP.qmap b m` using `fun m => exists_ringHom_of_isPushout (H.po m) _ _ (by`. Rewrite using `[← _root_.GlobalTheory.BSP.qmap_comp, ← _root_.GlobalTheory.BSP.qmap_comp, hab])`. Use `choose ψ hψa hψb using hex`. Establish `hψa' : ∀ m x, ψ m (Ideal.Quotient.mk _ (k'.f x)) = Ideal.Quotient.mk _ (a.f x)`.

Introduce `m x`. Establish `hx` using `RingHom.congr_fun (hψa m) (Ideal.Quotient.mk _ x)`. Simplify `hx` using `[_root_.GlobalTheory.BSP.qmap_mk]`. Establish `hψb' : ∀ m y, ψ m (Ideal.Quotient.mk _ (h'.f y)) = Ideal.Quotient.mk _ (b.f y)`. Introduce `m y`.

Establish `hy` using `RingHom.congr_fun (hψb m) (Ideal.Quotient.mk _ y)`. Simplify `hy` using `[_root_.GlobalTheory.BSP.qmap_mk]`. Establish `hcompat : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI Q) hle).comp ((ψ n).comp (Ideal.Quotient.mk _)) = (ψ m).comp (Ideal.Quotient.mk _)`. Introduce `m n hle`. Establish `key : (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI Q) hle).comp (ψ n) = (ψ m).comp (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI C') hle)`.

Use `ringHom_eq_of_isPushout_of_comp_eq (H.po n) ?_ ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_assoc, hψa, RingHom.comp_assoc, factorPow_comp_qmap_eq_qmap_comp_factorPow, factorPow_comp_qmap_eq_qmap_comp_factorPow, ← RingHom.comp_assoc, hψa]`. Rewrite using `[RingHom.comp_assoc, hψb, RingHom.comp_assoc, factorPow_comp_qmap_eq_qmap_comp_factorPow, factorPow_comp_qmap_eq_qmap_comp_factorPow, ← RingHom.comp_assoc, hψb]`. Rewrite using `[← RingHom.comp_assoc, key, RingHom.comp_assoc]`. Use `congr 1`.

Take `⟨c0, hc0⟩ : ∃ c0 : C'.A →+* Q.A, ∀ n x, Ideal.Quotient.mk (_root_.GlobalTheory.BSP.adI Q ^ n) (c0 x) = ψ n (Ideal.Quotient.mk _ x)` from `⟨_, fun n x => IsAdicComplete.mk_liftRingHom _ _ hcompat n x⟩`. Establish `hmap : ∀ n z, z ∈ _root_.GlobalTheory.BSP.adI C' ^ n → c0 z ∈ _root_.GlobalTheory.BSP.adI Q ^ n`. Introduce `n z hz`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, hc0, Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero]`. Establish `hk : ∀ x, c0 (k'.f x) = a.f x` using `fun x => eq_of_forall_mk_pow_eq_of_isHausdorff (_root_.GlobalTheory.BSP.adI Q) fun n => by rw [hc0, hψa']`.

Establish `hh : ∀ y, c0 (h'.f y) = b.f y` using `fun y => eq_of_forall_mk_pow_eq_of_isHausdorff (_root_.GlobalTheory.BSP.adI Q) fun n => by rw [hc0, hψb']`. Establish `hδ : ∀ x, c0 (C'.D.δ x) = Q.D.δ (c0 x)`. Introduce `x`. Establish `hS : ∀ n, ∃ s ∈ _root_.GlobalTheory.BSP.PoUniv.deltaLocus C'.D Q.D c0, x - s ∈ _root_.GlobalTheory.BSP.adI C' ^ n`. Introduce `n`.

Establish `hT` using `mem_subring_of_isPushout_of_maps_mem (H.po n) ((_root_.GlobalTheory.BSP.PoUniv.deltaLocus C'.D Q.D c0).map (Ideal.Quotient.mk (_root_.GlobalTheory.BSP.adI C' ^ n))) (fun y => by`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Rewrite using `[_root_.GlobalTheory.BSP.qmap_mk]`. Use `Subring.mem_map.mpr ⟨_, ?_, rfl⟩` and prove the remaining obligations. Use `show c0 (C'.D.δ (k'.f y)) = Q.D.δ (c0 (k'.f y))`.

Rewrite using `[← k'.f_δ, hk, hk, a.f_δ])`. Use the proof step `(fun y => by`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Rewrite using `[_root_.GlobalTheory.BSP.qmap_mk]`. Use `Subring.mem_map.mpr ⟨_, ?_, rfl⟩` and prove the remaining obligations.

Use `show c0 (C'.D.δ (h'.f y)) = Q.D.δ (c0 (h'.f y))`. Rewrite using `[← h'.f_δ, hh, hh, b.f_δ])`. Use the proof step `(Ideal.Quotient.mk _ x)`. Take `⟨s, hs, hsx⟩` from `Subring.mem_map.mp hT`. Conclude with `⟨s, hs, Ideal.Quotient.eq.mp hsx.symm⟩`.

Use `sub_eq_zero.mp (eq_of_forall_mk_pow_eq_of_isHausdorff (_root_.GlobalTheory.BSP.adI Q) fun n => ?_)` and prove the remaining obligations. Rewrite using `[map_zero, Ideal.Quotient.eq_zero_iff_mem]`. Take `⟨s, hs, hxs⟩` from `hS (n + 1)`. Establish `hs' : c0 (C'.D.δ s) = Q.D.δ (c0 s)` using `hs`. Establish `hlC : (l : C'.A) ∈ _root_.GlobalTheory.BSP.adI C'` using `Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)`.

Establish `hlQ : (l : Q.A) ∈ _root_.GlobalTheory.BSP.adI Q` using `Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)`. Establish `h1` using `_root_.GlobalTheory.BSP.delta_add_sub_mem_pow l C'.A C'.D _ hlC n s (x - s) hxs`. Establish `h2` using `_root_.GlobalTheory.BSP.delta_add_sub_mem_pow l Q.A Q.D _ hlQ n (c0 s) (c0 (x - s)) (hmap _ _ hxs)`. Rewrite `h1` using `[add_sub_cancel]`. Rewrite `h2` using `[← map_add, add_sub_cancel]`.

Establish `h3` using `hmap n _ h1`. Rewrite `h3` using `[map_sub, hs']`. Establish `h4` using `Ideal.sub_mem _ h3 h2`. Use `h4 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Establish `hI : ∀ z ∈ C'.I, c0 z ∈ Q.I`. Introduce `z hz`. Establish `hcb : c0.comp h'.f = b.f` using `RingHom.ext hh`. Establish `hz' : z ∈ Ideal.map h'.f B'.I`. Rewrite using `[_root_.GlobalTheory.Prism.Rigid.map_I_eq l R B' C' h']`.

Conclude with `hz`. Establish `hmem` using `Ideal.mem_map_of_mem c0 hz'`. Rewrite `hmem` using `[Ideal.map_map, hcb, _root_.GlobalTheory.Prism.Rigid.map_I_eq l R B' Q b]`. Then use the resulting hypothesis. Establish `hstr : ∀ (r : R) (z : C'.A), Ideal.Quotient.mk C'.I z = C'.str r → Ideal.Quotient.mk Q.I (c0 z) = Q.str r`. Introduce `r z hz`.

Take `⟨y, hy⟩` from `Ideal.Quotient.mk_surjective (B'.str r)`. Establish `h1` using `h'.f_str r y hy`. Establish `h2` using `b.f_str r y hy`. Rewrite using `[← h2, ← hh, Ideal.Quotient.eq, ← map_sub]`. Use `hI _ ?_` and prove the remaining obligations.

Rewrite using `[← Ideal.Quotient.eq, hz, h1]`. Set `c : _root_.GlobalTheory.Prism.Hom C' Q` to `⟨c0, hδ, hI, hstr⟩`. Establish `hcomm : c.comp k' = a ∧ c.comp h' = b` using `⟨_root_.GlobalTheory.Prism.Hom.ext' (RingHom.ext hk), _root_.GlobalTheory.Prism.Hom.ext' (RingHom.ext hh)⟩`. Use `⟨c, hcomm, fun c' hc' => ?_⟩` and prove the remaining obligations. Use `_root_.GlobalTheory.Prism.Hom.ext' (RingHom.ext fun x => eq_of_forall_mk_pow_eq_of_isHausdorff (_root_.GlobalTheory.BSP.adI Q) fun n => ?_)` and prove the remaining obligations.

Establish `hq : _root_.GlobalTheory.BSP.qmap c' n = _root_.GlobalTheory.BSP.qmap c n`. Use `ringHom_eq_of_isPushout_of_comp_eq (H.po n) ?_ ?_` and prove the remaining obligations. Rewrite using `[← _root_.GlobalTheory.BSP.qmap_comp, ← _root_.GlobalTheory.BSP.qmap_comp, hc'.1, hcomm.1]`. Rewrite using `[← _root_.GlobalTheory.BSP.qmap_comp, ← _root_.GlobalTheory.BSP.qmap_comp, hc'.2, hcomm.2]`. Establish `hx` using `RingHom.congr_fun hq (Ideal.Quotient.mk _ x)`.

Simplify `hx` using `only [_root_.GlobalTheory.BSP.qmap_mk]`.
-/
theorem _root_.GlobalTheory.BSP.PoUniv.isPO_univ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R]
    (B C B' C' : _root_.GlobalTheory.Prism.Obj l R) (h : _root_.GlobalTheory.Prism.Hom B C)
    (k : _root_.GlobalTheory.Prism.Hom B B') (k' : _root_.GlobalTheory.Prism.Hom C C') (h' : _root_.GlobalTheory.Prism.Hom B' C')
    (H : _root_.GlobalTheory.BSP.IsPO h k k' h') (Q : _root_.GlobalTheory.Prism.Obj l R)
    (a : _root_.GlobalTheory.Prism.Hom C Q) (b : _root_.GlobalTheory.Prism.Hom B' Q)
    (hab : a.comp h = b.comp k) :
    ∃! c : _root_.GlobalTheory.Prism.Hom C' Q,
      c.comp k' = a ∧ c.comp h' = b := by
  haveI : IsAdicComplete (_root_.GlobalTheory.BSP.adI Q) Q.A :=
    Q.complete
  have hex : ∀ m, ∃ ψ : C'.A ⧸ _root_.GlobalTheory.BSP.adI C' ^ m →+*
      Q.A ⧸ _root_.GlobalTheory.BSP.adI Q ^ m,
      ψ.comp (_root_.GlobalTheory.BSP.qmap k' m) = _root_.GlobalTheory.BSP.qmap a m ∧
      ψ.comp (_root_.GlobalTheory.BSP.qmap h' m) = _root_.GlobalTheory.BSP.qmap b m := fun m =>
    exists_ringHom_of_isPushout (H.po m) _ _ (by
      rw [← _root_.GlobalTheory.BSP.qmap_comp, ← _root_.GlobalTheory.BSP.qmap_comp, hab])
  choose ψ hψa hψb using hex
  have hψa' : ∀ m x, ψ m (Ideal.Quotient.mk _ (k'.f x)) =
      Ideal.Quotient.mk _ (a.f x) := by
    intro m x
    have hx := RingHom.congr_fun (hψa m) (Ideal.Quotient.mk _ x)
    simpa [_root_.GlobalTheory.BSP.qmap_mk] using hx
  have hψb' : ∀ m y, ψ m (Ideal.Quotient.mk _ (h'.f y)) =
      Ideal.Quotient.mk _ (b.f y) := by
    intro m y
    have hy := RingHom.congr_fun (hψb m) (Ideal.Quotient.mk _ y)
    simpa [_root_.GlobalTheory.BSP.qmap_mk] using hy
  have hcompat : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI Q) hle).comp
        ((ψ n).comp (Ideal.Quotient.mk _)) = (ψ m).comp (Ideal.Quotient.mk _) := by
    intro m n hle
    have key : (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI Q) hle).comp (ψ n) =
        (ψ m).comp (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI C') hle) := by
      refine ringHom_eq_of_isPushout_of_comp_eq (H.po n) ?_ ?_
      · rw [RingHom.comp_assoc, hψa, RingHom.comp_assoc, factorPow_comp_qmap_eq_qmap_comp_factorPow,
          factorPow_comp_qmap_eq_qmap_comp_factorPow, ← RingHom.comp_assoc, hψa]
      · rw [RingHom.comp_assoc, hψb, RingHom.comp_assoc, factorPow_comp_qmap_eq_qmap_comp_factorPow,
          factorPow_comp_qmap_eq_qmap_comp_factorPow, ← RingHom.comp_assoc, hψb]
    rw [← RingHom.comp_assoc, key, RingHom.comp_assoc]
    congr 1
  obtain ⟨c0, hc0⟩ : ∃ c0 : C'.A →+* Q.A, ∀ n x,
      Ideal.Quotient.mk (_root_.GlobalTheory.BSP.adI Q ^ n) (c0 x) = ψ n (Ideal.Quotient.mk _ x) :=
    ⟨_, fun n x => IsAdicComplete.mk_liftRingHom _ _ hcompat n x⟩
  have hmap : ∀ n z, z ∈ _root_.GlobalTheory.BSP.adI C' ^ n →
      c0 z ∈ _root_.GlobalTheory.BSP.adI Q ^ n := by
    intro n z hz
    rw [← Ideal.Quotient.eq_zero_iff_mem, hc0, Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero]
  have hk : ∀ x, c0 (k'.f x) = a.f x := fun x =>
    eq_of_forall_mk_pow_eq_of_isHausdorff (_root_.GlobalTheory.BSP.adI Q) fun n => by rw [hc0, hψa']
  have hh : ∀ y, c0 (h'.f y) = b.f y := fun y =>
    eq_of_forall_mk_pow_eq_of_isHausdorff (_root_.GlobalTheory.BSP.adI Q) fun n => by rw [hc0, hψb']
  have hδ : ∀ x, c0 (C'.D.δ x) =
      Q.D.δ (c0 x) := by
    intro x
    have hS : ∀ n, ∃ s ∈ _root_.GlobalTheory.BSP.PoUniv.deltaLocus C'.D Q.D c0,
        x - s ∈ _root_.GlobalTheory.BSP.adI C' ^ n := by
      intro n
      have hT := mem_subring_of_isPushout_of_maps_mem (H.po n)
        ((_root_.GlobalTheory.BSP.PoUniv.deltaLocus C'.D Q.D c0).map
          (Ideal.Quotient.mk (_root_.GlobalTheory.BSP.adI C' ^ n)))
        (fun y => by
          obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
          rw [_root_.GlobalTheory.BSP.qmap_mk]
          refine Subring.mem_map.mpr ⟨_, ?_, rfl⟩
          show c0 (C'.D.δ (k'.f y)) =
            Q.D.δ (c0 (k'.f y))
          rw [← k'.f_δ, hk, hk, a.f_δ])
        (fun y => by
          obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
          rw [_root_.GlobalTheory.BSP.qmap_mk]
          refine Subring.mem_map.mpr ⟨_, ?_, rfl⟩
          show c0 (C'.D.δ (h'.f y)) =
            Q.D.δ (c0 (h'.f y))
          rw [← h'.f_δ, hh, hh, b.f_δ])
        (Ideal.Quotient.mk _ x)
      obtain ⟨s, hs, hsx⟩ := Subring.mem_map.mp hT
      exact ⟨s, hs, Ideal.Quotient.eq.mp hsx.symm⟩
    refine sub_eq_zero.mp (eq_of_forall_mk_pow_eq_of_isHausdorff (_root_.GlobalTheory.BSP.adI Q) fun n => ?_)
    rw [map_zero, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨s, hs, hxs⟩ := hS (n + 1)
    have hs' : c0 (C'.D.δ s) =
        Q.D.δ (c0 s) := hs
    have hlC : (l : C'.A) ∈ _root_.GlobalTheory.BSP.adI C' :=
      Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    have hlQ : (l : Q.A) ∈ _root_.GlobalTheory.BSP.adI Q :=
      Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    have h1 := _root_.GlobalTheory.BSP.delta_add_sub_mem_pow l C'.A C'.D _ hlC n s
      (x - s) hxs
    have h2 := _root_.GlobalTheory.BSP.delta_add_sub_mem_pow l Q.A Q.D _ hlQ n (c0 s)
      (c0 (x - s)) (hmap _ _ hxs)
    rw [add_sub_cancel] at h1
    rw [← map_add, add_sub_cancel] at h2
    have h3 := hmap n _ h1
    rw [map_sub, hs'] at h3
    have h4 := Ideal.sub_mem _ h3 h2
    convert h4 using 1
    ring
  have hI : ∀ z ∈ C'.I, c0 z ∈ Q.I := by
    intro z hz
    have hcb : c0.comp h'.f = b.f := RingHom.ext hh
    have hz' : z ∈ Ideal.map h'.f B'.I := by
      rw [_root_.GlobalTheory.Prism.Rigid.map_I_eq l R B' C' h']
      exact hz
    have hmem := Ideal.mem_map_of_mem c0 hz'
    rwa [Ideal.map_map, hcb, _root_.GlobalTheory.Prism.Rigid.map_I_eq l R B' Q b] at hmem
  have hstr : ∀ (r : R) (z : C'.A),
      Ideal.Quotient.mk C'.I z = C'.str r →
      Ideal.Quotient.mk Q.I (c0 z) = Q.str r := by
    intro r z hz
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (B'.str r)
    have h1 := h'.f_str r y hy
    have h2 := b.f_str r y hy
    rw [← h2, ← hh, Ideal.Quotient.eq, ← map_sub]
    refine hI _ ?_
    rw [← Ideal.Quotient.eq, hz, h1]
  let c : _root_.GlobalTheory.Prism.Hom C' Q := ⟨c0, hδ, hI, hstr⟩
  have hcomm : c.comp k' = a ∧ c.comp h' = b :=
    ⟨_root_.GlobalTheory.Prism.Hom.ext' (RingHom.ext hk),
      _root_.GlobalTheory.Prism.Hom.ext' (RingHom.ext hh)⟩
  refine ⟨c, hcomm, fun c' hc' => ?_⟩
  refine _root_.GlobalTheory.Prism.Hom.ext' (RingHom.ext fun x =>
    eq_of_forall_mk_pow_eq_of_isHausdorff (_root_.GlobalTheory.BSP.adI Q) fun n => ?_)
  have hq : _root_.GlobalTheory.BSP.qmap c' n = _root_.GlobalTheory.BSP.qmap c n := by
    refine ringHom_eq_of_isPushout_of_comp_eq (H.po n) ?_ ?_
    · rw [← _root_.GlobalTheory.BSP.qmap_comp, ← _root_.GlobalTheory.BSP.qmap_comp, hc'.1, hcomm.1]
    · rw [← _root_.GlobalTheory.BSP.qmap_comp, ← _root_.GlobalTheory.BSP.qmap_comp, hc'.2, hcomm.2]
  have hx := RingHom.congr_fun hq (Ideal.Quotient.mk _ x)
  simpa only [_root_.GlobalTheory.BSP.qmap_mk] using hx

end GlobalTheory.BSP.PoUniv
