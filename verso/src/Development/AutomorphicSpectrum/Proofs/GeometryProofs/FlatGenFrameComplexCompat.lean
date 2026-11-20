import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsConstMul
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FixedByAutomorphismsMemFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramedPointDescendsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatGenFrameIndependentStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

section Comb

variable {S : Scheme.{0}} {R : Type} [CommRing R]

/- English proof (translation)
Apply `RingHom.ext` to reduce the goal to its premises. Introduce `x`. Apply the tactic sequence `apply TrivSqZeroExt.ext <;> simp [GlobalTheory.CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem epsMul_zero_eq : GlobalTheory.CompanionTheory.Ar.epsMul (0 : R) =
    (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  apply RingHom.ext
  intro x
  apply TrivSqZeroExt.ext <;> simp [GlobalTheory.CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Apply `RingHom.ext` to reduce the goal to its premises. Introduce `x`. Apply the tactic sequence `apply TrivSqZeroExt.ext <;> simp [GlobalTheory.CompanionTheory.Ar.epsMul]`.
-/
theorem epsMul_one_eq : GlobalTheory.CompanionTheory.Ar.epsMul (1 : R) = RingHom.id (DualNumber R) := by
  apply RingHom.ext
  intro x
  apply TrivSqZeroExt.ext <;> simp [GlobalTheory.CompanionTheory.Ar.epsMul]

/- English proof (translation)
Conclude with `MonObj.comp_one f`.
-/
theorem comp_one_over {Y Z M : Over S} [GrpObj M] (f : Y ⟶ Z) : f ≫ (1 : Z ⟶ M) = 1 := by
  exact MonObj.comp_one f

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro u j`. Conclude with `j.elim0`. Consider the case `succ n ih`.

Introduce `u j hu`. Rewrite using `[List.ofFn_succ, List.prod_cons]`. Distinguish the cases in `hj : j = 0`. Substitute `hj` using the available equality. Establish `h1 : (List.ofFn fun i : Fin n => u i.succ).prod = 1` using `List.prod_eq_one fun x hx => by`.

Simplify using `only [List.mem_ofFn] at hx`. Take `⟨i, rfl⟩` from `hx`. Conclude with `hu _ (Fin.succ_ne_zero i)`. Rewrite using `[h1, _root_.mul_one]`. Take `⟨j', rfl⟩` from `Fin.exists_succ_eq.2 hj`.

Rewrite using `[hu 0 (Fin.succ_ne_zero j').symm, _root_.one_mul]`. Conclude with `ih (fun i => u i.succ) j' fun i hi => hu _ fun h => hi (Fin.succ_injective _ h)`.
-/
theorem prod_ofFn_single {M : Type*} [Monoid M] : ∀ {n : ℕ} (u : Fin n → M) (j : Fin n),
    (∀ i, i ≠ j → u i = 1) → (List.ofFn u).prod = u j := by
  intro n
  induction n with
  | zero => intro u j; exact j.elim0
  | succ n ih =>
    intro u j hu
    rw [List.ofFn_succ, List.prod_cons]
    by_cases hj : j = 0
    · subst hj
      have h1 : (List.ofFn fun i : Fin n => u i.succ).prod = 1 := List.prod_eq_one fun x hx => by
        simp only [List.mem_ofFn] at hx
        obtain ⟨i, rfl⟩ := hx
        exact hu _ (Fin.succ_ne_zero i)
      rw [h1, _root_.mul_one]
    · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj
      rw [hu 0 (Fin.succ_ne_zero j').symm, _root_.one_mul]
      exact ih (fun i => u i.succ) j' fun i hi => hu _ fun h => hi (Fin.succ_injective _ h)

/- English proof (translation)
Use `⟨fun i => if i = j then w i else 1, fun i => ?_, ?_⟩` and prove the remaining obligations. Use `show Over.Hom.left (if i = j then w i else 1) = _`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[epsMul_one_eq, spMap]`.

Rewrite using `[if_neg hij, Pi.single_eq_of_ne hij, epsMul_zero_eq]`. Establish `h1` using `comp_one_over (M := G) (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R)))) rfl : GlobalTheory.CompanionTheory.Ar.epsAt x ⟶ Over.mk x)`. Rewrite using `[← h1, Over.comp_left, ← hw i]`. Simplify using `[spMap]`. Rewrite using `[prod_ofFn_single _ j fun i hi => if_neg hi, if_pos rfl]`.
-/
theorem isComb_single {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {n : ℕ} (w : Fin n → (epsAt x ⟶ G))
    (hw : ∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt G x (w i)) (j : Fin n) : GlobalTheory.CompanionTheory.Ar.Fl.IsComb (Pi.single j 1) w (w j) := by
  classical
  refine ⟨fun i => if i = j then w i else 1, fun i => ?_, ?_⟩
  · show Over.Hom.left (if i = j then w i else 1) = _
    by_cases hij : i = j
    · subst hij
      simp [epsMul_one_eq, spMap]
    · rw [if_neg hij, Pi.single_eq_of_ne hij, epsMul_zero_eq]
      have h1 := comp_one_over (M := G)
        (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R)))) rfl :
          GlobalTheory.CompanionTheory.Ar.epsAt x ⟶ Over.mk x)
      rw [← h1, Over.comp_left, ← hw i]
      simp [spMap]
  · rw [prod_ofFn_single _ j fun i hi => if_neg hi, if_pos rfl]

end Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

/- English proof (translation)
Establish `hv` using `h.2.2.1`. Establish `hw` using `h.2.2.2`. Establish `hv'` using `h'.2.2.1`. Establish `hw'` using `h'.2.2.2`. Establish `hvw' : IsFramed U τ β y v w'` using `⟨h.1, h.2.1, hv, hw'⟩`.

Set `A : Matrix (Fin D.p) (Fin D.p) F` to `fun a => (hv.2 (v' a) (hv'.1 a)).exists.choose`. Establish `hA : ∀ a, IsComb (A a) v (v' a)` using `fun a => (hv.2 (v' a) (hv'.1 a)).exists.choose_spec`. Set `B : Matrix (Fin D.q) (Fin D.q) F` to `fun b => (hw.2 (w' b) (hw'.1 b)).exists.choose`. Establish `hB : ∀ b, IsComb (B b) w (w' b)` using `fun b => (hw.2 (w' b) (hw'.1 b)).exists.choose_spec`. Establish `hIv : ∀ a, IsComb ((1 : Matrix (Fin D.p) (Fin D.p) F) a) v (v a)` using `fun a => by`.

Establish `h1 : (1 : Matrix (Fin D.p) (Fin D.p) F) a = Pi.single a 1`. Use function extensionality and compare the values at `fun b => Matrix.one_eq_pi_single`. Rewrite using `[h1]`. Conclude with `isComb_single v (fun i => (hv.1 i).1) a`. Establish `hIw : ∀ b, IsComb ((1 : Matrix (Fin D.q) (Fin D.q) F) b) w' (w' b)` using `fun b => by`.

Establish `h1 : (1 : Matrix (Fin D.q) (Fin D.q) F) b = Pi.single b 1`. Use function extensionality and compare the values at `fun b' => Matrix.one_eq_pi_single`. Rewrite using `[h1]`. Conclude with `isComb_single w' (fun i => (hw'.1 i).1) b`. Establish `e1` using `hφ.chg F β y v w v w' 1 B h hvw' hIv hB`.

Establish `e1₀` using `hφ₀.chg F β y v w v w' 1 B h hvw' hIv hB`. Establish `e2` using `hφ.chg F β y v w' v' w' A 1 hvw' h' hA hIw`. Establish `e2₀` using `hφ₀.chg F β y v w' v' w' A 1 hvw' h' hA hIw`. Rewrite `e1`, `e1₀`, `e2`, `e2₀` using `[Matrix.det_one, _root_.mul_one]`. Establish `hBne : B.det ≠ 0`.

Introduce `h0`. Rewrite `e1` using `[h0, mul_zero]`. Conclude with `hφ.ne F β y v w' hvw' e1`. Apply `mul_right_cancel₀ hBne` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eq_mul_of_frames {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ φ₀ : FrameFn Xo c} (hφ : IsLineFn U τ φ)
    (hφ₀ : IsLineFn U τ φ₀) {F : Type} [Field F] {β : c.F →+* F} {y : Sp F ⟶ Xo.XF c} {v v' : Vecs y D.p}
    {w w' : Vecs y D.q} (h : IsFramed U τ β y v w) (h' : IsFramed U τ β y v' w') {b : F}
    (hb : φ F y v' w' = b * φ₀ F y v' w') : φ F y v w = b * φ₀ F y v w := by
  have hv := h.2.2.1
  have hw := h.2.2.2
  have hv' := h'.2.2.1
  have hw' := h'.2.2.2
  have hvw' : IsFramed U τ β y v w' := ⟨h.1, h.2.1, hv, hw'⟩
  let A : Matrix (Fin D.p) (Fin D.p) F := fun a => (hv.2 (v' a) (hv'.1 a)).exists.choose
  have hA : ∀ a, IsComb (A a) v (v' a) := fun a => (hv.2 (v' a) (hv'.1 a)).exists.choose_spec
  let B : Matrix (Fin D.q) (Fin D.q) F := fun b => (hw.2 (w' b) (hw'.1 b)).exists.choose
  have hB : ∀ b, IsComb (B b) w (w' b) := fun b => (hw.2 (w' b) (hw'.1 b)).exists.choose_spec
  have hIv : ∀ a, IsComb ((1 : Matrix (Fin D.p) (Fin D.p) F) a) v (v a) := fun a => by
    have h1 : (1 : Matrix (Fin D.p) (Fin D.p) F) a = Pi.single a 1 :=
      funext fun b => Matrix.one_eq_pi_single
    rw [h1]
    exact isComb_single v (fun i => (hv.1 i).1) a
  have hIw : ∀ b, IsComb ((1 : Matrix (Fin D.q) (Fin D.q) F) b) w' (w' b) := fun b => by
    have h1 : (1 : Matrix (Fin D.q) (Fin D.q) F) b = Pi.single b 1 :=
      funext fun b' => Matrix.one_eq_pi_single
    rw [h1]
    exact isComb_single w' (fun i => (hw'.1 i).1) b
  have e1 := hφ.chg F β y v w v w' 1 B h hvw' hIv hB
  have e1₀ := hφ₀.chg F β y v w v w' 1 B h hvw' hIv hB
  have e2 := hφ.chg F β y v w' v' w' A 1 hvw' h' hA hIw
  have e2₀ := hφ₀.chg F β y v w' v' w' A 1 hvw' h' hA hIw
  rw [Matrix.det_one, _root_.mul_one] at e1 e1₀ e2 e2₀
  have hBne : B.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at e1
    exact hφ.ne F β y v w' hvw' e1
  apply mul_right_cancel₀ hBne
  calc φ F y v w * B.det = φ F y v w' := e1.symm
    _ = φ F y v' w' * A.det := e2.symm
    _ = b * (φ₀ F y v' w' * A.det) := by rw [hb, _root_.mul_assoc]
    _ = b * φ₀ F y v w * B.det := by rw [e2₀, e1₀, _root_.mul_assoc]

/- English proof (translation)
Take `⟨v', w', hfr, hv', hw'⟩` from `hb ℂ j`. Establish `hfr' : IsFramed U τ (algebraMap c.F ℂ) (spMap j ≫ y₀) v' w'`. Rewrite using `[← hj]`. Conclude with `hfr`. Establish `e` using `ha _ v' w' hfr'`.

Rewrite `e` using `[hφ.nat k ℂ j β₀ y₀ v₀ w₀ _ v' w' h₀ rfl hv' hw', hφ₀.nat k ℂ j β₀ y₀ v₀ w₀ _ v' w' h₀ rfl hv' hw']`. Conclude with `e`.
-/
theorem ratio_at {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ φ₀ : FrameFn Xo c} (hφ : IsLineFn U τ φ)
    (hφ₀ : IsLineFn U τ φ₀) {a : ℂ}
    (ha : ∀ y v w, IsFramed U τ (algebraMap c.F ℂ) y v w → φ ℂ y v w = a * φ₀ ℂ y v w)
    {k : Type} [Field k] {β₀ : c.F →+* k} {y₀ : Sp k ⟶ Xo.XF c} {v₀ : Vecs y₀ D.p} {w₀ : Vecs y₀ D.q}
    (h₀ : IsFramed U τ β₀ y₀ v₀ w₀)
    (hb : ∀ (F' : Type) [Field F'] (f' : k →+* F'), ∃ (v' : Vecs (spMap f' ≫ y₀) D.p)
      (w' : Vecs (spMap f' ≫ y₀) D.q), IsFramed U τ (f'.comp β₀) (spMap f' ≫ y₀) v' w' ∧
        (∀ a, (v' a).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f') ≫ (v₀ a).left) ∧
        ∀ b, (w' b).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f') ≫ (w₀ b).left)
    (j : k →+* ℂ) (hj : j.comp β₀ = algebraMap c.F ℂ) : j (φ k y₀ v₀ w₀) = a * j (φ₀ k y₀ v₀ w₀) := by
  obtain ⟨v', w', hfr, hv', hw'⟩ := hb ℂ j
  have hfr' : IsFramed U τ (algebraMap c.F ℂ) (spMap j ≫ y₀) v' w' := by
    rw [← hj]
    exact hfr
  have e := ha _ v' w' hfr'
  rw [hφ.nat k ℂ j β₀ y₀ v₀ w₀ _ v' w' h₀ rfl hv' hw',
    hφ₀.nat k ℂ j β₀ y₀ v₀ w₀ _ v' w' h₀ rfl hv' hw'] at e
  exact e

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c U τ φ φ₀ g ty FU i hty hφ hφ₀ hper`. Take `⟨a, ha⟩` from `GlobalTheory.T.flat_gen_frame_independent E H D l Xo c U τ φ φ₀ g ty FU i hty hφ hφ₀ hper`. Establish `hL` using `hφ.line`. Establish `hL₀` using `hφ₀.line`. Distinguish the cases in `hex : ∃ (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q), IsFramed U τ (algebraMap c.F ℂ) y v w`.

Take `⟨y1, v1, w1, h1⟩` from `hex`. Take `⟨k, _, β₀, y₀, v₀, w₀, f, j, h₀, -, hj, -, hb⟩` from `GlobalTheory.T.framed_point_descends E H D l Xo c U τ ℂ (algebraMap c.F ℂ) y1 v1 w1 h1`. Establish `hr` using `ratio_at hL hL₀ ha h₀ hb j hj`. Establish `hne₀ : j (φ₀ k y₀ v₀ w₀) ≠ 0` using `(map_ne_zero j).2 (hL₀.ne k β₀ y₀ v₀ w₀ h₀)`. Establish `hfix : ∀ σ' : ℂ ≃+* ℂ, (∀ x ∈ c.F, σ' x = x) → σ' a = a`.

Introduce `σ' hσ'`. Establish `hj' : (σ'.toRingHom.comp j).comp β₀ = algebraMap c.F ℂ`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Establish `hx` using `RingHom.congr_fun hj x`. Simplify using `only [RingHom.comp_apply] at hx ⊢`.

Rewrite using `[hx]`. Conclude with `hσ' _ x.2`. Establish `hr'` using `ratio_at hL hL₀ ha h₀ hb _ hj'`. Simplify using `only [RingHom.comp_apply] at hr'`. Rewrite `hr'` using `[hr, map_mul]`.

Conclude with `mul_right_cancel₀ ((map_ne_zero _).2 hne₀) hr'`. Establish `haF : a ∈ c.F` using `GlobalTheory.T.fixed_by_automorphisms_mem_field c.F a c.fin hfix`. Use `⟨⟨a, haF⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Establish `ha0 : a = 0` using `congrArg Subtype.val h0`.

Apply `hL.ne k β₀ y₀ v₀ w₀ h₀` to reduce the goal to its premises. Apply `j.injective` to reduce the goal to its premises. Rewrite using `[hr, map_zero, ha0, zero_mul]`. Introduce `F _ β y v w hfr`. Take `⟨k', _, β₀', y₀', v₀', w₀', f', j', h₀', hfβ', hj'', hy', hb'⟩` from `GlobalTheory.T.framed_point_descends E H D l Xo c U τ F β y v w hfr`.

Substitute `hy'` using the available equality. Substitute `hfβ'` using the available equality. Establish `hr2` using `ratio_at hL hL₀ ha h₀' hb' j' hj''`. Establish `hk : φ k' y₀' v₀' w₀' = β₀' ⟨a, haF⟩ * φ₀ k' y₀' v₀' w₀'`. Apply `j'.injective` to reduce the goal to its premises.

Rewrite using `[map_mul, hr2]`. Use `congr 1`. Establish `hx` using `RingHom.congr_fun hj'' ⟨a, haF⟩`. Simplify using `only [RingHom.comp_apply] at hx`. Rewrite using `[hx]`.

Both sides reduce to the same expression. Take `⟨v', w', hfr', hv', hw'⟩` from `hb' F f'`. Establish `n1` using `hL.nat k' F f' β₀' y₀' v₀' w₀' _ v' w' h₀' rfl hv' hw'`. Establish `n2` using `hL₀.nat k' F f' β₀' y₀' v₀' w₀' _ v' w' h₀' rfl hv' hw'`. Use `eq_mul_of_frames hL hL₀ hfr hfr' (b := f' (β₀' ⟨a, haF⟩)) ?_` and prove the remaining obligations.

Rewrite using `[n1, n2, hk, map_mul]`. Use `⟨1, one_ne_zero, fun F _ β y v w hfr => ?_⟩` and prove the remaining obligations. It suffices to derive a contradiction. Take `⟨k, _, β₀, y₀, v₀, w₀, f, j, h₀, -, hj, -, hb⟩` from `GlobalTheory.T.framed_point_descends E H D l Xo c U τ F β y v w hfr`. Take `⟨v', w', hfr', -, -⟩` from `hb ℂ j`.

Rewrite `hfr'` using `[hj]`. Conclude with `hex ⟨_, v', w', hfr'⟩`.
-/
theorem flatGen_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ φ₀ : FrameFn Xo c) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty → IsFlatGen U τ φ FU i → IsFlatGen U τ φ₀ FU i → (∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U → ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) → ∃ a : c.F, a ≠ 0 ∧ ∀ (F : Type) [Field F] (β : c.F →+* F) y v w, IsFramed U τ β y v w → φ F y v w = β a * φ₀ F y v w := by
  intro E _ _ _ H D l Xo c U τ φ φ₀ g ty FU i hty hφ hφ₀ hper
  obtain ⟨a, ha⟩ := GlobalTheory.T.flat_gen_frame_independent E H D l Xo c U τ φ φ₀ g ty FU i hty hφ hφ₀ hper
  have hL := hφ.line
  have hL₀ := hφ₀.line
  by_cases hex : ∃ (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q),
      IsFramed U τ (algebraMap c.F ℂ) y v w
  · obtain ⟨y1, v1, w1, h1⟩ := hex
    obtain ⟨k, _, β₀, y₀, v₀, w₀, f, j, h₀, -, hj, -, hb⟩ :=
      GlobalTheory.T.framed_point_descends E H D l Xo c U τ ℂ (algebraMap c.F ℂ) y1 v1 w1 h1
    have hr := ratio_at hL hL₀ ha h₀ hb j hj
    have hne₀ : j (φ₀ k y₀ v₀ w₀) ≠ 0 := (map_ne_zero j).2 (hL₀.ne k β₀ y₀ v₀ w₀ h₀)
    have hfix : ∀ σ' : ℂ ≃+* ℂ, (∀ x ∈ c.F, σ' x = x) → σ' a = a := by
      intro σ' hσ'
      have hj' : (σ'.toRingHom.comp j).comp β₀ = algebraMap c.F ℂ := by
        refine RingHom.ext fun x => ?_
        have hx := RingHom.congr_fun hj x
        simp only [RingHom.comp_apply] at hx ⊢
        rw [hx]
        exact hσ' _ x.2
      have hr' := ratio_at hL hL₀ ha h₀ hb _ hj'
      simp only [RingHom.comp_apply] at hr'
      rw [hr, map_mul] at hr'
      exact mul_right_cancel₀ ((map_ne_zero _).2 hne₀) hr'
    have haF : a ∈ c.F := GlobalTheory.T.fixed_by_automorphisms_mem_field c.F a c.fin hfix
    refine ⟨⟨a, haF⟩, ?_, ?_⟩
    · intro h0
      have ha0 : a = 0 := congrArg Subtype.val h0
      apply hL.ne k β₀ y₀ v₀ w₀ h₀
      apply j.injective
      rw [hr, map_zero, ha0, zero_mul]
    · intro F _ β y v w hfr
      obtain ⟨k', _, β₀', y₀', v₀', w₀', f', j', h₀', hfβ', hj'', hy', hb'⟩ :=
        GlobalTheory.T.framed_point_descends E H D l Xo c U τ F β y v w hfr
      subst hy'
      subst hfβ'
      have hr2 := ratio_at hL hL₀ ha h₀' hb' j' hj''
      have hk : φ k' y₀' v₀' w₀' = β₀' ⟨a, haF⟩ * φ₀ k' y₀' v₀' w₀' := by
        apply j'.injective
        rw [map_mul, hr2]
        congr 1
        have hx := RingHom.congr_fun hj'' ⟨a, haF⟩
        simp only [RingHom.comp_apply] at hx
        rw [hx]
        rfl
      obtain ⟨v', w', hfr', hv', hw'⟩ := hb' F f'
      have n1 := hL.nat k' F f' β₀' y₀' v₀' w₀' _ v' w' h₀' rfl hv' hw'
      have n2 := hL₀.nat k' F f' β₀' y₀' v₀' w₀' _ v' w' h₀' rfl hv' hw'
      refine eq_mul_of_frames hL hL₀ hfr hfr' (b := f' (β₀' ⟨a, haF⟩)) ?_
      rw [n1, n2, hk, map_mul]
  · refine ⟨1, one_ne_zero, fun F _ β y v w hfr => ?_⟩
    exfalso
    obtain ⟨k, _, β₀, y₀, v₀, w₀, f, j, h₀, -, hj, -, hb⟩ :=
      GlobalTheory.T.framed_point_descends E H D l Xo c U τ F β y v w hfr
    obtain ⟨v', w', hfr', -, -⟩ := hb ℂ j
    rw [hj] at hfr'
    exact hex ⟨_, v', w', hfr'⟩

end GlobalTheory.CompanionTheory.Ar.Flat
