import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsOpenChartFramedPointTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsTransitionUnique
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsDiscreteValuationRingPlace

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.LocM.Inhab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

section Transfer

variable {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {g : S' ⟶ S} (m : SABMap t' t g)
  {R : Type} [CommRing R] (x : Sp R ⟶ S')

/- English proof (translation)
The claim follows from `spMap_epsScaleR_comp c`.
-/
theorem eps_over (c : R) :
    spMap (epsMul c) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R)) :=
  spMap_epsScaleR_comp c

/- English proof (translation)
Establish `e : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R`. Use extensionality with `s`. Simplify using the standard rewrite rules. Simplify using `only [spMap]`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, e]`.

Simplify using the standard rewrite rules.
-/
theorem zs : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
  have e : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    ext s; simp
  simp only [spMap]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
  simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨m.cart.1.lift w (spMap (algebraMap R (DualNumber R)) ≫ x) (h.trans (Category.assoc _ _ _).symm), m.cart.1.lift_fst _ _ _, m.cart.1.lift_snd _ _ _⟩`.
-/
theorem lift_ex (w : Sp (DualNumber R) ⟶ t.G.left) (h : w ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x ≫ g) :
    ∃ v : Sp (DualNumber R) ⟶ t'.G.left, v ≫ m.φ = w ∧ v ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x :=
  ⟨m.cart.1.lift w (spMap (algebraMap R (DualNumber R)) ≫ x) (h.trans (Category.assoc _ _ _).symm),
    m.cart.1.lift_fst _ _ _, m.cart.1.lift_snd _ _ _⟩

/- English proof (translation)
Establish `one : (1 : Over.mk x ⟶ t'.G).left ≫ m.φ = (1 : Over.mk (x ≫ g) ⟶ t.G).left` using `congrArg (fun q => q.left) (map_one (pushHom m.cart (Over.mk x)))`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, m.cart.1.w, reassoc_of% hv]`.

Rewrite using `[← one, ← h, Category.assoc]`. Introduce and unpack `⟨-, h⟩`. Use `⟨hv, m.cart.1.hom_ext ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc]`. Conclude with `h.trans one.symm`.

Rewrite using `[Category.assoc, hv, ← Category.assoc, zs, Category.id_comp]`. Conclude with `(Over.w (1 : Over.mk x ⟶ t'.G)).symm`.
-/
theorem tan_iff (v : Sp (DualNumber R) ⟶ t'.G.left) (hv : v ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) :
    IsTanAtG t' x v ↔ IsTanAtG t (x ≫ g) (v ≫ m.φ) := by
  have one : (1 : Over.mk x ⟶ t'.G).left ≫ m.φ = (1 : Over.mk (x ≫ g) ⟶ t.G).left :=
    congrArg (fun q => q.left) (map_one (pushHom m.cart (Over.mk x)))
  constructor
  · rintro ⟨-, h⟩
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, m.cart.1.w, reassoc_of% hv]
    · rw [← one, ← h, Category.assoc]
  · rintro ⟨-, h⟩
    refine ⟨hv, m.cart.1.hom_ext ?_ ?_⟩
    · rw [Category.assoc]; exact h.trans one.symm
    · rw [Category.assoc, hv, ← Category.assoc, zs, Category.id_comp]
      exact (Over.w (1 : Over.mk x ⟶ t'.G)).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[Category.assoc, ← m.act a, ← Category.assoc, h, Category.assoc]`. Introduce `h`. Use `m.cart.1.hom_ext ?_ ?_` and prove the remaining obligations.

Rewrite using `[Category.assoc, m.act a, Category.assoc, ← h, Category.assoc]`. Rewrite using `[Category.assoc, Over.w (t'.act.act a), Category.assoc, hv, ← Category.assoc, eps_over]`.
-/
theorem eig_iff (v : Sp (DualNumber R) ⟶ t'.G.left) (hv : v ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x)
    (a : 𝓞 E) (c : R) :
    v ≫ (t'.act.act a).left = spMap (epsMul c) ≫ v ↔
      (v ≫ m.φ) ≫ (t.act.act a).left = spMap (epsMul c) ≫ v ≫ m.φ := by
  constructor
  · intro h
    rw [Category.assoc, ← m.act a, ← Category.assoc, h, Category.assoc]
  · intro h
    refine m.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, m.act a, Category.assoc, ← h, Category.assoc]
    · rw [Category.assoc, Over.w (t'.act.act a), Category.assoc, hv, ← Category.assoc, eps_over]

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[show u = u' from funext fun i => Over.OverMorphism.ext (hu i)]`.
-/
theorem prod_left_congr {X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b) {n : ℕ}
    (u : Fin n → (Over.mk a ⟶ G)) (u' : Fin n → (Over.mk b ⟶ G)) (hu : ∀ i, (u i).left = (u' i).left) :
    (List.ofFn u).prod.left = (List.ofFn u').prod.left := by
  subst h
  rw [show u = u' from funext fun i => Over.OverMorphism.ext (hu i)]

/- English proof (translation)
Establish `pr : ∀ (u : Fin n → (tEpsG x ⟶ t'.G)) (u' : Fin n → (tEpsG (x ≫ g) ⟶ t.G)), (∀ i, (u i).left ≫ m.φ = (u' i).left) → (List.ofFn u).prod.left ≫ m.φ = (List.ofFn u').prod.left`. Introduce `u u' h`. Establish `e` using `congrArg (fun q => q.left) ((map_list_prod (pushHom m.cart (tEpsG x)) (List.ofFn u)).trans (by rw [List.map_ofFn]))`. Conclude with `e.trans (prod_left_congr (Category.assoc _ _ _) _ _ h)`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, hu, rfl⟩`. Set `u' : Fin n → (tEpsG (x ≫ g) ⟶ t.G)` to `fun i => Over.homMk ((u i).left ≫ m.φ) (by`. Use `Over.w (u i)` as an intermediate fact. Use `erw [Category.assoc, m.cart.1.w, ← Category.assoc, this, Category.assoc]`. Use the proof step `rfl)`.

Use `⟨u', fun i => ?_, (pr u u' fun _ => rfl).symm⟩` and prove the remaining obligations. Use `show (u i).left ≫ m.φ = _`. Rewrite using `[hu i, Category.assoc]`. Introduce and unpack `⟨u', hu, hw'⟩`. Set `u : Fin n → (tEpsG x ⟶ t'.G)` to `fun i => Over.homMk (spMap (epsMul (cf i)) ≫ v i) (by erw [Category.assoc, hv i, ← Category.assoc, eps_over]; rfl)`.

Use `⟨u, fun _ => rfl, m.cart.1.hom_ext ?_ ?_⟩` and prove the remaining obligations. Conclude with `(pr u u' fun i => (Category.assoc _ _ _).trans (hu i).symm).trans hw'`. Conclude with `(Over.w _).trans hw.symm`.
-/
theorem comb_iff {n : ℕ} (v : Fin n → (Sp (DualNumber R) ⟶ t'.G.left))
    (hv : ∀ i, v i ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) (cf : Fin n → R)
    (w : Sp (DualNumber R) ⟶ t'.G.left) (hw : w ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) :
    IsCombAtG t' x v cf w ↔ IsCombAtG t (x ≫ g) (fun i => v i ≫ m.φ) cf (w ≫ m.φ) := by
  have pr : ∀ (u : Fin n → (tEpsG x ⟶ t'.G)) (u' : Fin n → (tEpsG (x ≫ g) ⟶ t.G)),
      (∀ i, (u i).left ≫ m.φ = (u' i).left) → (List.ofFn u).prod.left ≫ m.φ = (List.ofFn u').prod.left := by
    intro u u' h
    have e := congrArg (fun q => q.left) ((map_list_prod (pushHom m.cart (tEpsG x)) (List.ofFn u)).trans
      (by rw [List.map_ofFn]))
    exact e.trans (prod_left_congr (Category.assoc _ _ _) _ _ h)
  constructor
  · rintro ⟨u, hu, rfl⟩
    let u' : Fin n → (tEpsG (x ≫ g) ⟶ t.G) := fun i => Over.homMk ((u i).left ≫ m.φ) (by
      have := Over.w (u i)
      erw [Category.assoc, m.cart.1.w, ← Category.assoc, this, Category.assoc]; rfl)
    refine ⟨u', fun i => ?_, (pr u u' fun _ => rfl).symm⟩
    show (u i).left ≫ m.φ = _
    rw [hu i, Category.assoc]
  · rintro ⟨u', hu, hw'⟩
    let u : Fin n → (tEpsG x ⟶ t'.G) := fun i => Over.homMk (spMap (epsMul (cf i)) ≫ v i) (by
      erw [Category.assoc, hv i, ← Category.assoc, eps_over]; rfl)
    refine ⟨u, fun _ => rfl, m.cart.1.hom_ext ?_ ?_⟩
    · exact (pr u u' fun i => (Category.assoc _ _ _).trans (hu i).symm).trans hw'
    · exact (Over.w _).trans hw.symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun τ i => ⟨(tan_iff m x _ (hu τ i)).1 (h1 τ i).1, fun a => (eig_iff m x _ (hu τ i) a _).1 ((h1 τ i).2 a)⟩, fun τ w hw he => ?_⟩` and prove the remaining obligations. Take `⟨v, rfl, hv⟩` from `lift_ex m x w hw.1`. Use `h2 τ v ((tan_iff m x _ hv).2 hw) fun a => (eig_iff m x _ hv a _).2 (he a)` as an intermediate fact.

Simplify `this` using `only [comb_iff m x (u τ) (hu τ) _ v hv]`. Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun τ i => ⟨(tan_iff m x _ (hu τ i)).2 (h1 τ i).1, fun a => (eig_iff m x _ (hu τ i) a _).2 ((h1 τ i).2 a)⟩, fun τ w hw he => ?_⟩` and prove the remaining obligations. Use `h2 τ _ ((tan_iff m x _ hw.1).1 hw) fun a => (eig_iff m x _ hw.1 a _).1 (he a)` as an intermediate fact. Simplify `this` using `only [comb_iff m x (u τ) (hu τ) _ w hw.1]`.
-/
theorem frame_iff {l : Level H} {c : Coeff l} (f : c.F →+* R) (u : Vecs Dw t' R)
    (hu : ∀ τ i, u τ i ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) :
    IsFrame t' f x u ↔ IsFrame (Dw := Dw) t f (x ≫ g) (fun τ i => u τ i ≫ m.φ) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun τ i => ⟨(tan_iff m x _ (hu τ i)).1 (h1 τ i).1, fun a => (eig_iff m x _ (hu τ i) a _).1 ((h1 τ i).2 a)⟩,
      fun τ w hw he => ?_⟩
    obtain ⟨v, rfl, hv⟩ := lift_ex m x w hw.1
    have := h2 τ v ((tan_iff m x _ hv).2 hw) fun a => (eig_iff m x _ hv a _).2 (he a)
    simpa only [comb_iff m x (u τ) (hu τ) _ v hv] using this
  · rintro ⟨h1, h2⟩
    refine ⟨fun τ i => ⟨(tan_iff m x _ (hu τ i)).2 (h1 τ i).1, fun a => (eig_iff m x _ (hu τ i) a _).2 ((h1 τ i).2 a)⟩,
      fun τ w hw he => ?_⟩
    have := h2 τ _ ((tan_iff m x _ hw.1).1 hw) fun a => (eig_iff m x _ hw.1 a _).1 (he a)
    simpa only [comb_iff m x (u τ) (hu τ) _ w hw.1] using this

end Transfer

section Charts

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

/- English proof (translation)
Establish `h0 : IsFrame (Dw` using `Dw) Xo.univ.t (algebraMap c.F R) (q ≫ pullback.fst _ _) y.u := by`. Rewrite using `[hq]`. Conclude with `⟨fun τ i => ⟨y.tan τ i, y.eig τ i⟩, fun τ w hw he => y.basis τ w hw he⟩`. Use `choose v hv hv' using fun τ i => lift_ex Y.m0.toSABMap q (y.u τ i) (h0.1 τ i).1.1`. Establish `h1 : IsFrame (Dw` using `Dw) Y.oF.t (algebraMap c.F R) q v := by`.

Use `(frame_iff Y.m0.toSABMap q _ v hv').2 ?_` and prove the remaining obligations. Rewrite using `[show (fun τ i => v τ i ≫ Y.m0.toSABMap.φ) = y.u from funext fun τ => funext fun i => hv τ i]`. Conclude with `h0`. Conclude with `⟨_, (frame_iff Y.m q _ v hv').1 h1⟩`.
-/
theorem frame_of_frPt (Y : Model Xo c β) {R : Type} [CommRing R] [Algebra c.F R] (y : FrPt Xo c R)
    (q : Sp R ⟶ Xo.XF c) (hq : q ≫ pullback.fst _ _ = y.x) :
    ∃ fr : Vecs Dw Y.t R, IsFrame Y.t (algebraMap c.F R) (q ≫ Y.j) fr := by
  have h0 : IsFrame (Dw := Dw) Xo.univ.t (algebraMap c.F R) (q ≫ pullback.fst _ _) y.u := by
    rw [hq]
    exact ⟨fun τ i => ⟨y.tan τ i, y.eig τ i⟩, fun τ w hw he => y.basis τ w hw he⟩
  choose v hv hv' using fun τ i => lift_ex Y.m0.toSABMap q (y.u τ i) (h0.1 τ i).1.1
  have h1 : IsFrame (Dw := Dw) Y.oF.t (algebraMap c.F R) q v := by
    refine (frame_iff Y.m0.toSABMap q _ v hv').2 ?_
    rw [show (fun τ i => v τ i ≫ Y.m0.toSABMap.φ) = y.u from funext fun τ => funext fun i => hv τ i]
    exact h0
  exact ⟨_, (frame_iff Y.m q _ v hv').1 h1⟩

/- English proof (translation)
Establish `hS : Out.SecBaseChangeSt` using `GlobalTheory.lawsFieldsSeparately.2.1`. Take `⟨p, j, y₀, ⟨hj, h1, h2⟩, z', rfl⟩` from `exists_openChart_testRing hS E H Dw l Xo c z`. Set `U : Z.affineOpens` to `⟨(j ≫ J).opensRange, isAffineOpen_opensRange _⟩`. Set `q' : Sp Γ(Z, U.1) ⟶ Sp p.R` to `IsOpenImmersion.lift (j ≫ J) U.2.fromSpec (by`. Rewrite using `[U.2.range_fromSpec]`.

Use the proof step `rfl)`. Establish `hq' : q' ≫ j ≫ J = U.2.fromSpec` using `IsOpenImmersion.lift_fac _ _ _`. Set `φ : p.R →+* Γ(Z, U.1)` to `(Spec.preimage q').hom`. Establish `hφ : spMap φ = q'` using `Spec.map_preimage q'`. Set `: Algebra c.F Γ(Z, U.1)` to `(φ.comp (algebraMap c.F p.R)).toAlgebra`.

Take `⟨y, hy⟩` from `FramedBaseChange.exists_frMap hS E H Dw l Xo c p.R Γ(Z, U.1) ⟨φ, fun _ => rfl⟩ y₀`. Take `⟨fr, hfr⟩` from `frame_of_frPt Y y (q' ≫ j) (by rw [Category.assoc, h1, hy.1, ← hφ])`. Use `⟨U, φ.comp (algebraMap c.F p.R), q' ≫ j, fr, ⟨z', by simp⟩, by rw [Category.assoc, hq'], ?_, hfr⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, h2, ← hφ]`. Simplify using `only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]`.
-/
theorem exists_chart (Y : Model Xo c β) {Z : Scheme.{0}} (J : Xo.XF c ⟶ Z) [IsOpenImmersion J] (z : Xo.XF c) :
    ∃ (U : Z.affineOpens) (alg : c.F →+* Γ(Z, U.1)) (q : Sp Γ(Z, U.1) ⟶ Xo.XF c) (fr : Vecs Dw Y.t Γ(Z, U.1)),
      J z ∈ U.1 ∧ q ≫ J = U.2.fromSpec ∧ q ≫ pullback.snd _ _ = spMap alg ∧ IsFrame Y.t alg (q ≫ Y.j) fr := by
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨p, j, y₀, ⟨hj, h1, h2⟩, z', rfl⟩ := exists_openChart_testRing hS E H Dw l Xo c z
  let U : Z.affineOpens := ⟨(j ≫ J).opensRange, isAffineOpen_opensRange _⟩
  let q' : Sp Γ(Z, U.1) ⟶ Sp p.R := IsOpenImmersion.lift (j ≫ J) U.2.fromSpec (by
    rw [U.2.range_fromSpec]; rfl)
  have hq' : q' ≫ j ≫ J = U.2.fromSpec := IsOpenImmersion.lift_fac _ _ _
  let φ : p.R →+* Γ(Z, U.1) := (Spec.preimage q').hom
  have hφ : spMap φ = q' := Spec.map_preimage q'
  let : Algebra c.F Γ(Z, U.1) := (φ.comp (algebraMap c.F p.R)).toAlgebra
  obtain ⟨y, hy⟩ := FramedBaseChange.exists_frMap hS E H Dw l Xo c p.R Γ(Z, U.1) ⟨φ, fun _ => rfl⟩ y₀
  obtain ⟨fr, hfr⟩ := frame_of_frPt Y y (q' ≫ j) (by rw [Category.assoc, h1, hy.1, ← hφ])
  refine ⟨U, φ.comp (algebraMap c.F p.R), q' ≫ j, fr, ⟨z', by simp⟩, by rw [Category.assoc, hq'], ?_, hfr⟩
  rw [Category.assoc, h2, ← hφ]
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

/- English proof (translation)
Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible V`. Establish `: IsLocalization.Away π F`. Use `(IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers π) (nonZeroDivisors V) ?_ ?_).2 inferInstance` and prove the remaining obligations. Introduce and unpack `_ ⟨n, rfl⟩`. Conclude with `pow_mem (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero) n`.

Introduce `a ha`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero ha) hπ`. Conclude with `⟨π ^ n, ⟨n, rfl⟩, (Units.mul_left_dvd).2 dvd_rfl⟩`. Conclude with `IsOpenImmersion.of_isLocalization (S := F) π`.
-/
theorem isOpenImmersion_generic {F : Type} [Field F] (V : ValuationSubring F) [IsDiscreteValuationRing V] :
    IsOpenImmersion (spMap V.subtype) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have : IsLocalization.Away π F := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers π) (nonZeroDivisors V) ?_ ?_).2 inferInstance
    · rintro _ ⟨n, rfl⟩
      exact pow_mem (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero) n
    · intro a ha
      obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero ha) hπ
      exact ⟨π ^ n, ⟨n, rfl⟩, (Units.mul_left_dvd).2 dvd_rfl⟩
  exact IsOpenImmersion.of_isLocalization (S := F) π

/- English proof (translation)
Take `⟨N, i, _, _, h⟩` from `Xo.qproj`. Establish `: QuasiCompact (PSpace.str (KA l) N)` using `by have := isProper_str (KA l) N; infer_instance`. Establish `: QuasiCompact Xo.s` using `by rw [← h]; infer_instance`. Conclude with `QuasiCompact.compactSpace_of_compactSpace (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))`.
-/
theorem compactSpace_XF (Xo : Moduli Dw l) (c : Coeff l) : CompactSpace (Xo.XF c) := by
  obtain ⟨N, i, _, _, h⟩ := Xo.qproj
  have : QuasiCompact (PSpace.str (KA l) N) := by have := isProper_str (KA l) N; infer_instance
  have : QuasiCompact Xo.s := by rw [← h]; infer_instance
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))

/- English proof (translation)
Introduce `x` and use `by let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv have := (h (f x)).1 have := (h (f x)).2 exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩`.
-/
theorem normal_of_iso {X X' : Scheme.{0}} (f : X' ⟶ X) [IsIso f] (h : Geo.Tor.IsNormalScheme X) :
    Geo.Tor.IsNormalScheme X' := fun x => by
  let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  have := (h (f x)).1
  have := (h (f x)).2
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

end Charts

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ}

/- English proof (translation)
Take `⟨N, cl, hcl, hs⟩` from `(Y i).proj`. Use `GlobalTheory.ArcValuationSetting.isDiscreteValuationRing_place i.c W hp hW` as an intermediate fact. Use `isOpenImmersion_generic (i.c.V W)` as an intermediate fact. Use `(Y i).jQ_open` as an intermediate fact. Establish `hj : IsOpenImmersion (Y i).j` using `by unfold Model.j; infer_instance`.

Establish `hjs : (Y i).j ≫ (Y i).s = pullback.snd _ _ ≫ spMap (i.c.V W).subtype`. Unfold `Model.j`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, (Y i).jQ_over]`. Set `e : (Y i).X ⟶ cl.ker.subscheme` to `cl.toImage`. Establish `he : IsIso e` using `inferInstanceAs (IsIso cl.toImage)`.

Establish `hec : e ≫ cl.ker.subschemeι = cl` using `cl.toImage_imageι`. Set `J` to `(Y i).j ≫ e`. Establish `hJ : J ≫ inv e = (Y i).j` using `by simp [J]`. Use `choose U alg q fr hz hq hqa hfr using exists_chart (Y i) J`. Establish `hfs : ∀ z, IsOpenImmersion (U z).2.fromSpec` using `fun z => (U z).2.isOpenImmersion_fromSpec`.

Use `compactSpace_XF (Xo i.l) i.c` as an intermediate fact. Take `⟨T, hT⟩` from `isCompact_univ.elim_finite_subcover (fun z => ((J ⁻¹ᵁ (U z).1 : ((Xo i.l).XF i.c).Opens) : Set ((Xo i.l).XF i.c))) (fun z => (J ⁻¹ᵁ (U z).1).2) (fun z _ => Set.mem_iUnion.2 ⟨z, hz z⟩)`. Set `a : Fin (Fintype.card T) → (Xo i.l).XF i.c` to `fun k => ((Fintype.equivFin T).symm k).1`. Establish `ha : ∀ z, ∃ k, J z ∈ (U (a k)).1` using `fun z => by`. Take `⟨z', hz', h⟩` from `Set.mem_iUnion₂.1 (hT (Set.mem_univ z))`.

Conclude with `⟨Fintype.equivFin T ⟨z', hz'⟩, by simpa [a] using h⟩`. Set `P : Pre Y i₀` to `⟨i, hd, hle, N, cl.ker, inv e, fun _ => ∅, _, fun k => U (a k), fun k => alg (a k), fun k => fr (a k)⟩`. Establish `hπ : inv e ≫ (Y i).s = P.s` using `by show _ = cl.ker.subschemeι ≫ PSpace.str _ N`. Rewrite using `[IsIso.inv_comp_eq, ← Category.assoc, hec, hs]`. Establish `hopn : P.opn = Set.range J`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, h⟩`. Use `⟨z, ?_⟩` and prove the remaining obligations. Establish `h' : (Y i).j z = inv e x` using `h`.

Use `show (_ ≫ e) z = x`. Rewrite using `[Scheme.Hom.comp_apply, h', ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]`. Both sides reduce to the same expression. Introduce and unpack `⟨z, rfl⟩`. Conclude with `⟨z, by rw [← Scheme.Hom.comp_apply]; exact congrArg (fun f => f z) hJ.symm⟩`.

Establish `hch : ∀ k, P.chart k ≫ inv e = q (a k) ≫ (Y i).j` using `fun k => by show (U (a k)).2.fromSpec ≫ _ = _`. Rewrite using `[← hq, Category.assoc, hJ]`. Establish `hn : Geo.Tor.IsNormalScheme P.X` using `normal_of_iso (inv e) (Y i).normal`. Apply the tactic sequence `refine ⟨⟨P, hπ, (by first | exact hn | exact (GlobalTheory.isNormalScheme_iff_pred _).2 hn), ?_, ?_, ?_, fun k => ?_, fun k => ?_, fun k => ?_, ?_, ?_⟩, rfl, (inferInstance : IsIso (inv e)), fun _ => rfl⟩`. Use `(Y i).flat` as an intermediate fact.

Rewrite using `[← hπ]`. Use `infer_instance`. Use `GlobalTheory.TransitionUnique.isDominant_j (Y i)` as an intermediate fact. Rewrite using `[hopn]`. Conclude with `J.denseRange`.

Rewrite using `[hopn]`. Use `Set.Subset.antisymm (Set.iUnion_subset fun k x hx => ?_) ?_` and prove the remaining obligations. Establish `hx' : x ∈ Set.range (U (a k)).2.fromSpec` using `by rw [(U (a k)).2.range_fromSpec]; exact hx`. Take `⟨y, rfl⟩` from `hx'`. Conclude with `⟨q (a k) y, by rw [← hq]; simp⟩`.

Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `Set.mem_iUnion.2 (ha z)`. Rewrite using `[← hπ, ← Category.assoc, hch, Category.assoc, hjs, ← Category.assoc, hqa]`. Simplify using `only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]`. Establish `: IsOpenImmersion (P.chart k)` using `hfs _`.

Conclude with `inferInstanceAs (Smooth (P.chart k ≫ inv e))`. Use `show IsFrame (Y i).t (alg (a k)) (P.chart k ≫ inv e) (fr (a k))`. Rewrite using `[hch]`. Conclude with `hfr _`. Introduce `k _ b b' φ φ' _ τ n hn`.

Conclude with `absurd hn (Finset.notMem_empty n)`. Introduce `k _ f y hy u hu`. Establish `hw : (y ≫ J) ≫ inv e = y ≫ (Y i).j` using `by rw [Category.assoc, hJ]`. Use `⟨y ≫ J, ⟨hw, ?_⟩, fun w h => ?_⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `ha (y default)`.

Use `hfs (a b)` as an intermediate fact. Set `v : Sp k ⟶ Sp Γ(cl.ker.subscheme, (U (a b)).1)` to `IsOpenImmersion.lift (U (a b)).2.fromSpec (y ≫ J) (by`. Rewrite using `[(U (a b)).2.range_fromSpec]`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[Subsingleton.elim x default]`.

Simplify using `using hb)`. Establish `hv : v ≫ (U (a b)).2.fromSpec = y ≫ J` using `IsOpenImmersion.lift_fac _ _ _`. Set `φ : Γ(cl.ker.subscheme, (U (a b)).1) →+* k` to `(Spec.preimage v).hom`. Establish `hφ : spMap φ = v` using `Spec.map_preimage v`. Establish `hvq : v ≫ q (a b) = y` using `by rw [← cancel_mono J, Category.assoc, hq, hv]`.

Establish `hf : φ.comp (alg (a b)) = f`. Establish `: spMap (φ.comp (alg (a b))) = spMap f`. Rewrite using `[← hy, ← hvq, Category.assoc, hqa, ← hφ]`. Simplify using `only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]`. Conclude with `congrArg CommRingCat.Hom.hom (Spec.map_injective this)`.

Use `⟨b, φ, by rw [hφ]; exact hv, ?_, fun τ n hn => absurd hn (Finset.notMem_empty n)⟩` and prove the remaining obligations. Use `show IsFrame (Y i).t (φ.comp (alg (a b))) ((y ≫ J) ≫ inv e) u`. Rewrite using `[hf, hw]`. Conclude with `hu`. Conclude with `(cancel_mono (inv e)).1 (h.1.trans hw.symm)`.
-/
theorem exists_base (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (Y : LocalSystem Xo p W) (i₀ i : Idx H p)
    (hd : i₀.l.Dvd i.l) (hle : i₀.c.F ≤ i.c.F) :
    ∃ Z : Mdl Y i₀, Z.i = i ∧ IsIso Z.π ∧ ∀ σ, Z.ty σ = ∅ := by
  obtain ⟨N, cl, hcl, hs⟩ := (Y i).proj
  have := GlobalTheory.ArcValuationSetting.isDiscreteValuationRing_place i.c W hp hW
  have := isOpenImmersion_generic (i.c.V W)
  have := (Y i).jQ_open
  have hj : IsOpenImmersion (Y i).j := by unfold Model.j; infer_instance
  have hjs : (Y i).j ≫ (Y i).s = pullback.snd _ _ ≫ spMap (i.c.V W).subtype := by
    unfold Model.j
    rw [Category.assoc, pullback.condition, ← Category.assoc, (Y i).jQ_over]
  let e : (Y i).X ⟶ cl.ker.subscheme := cl.toImage
  have he : IsIso e := inferInstanceAs (IsIso cl.toImage)
  have hec : e ≫ cl.ker.subschemeι = cl := cl.toImage_imageι
  let J := (Y i).j ≫ e
  have hJ : J ≫ inv e = (Y i).j := by simp [J]
  choose U alg q fr hz hq hqa hfr using exists_chart (Y i) J
  have hfs : ∀ z, IsOpenImmersion (U z).2.fromSpec := fun z => (U z).2.isOpenImmersion_fromSpec
  have := compactSpace_XF (Xo i.l) i.c
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun z => ((J ⁻¹ᵁ (U z).1 : ((Xo i.l).XF i.c).Opens) : Set ((Xo i.l).XF i.c)))
    (fun z => (J ⁻¹ᵁ (U z).1).2) (fun z _ => Set.mem_iUnion.2 ⟨z, hz z⟩)
  let a : Fin (Fintype.card T) → (Xo i.l).XF i.c := fun k => ((Fintype.equivFin T).symm k).1
  have ha : ∀ z, ∃ k, J z ∈ (U (a k)).1 := fun z => by
    obtain ⟨z', hz', h⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ z))
    exact ⟨Fintype.equivFin T ⟨z', hz'⟩, by simpa [a] using h⟩
  let P : Pre Y i₀ := ⟨i, hd, hle, N, cl.ker, inv e, fun _ => ∅, _, fun k => U (a k), fun k => alg (a k), fun k => fr (a k)⟩
  have hπ : inv e ≫ (Y i).s = P.s := by
    show _ = cl.ker.subschemeι ≫ PSpace.str _ N
    rw [IsIso.inv_comp_eq, ← Category.assoc, hec, hs]
  have hopn : P.opn = Set.range J := by
    ext x
    constructor
    · rintro ⟨z, h⟩
      refine ⟨z, ?_⟩
      have h' : (Y i).j z = inv e x := h
      show (_ ≫ e) z = x
      rw [Scheme.Hom.comp_apply, h', ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
      rfl
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [← Scheme.Hom.comp_apply]; exact congrArg (fun f => f z) hJ.symm⟩
  have hch : ∀ k, P.chart k ≫ inv e = q (a k) ≫ (Y i).j := fun k => by
    show (U (a k)).2.fromSpec ≫ _ = _
    rw [← hq, Category.assoc, hJ]
  have hn : Geo.Tor.IsNormalScheme P.X := normal_of_iso (inv e) (Y i).normal
  refine ⟨⟨P, hπ, (by first | exact hn | exact (GlobalTheory.isNormalScheme_iff_pred _).2 hn), ?_, ?_, ?_, fun k => ?_, fun k => ?_, fun k => ?_, ?_, ?_⟩,
    rfl, (inferInstance : IsIso (inv e)), fun _ => rfl⟩
  · have := (Y i).flat
    rw [← hπ]; infer_instance
  · have := GlobalTheory.TransitionUnique.isDominant_j (Y i)
    rw [hopn]
    exact J.denseRange
  · rw [hopn]
    refine Set.Subset.antisymm (Set.iUnion_subset fun k x hx => ?_) ?_
    · have hx' : x ∈ Set.range (U (a k)).2.fromSpec := by rw [(U (a k)).2.range_fromSpec]; exact hx
      obtain ⟨y, rfl⟩ := hx'
      exact ⟨q (a k) y, by rw [← hq]; simp⟩
    · rintro _ ⟨z, rfl⟩
      exact Set.mem_iUnion.2 (ha z)
  · rw [← hπ, ← Category.assoc, hch, Category.assoc, hjs, ← Category.assoc, hqa]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  · have : IsOpenImmersion (P.chart k) := hfs _
    exact inferInstanceAs (Smooth (P.chart k ≫ inv e))
  · show IsFrame (Y i).t (alg (a k)) (P.chart k ≫ inv e) (fr (a k))
    rw [hch]; exact hfr _
  · intro k _ b b' φ φ' _ τ n hn
    exact absurd hn (Finset.notMem_empty n)
  · intro k _ f y hy u hu
    have hw : (y ≫ J) ≫ inv e = y ≫ (Y i).j := by rw [Category.assoc, hJ]
    refine ⟨y ≫ J, ⟨hw, ?_⟩, fun w h => ?_⟩
    · obtain ⟨b, hb⟩ := ha (y default)
      have := hfs (a b)
      let v : Sp k ⟶ Sp Γ(cl.ker.subscheme, (U (a b)).1) := IsOpenImmersion.lift (U (a b)).2.fromSpec (y ≫ J) (by
        rw [(U (a b)).2.range_fromSpec]
        rintro _ ⟨x, rfl⟩
        rw [Subsingleton.elim x default]
        simpa using hb)
      have hv : v ≫ (U (a b)).2.fromSpec = y ≫ J := IsOpenImmersion.lift_fac _ _ _
      let φ : Γ(cl.ker.subscheme, (U (a b)).1) →+* k := (Spec.preimage v).hom
      have hφ : spMap φ = v := Spec.map_preimage v
      have hvq : v ≫ q (a b) = y := by rw [← cancel_mono J, Category.assoc, hq, hv]
      have hf : φ.comp (alg (a b)) = f := by
        have : spMap (φ.comp (alg (a b))) = spMap f := by
          rw [← hy, ← hvq, Category.assoc, hqa, ← hφ]
          simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
        exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
      refine ⟨b, φ, by rw [hφ]; exact hv, ?_, fun τ n hn => absurd hn (Finset.notMem_empty n)⟩
      show IsFrame (Y i).t (φ.comp (alg (a b))) ((y ≫ J) ≫ inv e) u
      rw [hf, hw]; exact hu
    · exact (cancel_mono (inv e)).1 (h.1.trans hw.symm)

/- English proof (translation)
Take `⟨d, rfl⟩` from `h`. Establish `hn : (n : ℂ) ≠ 0` using `by exact_mod_cast left_ne_zero_of_mul hm`. Establish `hd : (d : ℂ) ≠ 0` using `by exact_mod_cast right_ne_zero_of_mul hm`. Establish `: zeta n = zeta (n * d) ^ d`. Unfold `zeta`.

Rewrite using `[← Complex.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`.

Conclude with `pow_mem hF d`.
-/
theorem zeta_mem {n m : ℕ} (hm : m ≠ 0) (h : n ∣ m) (F : IntermediateField ℚ ℂ) (hF : zeta m ∈ F) : zeta n ∈ F := by
  obtain ⟨d, rfl⟩ := h
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast left_ne_zero_of_mul hm
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast right_ne_zero_of_mul hm
  have : zeta n = zeta (n * d) ^ d := by
    unfold zeta
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [this]
  exact pow_mem hF d

/- English proof (translation)
Consider the cases of `b with`. Consider the case `none => exact ⟨i₀, rfl, ⟨dvd_rfl, le_rfl, dvd_rfl⟩, le_rfl⟩`. Consider the case `some n`. Set `l : Level H` to `{ i₀.l with A := i₀.l.A * p ^ n, A_pos := Nat.mul_pos i₀.l.A_pos (pow_pos (Nat.pos_of_ne_zero hp) n) }`. Establish `hM : l.M' ≠ 0` using `Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'`.

Establish `hz : zeta l.M' ∈ i₀.c.F ⊔ IntermediateField.adjoin ℚ {zeta l.M'}` using `(le_sup_right : IntermediateField.adjoin ℚ {zeta l.M'} ≤ _) (IntermediateField.subset_adjoin _ _ rfl)`. Establish `hint : IsIntegral ℚ (zeta l.M')` using `((Complex.isPrimitiveRoot_exp l.M' hM).isIntegral (Nat.pos_of_ne_zero hM)).tower_top`. Use `IntermediateField.adjoin.finiteDimensional hint` as an intermediate fact. Use `i₀.c.fin` as an intermediate fact. Set `c : Coeff l` to `⟨i₀.c.F ⊔ IntermediateField.adjoin ℚ {zeta l.M'}, inferInstance, fun τ a => (le_sup_left : i₀.c.F ≤ _) (i₀.c.conj τ a), hz, by`.

Use `IntermediateField.adjoin_le_iff.2 ?_` and prove the remaining obligations. Introduce and unpack `x (rfl | rfl)`. Conclude with `(le_sup_left : i₀.c.F ≤ _) (i₀.c.le (IntermediateField.subset_adjoin _ _ (by simp)))`. Conclude with `zeta_mem hM (Nat.dvd_lcm_right _ _) _ hz⟩`. Conclude with `⟨⟨l, c, i₀.good⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨dvd_rfl, le_rfl, dvd_mul_right _ _⟩, le_sup_left⟩`.
-/
theorem exists_lvl (hp : p ≠ 0) (i₀ : Idx H p) (b : Option ℕ) :
    ∃ i : Idx H p, IsLvl i₀ i b ∧ i₀.l.Dvd i.l ∧ i₀.c.F ≤ i.c.F := by
  cases b with
  | none => exact ⟨i₀, rfl, ⟨dvd_rfl, le_rfl, dvd_rfl⟩, le_rfl⟩
  | some n =>
    let l : Level H := { i₀.l with A := i₀.l.A * p ^ n, A_pos := Nat.mul_pos i₀.l.A_pos (pow_pos (Nat.pos_of_ne_zero hp) n) }
    have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
    have hz : zeta l.M' ∈ i₀.c.F ⊔ IntermediateField.adjoin ℚ {zeta l.M'} :=
      (le_sup_right : IntermediateField.adjoin ℚ {zeta l.M'} ≤ _) (IntermediateField.subset_adjoin _ _ rfl)
    have hint : IsIntegral ℚ (zeta l.M') := ((Complex.isPrimitiveRoot_exp l.M' hM).isIntegral (Nat.pos_of_ne_zero hM)).tower_top
    have := IntermediateField.adjoin.finiteDimensional hint
    have := i₀.c.fin
    let c : Coeff l := ⟨i₀.c.F ⊔ IntermediateField.adjoin ℚ {zeta l.M'}, inferInstance,
      fun τ a => (le_sup_left : i₀.c.F ≤ _) (i₀.c.conj τ a), hz, by
        refine IntermediateField.adjoin_le_iff.2 ?_
        rintro x (rfl | rfl)
        · exact (le_sup_left : i₀.c.F ≤ _) (i₀.c.le (IntermediateField.subset_adjoin _ _ (by simp)))
        · exact zeta_mem hM (Nat.dvd_lcm_right _ _) _ hz⟩
    exact ⟨⟨l, c, i₀.good⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨dvd_rfl, le_rfl, dvd_mul_right _ _⟩, le_sup_left⟩

/- English proof (translation)
Use `choose i h1 h2 h3 using exists_lvl hp i₀`. Use `choose Z g1 g2 g3 using fun b => exists_base hp hW Y i₀ (i b) (h2 b) (h3 b)`. Conclude with `⟨⟨Z, fun b => by rw [g1]; exact h1 b, g2, g3⟩⟩`.
-/
theorem nonempty_bases (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (Y : LocalSystem Xo p W) (i₀ : Idx H p) :
    Nonempty (Bases Y i₀) := by
  choose i h1 h2 h3 using exists_lvl hp i₀
  choose Z g1 g2 g3 using fun b => exists_base hp hW Y i₀ (i b) (h2 b) (h3 b)
  exact ⟨⟨Z, fun b => by rw [g1]; exact h1 b, g2, g3⟩⟩

section Ident

open GlobalTheory.Frames.EigenBaseChange

/- English proof (translation)
Set `` to `f.toAlgebra`. Set `` to `(φ.comp f).toAlgebra`. Set `ψ : R →ₐ[c.F] T` to `⟨φ, fun _ => rfl⟩`. Set `e` to `(Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))).symm`. Establish `t1 : ∀ τ i, IsTanAt x (u τ i)` using `fun τ i => (h.1 τ i).1`.

Establish `e1 : ∀ τ i, IsEigAt c τ (u τ i)` using `fun τ i => (h.1 τ i).2`. Establish `h1` using `(GlobalTheory.T.eigenBasis_iff_tangentBasis E H Dw l X₀ c R x u _ e t1 e1).1 h.2`. Establish `h2` using `GlobalTheory.T.isTangentVectorBasisAtPoint_baseChange E H Dw l X₀ R T φ x _ _ h1`. Conclude with `⟨fun τ i => ⟨isTanAt_baseChange φ (t1 τ i), isEigAt_baseChange ψ τ (e1 τ i)⟩, (GlobalTheory.T.eigenBasis_iff_tangentBasis E H Dw l X₀ c T (spMap φ ≫ x) (u.bc φ) _ e (fun τ i => isTanAt_baseChange φ (t1 τ i)) (fun τ i => isEigAt_baseChange ψ τ (e1 τ i))).2 h2⟩`.
-/
theorem frame_bc_univ {l : Level H} (X₀ : Moduli Dw l) {c : Coeff l} {R T : Type} [CommRing R] [CommRing T] (f : c.F →+* R)
    (φ : R →+* T) (x : Sp R ⟶ X₀.X) (u : Vecs Dw X₀.univ.t R) (h : IsFrame X₀.univ.t f x u) :
    IsFrame X₀.univ.t (φ.comp f) (spMap φ ≫ x) (u.bc φ) := by
  classical
  let := f.toAlgebra
  let := (φ.comp f).toAlgebra
  let ψ : R →ₐ[c.F] T := ⟨φ, fun _ => rfl⟩
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))).symm
  have t1 : ∀ τ i, IsTanAt x (u τ i) := fun τ i => (h.1 τ i).1
  have e1 : ∀ τ i, IsEigAt c τ (u τ i) := fun τ i => (h.1 τ i).2
  have h1 := (GlobalTheory.T.eigenBasis_iff_tangentBasis E H Dw l X₀ c R x u _ e t1 e1).1 h.2
  have h2 := GlobalTheory.T.isTangentVectorBasisAtPoint_baseChange E H Dw l X₀ R T φ x _ _ h1
  exact ⟨fun τ i => ⟨isTanAt_baseChange φ (t1 τ i), isEigAt_baseChange ψ τ (e1 τ i)⟩,
    (GlobalTheory.T.eigenBasis_iff_tangentBasis E H Dw l X₀ c T (spMap φ ≫ x) (u.bc φ) _ e
    (fun τ i => isTanAt_baseChange φ (t1 τ i)) (fun τ i => isEigAt_baseChange ψ τ (e1 τ i))).2 h2⟩

/- English proof (translation)
Use `choose v hv hv' using fun τ i => lift_ex Y.m q (u τ i) (h.1 τ i).1.1`. Take `rfl : (fun τ i => v τ i ≫ Y.m.φ) = u` from `funext fun τ => funext fun i => hv τ i`. Establish `h1` using `(frame_iff Y.m0.toSABMap q f v hv').1 ((frame_iff Y.m q f v hv').2 h)`. Establish `h2` using `frame_bc_univ X₀ f φ _ _ h1`. Establish `hb : ∀ τ i, Vecs.bc (Dw` using `Dw) (t := Y.oF.t) φ v τ i ≫ Y.oF.t.G.hom = spMap (algebraMap T (DualNumber T)) ≫ spMap φ ≫ q := fun τ i => by show (_ ≫ _) ≫ _ = _`.

Rewrite using `[Category.assoc, hv', ← Category.assoc, spMap_spMap, EigenBaseChange.dualMap_comp_alg, ← spMap_spMap, Category.assoc]`. Establish `h3` using `(frame_iff Y.m0.toSABMap (spMap φ ≫ q) (φ.comp f) _ hb).2 (by`. Establish `h2'` using `h2`. Unfold `Vecs.bc at h2' ⊢`. Simplify `h2')` using `only [Category.assoc]`.

Establish `h4` using `(frame_iff Y.m (spMap φ ≫ q) (φ.comp f) _ hb).1 h3`. Unfold `Vecs.bc at h4 ⊢`. Simplify `h4` using `only [Category.assoc, Model.j]`.
-/
theorem frame_bc {l : Level H} {X₀ : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model X₀ c β) {R T : Type} [CommRing R] [CommRing T] (f : c.F →+* R)
    (φ : R →+* T) (q : Sp R ⟶ X₀.XF c) (u : Vecs Dw Y.t R) (h : IsFrame Y.t f (q ≫ Y.j) u) :
    IsFrame Y.t (φ.comp f) (spMap φ ≫ q ≫ Y.j) (u.bc φ) := by
  choose v hv hv' using fun τ i => lift_ex Y.m q (u τ i) (h.1 τ i).1.1
  obtain rfl : (fun τ i => v τ i ≫ Y.m.φ) = u := funext fun τ => funext fun i => hv τ i
  have h1 := (frame_iff Y.m0.toSABMap q f v hv').1 ((frame_iff Y.m q f v hv').2 h)
  have h2 := frame_bc_univ X₀ f φ _ _ h1
  have hb : ∀ τ i, Vecs.bc (Dw := Dw) (t := Y.oF.t) φ v τ i ≫ Y.oF.t.G.hom =
      spMap (algebraMap T (DualNumber T)) ≫ spMap φ ≫ q := fun τ i => by
    show (_ ≫ _) ≫ _ = _
    rw [Category.assoc, hv', ← Category.assoc, spMap_spMap, EigenBaseChange.dualMap_comp_alg, ← spMap_spMap, Category.assoc]
  have h3 := (frame_iff Y.m0.toSABMap (spMap φ ≫ q) (φ.comp f) _ hb).2 (by
    have h2' := h2
    unfold Vecs.bc at h2' ⊢
    simpa only [Category.assoc] using h2')
  have h4 := (frame_iff Y.m (spMap φ ≫ q) (φ.comp f) _ hb).1 h3
  unfold Vecs.bc at h4 ⊢
  simpa only [Category.assoc, Model.j] using h4

/- English proof (translation)
Set `w : tEpsG x ⟶ t.G` to `Over.homMk (v i) (hv i).1`. Use `⟨Pi.mulSingle i w, fun j => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Apply the tactic sequence `have : (epsMul (1 : R)) = RingHom.id _ := by ext s <;> simp [epsMul]`.

Simplify using `[w, this, spMap]`. Establish `: (epsMul (0 : R)) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom`. Apply the tactic sequence `ext s <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]`. Rewrite using `[Pi.mulSingle_eq_of_ne h, Pi.single_eq_of_ne h, this, ← spMap_spMap, Category.assoc, (hv j).2]`. Establish `e : (Over.homMk (spMap (algebraMap R (DualNumber R))) rfl : tEpsG x ⟶ Over.mk x) ≫ (1 : Over.mk x ⟶ t.G) = 1`.

Simplify using `[Hom.one_def]`. Rewrite using `[← e, Over.comp_left]`. Both sides reduce to the same expression. Set `: CommMonoid (tEpsG x ⟶ t.G)` to `inferInstance`. Rewrite using `[List.prod_ofFn, Finset.prod_pi_mulSingle']`.

Simplify using `[w]`.
-/
theorem comb_single {S : Scheme.{0}} (t : SAB H S) {R : Type} [CommRing R] (x : Sp R ⟶ S) {n : ℕ}
    (v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)) (hv : ∀ i, IsTanAtG t x (v i)) (i : Fin n) :
    IsCombAtG t x v (Pi.single i 1) (v i) := by
  classical
  let w : tEpsG x ⟶ t.G := Over.homMk (v i) (hv i).1
  refine ⟨Pi.mulSingle i w, fun j => ?_, ?_⟩
  · by_cases h : j = i
    · subst h
      have : (epsMul (1 : R)) = RingHom.id _ := by ext s <;> simp [epsMul]
      simp [w, this, spMap]
    · have : (epsMul (0 : R)) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
        ext s <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
      rw [Pi.mulSingle_eq_of_ne h, Pi.single_eq_of_ne h, this, ← spMap_spMap, Category.assoc, (hv j).2]
      have e : (Over.homMk (spMap (algebraMap R (DualNumber R))) rfl : tEpsG x ⟶ Over.mk x) ≫
          (1 : Over.mk x ⟶ t.G) = 1 := by
        simp [Hom.one_def]
      rw [← e, Over.comp_left]
      rfl
  · let : CommMonoid (tEpsG x ⟶ t.G) := inferInstance
    rw [List.prod_ofFn, Finset.prod_pi_mulSingle']
    simp [w]

/- English proof (translation)
Introduce `τ k _ i hi` and use `⟨Pi.single i 1, fun j hj => Pi.single_eq_of_ne (fun h => by subst h; omega) _, comb_single t x _ (hu τ) i⟩`.
-/
theorem sameFlag_refl (ty : (E →+* ℂ) → Finset ℕ) {S : Scheme.{0}} (t : SAB H S) {R : Type} [CommRing R] (x : Sp R ⟶ S)
    (u : Vecs Dw t R) (hu : ∀ τ i, IsTanAtG t x (u τ i)) : SameFlag ty t x u u := fun τ k _ i hi =>
  ⟨Pi.single i 1, fun j hj => Pi.single_eq_of_ne (fun h => by subst h; omega) _, comb_single t x _ (hu τ) i⟩

variable {Y : LocalSystem Xo p W} {i₀ : Idx H p}

/- English proof (translation)
Use `GlobalTheory.ArcValuationSetting.isDiscreteValuationRing_place Z.i.c W hp hW` as an intermediate fact. Use `isOpenImmersion_generic (Z.i.c.V W)` as an intermediate fact. Use `(Y Z.i).jQ_open` as an intermediate fact. Establish `hj : IsOpenImmersion (Y Z.i).j` using `by unfold Model.j; infer_instance`. Take `⟨a, ha⟩` from `Set.mem_iUnion.1 (Z.cover.ge (hw ⟨default, rfl⟩))`.

Establish `hc : IsOpenImmersion (Z.chart a)` using `(Z.U a).2.isOpenImmersion_fromSpec`. Establish `hr : Set.range (Z.chart a) = (Z.U a).1` using `(Z.U a).2.range_fromSpec`. Set `v` to `IsOpenImmersion.lift (Z.chart a) w (by`. Rewrite using `[hr]`. Introduce and unpack `_ ⟨x, rfl⟩`.

Rewrite using `[Subsingleton.elim x default]`. Conclude with `ha)`. Establish `hv : v ≫ Z.chart a = w` using `IsOpenImmersion.lift_fac _ _ _`. Set `φ : Γ(Z.X, (Z.U a).1) →+* k` to `(Spec.preimage v).hom`. Establish `hφ : spMap φ = v` using `Spec.map_preimage v`.

Set `q` to `IsOpenImmersion.lift (Y Z.i).j (Z.chart a ≫ Z.π) (by`. Introduce and unpack `_ ⟨x, rfl⟩`. Establish `: Z.chart a x ∈ Z.opn` using `Z.cover.le (Set.mem_iUnion.2 ⟨a, hr.le ⟨x, rfl⟩⟩)`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `this)`.

Establish `hq : q ≫ (Y Z.i).j = Z.chart a ≫ Z.π` using `IsOpenImmersion.lift_fac _ _ _`. Establish `h` using `frame_bc (Y Z.i) (Z.alg a) φ q (Z.fr a) (by rw [hq]; exact Z.frame a)`. Rewrite `h` using `[hq, hφ, ← Category.assoc, hv]`. Conclude with `⟨_, a, φ, by rw [hφ, hv], h, sameFlag_refl _ _ _ _ fun τ i => (h.1 τ i).1⟩`.
-/
theorem exists_flagAt (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) {k : Type} [Field k] (w : Sp k ⟶ Z.X)
    (hw : Set.range w ⊆ Z.opn) : ∃ u, Z.FlagAt w u := by
  have := GlobalTheory.ArcValuationSetting.isDiscreteValuationRing_place Z.i.c W hp hW
  have := isOpenImmersion_generic (Z.i.c.V W)
  have := (Y Z.i).jQ_open
  have hj : IsOpenImmersion (Y Z.i).j := by unfold Model.j; infer_instance
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (Z.cover.ge (hw ⟨default, rfl⟩))
  have hc : IsOpenImmersion (Z.chart a) := (Z.U a).2.isOpenImmersion_fromSpec
  have hr : Set.range (Z.chart a) = (Z.U a).1 := (Z.U a).2.range_fromSpec
  let v := IsOpenImmersion.lift (Z.chart a) w (by
    rw [hr]
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x default]
    exact ha)
  have hv : v ≫ Z.chart a = w := IsOpenImmersion.lift_fac _ _ _
  let φ : Γ(Z.X, (Z.U a).1) →+* k := (Spec.preimage v).hom
  have hφ : spMap φ = v := Spec.map_preimage v
  let q := IsOpenImmersion.lift (Y Z.i).j (Z.chart a ≫ Z.π) (by
    rintro _ ⟨x, rfl⟩
    have : Z.chart a x ∈ Z.opn := Z.cover.le (Set.mem_iUnion.2 ⟨a, hr.le ⟨x, rfl⟩⟩)
    rw [Scheme.Hom.comp_apply]
    exact this)
  have hq : q ≫ (Y Z.i).j = Z.chart a ≫ Z.π := IsOpenImmersion.lift_fac _ _ _
  have h := frame_bc (Y Z.i) (Z.alg a) φ q (Z.fr a) (by rw [hq]; exact Z.frame a)
  rw [hq, hφ, ← Category.assoc, hv] at h
  exact ⟨_, a, φ, by rw [hφ, hv], h, sameFlag_refl _ _ _ _ fun τ i => (h.1 τ i).1⟩

/- English proof (translation)
Use `⟨⟨⟨dvd_rfl, le_rfl, dvd_rfl⟩, le_rfl, fun _ => le_rfl⟩, fun k _ w hw => ?_⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `exists_flagAt hp hW Z w hw`. Take `⟨m, hm⟩` from `GlobalTheory.ObjMaps.exists_sab_id (Y Z.i).t`. Establish `hid : spMap (RingHom.id (Z.i.c.V W)) = 𝟙 _` using `Spec.map_id _`. Establish `: IsIso (spMap (RingHom.id (Z.i.c.V W)))` using `by rw [hid]; infer_instance`.

Use `⟨𝟙 _, m, u, ⟨RingHom.id _, inv (pullback.fst _ _), 𝟙 _, fun _ => rfl, by simp, ?_, inferInstance, by simp, fun a => ?_, fun a => ?_⟩, by simp, hu, by simpa [hm] using hu⟩` and prove the remaining obligations. Rewrite using `[IsIso.inv_comp_eq, pullback.condition]`. Conclude with `((congrArg (_ ≫ ·) hid).trans (Category.comp_id _)).symm`. Rewrite using `[Nat.div_self (by have := Z.i.l.three_le; omega), pow_one, hm]; simp`. Rewrite using `[Nat.div_self Z.i.l.A_pos, pow_one, hm]`.

Simplify using the standard rewrite rules.
-/
theorem isMap_id (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) : IsMap Z Z (𝟙 _) := by
  refine ⟨⟨⟨dvd_rfl, le_rfl, dvd_rfl⟩, le_rfl, fun _ => le_rfl⟩, fun k _ w hw => ?_⟩
  obtain ⟨u, hu⟩ := exists_flagAt hp hW Z w hw
  obtain ⟨m, hm⟩ := GlobalTheory.ObjMaps.exists_sab_id (Y Z.i).t
  have hid : spMap (RingHom.id (Z.i.c.V W)) = 𝟙 _ := Spec.map_id _
  have : IsIso (spMap (RingHom.id (Z.i.c.V W))) := by rw [hid]; infer_instance
  refine ⟨𝟙 _, m, u, ⟨RingHom.id _, inv (pullback.fst _ _), 𝟙 _, fun _ => rfl, by simp, ?_, inferInstance, by simp,
    fun a => ?_, fun a => ?_⟩, by simp, hu, by simpa [hm] using hu⟩
  · rw [IsIso.inv_comp_eq, pullback.condition]
    exact ((congrArg (_ ≫ ·) hid).trans (Category.comp_id _)).symm
  · rw [Nat.div_self (by have := Z.i.l.three_le; omega), pow_one, hm]; simp
  · rw [Nat.div_self Z.i.l.A_pos, pow_one, hm]; simp

/- English proof (translation)
Use `⟨rfl, rfl, 𝟙 _, 𝟙 _, isMap_id hp hW Z, isMap_id hp hW Z, ?_⟩` and prove the remaining obligations. Use `isProper_str (Z.i.c.V W) Z.n` as an intermediate fact. Establish `: IsSeparated Z.s` using `by unfold Pre.s; infer_instance`. Establish `: Z.X.IsSeparated` using `⟨by rw [← terminal.comp_from Z.s]; infer_instance⟩`. Use `infer_instance`.
-/
theorem isDiag_self (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) : IsDiag Z Z Z := by
  refine ⟨rfl, rfl, 𝟙 _, 𝟙 _, isMap_id hp hW Z, isMap_id hp hW Z, ?_⟩
  have := isProper_str (Z.i.c.V W) Z.n
  have : IsSeparated Z.s := by unfold Pre.s; infer_instance
  have : Z.X.IsSeparated := ⟨by rw [← terminal.comp_from Z.s]; infer_instance⟩
  infer_instance

def unitIdl (Z : Mdl Y i₀) : Z.Idl := ⟨⊤, fun x hx => by
  rw [Scheme.IdealSheafData.support_top] at hx
  exact hx.elim⟩

/- English proof (translation)
Use `⟨rfl, rfl, Z.X, 𝟙 _, 𝟙 _, ⟨fun x => ?_, fun T g _ => ⟨g, by simp, fun h hh => by simpa using hh⟩⟩, inferInstance, by simpa using isMap_id hp hW Z⟩` and prove the remaining obligations. Take `⟨_, ⟨U, hU, rfl⟩, hx, -⟩` from `Z.X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Conclude with `⟨⟨U, hU⟩, 1, hx, one_mem _, by simp [unitIdl]⟩`.
-/
theorem isNBlow_unit (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) : IsNBlow Z (unitIdl Z) Z := by
  refine ⟨rfl, rfl, Z.X, 𝟙 _, 𝟙 _, ⟨fun x => ?_, fun T g _ => ⟨g, by simp, fun h hh => by simpa using hh⟩⟩,
    inferInstance, by simpa using isMap_id hp hW Z⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := Z.X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨⟨U, hU⟩, 1, hx, one_mem _, by simp [unitIdl]⟩

end Ident

end GlobalTheory.LocM.Inhab
