import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramConjugateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ConjPt

variable {S : Scheme.{0}} {R : Type} [CommRing R]

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : B →+* C) (b : A →+* B) :
    spMap a ≫ spMap b = spMap (a.comp b) := by
  rw [← Spec.map_comp]; rfl

/- English proof (translation)
Rewrite using `[← Category.assoc, spMap_spMap]`.
-/
theorem spMap_spMap_assoc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : B →+* C) (b : A →+* B)
    {T : Scheme.{0}} (g : Sp A ⟶ T) : spMap a ≫ spMap b ≫ g = spMap (a.comp b) ≫ g := by
  rw [← Category.assoc, spMap_spMap]

/- English proof (translation)
The claim follows from `Spec.map_id (CommRingCat.of A)`.
-/
theorem spMap_idR (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ :=
  Spec.map_id (CommRingCat.of A)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem algebraMap_dual (a : R) : algebraMap R (DualNumber R) a = TrivSqZeroExt.inl a := rfl

/- English proof (translation)
Apply the tactic sequence `ext a <;> simp [dualMap, algebraMap_dual]`.
-/
theorem dualMap_comp_algebraMap (f : R →+* R) :
    (dualMap f).comp (algebraMap R (DualNumber R)) = (algebraMap R (DualNumber R)).comp f := by
  ext a <;> simp [dualMap, algebraMap_dual]

/- English proof (translation)
Apply the tactic sequence `ext a <;> simp [dualMap, epsMul, algebraMap_dual]`.
-/
theorem dualMap_comp_epsMul (f : R →+* R) (c : R) :
    (dualMap f).comp (epsMul c) = (epsMul (f c)).comp (dualMap f) := by
  ext a <;> simp [dualMap, epsMul, algebraMap_dual]

/- English proof (translation)
Apply the tactic sequence `ext a <;> simp [dualMap, algebraMap_dual]`.
-/
theorem fst_comp_dualMap (f : R →+* R) :
    (TrivSqZeroExt.fstHom R R R).toRingHom.comp (dualMap f) = f.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  ext a <;> simp [dualMap, algebraMap_dual]

/- English proof (translation)
Apply the tactic sequence `ext a <;> simp [dualMap, hf, algebraMap_dual]`.
-/
theorem dualMap_comp_dualMap (f : R →+* R) (hf : ∀ a, f (f a) = a) :
    (dualMap f).comp (dualMap f) = RingHom.id _ := by
  ext a <;> simp [dualMap, hf, algebraMap_dual]

def trM (f : R →+* R) {x x' : Sp R ⟶ S} (hx : x' = spMap f ≫ x) : epsAt x' ⟶ epsAt x :=
  Over.homMk (spMap (dualMap f)) (by
    subst hx
    change spMap (dualMap f) ≫ spMap (algebraMap R (DualNumber R)) ≫ x =
      spMap (algebraMap R (DualNumber R)) ≫ spMap f ≫ x
    rw [spMap_spMap_assoc, spMap_spMap_assoc, dualMap_comp_algebraMap])

def tr (f : R →+* R) {x x' : Sp R ⟶ S} (hx : x' = spMap f ≫ x) {G : Over S} (v : epsAt x ⟶ G) : epsAt x' ⟶ G :=
  trM f hx ≫ v

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tr_left (f : R →+* R) {x x' : Sp R ⟶ S} (hx : x' = spMap f ≫ x) {G : Over S} (v : epsAt x ⟶ G) :
    (tr f hx v).left = spMap (dualMap f) ≫ v.left := rfl

variable {G : Over S} [GrpObj G] {x x' : Sp R ⟶ S}

/- English proof (translation)
The claim follows from `MonObj.comp_mul _ _ _`.
-/
theorem tr_mul (f : R →+* R) (hx : x' = spMap f ≫ x) (a b : epsAt x ⟶ G) :
    tr f hx (a * b) = tr f hx a * tr f hx b :=
  MonObj.comp_mul _ _ _

/- English proof (translation)
Rewrite using `[tr, Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (trM f hx ≫ toUnit _) (toUnit _)]`.
-/
theorem tr_one (f : R →+* R) (hx : x' = spMap f ≫ x) : tr f hx (1 : epsAt x ⟶ G) = 1 := by
  rw [tr, Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (trM f hx ≫ toUnit _) (toUnit _)]

def trHom (f : R →+* R) (hx : x' = spMap f ≫ x) : (epsAt x ⟶ G) →* (epsAt x' ⟶ G) where
  toFun := tr f hx
  map_one' := tr_one f hx
  map_mul' := tr_mul f hx

/- English proof (translation)
Use `map_list_prod (trHom (G := G) f hx) (List.ofFn u)` as an intermediate fact. Rewrite `this` using `[List.map_ofFn]`. Conclude with `this`.
-/
theorem tr_prod (f : R →+* R) (hx : x' = spMap f ≫ x) {n : ℕ} (u : Fin n → (epsAt x ⟶ G)) :
    tr f hx (List.ofFn u).prod = (List.ofFn fun i => tr f hx (u i)).prod := by
  have := map_list_prod (trHom (G := G) f hx) (List.ofFn u)
  rw [List.map_ofFn] at this
  exact this

/- English proof (translation)
Establish `h1 : (1 : Over.mk x' ⟶ G) = (Over.homMk (spMap f) hx.symm : Over.mk x' ⟶ Over.mk x) ≫ (1 : Over.mk x ⟶ G)`. Rewrite using `[Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]`. Unfold `IsTanAt at h ⊢`. Rewrite using `[h1, Over.comp_left, ← h, tr_left]`. Express the relevant statement in the definitionally equal form `spMap _ ≫ spMap (dualMap f) ≫ v.left = spMap f ≫ spMap _ ≫ v.left`.

Rewrite using `[spMap_spMap_assoc, spMap_spMap_assoc, fst_comp_dualMap]`.
-/
theorem isTanAt_tr (f : R →+* R) (hx : x' = spMap f ≫ x) {v : epsAt x ⟶ G} (h : IsTanAt G x v) :
    IsTanAt G x' (tr f hx v) := by
  have h1 : (1 : Over.mk x' ⟶ G) = (Over.homMk (spMap f) hx.symm : Over.mk x' ⟶ Over.mk x) ≫ (1 : Over.mk x ⟶ G) := by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
  unfold IsTanAt at h ⊢
  rw [h1, Over.comp_left, ← h, tr_left]
  change spMap _ ≫ spMap (dualMap f) ≫ v.left = spMap f ≫ spMap _ ≫ v.left
  rw [spMap_spMap_assoc, spMap_spMap_assoc, fst_comp_dualMap]

/- English proof (translation)
Use `⟨isTanAt_tr f hx h.1, fun a => ?_⟩` and prove the remaining obligations. Establish `h2 : (tr f hx v ≫ act.act a).left = spMap (dualMap f) ≫ (v ≫ act.act a).left`. Rewrite using `[tr, Category.assoc]`. Both sides reduce to the same expression. Rewrite using `[h2, h.2 a, tr_left, spMap_spMap_assoc, spMap_spMap_assoc, dualMap_comp_epsMul]`.
-/
theorem isEigVec_tr {O : Type} [CommRing O] (act : OAct O G) (f : R →+* R) (hx : x' = spMap f ≫ x) {τ : O →+* R}
    {v : epsAt x ⟶ G} (h : IsEigVec act x τ v) : IsEigVec act x' (f.comp τ) (tr f hx v) := by
  refine ⟨isTanAt_tr f hx h.1, fun a => ?_⟩
  have h2 : (tr f hx v ≫ act.act a).left = spMap (dualMap f) ≫ (v ≫ act.act a).left := by
    rw [tr, Category.assoc]; rfl
  rw [h2, h.2 a, tr_left, spMap_spMap_assoc, spMap_spMap_assoc, dualMap_comp_epsMul]

/- English proof (translation)
Take `⟨u, hu, rfl⟩` from `h`. Use `⟨fun i => tr f hx (u i), fun i => ?_, tr_prod f hx u⟩` and prove the remaining obligations. Rewrite using `[tr_left, hu, tr_left, spMap_spMap_assoc, spMap_spMap_assoc, dualMap_comp_epsMul]`.
-/
theorem isComb_tr (f : R →+* R) (hx : x' = spMap f ≫ x) {n : ℕ} {c : Fin n → R} {v : Fin n → (epsAt x ⟶ G)}
    {w : epsAt x ⟶ G} (h : IsComb c v w) : IsComb (fun i => f (c i)) (fun i => tr f hx (v i)) (tr f hx w) := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨fun i => tr f hx (u i), fun i => ?_, tr_prod f hx u⟩
  rw [tr_left, hu, tr_left, spMap_spMap_assoc, spMap_spMap_assoc, dualMap_comp_epsMul]

/- English proof (translation)
Establish `: f.comp f = RingHom.id R` using `RingHom.ext hf`. Rewrite using `[hx, spMap_spMap_assoc, this, spMap_idR, Category.id_comp]`.
-/
theorem back (f : R →+* R) (hf : ∀ a, f (f a) = a) (hx : x' = spMap f ≫ x) : x = spMap f ≫ x' := by
  have : f.comp f = RingHom.id R := RingHom.ext hf
  rw [hx, spMap_spMap_assoc, this, spMap_idR, Category.id_comp]

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[tr_left, tr_left, spMap_spMap_assoc, dualMap_comp_dualMap f hf, spMap_idR, Category.id_comp]`.
-/
theorem tr_tr (f : R →+* R) (hf : ∀ a, f (f a) = a) (hx : x' = spMap f ≫ x) (hx' : x = spMap f ≫ x')
    (v : epsAt x ⟶ G) : tr f hx' (tr f hx v) = v := by
  apply Over.OverMorphism.ext
  rw [tr_left, tr_left, spMap_spMap_assoc, dualMap_comp_dualMap f hf, spMap_idR, Category.id_comp]

/- English proof (translation)
Establish `hx'` using `back f hf hx`. Use `⟨fun i => isEigVec_tr act f hx (h.1 i), fun w hw => ?_⟩` and prove the remaining obligations. Establish `hw0 : IsEigVec act x τ (tr f hx' w)`. Use `isEigVec_tr act f hx' hw` as an intermediate fact. Establish `e : f.comp (f.comp τ) = τ` using `RingHom.ext fun a => hf _`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis. Take `⟨c, hc, hu⟩` from `h.2 _ hw0`. Use `⟨fun i => f (c i), ?_, fun c' hc' => ?_⟩` and prove the remaining obligations. Use `isComb_tr f hx hc` as an intermediate fact. Rewrite `this` using `[tr_tr f hf hx' hx]`. Then use the resulting hypothesis.

Establish `h3` using `isComb_tr f hx' hc'`. Simplify using `only [tr_tr f hf hx hx'] at h3`. Establish `h4` using `hu _ h3`. Use function extensionality and compare the values at `i`. Rewrite using `[← h4]`.

Conclude with `(hf _).symm`.
-/
theorem isEigFrame_tr {O : Type} [CommRing O] (act : OAct O G) (f : R →+* R) (hf : ∀ a, f (f a) = a)
    (hx : x' = spMap f ≫ x) {τ : O →+* R} {n : ℕ} {v : Fin n → (epsAt x ⟶ G)} (h : IsEigFrame act x τ v) :
    IsEigFrame act x' (f.comp τ) (fun i => tr f hx (v i)) := by
  have hx' := back f hf hx
  refine ⟨fun i => isEigVec_tr act f hx (h.1 i), fun w hw => ?_⟩
  have hw0 : IsEigVec act x τ (tr f hx' w) := by
    have := isEigVec_tr act f hx' hw
    have e : f.comp (f.comp τ) = τ := RingHom.ext fun a => hf _
    rwa [e] at this
  obtain ⟨c, hc, hu⟩ := h.2 _ hw0
  refine ⟨fun i => f (c i), ?_, fun c' hc' => ?_⟩
  · have := isComb_tr f hx hc
    rwa [tr_tr f hf hx' hx] at this
  · have h3 := isComb_tr f hx' hc'
    simp only [tr_tr f hf hx hx'] at h3
    have h4 := hu _ h3
    funext i
    rw [← h4]
    exact (hf _).symm

end GlobalTheory.CompanionTheory.Ar.Flat.ConjPt

namespace GlobalTheory.CompanionTheory.Ar.Flat

open ConjPt in

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c U τ φ s t hl hs y v w Γ Δ hfr hΓ hΔ`. Establish `hcc : ∀ z : ℂ, (starRingEnd ℂ) ((starRingEnd ℂ) z) = z` using `fun z => Complex.conj_conj z`. Take `⟨h1, h2, h3, h4⟩` from `hfr`. Establish `hy : under (spMap (starRingEnd ℂ) ≫ y) = spMap (starRingEnd ℂ) ≫ under y` using `Category.assoc _ _ _`. Establish `hcomp : ∀ {A : Type} [CommRing A] (g : A →+* ℂ), (starRingEnd ℂ).comp ((starRingEnd ℂ).comp g) = g` using `fun g => RingHom.ext fun a => hcc _`.

Set `v' : Vecs (spMap (starRingEnd ℂ) ≫ y) D.p` to `fun i => tr (starRingEnd ℂ) hy (v i)`. Set `w' : Vecs (spMap (starRingEnd ℂ) ≫ y) D.q` to `fun i => tr (starRingEnd ℂ) hy (w i)`. Establish `hfr' : IsFramed U τ s (spMap (starRingEnd ℂ) ≫ y) v' w'`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, h1, spMap_spMap, hcomp]`.

Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `h2 ⟨(spMap (starRingEnd ℂ)) a, by simp⟩`. Use `isEigFrame_tr Xo.univ.t.act (starRingEnd ℂ) hcc hy h3` as an intermediate fact. Establish `e : (starRingEnd ℂ).comp (((starRingEnd ℂ).comp s).comp (tauIn c τ)) = s.comp (tauIn c τ)` using `RingHom.ext fun a => hcc _`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.

Use `isEigFrame_tr Xo.univ.t.act (starRingEnd ℂ) hcc hy h4` as an intermediate fact. Establish `e : (starRingEnd ℂ).comp (((starRingEnd ℂ).comp s).comp (tauIn c (ComplexEmbedding.conjugate τ))) = s.comp (tauIn c (ComplexEmbedding.conjugate τ))` using `RingHom.ext fun a => hcc _`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `hΓ'` using `GlobalTheory.T.hodge_gram_conjugate _ Xo.univ.t.G Xo.univ.t.PP.L (under y) _ _ v v' Γ hy (fun a => tr_left _ hy _) hΓ`. Establish `hΔ'` using `GlobalTheory.T.hodge_gram_conjugate _ Xo.univ.t.G Xo.univ.t.PP.L (under y) _ _ w w' Δ hy (fun a => tr_left _ hy _) hΔ`.

Establish `hnat` using `hl.nat ℂ ℂ (starRingEnd ℂ) ((starRingEnd ℂ).comp s) y v w (spMap (starRingEnd ℂ) ≫ y) v' w' ⟨h1, h2, h3, h4⟩ rfl (fun i => tr_left _ hy _) (fun i => tr_left _ hy _)`. Establish `hm` using `hs _ v' w' _ _ hfr' hΓ' hΔ'`. Establish `hdet : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ), ‖(M.map star).det‖ = ‖M.det‖`. Introduce `n M`. Establish `: (M.map star).det = (starRingEnd ℂ) M.det`.

Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[this, RCLike.norm_conj]`. Rewrite `hm` using `[hnat, RCLike.norm_conj, hdet, hdet]`. Conclude with `hm`.
-/
theorem hasInfNorm_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (s : c.F →+* ℂ) (t : ℝ), IsLineFn U τ φ → HasInfNorm U τ φ s t → HasInfNorm U τ φ ((starRingEnd ℂ).comp s) t := by
  intro E _ _ _ H D l Xo c U τ φ s t hl hs y v w Γ Δ hfr hΓ hΔ
  have hcc : ∀ z : ℂ, (starRingEnd ℂ) ((starRingEnd ℂ) z) = z := fun z => Complex.conj_conj z
  obtain ⟨h1, h2, h3, h4⟩ := hfr
  have hy : under (spMap (starRingEnd ℂ) ≫ y) = spMap (starRingEnd ℂ) ≫ under y := Category.assoc _ _ _
  have hcomp : ∀ {A : Type} [CommRing A] (g : A →+* ℂ), (starRingEnd ℂ).comp ((starRingEnd ℂ).comp g) = g :=
    fun g => RingHom.ext fun a => hcc _
  let v' : Vecs (spMap (starRingEnd ℂ) ≫ y) D.p := fun i => tr (starRingEnd ℂ) hy (v i)
  let w' : Vecs (spMap (starRingEnd ℂ) ≫ y) D.q := fun i => tr (starRingEnd ℂ) hy (w i)
  have hfr' : IsFramed U τ s (spMap (starRingEnd ℂ) ≫ y) v' w' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Category.assoc, h1, spMap_spMap, hcomp]
    · rintro _ ⟨a, rfl⟩
      exact h2 ⟨(spMap (starRingEnd ℂ)) a, by simp⟩
    · have := isEigFrame_tr Xo.univ.t.act (starRingEnd ℂ) hcc hy h3
      have e : (starRingEnd ℂ).comp (((starRingEnd ℂ).comp s).comp (tauIn c τ)) = s.comp (tauIn c τ) :=
        RingHom.ext fun a => hcc _
      rwa [e] at this
    · have := isEigFrame_tr Xo.univ.t.act (starRingEnd ℂ) hcc hy h4
      have e : (starRingEnd ℂ).comp (((starRingEnd ℂ).comp s).comp (tauIn c (ComplexEmbedding.conjugate τ))) =
          s.comp (tauIn c (ComplexEmbedding.conjugate τ)) := RingHom.ext fun a => hcc _
      rwa [e] at this
  have hΓ' := GlobalTheory.T.hodge_gram_conjugate _ Xo.univ.t.G Xo.univ.t.PP.L (under y) _ _ v v' Γ hy (fun a => tr_left _ hy _) hΓ
  have hΔ' := GlobalTheory.T.hodge_gram_conjugate _ Xo.univ.t.G Xo.univ.t.PP.L (under y) _ _ w w' Δ hy (fun a => tr_left _ hy _) hΔ
  have hnat := hl.nat ℂ ℂ (starRingEnd ℂ) ((starRingEnd ℂ).comp s) y v w (spMap (starRingEnd ℂ) ≫ y) v' w'
    ⟨h1, h2, h3, h4⟩ rfl (fun i => tr_left _ hy _) (fun i => tr_left _ hy _)
  have hm := hs _ v' w' _ _ hfr' hΓ' hΔ'
  have hdet : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ), ‖(M.map star).det‖ = ‖M.det‖ := by
    intro n M
    have : (M.map star).det = (starRingEnd ℂ) M.det := by
      rw [RingHom.map_det]; rfl
    rw [this, RCLike.norm_conj]
  rw [hnat, RCLike.norm_conj, hdet, hdet] at hm
  exact hm

end GlobalTheory.CompanionTheory.Ar.Flat
