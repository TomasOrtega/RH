import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowFlatLocallyQuasiFinite
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FormallyUnramifiedMulInvertibleInteger
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.Tors

section Kernel
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

variable [BraidedCategory C] {A B : C} [GrpObj B] [IsCommMonObj B] {N : ℕ} {j : A ⟶ B}

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simp [Hom.one_def]`. Consider the case `succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]`.
-/
theorem comp_pow_id {Y : C} (y : Y ⟶ B) : y ≫ (𝟙 B) ^ N = y ^ N := by
  induction N with
  | zero => simp [Hom.one_def]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

/- English proof (translation)
Assemble the required witnesses or components as `⟨hp.lift y (toUnit Y) (by rw [comp_pow_id, hy, Hom.one_def]), hp.lift_fst _ _ _⟩`.
-/
theorem lift_of_torsion (hp : IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B]) {Y : C} (y : Y ⟶ B) (hy : y ^ N = 1) :
    ∃ z : Y ⟶ A, z ≫ j = y :=
  ⟨hp.lift y (toUnit Y) (by rw [comp_pow_id, hy, Hom.one_def]), hp.lift_fst _ _ _⟩

/- English proof (translation)
Rewrite using `[← comp_pow_id, Category.assoc, hp.w, Hom.one_def, ← Category.assoc, toUnit_unique (z ≫ toUnit A) (toUnit Y)]`.
-/
theorem torsion_of_comp (hp : IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B]) {Y : C} (z : Y ⟶ A) : (z ≫ j) ^ N = 1 := by
  rw [← comp_pow_id, Category.assoc, hp.w, Hom.one_def, ← Category.assoc, toUnit_unique (z ≫ toUnit A) (toUnit Y)]

/- English proof (translation)
Conclude with `⟨fun a b h => hp.hom_ext h (toUnit_unique _ _)⟩`.
-/
theorem mono_of_pullback (hp : IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B]) : Mono j := by
  exact ⟨fun a b h => hp.hom_ext h (toUnit_unique _ _)⟩

/- English proof (translation)
Use `mono_of_pullback hp` as an intermediate fact. Take `⟨e, he⟩` from `lift_of_torsion hp (1 : 𝟙_ C ⟶ B) (one_pow _)`. Take `⟨m, hm⟩` from `lift_of_torsion hp ((fst A A ≫ j) * (snd A A ≫ j)) (by rw [mul_pow, torsion_of_comp hp, torsion_of_comp hp, _root_.one_mul])`. Take `⟨n, hn⟩` from `lift_of_torsion hp (j⁻¹) (by have h := torsion_of_comp hp (𝟙 A); rw [Category.id_comp] at h; rw [inv_pow, h, inv_one])`. Take `⟨g, hg⟩` from `GlobalTheory.PointQuot.exists_grpObj_of_mono j e m n he hm hn`.

Use `⟨g, ⟨?_⟩, hg⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono j, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]`.
-/
theorem exists_kernel_grp (hp : IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B]) :
    ∃ (_ : GrpObj A) (_ : IsCommMonObj A), IsMonHom j := by
  have := mono_of_pullback hp
  obtain ⟨e, he⟩ := lift_of_torsion hp (1 : 𝟙_ C ⟶ B) (one_pow _)
  obtain ⟨m, hm⟩ := lift_of_torsion hp ((fst A A ≫ j) * (snd A A ≫ j))
    (by rw [mul_pow, torsion_of_comp hp, torsion_of_comp hp, _root_.one_mul])
  obtain ⟨n, hn⟩ := lift_of_torsion hp (j⁻¹)
    (by have h := torsion_of_comp hp (𝟙 A); rw [Category.id_comp] at h; rw [inv_pow, h, inv_one])
  obtain ⟨g, hg⟩ := GlobalTheory.PointQuot.exists_grpObj_of_mono j e m n he hm hn
  refine ⟨g, ⟨?_⟩, hg⟩
  rw [← cancel_mono j, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
    IsCommMonObj.mul_comm]

end Kernel

section Bridge
variable {S' S : Scheme.{0}} (x : S' ⟶ S) (G : Over S)

def toPull {Y : Over S'} (g : Over.mk (Y.hom ≫ x) ⟶ G) : Y ⟶ (Over.pullback x).obj G :=
  Over.homMk (pullback.lift g.left Y.hom (by simpa using Over.w g)) (pullback.lift_snd _ _ _)

/- English proof (translation)
The claim follows from `pullback.lift_fst _ _ _`.
-/
theorem toPull_fst {Y : Over S'} (g : Over.mk (Y.hom ≫ x) ⟶ G) :
    (toPull x G g).left ≫ pullback.fst G.hom x = g.left := pullback.lift_fst _ _ _

variable {x G} in
/- English proof (translation)
Use `ext`. Use `pullback.hom_ext h ?_` and prove the remaining obligations. Establish `h1` using `Over.w y`. Establish `h2` using `Over.w z`. Simplify using `only [Over.pullback_obj_hom] at h1 h2`.

Rewrite using `[h1, h2]`.
-/
theorem hom_ext_pull {Y : Over S'} {y z : Y ⟶ (Over.pullback x).obj G}
    (h : y.left ≫ pullback.fst G.hom x = z.left ≫ pullback.fst G.hom x) : y = z := by
  ext
  refine pullback.hom_ext h ?_
  have h1 := Over.w y
  have h2 := Over.w z
  simp only [Over.pullback_obj_hom] at h1 h2
  rw [h1, h2]

/- English proof (translation)
Apply `hom_ext_pull` to reduce the goal to its premises. Establish `h1 : ((Over.pullback x).map g).left ≫ pullback.fst G.hom x = pullback.fst _ x ≫ g.left` using `pullback.lift_fst _ _ _`. Establish `h2` using `toPull_fst x _ (𝟙 (Over.mk (Y.hom ≫ x)))`. Rewrite using `[toPull_fst, Over.comp_left, Category.assoc, h1, ← Category.assoc, h2]`. Simplify using the standard rewrite rules.
-/
theorem toPull_eq {Y : Over S'} (g : Over.mk (Y.hom ≫ x) ⟶ G) :
    toPull x G g = toPull x _ (𝟙 (Over.mk (Y.hom ≫ x))) ≫ (Over.pullback x).map g := by
  apply hom_ext_pull
  have h1 : ((Over.pullback x).map g).left ≫ pullback.fst G.hom x = pullback.fst _ x ≫ g.left :=
    pullback.lift_fst _ _ _
  have h2 := toPull_fst x _ (𝟙 (Over.mk (Y.hom ≫ x)))
  rw [toPull_fst, Over.comp_left, Category.assoc, h1, ← Category.assoc, h2]
  simp

def toPullHom [GrpObj G] (Y : Over S') : (Over.mk (Y.hom ≫ x) ⟶ G) →* (Y ⟶ (Over.pullback x).obj G) where
  toFun := toPull x G
  map_one' := by
    rw [toPull_eq, Functor.map_one, MonObj.comp_one]
  map_mul' g h := by
    rw [toPull_eq, toPull_eq x G g, toPull_eq x G h, Functor.map_mul, MonObj.comp_mul]

variable {x G} in
/- English proof (translation)
Use `ext`. Rewrite using `[← toPull_fst x G g, ← toPull_fst x G h, e]`.
-/
theorem toPull_inj {Y : Over S'} {g h : Over.mk (Y.hom ≫ x) ⟶ G} (e : toPull x G g = toPull x G h) : g = h := by
  ext
  rw [← toPull_fst x G g, ← toPull_fst x G h, e]

def ofPull {Y : Over S'} (y : Y ⟶ (Over.pullback x).obj G) : Over.mk (Y.hom ≫ x) ⟶ G :=
  Over.homMk (y.left ≫ pullback.fst G.hom x) (by
    have h1 := Over.w y
    simp only [Over.pullback_obj_hom] at h1
    simp [pullback.condition, reassoc_of% h1])

/- English proof (translation)
Apply `hom_ext_pull` to reduce the goal to its premises. Rewrite using `[toPull_fst]`. Both sides reduce to the same expression.
-/
theorem toPull_ofPull {Y : Over S'} (y : Y ⟶ (Over.pullback x).obj G) : toPull x G (ofPull x G y) = y := by
  apply hom_ext_pull
  rw [toPull_fst]
  rfl

end Bridge

section Props
variable {Z : Scheme.{0}} {A B : Over Z} [GrpObj B] [IsCommMonObj B] {N : ℕ} {j : A ⟶ B}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `U hU V hV e`. Use `haveI : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩`. Establish `h` using `f.finiteType_appLE hU hV e`. Use `letI := (f.appLE U V e).hom.toAlgebra`.

Conclude with `Algebra.FinitePresentation.of_finiteType.mp h`.
-/
theorem lofp_of_noeth {X Z : Scheme.{0}} [IsLocallyNoetherian Z] (f : X ⟶ Z) [LocallyOfFiniteType f] :
    LocallyOfFinitePresentation f := by
  constructor
  intro U hU V hV e
  haveI : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have h := f.finiteType_appLE hU hV e
  letI := (f.appLE U V e).hom.toAlgebra
  exact Algebra.FinitePresentation.of_finiteType.mp h

/- English proof (translation)
Establish `hl` using `hp.map (Over.forget Z)`. Establish `hA : (toUnit A).left = A.hom` using `by simpa using Over.w (toUnit A)`. Establish `hl' : IsPullback j.left A.hom ((𝟙 B) ^ N).left (η[B]).left` using `by rw [← hA]; exact hl`. Establish `hη : IsClosedImmersion (η[B]).left`. Establish `: IsClosedImmersion ((η[B]).left ≫ B.hom)`.

Establish `: (η[B]).left ≫ B.hom = 𝟙 _` using `by simpa using Over.w η[B]`. Rewrite using `[this]`. Use `infer_instance`. Conclude with `IsClosedImmersion.of_comp _ B.hom`. Establish `hj : IsClosedImmersion j.left` using `MorphismProperty.of_isPullback hl'.flip hη`.

Establish `hc : j.left ≫ B.hom = A.hom` using `Over.w j`. Establish `: LocallyOfFiniteType A.hom` using `by rw [← hc]; infer_instance`. Use `⟨MorphismProperty.of_isPullback hl' ‹_›, MorphismProperty.of_isPullback hl' ‹_›, ?_, ?_, lofp_of_noeth _⟩` and prove the remaining obligations. Rewrite using `[← hc]`. Use `infer_instance`.

Rewrite using `[← hc]`. Use `infer_instance`.
-/
theorem kernel_props [IsLocallyNoetherian Z] (hp : IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B])
    [Flat ((𝟙 B) ^ N).left] [LocallyQuasiFinite ((𝟙 B) ^ N).left] [Smooth B.hom] [IsSeparated B.hom]
    [QuasiCompact B.hom] :
    Flat A.hom ∧ LocallyQuasiFinite A.hom ∧ IsSeparated A.hom ∧ QuasiCompact A.hom ∧
      LocallyOfFinitePresentation A.hom := by
  have hl := hp.map (Over.forget Z)
  have hA : (toUnit A).left = A.hom := by simpa using Over.w (toUnit A)
  have hl' : IsPullback j.left A.hom ((𝟙 B) ^ N).left (η[B]).left := by rw [← hA]; exact hl
  have hη : IsClosedImmersion (η[B]).left := by
    have : IsClosedImmersion ((η[B]).left ≫ B.hom) := by
      have : (η[B]).left ≫ B.hom = 𝟙 _ := by simpa using Over.w η[B]
      rw [this]; infer_instance
    exact IsClosedImmersion.of_comp _ B.hom
  have hj : IsClosedImmersion j.left := MorphismProperty.of_isPullback hl'.flip hη
  have hc : j.left ≫ B.hom = A.hom := Over.w j
  have : LocallyOfFiniteType A.hom := by rw [← hc]; infer_instance
  refine ⟨MorphismProperty.of_isPullback hl' ‹_›, MorphismProperty.of_isPullback hl' ‹_›, ?_, ?_,
    lofp_of_noeth _⟩
  · rw [← hc]; infer_instance
  · rw [← hc]; infer_instance

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [Functor.map_one]`. Consider the case `succ n ih => rw [pow_succ, pow_succ, Functor.map_mul, ih, F.map_id]`.
-/
theorem map_pow_id {C D : Type*} [Category C] [Category D] [CartesianMonoidalCategory C]
    [CartesianMonoidalCategory D] (F : C ⥤ D) [F.Monoidal] (B : C) [GrpObj B] (n : ℕ) :
    F.map ((𝟙 B) ^ n) = (𝟙 (F.obj B)) ^ n := by
  induction n with
  | zero => simp [Functor.map_one]
  | succ n ih => rw [pow_succ, pow_succ, Functor.map_mul, ih, F.map_id]

/- English proof (translation)
Establish `hq` using `hp.map (Over.pullback c)`. Establish `hq2` using `hq.map (Over.forget W)`. Establish `e1 : FormallyUnramified ((𝟙 ((Over.pullback c).obj B)) ^ N).left` using `GlobalTheory.formallyUnramified_mulA W ((Over.pullback c).obj B) N hN`. Rewrite `e1` using `[← map_pow_id]`. Establish `h1 : FormallyUnramified ((Over.pullback c).map (toUnit A)).left` using `MorphismProperty.of_isPullback hq2 e1`.

Establish `h3` using `Over.w ((Over.pullback c).map (toUnit A))`. Establish `: IsIso ((Over.pullback c).obj (𝟙_ (Over Z))).hom` using `by show IsIso (pullback.snd (𝟙 Z) c) infer_instance`. Establish `: FormallyUnramified (pullback.snd A.hom c)` using `by show FormallyUnramified ((Over.pullback c).obj A).hom`. Rewrite using `[← h3]`. Conclude with `MorphismProperty.comp_mem @FormallyUnramified _ _ h1 inferInstance`.

Conclude with `Etale.of_formallyUnramified_of_flat _`.
-/
theorem kernel_base_etale {W : Scheme.{0}} (c : W ⟶ Z) (hp : IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B])
    (hN : IsUnit (N : Γ(W, ⊤))) [Flat A.hom] [LocallyOfFinitePresentation A.hom] :
    Etale (pullback.snd A.hom c) := by
  have hq := hp.map (Over.pullback c)
  have hq2 := hq.map (Over.forget W)
  have e1 : FormallyUnramified ((𝟙 ((Over.pullback c).obj B)) ^ N).left :=
    GlobalTheory.formallyUnramified_mulA W ((Over.pullback c).obj B) N hN
  rw [← map_pow_id] at e1
  have h1 : FormallyUnramified ((Over.pullback c).map (toUnit A)).left := MorphismProperty.of_isPullback hq2 e1
  have h3 := Over.w ((Over.pullback c).map (toUnit A))
  have : IsIso ((Over.pullback c).obj (𝟙_ (Over Z))).hom := by
    show IsIso (pullback.snd (𝟙 Z) c)
    infer_instance
  have : FormallyUnramified (pullback.snd A.hom c) := by
    show FormallyUnramified ((Over.pullback c).obj A).hom
    rw [← h3]
    exact MorphismProperty.comp_mem @FormallyUnramified _ _ h1 inferInstance
  exact Etale.of_formallyUnramified_of_flat _

end Props

section FieldPoints
variable {R : Type} [CommRing R] [IsDomain R]

/- English proof (translation)
Take `⟨⟨z, a⟩, rfl⟩` from `(Scheme.SpecToEquivOfField (FractionRing R) X).symm.surjective f`. Take `⟨⟨z', b⟩, rfl⟩` from `(Scheme.SpecToEquivOfField (FractionRing R) X).symm.surjective g`. Simplify using `only [Scheme.SpecToEquivOfField_symm_apply] at h hf hg ⊢`. Establish `hz : z = z'`. Simplify `h` using `only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]`.

Substitute `hz` using the available equality. Set `ψ` to `Spec.preimage (X.fromSpecResidueField z ≫ p)`. Establish `hψ : Spec.map ψ = X.fromSpecResidueField z ≫ p` using `Spec.map_preimage _`. Establish `ha : ψ ≫ a = CommRingCat.ofHom (algebraMap R (FractionRing R))` using `Spec.map_injective (by rw [Spec.map_comp, hψ, ← Category.assoc]; exact hf)`. Establish `hb : ψ ≫ b = CommRingCat.ofHom (algebraMap R (FractionRing R))` using `Spec.map_injective (by rw [Spec.map_comp, hψ, ← Category.assoc]; exact hg)`.

Establish `hpa : ∀ r, a.hom (ψ.hom r) = algebraMap R (FractionRing R) r` using `fun r => congrArg (fun φ => φ.hom r) ha`. Establish `hpb : ∀ r, b.hom (ψ.hom r) = algebraMap R (FractionRing R) r` using `fun r => congrArg (fun φ => φ.hom r) hb`. Establish `key : a = b`. Use extensionality with `c`. Take `⟨r, s, hs, e⟩` from `IsFractionRing.div_surjective (A := R) (a.hom c)`.

Establish `hs' : algebraMap R (FractionRing R) s ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (nonZeroDivisors.ne_zero hs)`. Establish `h1 : a.hom (ψ.hom s * c - ψ.hom r) = 0`. Rewrite using `[map_sub, map_mul, hpa, hpa, ← e]`. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules.

Establish `h2 : ψ.hom s * c - ψ.hom r = 0` using `(map_eq_zero a.hom).1 h1`. Establish `h3 : b.hom (ψ.hom s * c - ψ.hom r) = 0` using `by rw [h2, map_zero]`. Rewrite `h3` using `[map_sub, map_mul, hpb, hpb]`. Use `show a.hom c = b.hom c`. Rewrite using `[← e, div_eq_iff hs']`.

Take the linear combination `(-1 : FractionRing R) * h3`. Rewrite using `[key]`.
-/
theorem eq_of_same_point {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R))
    (f g : Spec (CommRingCat.of (FractionRing R)) ⟶ X) (hf : f ≫ p = (genPt R).hom) (hg : g ≫ p = (genPt R).hom)
    (u v : Spec (CommRingCat.of (FractionRing R))) (h : f u = g v) : f = g := by
  obtain ⟨⟨z, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField (FractionRing R) X).symm.surjective f
  obtain ⟨⟨z', b⟩, rfl⟩ := (Scheme.SpecToEquivOfField (FractionRing R) X).symm.surjective g
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h hf hg ⊢
  have hz : z = z' := by
    simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using h
  subst hz
  let ψ := Spec.preimage (X.fromSpecResidueField z ≫ p)
  have hψ : Spec.map ψ = X.fromSpecResidueField z ≫ p := Spec.map_preimage _
  have ha : ψ ≫ a = CommRingCat.ofHom (algebraMap R (FractionRing R)) :=
    Spec.map_injective (by rw [Spec.map_comp, hψ, ← Category.assoc]; exact hf)
  have hb : ψ ≫ b = CommRingCat.ofHom (algebraMap R (FractionRing R)) :=
    Spec.map_injective (by rw [Spec.map_comp, hψ, ← Category.assoc]; exact hg)
  have hpa : ∀ r, a.hom (ψ.hom r) = algebraMap R (FractionRing R) r := fun r =>
    congrArg (fun φ => φ.hom r) ha
  have hpb : ∀ r, b.hom (ψ.hom r) = algebraMap R (FractionRing R) r := fun r =>
    congrArg (fun φ => φ.hom r) hb
  have key : a = b := by
    ext c
    obtain ⟨r, s, hs, e⟩ := IsFractionRing.div_surjective (A := R) (a.hom c)
    have hs' : algebraMap R (FractionRing R) s ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (nonZeroDivisors.ne_zero hs)
    have h1 : a.hom (ψ.hom s * c - ψ.hom r) = 0 := by
      rw [map_sub, map_mul, hpa, hpa, ← e]
      field_simp
      simp
    have h2 : ψ.hom s * c - ψ.hom r = 0 := (map_eq_zero a.hom).1 h1
    have h3 : b.hom (ψ.hom s * c - ψ.hom r) = 0 := by rw [h2, map_zero]
    rw [map_sub, map_mul, hpb, hpb] at h3
    show a.hom c = b.hom c
    rw [← e, div_eq_iff hs']
    linear_combination (-1 : FractionRing R) * h3
  rw [key]

/- English proof (translation)
Set `ψ : R →+* Ω` to `(Spec.preimage q).hom`. Establish `hψ : Spec.map (CommRingCat.ofHom ψ) = q` using `Spec.map_preimage _`. Establish `hinjψ : Function.Injective ψ`. Set `u₀ : Spec (CommRingCat.of Ω)` to `⟨⊥, Ideal.isPrime_bot⟩`. Establish `h1 : (Spec.map (CommRingCat.ofHom ψ) u₀).asIdeal = ⊥`.

Rewrite using `[hψ]`. Conclude with `hq _`. Establish `h2 : (Spec.map (CommRingCat.ofHom ψ) u₀).asIdeal = Ideal.comap ψ ⊥` using `rfl`. Rewrite `h1` using `[h2]`. Conclude with `(RingHom.injective_iff_ker_eq_bot ψ).2 h1`.

Use `⟨IsFractionRing.lift hinjψ, ?_⟩` and prove the remaining obligations. Establish `ha : (IsFractionRing.lift hinjψ : FractionRing R →+* Ω).comp (algebraMap R (FractionRing R)) = ψ`. Use extensionality with `r`. Conclude with `IsFractionRing.lift_algebraMap hinjψ r`. Establish `e : CommRingCat.ofHom ψ = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ CommRingCat.ofHom (IsFractionRing.lift hinjψ : FractionRing R →+* Ω)`.

Rewrite using `[← CommRingCat.ofHom_comp, ha]`. Rewrite using `[← hψ, e, Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem lift_to_frac {Ω : Type} [Field Ω] (q : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R))
    (hq : ∀ u, (q u).asIdeal = ⊥) :
    ∃ a : FractionRing R →+* Ω, q = Spec.map (CommRingCat.ofHom a) ≫ (genPt R).hom := by
  let ψ : R →+* Ω := (Spec.preimage q).hom
  have hψ : Spec.map (CommRingCat.ofHom ψ) = q := Spec.map_preimage _
  have hinjψ : Function.Injective ψ := by
    let u₀ : Spec (CommRingCat.of Ω) := ⟨⊥, Ideal.isPrime_bot⟩
    have h1 : (Spec.map (CommRingCat.ofHom ψ) u₀).asIdeal = ⊥ := by
      rw [hψ]
      exact hq _
    have h2 : (Spec.map (CommRingCat.ofHom ψ) u₀).asIdeal = Ideal.comap ψ ⊥ := rfl
    rw [h2] at h1
    exact (RingHom.injective_iff_ker_eq_bot ψ).2 h1
  refine ⟨IsFractionRing.lift hinjψ, ?_⟩
  have ha : (IsFractionRing.lift hinjψ : FractionRing R →+* Ω).comp (algebraMap R (FractionRing R)) = ψ := by
    ext r
    exact IsFractionRing.lift_algebraMap hinjψ r
  have e : CommRingCat.ofHom ψ = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫
      CommRingCat.ofHom (IsFractionRing.lift hinjψ : FractionRing R →+* Ω) := by
    rw [← CommRingCat.ofHom_comp, ha]
  rw [← hψ, e, Spec.map_comp]
  rfl

/- English proof (translation)
Set `c : Spec (CommRingCat.of (AlgebraicClosure (X.residueField g))) ⟶ X` to `Spec.map (CommRingCat.ofHom (algebraMap (X.residueField g) (AlgebraicClosure (X.residueField g)))) ≫ X.fromSpecResidueField g`. Establish `hc : ∀ u, c u = g` using `fun u => (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)`. Take `⟨a, ha⟩` from `lift_to_frac (c ≫ p) (fun u => by rw [Scheme.Hom.comp_apply, hc]; exact hg)`. Conclude with `⟨_, inferInstance, inferInstance, a, c, ha, hc⟩`.
-/
theorem exists_geom_point {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (g : X) (hg : (p g).asIdeal = ⊥) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (a : FractionRing R →+* Ω) (c : Spec (CommRingCat.of Ω) ⟶ X),
      c ≫ p = Spec.map (CommRingCat.ofHom a) ≫ (genPt R).hom ∧ ∀ u, c u = g := by
  let c : Spec (CommRingCat.of (AlgebraicClosure (X.residueField g))) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField g) (AlgebraicClosure (X.residueField g)))) ≫
      X.fromSpecResidueField g
  have hc : ∀ u, c u = g := fun u =>
    (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply _ _)
  obtain ⟨a, ha⟩ := lift_to_frac (c ≫ p) (fun u => by rw [Scheme.Hom.comp_apply, hc]; exact hg)
  exact ⟨_, inferInstance, inferInstance, a, c, ha, hc⟩

end FieldPoints

section Main
variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] {T : Type} [CommGroup T]
  {S : Scheme.{0}} {G : Over S} {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ}

/- English proof (translation)
Establish `h : IsUnit (N : FractionRing R)`. Establish `h0 : (N : R) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Establish `h1 : algebraMap R (FractionRing R) (N : R) ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R _)).2 h0`. Rewrite `h1` using `[map_natCast]`. Conclude with `isUnit_iff_ne_zero.2 h1`.

Use `h.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom` as an intermediate fact. Simplify using `using this`.
-/
theorem isUnit_natCast_generic (hN : 1 ≤ N) :
    IsUnit (N : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)) := by
  have h : IsUnit (N : FractionRing R) := by
    have h0 : (N : R) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have h1 : algebraMap R (FractionRing R) (N : R) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 h0
    rw [map_natCast] at h1
    exact isUnit_iff_ne_zero.2 h1
  have := h.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
  simpa using this

/- English proof (translation)
Establish `hm` using `mono_of_pullback hp`. Establish `tors : ∀ {Y : Over (Spec (CommRingCat.of R))} (g : Over.mk (Y.hom ≫ x) ⟶ G), g ^ N = 1 → toPull x G g ^ N = 1` using `fun {Y} g h => by`. Use `map_pow (toPullHom x G Y) g N` as an intermediate fact. Rewrite `this` using `[h, map_one]`. Conclude with `this.symm`.

Establish `tors' : ∀ {Y : Over (Spec (CommRingCat.of R))} (g : Over.mk (Y.hom ≫ x) ⟶ G), toPull x G g ^ N = 1 → g ^ N = 1` using `fun {Y} g h => by`. Establish `h1` using `map_pow (toPullHom x G Y) g N`. Establish `h2 : toPullHom x G Y g = toPull x G g` using `rfl`. Rewrite `h1` using `[h2, h, ← map_one (toPullHom x G Y)]`. Conclude with `toPull_inj h1`.

Use `choose p0 hp0 using fun t => lift_of_torsion hp (toPull x G (τ t)) (tors _ (hτ t))`. Establish `hmul : ∀ s t, p0 (s * t) ≫ j = (p0 s * p0 t) ≫ j` using `fun s t => by`. Rewrite using `[hp0, MonObj.mul_comp, hp0, hp0, map_mul]`. Conclude with `map_mul (toPullHom x G (genPt R)) _ _`. Establish `hone : p0 1 ≫ j = 1 ≫ j`.

Rewrite using `[hp0, MonObj.one_comp, map_one]`. Conclude with `map_one (toPullHom x G (genPt R))`. Set `pt : T →* (genPt R ⟶ A)` to `{ toFun := p0 map_one' := (cancel_mono j).1 hone map_mul' := fun s t => (cancel_mono j).1 (hmul s t) }`. Set `i : A.left ⟶ G.left` to `j.left ≫ pullback.fst G.hom x`. Establish `hi : ∀ {Y : Over (Spec (CommRingCat.of R))} (g : Over.mk (Y.hom ≫ x) ⟶ G) (y : Y ⟶ A), y ≫ j = toPull x G g → y.left ≫ i = g.left` using `fun {Y} g y h => by`.

Rewrite using `[← toPull_fst x G g, ← h]`. Simplify using `[i]`. Establish `hi' : ∀ {Y : Over (Spec (CommRingCat.of R))} (g : Over.mk (Y.hom ≫ x) ⟶ G) (y : Y ⟶ A), y.left ≫ i = g.left → y ≫ j = toPull x G g` using `fun {Y} g y h => by`. Apply `hom_ext_pull` to reduce the goal to its premises. Rewrite using `[toPull_fst, ← h]`.

Simplify using `[i]`. Establish `inj : ∀ {Y : Over (Spec (CommRingCat.of R))} (y z : Y ⟶ A), y.left ≫ i = z.left ≫ i → y = z` using `fun y z h => by`. Rewrite using `[← cancel_mono j]`. Apply `hom_ext_pull` to reduce the goal to its premises. Simplify `h` using `[i]`.

Establish `ptl : ∀ t, (pt t).left ≫ i = (τ t).left` using `fun t => hi _ _ (hp0 t)`. Use `⟨{ G := A, flat := hflat, quasiFinite := hqf, separated := hsep, quasiCompact := hqc, finPres := hfp, pt := pt, pt_inj := ?_, pt_onto := ?_, gen_reduced := hred }, i, ?_, ptl⟩` and prove the remaining obligations. Introduce `s t u v h`. Establish `e : (pt s).left = (pt t).left` using `eq_of_same_point A.hom _ _ (Over.w _) (Over.w _) u v h`. Establish `e' : pt s = pt t` using `Over.OverMorphism.ext e`.

Apply `hinj` to reduce the goal to its premises. Apply `toPull_inj` to reduce the goal to its premises. Rewrite using `[← hp0, ← hp0]`. Conclude with `congrArg (· ≫ j) e'`. Introduce `g hg`.

Take `⟨Ω, _, _, a, c, hcov, hc⟩` from `exists_geom_point A.hom g hg`. Set `Y : Over (Spec (CommRingCat.of R))` to `Over.mk (Spec.map (CommRingCat.ofHom a) ≫ (genPt R).hom)`. Set `y : Y ⟶ A` to `Over.homMk c hcov`. Set `g0` to `ofPull x G (y ≫ j)`. Establish `hg0 : toPull x G g0 = y ≫ j` using `toPull_ofPull x G _`.

Establish `htor : g0 ^ N = 1` using `tors' g0 (by rw [hg0]; exact torsion_of_comp hp y)`. Establish `key : ∀ (X : Spec (CommRingCat.of Ω) ⟶ S) (_ : X = Spec.map (CommRingCat.ofHom a) ≫ (genPt R).hom ≫ x) (g : Over.mk X ⟶ G), g ^ N = 1 → ∃ t, g.left = Spec.map (CommRingCat.ofHom a) ≫ (τ t).left`. Introduce and unpack `_ rfl g hgN`. Conclude with `hsurj Ω a g hgN`. Take `⟨t, ht⟩` from `key _ (Category.assoc _ _ _) g0 htor`.

Set `z : Y ⟶ A` to `Over.homMk (Spec.map (CommRingCat.ofHom a) ≫ (pt t).left) (by`. Rewrite using `[Category.assoc]`. Conclude with `congrArg (fun w => Spec.map (CommRingCat.ofHom a) ≫ w) (Over.w (pt t)))`. Establish `hyz : y = z` using `inj y z (by show c ≫ i = (Spec.map (CommRingCat.ofHom a) ≫ (pt t).left) ≫ i`. Rewrite using `[Category.assoc, ptl, ← ht]`.

Conclude with `hi _ _ hg0.symm)`. Establish `hc2 : c = Spec.map (CommRingCat.ofHom a) ≫ (pt t).left` using `congrArg (fun w => w.left) hyz`. Set `u₀ : Spec (CommRingCat.of Ω)` to `⟨⊥, Ideal.isPrime_bot⟩`. Use `⟨t, Spec.map (CommRingCat.ofHom a) u₀, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← hc2, hc]`.

Use `{ isOver := ?_, mul := ?_, inj := ?_, kernel := ?_ }` and prove the remaining obligations. Use `show (j.left ≫ pullback.fst G.hom x) ≫ G.hom = A.hom ≫ x`. Establish `hj` using `Over.w j`. Simplify using `only [Over.pullback_obj_hom] at hj`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, hj]`.

Introduce `Y y z y₀ z₀ hy hz`. Establish `h1` using `hi' y₀ y hy.symm`. Establish `h2` using `hi' z₀ z hz.symm`. Use `(hi (y₀ * z₀) (y * z) ?_).symm` and prove the remaining obligations. Rewrite using `[MonObj.mul_comp, h1, h2]`.

Conclude with `(map_mul (toPullHom x G Y) y₀ z₀).symm`. Introduce `Y y z h`. Conclude with `inj y z h`. Introduce `Y g`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Take `⟨y, hy⟩` from `lift_of_torsion hp _ (tors g h)`. Conclude with `⟨y, hi g y hy⟩`. Introduce and unpack `⟨y, hy⟩`. Apply `tors'` to reduce the goal to its premises.

Rewrite using `[← hi' g y hy]`. Conclude with `torsion_of_comp hp y`.
-/
theorem exists_of_kernel [GrpObj G] [IsCommMonObj G]
    {A : Over (Spec (CommRingCat.of R))} [GrpObj A] [IsCommMonObj A]
    {j : A ⟶ (Over.pullback x).obj G} [IsMonHom j]
    (hp : IsPullback j (toUnit A) ((𝟙 ((Over.pullback x).obj G)) ^ N) η[(Over.pullback x).obj G])
    (hflat : Flat A.hom) (hqf : LocallyQuasiFinite A.hom) (hsep : IsSeparated A.hom) (hqc : QuasiCompact A.hom)
    (hfp : LocallyOfFinitePresentation A.hom) (hred : IsReduced (pullback A.hom (genPt R).hom))
    (τ : T →* (Over.mk ((genPt R).hom ≫ x) ⟶ G)) (hinj : Function.Injective τ) (hτ : ∀ t, τ t ^ N = 1)
    (hsurj : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (a : FractionRing R →+* Ω)
      (g : Over.mk (Spec.map (CommRingCat.ofHom a) ≫ (genPt R).hom ≫ x) ⟶ G), g ^ N = 1 →
      ∃ t, g.left = Spec.map (CommRingCat.ofHom a) ≫ (τ t).left) :
    ∃ (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i ∧ ∀ t, (Γ.pt t).left ≫ i = (τ t).left := by
  have hm := mono_of_pullback hp

  have tors : ∀ {Y : Over (Spec (CommRingCat.of R))} (g : Over.mk (Y.hom ≫ x) ⟶ G), g ^ N = 1 →
      toPull x G g ^ N = 1 := fun {Y} g h => by
    have := map_pow (toPullHom x G Y) g N
    rw [h, map_one] at this
    exact this.symm
  have tors' : ∀ {Y : Over (Spec (CommRingCat.of R))} (g : Over.mk (Y.hom ≫ x) ⟶ G), toPull x G g ^ N = 1 →
      g ^ N = 1 := fun {Y} g h => by
    have h1 := map_pow (toPullHom x G Y) g N
    have h2 : toPullHom x G Y g = toPull x G g := rfl
    rw [h2, h, ← map_one (toPullHom x G Y)] at h1
    exact toPull_inj h1
  choose p0 hp0 using fun t => lift_of_torsion hp (toPull x G (τ t)) (tors _ (hτ t))
  have hmul : ∀ s t, p0 (s * t) ≫ j = (p0 s * p0 t) ≫ j := fun s t => by
    rw [hp0, MonObj.mul_comp, hp0, hp0, map_mul]
    exact map_mul (toPullHom x G (genPt R)) _ _
  have hone : p0 1 ≫ j = 1 ≫ j := by
    rw [hp0, MonObj.one_comp, map_one]
    exact map_one (toPullHom x G (genPt R))
  let pt : T →* (genPt R ⟶ A) :=
    { toFun := p0
      map_one' := (cancel_mono j).1 hone
      map_mul' := fun s t => (cancel_mono j).1 (hmul s t) }
  let i : A.left ⟶ G.left := j.left ≫ pullback.fst G.hom x
  have hi : ∀ {Y : Over (Spec (CommRingCat.of R))} (g : Over.mk (Y.hom ≫ x) ⟶ G) (y : Y ⟶ A),
      y ≫ j = toPull x G g → y.left ≫ i = g.left := fun {Y} g y h => by
    rw [← toPull_fst x G g, ← h]; simp [i]
  have hi' : ∀ {Y : Over (Spec (CommRingCat.of R))} (g : Over.mk (Y.hom ≫ x) ⟶ G) (y : Y ⟶ A),
      y.left ≫ i = g.left → y ≫ j = toPull x G g := fun {Y} g y h => by
    apply hom_ext_pull
    rw [toPull_fst, ← h]; simp [i]
  have inj : ∀ {Y : Over (Spec (CommRingCat.of R))} (y z : Y ⟶ A), y.left ≫ i = z.left ≫ i → y = z := fun y z h => by
    rw [← cancel_mono j]
    apply hom_ext_pull
    simpa [i] using h
  have ptl : ∀ t, (pt t).left ≫ i = (τ t).left := fun t => hi _ _ (hp0 t)
  refine ⟨{ G := A, flat := hflat, quasiFinite := hqf, separated := hsep, quasiCompact := hqc, finPres := hfp,
            pt := pt, pt_inj := ?_, pt_onto := ?_, gen_reduced := hred }, i, ?_, ptl⟩
  · intro s t u v h
    have e : (pt s).left = (pt t).left := eq_of_same_point A.hom _ _ (Over.w _) (Over.w _) u v h
    have e' : pt s = pt t := Over.OverMorphism.ext e
    apply hinj
    apply toPull_inj
    rw [← hp0, ← hp0]
    exact congrArg (· ≫ j) e'
  · intro g hg
    obtain ⟨Ω, _, _, a, c, hcov, hc⟩ := exists_geom_point A.hom g hg
    let Y : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom a) ≫ (genPt R).hom)
    let y : Y ⟶ A := Over.homMk c hcov
    let g0 := ofPull x G (y ≫ j)
    have hg0 : toPull x G g0 = y ≫ j := toPull_ofPull x G _
    have htor : g0 ^ N = 1 := tors' g0 (by rw [hg0]; exact torsion_of_comp hp y)
    have key : ∀ (X : Spec (CommRingCat.of Ω) ⟶ S)
        (_ : X = Spec.map (CommRingCat.ofHom a) ≫ (genPt R).hom ≫ x) (g : Over.mk X ⟶ G), g ^ N = 1 →
        ∃ t, g.left = Spec.map (CommRingCat.ofHom a) ≫ (τ t).left := by
      rintro _ rfl g hgN
      exact hsurj Ω a g hgN
    obtain ⟨t, ht⟩ := key _ (Category.assoc _ _ _) g0 htor
    let z : Y ⟶ A := Over.homMk (Spec.map (CommRingCat.ofHom a) ≫ (pt t).left) (by
      rw [Category.assoc]
      exact congrArg (fun w => Spec.map (CommRingCat.ofHom a) ≫ w) (Over.w (pt t)))
    have hyz : y = z := inj y z (by
      show c ≫ i = (Spec.map (CommRingCat.ofHom a) ≫ (pt t).left) ≫ i
      rw [Category.assoc, ptl, ← ht]
      exact hi _ _ hg0.symm)
    have hc2 : c = Spec.map (CommRingCat.ofHom a) ≫ (pt t).left := congrArg (fun w => w.left) hyz
    let u₀ : Spec (CommRingCat.of Ω) := ⟨⊥, Ideal.isPrime_bot⟩
    refine ⟨t, Spec.map (CommRingCat.ofHom a) u₀, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hc2, hc]
  · refine { isOver := ?_, mul := ?_, inj := ?_, kernel := ?_ }
    · show (j.left ≫ pullback.fst G.hom x) ≫ G.hom = A.hom ≫ x
      have hj := Over.w j
      simp only [Over.pullback_obj_hom] at hj
      rw [Category.assoc, pullback.condition, ← Category.assoc, hj]
    · intro Y y z y₀ z₀ hy hz
      have h1 := hi' y₀ y hy.symm
      have h2 := hi' z₀ z hz.symm
      refine (hi (y₀ * z₀) (y * z) ?_).symm
      rw [MonObj.mul_comp, h1, h2]
      exact (map_mul (toPullHom x G Y) y₀ z₀).symm
    · intro Y y z h
      exact inj y z h
    · intro Y g
      constructor
      · intro h
        obtain ⟨y, hy⟩ := lift_of_torsion hp _ (tors g h)
        exact ⟨y, hi g y hy⟩
      · rintro ⟨y, hy⟩
        apply tors'
        rw [← hi' g y hy]
        exact torsion_of_comp hp y

end Main

/- English proof (translation)
Introduce `R _ _ _ _ T _ S G _ hG x N hN τ hinj hτ hsurj`. Establish `hcomm` using `hG.comm`. Establish `hB : IsSemiAbelian ((Over.pullback x).obj G)` using `ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback x G hG`. Use `hB.smooth` as an intermediate fact. Use `hB.separated` as an intermediate fact.

Use `hB.quasiCompact` as an intermediate fact. Use `hB.comm` as an intermediate fact. Take `⟨hfl, hqf⟩` from `GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow _ ((Over.pullback x).obj G) hB N (by omega)`. Establish `hp : IsPullback (pullback.fst ((𝟙 ((Over.pullback x).obj G)) ^ N) η[(Over.pullback x).obj G]) (toUnit (pullback ((𝟙 ((Over.pullback x).obj G)) ^ N) η[(Over.pullback x).obj G])) ((𝟙 ((Over.pullback x).obj G)) ^ N) η[(Over.pullback x).obj G]`. Establish `h` using `IsPullback.of_hasPullback ((𝟙 ((Over.pullback x).obj G)) ^ N) η[(Over.pullback x).obj G]`.

Rewrite `h` using `[toUnit_unique (pullback.snd _ _) (toUnit _)]`. Then use the resulting hypothesis. Take `⟨_, _, _⟩` from `exists_kernel_grp hp`. Take `⟨h1, h2, h3, h4, h5⟩` from `kernel_props hp`. Use `kernel_base_etale (genPt R).hom hp (isUnit_natCast_generic hN)` as an intermediate fact. Use `haveI : IsReduced (genPt R).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (FractionRing R))))`.

Establish `hred` using `GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd (pullback ((𝟙 ((Over.pullback x).obj G)) ^ N) η[(Over.pullback x).obj G]).hom (genPt R).hom)`. Conclude with `exists_of_kernel hp h1 h2 h3 h4 h5 hred τ hinj hτ hsurj`.
-/
theorem exists_qfGroup_torsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (T : Type) [CommGroup T] (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ), 1 ≤ N → ∀ τ : T →* (Over.mk ((genPt R).hom ≫ x) ⟶ G), Function.Injective τ → (∀ t, τ t ^ N = 1) → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (a : FractionRing R →+* Ω) (g : Over.mk (Spec.map (CommRingCat.ofHom a) ≫ (genPt R).hom ≫ x) ⟶ G), g ^ N = 1 → ∃ t, g.left = Spec.map (CommRingCat.ofHom a) ≫ (τ t).left) → ∃ (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i ∧ ∀ t, (Γ.pt t).left ≫ i = (τ t).left := by
  intro R _ _ _ _ T _ S G _ hG x N hN τ hinj hτ hsurj
  have hcomm := hG.comm
  have hB : IsSemiAbelian ((Over.pullback x).obj G) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback x G hG
  have := hB.smooth
  have := hB.separated
  have := hB.quasiCompact
  have := hB.comm
  obtain ⟨hfl, hqf⟩ := GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow _ ((Over.pullback x).obj G) hB N (by omega)
  have hp : IsPullback (pullback.fst ((𝟙 ((Over.pullback x).obj G)) ^ N) η[(Over.pullback x).obj G])
      (toUnit (pullback ((𝟙 ((Over.pullback x).obj G)) ^ N) η[(Over.pullback x).obj G]))
      ((𝟙 ((Over.pullback x).obj G)) ^ N) η[(Over.pullback x).obj G] := by
    have h := IsPullback.of_hasPullback ((𝟙 ((Over.pullback x).obj G)) ^ N) η[(Over.pullback x).obj G]
    rwa [toUnit_unique (pullback.snd _ _) (toUnit _)] at h
  obtain ⟨_, _, _⟩ := exists_kernel_grp hp
  obtain ⟨h1, h2, h3, h4, h5⟩ := kernel_props hp
  have := kernel_base_etale (genPt R).hom hp (isUnit_natCast_generic hN)
  haveI : IsReduced (genPt R).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (FractionRing R))))
  have hred := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd
    (pullback ((𝟙 ((Over.pullback x).obj G)) ^ N) η[(Over.pullback x).obj G]).hom (genPt R).hom)
  exact exists_of_kernel hp h1 h2 h3 h4 h5 hred τ hinj hτ hsurj

end GlobalTheory.CompanionTheory.Ar.BT.Tors
