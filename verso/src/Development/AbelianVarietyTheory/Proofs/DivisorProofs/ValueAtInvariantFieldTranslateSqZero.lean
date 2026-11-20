import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsBasisVerticalDerivations
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TvELeft
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VertCoeffRing

/- English proof (translation)
Introduce `p`. Use `haveI := p.isPrime`. Use `⟨(⟨p.asIdeal.comap (algebraMap B (DualNumber B)), Ideal.IsPrime.comap _⟩ : PrimeSpectrum B), ?_⟩` and prove the remaining obligations. Use `PrimeSpectrum.ext (Ideal.ext fun x => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(algebraMap B (DualNumber B)) x.fst ∈ p.asIdeal ↔ x ∈ p.asIdeal`.

Establish `hx : x = algebraMap B (DualNumber B) x.fst + TrivSqZeroExt.inr x.snd`. Apply the tactic sequence `ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]`. Establish `hn : (TrivSqZeroExt.inr x.snd : DualNumber B) ∈ p.asIdeal`. Apply `p.isPrime.mem_of_pow_mem 2` to reduce the goal to its premises. Rewrite using `[pow_two, TrivSqZeroExt.inr_mul_inr]`.

Conclude with `zero_mem _`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[hx]`. Conclude with `add_mem h hn`.

Introduce `h`. Establish `h2` using `sub_mem h hn`. Rewrite using `[show x - TrivSqZeroExt.inr x.snd = algebraMap B (DualNumber B) x.fst by` and apply the resulting hypothesis. Rewrite using `[sub_eq_iff_eq_add]`. Conclude with `hx] at h2`.
-/
theorem spMap_fstHom_surjective (B : Type) [CommRing B] :
    Function.Surjective (spMap (TrivSqZeroExt.fstHom B B B).toRingHom) := by
  intro p
  haveI := p.isPrime
  refine ⟨(⟨p.asIdeal.comap (algebraMap B (DualNumber B)), Ideal.IsPrime.comap _⟩ : PrimeSpectrum B), ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
  change (algebraMap B (DualNumber B)) x.fst ∈ p.asIdeal ↔ x ∈ p.asIdeal
  have hx : x = algebraMap B (DualNumber B) x.fst + TrivSqZeroExt.inr x.snd := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hn : (TrivSqZeroExt.inr x.snd : DualNumber B) ∈ p.asIdeal := by
    apply p.isPrime.mem_of_pow_mem 2
    rw [pow_two, TrivSqZeroExt.inr_mul_inr]
    exact zero_mem _
  constructor
  · intro h
    rw [hx]
    exact add_mem h hn
  · intro h
    have h2 := sub_mem h hn
    rwa [show x - TrivSqZeroExt.inr x.snd = algebraMap B (DualNumber B) x.fst by
      rw [sub_eq_iff_eq_add]; exact hx] at h2

/- English proof (translation)
Introduce `R _ G _ _ u dd hinv B _ _ e he z O h`. Use `set φ : R →+* B := algebraMap R B with hφ`. Establish `hz : z.left ≫ G.hom = spMap φ` using `Over.w z`. Establish `eφ : (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap B (DualNumber B)).comp φ`. Apply the tactic sequence `ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`.

Establish `hv : (tv u).left ≫ G.hom = spMap (algebraMap R (DualNumber R))` using `(Over.w (tv u)).trans (Category.comp_id _)`. Establish `h2 : (spMap (dualMap φ) ≫ (tv u).left) ≫ G.hom = (tEpsG (z.left ≫ G.hom)).hom` using `by show _ = spMap (algebraMap B (DualNumber B)) ≫ z.left ≫ G.hom`. Use `(Category.assoc _ _ _).trans ((congrArg (spMap (dualMap φ) ≫ ·) hv).trans ?_)` and prove the remaining obligations. Rewrite using `[hz, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, eφ]`. Set `g' : tEpsG (z.left ≫ G.hom) ⟶ G` to `Over.homMk (spMap (algebraMap B (DualNumber B)) ≫ z.left) (Category.assoc _ _ _)`.

Set `v' : tEpsG (z.left ≫ G.hom) ⟶ G` to `Over.homMk (spMap (dualMap φ) ≫ (tv u).left) h2`. Establish `htr : IsTr G φ z.left u (g' * v').left` using `⟨g', v', rfl, rfl, rfl⟩`. Establish `hk : ∀ (t : B) (ht : t * t = 0), ∃ kt : Chart.sp (R₀` using `R) B ⟶ tEpsG (z.left ≫ G.hom), kt.left = spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) t ht).toRingHom ∧ kt ≫ g' = z ∧ kt ≫ v' = Chart.spMap (GlobalTheory.SqZero.epsTo R t ht) ≫ tvE u := by`. Introduce `t ht`. Establish `hτa : (GlobalTheory.SqZero.dualTo (AlgHom.id R B) t ht).toRingHom.comp (algebraMap B (DualNumber B)) = RingHom.id B`.

Use extensionality with `b`. Simplify using `[GlobalTheory.SqZero.dualTo_apply, TrivSqZeroExt.algebraMap_eq_inl]`. Establish `hsp : spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) t ht).toRingHom ≫ spMap (algebraMap B (DualNumber B)) = 𝟙 _`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, hτa, CommRingCat.ofHom_id, Spec.map_id]`. Use `⟨Over.homMk (spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) t ht).toRingHom) ?_, rfl, ?_, ?_⟩` and prove the remaining obligations.

Use `show spMap _ ≫ spMap (algebraMap B (DualNumber B)) ≫ z.left ≫ G.hom = _`. Rewrite using `[← Category.assoc, hsp, Category.id_comp]`. Conclude with `hz`. Apply `Over.OverMorphism.ext show spMap _ ≫ spMap (algebraMap B (DualNumber B)) ≫ z.left = z.left` to reduce the goal to its premises. Rewrite using `[← Category.assoc, hsp, Category.id_comp]`.

Apply `Over.OverMorphism.ext show spMap _ ≫ spMap (dualMap φ) ≫ (tv u).left = (Chart.spMap (GlobalTheory.SqZero.epsTo R t ht)).left ≫ (tv u).left` to reduce the goal to its premises. Rewrite using `[Chart.spMap_left, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 3`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Simplify using `[GlobalTheory.SqZero.dualTo_apply, GlobalTheory.SqZero.epsTo, dualMap, hφ, TrivSqZeroExt.algebraMap_eq_inl, Algebra.smul_def]`.

Take `⟨k, hkl, hkg, hkv⟩` from `hk e he`. Take `⟨k0, hk0l, hk0g, hk0v⟩` from `hk 0 (mul_zero 0)`. Establish `hone : Chart.spMap (GlobalTheory.SqZero.epsTo R (0 : B) (mul_zero 0)) ≫ tvE u = 1`. Set `K : Chart.sp (R₀` to `R) B ⟶ overAt (𝟙 (Sp R)) (DualNumber R) := Over.homMk (spMap (GlobalTheory.SqZero.epsTo R (0 : B) (mul_zero 0)).toRingHom) (by show _ ≫ spMap (algebraMap R (DualNumber R)) ≫ 𝟙 _ = spMap φ`. Rewrite using `[Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.

Use `congr 2`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Simplify using `[GlobalTheory.SqZero.epsTo, GlobalTheory.SqZero.dualTo_apply, TrivSqZeroExt.algebraMap_eq_inl, hφ])`. Establish `e1 : Chart.spMap (GlobalTheory.SqZero.epsTo R (0 : B) (mul_zero 0)) ≫ tvE u = K ≫ smT (𝟙 (Sp R)) 0 (tv u)`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Use `show (Chart.spMap _).left ≫ (tv u).left = spMap _ ≫ (smT (𝟙 (Sp R)) 0 (tv u)).left`. Rewrite using `[smT_left, Chart.spMap_left, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 3`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Simplify using `[GlobalTheory.SqZero.epsTo, GlobalTheory.SqZero.dualTo_apply, epsMul]`.

Rewrite using `[e1, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem, MonObj.comp_one]`. Establish `hp : (Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ tvE u) * z = k ≫ (g' * v')`. Rewrite using `[MonObj.comp_mul, hkg, hkv, mul_comm]`. Establish `hp0 : k0 ≫ (g' * v') = z`. Rewrite using `[MonObj.comp_mul, hk0g, hk0v, hone, _root_.mul_one]`.

Establish `hfst : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ (g' * v').left = z.left`. Use `congrArg (fun q => q.left) hp0` as an intermediate fact. Simplify using `only [Over.comp_left, hk0l] at this`. Establish `hfh : (GlobalTheory.SqZero.dualTo (AlgHom.id R B) (0 : B) (mul_zero 0)).toRingHom = (TrivSqZeroExt.fstHom B B B).toRingHom` using `RingHom.ext fun a => by`. Simplify using `[GlobalTheory.SqZero.dualTo_apply]`.

Rewrite using `[← hfh]`. Conclude with `this`. Establish `hw : ⊤ ≤ (g' * v').left ⁻¹ᵁ O`. Introduce `p _`. Take `⟨q, rfl⟩` from `spMap_fstHom_surjective B p`.

Rewrite `h` using `[← hfst]`. Conclude with `h (Set.mem_univ q)`. Establish `hpl : ((Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ tvE u) * z).left = spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) e he).toRingHom ≫ (g' * v').left`. Rewrite using `[hp, Over.comp_left, hkl]`. Establish `h' : ⊤ ≤ ((Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ tvE u) * z).left ⁻¹ᵁ O`.

Rewrite using `[hpl]`. Introduce `q _`. Conclude with `hw (Set.mem_univ _)`. Use `⟨h', fun f => ?_⟩` and prove the remaining obligations. Establish `hval : valR (g' * v').left O f = evalPt (g' * v').left O hw f`.

Unfold `valR`. Rewrite using `[dif_pos hw]`. Both sides reduce to the same expression. Establish `hvalz : valR z.left O (dd O f) = evalPt z.left O h (dd O f)`. Unfold `valR`.

Rewrite using `[dif_pos h]`. Both sides reduce to the same expression. Establish `hsnd` using `hinv.2 B φ z.left (g' * v').left O f hz h htr`. Rewrite `hsnd` using `[hval, hvalz]`. Establish `key : ∀ (y : Sp B ⟶ G.left) (hy : ⊤ ≤ y ⁻¹ᵁ O), spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) e he).toRingHom ≫ (g' * v').left = y → evalPt y O hy f = (evalPt (g' * v').left O hw f).fst + (evalPt (g' * v').left O hw f).snd * e`.

Introduce and unpack `y hy rfl`. Rewrite using `[evalPt_spMap_comp _ _ O hw hy f]`. Conclude with `GlobalTheory.SqZero.dualTo_apply _ _ _ _`. Establish `key0 : ∀ (y : Sp B ⟶ G.left) (hy : ⊤ ≤ y ⁻¹ᵁ O), spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ (g' * v').left = y → evalPt y O hy f = (evalPt (g' * v').left O hw f).fst`. Introduce and unpack `y hy rfl`.

Conclude with `evalPt_spMap_comp _ _ O hw hy f`. Rewrite using `[key _ h' hpl.symm, key0 _ h hfst, hsnd]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem evalPt_tvE_mul : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {u : TanM (𝟙 (Sp R)) G} {dd : Fld G.left}, IsInv G u dd → ∀ {B : Type} [CommRing B] [Algebra R B]
    (e : B) (he : e * e = 0) (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O),
    ∃ h' : ⊤ ≤ ((ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ GlobalTheory.VertCoeffRing.tvE u) * z).left ⁻¹ᵁ O, ∀ f,
      GlobalTheory.TangentOrigin.evalPt _ O h' f = GlobalTheory.TangentOrigin.evalPt z.left O h f + e * GlobalTheory.TangentOrigin.evalPt z.left O h (dd O f) := by
  intro R _ G _ _ u dd hinv B _ _ e he z O h
  set φ : R →+* B := algebraMap R B with hφ
  have hz : z.left ≫ G.hom = spMap φ := Over.w z
  have eφ : (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap B (DualNumber B)).comp φ := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hv : (tv u).left ≫ G.hom = spMap (algebraMap R (DualNumber R)) :=
    (Over.w (tv u)).trans (Category.comp_id _)
  have h2 : (spMap (dualMap φ) ≫ (tv u).left) ≫ G.hom = (tEpsG (z.left ≫ G.hom)).hom := by
    show _ = spMap (algebraMap B (DualNumber B)) ≫ z.left ≫ G.hom
    refine (Category.assoc _ _ _).trans ((congrArg (spMap (dualMap φ) ≫ ·) hv).trans ?_)
    rw [hz, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, eφ]
  let g' : tEpsG (z.left ≫ G.hom) ⟶ G :=
    Over.homMk (spMap (algebraMap B (DualNumber B)) ≫ z.left) (Category.assoc _ _ _)
  let v' : tEpsG (z.left ≫ G.hom) ⟶ G := Over.homMk (spMap (dualMap φ) ≫ (tv u).left) h2
  have htr : IsTr G φ z.left u (g' * v').left := ⟨g', v', rfl, rfl, rfl⟩

  have hk : ∀ (t : B) (ht : t * t = 0), ∃ kt : Chart.sp (R₀ := R) B ⟶ tEpsG (z.left ≫ G.hom),
      kt.left = spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) t ht).toRingHom ∧ kt ≫ g' = z ∧
        kt ≫ v' = Chart.spMap (GlobalTheory.SqZero.epsTo R t ht) ≫ tvE u := by
    intro t ht
    have hτa : (GlobalTheory.SqZero.dualTo (AlgHom.id R B) t ht).toRingHom.comp (algebraMap B (DualNumber B)) =
        RingHom.id B := by
      ext b
      simp [GlobalTheory.SqZero.dualTo_apply, TrivSqZeroExt.algebraMap_eq_inl]
    have hsp : spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) t ht).toRingHom ≫ spMap (algebraMap B (DualNumber B)) =
        𝟙 _ := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hτa, CommRingCat.ofHom_id, Spec.map_id]
    refine ⟨Over.homMk (spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) t ht).toRingHom) ?_, rfl, ?_, ?_⟩
    · show spMap _ ≫ spMap (algebraMap B (DualNumber B)) ≫ z.left ≫ G.hom = _
      rw [← Category.assoc, hsp, Category.id_comp]
      exact hz
    · apply Over.OverMorphism.ext
      show spMap _ ≫ spMap (algebraMap B (DualNumber B)) ≫ z.left = z.left
      rw [← Category.assoc, hsp, Category.id_comp]
    · apply Over.OverMorphism.ext
      show spMap _ ≫ spMap (dualMap φ) ≫ (tv u).left = (Chart.spMap (GlobalTheory.SqZero.epsTo R t ht)).left ≫ (tv u).left
      rw [Chart.spMap_left, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      refine RingHom.ext fun a => ?_
      simp [GlobalTheory.SqZero.dualTo_apply, GlobalTheory.SqZero.epsTo, dualMap, hφ, TrivSqZeroExt.algebraMap_eq_inl, Algebra.smul_def]
  obtain ⟨k, hkl, hkg, hkv⟩ := hk e he
  obtain ⟨k0, hk0l, hk0g, hk0v⟩ := hk 0 (mul_zero 0)

  have hone : Chart.spMap (GlobalTheory.SqZero.epsTo R (0 : B) (mul_zero 0)) ≫ tvE u = 1 := by
    let K : Chart.sp (R₀ := R) B ⟶ overAt (𝟙 (Sp R)) (DualNumber R) :=
      Over.homMk (spMap (GlobalTheory.SqZero.epsTo R (0 : B) (mul_zero 0)).toRingHom) (by
        show _ ≫ spMap (algebraMap R (DualNumber R)) ≫ 𝟙 _ = spMap φ
        rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        refine RingHom.ext fun a => ?_
        simp [GlobalTheory.SqZero.epsTo, GlobalTheory.SqZero.dualTo_apply, TrivSqZeroExt.algebraMap_eq_inl, hφ])
    have e1 : Chart.spMap (GlobalTheory.SqZero.epsTo R (0 : B) (mul_zero 0)) ≫ tvE u =
        K ≫ smT (𝟙 (Sp R)) 0 (tv u) := by
      apply Over.OverMorphism.ext
      show (Chart.spMap _).left ≫ (tv u).left = spMap _ ≫ (smT (𝟙 (Sp R)) 0 (tv u)).left
      rw [smT_left, Chart.spMap_left, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      refine RingHom.ext fun a => ?_
      simp [GlobalTheory.SqZero.epsTo, GlobalTheory.SqZero.dualTo_apply, epsMul]
    rw [e1, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem, MonObj.comp_one]
  have hp : (Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ tvE u) * z = k ≫ (g' * v') := by
    rw [MonObj.comp_mul, hkg, hkv, mul_comm]
  have hp0 : k0 ≫ (g' * v') = z := by
    rw [MonObj.comp_mul, hk0g, hk0v, hone, _root_.mul_one]
  have hfst : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ (g' * v').left = z.left := by
    have := congrArg (fun q => q.left) hp0
    simp only [Over.comp_left, hk0l] at this
    have hfh : (GlobalTheory.SqZero.dualTo (AlgHom.id R B) (0 : B) (mul_zero 0)).toRingHom =
        (TrivSqZeroExt.fstHom B B B).toRingHom := RingHom.ext fun a => by
      simp [GlobalTheory.SqZero.dualTo_apply]
    rw [← hfh]
    exact this
  have hw : ⊤ ≤ (g' * v').left ⁻¹ᵁ O := by
    intro p _
    obtain ⟨q, rfl⟩ := spMap_fstHom_surjective B p
    rw [← hfst] at h
    exact h (Set.mem_univ q)
  have hpl : ((Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ tvE u) * z).left =
      spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) e he).toRingHom ≫ (g' * v').left := by
    rw [hp, Over.comp_left, hkl]
  have h' : ⊤ ≤ ((Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ tvE u) * z).left ⁻¹ᵁ O := by
    rw [hpl]
    intro q _
    exact hw (Set.mem_univ _)
  refine ⟨h', fun f => ?_⟩
  have hval : valR (g' * v').left O f = evalPt (g' * v').left O hw f := by
    unfold valR; rw [dif_pos hw]; rfl
  have hvalz : valR z.left O (dd O f) = evalPt z.left O h (dd O f) := by
    unfold valR; rw [dif_pos h]; rfl
  have hsnd := hinv.2 B φ z.left (g' * v').left O f hz h htr
  rw [hval, hvalz] at hsnd
  have key : ∀ (y : Sp B ⟶ G.left) (hy : ⊤ ≤ y ⁻¹ᵁ O),
      spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) e he).toRingHom ≫ (g' * v').left = y →
      evalPt y O hy f = (evalPt (g' * v').left O hw f).fst + (evalPt (g' * v').left O hw f).snd * e := by
    rintro y hy rfl
    rw [evalPt_spMap_comp _ _ O hw hy f]
    exact GlobalTheory.SqZero.dualTo_apply _ _ _ _
  have key0 : ∀ (y : Sp B ⟶ G.left) (hy : ⊤ ≤ y ⁻¹ᵁ O),
      spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ (g' * v').left = y →
      evalPt y O hy f = (evalPt (g' * v').left O hw f).fst := by
    rintro y hy rfl
    exact evalPt_spMap_comp _ _ O hw hy f
  rw [key _ h' hpl.symm, key0 _ h hfst, hsnd]
  ring

end GlobalTheory.VertCoeffRing
