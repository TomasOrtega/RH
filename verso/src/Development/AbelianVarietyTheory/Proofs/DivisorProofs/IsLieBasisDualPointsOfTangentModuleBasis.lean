import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
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

noncomputable section
namespace GlobalTheory.VertCoeffRing

/- English proof (translation)
Introduce `R _ G _ _ n v`. Establish `hE : (overAt (𝟙 (Sp R)) (DualNumber R)).hom = (epsR R).hom`. Simplify using `[epsR, overAt]`. Set `e : epsR R ⟶ overAt (𝟙 (Sp R)) (DualNumber R)` to `Over.homMk (𝟙 _) (by simp [hE])`. Set `f : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ epsR R` to `Over.homMk (𝟙 _) (by simp [hE])`.

Establish `hfe : f ≫ e = 𝟙 _` using `Over.OverMorphism.ext (by simp [e, f])`. Establish `hef : e ≫ f = 𝟙 _` using `Over.OverMorphism.ext (by simp [e, f])`. Establish `htv : ∀ x : TanM (𝟙 (Sp R)) G, tvE x = e ≫ tv x`. Introduce `x`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Use `first`. Consider the case `(simp only [e, Over.comp_left, Over.homMk_left, Category.id_comp]; exact tvE_left x)`. Consider the case `simp [e, tvE_left x]`. Establish `hadd : ∀ x y : TanM (𝟙 (Sp R)) G, tvE (x + y) = tvE x * tvE y`. Introduce `x y`.

Rewrite using `[htv, htv, htv, PullbackSections.tv_add, MonObj.comp_mul]`. Establish `hzero : tvE (0 : TanM (𝟙 (Sp R)) G) = 1`. Rewrite using `[htv, PullbackSections.tv_zero, MonObj.comp_one]`. Establish `hsmul : ∀ (a : R) (x : TanM (𝟙 (Sp R)) G), (tvE (a • x)).left = spMap (epsScaleR a) ≫ (tvE x).left`. Introduce `a x`.

Rewrite using `[tvE_left, tvE_left, PullbackSections.tv_smul]`. Use `first`. Consider the case `rfl`. Consider the case `(simp only [smT.eq_1, Formalism.L2.Pj.homAt.eq_1, Over.comp_left, Over.homMk_left, tm.eq_1, epsScaleR.eq_1]; rfl)`. Establish `hinj : ∀ x y : TanM (𝟙 (Sp R)) G, tvE x = tvE y → x = y`.

Introduce `x y h`. Apply `PullbackSections.tanM_ext` to reduce the goal to its premises. Establish `h'` using `congrArg (fun t => f ≫ t) h`. Simplify `h'` using `[htv, ← Category.assoc, hfe]`. Establish `hsum : ∀ (c : Fin n → R) (s : Finset (Fin n)), tvE (∑ i ∈ s, c i • v i) = ∏ i ∈ s, tvE (c i • v i)`.

Introduce `c s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hzero`. Consider the case `@insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hadd, ih]`. Establish `hcomb : ∀ (c : Fin n → R) (w : epsR R ⟶ G), IsLieComb c (fun a => tvE (v a)) w ↔ w = tvE (∑ i, c i • v i)`.

Introduce `c w`. Rewrite using `[IsLieComb.eq_1, hsum]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Rewrite using `[List.prod_ofFn]`.

Use `Finset.prod_congr rfl fun i _ => Over.OverMorphism.ext ?_` and prove the remaining obligations. Rewrite using `[hu i, hsmul]`. Introduce and unpack `rfl`. Conclude with `⟨fun i => tvE (c i • v i), fun i => hsmul _ _, by rw [List.prod_ofFn]⟩`. Establish `hfa : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R`.

Use extensionality with `r`. Simplify using the standard rewrite rules. Establish `hdual : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _`. Simplify using `only [spMap.eq_1, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hfa, CommRingCat.ofHom_id, Spec.map_id]`. Apply the tactic sequence `all_goals rfl`.

Establish `hz : spMap (epsScaleR (0 : R)) = spMap (algebraMap R (DualNumber R)) ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom`. Establish `h0 : epsScaleR (0 : R) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom`. Use `RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_` and prove the remaining obligations. Apply the tactic sequence `all_goals first`. Consider the case `(simp [epsScaleR]; done)`.

Consider the case `(simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]; done)`. Consider the case `(simp [epsScaleR.eq_1, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fstHom_apply, TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]; done)`. Consider the case `rfl`. Consider the case `(simp [epsScaleR]; rfl)`. Rewrite using `[h0]`.

Simplify using `only [spMap.eq_1, CommRingCat.ofHom_comp, Spec.map_comp]`. Establish `hu : (toUnit (overAt (𝟙 (Sp R)) (DualNumber R))).left = spMap (algebraMap R (DualNumber R))` using `by first`. Consider the case `simp [overAt]`. Consider the case `(have h := Over.w (toUnit (overAt (𝟙 (Sp R)) (DualNumber R))); simpa [overAt] using h)`. Establish `hone : (1 : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G).left = spMap (algebraMap R (DualNumber R)) ≫ (η : 𝟙_ (Over (Sp R)) ⟶ G).left`.

Combine the equalities or inequalities in the displayed calculation. Establish `key : ∀ g : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G, smT (𝟙 (Sp R)) 0 g = 1 ↔ IsTangent (e ≫ g)`. Introduce `g`. Rewrite using `[IsTangent.eq_1]`. Establish `hl : (smT (𝟙 (Sp R)) 0 g).left = spMap (algebraMap R (DualNumber R)) ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ g.left`.

Rewrite using `[← Category.assoc, ← hz]`. Use `first`. Consider the case `rfl`. Consider the case `(simp only [smT.eq_1, Formalism.L2.Pj.homAt.eq_1, Over.comp_left, Over.homMk_left, tm.eq_1, epsScaleR.eq_1]; rfl)`. Establish `he : ∀ t : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G, spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (e ≫ t).left = spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ t.left`.

Introduce `t`. Simplify using `[e]`. Rewrite using `[he]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h2` using `congrArg Over.Hom.left h`. Rewrite `h2` using `[hl, hone]`. Establish `h3` using `congrArg (fun t => spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ t) h2`. Simplify `h3` using `only [← Category.assoc, hdual, Category.id_comp]`. Introduce `h`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[hl, hone, h]`. Establish `htan : ∀ x, IsTangent (tvE x)` using `fun x => by`. Rewrite using `[htv]`. Conclude with `(key (tv x)).1 (PullbackSections.tv_mem x)`.

Establish `hsurj : ∀ w : epsR R ⟶ G, IsTangent w → ∃ x, tvE x = w`. Introduce `w hw`. Establish `hw' : IsTangent (e ≫ (f ≫ w))` using `by rwa [← Category.assoc, hef, Category.id_comp]`. Use `⟨PullbackSections.mkT (f ≫ w) ((key _).2 hw'), ?_⟩` and prove the remaining obligations. Rewrite using `[htv, PullbackSections.tv_mkT, ← Category.assoc, hef, Category.id_comp]`.

Rewrite using `[IsLieBasis.eq_1]`. Use `⟨fun i => htan (v i), fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `hsurj w hw`. Use `⟨⇑(v.repr x), (hcomb _ _).2 ?_, fun c hc => ?_⟩` and prove the remaining obligations. Rewrite using `[v.sum_repr]`.

Establish `h` using `hinj _ _ ((hcomb c _).1 hc)`. Rewrite using `[h, v.repr_sum_self]`.
-/
theorem isLieBasis_tvE : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}
    (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)), IsLieBasis (fun a => GlobalTheory.VertCoeffRing.tvE (v a)) := by
  intro R _ G _ _ n v
  have hE : (overAt (𝟙 (Sp R)) (DualNumber R)).hom = (epsR R).hom := by
    simp [epsR, overAt]
  let e : epsR R ⟶ overAt (𝟙 (Sp R)) (DualNumber R) := Over.homMk (𝟙 _) (by simp [hE])
  let f : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ epsR R := Over.homMk (𝟙 _) (by simp [hE])
  have hfe : f ≫ e = 𝟙 _ := Over.OverMorphism.ext (by simp [e, f])
  have hef : e ≫ f = 𝟙 _ := Over.OverMorphism.ext (by simp [e, f])

  have htv : ∀ x : TanM (𝟙 (Sp R)) G, tvE x = e ≫ tv x := by
    intro x
    apply Over.OverMorphism.ext
    first
    | (simp only [e, Over.comp_left, Over.homMk_left, Category.id_comp]; exact tvE_left x)
    | simp [e, tvE_left x]
  have hadd : ∀ x y : TanM (𝟙 (Sp R)) G, tvE (x + y) = tvE x * tvE y := by
    intro x y; rw [htv, htv, htv, PullbackSections.tv_add, MonObj.comp_mul]
  have hzero : tvE (0 : TanM (𝟙 (Sp R)) G) = 1 := by
    rw [htv, PullbackSections.tv_zero, MonObj.comp_one]

  have hsmul : ∀ (a : R) (x : TanM (𝟙 (Sp R)) G),
      (tvE (a • x)).left = spMap (epsScaleR a) ≫ (tvE x).left := by
    intro a x; rw [tvE_left, tvE_left, PullbackSections.tv_smul]
    first
    | rfl
    | (simp only [smT.eq_1, Formalism.L2.Pj.homAt.eq_1, Over.comp_left, Over.homMk_left, tm.eq_1, epsScaleR.eq_1]; rfl)
  have hinj : ∀ x y : TanM (𝟙 (Sp R)) G, tvE x = tvE y → x = y := by
    intro x y h
    apply PullbackSections.tanM_ext
    have h' := congrArg (fun t => f ≫ t) h
    simpa [htv, ← Category.assoc, hfe] using h'
  have hsum : ∀ (c : Fin n → R) (s : Finset (Fin n)),
      tvE (∑ i ∈ s, c i • v i) = ∏ i ∈ s, tvE (c i • v i) := by
    intro c s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hadd, ih]

  have hcomb : ∀ (c : Fin n → R) (w : epsR R ⟶ G),
      IsLieComb c (fun a => tvE (v a)) w ↔ w = tvE (∑ i, c i • v i) := by
    intro c w
    rw [IsLieComb.eq_1, hsum]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [List.prod_ofFn]
      refine Finset.prod_congr rfl fun i _ => Over.OverMorphism.ext ?_
      rw [hu i, hsmul]
    · rintro rfl
      exact ⟨fun i => tvE (c i • v i), fun i => hsmul _ _, by rw [List.prod_ofFn]⟩

  have hfa : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    ext r; simp
  have hdual : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    simp only [spMap.eq_1, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hfa, CommRingCat.ofHom_id, Spec.map_id]
    all_goals rfl
  have hz : spMap (epsScaleR (0 : R)) =
      spMap (algebraMap R (DualNumber R)) ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
    have h0 : epsScaleR (0 : R) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
      refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
      all_goals first
        | (simp [epsScaleR]; done)
        | (simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]; done)
        | (simp [epsScaleR.eq_1, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fstHom_apply,
            TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map]; done)
        | rfl
        | (simp [epsScaleR]; rfl)
    rw [h0]
    simp only [spMap.eq_1, CommRingCat.ofHom_comp, Spec.map_comp]
  have hu : (toUnit (overAt (𝟙 (Sp R)) (DualNumber R))).left = spMap (algebraMap R (DualNumber R)) := by
    first
    | simp [overAt]
    | (have h := Over.w (toUnit (overAt (𝟙 (Sp R)) (DualNumber R))); simpa [overAt] using h)
  have hone : (1 : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G).left =
      spMap (algebraMap R (DualNumber R)) ≫ (η : 𝟙_ (Over (Sp R)) ⟶ G).left := by
    calc (1 : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G).left
        = (toUnit (overAt (𝟙 (Sp R)) (DualNumber R))).left ≫ (η : 𝟙_ (Over (Sp R)) ⟶ G).left := rfl
      _ = _ := by rw [hu]

  have key : ∀ g : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G, smT (𝟙 (Sp R)) 0 g = 1 ↔ IsTangent (e ≫ g) := by
    intro g
    rw [IsTangent.eq_1]
    have hl : (smT (𝟙 (Sp R)) 0 g).left = spMap (algebraMap R (DualNumber R)) ≫
        spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ g.left := by
      rw [← Category.assoc, ← hz]
      first
      | rfl
      | (simp only [smT.eq_1, Formalism.L2.Pj.homAt.eq_1, Over.comp_left, Over.homMk_left, tm.eq_1, epsScaleR.eq_1]; rfl)
    have he : ∀ t : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G, spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (e ≫ t).left =
        spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ t.left := by
      intro t; simp [e]
    rw [he]
    constructor
    · intro h
      have h2 := congrArg Over.Hom.left h
      rw [hl, hone] at h2
      have h3 := congrArg (fun t => spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ t) h2
      simpa only [← Category.assoc, hdual, Category.id_comp] using h3
    · intro h
      apply Over.OverMorphism.ext
      rw [hl, hone, h]
  have htan : ∀ x, IsTangent (tvE x) := fun x => by
    rw [htv]; exact (key (tv x)).1 (PullbackSections.tv_mem x)
  have hsurj : ∀ w : epsR R ⟶ G, IsTangent w → ∃ x, tvE x = w := by
    intro w hw
    have hw' : IsTangent (e ≫ (f ≫ w)) := by rwa [← Category.assoc, hef, Category.id_comp]
    refine ⟨PullbackSections.mkT (f ≫ w) ((key _).2 hw'), ?_⟩
    rw [htv, PullbackSections.tv_mkT, ← Category.assoc, hef, Category.id_comp]
  rw [IsLieBasis.eq_1]
  refine ⟨fun i => htan (v i), fun w hw => ?_⟩
  obtain ⟨x, rfl⟩ := hsurj w hw
  refine ⟨⇑(v.repr x), (hcomb _ _).2 ?_, fun c hc => ?_⟩
  · rw [v.sum_repr]
  · have h := hinj _ _ ((hcomb c _).1 hc)
    rw [h, v.repr_sum_self]

end GlobalTheory.VertCoeffRing
