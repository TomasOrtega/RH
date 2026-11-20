import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoValueOneOriginPolarised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoValueOneZeroFirstFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.GenOrigin

/- English proof (translation)
Establish `hs` using `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2`. Establish `hi` using `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv).1`. Introduce `x y h`. Take `⟨a, rfl⟩` from `hs x`. Take `⟨b, rfl⟩` from `hs y`.

Establish `e` using `fun c => congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e`. Use `hi ((e a).trans (h.trans (e b).symm))` as an intermediate fact. Rewrite using `[IsFractionRing.injective R (FractionRing R) this]`.
-/
theorem jK_appTop_inj (R : Type) [CommRing R] [IsDomain R] : Function.Injective (jK R).appTop.hom := by
  have hs := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2
  have hi := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv).1
  intro x y h
  obtain ⟨a, rfl⟩ := hs x
  obtain ⟨b, rfl⟩ := hs y
  have e := fun c => congrArg (fun q => q.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  have := hi ((e a).trans (h.trans (e b).symm))
  rw [IsFractionRing.injective R (FractionRing R) this]

/- English proof (translation)
Set `C : M.ι × M'.ι → X'.Opens` to `fun i => ((LB.LinComb M φ ε).pull F).U (fun _ _ => i.1) ⊓ (LB.LinComb M' φ' ε).U (fun _ => i.2)`. Establish `mem : ∀ (x : S) (a : M.ι) (b : M'.ι), q x ∈ M.U a → q' x ∈ M'.U b → e x ∈ C (a, b)` using `fun x a b ha hb => ⟨mem_pull.2 (NormIso.mem_const M φ (e ≫ F) q hq x a ha), NormIso.mem_const M' φ' e q' hq' x b hb⟩`. Take `⟨u, hu⟩` from `glue_unit (⊤ : S.Opens) (fun i => e ⁻¹ᵁ C i) (fun _ => le_top) (fun x _ => by`. Take `⟨a, ha⟩` from `exists_chart hM (q x)`. Take `⟨b, hb⟩` from `exists_chart hM' (q' x)`.

Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b), mem x a b ha hb⟩)`. Use the proof step `(fun i => pullU e (C i) (w.s (fun _ _ => i.1, fun _ => i.2))) (fun i j x hx => by`. Establish `hi : e x ∈ C i` using `hx.1`. Establish `hj : e x ∈ C j` using `hx.2`. Use `(gm_pull (𝟙 S) e x (C i) hi _).trans (Eq.trans ?_ (gm_pull (𝟙 S) e x (C j) hj _).symm)` and prove the remaining obligations.

Rewrite using `[Category.id_comp]`. Establish `h` using `(isGen_iff w).1 hw S e x (fun _ => i.1) (fun _ => j.1) (fun _ => i.2) (fun _ => j.2) (mem_pull.1 hi.1) (mem_pull.1 hj.1) hi.2 hj.2`. Use `h.trans ((congrArg (· * _) ((congrArg₂ (fun s t => s * t⁻¹) (NormIso.gm_const M φ ε hε (e ≫ F) q hq x i.1 j.1 (mem_pull.1 hi.1) (mem_pull.1 hj.1)) (NormIso.gm_const M' φ' ε hε e q' hq' x i.2 j.2 hi.2 hj.2)).trans (mul_inv_cancel 1))).trans (_root_.one_mul _)))` and prove the remaining obligations. Use `⟨u, fun Z t z a b ha hb => ?_⟩` and prove the remaining obligations. Establish `hm : e (t z) ∈ C (a, b)` using `mem (t z) a b ha hb`.

Conclude with `(gm_pull t e z (C (a, b)) hm _).symm.trans ((congrArg (gm t z (e ⁻¹ᵁ C (a, b))) (hu (a, b)).symm).trans (gm_res t z le_top hm u))`.
-/
theorem exists_unit_along {S X X' B B' : Scheme.{0}} (M : LB B) (M' : LB B') (hM : M.IsLB) (hM' : M'.IsLB)
    {K : Type} [Fintype K] (φ : K → (X ⟶ B)) (φ' : K → (X' ⟶ B')) (ε : K → ℤ) (hε : ∑ k, ε k = 0) (F : X' ⟶ X)
    (e : S ⟶ X') (q : S ⟶ B) (q' : S ⟶ B') (hq : ∀ k, (e ≫ F) ≫ φ k = q)
    (hq' : ∀ k, e ≫ φ' k = q') (w : LB.Iso (LB.LinComb M' φ' ε) ((LB.LinComb M φ ε).pull F)) (hw : w.IsGen) :
    ∃ u : Γ(S, ⊤)ˣ, ∀ (Z : Scheme.{0}) (t : Z ⟶ S) (z : Z) (a : M.ι) (b : M'.ι), q (t z) ∈ M.U a →
      q' (t z) ∈ M'.U b → gw w (t ≫ e) z (fun _ => a) (fun _ => b) = gm t z ⊤ u := by
  let C : M.ι × M'.ι → X'.Opens := fun i =>
    ((LB.LinComb M φ ε).pull F).U (fun _ _ => i.1) ⊓ (LB.LinComb M' φ' ε).U (fun _ => i.2)
  have mem : ∀ (x : S) (a : M.ι) (b : M'.ι), q x ∈ M.U a → q' x ∈ M'.U b → e x ∈ C (a, b) := fun x a b ha hb =>
    ⟨mem_pull.2 (NormIso.mem_const M φ (e ≫ F) q hq x a ha), NormIso.mem_const M' φ' e q' hq' x b hb⟩
  obtain ⟨u, hu⟩ := glue_unit (⊤ : S.Opens) (fun i => e ⁻¹ᵁ C i) (fun _ => le_top) (fun x _ => by
      obtain ⟨a, ha⟩ := exists_chart hM (q x)
      obtain ⟨b, hb⟩ := exists_chart hM' (q' x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b), mem x a b ha hb⟩)
    (fun i => pullU e (C i) (w.s (fun _ _ => i.1, fun _ => i.2))) (fun i j x hx => by
      have hi : e x ∈ C i := hx.1
      have hj : e x ∈ C j := hx.2
      refine (gm_pull (𝟙 S) e x (C i) hi _).trans (Eq.trans ?_ (gm_pull (𝟙 S) e x (C j) hj _).symm)
      rw [Category.id_comp]
      have h := (isGen_iff w).1 hw S e x (fun _ => i.1) (fun _ => j.1) (fun _ => i.2) (fun _ => j.2)
        (mem_pull.1 hi.1) (mem_pull.1 hj.1) hi.2 hj.2
      refine h.trans ((congrArg (· * _) ((congrArg₂ (fun s t => s * t⁻¹)
        (NormIso.gm_const M φ ε hε (e ≫ F) q hq x i.1 j.1 (mem_pull.1 hi.1) (mem_pull.1 hj.1))
        (NormIso.gm_const M' φ' ε hε e q' hq' x i.2 j.2 hi.2 hj.2)).trans (mul_inv_cancel 1))).trans (_root_.one_mul _)))
  refine ⟨u, fun Z t z a b ha hb => ?_⟩
  have hm : e (t z) ∈ C (a, b) := mem (t z) a b ha hb
  exact (gm_pull t e z (C (a, b)) hm _).symm.trans ((congrArg (gm t z (e ⁻¹ᵁ C (a, b))) (hu (a, b)).symm).trans
    (gm_res t z le_top hm u))

/- English proof (translation)
Introduce `S V _ _ B B' _ _ _ _ M M' hM hM' f β β₂ w hpb hs hw hgen`. Set `O : Over (Sp V)` to `𝟙_ (Over (Sp V))`. Set `e : O.left ⟶ (G2 B').left` to `(lift (1 : O ⟶ B') 1).left`. Set `q : O.left ⟶ B.left` to `(1 : Over.mk (O.hom ≫ f) ⟶ B).left`. Set `q' : O.left ⟶ B'.left` to `(1 : O ⟶ B').left`.

Establish `hq : ∀ I : ULift.{0} (Finset (Fin 2)), (e ≫ β₂) ≫ (psum B (x2 B) I.down).left = q` using `fun I => (congrArg (· ≫ (psum B (x2 B) I.down).left) (NormIso.origin_square hpb hs O)).trans (congrArg (fun z => z.left) (NormIso.lift_one_psum B (T := Over.mk (O.hom ≫ f)) I.down))`. Establish `hq' : ∀ I : ULift.{0} (Finset (Fin 2)), e ≫ (psum B' (x2 B') I.down).left = q'` using `fun I => congrArg (fun z => z.left) (NormIso.lift_one_psum B' (T := O) I.down)`. Take `⟨u, hu⟩` from `exists_unit_along M M' hM hM' (K := ULift.{0} (Finset (Fin 2))) (fun I => (psum B (x2 B) I.down).left) (fun I => (psum B' (x2 B') I.down).left) (fun I => (-1) ^ (2 - I.down.card)) (by decide) β₂ e q q' hq hq' w hw`. Establish `hval : ∀ (T : Over (Sp V)) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = gm (toUnit T).left z ⊤ u`. Introduce `T z J J' hJ hJ'`.

Establish `hp : (lift (1 : T ⟶ B') (1 : T ⟶ B')).left = (toUnit T).left ≫ e` using `by show _ = (toUnit T ≫ lift (1 : O ⟶ B') 1).left`. Rewrite using `[comp_lift, MonObj.comp_one]`. Establish `key : ∀ (p : T.left ⟶ (G2 B').left) (j : (abelian₂ B M).ι) (k : (abelian₂ B' M').ι), (fun I : ULift.{0} (Finset (Fin 2)) => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)) = j → (fun I : ULift.{0} (Finset (Fin 2)) => J' (p ≫ (psum B' (x2 B') I.down).left)) = k → lamVal w p z J J' = gw …` using `abelian₂ B M) (L' := abelian₂ B' M') w p z j k := by`. Introduce and unpack `p _ _ rfl rfl`. Both sides reduce to the same expression.

Rewrite using `[hp]`. Use `(key _ (fun _ => J ((toUnit T).left ≫ q)) (fun _ => J' ((toUnit T).left ≫ q')) (funext fun I => ?_) (funext fun I => ?_)).trans (hu T.left (toUnit T).left z _ _ (hJ ((toUnit T).left ≫ q)) (hJ' ((toUnit T).left ≫ q')))` and prove the remaining obligations. Rewrite using `[← hq I, Category.assoc, Category.assoc]`. Rewrite using `[← hq' I, Category.assoc]`. Establish `hK : (toUnit (TK V)).left = jK V` using `by simpa using Over.w (toUnit (TK V))`.

Establish `h1 : (Units.map (jK V).appTop.hom.toMonoidHom u : Γ((TK V).left, ⊤)ˣ) = 1` using `unit_ext fun x _ => by choose a ha using fun χ : (TK V).left ⟶ B.left => exists_chart hM (χ x) choose b hb using fun χ : (TK V).left ⟶ B'.left => exists_chart hM' (χ x)`. Establish `h` using `(hval (TK V) x a b ha hb).symm.trans (hgen x a b ha hb)`. Rewrite `h` using `[hK]`. Rewrite using `[map_one]`. Conclude with `(gm_pull (𝟙 _) (jK V) x ⊤ trivial u).trans ((congrArg (fun g => gm g x ⊤ u) (Category.id_comp _)).trans h)`.

Establish `hu1 : u = 1` using `Units.ext (jK_appTop_inj V (by`. Use `congrArg Units.val h1` as an intermediate fact. Simplify using `using this))`. Introduce `T z J J' hJ hJ'`. Rewrite using `[hval T z J J' hJ hJ', hu1]`.

Conclude with `map_one _`.
-/
theorem lamVal_origin_of_generic : ∀ {S : Scheme.{0}} {V : Type} [CommRing V] [IsDomain V] (B : Over S) (B' : Over (Sp V)) [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : LB B.left) (M' : LB B'.left), M.IsLB → M'.IsLB → ∀ (f : Sp V ⟶ S) (β : B'.left ⟶ B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)), IsGrpPullback B' B f β → IsSquare β β₂ → w.IsGen → (∀ (z : (TK V).left) (J : ((TK V).left ⟶ B.left) → M.ι) (J' : ((TK V).left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : TK V ⟶ B') (1 : TK V ⟶ B')).left z J J' = 1) → ∀ (T : Over (Sp V)) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι), Good M z J → Good M' z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1 := by
  intro S V _ _ B B' _ _ _ _ M M' hM hM' f β β₂ w hpb hs hw hgen
  let O : Over (Sp V) := 𝟙_ (Over (Sp V))
  let e : O.left ⟶ (G2 B').left := (lift (1 : O ⟶ B') 1).left
  let q : O.left ⟶ B.left := (1 : Over.mk (O.hom ≫ f) ⟶ B).left
  let q' : O.left ⟶ B'.left := (1 : O ⟶ B').left
  have hq : ∀ I : ULift.{0} (Finset (Fin 2)), (e ≫ β₂) ≫ (psum B (x2 B) I.down).left = q := fun I =>
    (congrArg (· ≫ (psum B (x2 B) I.down).left) (NormIso.origin_square hpb hs O)).trans
      (congrArg (fun z => z.left) (NormIso.lift_one_psum B (T := Over.mk (O.hom ≫ f)) I.down))
  have hq' : ∀ I : ULift.{0} (Finset (Fin 2)), e ≫ (psum B' (x2 B') I.down).left = q' := fun I =>
    congrArg (fun z => z.left) (NormIso.lift_one_psum B' (T := O) I.down)
  obtain ⟨u, hu⟩ := exists_unit_along M M' hM hM' (K := ULift.{0} (Finset (Fin 2)))
    (fun I => (psum B (x2 B) I.down).left) (fun I => (psum B' (x2 B') I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) (by decide) β₂ e q q' hq hq' w hw
  have hval : ∀ (T : Over (Sp V)) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B'.left) → M'.ι),
      Good M z J → Good M' z J' →
      lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = gm (toUnit T).left z ⊤ u := by
    intro T z J J' hJ hJ'
    have hp : (lift (1 : T ⟶ B') (1 : T ⟶ B')).left = (toUnit T).left ≫ e := by
      show _ = (toUnit T ≫ lift (1 : O ⟶ B') 1).left
      rw [comp_lift, MonObj.comp_one]
    have key : ∀ (p : T.left ⟶ (G2 B').left) (j : (abelian₂ B M).ι) (k : (abelian₂ B' M').ι),
        (fun I : ULift.{0} (Finset (Fin 2)) => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left)) = j →
        (fun I : ULift.{0} (Finset (Fin 2)) => J' (p ≫ (psum B' (x2 B') I.down).left)) = k →
        lamVal w p z J J' = gw (L := abelian₂ B M) (L' := abelian₂ B' M') w p z j k := by
      rintro p _ _ rfl rfl
      rfl
    rw [hp]
    refine (key _ (fun _ => J ((toUnit T).left ≫ q)) (fun _ => J' ((toUnit T).left ≫ q')) (funext fun I => ?_)
      (funext fun I => ?_)).trans (hu T.left (toUnit T).left z _ _ (hJ ((toUnit T).left ≫ q)) (hJ' ((toUnit T).left ≫ q')))
    · rw [← hq I, Category.assoc, Category.assoc]
    · rw [← hq' I, Category.assoc]
  have hK : (toUnit (TK V)).left = jK V := by simpa using Over.w (toUnit (TK V))
  have h1 : (Units.map (jK V).appTop.hom.toMonoidHom u : Γ((TK V).left, ⊤)ˣ) = 1 := unit_ext fun x _ => by
    choose a ha using fun χ : (TK V).left ⟶ B.left => exists_chart hM (χ x)
    choose b hb using fun χ : (TK V).left ⟶ B'.left => exists_chart hM' (χ x)
    have h := (hval (TK V) x a b ha hb).symm.trans (hgen x a b ha hb)
    rw [hK] at h
    rw [map_one]
    exact (gm_pull (𝟙 _) (jK V) x ⊤ trivial u).trans ((congrArg (fun g => gm g x ⊤ u) (Category.id_comp _)).trans h)
  have hu1 : u = 1 := Units.ext (jK_appTop_inj V (by
    have := congrArg Units.val h1
    simpa using this))
  intro T z J J' hJ hJ'
  rw [hval T z J J' hJ hJ', hu1]; exact map_one _

end GlobalTheory.GenOrigin
