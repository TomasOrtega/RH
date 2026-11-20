import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfB

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLocBasis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (tvec IsUnivChart scaleD sp)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

def vec {S : Type} [CommRing S] (x : Sp S ⟶ X) {n : ℕ}
    (xc : ∀ m : ℕ, sp (R₀ := S) (ReciprocityTheory.ChartRestriction.G.Chart.JetR S (Fin n) m) ⟶ (Over.pullback x).obj t.G)
    (cc : Fin n → S) : Sp (DualNumber S) ⟶ t.G.left :=
  (tvec (x := xc) cc).left ≫ pullback.fst t.G.hom x

section V

variable {t} {S : Type} [CommRing S] {x : Sp S ⟶ X} {n : ℕ}
  {xc : ∀ m : ℕ, sp (R₀ := S) (ReciprocityTheory.ChartRestriction.G.Chart.JetR S (Fin n) m) ⟶ (Over.pullback x).obj t.G}

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `pullback.hom_ext` to reduce the goal to its premises. Conclude with `h`. Conclude with `(Over.w v).trans (Over.w v').symm`.
-/
theorem push_ext {Y : Over (Spec (CommRingCat.of S))} {v v' : Y ⟶ (Over.pullback x).obj t.G}
    (h : v.left ≫ pullback.fst t.G.hom x = v'.left ≫ pullback.fst t.G.hom x) : v = v' := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h
  · exact (Over.w v).trans (Over.w v').symm

/- English proof (translation)
Establish `hid : (sp (R₀` using `S) S).hom = 𝟙 _ := by show Spec.map (CommRingCat.ofHom (algebraMap S S)) = _`. Rewrite using `[Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]`. Both sides reduce to the same expression. Establish `e0 : (1 : sp (R₀` using `S) S ⟶ (Over.pullback x).obj t.G).left ≫ pullback.fst t.G.hom x = (1 : Over.mk ((sp (R₀ := S) S).hom ≫ x) ⟶ t.G).left := congrArg (fun q => q.left) (map_one (pushHom (isGrpPullback_pullback t.G x) (sp (R₀ := S) S)))`. Establish `e1 : (1 : Over.mk ((sp (R₀` using `S) S).hom ≫ x) ⟶ t.G).left = (1 : Over.mk x ⟶ t.G).left := by`.

Rewrite using `[ReciprocityTheory.ChartRestriction.G.Chart.one_left', ReciprocityTheory.ChartRestriction.G.Chart.one_left']`. Use `show ((sp (R₀ := S) S).hom ≫ x) ≫ _ = x ≫ _`. Rewrite using `[hid, Category.id_comp]`. Rewrite using `[← e1, ← e0, ← Category.assoc]`. Prove the components needed by the constructor for the conclusion.

Introduce `e`. Conclude with `push_ext e`. Introduce `e`. Conclude with `congrArg (fun q => q.left ≫ pullback.fst t.G.hom x) e`.
-/
theorem tan_iff (v : sp (R₀ := S) (DualNumber S) ⟶ (Over.pullback x).obj t.G) :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v.left ≫ pullback.fst t.G.hom x = (1 : Over.mk x ⟶ t.G).left ↔
      ReciprocityTheory.ChartRestriction.G.Chart.IsTan v := by
  have hid : (sp (R₀ := S) S).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap S S)) = _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    rfl
  have e0 : (1 : sp (R₀ := S) S ⟶ (Over.pullback x).obj t.G).left ≫ pullback.fst t.G.hom x =
      (1 : Over.mk ((sp (R₀ := S) S).hom ≫ x) ⟶ t.G).left :=
    congrArg (fun q => q.left) (map_one (pushHom (isGrpPullback_pullback t.G x) (sp (R₀ := S) S)))
  have e1 : (1 : Over.mk ((sp (R₀ := S) S).hom ≫ x) ⟶ t.G).left = (1 : Over.mk x ⟶ t.G).left := by
    rw [ReciprocityTheory.ChartRestriction.G.Chart.one_left', ReciprocityTheory.ChartRestriction.G.Chart.one_left']
    show ((sp (R₀ := S) S).hom ≫ x) ≫ _ = x ≫ _
    rw [hid, Category.id_comp]
  rw [← e1, ← e0, ← Category.assoc]
  constructor
  · intro e
    exact push_ext e
  · intro e
    exact congrArg (fun q => q.left ≫ pullback.fst t.G.hom x) e

/- English proof (translation)
Use `⟨?_, (tan_iff _).mpr (ReciprocityTheory.ChartRestriction.G.Chart.isTan_tvec hx cc)⟩` and prove the remaining obligations. Use `show ((tvec (x := xc) cc).left ≫ pullback.fst _ _) ≫ _ = _`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc]`. Conclude with `congrArg (· ≫ x) (Over.w (tvec (x := xc) cc))`.
-/
theorem vec_tan (hx : IsUnivChart _ n xc) (cc : Fin n → S) : IsTanAtG t x (vec t x xc cc) := by
  refine ⟨?_, (tan_iff _).mpr (ReciprocityTheory.ChartRestriction.G.Chart.isTan_tvec hx cc)⟩
  show ((tvec (x := xc) cc).left ≫ pullback.fst _ _) ≫ _ = _
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ x) (Over.w (tvec (x := xc) cc))

/- English proof (translation)
Set `v : sp (R₀` to `S) (DualNumber S) ⟶ (Over.pullback x).obj t.G := Over.homMk (pullback.lift w _ hw.1) (pullback.lift_snd _ _ _)`. Establish `hv : v.left ≫ pullback.fst t.G.hom x = w` using `pullback.lift_fst _ _ _`. Establish `ht : ReciprocityTheory.ChartRestriction.G.Chart.IsTan v` using `(tan_iff v).mp (by rw [hv]; exact hw.2)`. Use `⟨ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx v ht, ?_⟩` and prove the remaining obligations. Establish `e : v = tvec (x` using `xc) (ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx v ht) := ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec hx v ht`.

Rewrite using `[← hv]`. Conclude with `congrArg (fun q => q.left ≫ pullback.fst t.G.hom x) e`.
-/
theorem vec_exists (hx : IsUnivChart _ n xc) (w : Sp (DualNumber S) ⟶ t.G.left) (hw : IsTanAtG t x w) :
    ∃ cc, w = vec t x xc cc := by
  let v : sp (R₀ := S) (DualNumber S) ⟶ (Over.pullback x).obj t.G :=
    Over.homMk (pullback.lift w _ hw.1) (pullback.lift_snd _ _ _)
  have hv : v.left ≫ pullback.fst t.G.hom x = w := pullback.lift_fst _ _ _
  have ht : ReciprocityTheory.ChartRestriction.G.Chart.IsTan v := (tan_iff v).mp (by rw [hv]; exact hw.2)
  refine ⟨ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx v ht, ?_⟩
  have e : v = tvec (x := xc) (ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx v ht) := ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec hx v ht
  rw [← hv]
  exact congrArg (fun q => q.left ≫ pullback.fst t.G.hom x) e

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Establish `h` using `ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx (0 : Fin n → S) 0`. Rewrite `h` using `[add_zero]`. Simplify using `using mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)`.

Consider the case `succ m ih`. Rewrite using `[Fin.sum_univ_succ, ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_smul hx, ih (fun j => a j.succ) (fun j => e j.succ), List.ofFn_succ, List.prod_cons]`.
-/
theorem tvec_sum (hx : IsUnivChart _ n xc) {m : ℕ} (a : Fin m → S) (e : Fin m → Fin n → S) :
    tvec (x := xc) (∑ j, a j • e j) =
      (List.ofFn fun j => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j)).prod := by
  induction m with
  | zero =>
    have h := ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx (0 : Fin n → S) 0
    rw [add_zero] at h
    simpa using mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  | succ m ih =>
    rw [Fin.sum_univ_succ, ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_smul hx,
      ih (fun j => a j.succ) (fun j => e j.succ), List.ofFn_succ, List.prod_cons]

/- English proof (translation)
Set `P` to `pushHom (isGrpPullback_pullback t.G x) (sp (R₀ := S) (DualNumber S))`. Set `W' : Fin m → (tEpsG x ⟶ t.G)` to `fun j => P (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j))`. Establish `hW' : ∀ j, (W' j).left = spMap (epsMul (a j)) ≫ vec t x xc (e j)` using `fun j => Category.assoc _ _ _`. Establish `hP : ((List.ofFn W').prod).left = vec t x xc (∑ j, a j • e j)`. Establish `h` using `map_list_prod P (List.ofFn fun j => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j))`.

Rewrite `h` using `[← tvec_sum hx a e, List.map_ofFn]`. Conclude with `(congrArg (fun q => q.left) h).symm`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, hprod⟩`. Establish `eu' : u = W'` using `funext fun j => Over.OverMorphism.ext ((hu j).trans (hW' j).symm)`.

Rewrite `hprod` using `[eu', hP]`. Conclude with `(ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx (push_ext hprod)).symm`. Introduce `h`. Substitute `h` using the available equality. Conclude with `⟨W', hW', hP⟩`.
-/
theorem comb_iff (hx : IsUnivChart _ n xc) {m : ℕ} (e : Fin m → Fin n → S) (a : Fin m → S) (cc : Fin n → S) :
    IsCombAtG t x (fun j => vec t x xc (e j)) a (vec t x xc cc) ↔ cc = ∑ j, a j • e j := by
  let P := pushHom (isGrpPullback_pullback t.G x) (sp (R₀ := S) (DualNumber S))
  let W' : Fin m → (tEpsG x ⟶ t.G) := fun j =>
    P (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j))
  have hW' : ∀ j, (W' j).left = spMap (epsMul (a j)) ≫ vec t x xc (e j) := fun j =>
    Category.assoc _ _ _
  have hP : ((List.ofFn W').prod).left = vec t x xc (∑ j, a j • e j) := by
    have h := map_list_prod P
      (List.ofFn fun j => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j))
    rw [← tvec_sum hx a e, List.map_ofFn] at h
    exact (congrArg (fun q => q.left) h).symm
  constructor
  · rintro ⟨u, hu, hprod⟩
    have eu' : u = W' := funext fun j => Over.OverMorphism.ext ((hu j).trans (hW' j).symm)
    rw [eu', hP] at hprod
    exact (ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx (push_ext hprod)).symm
  · intro h
    subst h
    exact ⟨W', hW', hP⟩

/- English proof (translation)
Take `⟨x₁, hx₁, hcomp⟩` from `ReciprocityTheory.ChartRestriction.G.Chart.tanBC_alg (R := S) (R' := S') _ n xc hx`. Establish `h₁` using `IsGrpPullback.comp (isGrpPullback_pullback ((Over.pullback x).obj t.G) (ReciprocityTheory.ChartRestriction.G.Chart.fB S S')) (isGrpPullback_pullback t.G x)`. Take `⟨e, he, hφ⟩` from `grpPullback_iso h₁ (isGrpPullback_pullback t.G (ReciprocityTheory.ChartRestriction.G.Chart.fB S S' ≫ x))`. Use `⟨fun m => x₁ m ≫ e.hom, gfp_chart_iso e hx₁, fun cc => ?_⟩` and prove the remaining obligations. Establish `key : (tvec (x` using `fun m => x₁ m ≫ e.hom) (algebraMap S S' ∘ cc)).left = (tvec (x := x₁) (algebraMap S S' ∘ cc)).left ≫ e.hom.left := by show (_ ≫ x₁ 1 ≫ e.hom).left = (_ ≫ x₁ 1).left ≫ e.hom.left`.

Rewrite using `[Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc]`. Use `show (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap S S' ∘ cc)).left ≫ pullback.fst _ _ = _`. Rewrite using `[key, Category.assoc, hφ, ← Category.assoc, hcomp cc, Category.assoc]`. Both sides reduce to the same expression.
-/
theorem vec_bc [IsLocalRing S] {S' : Type} [CommRing S'] [Algebra S S'] (hx : IsUnivChart _ n xc) :
    ∃ (xc' : ∀ m : ℕ, sp (R₀ := S') (ReciprocityTheory.ChartRestriction.G.Chart.JetR S' (Fin n) m) ⟶
        (Over.pullback (spMap (algebraMap S S') ≫ x)).obj t.G), IsUnivChart _ n xc' ∧
      ∀ cc : Fin n → S, vec t (spMap (algebraMap S S') ≫ x) xc' (algebraMap S S' ∘ cc) =
        spMap (dualMap (algebraMap S S')) ≫ vec t x xc cc := by
  obtain ⟨x₁, hx₁, hcomp⟩ := ReciprocityTheory.ChartRestriction.G.Chart.tanBC_alg (R := S) (R' := S') _ n xc hx
  have h₁ := IsGrpPullback.comp
    (isGrpPullback_pullback ((Over.pullback x).obj t.G) (ReciprocityTheory.ChartRestriction.G.Chart.fB S S'))
    (isGrpPullback_pullback t.G x)
  obtain ⟨e, he, hφ⟩ := grpPullback_iso h₁
    (isGrpPullback_pullback t.G (ReciprocityTheory.ChartRestriction.G.Chart.fB S S' ≫ x))
  refine ⟨fun m => x₁ m ≫ e.hom, gfp_chart_iso e hx₁, fun cc => ?_⟩
  have key : (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap S S' ∘ cc)).left =
      (tvec (x := x₁) (algebraMap S S' ∘ cc)).left ≫ e.hom.left := by
    show (_ ≫ x₁ 1 ≫ e.hom).left = (_ ≫ x₁ 1).left ≫ e.hom.left
    rw [Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc]
  show (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap S S' ∘ cc)).left ≫ pullback.fst _ _ = _
  rw [key, Category.assoc, hφ, ← Category.assoc, hcomp cc, Category.assoc]
  rfl

end V

/- English proof (translation)
Establish `: Smooth ((Over.pullback x).obj t.G).hom`. Use `t.semi.smooth` as an intermediate fact. Use `show Smooth (pullback.snd t.G.hom x)`. Use `infer_instance`. Take `⟨n, xc, hx⟩` from `ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback x).obj t.G)`.

Use `⟨n, fun e => vec t x xc (Pi.single e 1), fun e => vec_tan hx _, fun S' _ φ w hw => ?_⟩` and prove the remaining obligations. Use `letI : Algebra S S' := φ.toAlgebra`. Take `⟨xc', hx', hv⟩` from `vec_bc (S' := S') hx`. Take `⟨cc, rfl⟩` from `vec_exists hx' w hw`. Establish `hD : (fun e => spMap (dualMap φ) ≫ vec t x xc (Pi.single e 1)) = fun e => vec t (spMap (algebraMap S S') ≫ x) xc' (Pi.single e 1)`.

Use function extensionality and compare the values at `e`. Establish `h1 : (Pi.single e 1 : Fin n → S') = algebraMap S S' ∘ (Pi.single e 1 : Fin n → S)`. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = e`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne h]`. Conclude with `(hv _).symm.trans (by rw [← h1])`. Establish `hs : ∀ a : Fin n → S', ∑ j, a j • (Pi.single j 1 : Fin n → S') = a` using `fun a => by`. Use function extensionality and compare the values at `i`.

Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[hD]`. Use `⟨cc, (comb_iff hx' _ _ _).2 (hs cc).symm, fun a ha => ?_⟩` and prove the remaining obligations. Conclude with `(hs a).symm.trans ((comb_iff hx' _ _ _).1 ha).symm`.
-/
theorem exists_lie_basis_stable (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0})
    (t : SAB H X) (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X) :
    ∃ (n : ℕ) (D : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), (∀ e, IsTanAtG t x (D e)) ∧
      ∀ (S' : Type) [CommRing S'] (φ : S →+* S') (w : Sp (DualNumber S') ⟶ t.G.left),
        IsTanAtG t (spMap φ ≫ x) w →
          ∃! a : Fin n → S', IsCombAtG t (spMap φ ≫ x) (fun e => spMap (dualMap φ) ≫ D e) a w := by
  have : Smooth ((Over.pullback x).obj t.G).hom := by
    have := t.semi.smooth
    show Smooth (pullback.snd t.G.hom x)
    infer_instance
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback x).obj t.G)
  refine ⟨n, fun e => vec t x xc (Pi.single e 1), fun e => vec_tan hx _, fun S' _ φ w hw => ?_⟩
  letI : Algebra S S' := φ.toAlgebra
  obtain ⟨xc', hx', hv⟩ := vec_bc (S' := S') hx
  obtain ⟨cc, rfl⟩ := vec_exists hx' w hw
  have hD : (fun e => spMap (dualMap φ) ≫ vec t x xc (Pi.single e 1)) =
      fun e => vec t (spMap (algebraMap S S') ≫ x) xc' (Pi.single e 1) := by
    funext e
    have h1 : (Pi.single e 1 : Fin n → S') = algebraMap S S' ∘ (Pi.single e 1 : Fin n → S) := by
      funext j
      by_cases h : j = e
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    exact (hv _).symm.trans (by rw [← h1])
  have hs : ∀ a : Fin n → S', ∑ j, a j • (Pi.single j 1 : Fin n → S') = a := fun a => by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hD]
  refine ⟨cc, (comb_iff hx' _ _ _).2 (hs cc).symm, fun a ha => ?_⟩
  exact (hs a).symm.trans ((comb_iff hx' _ _ _).1 ha).symm

end GlobalTheory.LieLocBasis
