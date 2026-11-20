import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CotangentBidualToTangentFunctionInjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusLieRetraction

open IsLocalRing GlobalTheory.HodgeTateCompare GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems

variable {R : Type} [CommRing R] [IsLocalRing R]

/- English proof (translation)
The claim follows from `Subtype.ext (lieEquiv_add v w)`.
-/
theorem lieEquiv_add' {G : Over (Spec (CommRingCat.of R))} [GrpObj G] (v w : Lie G) :
    lieEquiv G (v + w) = lieAdd G (lieEquiv G v) (lieEquiv G w) :=
  Subtype.ext (lieEquiv_add v w)

/- English proof (translation)
The claim follows from `Subtype.ext (lieEquiv_smul a v)`.
-/
theorem lieEquiv_smul' {G : Over (Spec (CommRingCat.of R))} [GrpObj G] (a : R) (v : Lie G) :
    lieEquiv G (a • v) = lieScale G a (lieEquiv G v) :=
  Subtype.ext (lieEquiv_smul a v)

def lieLin {T G : Over (Spec (CommRingCat.of R))} [GrpObj T] [GrpObj G] (u : T ⟶ G) [IsMonHom u] :
    Lie T →ₗ[R] Lie G where
  toFun v := (lieEquiv G).symm (lieMap u (lieEquiv T v))
  map_add' v w := by
    apply (lieEquiv G).injective
    rw [Equiv.apply_symm_apply, lieEquiv_add', lieEquiv_add', Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
    exact (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.isLieLinear_lieMap u).1 _ _
  map_smul' a v := by
    apply (lieEquiv G).injective
    rw [Equiv.apply_symm_apply, lieEquiv_smul', RingHom.id_apply, lieEquiv_smul',
      Equiv.apply_symm_apply]
    exact (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.isLieLinear_lieMap u).2 _ _

/- English proof (translation)
The claim follows from `Equiv.apply_symm_apply _ _`.
-/
theorem lieEquiv_lieLin {T G : Over (Spec (CommRingCat.of R))} [GrpObj T] [GrpObj G] (u : T ⟶ G)
    [IsMonHom u] (v : Lie T) : lieEquiv G (lieLin u v) = lieMap u (lieEquiv T v) :=
  Equiv.apply_symm_apply _ _

/- English proof (translation)
Use `Submodule.smul_induction_on (p := fun v : Module.Dual R M => (Algebra.ofId R (ResidueField R)).toLinearMap ∘ₗ v = 0) hv ?_ ?_` and prove the remaining obligations. Introduce `a ha w _`. Use extensionality with `c`. Simplify using `[IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff a).2 ha]`. Introduce `x y hx hy`.

Rewrite using `[LinearMap.comp_add, hx, hy, add_zero]`.
-/
theorem res_comp_of_mem {M : Type} [AddCommGroup M] [Module R M] {v : Module.Dual R M}
    (hv : v ∈ (maximalIdeal R) • (⊤ : Submodule R (Module.Dual R M))) :
    (Algebra.ofId R (ResidueField R)).toLinearMap ∘ₗ v = 0 := by
  refine Submodule.smul_induction_on (p := fun v : Module.Dual R M =>
    (Algebra.ofId R (ResidueField R)).toLinearMap ∘ₗ v = 0) hv ?_ ?_
  · intro a ha w _
    ext c
    simp [IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff a).2 ha]
  · intro x y hx hy
    rw [LinearMap.comp_add, hx, hy, add_zero]

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis R M`. Rewrite using `[← b.sum_dual_apply_smul_coord v]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ trivial` and prove the remaining obligations. Use `LinearMap.congr_fun hv (b i)` as an intermediate fact. Rewrite using `[← IsLocalRing.residue_eq_zero_iff]`.

Simplify `this` using `[IsLocalRing.ResidueField.algebraMap_eq]`.
-/
theorem mem_of_res_comp {M : Type} [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] {v : Module.Dual R M}
    (hv : (Algebra.ofId R (ResidueField R)).toLinearMap ∘ₗ v = 0) :
    v ∈ (maximalIdeal R) • (⊤ : Submodule R (Module.Dual R M)) := by
  let b := Module.Free.chooseBasis R M
  rw [← b.sum_dual_apply_smul_coord v]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ trivial
  have := LinearMap.congr_fun hv (b i)
  rw [← IsLocalRing.residue_eq_zero_iff]
  simpa [IsLocalRing.ResidueField.algebraMap_eq] using this

/- English proof (translation)
Establish `h1 : tangentAlg v = tangentAlg w` using `ptMap_locIncl_injective h`. Use `GlobalTheory.AugCot.hom_ext (ε := aug G) fun a => ?_` and prove the remaining obligations. Conclude with `(tangentAlg_snd v a).symm.trans ((congrArg (fun φ => (φ a).snd) h1).trans (tangentAlg_snd w a))`.
-/
theorem tangentPt_inj {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {A : Type} [CommRing A]
    [Algebra R A] {v w : Cotangent G →ₗ[R] A}
    (h : (tangentPt v : specO R (DualNumber A) ⟶ G) = tangentPt w) : v = w := by
  have h1 : tangentAlg v = tangentAlg w := ptMap_locIncl_injective h
  refine GlobalTheory.AugCot.hom_ext (ε := aug G) fun a => ?_
  exact (tangentAlg_snd v a).symm.trans
    ((congrArg (fun φ => (φ a).snd) h1).trans (tangentAlg_snd w a))

/- English proof (translation)
Set `k` to `ResidueField R`. Set `f : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)` to `Spec.map (CommRingCat.ofHom (algebraMap R k))`. Set `Y : Over (Spec (CommRingCat.of k))` to `specO k (DualNumber k)`. Set `e : specO R (DualNumber k) ≅ (Over.map f).obj Y` to `Over.isoMk (Iso.refl _) (by`. Simplify using `only [Iso.refl_hom, Category.id_comp, Over.map_obj_hom, Y, f, specO, Over.mk_hom]`.

Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])`. Set `adj` to `Over.mapPullbackAdj f`. Use `haveI : Mono ((Over.pullback f).map u) := by haveI : Mono ((Over.pullback f).map u).left := inferInstanceAs (Mono ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map u).left)`. Conclude with `Over.mono_of_mono_left _`. Establish `h1 : adj.homEquiv _ _ (e.inv ≫ p) = adj.homEquiv _ _ (e.inv ≫ q)`.

Apply `(cancel_mono ((Over.pullback f).map u)).1` to reduce the goal to its premises. Rewrite using `[← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_right, Category.assoc, Category.assoc, h]`. Establish `h2` using `(adj.homEquiv _ _).injective h1`. Conclude with `(cancel_epi e.inv).1 h2`.
-/
theorem comp_cancel {T G : Over (Spec (CommRingCat.of R))} (u : T ⟶ G)
    (hu : IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (ResidueField R)).map u).left)
    {p q : specO R (DualNumber (ResidueField R)) ⟶ T} (h : p ≫ u = q ≫ u) : p = q := by
  let k := ResidueField R
  let f : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R k))
  let Y : Over (Spec (CommRingCat.of k)) := specO k (DualNumber k)
  let e : specO R (DualNumber k) ≅ (Over.map f).obj Y := Over.isoMk (Iso.refl _) (by
    simp only [Iso.refl_hom, Category.id_comp, Over.map_obj_hom, Y, f, specO, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])
  let adj := Over.mapPullbackAdj f
  haveI : Mono ((Over.pullback f).map u) := by
    haveI : Mono ((Over.pullback f).map u).left := inferInstanceAs (Mono ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map u).left)
    exact Over.mono_of_mono_left _
  have h1 : adj.homEquiv _ _ (e.inv ≫ p) = adj.homEquiv _ _ (e.inv ≫ q) := by
    apply (cancel_mono ((Over.pullback f).map u)).1
    rw [← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_right, Category.assoc,
      Category.assoc, h]
  have h2 := (adj.homEquiv _ _).injective h1
  exact (cancel_epi e.inv).1 h2

/- English proof (translation)
Set `eM` to `TensorProduct.quotTensorEquivQuotSMul M (maximalIdeal R)`. Set `eN` to `TensorProduct.quotTensorEquivQuotSMul N (maximalIdeal R)`. Establish `hle : (maximalIdeal R) • (⊤ : Submodule R M) ≤ ((maximalIdeal R) • (⊤ : Submodule R N)).comap l` using `Submodule.smul_le.2 fun r hr n _ => by`. Rewrite using `[Submodule.mem_comap, map_smul]`. Conclude with `Submodule.smul_mem_smul hr trivial`.

Set `q` to `Submodule.mapQ _ _ l hle`. Establish `hq : Function.Injective q`. Use `(injective_iff_map_eq_zero q).2 fun x hx => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite `hx` using `[Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]`.

Conclude with `(Submodule.Quotient.mk_eq_zero _).2 (h x hx)`. Establish `hcomm : ∀ t, eN (l.lTensor (R ⧸ maximalIdeal R) t) = q (eM t)`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero, map_zero, map_zero]`.

Consider the case `tmul a x`. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Rewrite using `[LinearMap.lTensor_tmul, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, Submodule.mapQ_apply, map_smul]`. Consider the case `add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]`. Introduce `s t hst`.

Apply `eM.injective` to reduce the goal to its premises. Apply `hq` to reduce the goal to its premises. Rewrite using `[← hcomm, ← hcomm, hst]`.
-/
theorem lTensor_injective_of {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (l : M →ₗ[R] N)
    (h : ∀ x, l x ∈ (maximalIdeal R) • (⊤ : Submodule R N) →
      x ∈ (maximalIdeal R) • (⊤ : Submodule R M)) :
    Function.Injective (l.lTensor (R ⧸ maximalIdeal R)) := by
  let eM := TensorProduct.quotTensorEquivQuotSMul M (maximalIdeal R)
  let eN := TensorProduct.quotTensorEquivQuotSMul N (maximalIdeal R)
  have hle : (maximalIdeal R) • (⊤ : Submodule R M) ≤
      ((maximalIdeal R) • (⊤ : Submodule R N)).comap l :=
    Submodule.smul_le.2 fun r hr n _ => by
      rw [Submodule.mem_comap, map_smul]
      exact Submodule.smul_mem_smul hr trivial
  let q := Submodule.mapQ _ _ l hle
  have hq : Function.Injective q := by
    refine (injective_iff_map_eq_zero q).2 fun x hx => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    exact (Submodule.Quotient.mk_eq_zero _).2 (h x hx)
  have hcomm : ∀ t, eN (l.lTensor (R ⧸ maximalIdeal R) t) = q (eM t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero]
    | tmul a x =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [LinearMap.lTensor_tmul, TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
        TensorProduct.quotTensorEquivQuotSMul_mk_tmul, Submodule.mapQ_apply, map_smul]
    | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]
  intro s t hst
  apply eM.injective
  apply hq
  rw [← hcomm, ← hcomm, hst]

/- English proof (translation)
Introduce `R _ _ G _ hG r u _ hu`. Use `haveI := hG`. Take `⟨_, _⟩` from `finite_projective_of_smooth (G := G)`. Take `⟨_, _⟩` from `finite_projective_of_smooth (G := torus R r)`. Use `haveI : Module.FinitePresentation R (Cotangent G) := Module.finitePresentation_of_projective _ _`.

Use `haveI : Module.Free R (Cotangent G) := Module.free_of_flat_of_isLocalRing`. Use `haveI : Module.FinitePresentation R (Cotangent (torus R r)) := Module.finitePresentation_of_projective _ _`. Use `haveI : Module.Free R (Cotangent (torus R r)) := Module.free_of_flat_of_isLocalRing`. Set `l` to `lieLin u`. Set `φ` to `Algebra.ofId R (ResidueField R)`.

Establish `key : ∀ x, l x ∈ (maximalIdeal R) • (⊤ : Submodule R (Lie G)) → x ∈ (maximalIdeal R) • (⊤ : Submodule R (Lie (torus R r)))`. Introduce `x hx`. Establish `h1` using `res_comp_of_mem hx`. Establish `a1 : ∀ y, (lieEquiv (torus R r) y).1 ≫ u = (lieEquiv G (l y)).1` using `fun y => by`. Rewrite using `[lieEquiv_lieLin]`.

Both sides reduce to the same expression. Establish `h2 : (ptMap (dualBC φ) ≫ (lieEquiv (torus R r) x).1) ≫ u = (ptMap (dualBC φ) ≫ (lieEquiv (torus R r) 0).1) ≫ u`. Rewrite using `[Category.assoc, Category.assoc, a1, a1, map_zero, lieEquiv_val, lieEquiv_val, dualBC_tangentPt, dualBC_tangentPt]`. Conclude with `congrArg tangentPt (h1.trans (LinearMap.comp_zero _).symm)`. Establish `h3` using `comp_cancel u hu h2`.

Rewrite `h3` using `[lieEquiv_val, lieEquiv_val, dualBC_tangentPt, dualBC_tangentPt, LinearMap.comp_zero]`. Conclude with `mem_of_res_comp (tangentPt_inj h3)`. Take `⟨l', hl'⟩` from `(IsLocalRing.split_injective_iff_lTensor_residueField_injective l).2 (lTensor_injective_of l key)`. Use `⟨fun y => lieEquiv (torus R r) (l' ((lieEquiv G).symm y)), ⟨fun x y => ?_, fun a x => ?_⟩, fun x => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `(lieEquiv G).surjective x`.

Take `⟨y, rfl⟩` from `(lieEquiv G).surjective y`. Simplify using `only`. Rewrite using `[← lieEquiv_add', Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, map_add, lieEquiv_add']`. Take `⟨x, rfl⟩` from `(lieEquiv G).surjective x dsimp only`. Rewrite using `[← lieEquiv_smul', Equiv.symm_apply_apply, Equiv.symm_apply_apply, map_smul, lieEquiv_smul']`.

Take `⟨x, rfl⟩` from `(lieEquiv (torus R r)).surjective x dsimp only`. Rewrite using `[← lieEquiv_lieLin, Equiv.symm_apply_apply]`. Conclude with `congrArg _ (LinearMap.congr_fun hl' x)`.
-/
theorem main : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G], Smooth G.hom → ∀ (r : ℕ) (u : torus R r ⟶ G) [IsMonHom u],
    IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map u).left →
    ∃ ρ : LieG G → LieG (torus R r), IsLieLinear ρ ∧ ∀ x, ρ (lieMap u x) = x := by
  intro R _ _ G _ hG r u _ hu
  haveI := hG
  obtain ⟨_, _⟩ := finite_projective_of_smooth (G := G)
  obtain ⟨_, _⟩ := finite_projective_of_smooth (G := torus R r)
  haveI : Module.FinitePresentation R (Cotangent G) := Module.finitePresentation_of_projective _ _
  haveI : Module.Free R (Cotangent G) := Module.free_of_flat_of_isLocalRing
  haveI : Module.FinitePresentation R (Cotangent (torus R r)) :=
    Module.finitePresentation_of_projective _ _
  haveI : Module.Free R (Cotangent (torus R r)) := Module.free_of_flat_of_isLocalRing
  let l := lieLin u
  let φ := Algebra.ofId R (ResidueField R)
  have key : ∀ x, l x ∈ (maximalIdeal R) • (⊤ : Submodule R (Lie G)) →
      x ∈ (maximalIdeal R) • (⊤ : Submodule R (Lie (torus R r))) := by
    intro x hx
    have h1 := res_comp_of_mem hx
    have a1 : ∀ y, (lieEquiv (torus R r) y).1 ≫ u = (lieEquiv G (l y)).1 := fun y => by
      rw [lieEquiv_lieLin]; rfl
    have h2 : (ptMap (dualBC φ) ≫ (lieEquiv (torus R r) x).1) ≫ u =
        (ptMap (dualBC φ) ≫ (lieEquiv (torus R r) 0).1) ≫ u := by
      rw [Category.assoc, Category.assoc, a1, a1, map_zero, lieEquiv_val, lieEquiv_val,
        dualBC_tangentPt, dualBC_tangentPt]
      exact congrArg tangentPt (h1.trans (LinearMap.comp_zero _).symm)
    have h3 := comp_cancel u hu h2
    rw [lieEquiv_val, lieEquiv_val, dualBC_tangentPt, dualBC_tangentPt, LinearMap.comp_zero] at h3
    exact mem_of_res_comp (tangentPt_inj h3)
  obtain ⟨l', hl'⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective l).2
    (lTensor_injective_of l key)
  refine ⟨fun y => lieEquiv (torus R r) (l' ((lieEquiv G).symm y)), ⟨fun x y => ?_, fun a x => ?_⟩,
    fun x => ?_⟩
  · obtain ⟨x, rfl⟩ := (lieEquiv G).surjective x
    obtain ⟨y, rfl⟩ := (lieEquiv G).surjective y
    dsimp only
    rw [← lieEquiv_add', Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      map_add, lieEquiv_add']
  · obtain ⟨x, rfl⟩ := (lieEquiv G).surjective x
    dsimp only
    rw [← lieEquiv_smul', Equiv.symm_apply_apply, Equiv.symm_apply_apply, map_smul, lieEquiv_smul']
  · obtain ⟨x, rfl⟩ := (lieEquiv (torus R r)).surjective x
    dsimp only
    rw [← lieEquiv_lieLin, Equiv.symm_apply_apply]
    exact congrArg _ (LinearMap.congr_fun hl' x)

end GlobalTheory.TorusLieRetraction
