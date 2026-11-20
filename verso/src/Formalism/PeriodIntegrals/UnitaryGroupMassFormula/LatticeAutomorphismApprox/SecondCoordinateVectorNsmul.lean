import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LocDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.SecondProjectionSplitEquiv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.LocSplitChiOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.AdelicLatticeToLocalLattices

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists.BrB

open NumberField IsDedekindDomain Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

abbrev LL (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : Submodule (OV I v) (Fin I.n → RV I v) :=
  Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))

/- English proof (translation)
Proceed by induction on `r using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e`. Simplify using `only [sigV, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]`. Rewrite using `[show I.cm.sig (I.cm.sig e) = e from star_star e]`.

Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem sigV_sigV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (r : RV I v) :
    sigV I v (sigV I v r) = r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [sigV, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [show I.cm.sig (I.cm.sig e) = e from star_star e]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Simplify using `[sigV, Algebra.TensorProduct.algebraMap_apply]`.
-/
theorem sigV_alg (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (c : KV I v) :
    sigV I v (algebraMap (KV I v) (RV I v) c) = algebraMap (KV I v) (RV I v) c := by
  simp [sigV, Algebra.TensorProduct.algebraMap_apply]

def vecqL (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (q : RV I v →+* KV I v)
    (hq : ∀ c, q (algebraMap (KV I v) (RV I v) c) = c) :
    (Fin I.n → RV I v) →ₗ[OV I v] (Fin I.n → KV I v) where
  toFun x i := q (x i)
  map_add' x y := by funext i; simp
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [PI.FinKW.LocTo.ov_smul_eq, map_mul]
    have e : ((c : KV I v) ⊗ₜ[I.F] (1 : I.E)) = algebraMap (KV I v) (RV I v) (c : KV I v) := by
      simp [Algebra.TensorProduct.algebraMap_apply]
    rw [e, hq]
    rfl

/- English proof (translation)
Establish `hy' : y ∈ Submodule.span (OV I v) (⇑(vecqL I v q hq) '' (LL I v : Set (Fin I.n → RV I v)))` using `hy`. Rewrite `hy'` using `[← Submodule.map_coe, Submodule.span_eq]`. Take `⟨x, hx, hxy⟩` from `Submodule.mem_map.mp hy'`. Conclude with `⟨x, hx, hxy⟩`.
-/
theorem exists_of_mem_span (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (q : RV I v →+* KV I v)
    (hq : ∀ c, q (algebraMap (KV I v) (RV I v) c) = c) (y : Fin I.n → KV I v)
    (hy : y ∈ Submodule.span (OV I v)
      ((fun x : Fin I.n → RV I v => fun i => q (x i)) '' (LL I v : Set (Fin I.n → RV I v)))) :
    ∃ x ∈ LL I v, (fun i => q (x i)) = y := by
  have hy' : y ∈ Submodule.span (OV I v) (⇑(vecqL I v q hq) '' (LL I v : Set (Fin I.n → RV I v))) := hy
  rw [← Submodule.map_coe, Submodule.span_eq] at hy'
  obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy'
  exact ⟨x, hx, hxy⟩

/- English proof (translation)
Take `⟨hp1, hpe, hpse, -⟩` from `hp`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨Submodule.subset_span (Set.mem_image_of_mem _ hx), Submodule.subset_span (Set.mem_image_of_mem _ hx)⟩`. Introduce and unpack `⟨h1, h2⟩`.

Take `⟨x1, hx1, e1⟩` from `exists_of_mem_span I v p1 hp1 (vec1 p1 x) h1`. Establish `hq2 : ∀ c, (p1.comp (sigV I v)) (algebraMap (KV I v) (RV I v) c) = c`. Introduce `c`. Rewrite using `[RingHom.comp_apply, sigV_alg, hp1]`. Take `⟨x2, hx2, e2⟩` from `exists_of_mem_span I v (p1.comp (sigV I v)) hq2 (vec2 p1 x) h2`.

Establish `hw : ε • x1 + (x2 - ε • x2) ∈ LL I v` using `(LL I v).add_mem (hε x1 hx1) ((LL I v).sub_mem hx2 (hε x2 hx2))`. Establish `hxw : x = ε • x1 + (x2 - ε • x2)`. Use function extensionality and compare the values at `i`. Apply `hinj` to reduce the goal to its premises. Establish `f1 : p1 (x1 i) = p1 (x i)` using `congrFun e1 i`.

Establish `f2 : p1 (sigV I v (x2 i)) = p1 (sigV I v (x i))` using `congrFun e2 i`. Simplify using `only [piHom, RingHom.prod_apply, RingHom.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add, map_sub, map_mul, hpe, hpse, f1, f2]`. Apply the tactic sequence `refine Prod.ext ?_ ?_ <;> simp`. Rewrite using `[hxw]`. Conclude with `hw`.
-/
theorem mem_LL_iff (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (ε : RV I v) (p1 : RV I v →+* KV I v)
    (hp : IsAdaptedFirstProjection I v ε p1) (hinj : Function.Injective (piHom (sigV I v) p1))
    (hε : ∀ w ∈ LL I v, ε • w ∈ LL I v) (x : Fin I.n → RV I v) :
    x ∈ LL I v ↔ vec1 p1 x ∈ Lam1 I v p1 ∧ vec2 p1 x ∈ Lam2 I v p1 := by
  obtain ⟨hp1, hpe, hpse, -⟩ := hp
  constructor
  · intro hx
    exact ⟨Submodule.subset_span (Set.mem_image_of_mem _ hx), Submodule.subset_span (Set.mem_image_of_mem _ hx)⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨x1, hx1, e1⟩ := exists_of_mem_span I v p1 hp1 (vec1 p1 x) h1
    have hq2 : ∀ c, (p1.comp (sigV I v)) (algebraMap (KV I v) (RV I v) c) = c := by
      intro c
      rw [RingHom.comp_apply, sigV_alg, hp1]
    obtain ⟨x2, hx2, e2⟩ := exists_of_mem_span I v (p1.comp (sigV I v)) hq2 (vec2 p1 x) h2
    have hw : ε • x1 + (x2 - ε • x2) ∈ LL I v :=
      (LL I v).add_mem (hε x1 hx1) ((LL I v).sub_mem hx2 (hε x2 hx2))
    have hxw : x = ε • x1 + (x2 - ε • x2) := by
      funext i
      apply hinj
      have f1 : p1 (x1 i) = p1 (x i) := congrFun e1 i
      have f2 : p1 (sigV I v (x2 i)) = p1 (sigV I v (x i)) := congrFun e2 i
      simp only [piHom, RingHom.prod_apply, RingHom.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, map_add, map_sub, map_mul, hpe, hpse, f1, f2]
      refine Prod.ext ?_ ?_ <;> simp
    rw [hxw]
    exact hw

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[vec1]`.
-/
theorem first_coordinate_vector_sub {I : AutInst} {v : HeightOneSpectrum (𝓞 I.F)} (p1 : RV I v →+* KV I v)
    (X X' : Fin I.n → RV I v) : vec1 p1 (X - X') = vec1 p1 X - vec1 p1 X' := by
  funext i
  simp [vec1]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[vec2]`.
-/
theorem second_coordinate_vector_sub {I : AutInst} {v : HeightOneSpectrum (𝓞 I.F)} (p1 : RV I v →+* KV I v)
    (X X' : Fin I.n → RV I v) : vec2 p1 (X - X') = vec2 p1 X - vec2 p1 X' := by
  funext i
  simp [vec2]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[vec1]`.
-/
theorem first_coordinate_vector_nsmul {I : AutInst} {v : HeightOneSpectrum (𝓞 I.F)} (p1 : RV I v →+* KV I v)
    (c : ℕ) (X : Fin I.n → RV I v) : vec1 p1 ((c : RV I v) • X) = (c : KV I v) • vec1 p1 X := by
  funext i
  simp [vec1]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[vec2]`.
-/
theorem second_coordinate_vector_nsmul {I : AutInst} {v : HeightOneSpectrum (𝓞 I.F)} (p1 : RV I v →+* KV I v)
    (c : ℕ) (X : Fin I.n → RV I v) : vec2 p1 ((c : RV I v) • X) = (c : KV I v) • vec2 p1 X := by
  funext i
  simp [vec2]

end PI.UnitaryGroupMassFormula.ScXuExists.BrB
