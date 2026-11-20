import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCoverPfSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinOrd

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.KExpCut
  Formalism.L2.SG.Full Formalism.L2.SG.Pf.Slab Formalism.L2.SG.Pf.Vanish2
open Matrix

namespace Formalism.L2.SG.Pf.SlabCoverPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Set `b` to `Module.finBasis E ((Fin n → E) ⧸ W)`. Use `⟨Module.finrank E ((Fin n → E) ⧸ W), Matrix.of fun i j => b.coord i (W.mkQ (Pi.single j 1)), fun w => ?_⟩` and prove the remaining obligations. Establish `key : ∀ i, ((Matrix.of fun i j => b.coord i (W.mkQ (Pi.single j 1))) *ᵥ w) i = b.coord i (W.mkQ w)`. Introduce `i`. Use `conv_rhs => rw [show w = ∑ j, w j • Pi.single j 1 by`.

Use function extensionality and compare the values at `x`. Simplify using `[Finset.sum_apply, Pi.single_apply]]`. Simplify using `[Matrix.mulVec, dotProduct, map_sum, mul_comm]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite using `[← Submodule.Quotient.mk_eq_zero]`. Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `i`. Establish `e` using `congrFun h i`. Rewrite `e` using `[key]`.

Simplify using `using e`. Introduce `hw`. Use function extensionality and compare the values at `i`. Rewrite using `[key]`. Simplify using `[(Submodule.Quotient.mk_eq_zero W).2 hw]`.
-/
theorem exists_ker_mat {E : Type*} [Field E] {n : ℕ} (W : Submodule E (Fin n → E)) :
    ∃ (k : ℕ) (B : Matrix (Fin k) (Fin n) E), ∀ w, B *ᵥ w = 0 ↔ w ∈ W := by
  classical
  let b := Module.finBasis E ((Fin n → E) ⧸ W)
  refine ⟨Module.finrank E ((Fin n → E) ⧸ W), Matrix.of fun i j => b.coord i (W.mkQ (Pi.single j 1)),
    fun w => ?_⟩
  have key : ∀ i, ((Matrix.of fun i j => b.coord i (W.mkQ (Pi.single j 1))) *ᵥ w) i =
      b.coord i (W.mkQ w) := by
    intro i
    conv_rhs => rw [show w = ∑ j, w j • Pi.single j 1 by
      funext x; simp [Finset.sum_apply, Pi.single_apply]]
    simp [Matrix.mulVec, dotProduct, map_sum, mul_comm]
  constructor
  · intro h
    rw [← Submodule.Quotient.mk_eq_zero]
    apply b.repr.injective
    ext i
    have e := congrFun h i
    rw [key] at e
    simpa using e
  · intro hw
    funext i
    rw [key]
    simp [(Submodule.Quotient.mk_eq_zero W).2 hw]

/- English proof (translation)
Take `⟨k, B, hB⟩` from `exists_ker_mat (Submodule.span X.B.I.E T)`. Rewrite using `[← hB w]`. Establish `hφ : ∀ y : Fin X.B.I.n → X.B.I.E, (B.map (X.B.I.φ v)) *ᵥ (fun i => X.B.I.φ v (y i)) = fun i => X.B.I.φ v ((B *ᵥ y) i)`. Introduce `y`. Use function extensionality and compare the values at `i`.

Simplify using `[Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]`. Establish `hrv : ∀ y, (fun i => X.B.I.φ v (y i)) = X.B.I.P v *ᵥ rv X.B.I v y`. Introduce `y`. Rewrite using `[rv, Matrix.mulVec_mulVec, Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.one_mulVec]`. Set `M : (Fin X.B.I.n → ℂ) →ₗ[ℂ] (Fin k → ℂ)` to `Matrix.mulVecLin (B.map (X.B.I.φ v) * X.B.I.P v)`.

Establish `hM : ∀ y, M (rv X.B.I v y) = fun i => X.B.I.φ v ((B *ᵥ y) i)`. Introduce `y`. Simplify using `only [M, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, ← hrv, hφ]`. Establish `hT : ∀ t ∈ T, M (rv X.B.I v t) = 0`. Introduce `t ht`.

Rewrite using `[hM, (hB t).2 (Submodule.subset_span ht)]`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Establish `hle : Submodule.span ℂ (rv X.B.I v '' T) ≤ LinearMap.ker M`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨t, ht, rfl⟩`. Conclude with `hT t ht`. Establish `hw0 : M (rv X.B.I v w) = 0` using `hle h`. Rewrite `hw0` using `[hM]`. Use function extensionality and compare the values at `i`.

Establish `e` using `congrFun hw0 i`. Conclude with `(map_eq_zero_iff _ (X.B.I.φ v).injective).1 e`.
-/
theorem rv_desc {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) (T : Set (Fin X.B.I.n → X.B.I.E))
    (w : Fin X.B.I.n → X.B.I.E) (h : rv X.B.I v w ∈ Submodule.span ℂ (rv X.B.I v '' T)) :
    w ∈ Submodule.span X.B.I.E T := by
  classical
  obtain ⟨k, B, hB⟩ := exists_ker_mat (Submodule.span X.B.I.E T)
  rw [← hB w]
  have hφ : ∀ y : Fin X.B.I.n → X.B.I.E,
      (B.map (X.B.I.φ v)) *ᵥ (fun i => X.B.I.φ v (y i)) = fun i => X.B.I.φ v ((B *ᵥ y) i) := by
    intro y
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  have hrv : ∀ y, (fun i => X.B.I.φ v (y i)) = X.B.I.P v *ᵥ rv X.B.I v y := by
    intro y
    rw [rv, Matrix.mulVec_mulVec, Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.one_mulVec]
  let M : (Fin X.B.I.n → ℂ) →ₗ[ℂ] (Fin k → ℂ) := Matrix.mulVecLin (B.map (X.B.I.φ v) * X.B.I.P v)
  have hM : ∀ y, M (rv X.B.I v y) = fun i => X.B.I.φ v ((B *ᵥ y) i) := by
    intro y
    simp only [M, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, ← hrv, hφ]
  have hT : ∀ t ∈ T, M (rv X.B.I v t) = 0 := by
    intro t ht
    rw [hM, (hB t).2 (Submodule.subset_span ht)]
    funext i
    simp
  have hle : Submodule.span ℂ (rv X.B.I v '' T) ≤ LinearMap.ker M := by
    rw [Submodule.span_le]
    rintro _ ⟨t, ht, rfl⟩
    exact hT t ht
  have hw0 : M (rv X.B.I v w) = 0 := hle h
  rw [hM] at hw0
  funext i
  have e := congrFun hw0 i
  exact (map_eq_zero_iff _ (X.B.I.φ v).injective).1 e

def toVHom {D : D7} (X : HidaSetting D) : (Fin X.B.I.n → X.B.I.E) →+ (VS D).V where
  toFun := toV X
  map_zero' := by
    have h := toV_add X 0 0
    rw [add_zero] at h
    exact left_eq_add.1 h
  map_add' := toV_add X

/- English proof (translation)
Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, rfl⟩` from `hy`. Use `show toV X (X.crd (X.eX a)) ∈ _`. Rewrite using `[toV_crd]`.

Conclude with `Submodule.subset_span ⟨a, ha, rfl⟩`. Consider the case `zero`. Rewrite using `[show toV X 0 = 0 from (toVHom X).map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`.

Rewrite using `[toV_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx`. Rewrite using `[toV_smul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem toV_span {D : D7} (X : HidaSetting D) {S : Set (Fin D.R.rS)} {w : Fin X.B.I.n → X.B.I.E}
    (hw : w ∈ Submodule.span X.B.I.E (X.eR '' S)) : toV X w ∈ Submodule.span D.host.E (X.eX '' S) := by
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    show toV X (X.crd (X.eX a)) ∈ _
    rw [toV_crd]
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  | zero =>
    rw [show toV X 0 = 0 from (toVHom X).map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [toV_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [toV_smul]
    exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Introduce `D X Y u ρ ν hKL hν h1 _ hK2`. Take `⟨γ, hγU, hγinf, hγfin⟩` from `hν`. Establish `hrvg : ∀ (v : InfinitePlace X.B.I.F) (y : Fin X.B.I.n → X.B.I.E), rv X.B.I v ((γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y) = uMat (ν.1 v) *ᵥ rv X.B.I v y`. Introduce `v y`. Rewrite using `[hγinf v, rv, rv]`.

Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.mul_one]`. Rewrite using `[← Matrix.mulVec_mulVec]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]`.

Establish `hsub : ∀ (v : InfinitePlace X.B.I.F) (y : Fin X.B.I.n → X.B.I.E), (uMat (ν.1 v) - 1) *ᵥ rv X.B.I v y = rv X.B.I v ((γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y - y)`. Introduce `v y`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, ← hrvg]`. Conclude with `(map_sub (Formalism.L2.SG.Pf.Level.rvHom X v) _ _).symm`. Establish `hdesc : ∀ (S : Set (Fin D.R.rS)) (x : (VS D).V), (∀ v, (uMat (ν.1 v) - 1) *ᵥ rv X.B.I v (X.crd x) ∈ Submodule.span ℂ ((fun a => rv X.B.I v (X.eR a)) '' S)) → matEC X γ x - x ∈ Submodule.span D.host.E (X.eX '' S)`.

Introduce `S x hx`. Take `⟨v⟩ : Nonempty (InfinitePlace X.B.I.F)` from `inferInstance`. Establish `h` using `hx v`. Rewrite `h` using `[hsub, ← Set.image_image (fun w => rv X.B.I v w) X.eR S]`. Establish `hw` using `rv_desc X v _ _ h`.

Establish `e : matEC X γ x - x = toV X ((γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd x - X.crd x)`. Rewrite using `[← matE_crdC X γ x, ← crd_sub', toV_crd]`. Rewrite using `[e]`. Conclude with `toV_span X hw`. Use `show ∃ (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X x n ∧ ν.1 = x.1 ∧ n ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u))`.

Use `⟨ν, matEC X γ, ⟨γ, hγU, hγinf, hγfin, fun y => matE_crdC X γ y⟩, rfl, ?_⟩` and prove the remaining obligations. Use `show _ ∧ _ ∧ _`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[isAutLam_iff]`. Use `⟨fun x y => matE_isomC X γ hγU x y, fun y => ?_⟩` and prove the remaining obligations.

Rewrite using `[(Y.cs u).lat_eq ρ (matEC X γ y), (Y.cs u).lat_eq ρ y, matE_inclC, ← hγfin, Matrix.mulVec_mulVec]`. Establish `hk : ∀ w, w ∈ X.B.I.Lf ↔ X.B.I.fmat ((((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ν.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)) *ᵥ w ∈ X.B.I.Lf` using `hKL.2.1 _ hK2`. Establish `e : X.B.I.fmat (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * X.B.I.fmat ν.2 = X.B.I.fmat ((((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ν.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)) * X.B.I.fmat (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹`. Simplify using `[AutInst.fmat, Matrix.mul_assoc]`. Rewrite using `[e, ← Matrix.mulVec_mulVec]`.

Conclude with `(hk _).symm`. Introduce `j x hx`. Express the relevant statement in the definitionally equal form `x ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j + 1}) at hx`. Express the relevant statement in the definitionally equal form `matEC X γ x - x ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j})`. Rewrite `hx`, the goal using `[X.Fu_e u]`.

Set `Lm : (VS D).V →ₗ[D.host.E] (VS D).V` to `(matEC X γ : (VS D).V →ₗ[D.host.E] (VS D).V) - LinearMap.id`. Establish `hL : ∀ y, Lm y = matEC X γ y - y` using `fun y => rfl`. Rewrite using `[← hL]`. Use `(Submodule.span_le (p := (Submodule.span D.host.E (X.eX '' {i | i.1 < j})).comap Lm)).2 ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨i, hi, rfl⟩`.

Use `show X.eX i ∈ (Submodule.span D.host.E (X.eX '' {i | i.1 < j})).comap Lm`. Rewrite using `[Submodule.mem_comap, hL]`. Use `Submodule.span_mono (Set.image_mono fun b hb => ?_) (hdesc {b | b.1 < i.1} (X.eX i) fun v => (h1 v).1.1 i)` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hb hi ⊢`. Use linear arithmetic over natural numbers and integers.

Introduce `x hx`. Simplify using `only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx`. Establish `hx' : ∀ a, (VS D).hT (X.eX a) x = 0`. Introduce `a`. Use `hx (X.eX a) ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `X.eX a ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)`. Rewrite using `[X.Fu_e u]`. Conclude with `Submodule.subset_span ⟨a, rfl⟩`. Express the relevant statement in the definitionally equal form `matEC X γ x - x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)`. Rewrite using `[X.Fu_e u]`.

Establish `hsp : Submodule.span D.host.E (X.eX '' {b : Fin D.R.rS | b.1 < D.R.rS}) = Submodule.span D.host.E (Set.range X.eX)`. Use `congr 1`. Use extensionality with `y`. Simplify using the standard rewrite rules. Rewrite using `[← hsp]`.

Use `hdesc _ x fun v => (h1 v).2 _ fun a => ?_` and prove the remaining obligations. Use `show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.eX a))) (rv X.B.I v (X.crd x)) = 0`. Rewrite using `[hJ_crd, hx' a, map_zero]`.
-/
theorem nilradical_rational_lattice : NRatLam := by
  intro D X Y u ρ ν hKL hν h1 _ hK2
  obtain ⟨γ, hγU, hγinf, hγfin⟩ := hν

  have hrvg : ∀ (v : InfinitePlace X.B.I.F) (y : Fin X.B.I.n → X.B.I.E),
      rv X.B.I v ((γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y) =
        uMat (ν.1 v) *ᵥ rv X.B.I v y := by
    intro v y
    rw [hγinf v, rv, rv]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.mul_one]
    rw [← Matrix.mulVec_mulVec]
    congr 1
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  have hsub : ∀ (v : InfinitePlace X.B.I.F) (y : Fin X.B.I.n → X.B.I.E),
      (uMat (ν.1 v) - 1) *ᵥ rv X.B.I v y =
        rv X.B.I v ((γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y - y) := by
    intro v y
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← hrvg]
    exact (map_sub (Formalism.L2.SG.Pf.Level.rvHom X v) _ _).symm

  have hdesc : ∀ (S : Set (Fin D.R.rS)) (x : (VS D).V),
      (∀ v, (uMat (ν.1 v) - 1) *ᵥ rv X.B.I v (X.crd x) ∈
        Submodule.span ℂ ((fun a => rv X.B.I v (X.eR a)) '' S)) →
      matEC X γ x - x ∈ Submodule.span D.host.E (X.eX '' S) := by
    intro S x hx
    obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
    have h := hx v
    rw [hsub, ← Set.image_image (fun w => rv X.B.I v w) X.eR S] at h
    have hw := rv_desc X v _ _ h
    have e : matEC X γ x - x =
        toV X ((γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd x - X.crd x) := by
      rw [← matE_crdC X γ x, ← crd_sub', toV_crd]
    rw [e]
    exact toV_span X hw
  show ∃ (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X x n ∧ ν.1 = x.1 ∧
    n ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u))
  refine ⟨ν, matEC X γ, ⟨γ, hγU, hγinf, hγfin, fun y => matE_crdC X γ y⟩, rfl, ?_⟩
  show _ ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [isAutLam_iff]
    refine ⟨fun x y => matE_isomC X γ hγU x y, fun y => ?_⟩
    rw [(Y.cs u).lat_eq ρ (matEC X γ y), (Y.cs u).lat_eq ρ y, matE_inclC, ← hγfin, Matrix.mulVec_mulVec]
    have hk : ∀ w, w ∈ X.B.I.Lf ↔ X.B.I.fmat ((((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ν.2 *
        (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)) *ᵥ w ∈ X.B.I.Lf := hKL.2.1 _ hK2
    have e : X.B.I.fmat (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * X.B.I.fmat ν.2 =
        X.B.I.fmat ((((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ν.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)) *
          X.B.I.fmat (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ := by
      simp [AutInst.fmat, Matrix.mul_assoc]
    rw [e, ← Matrix.mulVec_mulVec]
    exact (hk _).symm
  · intro j x hx
    change x ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j + 1}) at hx
    change matEC X γ x - x ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j})
    rw [X.Fu_e u] at hx ⊢
    let Lm : (VS D).V →ₗ[D.host.E] (VS D).V :=
      (matEC X γ : (VS D).V →ₗ[D.host.E] (VS D).V) - LinearMap.id
    have hL : ∀ y, Lm y = matEC X γ y - y := fun y => rfl
    rw [← hL]
    refine (Submodule.span_le (p := (Submodule.span D.host.E (X.eX '' {i | i.1 < j})).comap Lm)).2 ?_ hx
    rintro _ ⟨i, hi, rfl⟩
    show X.eX i ∈ (Submodule.span D.host.E (X.eX '' {i | i.1 < j})).comap Lm
    rw [Submodule.mem_comap, hL]
    refine Submodule.span_mono (Set.image_mono fun b hb => ?_)
      (hdesc {b | b.1 < i.1} (X.eX i) fun v => (h1 v).1.1 i)
    simp only [Set.mem_setOf_eq] at hb hi ⊢
    omega
  · intro x hx
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
    have hx' : ∀ a, (VS D).hT (X.eX a) x = 0 := by
      intro a
      refine hx (X.eX a) ?_
      change X.eX a ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)
      rw [X.Fu_e u]
      exact Submodule.subset_span ⟨a, rfl⟩
    change matEC X γ x - x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)
    rw [X.Fu_e u]
    have hsp : Submodule.span D.host.E (X.eX '' {b : Fin D.R.rS | b.1 < D.R.rS}) =
        Submodule.span D.host.E (Set.range X.eX) := by
      congr 1
      ext y
      simp
    rw [← hsp]
    refine hdesc _ x fun v => (h1 v).2 _ fun a => ?_
    show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.eX a))) (rv X.B.I v (X.crd x)) = 0
    rw [hJ_crd, hx' a, map_zero]

end Formalism.L2.SG.Pf.SlabCoverPf
