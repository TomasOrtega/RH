import Mathlib
import GroundTheory.PAdicHodge.SlopePhiModule
import GroundTheory.PAdicHodge.SlopeBezout
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace PhiModule

open Matrix Module

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] {φ : R →+* R}
variable {M : Type*} [AddCommGroup M] [Module R M]

def IsStable (Φ : M →ₛₗ[φ] M) (N : Submodule R M) : Prop := ∀ x ∈ N, Φ x ∈ N

def restrict (Φ : M →ₛₗ[φ] M) (N : Submodule R M) (h : IsStable Φ N) : N →ₛₗ[φ] N where
  toFun x := ⟨Φ (x : M), h _ x.2⟩
  map_add' x y := Subtype.ext (map_add Φ (x : M) y)
  map_smul' r x := Subtype.ext (Φ.map_smulₛₗ r (x : M))

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_restrict_apply (Φ : M →ₛₗ[φ] M) (N : Submodule R M) (h : IsStable Φ N)
    (x : N) : (restrict Φ N h x : M) = Φ (x : M) := rfl

def quot (Φ : M →ₛₗ[φ] M) (N : Submodule R M) (h : IsStable Φ N) :
    (M ⧸ N) →ₛₗ[φ] (M ⧸ N) :=
  N.mapQ N Φ h

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem quot_mk (Φ : M →ₛₗ[φ] M) (N : Submodule R M) (h : IsStable Φ N) (x : M) :
    quot Φ N h (Submodule.Quotient.mk x) = Submodule.Quotient.mk (Φ x) := rfl

/- English proof (translation)
Introduce and unpack `x ⟨r, hr, hx⟩`. Use `⟨φ r, fun h0 => hr (hφ (by rw [h0, map_zero])), ?_⟩` and prove the remaining obligations. Rewrite using `[← Φ.map_smulₛₗ]`. Conclude with `h _ hx`.
-/
theorem IsStable.saturation [IsDomain R] {Φ : M →ₛₗ[φ] M} {N : Submodule R M} (h : IsStable Φ N)
    (hφ : Function.Injective φ) : IsStable Φ (saturation N) := by
  rintro x ⟨r, hr, hx⟩
  refine ⟨φ r, fun h0 => hr (hφ (by rw [h0, map_zero])), ?_⟩
  rw [← Φ.map_smulₛₗ]
  exact h _ hx

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[phiMatrix_apply, ← he]`.
-/
theorem phiMatrix_map {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] (b : Basis ι R M)
    (e : M ≃ₗ[R] M₂) {Φ : M →ₛₗ[φ] M} {Φ₂ : M₂ →ₛₗ[φ] M₂} (he : ∀ x, e (Φ x) = Φ₂ (e x)) :
    phiMatrix (b.map e) Φ₂ = phiMatrix b Φ := by
  ext i j
  simp [phiMatrix_apply, ← he]

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis R M`. Rewrite using `[isPhiModule_iff_isUnit_det b, isPhiModule_iff_isUnit_det (b.map e), phiMatrix_map b e he]`.
-/
theorem isPhiModule_congr {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] [Module.Free R M]
    [Module.Finite R M] (e : M ≃ₗ[R] M₂) {Φ : M →ₛₗ[φ] M} {Φ₂ : M₂ →ₛₗ[φ] M₂}
    (he : ∀ x, e (Φ x) = Φ₂ (e x)) : IsPhiModule Φ ↔ IsPhiModule Φ₂ := by
  classical
  let b := Module.Free.chooseBasis R M
  rw [isPhiModule_iff_isUnit_det b, isPhiModule_iff_isUnit_det (b.map e), phiMatrix_map b e he]

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis R M`. Distinguish the cases in `h : IsPhiModule Φ`. Establish `h₂` using `(isPhiModule_congr e he).1 h`. Rewrite using `[deg_eq v b Φ h, deg_eq v (b.map e) Φ₂ h₂, degIn, degIn]`. Conclude with `v.ord_unit_eq _ _ (by rw [phiMatrix_map b e he])`.

Establish `h₂ : ¬ IsPhiModule Φ₂` using `fun h₂ => h ((isPhiModule_congr e he).2 h₂)`. Rewrite using `[deg, deg, dif_neg h, dif_neg h₂]`.
-/
theorem deg_congr [Nontrivial R] (v : UnitOrd R φ) {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]
    [Module.Free R M] [Module.Finite R M] [Module.Free R M₂] [Module.Finite R M₂]
    (e : M ≃ₗ[R] M₂) {Φ : M →ₛₗ[φ] M} {Φ₂ : M₂ →ₛₗ[φ] M₂} (he : ∀ x, e (Φ x) = Φ₂ (e x)) :
    deg v Φ₂ = deg v Φ := by
  classical
  let b := Module.Free.chooseBasis R M
  by_cases h : IsPhiModule Φ
  · have h₂ := (isPhiModule_congr e he).1 h
    rw [deg_eq v b Φ h, deg_eq v (b.map e) Φ₂ h₂, degIn, degIn]
    exact v.ord_unit_eq _ _ (by rw [phiMatrix_map b e he])
  · have h₂ : ¬ IsPhiModule Φ₂ := fun h₂ => h ((isPhiModule_congr e he).2 h₂)
    rw [deg, deg, dif_neg h, dif_neg h₂]

section Adapted

variable {N N' : Submodule R M} (hc : IsCompl N N') {κ κ' : Type*} [Fintype κ] [Fintype κ']
  [DecidableEq κ] [DecidableEq κ'] (bN : Basis κ R N) (bN' : Basis κ' R N')

def adaptedBasis : Basis (κ ⊕ κ') R M := (bN.prod bN').map (Submodule.prodEquivOfIsCompl N N' hc)

/- English proof (translation)
Simplify using `[adaptedBasis, Basis.prod_apply]`.
-/
theorem adaptedBasis_inl (i : κ) : adaptedBasis hc bN bN' (Sum.inl i) = bN i := by
  simp [adaptedBasis, Basis.prod_apply]

/- English proof (translation)
Simplify using `[adaptedBasis, Basis.prod_apply]`.
-/
theorem adaptedBasis_inr (i : κ') : adaptedBasis hc bN bN' (Sum.inr i) = bN' i := by
  simp [adaptedBasis, Basis.prod_apply]

/- English proof (translation)
Simplify using `[adaptedBasis, Basis.prod_repr_inl]`.
-/
theorem adaptedBasis_repr_inl (x : M) (i : κ) :
    (adaptedBasis hc bN bN').repr x (Sum.inl i) = bN.repr (N.projectionOnto N' hc x) i := by
  simp [adaptedBasis, Basis.prod_repr_inl]

/- English proof (translation)
Simplify using `[adaptedBasis, Basis.prod_repr_inr]`.
-/
theorem adaptedBasis_repr_inr (x : M) (i : κ') :
    (adaptedBasis hc bN bN').repr x (Sum.inr i) = bN'.repr (N'.projectionOnto N hc.symm x) i := by
  simp [adaptedBasis, Basis.prod_repr_inr]

def quotBasis : Basis κ' R (M ⧸ N) := bN'.map (N.quotientEquivOfIsCompl N' hc).symm

/- English proof (translation)
Simplify using `[quotBasis]`.
-/
theorem quotBasis_apply (i : κ') : quotBasis hc bN' i = Submodule.Quotient.mk (bN' i : M) := by
  simp [quotBasis]

/- English proof (translation)
Simplify using `[quotBasis]`.
-/
theorem quotBasis_repr_mk (x : M) (i : κ') :
    (quotBasis hc bN').repr (Submodule.Quotient.mk x) i = bN'.repr (N'.projectionOnto N hc.symm x) i := by
  simp [quotBasis]

/- English proof (translation)
Establish `e : phiMatrix (adaptedBasis hc bN bN') Φ = Matrix.fromBlocks (phiMatrix bN (restrict Φ N h)) (Matrix.of fun i j => (adaptedBasis hc bN bN').repr (Φ (bN' j)) (Sum.inl i)) 0 (phiMatrix (quotBasis hc bN') (quot Φ N h))`. Use extensionality with `(i | i) (j | j)`. Rewrite using `[phiMatrix_apply, adaptedBasis_inl, adaptedBasis_repr_inl, Matrix.fromBlocks_apply₁₁, phiMatrix_apply, ← coe_restrict_apply Φ N h, Submodule.projectionOnto_apply_left]`. Rewrite using `[phiMatrix_apply, adaptedBasis_inr, Matrix.fromBlocks_apply₁₂, Matrix.of_apply]`. Rewrite using `[phiMatrix_apply, adaptedBasis_inl, adaptedBasis_repr_inr, Matrix.fromBlocks_apply₂₁, ← coe_restrict_apply Φ N h, Submodule.projectionOnto_apply_right]`.

Simplify using the standard rewrite rules. Rewrite using `[phiMatrix_apply, adaptedBasis_inr, adaptedBasis_repr_inr, Matrix.fromBlocks_apply₂₂, phiMatrix_apply, quotBasis_apply, quot_mk, quotBasis_repr_mk]`. Rewrite using `[e, Matrix.det_fromBlocks_zero₂₁]`.
-/
theorem det_phiMatrix_adapted (Φ : M →ₛₗ[φ] M) (h : IsStable Φ N) :
    (phiMatrix (adaptedBasis hc bN bN') Φ).det =
      (phiMatrix bN (restrict Φ N h)).det * (phiMatrix (quotBasis hc bN') (quot Φ N h)).det := by
  have e : phiMatrix (adaptedBasis hc bN bN') Φ = Matrix.fromBlocks (phiMatrix bN (restrict Φ N h))
      (Matrix.of fun i j => (adaptedBasis hc bN bN').repr (Φ (bN' j)) (Sum.inl i)) 0
      (phiMatrix (quotBasis hc bN') (quot Φ N h)) := by
    ext (i | i) (j | j)
    · rw [phiMatrix_apply, adaptedBasis_inl, adaptedBasis_repr_inl, Matrix.fromBlocks_apply₁₁,
        phiMatrix_apply, ← coe_restrict_apply Φ N h, Submodule.projectionOnto_apply_left]
    · rw [phiMatrix_apply, adaptedBasis_inr, Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
    · rw [phiMatrix_apply, adaptedBasis_inl, adaptedBasis_repr_inr, Matrix.fromBlocks_apply₂₁,
        ← coe_restrict_apply Φ N h, Submodule.projectionOnto_apply_right]
      simp
    · rw [phiMatrix_apply, adaptedBasis_inr, adaptedBasis_repr_inr, Matrix.fromBlocks_apply₂₂,
        phiMatrix_apply, quotBasis_apply, quot_mk, quotBasis_repr_mk]
  rw [e, Matrix.det_fromBlocks_zero₂₁]

end Adapted

section Bezout

variable [IsDomain R] [IsBezout R] [Module.Free R M] [Module.Finite R M]

/- English proof (translation)
The claim follows from `free_of_isTorsionFree_quotient N`.
-/
theorem free_of_saturated (N : Submodule R M) [Module.IsTorsionFree R (M ⧸ N)] : Module.Free R N :=
  free_of_isTorsionFree_quotient N

/- English proof (translation)
The claim follows from `finite_of_isTorsionFree_quotient N`.
-/
theorem finite_of_saturated (N : Submodule R M) [Module.IsTorsionFree R (M ⧸ N)] :
    Module.Finite R N :=
  finite_of_isTorsionFree_quotient N

/- English proof (translation)
The claim follows from `free_quotient_of_isTorsionFree N`.
-/
theorem free_quot_of_saturated (N : Submodule R M) [Module.IsTorsionFree R (M ⧸ N)] :
    Module.Free R (M ⧸ N) :=
  free_quotient_of_isTorsionFree N

/- English proof (translation)
Take `⟨N', hc⟩` from `exists_isCompl_of_isTorsionFree_quotient N`. Set `bN` to `Module.Free.chooseBasis R N`. Set `bQ` to `Module.Free.chooseBasis R (M ⧸ N)`. Set `bN'` to `bQ.map (N.quotientEquivOfIsCompl N' hc)`. Establish `hq : quotBasis hc bN' = bQ`.

Use extensionality with `i`. Simplify using `[quotBasis, bN']`. Use `⟨adaptedBasis hc bN bN', ?_⟩` and prove the remaining obligations. Rewrite using `[det_phiMatrix_adapted hc bN bN' Φ h, hq]`.
-/
theorem exists_det_eq_mul (Φ : M →ₛₗ[φ] M) (N : Submodule R M) (h : IsStable Φ N)
    [Module.IsTorsionFree R (M ⧸ N)] [Module.Free R N] [Module.Finite R N]
    [Module.Free R (M ⧸ N)] :
    ∃ b : Basis (Module.Free.ChooseBasisIndex R N ⊕ Module.Free.ChooseBasisIndex R (M ⧸ N)) R M,
      (phiMatrix b Φ).det = (phiMatrix (Module.Free.chooseBasis R N) (restrict Φ N h)).det *
        (phiMatrix (Module.Free.chooseBasis R (M ⧸ N)) (quot Φ N h)).det := by
  classical
  obtain ⟨N', hc⟩ := exists_isCompl_of_isTorsionFree_quotient N
  let bN := Module.Free.chooseBasis R N
  let bQ := Module.Free.chooseBasis R (M ⧸ N)
  let bN' := bQ.map (N.quotientEquivOfIsCompl N' hc)
  have hq : quotBasis hc bN' = bQ := by
    ext i
    simp [quotBasis, bN']
  refine ⟨adaptedBasis hc bN bN', ?_⟩
  rw [det_phiMatrix_adapted hc bN bN' Φ h, hq]

/- English proof (translation)
Use `free_of_saturated N` as an intermediate fact. Use `finite_of_saturated N` as an intermediate fact. Use `free_quot_of_saturated N` as an intermediate fact. Take `⟨b, hb⟩` from `exists_det_eq_mul Φ N h`. Rewrite `hΦ` using `[isPhiModule_iff_isUnit_det b, hb]`.

Rewrite using `[isPhiModule_iff_isUnit_det (Module.Free.chooseBasis R N)]`. Conclude with `isUnit_of_mul_isUnit_left hΦ`.
-/
theorem isPhiModule_restrict {Φ : M →ₛₗ[φ] M} (hΦ : IsPhiModule Φ) {N : Submodule R M}
    (h : IsStable Φ N) [Module.IsTorsionFree R (M ⧸ N)] : IsPhiModule (restrict Φ N h) := by
  classical
  have := free_of_saturated N
  have := finite_of_saturated N
  have := free_quot_of_saturated N
  obtain ⟨b, hb⟩ := exists_det_eq_mul Φ N h
  rw [isPhiModule_iff_isUnit_det b, hb] at hΦ
  rw [isPhiModule_iff_isUnit_det (Module.Free.chooseBasis R N)]
  exact isUnit_of_mul_isUnit_left hΦ

/- English proof (translation)
Use `free_of_saturated N` as an intermediate fact. Use `finite_of_saturated N` as an intermediate fact. Use `free_quot_of_saturated N` as an intermediate fact. Take `⟨b, hb⟩` from `exists_det_eq_mul Φ N h`. Rewrite `hΦ` using `[isPhiModule_iff_isUnit_det b, hb]`.

Rewrite using `[isPhiModule_iff_isUnit_det (Module.Free.chooseBasis R (M ⧸ N))]`. Conclude with `isUnit_of_mul_isUnit_right hΦ`.
-/
theorem isPhiModule_quot {Φ : M →ₛₗ[φ] M} (hΦ : IsPhiModule Φ) {N : Submodule R M}
    (h : IsStable Φ N) [Module.IsTorsionFree R (M ⧸ N)] : IsPhiModule (quot Φ N h) := by
  classical
  have := free_of_saturated N
  have := finite_of_saturated N
  have := free_quot_of_saturated N
  obtain ⟨b, hb⟩ := exists_det_eq_mul Φ N h
  rw [isPhiModule_iff_isUnit_det b, hb] at hΦ
  rw [isPhiModule_iff_isUnit_det (Module.Free.chooseBasis R (M ⧸ N))]
  exact isUnit_of_mul_isUnit_right hΦ

/- English proof (translation)
Take `⟨b, hb⟩` from `exists_det_eq_mul Φ N h`. Establish `hN` using `isPhiModule_restrict hΦ h`. Establish `hQ` using `isPhiModule_quot hΦ h`. Rewrite using `[deg_eq v b Φ hΦ, deg_eq v (Module.Free.chooseBasis R N) _ hN, deg_eq v (Module.Free.chooseBasis R (M ⧸ N)) _ hQ, degIn, degIn, degIn, ← v.ord_unit_mul]`. Conclude with `v.ord_unit_eq _ _ hb`.
-/
theorem deg_eq_deg_restrict_add (v : UnitOrd R φ) {Φ : M →ₛₗ[φ] M}
    (hΦ : IsPhiModule Φ) {N : Submodule R M} (h : IsStable Φ N) [Module.IsTorsionFree R (M ⧸ N)]
    [Module.Free R N] [Module.Finite R N] [Module.Free R (M ⧸ N)] :
    deg v Φ = deg v (restrict Φ N h) + deg v (quot Φ N h) := by
  classical
  obtain ⟨b, hb⟩ := exists_det_eq_mul Φ N h
  have hN := isPhiModule_restrict hΦ h
  have hQ := isPhiModule_quot hΦ h
  rw [deg_eq v b Φ hΦ, deg_eq v (Module.Free.chooseBasis R N) _ hN,
    deg_eq v (Module.Free.chooseBasis R (M ⧸ N)) _ hQ, degIn, degIn, degIn,
    ← v.ord_unit_mul]
  exact v.ord_unit_eq _ _ hb

end Bezout

section FullRank

/- English proof (translation)
Use extensionality with `k j`. Establish `hlin : ∀ y : I, ∑ m, bN.repr (Submodule.inclusion hIN (bI m)) k * bI.repr y m = bN.repr (Submodule.inclusion hIN y) k`. Introduce `y`. Use `congrArg (fun z => bN.repr (Submodule.inclusion hIN z) k) (bI.sum_repr y)` as an intermediate fact. Simplify using `only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul] at this`.

Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun m _ => mul_comm _ _`. Establish `e1 : Submodule.inclusion hIN (restrict Φ I hI (bI j)) = restrict Φ N hN (Submodule.inclusion hIN (bI j))` using `rfl`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.of_apply, phiMatrix_apply]`.

Rewrite using `[hlin, e1, repr_phi]`. Simplify using `[Matrix.mul_apply, mulVec, dotProduct, phiMatrix_apply]`.
-/
theorem mul_phiMatrix_eq_of_le {Φ : M →ₛₗ[φ] M} {I N : Submodule R M} (hIN : I ≤ N)
    (hI : IsStable Φ I) (hN : IsStable Φ N) (bI : Basis ι R I) (bN : Basis ι R N) :
    (Matrix.of fun k j => bN.repr (Submodule.inclusion hIN (bI j)) k) *
        phiMatrix bI (restrict Φ I hI) =
      phiMatrix bN (restrict Φ N hN) *
        (Matrix.of fun k j => bN.repr (Submodule.inclusion hIN (bI j)) k).map φ := by
  ext k j
  have hlin : ∀ y : I, ∑ m, bN.repr (Submodule.inclusion hIN (bI m)) k * bI.repr y m =
      bN.repr (Submodule.inclusion hIN y) k := by
    intro y
    have := congrArg (fun z => bN.repr (Submodule.inclusion hIN z) k) (bI.sum_repr y)
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul] at this
    rw [← this]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have e1 : Submodule.inclusion hIN (restrict Φ I hI (bI j)) =
      restrict Φ N hN (Submodule.inclusion hIN (bI j)) := rfl
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply, phiMatrix_apply]
  rw [hlin, e1, repr_phi]
  simp [Matrix.mul_apply, mulVec, dotProduct, phiMatrix_apply]

/- English proof (translation)
Use `set X : Matrix ι ι R := Matrix.of fun k j => bN.repr (Submodule.inclusion hIN (bI j)) k`. Use `⟨X.det, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Take `⟨c, hc0, hc⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Apply `hc0` to reduce the goal to its premises.

Establish `key : Submodule.inclusion hIN (∑ j, c j • bI j) = 0`. Apply `bN.repr.injective` to reduce the goal to its premises. Use extensionality with `k`. Use `congrFun hc k` as an intermediate fact. Simplify using `only [mulVec, dotProduct, X, Matrix.of_apply, Pi.zero_apply] at this`.

Simplify using `[map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, ← this, mul_comm]`. Establish `h2 : ∑ j, c j • bI j = 0` using `Submodule.inclusion_injective hIN (by rw [key, map_zero])`. Use `bI.linearIndependent` as an intermediate fact. Rewrite `this` using `[Fintype.linearIndependent_iff]`. Use function extensionality and compare the values at `j`.

Conclude with `this c h2 j`. Rewrite using `[← det_mul, mul_phiMatrix_eq_of_le hIN hI hN bI bN, det_mul, RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem exists_det_mul_eq_of_le [IsDomain R] {Φ : M →ₛₗ[φ] M} {I N : Submodule R M}
    (hIN : I ≤ N) (hI : IsStable Φ I) (hN : IsStable Φ N) (bI : Basis ι R I) (bN : Basis ι R N) :
    ∃ f : R, f ≠ 0 ∧ f * (phiMatrix bI (restrict Φ I hI)).det =
      (phiMatrix bN (restrict Φ N hN)).det * φ f := by
  set X : Matrix ι ι R := Matrix.of fun k j => bN.repr (Submodule.inclusion hIN (bI j)) k
  refine ⟨X.det, ?_, ?_⟩
  · intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hc0
    have key : Submodule.inclusion hIN (∑ j, c j • bI j) = 0 := by
      apply bN.repr.injective
      ext k
      have := congrFun hc k
      simp only [mulVec, dotProduct, X, Matrix.of_apply, Pi.zero_apply] at this
      simp [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, ← this, mul_comm]
    have h2 : ∑ j, c j • bI j = 0 := Submodule.inclusion_injective hIN (by rw [key, map_zero])
    have := bI.linearIndependent
    rw [Fintype.linearIndependent_iff] at this
    funext j
    exact this c h2 j
  · rw [← det_mul, mul_phiMatrix_eq_of_le hIN hI hN bI bN, det_mul, RingHom.map_det]
    rfl

end FullRank

section Equivariant

variable {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]

def IsEquivariant (f : M →ₗ[R] M₂) (Φ : M →ₛₗ[φ] M) (Φ₂ : M₂ →ₛₗ[φ] M₂) : Prop :=
  ∀ x, f (Φ x) = Φ₂ (f x)

variable {f : M →ₗ[R] M₂} {Φ : M →ₛₗ[φ] M} {Φ₂ : M₂ →ₛₗ[φ] M₂}

/- English proof (translation)
Introduce `x hx` and use `by rw [LinearMap.mem_ker] at hx ⊢; rw [hf, hx, map_zero]`.
-/
theorem IsEquivariant.isStable_ker (hf : IsEquivariant f Φ Φ₂) : IsStable Φ (LinearMap.ker f) :=
  fun x hx => by rw [LinearMap.mem_ker] at hx ⊢; rw [hf, hx, map_zero]

/- English proof (translation)
Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨Φ x, hf x⟩`.
-/
theorem IsEquivariant.isStable_range (hf : IsEquivariant f Φ Φ₂) :
    IsStable Φ₂ (LinearMap.range f) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨Φ x, hf x⟩

/- English proof (translation)
The claim follows from `(saturation_eq_self_iff (N := LinearMap.ker f)).1 (le_antisymm (fun x ⟨r, hr, hx⟩ => by rw [LinearMap.mem_ker, map_smul] at hx rw [LinearMap.mem_ker] exact (smul_eq_zero.1 hx).resolve_left hr) (le_saturation _))`.
-/
theorem isTorsionFree_quotient_ker [IsDomain R] [Module.IsTorsionFree R M₂] (f : M →ₗ[R] M₂) :
    Module.IsTorsionFree R (M ⧸ LinearMap.ker f) :=
  (saturation_eq_self_iff (N := LinearMap.ker f)).1 (le_antisymm (fun x ⟨r, hr, hx⟩ => by
    rw [LinearMap.mem_ker, map_smul] at hx
    rw [LinearMap.mem_ker]
    exact (smul_eq_zero.1 hx).resolve_left hr) (le_saturation _))

/- English proof (translation)
Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[quot_mk, LinearMap.quotKerEquivRange_apply_mk, hf x]`.
-/
theorem IsEquivariant.quotKerEquivRange (hf : IsEquivariant f Φ Φ₂) (x : M ⧸ LinearMap.ker f) :
    f.quotKerEquivRange (quot Φ _ hf.isStable_ker x) =
      restrict Φ₂ _ hf.isStable_range (f.quotKerEquivRange x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  apply Subtype.ext
  simp [quot_mk, LinearMap.quotKerEquivRange_apply_mk, hf x]

end Equivariant

section Subquot

variable {Φ : M →ₛₗ[φ] M} {N N' : Submodule R M}

abbrev inSub (N N' : Submodule R M) : Submodule R N' := N.comap N'.subtype

/- English proof (translation)
Introduce `_ hx` and use `h _ hx`.
-/
theorem isStable_inSub (h : IsStable Φ N) (h' : IsStable Φ N') :
    IsStable (restrict Φ N' h') (inSub N N') := fun _ hx => h _ hx

def subquot (Φ : M →ₛₗ[φ] M) (N N' : Submodule R M) (h : IsStable Φ N) (h' : IsStable Φ N') :
    (N' ⧸ inSub N N') →ₛₗ[φ] (N' ⧸ inSub N N') :=
  quot (restrict Φ N' h') (inSub N N') (isStable_inSub h h')

/- English proof (translation)
Use `(saturation_eq_self_iff (N := inSub N N')).1 (le_antisymm (fun _ ⟨r, hr, hx⟩ => ?_) (le_saturation _))` and prove the remaining obligations. Establish `hsat` using `saturation_eq_self (N := N)`. Conclude with `hsat ▸ (⟨r, hr, hx⟩ : _ ∈ saturation N)`.
-/
theorem isTorsionFree_subquot [IsDomain R] [Module.IsTorsionFree R (M ⧸ N)] :
    Module.IsTorsionFree R (N' ⧸ inSub N N') := by
  refine (saturation_eq_self_iff (N := inSub N N')).1 (le_antisymm (fun _ ⟨r, hr, hx⟩ => ?_)
    (le_saturation _))
  have hsat := saturation_eq_self (N := N)
  exact hsat ▸ (⟨r, hr, hx⟩ : _ ∈ saturation N)

/- English proof (translation)
Use `finite_of_saturated N'` as an intermediate fact. Use `isTorsionFree_subquot (N := N) (N' := N')` as an intermediate fact. Conclude with `free_quotient_of_isTorsionFree _`.
-/
theorem free_subquot [IsDomain R] [IsBezout R] [Module.Free R M] [Module.Finite R M]
    [Module.IsTorsionFree R (M ⧸ N)] [Module.IsTorsionFree R (M ⧸ N')] :
    Module.Free R (N' ⧸ inSub N N') := by
  have := finite_of_saturated N'
  have := isTorsionFree_subquot (N := N) (N' := N')
  exact free_quotient_of_isTorsionFree _

/- English proof (translation)
Use `finite_of_saturated N'` as an intermediate fact. Use `infer_instance`.
-/
theorem finite_subquot [IsDomain R] [IsBezout R] [Module.Free R M] [Module.Finite R M]
    [Module.IsTorsionFree R (M ⧸ N')] : Module.Finite R (N' ⧸ inSub N N') := by
  have := finite_of_saturated N'
  infer_instance

end Subquot

end PhiModule

end GroundTheory.PAdicHodge
