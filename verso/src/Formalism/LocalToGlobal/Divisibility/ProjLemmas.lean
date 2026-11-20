import Mathlib
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Formalism.LocalToGlobal.Divisibility.ClassSumLemmas
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ClassSumDualGeOfFamily

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues

section Sub

variable {K : Type} [Field K] [StarRing K] {n : ℕ}

/- English proof (translation)
Use extensionality with `i`. Simplify using `only [Matrix.mulVec, dotProduct, subE, Matrix.of_apply, Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`.
-/
theorem subE_mulVec (Z : Submodule K (Fin n → K)) (x : Fin (subDim Z) → K) :
    (subE Z).mulVec x = (((subBasis Z).equivFun.symm x : Z) : Fin n → K) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, subE, Matrix.of_apply, Basis.equivFun_symm_apply,
    Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/- English proof (translation)
Introduce `K _ _ n Z`. Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Rewrite `hxy` using `[subE_mulVec, subE_mulVec]`. Conclude with `(subBasis Z).equivFun.symm.injective (Subtype.ext hxy)`.

Use extensionality with `v`. Simplify using `only [LinearMap.mem_range, Matrix.mulVecLin_apply, subE_mulVec]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`. Conclude with `((subBasis Z).equivFun.symm x).2`.

Introduce `hv`. Conclude with `⟨(subBasis Z).equivFun ⟨v, hv⟩, by simp⟩`.
-/
theorem subspace_image_spec : SubESpec := by
  intro K _ _ n Z
  constructor
  · intro x y hxy
    rw [subE_mulVec, subE_mulVec] at hxy
    exact (subBasis Z).equivFun.symm.injective (Subtype.ext hxy)
  · ext v
    simp only [LinearMap.mem_range, Matrix.mulVecLin_apply, subE_mulVec]
    constructor
    · rintro ⟨x, rfl⟩
      exact ((subBasis Z).equivFun.symm x).2
    · intro hv
      exact ⟨(subBasis Z).equivFun ⟨v, hv⟩, by simp⟩

/- English proof (translation)
Introduce `K _ _ n e`. Conclude with `subspace_image_spec K n (LinearMap.range e.mulVecLin)`.
-/
theorem image_idempotent_spec : ImESpec := by
  intro K _ _ n e
  exact subspace_image_spec K n (LinearMap.range e.mulVecLin)

/- English proof (translation)
Take `⟨b, hbT, hspan, hli⟩` from `exists_linearIndependent K T`. Establish `hZ : Submodule.span K (Set.range ((↑) : b → Fin n → K)) = Z`. Rewrite using `[Subtype.range_coe, hspan, hT]`. Use `⟨((Basis.span hli).map (LinearEquiv.ofEq _ _ hZ)).reindex (((Basis.span hli).map (LinearEquiv.ofEq _ _ hZ)).indexEquiv (Module.finBasis K Z)), fun j i => ?_⟩` and prove the remaining obligations. Rewrite using `[Basis.reindex_apply, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]`.

Conclude with `hrat _ (hbT (Subtype.mem _)) i`.
-/
theorem subHasRat_of_span (Z : Submodule K (Fin n → K)) (T : Set (Fin n → K))
    (hT : Submodule.span K T = Z) (hrat : ∀ v ∈ T, ∀ i, v i ∈ cmMax K) : SubHasRatBasis Z := by
  obtain ⟨b, hbT, hspan, hli⟩ := exists_linearIndependent K T
  have hZ : Submodule.span K (Set.range ((↑) : b → Fin n → K)) = Z := by
    rw [Subtype.range_coe, hspan, hT]
  refine ⟨((Basis.span hli).map (LinearEquiv.ofEq _ _ hZ)).reindex
      (((Basis.span hli).map (LinearEquiv.ofEq _ _ hZ)).indexEquiv (Module.finBasis K Z)), fun j i => ?_⟩
  rw [Basis.reindex_apply, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]
  exact hrat _ (hbT (Subtype.mem _)) i

/- English proof (translation)
Establish `e : subBasis Z = h.choose` using `by first`. Consider the case `exact dif_pos h`. Consider the case `(unfold subBasis; exact dif_pos h)`. Consider the case `(rw [subBasis, dif_pos h])`. Consider the case `(simp only [subBasis, h, dite_true])`.

Consider the case `(unfold subBasis; simp [h])`. Use `show ((subBasis Z j : Fin n → K) i) ∈ cmMax K`. Rewrite using `[e]`. Conclude with `h.choose_spec j i`.
-/
theorem subE_rat (Z : Submodule K (Fin n → K)) (h : SubHasRatBasis Z) (i : Fin n)
    (j : Fin (subDim Z)) : subE Z i j ∈ cmMax K := by
  have e : subBasis Z = h.choose := by
    first
    | exact dif_pos h
    | (unfold subBasis; exact dif_pos h)
    | (rw [subBasis, dif_pos h])
    | (simp only [subBasis, h, dite_true])
    | (unfold subBasis; simp [h])
  show ((subBasis Z j : Fin n → K) i) ∈ cmMax K
  rw [e]
  exact h.choose_spec j i

/- English proof (translation)
Introduce `K _ _ n e he i j`. Apply `subE_rat` to reduce the goal to its premises. Apply `subHasRat_of_span _ (Set.range eᵀ) (Matrix.range_mulVecLin e).symm` to reduce the goal to its premises. Introduce and unpack `v ⟨k, rfl⟩ l`. Conclude with `he l k`.
-/
theorem image_idempotent_rational : ImERat := by
  intro K _ _ n e he i j
  apply subE_rat
  apply subHasRat_of_span _ (Set.range eᵀ) (Matrix.range_mulVecLin e).symm
  rintro v ⟨k, rfl⟩ l
  exact he l k

end Sub

namespace CSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)

/- English proof (translation)
Use `show ((S.basis.equivFun.symm ((S.actMat r t).mulVec x) : S.Forms) : S.Cl → S.V) = _`. Use `congr 1`. Apply `S.basis.equivFun.injective` to reduce the goal to its premises. Rewrite using `[LinearEquiv.apply_symm_apply, Basis.equivFun_apply, ← LinearMap.toMatrix_mulVec_repr S.basis S.basis, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`. Both sides reduce to the same expression.
-/
theorem I_actMat (t : G) (x : Fin S.dim → K) :
    S.I ((S.actMat r t).mulVec x) = (r t (S.basis.equivFun.symm x) : S.Cl → S.V) := by
  show ((S.basis.equivFun.symm ((S.actMat r t).mulVec x) : S.Forms) : S.Cl → S.V) = _
  congr 1
  apply S.basis.equivFun.injective
  rw [LinearEquiv.apply_symm_apply, Basis.equivFun_apply,
    ← LinearMap.toMatrix_mulVec_repr S.basis S.basis, ← Basis.equivFun_apply,
    LinearEquiv.apply_symm_apply]
  rfl

def actHom : G →* Matrix (Fin S.dim) (Fin S.dim) K where
  toFun := S.actMat r
  map_one' := by
    unfold actMat
    rw [map_one]
    exact LinearMap.toMatrix_one _
  map_mul' := by
    intro s t
    unfold actMat
    rw [map_mul]
    exact LinearMap.toMatrix_mul _ _ _

/- English proof (translation)
Rewrite using `[MonoidAlgebra.lift_apply]`. Unfold `CSD.gaMat`. Rewrite using `[Finsupp.sum_fintype]`. Both sides reduce to the same expression. Use `intro`.

Conclude with `zero_smul _ _`.
-/
theorem gaMat_eq_lift (a : MonoidAlgebra K G) :
    S.gaMat r a = MonoidAlgebra.lift K (Matrix (Fin S.dim) (Fin S.dim) K) G (S.actHom r) a := by
  rw [MonoidAlgebra.lift_apply]
  unfold CSD.gaMat
  rw [Finsupp.sum_fintype]
  · rfl
  · intro
    exact zero_smul _ _

end CSD

/- English proof (translation)
Introduce `K _ _ _ S G _ _ r t x`. Conclude with `S.I_actMat r t x`.
-/
theorem action_matrix_spec : ActMatSpec := by
  intro K _ _ _ S G _ _ r t x
  exact S.I_actMat r t x

/- English proof (translation)
Introduce `K _ _ _ S G _ _ r`. Conclude with `⟨by rw [S.gaMat_eq_lift r, map_one], fun a b => by simp only [S.gaMat_eq_lift r, map_mul]⟩`.
-/
theorem group_action_matrix_hom : GaMatHom := by
  intro K _ _ _ S G _ _ r
  exact ⟨by rw [S.gaMat_eq_lift r, map_one], fun a b => by simp only [S.gaMat_eq_lift r, map_mul]⟩

/- English proof (translation)
Use `first`. Consider the case `exact ⟨fun h c => h c (Set.mem_univ c), fun h c _ => h c⟩`. Consider the case `(unfold valLatF; simp [Submodule.mem_pi])`. Consider the case `(simp only [valLatF, Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, forall_const, LinearMap.restrictScalars_apply])`.
-/
theorem mem_valLatF {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} {Cl V : Type}
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (I : (Fin n → K) →ₗ[K] (Cl → V)) (N : Cl → Submodule (𝓞 K) V) (x : Fin n → K) :
    x ∈ valLatF I N ↔ ∀ c, I x c ∈ N c := by
  first
  | exact ⟨fun h c => h c (Set.mem_univ c), fun h c _ => h c⟩
  | (unfold valLatF; simp [Submodule.mem_pi])
  | (simp only [valLatF, Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, forall_const,
      LinearMap.restrictScalars_apply])

/- English proof (translation)
Introduce `K _ _ _ S G _ _ r hr t`. Prove the components needed by the constructor for the conclusion. Introduce `x hx`. Unfold `CSD.nabLat at hx ⊢`. Rewrite `hx`, the goal using `[mem_valLatF]`.

Introduce `c`. Rewrite using `[S.I_actMat r t x]`. Conclude with `hr.nab_stable t (S.basis.equivFun.symm x) hx c`. Introduce `x hx`. Unfold `CSD.delLat at hx ⊢`.

Rewrite `hx`, the goal using `[mem_valLatF]`. Introduce `c`. Rewrite using `[S.I_actMat r t x]`. Conclude with `hr.del_stable t (S.basis.equivFun.symm x) hx c`.
-/
theorem action_preserves_lattice : ActLat := by
  intro K _ _ _ S G _ _ r hr t
  constructor
  · intro x hx
    unfold CSD.nabLat at hx ⊢
    rw [mem_valLatF] at hx ⊢
    intro c
    rw [S.I_actMat r t x]
    exact hr.nab_stable t (S.basis.equivFun.symm x) hx c
  · intro x hx
    unfold CSD.delLat at hx ⊢
    rw [mem_valLatF] at hx ⊢
    intro c
    rw [S.I_actMat r t x]
    exact hr.del_stable t (S.basis.equivFun.symm x) hx c

namespace CSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)

/- English proof (translation)
Establish `hI : ∀ x : Fin S.dim → K, ∀ c, S.I x c = ∑ k, x k • (S.basis k : S.Cl → S.V) c`. Introduce `x c`. Use `show ((S.basis.equivFun.symm x : S.Forms) : S.Cl → S.V) c = _`. Rewrite using `[Basis.equivFun_symm_apply, Submodule.coe_sum, Finset.sum_apply]`. Both sides reduce to the same expression.

Establish `hp : ∀ (x y : Fin S.dim → K) (u w : Fin S.dim → S.V), S.pair (∑ k, x k • u k) (∑ l, y l • w l) = ∑ k, ∑ l, star (x k) * y l * S.pair (u k) (w l)`. Introduce `x y u w`. Simplify using `only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply, RingHom.id_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Unfold `CSD.csum`. Simplify using `only [hI, hp]`. Simplify using `only [dotProduct, Matrix.mulVec, CSD.H, Matrix.of_apply, CSD.csum, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]`. Use `conv_rhs =>`.

Rewrite using `[Finset.sum_comm]`. Use `arg 2`. Use extensionality with `k`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem dot_H_lemma {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
    (x y : Fin S.dim → K) : star x ⬝ᵥ (S.H *ᵥ y) = S.csum (S.I x) (S.I y) := by
  have hI : ∀ x : Fin S.dim → K, ∀ c, S.I x c = ∑ k, x k • (S.basis k : S.Cl → S.V) c := by
    intro x c
    show ((S.basis.equivFun.symm x : S.Forms) : S.Cl → S.V) c = _
    rw [Basis.equivFun_symm_apply, Submodule.coe_sum, Finset.sum_apply]
    rfl
  have hp : ∀ (x y : Fin S.dim → K) (u w : Fin S.dim → S.V),
      S.pair (∑ k, x k • u k) (∑ l, y l • w l) = ∑ k, ∑ l, star (x k) * y l * S.pair (u k) (w l) := by
    intro x y u w
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  unfold CSD.csum
  simp only [hI, hp]
  simp only [dotProduct, Matrix.mulVec, CSD.H, Matrix.of_apply, CSD.csum, Pi.star_apply, Finset.mul_sum,
    Finset.sum_mul]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext k
    rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun c _ => ?_
  ring

/- English proof (translation)
Establish `Q` using `dot_H_lemma S`. Establish `key : ∀ x y : Fin S.dim → K, star x ⬝ᵥ (((S.actMat r t)ᴴ * S.H * S.actMat r t) *ᵥ y) = star x ⬝ᵥ (S.H *ᵥ y)`. Introduce `x y`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, Q, Q, S.I_actMat r t, S.I_actMat r t]`. Conclude with `hr.unitary t _ _`.

Use extensionality with `i j`. Establish `hs : star (Pi.single i 1 : Fin S.dim → K) = Pi.single i 1`. Use extensionality with `k`. Apply the tactic sequence `by_cases hk : k = i <;> simp [hk]`. Use `key (Pi.single i 1) (Pi.single j 1)` as an intermediate fact.

Rewrite `this` using `[hs]`. Simplify `this` using `[dotProduct, Matrix.mulVec, Pi.single_apply]`.
-/
theorem actMat_unitary (hr : S.ActGood r) (t : G) :
    (S.actMat r t)ᴴ * S.H * S.actMat r t = S.H := by
  have Q := dot_H_lemma S
  have key : ∀ x y : Fin S.dim → K,
      star x ⬝ᵥ (((S.actMat r t)ᴴ * S.H * S.actMat r t) *ᵥ y) = star x ⬝ᵥ (S.H *ᵥ y) := by
    intro x y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, Q, Q,
      S.I_actMat r t, S.I_actMat r t]
    exact hr.unitary t _ _
  ext i j
  have hs : star (Pi.single i 1 : Fin S.dim → K) = Pi.single i 1 := by
    ext k
    by_cases hk : k = i <;> simp [hk]
  have := key (Pi.single i 1) (Pi.single j 1)
  rw [hs] at this
  simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using this

/- English proof (translation)
Establish `h` using `(S.actHom r).map_mul t t⁻¹`. Rewrite `h` using `[mul_inv_cancel, map_one]`. Conclude with `h.symm`.
-/
theorem actMat_mul_inv (t : G) : S.actMat r t * S.actMat r t⁻¹ = 1 := by
  have h := (S.actHom r).map_mul t t⁻¹
  rw [mul_inv_cancel, map_one] at h
  exact h.symm

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[S.actMat_mul_inv r t, Matrix.mul_one]`. Use `_ = ((S.actMat r t)ᴴ * S.H * S.actMat r t) * S.actMat r t⁻¹ := (Matrix.mul_assoc _ _ _).symm`. Use `_ = S.H * S.actMat r t⁻¹ := by rw [S.actMat_unitary r hr t]`.
-/
theorem actMat_adj (hr : S.ActGood r) (t : G) :
    (S.actMat r t)ᴴ * S.H = S.H * S.actMat r t⁻¹ := by
  calc (S.actMat r t)ᴴ * S.H = (S.actMat r t)ᴴ * S.H * (S.actMat r t * S.actMat r t⁻¹) := by
        rw [S.actMat_mul_inv r t, Matrix.mul_one]
    _ = ((S.actMat r t)ᴴ * S.H * S.actMat r t) * S.actMat r t⁻¹ := (Matrix.mul_assoc _ _ _).symm
    _ = S.H * S.actMat r t⁻¹ := by rw [S.actMat_unitary r hr t]

end CSD

/- English proof (translation)
Introduce `K _ _ _ S G _ _ r hr a`. Rewrite using `[S.gaMat_eq_lift r (gaStar a)]`. Unfold `gaStar`. Rewrite using `[map_sum]`. Simplify using `only [MonoidAlgebra.lift_single]`.

Unfold `CSD.gaMat`. Rewrite using `[Matrix.conjTranspose_sum, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_smul, Matrix.smul_mul, S.actMat_adj r hr t, Matrix.mul_smul]`. Both sides reduce to the same expression.
-/
theorem group_action_matrix_adjoint : GaMatAdj := by
  intro K _ _ _ S G _ _ r hr a
  rw [S.gaMat_eq_lift r (gaStar a)]
  unfold gaStar
  rw [map_sum]
  simp only [MonoidAlgebra.lift_single]
  unfold CSD.gaMat
  rw [Matrix.conjTranspose_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, S.actMat_adj r hr t, Matrix.mul_smul]
  rfl

namespace CSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
  {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)

open Classical in
/- English proof (translation)
Rewrite using `[S.gaMat_eq_lift r]`. Unfold `lvlIdem`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Rewrite using `[MonoidAlgebra.lift_single]`.

Both sides reduce to the same expression.
-/
theorem gaMat_lvlIdem (P : Subgroup G) (ψ : P →* Kˣ) :
    S.gaMat r (lvlIdem P ψ) =
      ∑ h : P, ((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) • S.actMat r (h : G) := by
  rw [S.gaMat_eq_lift r]
  unfold lvlIdem
  rw [map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [MonoidAlgebra.lift_single]
  rfl

/- English proof (translation)
Unfold `lvlIdem`. Rewrite using `[Finset.mul_sum, Finset.smul_sum]`. Simplify using `only [MonoidAlgebra.single_mul_single, one_mul]`. Use `conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft h)]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Simplify using `only [Equiv.coe_mulLeft, Subgroup.coe_mul]`. Use `first`. Consider the case `rw [MonoidAlgebra.smul_single']`. Consider the case `rw [MonoidAlgebra.smul_single, smul_eq_mul]`. Use `congr 1`.

Rewrite using `[mul_inv_rev, map_mul, Units.val_mul]`. Establish `e : ((ψ h : Kˣ) : K) * ((ψ h⁻¹ : Kˣ) : K) = 1`. Rewrite using `[← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e, mul_one]`.

Use `_ = _ := by ring`.
-/
private theorem single_mul_lvlIdem_lemma {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
    (P : Subgroup G) (ψ : P →* Kˣ) (h : P) :
    MonoidAlgebra.single (h : G) (1 : K) * lvlIdem P ψ = ((ψ h : Kˣ) : K) • lvlIdem P ψ := by
  classical
  unfold lvlIdem
  rw [Finset.mul_sum, Finset.smul_sum]
  simp only [MonoidAlgebra.single_mul_single, one_mul]
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft h)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul]
  first
  | rw [MonoidAlgebra.smul_single']
  | rw [MonoidAlgebra.smul_single, smul_eq_mul]
  congr 1
  rw [mul_inv_rev, map_mul, Units.val_mul]
  have e : ((ψ h : Kˣ) : K) * ((ψ h⁻¹ : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  calc (Nat.card P : K)⁻¹ * ((ψ k⁻¹ : Kˣ) : K)
      = (Nat.card P : K)⁻¹ * ((ψ k⁻¹ : Kˣ) : K) * (((ψ h : Kˣ) : K) * ((ψ h⁻¹ : Kˣ) : K)) := by
        rw [e, mul_one]
    _ = _ := by ring

/- English proof (translation)
Establish `e1 : S.actMat r (k : G) = S.gaMat r (MonoidAlgebra.single (k : G) 1)`. Rewrite using `[S.gaMat_eq_lift r, MonoidAlgebra.lift_single, one_smul]`. Both sides reduce to the same expression. Rewrite using `[e1, ← (group_action_matrix_hom K S G r).2, single_mul_lvlIdem_lemma, S.gaMat_eq_lift r, S.gaMat_eq_lift r, map_smul]`.
-/
theorem actMat_mul_lvlIdem (P : Subgroup G) (ψ : P →* Kˣ) (k : P) :
    S.actMat r (k : G) * S.gaMat r (lvlIdem P ψ) = ((ψ k : Kˣ) : K) • S.gaMat r (lvlIdem P ψ) := by
  have e1 : S.actMat r (k : G) = S.gaMat r (MonoidAlgebra.single (k : G) 1) := by
    rw [S.gaMat_eq_lift r, MonoidAlgebra.lift_single, one_smul]
    rfl
  rw [e1, ← (group_action_matrix_hom K S G r).2, single_mul_lvlIdem_lemma, S.gaMat_eq_lift r, S.gaMat_eq_lift r,
    map_smul]

/- English proof (translation)
Establish `hsum : ∀ (s : Finset P) (M : P → Matrix (Fin S.dim) (Fin S.dim) K), (∑ h ∈ s, M h).mulVec x = ∑ h ∈ s, (M h).mulVec x`. Introduce `s M`. Proceed by induction on `s using Finset.cons_induction with`. Consider the case `empty => simp`. Consider the case `cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, Matrix.add_mulVec, ih]`.

Establish `hsm : ∀ (c : K) (M : Matrix (Fin S.dim) (Fin S.dim) K) (v : Fin S.dim → K), (c • M).mulVec v = c • M.mulVec v`. Introduce `c M v`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`. Establish `hx' : ∀ h : P, (S.actMat r (h : G)).mulVec x = ((ψ h : Kˣ) : K) • x` using `hx`.

Rewrite using `[S.gaMat_lvlIdem r P ψ, hsum]`. Simplify using `only [hsm, hx', smul_smul]`. Rewrite using `[← Finset.sum_smul]`. Establish `e : ∀ h : P, (Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K) * ((ψ h : Kˣ) : K) = (Nat.card P : K)⁻¹` using `fun h => by rw [mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, mul_one]`. Simplify using `only [e, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`.

Rewrite using `[← Nat.card_eq_fintype_card, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_smul]`.
-/
theorem lvlIdem_mulVec_of_mem (P : Subgroup G) (ψ : P →* Kˣ) (x : Fin S.dim → K)
    (hx : x ∈ S.lvlPart r P ψ) : (S.gaMat r (lvlIdem P ψ)).mulVec x = x := by
  classical
  have hsum : ∀ (s : Finset P) (M : P → Matrix (Fin S.dim) (Fin S.dim) K),
      (∑ h ∈ s, M h).mulVec x = ∑ h ∈ s, (M h).mulVec x := by
    intro s M
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, Matrix.add_mulVec, ih]
  have hsm : ∀ (c : K) (M : Matrix (Fin S.dim) (Fin S.dim) K) (v : Fin S.dim → K),
      (c • M).mulVec v = c • M.mulVec v := by
    intro c M v
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  have hx' : ∀ h : P, (S.actMat r (h : G)).mulVec x = ((ψ h : Kˣ) : K) • x := hx
  rw [S.gaMat_lvlIdem r P ψ, hsum]
  simp only [hsm, hx', smul_smul]
  rw [← Finset.sum_smul]
  have e : ∀ h : P, (Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K) * ((ψ h : Kˣ) : K) = (Nat.card P : K)⁻¹ :=
    fun h => by rw [mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, mul_one]
  simp only [e, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_smul]

end CSD

/- English proof (translation)
Introduce `K _ _ _ S G _ _ r P ψ`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩ show ∀ h : P, (S.actMat r (h : G)).mulVec ((S.gaMat r (lvlIdem P ψ)).mulVecLin y) = ((ψ h : Kˣ) : K) • (S.gaMat r (lvlIdem P ψ)).mulVecLin y`. Introduce `h`.

Establish `hsm : ∀ (c : K) (M : Matrix (Fin S.dim) (Fin S.dim) K) (v : Fin S.dim → K), (c • M).mulVec v = c • M.mulVec v`. Introduce `c M v`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`. Rewrite using `[Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, S.actMat_mul_lvlIdem r P ψ h, hsm]`.

Introduce `hx`. Conclude with `LinearMap.mem_range.mpr ⟨x, by`. Rewrite using `[Matrix.mulVecLin_apply]`. Conclude with `S.lvlIdem_mulVec_of_mem r P ψ x hx⟩`.
-/
theorem level_part_spec : LvlPartSpec := by
  intro K _ _ _ S G _ _ r P ψ
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    show ∀ h : P, (S.actMat r (h : G)).mulVec ((S.gaMat r (lvlIdem P ψ)).mulVecLin y) =
      ((ψ h : Kˣ) : K) • (S.gaMat r (lvlIdem P ψ)).mulVecLin y
    intro h
    have hsm : ∀ (c : K) (M : Matrix (Fin S.dim) (Fin S.dim) K) (v : Fin S.dim → K),
        (c • M).mulVec v = c • M.mulVec v := by
      intro c M v
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, S.actMat_mul_lvlIdem r P ψ h, hsm]
  · intro hx
    exact LinearMap.mem_range.mpr ⟨x, by
      rw [Matrix.mulVecLin_apply]
      exact S.lvlIdem_mulVec_of_mem r P ψ x hx⟩

section Basic

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

/- English proof (translation)
Proceed by induction on `s using Finset.cons_induction with`. Consider the case `empty => simp`. Consider the case `cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, MonoidAlgebra.coeff_add, Finsupp.add_apply, ih]`.
-/
private theorem coeff_sum_lemma {K G ι : Type} [Field K] (s : Finset ι) (f : ι → MonoidAlgebra K G)
    (u : G) : (∑ i ∈ s, f i).coeff u = ∑ i ∈ s, (f i).coeff u := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, MonoidAlgebra.coeff_add, Finsupp.add_apply, ih]

/- English proof (translation)
Use extensionality with `u`. Rewrite using `[coeff_sum_lemma, Finset.sum_eq_single u]`. Rewrite using `[MonoidAlgebra.coeff_single, Finsupp.single_eq_same]`. Introduce `t _ ht`. Rewrite using `[MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg ht]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ u) h`.
-/
private theorem eq_sum_single_lemma {K G : Type} [Field K] [Fintype G] (a : MonoidAlgebra K G) :
    a = ∑ t : G, MonoidAlgebra.single t (a.coeff t) := by
  classical
  ext u
  rw [coeff_sum_lemma, Finset.sum_eq_single u]
  · rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  · intro t _ ht
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg ht]
  · intro h
    exact absurd (Finset.mem_univ u) h

/- English proof (translation)
Use `conv_lhs => rw [eq_sum_single_lemma a, eq_sum_single_lemma b]`. Rewrite using `[Finset.sum_mul]`. Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[coeff_sum_lemma]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[coeff_sum_lemma, Finset.sum_eq_single (s⁻¹ * u)]`. Rewrite using `[MonoidAlgebra.single_mul_single, mul_inv_cancel_left, MonoidAlgebra.coeff_single, Finsupp.single_eq_same]`. Introduce `t _ ht`. Rewrite using `[MonoidAlgebra.single_mul_single, MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg]`. Introduce `h`.

Apply `ht` to reduce the goal to its premises. Rewrite using `[← h, inv_mul_cancel_left]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem coeff_mul_fin (a b : MonoidAlgebra K G) (u : G) :
    (a * b).coeff u = ∑ s : G, a.coeff s * b.coeff (s⁻¹ * u) := by
  classical
  conv_lhs => rw [eq_sum_single_lemma a, eq_sum_single_lemma b]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [coeff_sum_lemma]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_sum_lemma, Finset.sum_eq_single (s⁻¹ * u)]
  · rw [MonoidAlgebra.single_mul_single, mul_inv_cancel_left, MonoidAlgebra.coeff_single,
      Finsupp.single_eq_same]
  · intro t _ ht
    rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg]
    intro h
    apply ht
    rw [← h, inv_mul_cancel_left]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Conclude with `eq_sum_single_lemma a`.
-/
theorem eq_sum_single (a : MonoidAlgebra K G) : a = ∑ t : G, MonoidAlgebra.single t (a.coeff t) := by
  exact eq_sum_single_lemma a

/- English proof (translation)
Unfold `gaStar`. Simplify using `only [MonoidAlgebra.coeff_add, Finsupp.add_apply, star_add, MonoidAlgebra.single_add, Finset.sum_add_distrib]`.
-/
theorem gaStar_add [StarRing K] (a b : MonoidAlgebra K G) : gaStar (a + b) = gaStar a + gaStar b := by
  unfold gaStar
  simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, star_add, MonoidAlgebra.single_add,
    Finset.sum_add_distrib]

/- English proof (translation)
Unfold `gaStar`. Simplify using the standard rewrite rules.
-/
theorem gaStar_zero [StarRing K] : gaStar (0 : MonoidAlgebra K G) = 0 := by
  unfold gaStar
  simp

/- English proof (translation)
Unfold `gaStar`. Rewrite using `[Finset.sum_eq_single t]`. Rewrite using `[MonoidAlgebra.coeff_single, Finsupp.single_eq_same]`. Introduce `u _ hu`. Rewrite using `[MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (Ne.symm hu), star_zero, MonoidAlgebra.single_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ t) h`.
-/
theorem gaStar_single [StarRing K] (t : G) (x : K) :
    gaStar (MonoidAlgebra.single t x) = MonoidAlgebra.single t⁻¹ (star x) := by
  classical
  unfold gaStar
  rw [Finset.sum_eq_single t]
  · rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  · intro u _ hu
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (Ne.symm hu), star_zero,
      MonoidAlgebra.single_zero]
  · intro h
    exact absurd (Finset.mem_univ t) h

/- English proof (translation)
Proceed by induction on `s using Finset.cons_induction with`. Consider the case `empty => rw [Finset.sum_empty, Finset.sum_empty]`. Conclude with `gaStar_zero`. Consider the case `cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, gaStar_add, ih]`.
-/
theorem gaStar_sum [StarRing K] {ι : Type} (s : Finset ι) (f : ι → MonoidAlgebra K G) :
    gaStar (∑ i ∈ s, f i) = ∑ i ∈ s, gaStar (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact gaStar_zero
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, gaStar_add, ih]

/- English proof (translation)
Use `conv_lhs => rw [eq_sum_single a, eq_sum_single b]`. Rewrite using `[Finset.sum_mul]`. Repeatedly rewrite using `[Finset.mul_sum, gaStar_sum, MonoidAlgebra.single_mul_single, gaStar_single, mul_inv_rev, star_mul']`. Use `conv_rhs =>`. Unfold `gaStar`.

Rewrite using `[Finset.sum_mul]`. Simplify using `only [Finset.mul_sum, MonoidAlgebra.single_mul_single]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm (star (a.coeff s))]`.
-/
theorem gaStar_mul [StarRing K] (a b : MonoidAlgebra K G) : gaStar (a * b) = gaStar b * gaStar a := by
  classical
  conv_lhs => rw [eq_sum_single a, eq_sum_single b]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, gaStar_sum, MonoidAlgebra.single_mul_single, gaStar_single, mul_inv_rev,
    star_mul']
  conv_rhs =>
    unfold gaStar
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, MonoidAlgebra.single_mul_single]
    rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [mul_comm (star (a.coeff s))]

end Basic

/- English proof (translation)
Introduce `K _ G _ _ ψ`. Unfold `lvlIdem`. Establish `hb : ∀ (inst : Fintype (⊥ : Subgroup G)) (F : (⊥ : Subgroup G) → MonoidAlgebra K G), @Finset.sum _ _ _ (@Finset.univ _ inst) F = F 1` using `fun inst F => by`. Use `Fintype.sum_subsingleton F 1` and compare the differences between its conclusion and the goal. Rewrite using `[hb]`.

Simplify using `[MonoidAlgebra.one_def]`.
-/
theorem level_idempotent_bot : LvlIdemBot := by
  intro K _ G _ _ ψ
  unfold lvlIdem
  have hb : ∀ (inst : Fintype (⊥ : Subgroup G)) (F : (⊥ : Subgroup G) → MonoidAlgebra K G),
      @Finset.sum _ _ _ (@Finset.univ _ inst) F = F 1 := fun inst F => by
    convert Fintype.sum_subsingleton F 1
  rw [hb]
  simp [MonoidAlgebra.one_def]

section Lvl

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

/- English proof (translation)
Conclude with `CSD.single_mul_lvlIdem_lemma P ψ h`.
-/
theorem single_mul_lvlIdem (P : Subgroup G) (ψ : P →* Kˣ) (h : P) :
    MonoidAlgebra.single (h : G) (1 : K) * lvlIdem P ψ = ((ψ h : Kˣ) : K) • lvlIdem P ψ := by
  exact CSD.single_mul_lvlIdem_lemma P ψ h

/- English proof (translation)
Use `conv_lhs => arg 1`. Unfold `lvlIdem`. Rewrite using `[Finset.sum_mul]`. Establish `e : ∀ h : P, MonoidAlgebra.single (h : G) ((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) * lvlIdem P ψ = (Nat.card P : K)⁻¹ • lvlIdem P ψ`. Introduce `h`.

Establish `hs : MonoidAlgebra.single (h : G) ((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) = ((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) • MonoidAlgebra.single (h : G) (1 : K)` using `by first`. Consider the case `rw [MonoidAlgebra.smul_single', mul_one]`. Consider the case `rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]`. Rewrite using `[hs, smul_mul_assoc, single_mul_lvlIdem, smul_smul, mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, mul_one]`. Rewrite using `[Finset.sum_congr rfl fun h _ => e h, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul K, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_smul]`.
-/
theorem lvlIdem_idem [CharZero K] (P : Subgroup G) (ψ : P →* Kˣ) :
    lvlIdem P ψ * lvlIdem P ψ = lvlIdem P ψ := by
  classical
  conv_lhs => arg 1; unfold lvlIdem
  rw [Finset.sum_mul]
  have e : ∀ h : P, MonoidAlgebra.single (h : G) ((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) * lvlIdem P ψ =
      (Nat.card P : K)⁻¹ • lvlIdem P ψ := by
    intro h
    have hs : MonoidAlgebra.single (h : G) ((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) =
        ((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) • MonoidAlgebra.single (h : G) (1 : K) := by
      first
      | rw [MonoidAlgebra.smul_single', mul_one]
      | rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [hs, smul_mul_assoc, single_mul_lvlIdem, smul_smul, mul_assoc, ← Units.val_mul, ← map_mul,
      inv_mul_cancel, map_one, Units.val_one, mul_one]
  rw [Finset.sum_congr rfl fun h _ => e h, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.cast_smul_eq_nsmul K, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_smul]

/- English proof (translation)
Unfold `lvlIdem`. Rewrite using `[coeff_sum_lemma]`. Distinguish the cases in `ht : t ∈ P`. Use `left`. Use `⟨⟨t, ht⟩, rfl, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.sum_eq_single ⟨t, ht⟩]`. Rewrite using `[MonoidAlgebra.coeff_single, Finsupp.single_eq_same]`. Introduce `k _ hk`. Rewrite using `[MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg]`. Introduce `h`.

Conclude with `hk (Subtype.ext h)`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Use `right`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg]`. Introduce `h`. Conclude with `ht (h ▸ k.2)`.
-/
theorem coeff_lvlIdem (P : Subgroup G) (ψ : P →* Kˣ) (t : G) :
    (∃ h : P, (h : G) = t ∧ (lvlIdem P ψ).coeff t = (Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) ∨
      (lvlIdem P ψ).coeff t = 0 := by
  classical
  unfold lvlIdem
  rw [coeff_sum_lemma]
  by_cases ht : t ∈ P
  · left
    refine ⟨⟨t, ht⟩, rfl, ?_⟩
    rw [Finset.sum_eq_single ⟨t, ht⟩]
    · rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_same]
    · intro k _ hk
      rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg]
      intro h
      exact hk (Subtype.ext h)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · right
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg]
    intro h
    exact ht (h ▸ k.2)

end Lvl

section Roots

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Establish `hnorm : ‖z‖ = 1` using `by first`. Consider the case `exact norm_eq_one_of_pow_eq_one h hn`. Consider the case `exact Complex.norm_eq_one_of_pow_eq_one h hn`. Establish `hz : starRingEnd ℂ z * z = 1` using `by first`. Consider the case `(rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; simp)`.

Consider the case `(rw [mul_comm, Complex.mul_conj, hnorm]; simp)`. Consider the case `(rw [Complex.conj_mul', hnorm]; simp)`. Conclude with `eq_inv_of_mul_eq_one_left hz`.
-/
private theorem conj_eq_inv_lemma {z : ℂ} {n : ℕ} (hn : n ≠ 0) (h : z ^ n = 1) :
    starRingEnd ℂ z = z⁻¹ := by
  have hnorm : ‖z‖ = 1 := by
    first
    | exact norm_eq_one_of_pow_eq_one h hn
    | exact Complex.norm_eq_one_of_pow_eq_one h hn
  have hz : starRingEnd ℂ z * z = 1 := by
    first
    | (rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; simp)
    | (rw [mul_comm, Complex.mul_conj, hnorm]; simp)
    | (rw [Complex.conj_mul', hnorm]; simp)
  exact eq_inv_of_mul_eq_one_left hz

/- English proof (translation)
Apply `v0.embedding.injective` to reduce the goal to its premises. Rewrite using `[hv u, map_inv₀]`. Conclude with `conj_eq_inv_lemma hn (by rw [← map_pow, hu, map_one])`.
-/
theorem star_of_pow_eq_one {v0 : InfinitePlace K} (hv : IsConjAt v0) {u : K} {n : ℕ} (hn : n ≠ 0)
    (hu : u ^ n = 1) : star u = u⁻¹ := by
  apply v0.embedding.injective
  rw [hv u, map_inv₀]
  exact conj_eq_inv_lemma hn (by rw [← map_pow, hu, map_one])

/- English proof (translation)
Use `show ∀ σ : K →+* ℂ, σ (star u) = starRingEnd ℂ (σ u)`. Introduce `σ`. Rewrite using `[star_of_pow_eq_one hv hn hu, map_inv₀]`. Conclude with `(conj_eq_inv_lemma hn (by rw [← map_pow, hu, map_one])).symm`.
-/
theorem mem_cmMax_of_pow_eq_one {v0 : InfinitePlace K} (hv : IsConjAt v0) {u : K} {n : ℕ} (hn : n ≠ 0)
    (hu : u ^ n = 1) : u ∈ cmMax K := by
  show ∀ σ : K →+* ℂ, σ (star u) = starRingEnd ℂ (σ u)
  intro σ
  rw [star_of_pow_eq_one hv hn hu, map_inv₀]
  exact (conj_eq_inv_lemma hn (by rw [← map_pow, hu, map_one])).symm

/- English proof (translation)
Establish `hint : IsIntegral ℤ u` using `⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [hu]⟩`. Use `first`. Consider the case `exact ⟨⟨u, hint⟩, rfl⟩`. Consider the case `exact ⟨⟨u, (mem_integralClosure_iff ℤ K).mpr hint⟩, rfl⟩`. Consider the case `exact ⟨NumberField.RingOfIntegers.mk u hint, rfl⟩`.
-/
theorem exists_int_of_pow_eq_one {u : K} {n : ℕ} (hn : n ≠ 0) (hu : u ^ n = 1) :
    ∃ b : 𝓞 K, (b : K) = u := by
  have hint : IsIntegral ℤ u :=
    ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [hu]⟩
  first
  | exact ⟨⟨u, hint⟩, rfl⟩
  | exact ⟨⟨u, (mem_integralClosure_iff ℤ K).mpr hint⟩, rfl⟩
  | exact ⟨NumberField.RingOfIntegers.mk u hint, rfl⟩

variable {G : Type} [Group G] [Fintype G]

/- English proof (translation)
Establish `h1 : h ^ Nat.card P = 1` using `by first`. Consider the case `exact pow_card_eq_one'`. Consider the case `exact pow_natCard_eq_one`. Consider the case `simp`. Establish `h2 : (ψ h) ^ Nat.card P = 1` using `by rw [← map_pow, h1, map_one]`.

Rewrite using `[← Units.val_pow_eq_pow_val, h2, Units.val_one]`.
-/
theorem psi_pow (P : Subgroup G) (ψ : P →* Kˣ) (h : P) : ((ψ h : Kˣ) : K) ^ Nat.card P = 1 := by
  have h1 : h ^ Nat.card P = 1 := by
    first
    | exact pow_card_eq_one'
    | exact pow_natCard_eq_one
    | simp
  have h2 : (ψ h) ^ Nat.card P = 1 := by rw [← map_pow, h1, map_one]
  rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]

end Roots

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, rfl⟩ first`. Consider the case `exact NumberField.RingOfIntegers.isIntegral_coe b`. Consider the case `exact b.2`. Consider the case `exact (mem_integralClosure_iff ℤ K).mp b.2`.

Introduce `h first`. Consider the case `exact ⟨⟨x, h⟩, rfl⟩`. Consider the case `exact ⟨⟨x, (mem_integralClosure_iff ℤ K).mpr h⟩, rfl⟩`.
-/
private theorem int_iff_lemma {K : Type} [Field K] [NumberField K] (x : K) :
    (∃ b : 𝓞 K, (b : K) = x) ↔ IsIntegral ℤ x := by
  constructor
  · rintro ⟨b, rfl⟩
    first
    | exact NumberField.RingOfIntegers.isIntegral_coe b
    | exact b.2
    | exact (mem_integralClosure_iff ℤ K).mp b.2
  · intro h
    first
    | exact ⟨⟨x, h⟩, rfl⟩
    | exact ⟨⟨x, (mem_integralClosure_iff ℤ K).mpr h⟩, rfl⟩

/- English proof (translation)
Introduce `K _ _ _ v0 hv G _ _ P ψ`. Establish `hcm : ∀ h : P, ((ψ h : Kˣ) : K) ∈ cmMax K` using `fun h => mem_cmMax_of_pow_eq_one hv Nat.card_pos.ne' (psi_pow P ψ h)`. Use `⟨⟨lvlIdem_idem P ψ, ?_, ?_, ?_⟩, single_mul_lvlIdem P ψ⟩` and prove the remaining obligations. Unfold `lvlIdem`. Rewrite using `[gaStar_sum]`.

Simplify using `only [gaStar_single]`. Rewrite using `[← Equiv.sum_comp (Equiv.inv P)]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [Equiv.inv_apply, Subgroup.coe_inv, inv_inv]`. Use `congr 1`.

Rewrite using `[star_mul', star_inv₀, star_natCast, star_of_pow_eq_one hv Nat.card_pos.ne' (psi_pow P ψ k), map_inv, Units.val_inv_eq_inv_val]`. Introduce `t`. Break down `coeff_lvlIdem P ψ t with ⟨h, _, ht⟩ | ht` into its components or cases. Rewrite using `[ht]`. Conclude with `mul_mem (inv_mem (natCast_mem _ _)) (hcm h⁻¹)`.

Rewrite using `[ht]`. Conclude with `zero_mem _`. Introduce `t`. Break down `coeff_lvlIdem P ψ t with ⟨h, _, ht⟩ | ht` into its components or cases. Rewrite using `[ht, ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul]`.

Conclude with `exists_int_of_pow_eq_one Nat.card_pos.ne' (psi_pow P ψ h⁻¹)`. Conclude with `⟨0, by simp [ht]⟩`.
-/
theorem level_idempotent_spec : LvlIdemSpec := by
  intro K _ _ _ v0 hv G _ _ P ψ
  classical
  have hcm : ∀ h : P, ((ψ h : Kˣ) : K) ∈ cmMax K :=
    fun h => mem_cmMax_of_pow_eq_one hv Nat.card_pos.ne' (psi_pow P ψ h)
  refine ⟨⟨lvlIdem_idem P ψ, ?_, ?_, ?_⟩, single_mul_lvlIdem P ψ⟩
  · unfold lvlIdem
    rw [gaStar_sum]
    simp only [gaStar_single]
    rw [← Equiv.sum_comp (Equiv.inv P)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Equiv.inv_apply, Subgroup.coe_inv, inv_inv]
    congr 1
    rw [star_mul', star_inv₀, star_natCast, star_of_pow_eq_one hv Nat.card_pos.ne' (psi_pow P ψ k),
      map_inv, Units.val_inv_eq_inv_val]
  · intro t
    rcases coeff_lvlIdem P ψ t with ⟨h, _, ht⟩ | ht
    · rw [ht]
      exact mul_mem (inv_mem (natCast_mem _ _)) (hcm h⁻¹)
    · rw [ht]
      exact zero_mem _
  · intro t
    rcases coeff_lvlIdem P ψ t with ⟨h, _, ht⟩ | ht
    · rw [ht, ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul]
      exact exists_int_of_pow_eq_one Nat.card_pos.ne' (psi_pow P ψ h⁻¹)
    · exact ⟨0, by simp [ht]⟩

/- English proof (translation)
Introduce `K _ _ _ v0 hv G _ _ X hX P ψ`. Take `⟨⟨eI, eS, eR, eZ⟩, eC⟩` from `h1 K v0 hv G X hX`. Take `⟨⟨lI, lS, lR, lZ⟩, _⟩` from `h2 K v0 hv G P ψ`. Unfold `goodAt`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[gaStar_mul, eS, lS]`. Conclude with `eC _`. Introduce `t`. Rewrite using `[coeff_mul_fin]`.

Conclude with `sum_mem fun s _ => mul_mem (eR s) (lR _)`. Introduce `t`. Rewrite using `[int_iff_lemma, coeff_mul_fin, Finset.mul_sum]`. Establish `key : ∀ s : G, IsIntegral ℤ (((Fintype.card G * Nat.card P : ℕ) : K) * ((idemOf X).coeff s * (lvlIdem P ψ).coeff (s⁻¹ * t)))`. Introduce `s`.

Establish `e1` using `(int_iff_lemma _).mp (eZ s)`. Establish `e2` using `(int_iff_lemma _).mp (lZ (s⁻¹ * t))`. Establish `e3 : ((Fintype.card G * Nat.card P : ℕ) : K) * ((idemOf X).coeff s * (lvlIdem P ψ).coeff (s⁻¹ * t)) = ((Fintype.card G : K) * (idemOf X).coeff s) * ((Nat.card P : K) * (lvlIdem P ψ).coeff (s⁻¹ * t))`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e3]`. Conclude with `e1.mul e2`. Use `first`. Consider the case `exact IsIntegral.sum _ fun s _ => key s`. Consider the case `exact IsIntegral.sum fun s _ => key s`.

Consider the case `exact (integralClosure ℤ K).sum_mem fun s _ => key s`.
-/
theorem goodAtSpec_of (h1 : IdemOfSpec) (h2 : LvlIdemSpec) : GoodAtSpec := by
  intro K _ _ _ v0 hv G _ _ X hX P ψ
  obtain ⟨⟨eI, eS, eR, eZ⟩, eC⟩ := h1 K v0 hv G X hX
  obtain ⟨⟨lI, lS, lR, lZ⟩, _⟩ := h2 K v0 hv G P ψ
  unfold goodAt
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc idemOf X * lvlIdem P ψ * (idemOf X * lvlIdem P ψ)
        = idemOf X * (lvlIdem P ψ * idemOf X) * lvlIdem P ψ := by simp only [mul_assoc]
      _ = idemOf X * (idemOf X * lvlIdem P ψ) * lvlIdem P ψ := by rw [eC (lvlIdem P ψ)]
      _ = idemOf X * lvlIdem P ψ := by rw [← mul_assoc, eI, mul_assoc, lI]
  · rw [gaStar_mul, eS, lS]
    exact eC _
  · intro t
    rw [coeff_mul_fin]
    exact sum_mem fun s _ => mul_mem (eR s) (lR _)
  · intro t
    rw [int_iff_lemma, coeff_mul_fin, Finset.mul_sum]
    have key : ∀ s : G, IsIntegral ℤ (((Fintype.card G * Nat.card P : ℕ) : K) *
        ((idemOf X).coeff s * (lvlIdem P ψ).coeff (s⁻¹ * t))) := by
      intro s
      have e1 := (int_iff_lemma _).mp (eZ s)
      have e2 := (int_iff_lemma _).mp (lZ (s⁻¹ * t))
      have e3 : ((Fintype.card G * Nat.card P : ℕ) : K) * ((idemOf X).coeff s * (lvlIdem P ψ).coeff (s⁻¹ * t)) =
          ((Fintype.card G : K) * (idemOf X).coeff s) * ((Nat.card P : K) * (lvlIdem P ψ).coeff (s⁻¹ * t)) := by
        push_cast
        ring
      rw [e3]
      exact e1.mul e2
    first
    | exact IsIntegral.sum _ fun s _ => key s
    | exact IsIntegral.sum fun s _ => key s
    | exact (integralClosure ℤ K).sum_mem fun s _ => key s

section Chars

/- English proof (translation)
Rewrite using `[Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]`. Use `IsIntegral.multiset_sum fun μ hμ => ?_` and prove the remaining obligations. Establish `hroot : f.charpoly.IsRoot μ` using `(Polynomial.mem_roots'.mp hμ).2`. Take `⟨v, hv⟩` from `((Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mpr hroot).exists_hasEigenvector`. Establish `h1` using `hv.pow_apply N`.

Rewrite `h1` using `[hf, Module.End.one_apply]`. Establish `h2 : (μ ^ N - 1) • v = 0` using `by rw [sub_smul, one_smul, ← h1, sub_self]`. Establish `h3 : μ ^ N = 1`. Break down `smul_eq_zero.mp h2 with h | h` into its components or cases. Conclude with `sub_eq_zero.mp h`.

Conclude with `absurd h hv.2`. Conclude with `IsIntegral.of_pow (Nat.pos_of_ne_zero hN) (by rw [h3]; exact isIntegral_one)`.
-/
theorem trace_isIntegral_of_pow_eq_one {k V : Type} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (f : Module.End k V) {N : ℕ} (hN : N ≠ 0) (hf : f ^ N = 1) :
    IsIntegral ℤ (LinearMap.trace k V f) := by
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  refine IsIntegral.multiset_sum fun μ hμ => ?_
  have hroot : f.charpoly.IsRoot μ := (Polynomial.mem_roots'.mp hμ).2
  obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mpr hroot).exists_hasEigenvector
  have h1 := hv.pow_apply N
  rw [hf, Module.End.one_apply] at h1
  have h2 : (μ ^ N - 1) • v = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
  have h3 : μ ^ N = 1 := by
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv.2
  exact IsIntegral.of_pow (Nat.pos_of_ne_zero hN) (by rw [h3]; exact isIntegral_one)

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

/- English proof (translation)
Take `⟨n, ρ, -, hχ⟩` from `h`. Apply `(algebraMap K (AlgebraicClosure K)).injective` to reduce the goal to its premises. Rewrite using `[← hχ, ← hχ]`. Use `show LinearMap.trace _ _ (ρ (s * t * s⁻¹)) = LinearMap.trace _ _ (ρ t)`. Rewrite using `[map_mul ρ, map_mul ρ, LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul ρ, ← map_mul ρ, inv_mul_cancel, one_mul]`.
-/
theorem IsAbsIrrChar.conj {χ : G → K} (h : IsAbsIrrChar χ) (s t : G) : χ (s * t * s⁻¹) = χ t := by
  obtain ⟨n, ρ, -, hχ⟩ := h
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [← hχ, ← hχ]
  show LinearMap.trace _ _ (ρ (s * t * s⁻¹)) = LinearMap.trace _ _ (ρ t)
  rw [map_mul ρ, map_mul ρ, LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul ρ, ← map_mul ρ, inv_mul_cancel,
    one_mul]

/- English proof (translation)
Take `⟨n, ρ, -, hχ⟩` from `h`. Establish `hpow : (ρ t) ^ Fintype.card G = 1` using `by rw [← map_pow, pow_card_eq_one, map_one]`. Establish `h1` using `trace_isIntegral_of_pow_eq_one (ρ t) Fintype.card_ne_zero hpow`. Establish `h2 : IsIntegral ℤ (algebraMap K (AlgebraicClosure K) (χ t))`. Rewrite using `[← hχ t]`.

Conclude with `h1`. Conclude with `(isIntegral_algebraMap_iff (algebraMap K (AlgebraicClosure K)).injective).mp h2`.
-/
theorem IsAbsIrrChar.isIntegral {χ : G → K} (h : IsAbsIrrChar χ) (t : G) : IsIntegral ℤ (χ t) := by
  obtain ⟨n, ρ, -, hχ⟩ := h
  have hpow : (ρ t) ^ Fintype.card G = 1 := by rw [← map_pow, pow_card_eq_one, map_one]
  have h1 := trace_isIntegral_of_pow_eq_one (ρ t) Fintype.card_ne_zero hpow
  have h2 : IsIntegral ℤ (algebraMap K (AlgebraicClosure K) (χ t)) := by
    rw [← hχ t]
    exact h1
  exact (isIntegral_algebraMap_iff (algebraMap K (AlgebraicClosure K)).injective).mp h2

/- English proof (translation)
Unfold `chiIdem`. Rewrite using `[coeff_sum_lemma, Finset.sum_eq_single t]`. Rewrite using `[MonoidAlgebra.coeff_single, Finsupp.single_eq_same]`. Introduce `u _ hu`. Rewrite using `[MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg hu]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
private theorem coeff_chiIdem_lemma {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (χ : G → K) (t : G) :
    (chiIdem χ).coeff t = χ 1 / (Fintype.card G : K) * χ t⁻¹ := by
  classical
  unfold chiIdem
  rw [coeff_sum_lemma, Finset.sum_eq_single t]
  · rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  · intro u _ hu
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg hu]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Use extensionality with `u`. Rewrite using `[coeff_mul_fin, coeff_mul_fin, Finset.sum_eq_single s, Finset.sum_eq_single (u * s⁻¹)]`. Rewrite using `[MonoidAlgebra.coeff_single, Finsupp.single_eq_same, show (u * s⁻¹)⁻¹ * u = s by group, Finsupp.single_eq_same, coeff_chiIdem_lemma, coeff_chiIdem_lemma, show (s⁻¹ * u)⁻¹ = u⁻¹ * s by group, show (u * s⁻¹)⁻¹ = s * u⁻¹ by group]`. Establish `hc : χ (u⁻¹ * s) = χ (s * u⁻¹)`. Rewrite using `[← h s (u⁻¹ * s)]`.

Use `congr 1`. Use `group`. Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree. Introduce `v _ hv`.

Rewrite using `[MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg, mul_zero]`. Introduce `e`. Apply `hv` to reduce the goal to its premises. Rewrite using `[e]`. Use `group`.

Introduce `hn`. Conclude with `absurd (Finset.mem_univ _) hn`. Introduce `v _ hv`. Rewrite using `[MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (Ne.symm hv), zero_mul]`. Introduce `hn`.

Conclude with `absurd (Finset.mem_univ _) hn`.
-/
theorem chiIdem_comm_single {χ : G → K} (h : ∀ s t : G, χ (s * t * s⁻¹) = χ t) (s : G) (x : K) :
    MonoidAlgebra.single s x * chiIdem χ = chiIdem χ * MonoidAlgebra.single s x := by
  classical
  ext u
  rw [coeff_mul_fin, coeff_mul_fin, Finset.sum_eq_single s, Finset.sum_eq_single (u * s⁻¹)]
  · rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_same, show (u * s⁻¹)⁻¹ * u = s by group,
      Finsupp.single_eq_same, coeff_chiIdem_lemma, coeff_chiIdem_lemma, show (s⁻¹ * u)⁻¹ = u⁻¹ * s by group,
      show (u * s⁻¹)⁻¹ = s * u⁻¹ by group]
    have hc : χ (u⁻¹ * s) = χ (s * u⁻¹) := by
      rw [← h s (u⁻¹ * s)]
      congr 1
      group
    rw [hc]
    ring
  · intro v _ hv
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg, mul_zero]
    intro e
    apply hv
    rw [e]
    group
  · intro hn
    exact absurd (Finset.mem_univ _) hn
  · intro v _ hv
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (Ne.symm hv), zero_mul]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

/- English proof (translation)
Rewrite using `[eq_sum_single b, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Unfold `idemOf`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun χ hχ => chiIdem_comm_single (hX χ hχ).conj s _`.
-/
theorem idemOf_central (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (b : MonoidAlgebra K G) :
    b * idemOf X = idemOf X * b := by
  rw [eq_sum_single b, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold idemOf
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun χ hχ => chiIdem_comm_single (hX χ hχ).conj s _

/- English proof (translation)
Conclude with `coeff_chiIdem_lemma χ t`.
-/
theorem coeff_chiIdem (χ : G → K) (t : G) :
    (chiIdem χ).coeff t = χ 1 / (Fintype.card G : K) * χ t⁻¹ := by
  exact coeff_chiIdem_lemma χ t

/- English proof (translation)
Unfold `idemOf`. Rewrite using `[coeff_sum_lemma]`. Conclude with `Finset.sum_congr rfl fun χ _ => coeff_chiIdem χ t`.
-/
theorem coeff_idemOf (X : Finset (G → K)) (t : G) :
    (idemOf X).coeff t = ∑ χ ∈ X, χ 1 / (Fintype.card G : K) * χ t⁻¹ := by
  unfold idemOf
  rw [coeff_sum_lemma]
  exact Finset.sum_congr rfl fun χ _ => coeff_chiIdem χ t

/- English proof (translation)
Establish `hn : (Fintype.card G : K) ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`. Rewrite using `[int_iff_lemma, coeff_idemOf, Finset.mul_sum]`. Establish `key : ∀ χ ∈ X, IsIntegral ℤ ((Fintype.card G : K) * (χ 1 / (Fintype.card G : K) * χ t⁻¹))`. Introduce `χ hχ`. Establish `e : (Fintype.card G : K) * (χ 1 / (Fintype.card G : K) * χ t⁻¹) = χ 1 * χ t⁻¹`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `((hX χ hχ).isIntegral 1).mul ((hX χ hχ).isIntegral t⁻¹)`. Use `first`. Consider the case `exact IsIntegral.sum _ key`.

Consider the case `exact IsIntegral.sum key`. Consider the case `exact (integralClosure ℤ K).sum_mem key`.
-/
theorem idemOf_integral {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
    (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (t : G) :
    ∃ b : 𝓞 K, (b : K) = (Fintype.card G : K) * (idemOf X).coeff t := by
  have hn : (Fintype.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [int_iff_lemma, coeff_idemOf, Finset.mul_sum]
  have key : ∀ χ ∈ X, IsIntegral ℤ ((Fintype.card G : K) * (χ 1 / (Fintype.card G : K) * χ t⁻¹)) := by
    intro χ hχ
    have e : (Fintype.card G : K) * (χ 1 / (Fintype.card G : K) * χ t⁻¹) = χ 1 * χ t⁻¹ := by
      field_simp
    rw [e]
    exact ((hX χ hχ).isIntegral 1).mul ((hX χ hχ).isIntegral t⁻¹)
  first
  | exact IsIntegral.sum _ key
  | exact IsIntegral.sum key
  | exact (integralClosure ℤ K).sum_mem key

end Chars

section Conj

/- English proof (translation)
Use `set H : Matrix (Fin n) (Fin n) ℂ := ∑ k ∈ Finset.range N, (B ^ k)ᴴ * B ^ k with hH`. Establish `hshift : Bᴴ * H * B = H`. Rewrite using `[hH, Finset.mul_sum, Finset.sum_mul]`. Establish `: ∀ k, Bᴴ * ((B ^ k)ᴴ * B ^ k) * B = (B ^ (k + 1))ᴴ * B ^ (k + 1)`. Introduce `k`.

Rewrite using `[pow_succ, Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Finset.sum_congr rfl fun k _ => this k]`. Establish `h1` using `Finset.sum_range_succ' (fun k => (B ^ k)ᴴ * B ^ k) N`. Establish `h2` using `Finset.sum_range_succ (fun k => (B ^ k)ᴴ * B ^ k) N`.

Rewrite `h1` using `[h2]`. Simplify using `only [hB, pow_zero] at h1`. Conclude with `(add_right_cancel h1).symm`. Establish `hpos : H.PosDef`. Take `⟨M, rfl⟩ : ∃ M, N = M + 1` from `Nat.exists_eq_succ_of_ne_zero hN`.

Rewrite using `[hH, Finset.sum_range_succ']`. Simplify using `only [pow_zero, Matrix.conjTranspose_one, Matrix.one_mul]`. Use `Matrix.PosDef.posSemidef_add ?_ Matrix.PosDef.one` and prove the remaining obligations. Conclude with `Matrix.posSemidef_sum _ fun k _ => Matrix.posSemidef_conjTranspose_mul_self _`. Establish `hu : IsUnit H.det` using `(Matrix.isUnit_iff_isUnit_det _).mp hpos.isUnit`.

Establish `hCe : C = H⁻¹ * Bᴴ * H`. Establish `h3 : (H⁻¹ * Bᴴ * H) * B = 1`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Bᴴ, hshift, Matrix.nonsing_inv_mul _ hu]`. Establish `h4 : B * C = 1` using `mul_eq_one_comm.mp hC`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hCe, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.trace_conjTranspose]`. Both sides reduce to the same expression.
-/
theorem trace_inv_of_pow_eq_one {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℂ) {N : ℕ} (hN : N ≠ 0)
    (hB : B ^ N = 1) (hC : C * B = 1) : C.trace = starRingEnd ℂ B.trace := by
  set H : Matrix (Fin n) (Fin n) ℂ := ∑ k ∈ Finset.range N, (B ^ k)ᴴ * B ^ k with hH
  have hshift : Bᴴ * H * B = H := by
    rw [hH, Finset.mul_sum, Finset.sum_mul]
    have : ∀ k, Bᴴ * ((B ^ k)ᴴ * B ^ k) * B = (B ^ (k + 1))ᴴ * B ^ (k + 1) := by
      intro k
      rw [pow_succ, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [Finset.sum_congr rfl fun k _ => this k]
    have h1 := Finset.sum_range_succ' (fun k => (B ^ k)ᴴ * B ^ k) N
    have h2 := Finset.sum_range_succ (fun k => (B ^ k)ᴴ * B ^ k) N
    rw [h2] at h1
    simp only [hB, pow_zero] at h1
    exact (add_right_cancel h1).symm
  have hpos : H.PosDef := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := Nat.exists_eq_succ_of_ne_zero hN
    rw [hH, Finset.sum_range_succ']
    simp only [pow_zero, Matrix.conjTranspose_one, Matrix.one_mul]
    refine Matrix.PosDef.posSemidef_add ?_ Matrix.PosDef.one
    exact Matrix.posSemidef_sum _ fun k _ => Matrix.posSemidef_conjTranspose_mul_self _
  have hu : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det _).mp hpos.isUnit
  have hCe : C = H⁻¹ * Bᴴ * H := by
    have h3 : (H⁻¹ * Bᴴ * H) * B = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Bᴴ, hshift, Matrix.nonsing_inv_mul _ hu]
    have h4 : B * C = 1 := mul_eq_one_comm.mp hC
    calc C = (H⁻¹ * Bᴴ * H) * B * C := by rw [h3, Matrix.one_mul]
      _ = H⁻¹ * Bᴴ * H := by rw [Matrix.mul_assoc _ B C, h4, Matrix.mul_one]
  rw [hCe, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul,
    Matrix.trace_conjTranspose]
  rfl

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

/- English proof (translation)
Take `⟨n, ρ, -, hρ⟩` from `h`. Set `_ : Algebra K ℂ` to `σ.toAlgebra`. Set `τ : AlgebraicClosure K →ₐ[K] ℂ` to `IsAlgClosed.lift`. Establish `hτ : ∀ x : K, τ (algebraMap K (AlgebraicClosure K) x) = σ x` using `fun x => τ.commutes x`. Set `A : G → Matrix (Fin n) (Fin n) (AlgebraicClosure K)` to `fun s => LinearMap.toMatrix' (ρ s)`.

Establish `hA : ∀ s, (A s).trace = algebraMap K (AlgebraicClosure K) (χ s)`. Introduce `s`. Rewrite using `[← hρ s, Representation.character, LinearMap.trace_eq_matrix_trace _ (Pi.basisFun _ (Fin n))]`. Both sides reduce to the same expression. Establish `hmul : ∀ s u, A (s * u) = A s * A u`.

Introduce `s u`. Simplify using `only [A, map_mul, Module.End.mul_eq_comp, LinearMap.toMatrix'_comp]`. Establish `hone : A 1 = 1` using `by simp [A, Module.End.one_eq_id]`. Establish `htr : ∀ s, ((A s).map τ).trace = σ (χ s)`. Introduce `s`.

Rewrite using `[← hτ, ← hA s, Matrix.trace, Matrix.trace, map_sum]`. Both sides reduce to the same expression. Establish `hmap : ∀ s u, (A (s * u)).map τ = (A s).map τ * (A u).map τ`. Introduce `s u`. Rewrite using `[hmul, Matrix.map_mul]`.

Establish `hpow : ∀ k : ℕ, ((A t).map τ) ^ k = (A (t ^ k)).map τ`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp [hone]`. Consider the case `succ k ih => rw [pow_succ, pow_succ, ih, hmap]`.

Rewrite using `[← htr, ← htr]`. Use `trace_inv_of_pow_eq_one _ _ (N := Fintype.card G) Fintype.card_ne_zero ?_ ?_` and prove the remaining obligations. Rewrite using `[hpow, pow_card_eq_one, hone]`. Simplify using the standard rewrite rules. Rewrite using `[← hmap, inv_mul_cancel, hone]`.

Simplify using the standard rewrite rules.
-/
theorem IsAbsIrrChar.map_inv {χ : G → K} (h : IsAbsIrrChar χ) (σ : K →+* ℂ) (t : G) :
    σ (χ t⁻¹) = starRingEnd ℂ (σ (χ t)) := by
  obtain ⟨n, ρ, -, hρ⟩ := h
  let _ : Algebra K ℂ := σ.toAlgebra
  let τ : AlgebraicClosure K →ₐ[K] ℂ := IsAlgClosed.lift
  have hτ : ∀ x : K, τ (algebraMap K (AlgebraicClosure K) x) = σ x := fun x => τ.commutes x
  let A : G → Matrix (Fin n) (Fin n) (AlgebraicClosure K) := fun s => LinearMap.toMatrix' (ρ s)
  have hA : ∀ s, (A s).trace = algebraMap K (AlgebraicClosure K) (χ s) := by
    intro s
    rw [← hρ s, Representation.character, LinearMap.trace_eq_matrix_trace _ (Pi.basisFun _ (Fin n))]
    rfl
  have hmul : ∀ s u, A (s * u) = A s * A u := by
    intro s u
    simp only [A, map_mul, Module.End.mul_eq_comp, LinearMap.toMatrix'_comp]
  have hone : A 1 = 1 := by simp [A, Module.End.one_eq_id]
  have htr : ∀ s, ((A s).map τ).trace = σ (χ s) := by
    intro s
    rw [← hτ, ← hA s, Matrix.trace, Matrix.trace, map_sum]
    rfl
  have hmap : ∀ s u, (A (s * u)).map τ = (A s).map τ * (A u).map τ := by
    intro s u
    rw [hmul, Matrix.map_mul]
  have hpow : ∀ k : ℕ, ((A t).map τ) ^ k = (A (t ^ k)).map τ := by
    intro k
    induction k with
    | zero => simp [hone]
    | succ k ih => rw [pow_succ, pow_succ, ih, hmap]
  rw [← htr, ← htr]
  refine trace_inv_of_pow_eq_one _ _ (N := Fintype.card G) Fintype.card_ne_zero ?_ ?_
  · rw [hpow, pow_card_eq_one, hone]; simp
  · rw [← hmap, inv_mul_cancel, hone]; simp

end Conj

section Assemble

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

/- English proof (translation)
Apply `v0.embedding.injective` to reduce the goal to its premises. Rewrite using `[hv, h.map_inv v0.embedding t]`.
-/
theorem IsAbsIrrChar.star_eq {v0 : InfinitePlace K} (hv : IsConjAt v0) {χ : G → K} (h : IsAbsIrrChar χ)
    (t : G) : star (χ t) = χ t⁻¹ := by
  apply v0.embedding.injective
  rw [hv, h.map_inv v0.embedding t]

/- English proof (translation)
Use `show ∀ σ : K →+* ℂ, σ (star (χ t)) = starRingEnd ℂ (σ (χ t))`. Introduce `σ`. Rewrite using `[h.star_eq hv t, h.map_inv σ t]`.
-/
theorem IsAbsIrrChar.mem_cmMax {v0 : InfinitePlace K} (hv : IsConjAt v0) {χ : G → K} (h : IsAbsIrrChar χ)
    (t : G) : χ t ∈ cmMax K := by
  show ∀ σ : K →+* ℂ, σ (star (χ t)) = starRingEnd ℂ (σ (χ t))
  intro σ
  rw [h.star_eq hv t, h.map_inv σ t]

/- English proof (translation)
Unfold `chiIdem`. Rewrite using `[gaStar_sum]`. Simplify using `only [gaStar_single]`. Rewrite using `[← Equiv.sum_comp (Equiv.inv G)]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations.

Simplify using `only [Equiv.inv_apply, inv_inv]`. Use `congr 1`. Rewrite using `[star_mul', star_div₀, star_natCast, h.star_eq hv, h.star_eq hv, inv_one]`.
-/
theorem chiIdem_selfAdj {v0 : InfinitePlace K} (hv : IsConjAt v0) {χ : G → K} (h : IsAbsIrrChar χ) :
    gaStar (chiIdem χ) = chiIdem χ := by
  unfold chiIdem
  rw [gaStar_sum]
  simp only [gaStar_single]
  rw [← Equiv.sum_comp (Equiv.inv G)]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Equiv.inv_apply, inv_inv]
  congr 1
  rw [star_mul', star_div₀, star_natCast, h.star_eq hv, h.star_eq hv, inv_one]

/- English proof (translation)
Introduce `K _ _ _ v0 hv G _ _ X hX`. Use `⟨⟨hidem K G X hX, ?_, ?_, idemOf_integral X hX⟩, idemOf_central X hX⟩` and prove the remaining obligations. Unfold `idemOf`. Rewrite using `[gaStar_sum]`. Conclude with `Finset.sum_congr rfl fun χ hχ => chiIdem_selfAdj hv (hX χ hχ)`.

Introduce `t`. Rewrite using `[coeff_idemOf]`. Conclude with `sum_mem fun χ hχ => mul_mem (div_mem ((hX χ hχ).mem_cmMax hv 1) (natCast_mem _ _)) ((hX χ hχ).mem_cmMax hv t⁻¹)`.
-/
theorem idemOfSpec_of
    (hidem : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K)),
      (∀ χ ∈ X, IsAbsIrrChar χ) → idemOf X * idemOf X = idemOf X) : IdemOfSpec := by
  intro K _ _ _ v0 hv G _ _ X hX
  refine ⟨⟨hidem K G X hX, ?_, ?_, idemOf_integral X hX⟩, idemOf_central X hX⟩
  · unfold idemOf
    rw [gaStar_sum]
    exact Finset.sum_congr rfl fun χ hχ => chiIdem_selfAdj hv (hX χ hχ)
  · intro t
    rw [coeff_idemOf]
    exact sum_mem fun χ hχ => mul_mem (div_mem ((hX χ hχ).mem_cmMax hv 1) (natCast_mem _ _))
      ((hX χ hχ).mem_cmMax hv t⁻¹)

end Assemble

section Schur

open Representation

/- English proof (translation)
Take `⟨c, hc⟩` from `(IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).2 (T.intertwiningMap_of_isIntertwiningMap ρ ρ hT)`. Use `⟨c, ?_⟩` and prove the remaining obligations. Use extensionality with `v`. Use `congrArg (fun f : IntertwiningMap ρ ρ => f v) hc` as an intermediate fact. Simplify using `using this.symm`.
-/
theorem schur_scalar {k V G : Type} [Field k] [IsAlgClosed k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) [ρ.IsIrreducible] (T : V →ₗ[k] V)
    (hT : ∀ g v, T (ρ g v) = ρ g (T v)) : ∃ c : k, T = c • LinearMap.id := by
  obtain ⟨c, hc⟩ := (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).2
    (T.intertwiningMap_of_isIntertwiningMap ρ ρ hT)
  refine ⟨c, ?_⟩
  ext v
  have := congrArg (fun f : IntertwiningMap ρ ρ => f v) hc
  simpa using this.symm

/- English proof (translation)
Use `set T : V →ₗ[k] V := ∑ s, φ s • ρ s with hTdef`. Establish `hT : ∀ g v, T (ρ g v) = ρ g (T v)`. Introduce `g v`. Simplify using `only [hTdef, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]`. Rewrite using `[← Equiv.sum_comp (MulAut.conj g).toEquiv]`.

Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Establish `e1 : φ ((MulAut.conj g).toEquiv s) = φ s` using `by simpa [MulAut.conj_apply] using hφ g s`. Rewrite using `[e1]`. Use `congr 1`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]`.

Simplify using `[MulAut.conj_apply]`. Take `⟨c, hc⟩` from `schur_scalar ρ T hT`. Establish `h1 : ∀ u : G, ∑ s, φ s * ρ.character (s * u) = c * ρ.character u`. Introduce `u`. Establish `: LinearMap.trace k V (T * ρ u) = c * ρ.character u`.

Rewrite using `[hc]`. Simplify using `[character, Module.End.mul_eq_comp]`. Rewrite using `[← this, hTdef, Finset.sum_mul, map_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, map_smul, smul_eq_mul, character, map_mul]`.

Establish `h2` using `h1 1`. Simplify using `only [mul_one, char_one] at h2`. Rewrite using `[h1 u, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem convA {k V G : Type} [Field k] [IsAlgClosed k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) [ρ.IsIrreducible] (φ : G → k)
    (hφ : ∀ g s, φ (g * s * g⁻¹) = φ s) (u : G) :
    (∑ s, φ s * ρ.character (s * u)) * (finrank k V : k) = (∑ s, φ s * ρ.character s) * ρ.character u := by
  set T : V →ₗ[k] V := ∑ s, φ s • ρ s with hTdef
  have hT : ∀ g v, T (ρ g v) = ρ g (T v) := by
    intro g v
    simp only [hTdef, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
    rw [← Equiv.sum_comp (MulAut.conj g).toEquiv]
    refine Finset.sum_congr rfl fun s _ => ?_
    have e1 : φ ((MulAut.conj g).toEquiv s) = φ s := by simpa [MulAut.conj_apply] using hφ g s
    rw [e1]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [MulAut.conj_apply]
  obtain ⟨c, hc⟩ := schur_scalar ρ T hT
  have h1 : ∀ u : G, ∑ s, φ s * ρ.character (s * u) = c * ρ.character u := by
    intro u
    have : LinearMap.trace k V (T * ρ u) = c * ρ.character u := by
      rw [hc]; simp [character, Module.End.mul_eq_comp]
    rw [← this, hTdef, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul, character, map_mul]
  have h2 := h1 1
  simp only [mul_one, char_one] at h2
  rw [h1 u, h2]
  ring

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

open Classical in

/- English proof (translation)
Establish `hcl : ∀ g s, χ (g * s * g⁻¹)⁻¹ = χ s⁻¹`. Introduce `g s`. Use `h.conj g s⁻¹` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Take `⟨n, ρ, hi, hρ⟩` from `h`.

Take `⟨n', ρ', hi', hρ'⟩` from `h'`. Set `j` to `algebraMap K (AlgebraicClosure K)`. Establish `hj : Function.Injective j` using `j.injective`. Establish `: Invertible ((Nat.card G : ℕ) : AlgebraicClosure K)` using `invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')`. Establish `hcard : ((Nat.card G : ℕ) : AlgebraicClosure K) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`.

Establish `hA` using `convA ρ' (fun s => j (χ s⁻¹)) (fun g s => by simp only [hcl]) u`. Establish `hfin : ((finrank (AlgebraicClosure K) (Fin n' → AlgebraicClosure K) : ℕ) : AlgebraicClosure K) = j (χ' 1)` using `by rw [← hρ', char_one]`. Establish `hsum : (∑ s, j (χ s⁻¹) * ρ'.character s) = if χ = χ' then ((Nat.card G : ℕ) : AlgebraicClosure K) else 0`. Establish `ho` using `char_orthonormal ρ' ρ`. Establish `e : (∑ s, j (χ s⁻¹) * ρ'.character s) = ∑ g, ρ'.character g * ρ.character g⁻¹` using `Finset.sum_congr rfl fun s _ => by rw [hρ, mul_comm]`.

Rewrite using `[e]`. Establish `hiff : Nonempty (Representation.Equiv ρ ρ') ↔ χ = χ'`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨φ⟩`. Use function extensionality and compare the values at `t`.

Apply `hj` to reduce the goal to its premises. Rewrite using `[← hρ, ← hρ', char_iso φ]`. Introduce `hc`. Assume the negation of the conclusion as `hne`. Rewrite `ho` using `[if_neg hne]`.

Establish `ho'` using `card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ`. Rewrite `ho'` using `[IsIrreducible.finrank_intertwiningMap_self]`. Establish `: ∀ g, ρ'.character g = ρ.character g` using `fun g => by rw [hρ, hρ', hc]`. Simplify using `only [this] at ho`. Rewrite `ho'` using `[ho]`.

Simplify using `at ho'`. Distinguish the cases in `hc : χ = χ'`. Rewrite using `[if_pos hc]`. Rewrite `ho` using `[if_pos (hiff.mpr hc)]`. Clear denominators, using `at ho` for the nonvanishing conditions.

Simplify using `using ho`. Rewrite using `[if_neg hc]`. Rewrite `ho` using `[if_neg (fun hh => hc (hiff.mp hh))]`. Simplify using `using ho`. Apply `hj` to reduce the goal to its premises.

Rewrite `hA` using `[hfin, hsum]`. Simplify using `only [hρ'] at hA`. Rewrite using `[map_mul, map_sum]`. Simplify using `only [map_mul]`. Rewrite using `[hA]`.

Use `split_ifs`. Rewrite using `[map_mul, map_natCast, Nat.card_eq_fintype_card]`. Simplify using the standard rewrite rules.
-/
theorem conv_char {χ χ' : G → K} (h : IsAbsIrrChar χ) (h' : IsAbsIrrChar χ') (u : G) :
    (∑ s, χ s⁻¹ * χ' (s * u)) * χ' 1 = if χ = χ' then (Fintype.card G : K) * χ' u else 0 := by
  classical
  have hcl : ∀ g s, χ (g * s * g⁻¹)⁻¹ = χ s⁻¹ := by
    intro g s
    have := h.conj g s⁻¹
    simpa [mul_assoc] using this
  obtain ⟨n, ρ, hi, hρ⟩ := h
  obtain ⟨n', ρ', hi', hρ'⟩ := h'
  let j := algebraMap K (AlgebraicClosure K)
  have hj : Function.Injective j := j.injective
  have : Invertible ((Nat.card G : ℕ) : AlgebraicClosure K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hcard : ((Nat.card G : ℕ) : AlgebraicClosure K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hA := convA ρ' (fun s => j (χ s⁻¹)) (fun g s => by simp only [hcl]) u
  have hfin : ((finrank (AlgebraicClosure K) (Fin n' → AlgebraicClosure K) : ℕ) : AlgebraicClosure K) =
      j (χ' 1) := by rw [← hρ', char_one]
  have hsum : (∑ s, j (χ s⁻¹) * ρ'.character s) =
      if χ = χ' then ((Nat.card G : ℕ) : AlgebraicClosure K) else 0 := by
    have ho := char_orthonormal ρ' ρ
    have e : (∑ s, j (χ s⁻¹) * ρ'.character s) = ∑ g, ρ'.character g * ρ.character g⁻¹ :=
      Finset.sum_congr rfl fun s _ => by rw [hρ, mul_comm]
    rw [e]
    have hiff : Nonempty (Representation.Equiv ρ ρ') ↔ χ = χ' := by
      constructor
      · rintro ⟨φ⟩
        funext t
        apply hj
        rw [← hρ, ← hρ', char_iso φ]
      · intro hc
        by_contra hne
        rw [if_neg hne] at ho
        have ho' := card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
        rw [IsIrreducible.finrank_intertwiningMap_self] at ho'
        have : ∀ g, ρ'.character g = ρ.character g := fun g => by rw [hρ, hρ', hc]
        simp only [this] at ho
        rw [ho] at ho'
        simp at ho'
    by_cases hc : χ = χ'
    · rw [if_pos hc]
      rw [if_pos (hiff.mpr hc)] at ho
      field_simp at ho
      simpa using ho
    · rw [if_neg hc]
      rw [if_neg (fun hh => hc (hiff.mp hh))] at ho
      simpa using ho
  apply hj
  rw [hfin, hsum] at hA
  simp only [hρ'] at hA
  rw [map_mul, map_sum]
  simp only [map_mul]
  rw [hA]
  split_ifs
  · rw [map_mul, map_natCast, Nat.card_eq_fintype_card]
  · simp

open Classical in
/- English proof (translation)
Establish `hn : (Fintype.card G : K) ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`. Use extensionality with `u`. Rewrite using `[coeff_mul_fin]`. Simplify using `only [coeff_chiIdem]`. Establish `hs : ∑ s : G, χ 1 / (Fintype.card G : K) * χ s⁻¹ * (χ' 1 / (Fintype.card G : K) * χ' (s⁻¹ * u)⁻¹) = χ 1 / (Fintype.card G : K) ^ 2 * ((∑ s, χ s⁻¹ * χ' (s * u⁻¹)) * χ' 1)`.

Rewrite using `[Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[mul_inv_rev, inv_inv, show χ' (u⁻¹ * s) = χ' (s * u⁻¹) from ?_]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← h'.conj s (u⁻¹ * s)]`.

Use `congr 1`. Use `group`. Rewrite using `[hs, conv_char h h' u⁻¹]`. Use `split_ifs with he`. Substitute `he` using the available equality.

Rewrite using `[coeff_chiIdem]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`. Rewrite using `[mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem chiIdem_mul {χ χ' : G → K} (h : IsAbsIrrChar χ) (h' : IsAbsIrrChar χ') :
    chiIdem χ * chiIdem χ' = if χ = χ' then chiIdem χ' else 0 := by
  classical
  have hn : (Fintype.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  ext u
  rw [coeff_mul_fin]
  simp only [coeff_chiIdem]
  have hs : ∑ s : G, χ 1 / (Fintype.card G : K) * χ s⁻¹ * (χ' 1 / (Fintype.card G : K) * χ' (s⁻¹ * u)⁻¹) =
      χ 1 / (Fintype.card G : K) ^ 2 * ((∑ s, χ s⁻¹ * χ' (s * u⁻¹)) * χ' 1) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_inv_rev, inv_inv, show χ' (u⁻¹ * s) = χ' (s * u⁻¹) from ?_]
    · ring
    · rw [← h'.conj s (u⁻¹ * s)]
      congr 1
      group
  rw [hs, conv_char h h' u⁻¹]
  split_ifs with he
  · subst he
    rw [coeff_chiIdem]
    field_simp
    try ring
  · rw [mul_zero]
    simp

/- English proof (translation)
Unfold `idemOf`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun χ hχ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.sum_congr rfl fun χ' hχ' => chiIdem_mul (hX χ hχ) (hX χ' hχ'), Finset.sum_ite_eq, if_pos hχ]`.
-/
theorem idemOf_mul_self (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) :
    idemOf X * idemOf X = idemOf X := by
  classical
  unfold idemOf
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  rw [Finset.mul_sum, Finset.sum_congr rfl fun χ' hχ' => chiIdem_mul (hX χ hχ) (hX χ' hχ'),
    Finset.sum_ite_eq, if_pos hχ]

end Schur

/- English proof (translation)
Conclude with `idemOfSpec_of (fun K _ _ G _ _ X hX => idemOf_mul_self X hX)`.
-/
theorem idempotent_spec : IdemOfSpec := by
  exact idemOfSpec_of (fun K _ _ G _ _ X hX => idemOf_mul_self X hX)

/- English proof (translation)
Conclude with `goodAtSpec_of idempotent_spec level_idempotent_spec`.
-/
theorem good_at_spec : GoodAtSpec := by
  exact goodAtSpec_of idempotent_spec level_idempotent_spec

/- English proof (translation)
Establish `hE` using `(group_action_matrix_hom K S G r).2`. Unfold `CSD.V0E CSD.cutE`. Rewrite using `[(image_idempotent_spec K S.dim (S.gaMat r (goodAt X P ψ))).2]`. Unfold `goodAt`. Rewrite using `[hE, ← level_part_spec K S G r P ψ]`.

Establish `hEE : S.gaMat r (idemOf X) * S.gaMat r (idemOf X) = S.gaMat r (idemOf X)`. Rewrite using `[← hE, hidem]`. Establish `hFF : S.gaMat r (lvlIdem P ψ) * S.gaMat r (lvlIdem P ψ) = S.gaMat r (lvlIdem P ψ)`. Rewrite using `[← hE, lvlIdem_idem]`. Establish `hEF : S.gaMat r (lvlIdem P ψ) * S.gaMat r (idemOf X) = S.gaMat r (idemOf X) * S.gaMat r (lvlIdem P ψ)`.

Rewrite using `[← hE, ← hE, hcomm]`. Use extensionality with `y`. Simplify using `only [LinearMap.mem_range, Matrix.mulVecLin_apply, Submodule.mem_inf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`.

Conclude with `⟨⟨(S.gaMat r (lvlIdem P ψ)).mulVec x, by rw [Matrix.mulVec_mulVec]⟩, ⟨(S.gaMat r (idemOf X)).mulVec x, by rw [Matrix.mulVec_mulVec, hEF]⟩⟩`. Introduce and unpack `⟨⟨a, ha⟩, ⟨b, hb⟩⟩`. Use `⟨y, ?_⟩` and prove the remaining obligations. Establish `hy1 : (S.gaMat r (idemOf X)).mulVec y = y` using `by rw [← ha, Matrix.mulVec_mulVec, hEE]`. Establish `hy2 : (S.gaMat r (lvlIdem P ψ)).mulVec y = y` using `by rw [← hb, Matrix.mulVec_mulVec, hFF]`.

Rewrite using `[← Matrix.mulVec_mulVec, hy2, hy1]`.
-/
theorem range_V0E {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G]
    [Fintype G] (r : Representation K G S.Forms) (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ)
    (hidem : idemOf X * idemOf X = idemOf X)
    (hcomm : lvlIdem P ψ * idemOf X = idemOf X * lvlIdem P ψ) :
    LinearMap.range (S.V0E r X P ψ).mulVecLin =
      LinearMap.range (S.gaMat r (idemOf X)).mulVecLin ⊓ S.lvlPart r P ψ := by
  have hE := (group_action_matrix_hom K S G r).2
  unfold CSD.V0E CSD.cutE
  rw [(image_idempotent_spec K S.dim (S.gaMat r (goodAt X P ψ))).2]
  unfold goodAt
  rw [hE, ← level_part_spec K S G r P ψ]
  have hEE : S.gaMat r (idemOf X) * S.gaMat r (idemOf X) = S.gaMat r (idemOf X) := by
    rw [← hE, hidem]
  have hFF : S.gaMat r (lvlIdem P ψ) * S.gaMat r (lvlIdem P ψ) = S.gaMat r (lvlIdem P ψ) := by
    rw [← hE, lvlIdem_idem]
  have hEF : S.gaMat r (lvlIdem P ψ) * S.gaMat r (idemOf X) = S.gaMat r (idemOf X) * S.gaMat r (lvlIdem P ψ) := by
    rw [← hE, ← hE, hcomm]
  ext y
  simp only [LinearMap.mem_range, Matrix.mulVecLin_apply, Submodule.mem_inf]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨(S.gaMat r (lvlIdem P ψ)).mulVec x, by rw [Matrix.mulVec_mulVec]⟩,
      ⟨(S.gaMat r (idemOf X)).mulVec x, by rw [Matrix.mulVec_mulVec, hEF]⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨y, ?_⟩
    have hy1 : (S.gaMat r (idemOf X)).mulVec y = y := by rw [← ha, Matrix.mulVec_mulVec, hEE]
    have hy2 : (S.gaMat r (lvlIdem P ψ)).mulVec y = y := by rw [← hb, Matrix.mulVec_mulVec, hFF]
    rw [← Matrix.mulVec_mulVec, hy2, hy1]

/- English proof (translation)
Introduce `K _ _ _ S G _ _ r X hX P ψ`. Take `⟨hidem, hcent⟩` from `h K G X hX`. Conclude with `range_V0E S r X P ψ hidem (hcent _)`.
-/
theorem good_part_spec_of_central (h : IdemOfCentral) : GoodPartSpec := by
  intro K _ _ _ S G _ _ r X hX P ψ
  obtain ⟨hidem, hcent⟩ := h K G X hX
  exact range_V0E S r X P ψ hidem (hcent _)

/- English proof (translation)
Establish `ha' : ∀ σ : K →+* ℂ, σ (star a) = starRingEnd ℂ (σ a)` using `ha`. Use `show ∀ σ : K →+* ℂ, σ (star (star a)) = starRingEnd ℂ (σ (star a))`. Introduce `σ`. Rewrite using `[star_star, ha' σ, Complex.conj_conj]`.
-/
theorem star_mem_cmMax {K : Type} [Field K] [StarRing K] {a : K} (ha : a ∈ cmMax K) :
    star a ∈ cmMax K := by
  have ha' : ∀ σ : K →+* ℂ, σ (star a) = starRingEnd ℂ (σ a) := ha
  show ∀ σ : K →+* ℂ, σ (star (star a)) = starRingEnd ℂ (σ (star a))
  intro σ
  rw [star_star, ha' σ, Complex.conj_conj]

/- English proof (translation)
Establish `hc : ∀ j, ∃ c : Fin n → K, A.mulVec c = fun i => B i j`. Introduce `j`. Establish `hB : (fun i => B i j) ∈ LinearMap.range B.mulVecLin` using `LinearMap.mem_range.mpr ⟨Pi.single j 1, by`. Use extensionality with `i`. Simplify using `[Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]⟩`.

Take `⟨c, hc⟩` from `LinearMap.mem_range.mp (h hB)`. Conclude with `⟨c, by rw [← Matrix.mulVecLin_apply]; exact hc⟩`. Use `choose c hc using hc`. Use `⟨Matrix.of fun k j => c j k, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Use `congrFun (hc j) i` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct] at this`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply]`. Conclude with `this.symm`.
-/
private theorem exists_mul_lemma {K : Type} [Field K] {m n p : ℕ} {A : Matrix (Fin m) (Fin n) K}
    {B : Matrix (Fin m) (Fin p) K}
    (h : LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin) :
    ∃ C : Matrix (Fin n) (Fin p) K, B = A * C := by
  have hc : ∀ j, ∃ c : Fin n → K, A.mulVec c = fun i => B i j := by
    intro j
    have hB : (fun i => B i j) ∈ LinearMap.range B.mulVecLin :=
      LinearMap.mem_range.mpr ⟨Pi.single j 1, by
        ext i
        simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]⟩
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp (h hB)
    exact ⟨c, by rw [← Matrix.mulVecLin_apply]; exact hc⟩
  choose c hc using hc
  refine ⟨Matrix.of fun k j => c j k, ?_⟩
  ext i j
  have := congrFun (hc j) i
  simp only [Matrix.mulVec, dotProduct] at this
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact this.symm

/- English proof (translation)
Establish `hE' : Function.Injective E.mulVecLin` using `hE`. Establish `hrk : E.rank = d`. Unfold `Matrix.rank`. Rewrite using `[LinearMap.finrank_range_of_inj hE', Module.finrank_fin_fun]`. Establish `hrkT : Eᵀ.rank = d` using `by rw [Matrix.rank_transpose, hrk]`.

Establish `htop : LinearMap.range Eᵀ.mulVecLin = ⊤`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[Module.finrank_fin_fun]`. Conclude with `hrkT`. Take `⟨C, hC⟩` from `exists_mul_lemma (A := Eᵀ) (B := (1 : Matrix (Fin d) (Fin d) K)) (by rw [htop]; exact le_top)`.

Establish `hL : Cᵀ * E = 1`. Use `congrArg Matrix.transpose hC` as an intermediate fact. Rewrite `this` using `[Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose, eq_comm]`. Then use the resulting hypothesis. Establish `hLσ : Cᵀ.map σ * E.map σ = 1` using `by rw [← Matrix.map_mul, hL, Matrix.map_one _ σ.map_zero σ.map_one]`. Introduce `x y hxy`.

Use `congrArg (fun z => (Cᵀ.map σ).mulVec z) hxy` as an intermediate fact. Simplify using `only [Matrix.mulVec_mulVec, hLσ, Matrix.one_mulVec] at this`. Conclude with `this`.
-/
theorem map_injective_of_injective {K : Type} [Field K] {n d : ℕ} (E : Matrix (Fin n) (Fin d) K)
    (hE : Function.Injective E.mulVec) (σ : K →+* ℂ) : Function.Injective (E.map σ).mulVec := by
  have hE' : Function.Injective E.mulVecLin := hE
  have hrk : E.rank = d := by
    unfold Matrix.rank
    rw [LinearMap.finrank_range_of_inj hE', Module.finrank_fin_fun]
  have hrkT : Eᵀ.rank = d := by rw [Matrix.rank_transpose, hrk]
  have htop : LinearMap.range Eᵀ.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact hrkT
  obtain ⟨C, hC⟩ := exists_mul_lemma (A := Eᵀ) (B := (1 : Matrix (Fin d) (Fin d) K))
    (by rw [htop]; exact le_top)
  have hL : Cᵀ * E = 1 := by
    have := congrArg Matrix.transpose hC
    rwa [Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose, eq_comm] at this
  have hLσ : Cᵀ.map σ * E.map σ = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ σ.map_zero σ.map_one]
  intro x y hxy
  have := congrArg (fun z => (Cᵀ.map σ).mulVec z) hxy
  simp only [Matrix.mulVec_mulVec, hLσ, Matrix.one_mulVec] at this
  exact this

/- English proof (translation)
Establish `hE'` using `map_injective_of_injective E hE v.embedding`. Establish `key : (Eᴴ * H * E).map v.embedding = (E.map v.embedding)ᴴ * H.map v.embedding * E.map v.embedding`. Rewrite using `[Matrix.map_mul, Matrix.map_mul]`. Use `congr 2`. Use extensionality with `i j`.

Simplify using `only [Matrix.map_apply, Matrix.conjTranspose_apply]`. Conclude with `hrat j i v.embedding`. Establish `hsm : ((N : K)⁻¹ • (Eᴴ * H * E)).map v.embedding = ((N : ℂ)⁻¹) • ((Eᴴ * H * E).map v.embedding)`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast]`.

Establish `hc : (0 : ℂ) < (N : ℂ)⁻¹` using `inv_pos.mpr (Nat.cast_pos.mpr hN)`. Rewrite using `[hsm, key]`. Establish `hP` using `hpos.conjTranspose_mul_mul_same hE'`. Use `first`. Consider the case `exact hP.smul hc`.

Consider the case `exact Matrix.PosDef.smul hP hc`.
-/
theorem cut_posDef {K : Type} [Field K] [NumberField K] [StarRing K] {n d : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin d) K)
    (hE : Function.Injective E.mulVec) (hrat : ∀ i j, E i j ∈ cmMax K) (N : ℕ) (hN : 0 < N)
    (v : InfinitePlace K) (hpos : (H.map v.embedding).PosDef) :
    (((N : K)⁻¹ • (Eᴴ * H * E)).map v.embedding).PosDef := by
  have hE' := map_injective_of_injective E hE v.embedding
  have key : (Eᴴ * H * E).map v.embedding =
      (E.map v.embedding)ᴴ * H.map v.embedding * E.map v.embedding := by
    rw [Matrix.map_mul, Matrix.map_mul]
    congr 2
    ext i j
    simp only [Matrix.map_apply, Matrix.conjTranspose_apply]
    exact hrat j i v.embedding
  have hsm : ((N : K)⁻¹ • (Eᴴ * H * E)).map v.embedding = ((N : ℂ)⁻¹) • ((Eᴴ * H * E).map v.embedding) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast]
  have hc : (0 : ℂ) < (N : ℂ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hN)
  rw [hsm, key]
  have hP := hpos.conjTranspose_mul_mul_same hE'
  first
  | exact hP.smul hc
  | exact Matrix.PosDef.smul hP hc

/- English proof (translation)
Unfold `CSD.gaMat`. Rewrite using `[Matrix.sum_apply]`. Conclude with `sum_mem fun t _ => by`. Rewrite using `[Matrix.smul_apply, smul_eq_mul]`. Conclude with `mul_mem (ha t) (hr t i j)`.
-/
theorem gaMat_rat {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G]
    [Fintype G] (r : Representation K G S.Forms) (hr : S.ActRat r) (a : MonoidAlgebra K G)
    (ha : ∀ t, a.coeff t ∈ cmMax K) (i j : Fin S.dim) : S.gaMat r a i j ∈ cmMax K := by
  unfold CSD.gaMat
  rw [Matrix.sum_apply]
  exact sum_mem fun t _ => by
    rw [Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (ha t) (hr t i j)

/- English proof (translation)
Introduce `K _ _ _ v0 hv S hH hpos G _ _ r hr X hX P ψ`. Establish `hrat : ∀ i j, S.V0E r X P ψ i j ∈ cmMax K`. Introduce `i j`. Unfold `CSD.V0E CSD.cutE`. Conclude with `image_idempotent_rational K S.dim _ (fun i j => gaMat_rat S r hr _ (h K v0 hv G X hX P ψ).rat i j) i j`.

Use `⟨hrat, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Unfold `CSD.goodPartHermitianForm CSD.cutH`. Rewrite using `[Matrix.smul_apply, smul_eq_mul]`. Use `mul_mem (inv_mem (natCast_mem _ _)) ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mul_apply]`. Use `sum_mem fun k _ => mul_mem ?_ (hrat k j)` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Conclude with `sum_mem fun l _ => mul_mem (by rw [Matrix.conjTranspose_apply]; exact star_mem_cmMax (hrat l i)) (hH l k)`. Introduce `v`.

Unfold `CSD.goodPartHermitianForm CSD.cutH`. Conclude with `cut_posDef S.H (S.cutE r _) (image_idempotent_spec K S.dim _).1 hrat (Nat.card P) Nat.card_pos v (hpos v)`.
-/
theorem good_part_hermitian_of_spec (h : GoodAtSpec) : GoodPartHermitianSpec := by
  intro K _ _ _ v0 hv S hH hpos G _ _ r hr X hX P ψ
  have hrat : ∀ i j, S.V0E r X P ψ i j ∈ cmMax K := by
    intro i j
    unfold CSD.V0E CSD.cutE
    exact image_idempotent_rational K S.dim _ (fun i j => gaMat_rat S r hr _ (h K v0 hv G X hX P ψ).rat i j) i j
  refine ⟨hrat, ?_, ?_⟩
  · intro i j
    unfold CSD.goodPartHermitianForm CSD.cutH
    rw [Matrix.smul_apply, smul_eq_mul]
    refine mul_mem (inv_mem (natCast_mem _ _)) ?_
    rw [Matrix.mul_apply]
    refine sum_mem fun k _ => mul_mem ?_ (hrat k j)
    rw [Matrix.mul_apply]
    exact sum_mem fun l _ => mul_mem (by rw [Matrix.conjTranspose_apply]; exact star_mem_cmMax (hrat l i)) (hH l k)
  · intro v
    unfold CSD.goodPartHermitianForm CSD.cutH
    exact cut_posDef S.H (S.cutE r _) (image_idempotent_spec K S.dim _).1 hrat (Nat.card P) Nat.card_pos v (hpos v)

/- English proof (translation)
Introduce `K _ _ _ v0 hv S hpos G _ _ r hr P ψ a ha`. Take `⟨⟨hI, hS, -, -⟩, -⟩` from `h2 K v0 hv G P ψ`. Take `⟨⟨hPE, -⟩, hEP⟩` from `h1 K v0 hv S hpos G r hr (lvlIdem P ψ) hI hS`. Establish `hmul` using `(group_action_matrix_hom K S G r).2`. Establish `hcomm : S.gaMat r a * S.gaMat r (lvlIdem P ψ) = S.gaMat r (lvlIdem P ψ) * S.gaMat r a`.

Rewrite using `[← hmul, ← hmul, ha]`. Unfold `CSD.lvlOp CSD.lvlE CSD.lvlPr`. Use `set E := S.cutE r (lvlIdem P ψ)`. Use `set Pr := S.cutPr r (lvlIdem P ψ)`. Use `set F := S.gaMat r (lvlIdem P ψ)`.

Establish `hFE : F * E = E` using `by rw [← hEP, Matrix.mul_assoc, hPE, Matrix.mul_one]`. Prove the components needed by the constructor for the conclusion. Combine the equalities or inequalities in the displayed calculation. Introduce `b`. Rewrite using `[hmul]`.

Use `symm`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Pr * S.gaMat r b * F * S.gaMat r a * E := by rw [hEP]`. Use `_ = Pr * S.gaMat r b * (F * S.gaMat r a) * E := by simp only [Matrix.mul_assoc]`.

Use `_ = Pr * S.gaMat r b * (S.gaMat r a * F) * E := by rw [hcomm]`. Use `_ = Pr * (S.gaMat r b * S.gaMat r a) * (F * E) := by simp only [Matrix.mul_assoc]`. Use `_ = Pr * (S.gaMat r b * S.gaMat r a) * E := by rw [hFE]`.
-/
theorem lvlOpSpec_of (h1 : CutOrthProj) (h2 : LvlIdemSpec) : LvlOpSpec := by
  intro K _ _ _ v0 hv S hpos G _ _ r hr P ψ a ha
  obtain ⟨⟨hI, hS, -, -⟩, -⟩ := h2 K v0 hv G P ψ
  obtain ⟨⟨hPE, -⟩, hEP⟩ := h1 K v0 hv S hpos G r hr (lvlIdem P ψ) hI hS
  have hmul := (group_action_matrix_hom K S G r).2
  have hcomm : S.gaMat r a * S.gaMat r (lvlIdem P ψ) = S.gaMat r (lvlIdem P ψ) * S.gaMat r a := by
    rw [← hmul, ← hmul, ha]
  unfold CSD.lvlOp CSD.lvlE CSD.lvlPr
  set E := S.cutE r (lvlIdem P ψ)
  set Pr := S.cutPr r (lvlIdem P ψ)
  set F := S.gaMat r (lvlIdem P ψ)
  have hFE : F * E = E := by rw [← hEP, Matrix.mul_assoc, hPE, Matrix.mul_one]
  constructor
  · calc E * (Pr * S.gaMat r a * E) = E * Pr * S.gaMat r a * E := by simp only [Matrix.mul_assoc]
      _ = F * S.gaMat r a * E := by rw [hEP]
      _ = S.gaMat r a * F * E := by rw [hcomm]
      _ = S.gaMat r a * (F * E) := Matrix.mul_assoc _ _ _
      _ = S.gaMat r a * E := by rw [hFE]
  · intro b
    rw [hmul]
    symm
    calc Pr * S.gaMat r b * E * (Pr * S.gaMat r a * E) = Pr * S.gaMat r b * (E * Pr) * S.gaMat r a * E := by
          simp only [Matrix.mul_assoc]
      _ = Pr * S.gaMat r b * F * S.gaMat r a * E := by rw [hEP]
      _ = Pr * S.gaMat r b * (F * S.gaMat r a) * E := by simp only [Matrix.mul_assoc]
      _ = Pr * S.gaMat r b * (S.gaMat r a * F) * E := by rw [hcomm]
      _ = Pr * (S.gaMat r b * S.gaMat r a) * (F * E) := by simp only [Matrix.mul_assoc]
      _ = Pr * (S.gaMat r b * S.gaMat r a) * E := by rw [hFE]

/- English proof (translation)
Conclude with `exists_mul_lemma h`.
-/
theorem exists_mul_of_range_le {K : Type} [Field K] {m n p : ℕ} {A : Matrix (Fin m) (Fin n) K}
    {B : Matrix (Fin m) (Fin p) K}
    (h : LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin) :
    ∃ C : Matrix (Fin n) (Fin p) K, B = A * C := by
  exact exists_mul_lemma h

/- English proof (translation)
Introduce `K _ _ _ v0 hv S hpos G _ _ r hr a hidem hself`. Take `⟨hinj, hrange⟩` from `h1 K S.dim (S.gaMat r a)`. Take `⟨-, hHdet, -, hOP, -⟩` from `orthogonal_projection_exists K v0 hv S.dim _ S.H hpos (S.cutE r a) hinj`. Establish `hOP' : IsOrthProj S.H (S.cutE r a) (S.cutPr r a)` using `hOP`. Use `⟨hOP', ?_⟩` and prove the remaining obligations.

Take `⟨-, hO⟩` from `hOP'`. Establish `hAA : S.gaMat r a * S.gaMat r a = S.gaMat r a` using `by rw [← (h2 K S G r).2, hidem]`. Establish `hadj : (S.gaMat r a)ᴴ * S.H = S.H * S.gaMat r a` using `by rw [h3 K S G r hr a, hself]`. Establish `hrE : LinearMap.range (S.cutE r a).mulVecLin = LinearMap.range (S.gaMat r a).mulVecLin` using `hrange`. Take `⟨C, hC⟩` from `exists_mul_of_range_le (A := S.cutE r a) (B := S.gaMat r a) hrE.ge`.

Take `⟨D, hD⟩` from `exists_mul_of_range_le (A := S.gaMat r a) (B := S.cutE r a) hrE.le`. Establish `hU : IsUnit S.H` using `(Matrix.isUnit_iff_isUnit_det S.H).mpr hHdet`. Use `set E := S.cutE r a`. Use `set Pr := S.cutPr r a`. Use `set A := S.gaMat r a`.

Establish `hAE : A * E = E` using `by rw [hD, ← Matrix.mul_assoc, hAA]`. Establish `hEH : Eᴴ * S.H = Eᴴ * S.H * (E * Pr)`. Establish `h'` using `hO`. Rewrite `h'` using `[Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]`. Conclude with `h'`.

Use `symm`. Apply `hU.mul_left_cancel` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cutOrthProj_of (h1 : ImESpec) (h2 : GaMatHom) (h3 : GaMatAdj) : CutOrthProj := by
  intro K _ _ _ v0 hv S hpos G _ _ r hr a hidem hself
  obtain ⟨hinj, hrange⟩ := h1 K S.dim (S.gaMat r a)
  obtain ⟨-, hHdet, -, hOP, -⟩ := orthogonal_projection_exists K v0 hv S.dim _ S.H hpos (S.cutE r a) hinj
  have hOP' : IsOrthProj S.H (S.cutE r a) (S.cutPr r a) := hOP
  refine ⟨hOP', ?_⟩
  obtain ⟨-, hO⟩ := hOP'
  have hAA : S.gaMat r a * S.gaMat r a = S.gaMat r a := by rw [← (h2 K S G r).2, hidem]
  have hadj : (S.gaMat r a)ᴴ * S.H = S.H * S.gaMat r a := by rw [h3 K S G r hr a, hself]
  have hrE : LinearMap.range (S.cutE r a).mulVecLin = LinearMap.range (S.gaMat r a).mulVecLin := hrange
  obtain ⟨C, hC⟩ := exists_mul_of_range_le (A := S.cutE r a) (B := S.gaMat r a) hrE.ge
  obtain ⟨D, hD⟩ := exists_mul_of_range_le (A := S.gaMat r a) (B := S.cutE r a) hrE.le
  have hU : IsUnit S.H := (Matrix.isUnit_iff_isUnit_det S.H).mpr hHdet
  set E := S.cutE r a
  set Pr := S.cutPr r a
  set A := S.gaMat r a
  have hAE : A * E = E := by rw [hD, ← Matrix.mul_assoc, hAA]
  have hEH : Eᴴ * S.H = Eᴴ * S.H * (E * Pr) := by
    have h' := hO
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h'
    exact h'
  symm
  apply hU.mul_left_cancel
  calc S.H * A = Aᴴ * S.H := hadj.symm
    _ = Cᴴ * (Eᴴ * S.H) := by rw [hC, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Cᴴ * (Eᴴ * S.H * (E * Pr)) := by rw [← hEH]
    _ = Aᴴ * S.H * (E * Pr) := by rw [hC, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = S.H * (A * (E * Pr)) := by rw [hadj, Matrix.mul_assoc]
    _ = S.H * (E * Pr) := by rw [← Matrix.mul_assoc A, hAE]

/- English proof (translation)
Introduce `K _ _ _ v0 hv S hpos G _ _ r hr X hX P ψ`. Establish `hP` using `h2 K v0 hv G X hX P ψ`. Take `⟨hO, hEP⟩` from `h1 K v0 hv S hpos G r hr (goodAt X P ψ) hP.idem hP.selfAdj`. Conclude with `⟨hO, hEP, hP.integral, fun t x hx => (h3 K S G r hr t).2 x hx⟩`.
-/
theorem boundsIHyps_of (h1 : CutOrthProj) (h2 : GoodAtSpec) (h3 : ActLat) : BoundsIHyps := by
  intro K _ _ _ v0 hv S hpos G _ _ r hr X hX P ψ
  have hP := h2 K v0 hv G X hX P ψ
  obtain ⟨hO, hEP⟩ := h1 K v0 hv S hpos G r hr (goodAt X P ψ) hP.idem hP.selfAdj
  exact ⟨hO, hEP, hP.integral, fun t x hx => (h3 K S G r hr t).2 x hx⟩

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.dual Formalism.E.hdual`. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]`.
-/
theorem mem_dual_iff {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}
    (h : (Fin n → K) →ₗ⋆[K] (Fin n → K) →ₗ[K] K) (L : Submodule (𝓞 K) (Fin n → K)) (x : Fin n → K) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 K) K) := by
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]

/- English proof (translation)
Unfold `hform`. Rewrite using `[Matrix.toLinearMapₛₗ₂'_apply]`. Simplify using `only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply, RingHom.id_apply, mul_assoc]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem hform_eq_lemma {K : Type} [Field K] [NumberField K] [StarRing K] {m : ℕ} (M : Matrix (Fin m) (Fin m) K)
    (u v : Fin m → K) : hform M u v = star u ⬝ᵥ (M *ᵥ v) := by
  unfold hform
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply, RingHom.id_apply,
    mul_assoc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [smul_eq_mul]
  ring

/- English proof (translation)
Rewrite using `[hform_eq_lemma, hform_eq_lemma, Matrix.mulVec_smul]`. Use `congr 1`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`.
-/
theorem hform_smul {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (c : K)
    (H : Matrix (Fin n) (Fin n) K) (y x : Fin n → K) : hform (c • H) y x = hform H y (c • x) := by
  rw [hform_eq_lemma, hform_eq_lemma, Matrix.mulVec_smul]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Introduce `K _ _ _ v0 hv0 S s hS hpos G _ _ r hr X hX P ψ`. Take `⟨hp, he, hint, hdel⟩` from `h K v0 hv0 S hpos G r hr X hX P ψ`. Take `⟨hH, hdet, -⟩` from `orthogonal_projection_exists K v0 hv0 S.dim 0 S.H hpos 0 (by intro x y _; exact Subsingleton.elim _ _)`. Take `⟨hl1, hl2, hl3⟩` from `bounds_class_field_fixed K S.dim (S.BaseDimension r X P ψ) S.H hH hdet (S.V0E r X P ψ) (S.goodPartProjection r X P ψ) hp S.Cl S.V S.pair hS.symm hS.nondeg S.Gam S.ρ hS.inv S.I S.I_injective S.I_onto S.isClassSum S.Nab S.Del hS.nab_lat s hS.dual_le hS.del_le hS.del_stable G (S.act …`. Use `⟨hl1, hl2, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Establish `hP : (Nat.card P : K) ≠ 0` using `by exact_mod_cast (Nat.card_pos (α := P)).ne'`. Establish `hx' : ((Nat.card P : K)⁻¹ • x) ∈ Formalism.HermitianLatticesTheory.dual (hform ((S.V0E r X P ψ)ᴴ * S.H * S.V0E r X P ψ)) (cutLat (S.V0E r X P ψ) (valLatF S.I S.Nab))`. Rewrite using `[mem_dual_iff]`. Introduce `y hy`.

Use `(mem_dual_iff _ _ _).1 hx y hy` as an intermediate fact. Rewrite `this` using `[CSD.goodPartHermitianForm, hform_smul]`. Then use the resulting hypothesis. Establish `h4` using `hl3 _ hx'`. Establish `e : ((Fintype.card G * Nat.card P * s : ℕ) : 𝓞 K) • ((Nat.card P : K)⁻¹ • x) = ((Fintype.card G * s : ℕ) : 𝓞 K) • x`. Rewrite using `[← algebraMap_smul K, ← algebraMap_smul K (((Fintype.card G * s : ℕ) : 𝓞 K)), smul_smul]`.

Use `congr 1`. Simplify using `only [map_natCast, map_mul, Nat.cast_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite `h4` using `[e]`. Conclude with `h4`.
-/
theorem boundsIAt_of (h : BoundsIHyps) : BoundsIAt := by
  intro K _ _ _ v0 hv0 S s hS hpos G _ _ r hr X hX P ψ
  obtain ⟨hp, he, hint, hdel⟩ := h K v0 hv0 S hpos G r hr X hX P ψ
  obtain ⟨hH, hdet, -⟩ := orthogonal_projection_exists K v0 hv0 S.dim 0 S.H hpos 0
    (by intro x y _; exact Subsingleton.elim _ _)
  obtain ⟨hl1, hl2, hl3⟩ := bounds_class_field_fixed K S.dim (S.BaseDimension r X P ψ) S.H hH hdet (S.V0E r X P ψ)
    (S.goodPartProjection r X P ψ) hp S.Cl S.V S.pair hS.symm hS.nondeg S.Gam S.ρ hS.inv S.I S.I_injective S.I_onto
    S.isClassSum S.Nab S.Del hS.nab_lat s hS.dual_le hS.del_le hS.del_stable G (S.actMat r)
    (fun t => (goodAt X P ψ).coeff t) (Fintype.card G * Nat.card P) he hint hdel
  refine ⟨hl1, hl2, ?_⟩
  intro x hx
  have hP : (Nat.card P : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := P)).ne'
  have hx' : ((Nat.card P : K)⁻¹ • x) ∈
      Formalism.HermitianLatticesTheory.dual (hform ((S.V0E r X P ψ)ᴴ * S.H * S.V0E r X P ψ)) (cutLat (S.V0E r X P ψ) (valLatF S.I S.Nab)) := by
    rw [mem_dual_iff]
    intro y hy
    have := (mem_dual_iff _ _ _).1 hx y hy
    rwa [CSD.goodPartHermitianForm, hform_smul] at this
  have h4 := hl3 _ hx'
  have e : ((Fintype.card G * Nat.card P * s : ℕ) : 𝓞 K) • ((Nat.card P : K)⁻¹ • x) =
      ((Fintype.card G * s : ℕ) : 𝓞 K) • x := by
    rw [← algebraMap_smul K, ← algebraMap_smul K (((Fintype.card G * s : ℕ) : 𝓞 K)), smul_smul]
    congr 1
    simp only [map_natCast, map_mul, Nat.cast_mul]
    field_simp
  rw [e] at h4
  exact h4

/- English proof (translation)
Introduce `K _ _ _ v0 hv0 S s hS hpos G _ _ r hr P ψ y hy`. Take `⟨hg, -⟩` from `h2 K v0 hv0 G P ψ`. Take `⟨hp, he⟩` from `h1 K v0 hv0 S hpos G r hr (lvlIdem P ψ) hg.idem hg.selfAdj`. Take `⟨hH, hdet, -⟩` from `orthogonal_projection_exists K v0 hv0 S.dim 0 S.H hpos 0 (by intro x y _; exact Subsingleton.elim _ _)`. Establish `hA : Submodule.IsLattice K S.nabLat` using `ValuationLatticeField.valLatF_isLattice S.I S.I_injective S.Nab hS.nab_lat`.

Establish `hP : (Nat.card P : K) ≠ 0` using `by exact_mod_cast (Nat.card_pos (α := P)).ne'`. Establish `hy' : ((Nat.card P : K)⁻¹ • y) ∈ Formalism.HermitianLatticesTheory.dual (hform ((S.cutE r (lvlIdem P ψ))ᴴ * S.H * S.cutE r (lvlIdem P ψ))) (cutLat (S.cutE r (lvlIdem P ψ)) S.nabLat)`. Rewrite using `[mem_dual_iff]`. Introduce `z hz`. Use `(mem_dual_iff _ _ _).1 hy z hz` as an intermediate fact.

Rewrite `this` using `[CSD.lvlH, hform_smul]`. Then use the resulting hypothesis. Rewrite `hy'` using `[sectioned_dual_lattice K S.dim _ S.H hH hdet _ _ hp S.nabLat hA]`. Take `⟨z, hz, hzy⟩` from `hy'`. Establish `hz' : (s : 𝓞 K) • z ∈ S.delLat` using `class_sum_dual_le_fixed K S.dim S.H S.Cl S.V S.pair hS.symm hS.nondeg S.Gam S.ρ hS.inv S.I S.I_onto S.isClassSum S.Nab S.Del hS.nab_lat s hS.dual_le hS.del_stable z hz`. Establish `h5` using `projection_integral K S.dim G (S.actMat r) (fun t => (lvlIdem P ψ).coeff t) (Nat.card P) hg.integral S.delLat (fun t => (h3 K S G r hr t).2) _ hz'`.

Use `show (S.cutE r (lvlIdem P ψ)).mulVec ((s : 𝓞 K) • y) ∈ S.delLat`. Establish `e : (S.cutE r (lvlIdem P ψ)).mulVec ((s : 𝓞 K) • y) = (Nat.card P : 𝓞 K) • (∑ t, (lvlIdem P ψ).coeff t • S.actMat r t).mulVec ((s : 𝓞 K) • z)`. Establish `e1 : (∑ t, (lvlIdem P ψ).coeff t • S.actMat r t) = S.cutE r (lvlIdem P ψ) * S.cutPr r (lvlIdem P ψ)` using `he.symm`. Establish `e2 : y = (Nat.card P : K) • (S.cutPr r (lvlIdem P ψ)).mulVec z`. Establish `: (S.cutPr r (lvlIdem P ψ)).mulVec z = (Nat.card P : K)⁻¹ • y` using `hzy`.

Rewrite using `[this, smul_smul, mul_inv_cancel₀ hP, one_smul]`. Rewrite using `[e1, ← Matrix.mulVec_mulVec]`. Use `conv_lhs => rw [e2]`. Simplify using `only [← algebraMap_smul K ((s : 𝓞 K)), ← algebraMap_smul K ((Nat.card P : 𝓞 K)), map_natCast, Matrix.mulVec_smul]`. Rewrite using `[smul_comm]`.

Rewrite using `[e]`. Conclude with `h5`.
-/
theorem lvlDualLe_of (h1 : CutOrthProj) (h2 : LvlIdemSpec) (h3 : ActLat) : LvlDualLe := by
  intro K _ _ _ v0 hv0 S s hS hpos G _ _ r hr P ψ y hy
  obtain ⟨hg, -⟩ := h2 K v0 hv0 G P ψ
  obtain ⟨hp, he⟩ := h1 K v0 hv0 S hpos G r hr (lvlIdem P ψ) hg.idem hg.selfAdj
  obtain ⟨hH, hdet, -⟩ := orthogonal_projection_exists K v0 hv0 S.dim 0 S.H hpos 0
    (by intro x y _; exact Subsingleton.elim _ _)
  have hA : Submodule.IsLattice K S.nabLat := ValuationLatticeField.valLatF_isLattice S.I S.I_injective S.Nab hS.nab_lat
  have hP : (Nat.card P : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := P)).ne'
  have hy' : ((Nat.card P : K)⁻¹ • y) ∈
      Formalism.HermitianLatticesTheory.dual (hform ((S.cutE r (lvlIdem P ψ))ᴴ * S.H * S.cutE r (lvlIdem P ψ)))
        (cutLat (S.cutE r (lvlIdem P ψ)) S.nabLat) := by
    rw [mem_dual_iff]
    intro z hz
    have := (mem_dual_iff _ _ _).1 hy z hz
    rwa [CSD.lvlH, hform_smul] at this
  rw [sectioned_dual_lattice K S.dim _ S.H hH hdet _ _ hp S.nabLat hA] at hy'
  obtain ⟨z, hz, hzy⟩ := hy'
  have hz' : (s : 𝓞 K) • z ∈ S.delLat :=
    class_sum_dual_le_fixed K S.dim S.H S.Cl S.V S.pair hS.symm hS.nondeg S.Gam S.ρ hS.inv S.I S.I_onto
      S.isClassSum S.Nab S.Del hS.nab_lat s hS.dual_le hS.del_stable z hz
  have h5 := projection_integral K S.dim G (S.actMat r) (fun t => (lvlIdem P ψ).coeff t) (Nat.card P)
    hg.integral S.delLat (fun t => (h3 K S G r hr t).2) _ hz'
  show (S.cutE r (lvlIdem P ψ)).mulVec ((s : 𝓞 K) • y) ∈ S.delLat
  have e : (S.cutE r (lvlIdem P ψ)).mulVec ((s : 𝓞 K) • y) =
      (Nat.card P : 𝓞 K) • (∑ t, (lvlIdem P ψ).coeff t • S.actMat r t).mulVec ((s : 𝓞 K) • z) := by
    have e1 : (∑ t, (lvlIdem P ψ).coeff t • S.actMat r t) = S.cutE r (lvlIdem P ψ) * S.cutPr r (lvlIdem P ψ) :=
      he.symm
    have e2 : y = (Nat.card P : K) • (S.cutPr r (lvlIdem P ψ)).mulVec z := by
      have : (S.cutPr r (lvlIdem P ψ)).mulVec z = (Nat.card P : K)⁻¹ • y := hzy
      rw [this, smul_smul, mul_inv_cancel₀ hP, one_smul]
    rw [e1, ← Matrix.mulVec_mulVec]
    conv_lhs => rw [e2]
    simp only [← algebraMap_smul K ((s : 𝓞 K)), ← algebraMap_smul K ((Nat.card P : 𝓞 K)), map_natCast,
      Matrix.mulVec_smul]
    rw [smul_comm]
  rw [e]
  exact h5

/- English proof (translation)
Rewrite using `[hform_eq_lemma, hform_eq_lemma, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]`.
-/
theorem hform_cut {K : Type} [Field K] [NumberField K] [StarRing K] {n d : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin d) K) (x y : Fin d → K) :
    hform (Eᴴ * H * E) x y = hform H (E.mulVec x) (E.mulVec y) := by
  rw [hform_eq_lemma, hform_eq_lemma, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.star_mulVec]

/- English proof (translation)
Introduce `K _ _ _ S G _ _ r P ψ`. Establish `hEinj : Function.Injective (S.lvlE r P ψ).mulVec` using `(h1 K S.dim (S.gaMat r (lvlIdem P ψ))).1`. Establish `hIinj : Function.Injective S.I`. Introduce `x y hxy`. Establish `h' : (S.basis.equivFun.symm x : S.Forms) = S.basis.equivFun.symm y` using `Subtype.ext hxy`.

Conclude with `S.basis.equivFun.symm.injective h'`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y hxy`. Conclude with `hEinj (hIinj hxy)`. Introduce `x y`.

Unfold `CSD.lvlH CSD.cutH`. Rewrite using `[hform_smul, hform_cut, hform_eq_lemma, CSD.dot_H_lemma, Matrix.mulVec_smul, map_smul]`. Unfold `CSD.csum`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, map_smul, smul_eq_mul, Nat.cast_mul, mul_inv]`.

Put the polynomial expressions in normal form. Both sides reduce to the same expression. Use `first`. Consider the case `rfl`. Consider the case `(ext x; exact Iff.rfl)`.

Use `first`. Consider the case `rfl`. Consider the case `(ext x; exact Iff.rfl)`.
-/
theorem lvlClassSum_of (h1 : ImESpec) : LvlClassSum := by
  intro K _ _ _ S G _ _ r P ψ
  have hEinj : Function.Injective (S.lvlE r P ψ).mulVec := (h1 K S.dim (S.gaMat r (lvlIdem P ψ))).1
  have hIinj : Function.Injective S.I := by
    intro x y hxy
    have h' : (S.basis.equivFun.symm x : S.Forms) = S.basis.equivFun.symm y := Subtype.ext hxy
    exact S.basis.equivFun.symm.injective h'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    exact hEinj (hIinj hxy)
  · intro x y
    unfold CSD.lvlH CSD.cutH
    rw [hform_smul, hform_cut, hform_eq_lemma, CSD.dot_H_lemma, Matrix.mulVec_smul, map_smul]
    unfold CSD.csum
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Pi.smul_apply, map_smul, smul_eq_mul, Nat.cast_mul, mul_inv]
    ring_nf
    rfl
  · first
    | rfl
    | (ext x; exact Iff.rfl)
  · first
    | rfl
    | (ext x; exact Iff.rfl)

/- English proof (translation)
Introduce `K _ _ G _ _ X hX`. Conclude with `⟨idemOf_mul_self X hX, idemOf_central X hX⟩`.
-/
theorem idempotent_central : IdemOfCentral := by
  intro K _ _ G _ _ X hX
  exact ⟨idemOf_mul_self X hX, idemOf_central X hX⟩

/- English proof (translation)
Conclude with `cutOrthProj_of image_idempotent_spec group_action_matrix_hom group_action_matrix_adjoint`.
-/
theorem orthogonal_projection_spec : CutOrthProj := by
  exact cutOrthProj_of image_idempotent_spec group_action_matrix_hom group_action_matrix_adjoint

/- English proof (translation)
Conclude with `good_part_spec_of_central idempotent_central`.
-/
theorem good_part_spec : GoodPartSpec := by
  exact good_part_spec_of_central idempotent_central

/- English proof (translation)
Conclude with `good_part_hermitian_of_spec good_at_spec`.
-/
theorem good_part_hermitian_spec : GoodPartHermitianSpec := by
  exact good_part_hermitian_of_spec good_at_spec

/- English proof (translation)
Conclude with `lvlClassSum_of image_idempotent_spec`.
-/
theorem level_class_sum : LvlClassSum := by
  exact lvlClassSum_of image_idempotent_spec

/- English proof (translation)
Conclude with `lvlOpSpec_of orthogonal_projection_spec level_idempotent_spec`.
-/
theorem level_operator_spec : LvlOpSpec := by
  exact lvlOpSpec_of orthogonal_projection_spec level_idempotent_spec

/- English proof (translation)
Conclude with `lvlDualLe_of orthogonal_projection_spec level_idempotent_spec action_preserves_lattice`.
-/
theorem level_dual_lattice_le : LvlDualLe := by
  exact lvlDualLe_of orthogonal_projection_spec level_idempotent_spec action_preserves_lattice

/- English proof (translation)
Conclude with `boundsIHyps_of orthogonal_projection_spec good_at_spec action_preserves_lattice`.
-/
theorem level_operator_integral : BoundsIHyps := by
  exact boundsIHyps_of orthogonal_projection_spec good_at_spec action_preserves_lattice

/- English proof (translation)
Conclude with `boundsIAt_of level_operator_integral`.
-/
theorem local_bounds_first : BoundsIAt := by
  exact boundsIAt_of level_operator_integral

end Formalism.L2.DIV

namespace Formalism.L2.DIV.Test

open Formalism.DivisionValues

variable (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]

def stdPair : K →ₗ⋆[K] K →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => star x * y)
    (by intro x y z; simp [add_mul])
    (by intro a x y; simp only [smul_eq_mul, star_mul', starRingEnd_apply, mul_assoc])
    (by intro x y z; simp [mul_add])
    (by intro a x y; simp [mul_left_comm])

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem stdPair_apply (x y : K) : stdPair K x y = star x * y := rfl

abbrev regCSD : CSD K where
  Cl := G
  V := K
  ιV := Unit
  bV := Basis.singleton Unit K
  pair := stdPair K
  Gam := fun _ => Unit
  ρ := fun _ => 1
  Nab := fun _ => 1
  Del := fun _ => 1

/- English proof (translation)
Introduce `c γ`. Both sides reduce to the same expression.
-/
theorem mem_regForms (f : G → K) : f ∈ (regCSD K G).Forms := by
  intro c γ
  rfl

def regAct : Representation K G (regCSD K G).Forms where
  toFun t := LinearMap.codRestrict _
    ((LinearMap.funLeft K K (fun c : G => c * t)) ∘ₗ (regCSD K G).Forms.subtype)
    (fun f => mem_regForms K G _)
  map_one' := by
    apply LinearMap.ext; intro f; apply Subtype.ext; funext c
    exact congrArg f.1 (mul_one (c : G))
  map_mul' := by
    intro s t
    apply LinearMap.ext; intro f; apply Subtype.ext; funext c
    exact congrArg f.1 (mul_assoc (c : G) s t).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem regAct_apply (t : G) (f : (regCSD K G).Forms) (c : G) :
    ((regAct K G t f).1 : G → K) c = (f.1 : G → K) (c * t) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem reg_wt (c : G) : (regCSD K G).wt c = 1 := rfl

/- English proof (translation)
Unfold `CSD.csum`. Simplify using `only [reg_wt, Nat.cast_one, inv_one, one_mul]`. Both sides reduce to the same expression.
-/
theorem reg_csum (f g : G → K) : (regCSD K G).csum f g = ∑ c : G, star (f c) * g c := by
  unfold CSD.csum
  simp only [reg_wt, Nat.cast_one, inv_one, one_mul]
  rfl

/- English proof (translation)
Introduce `t f g`. Rewrite using `[reg_csum, reg_csum]`. Conclude with `Equiv.sum_comp (Equiv.mulRight t) (fun c : G => star ((f.1 : G → K) c) * (g.1 : G → K) c)`. Use `nab_stable := by`. Introduce `t f hf c`.

Conclude with `hf ((c : G) * t)`. Use `del_stable := by`. Introduce `t f hf c`. Conclude with `hf ((c : G) * t)`.
-/
theorem regAct_good : (regCSD K G).ActGood (regAct K G) where
  unitary := by
    intro t f g
    rw [reg_csum, reg_csum]
    exact Equiv.sum_comp (Equiv.mulRight t) (fun c : G => star ((f.1 : G → K) c) * (g.1 : G → K) c)
  nab_stable := by
    intro t f hf c
    exact hf ((c : G) * t)
  del_stable := by
    intro t f hf c
    exact hf ((c : G) * t)

/- English proof (translation)
Use `⟨1, 1, ?_, ?_⟩` and prove the remaining obligations. Establish `hs : IsSimpleOrder (Submodule (AlgebraicClosure K) (Fin 1 → AlgebraicClosure K))`. Establish `: IsSimpleModule (AlgebraicClosure K) (Fin 1 → AlgebraicClosure K)` using `isSimpleModule_iff_finrank_eq_one.mpr (by simp)`. Conclude with `this.1`. Establish `: Nontrivial (Subrepresentation (1 : Representation (AlgebraicClosure K) G (Fin 1 → AlgebraicClosure K)))` using `⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩`.

Use `⟨fun σ => ?_⟩` and prove the remaining obligations. Break down `hs.eq_bot_or_eq_top σ.toSubmodule with h | h` into its components or cases. Conclude with `Or.inl (Subrepresentation.toSubmodule_injective h)`. Conclude with `Or.inr (Subrepresentation.toSubmodule_injective h)`. Introduce `t`.

Simplify using `[Representation.character]`.
-/
theorem isAbsIrrChar_one : IsAbsIrrChar (fun _ : G => (1 : K)) := by
  refine ⟨1, 1, ?_, ?_⟩
  · have hs : IsSimpleOrder (Submodule (AlgebraicClosure K) (Fin 1 → AlgebraicClosure K)) := by
      have : IsSimpleModule (AlgebraicClosure K) (Fin 1 → AlgebraicClosure K) :=
        isSimpleModule_iff_finrank_eq_one.mpr (by simp)
      exact this.1
    have : Nontrivial (Subrepresentation (1 : Representation (AlgebraicClosure K) G
        (Fin 1 → AlgebraicClosure K))) :=
      ⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩
    refine ⟨fun σ => ?_⟩
    rcases hs.eq_bot_or_eq_top σ.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)
  · intro t
    simp [Representation.character]

/- English proof (translation)
Rewrite using `[coeff_idemOf, Finset.sum_singleton]`. Simplify using the standard rewrite rules.
-/
theorem idemOf_one_coeff (t : G) :
    (idemOf ({fun _ : G => (1 : K)} : Finset (G → K))).coeff t = 1 / (Fintype.card G : K) := by
  rw [coeff_idemOf, Finset.sum_singleton]
  simp

/- English proof (translation)
Conclude with `level_idempotent_bot K G ψ`.
-/
theorem lvlIdem_bot (ψ : (⊥ : Subgroup G) →* Kˣ) : lvlIdem (⊥ : Subgroup G) ψ = 1 := by
  exact level_idempotent_bot K G ψ

/- English proof (translation)
Set `f1 : (regCSD K G).Forms` to `⟨fun _ => (1 : K), mem_regForms K G _⟩`. Establish `hfix : ∀ t : G, regAct K G t f1 = f1` using `fun t => rfl`. Establish `hact : ∀ t : G, ((regCSD K G).actMat (regAct K G) t).mulVec ((regCSD K G).basis.equivFun f1) = (regCSD K G).basis.equivFun f1`. Introduce `t`. Establish `h1` using `(regCSD K G).I_actMat (regAct K G) t ((regCSD K G).basis.equivFun f1)`.

Rewrite `h1` using `[LinearEquiv.symm_apply_apply, hfix]`. Establish `h3 : (regCSD K G).basis.equivFun.symm (((regCSD K G).actMat (regAct K G) t).mulVec ((regCSD K G).basis.equivFun f1)) = f1` using `Subtype.ext h1`. Establish `h4` using `congrArg (regCSD K G).basis.equivFun h3`. Rewrite `h4` using `[LinearEquiv.apply_symm_apply]`. Then use the resulting hypothesis. Establish `hsm : ∀ (c : K) (M : Matrix (Fin (regCSD K G).dim) (Fin (regCSD K G).dim) K) (v : Fin (regCSD K G).dim → K), (c • M).mulVec v = c • M.mulVec v`.

Introduce `c M v`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`. Establish `hsum : ∀ (s : Finset G) (M : G → Matrix (Fin (regCSD K G).dim) (Fin (regCSD K G).dim) K) (v : Fin (regCSD K G).dim → K), (∑ t ∈ s, M t).mulVec v = ∑ t ∈ s, (M t).mulVec v`. Introduce `s M v`.

Proceed by induction on `s using Finset.cons_induction with`. Consider the case `empty => simp`. Consider the case `cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, Matrix.add_mulVec, ih]`. Establish `hga : ((regCSD K G).gaMat (regAct K G) (goodAt X P ψ)).mulVec ((regCSD K G).basis.equivFun f1) = (∑ t : G, (goodAt X P ψ).coeff t) • (regCSD K G).basis.equivFun f1`. Unfold `CSD.gaMat`.

Rewrite using `[hsum, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[hsm, hact t]`. Establish `hx1 : (regCSD K G).basis.equivFun f1 ≠ 0`. Introduce `h0`.

Establish `h5 : f1 = 0` using `(regCSD K G).basis.equivFun.injective (by rw [h0, map_zero])`. Establish `h6` using `congrArg (fun f : (regCSD K G).Forms => (f : G → K) 1) h5`. Simplify using `[f1] at h6`. Use `show 0 < Module.finrank K (LinearMap.range ((regCSD K G).gaMat (regAct K G) (goodAt X P ψ)).mulVecLin)`. Apply `Module.finrank_pos_iff_exists_ne_zero.mpr` to reduce the goal to its premises.

Use `⟨⟨(∑ t : G, (goodAt X P ψ).coeff t) • (regCSD K G).basis.equivFun f1, LinearMap.mem_range.mpr ⟨(regCSD K G).basis.equivFun f1, by rw [Matrix.mulVecLin_apply, hga]⟩⟩, ?_⟩` and prove the remaining obligations. Introduce `h0`. Establish `h7` using `congrArg Subtype.val h0`. Conclude with `smul_ne_zero h hx1 h7`.
-/
private theorem v0dim_pos_lemma (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G]
    [Fintype G] (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ)
    (h : ∑ t : G, (goodAt X P ψ).coeff t ≠ 0) : 0 < (regCSD K G).BaseDimension (regAct K G) X P ψ := by
  let f1 : (regCSD K G).Forms := ⟨fun _ => (1 : K), mem_regForms K G _⟩
  have hfix : ∀ t : G, regAct K G t f1 = f1 := fun t => rfl
  have hact : ∀ t : G, ((regCSD K G).actMat (regAct K G) t).mulVec ((regCSD K G).basis.equivFun f1) =
      (regCSD K G).basis.equivFun f1 := by
    intro t
    have h1 := (regCSD K G).I_actMat (regAct K G) t ((regCSD K G).basis.equivFun f1)
    rw [LinearEquiv.symm_apply_apply, hfix] at h1
    have h3 : (regCSD K G).basis.equivFun.symm (((regCSD K G).actMat (regAct K G) t).mulVec
        ((regCSD K G).basis.equivFun f1)) = f1 := Subtype.ext h1
    have h4 := congrArg (regCSD K G).basis.equivFun h3
    rwa [LinearEquiv.apply_symm_apply] at h4
  have hsm : ∀ (c : K) (M : Matrix (Fin (regCSD K G).dim) (Fin (regCSD K G).dim) K)
      (v : Fin (regCSD K G).dim → K), (c • M).mulVec v = c • M.mulVec v := by
    intro c M v
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  have hsum : ∀ (s : Finset G) (M : G → Matrix (Fin (regCSD K G).dim) (Fin (regCSD K G).dim) K)
      (v : Fin (regCSD K G).dim → K), (∑ t ∈ s, M t).mulVec v = ∑ t ∈ s, (M t).mulVec v := by
    intro s M v
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, Matrix.add_mulVec, ih]
  have hga : ((regCSD K G).gaMat (regAct K G) (goodAt X P ψ)).mulVec ((regCSD K G).basis.equivFun f1) =
      (∑ t : G, (goodAt X P ψ).coeff t) • (regCSD K G).basis.equivFun f1 := by
    unfold CSD.gaMat
    rw [hsum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hsm, hact t]
  have hx1 : (regCSD K G).basis.equivFun f1 ≠ 0 := by
    intro h0
    have h5 : f1 = 0 := (regCSD K G).basis.equivFun.injective (by rw [h0, map_zero])
    have h6 := congrArg (fun f : (regCSD K G).Forms => (f : G → K) 1) h5
    simp [f1] at h6
  show 0 < Module.finrank K (LinearMap.range ((regCSD K G).gaMat (regAct K G) (goodAt X P ψ)).mulVecLin)
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨(∑ t : G, (goodAt X P ψ).coeff t) • (regCSD K G).basis.equivFun f1,
    LinearMap.mem_range.mpr ⟨(regCSD K G).basis.equivFun f1, by rw [Matrix.mulVecLin_apply, hga]⟩⟩, ?_⟩
  intro h0
  have h7 := congrArg Subtype.val h0
  exact smul_ne_zero h hx1 h7

/- English proof (translation)
Apply `v0dim_pos_lemma` to reduce the goal to its premises. Unfold `goodAt`. Rewrite using `[lvlIdem_bot, mul_one]`. Simplify using `only [idemOf_one_coeff, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Rewrite using `[one_div, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]`.

Conclude with `one_ne_zero`.
-/
theorem reg_V0dim_pos (ψ : (⊥ : Subgroup G) →* Kˣ) :
    0 < (regCSD K G).BaseDimension (regAct K G) ({fun _ : G => (1 : K)} : Finset (G → K)) ⊥ ψ := by
  apply v0dim_pos_lemma
  unfold goodAt
  rw [lvlIdem_bot, mul_one]
  simp only [idemOf_one_coeff, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [one_div, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  exact one_ne_zero

/- English proof (translation)
Establish `key : y ∈ Formalism.HermitianLatticesTheory.dual (stdPair K) (1 : Submodule (𝓞 K) K) ↔ ∀ z ∈ (1 : Submodule (𝓞 K) K), stdPair K z y ∈ (1 : Submodule (𝓞 K) K)`. Unfold `Formalism.HermitianLatticesTheory.dual Formalism.E.hdual`. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]`. Rewrite using `[key]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h1` using `h 1 (by rw [Submodule.mem_one]; exact ⟨1, map_one _⟩)`. Rewrite `h1` using `[stdPair_apply, star_one, one_mul]`. Then use the resulting hypothesis. Introduce `hy z hz`. Rewrite using `[stdPair_apply]`.

Rewrite `hy`, `hz`, the goal using `[Submodule.mem_one]`. Take `⟨a, rfl⟩` from `hz`. Take `⟨b, rfl⟩` from `hy`. Establish `ha : IsIntegral ℤ (algebraMap (𝓞 K) K a)` using `(int_iff_lemma _).mp ⟨a, rfl⟩`. Establish `hb : IsIntegral ℤ (algebraMap (𝓞 K) K b)` using `(int_iff_lemma _).mp ⟨b, rfl⟩`.

Establish `hs : IsIntegral ℤ (star (algebraMap (𝓞 K) K a))` using `ha.map (starRingEnd K).toIntAlgHom`. Take `⟨c, hc⟩` from `(int_iff_lemma _).mpr (hs.mul hb)`. Conclude with `⟨c, hc⟩`.
-/
theorem mem_dual_one (y : K) :
    y ∈ Formalism.HermitianLatticesTheory.dual (stdPair K) (1 : Submodule (𝓞 K) K) ↔ y ∈ (1 : Submodule (𝓞 K) K) := by
  have key : y ∈ Formalism.HermitianLatticesTheory.dual (stdPair K) (1 : Submodule (𝓞 K) K) ↔
      ∀ z ∈ (1 : Submodule (𝓞 K) K), stdPair K z y ∈ (1 : Submodule (𝓞 K) K) := by
    unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
  rw [key]
  constructor
  · intro h
    have h1 := h 1 (by rw [Submodule.mem_one]; exact ⟨1, map_one _⟩)
    rwa [stdPair_apply, star_one, one_mul] at h1
  · intro hy z hz
    rw [stdPair_apply]
    rw [Submodule.mem_one] at hy hz ⊢
    obtain ⟨a, rfl⟩ := hz
    obtain ⟨b, rfl⟩ := hy
    have ha : IsIntegral ℤ (algebraMap (𝓞 K) K a) := (int_iff_lemma _).mp ⟨a, rfl⟩
    have hb : IsIntegral ℤ (algebraMap (𝓞 K) K b) := (int_iff_lemma _).mp ⟨b, rfl⟩
    have hs : IsIntegral ℤ (star (algebraMap (𝓞 K) K a)) := ha.map (starRingEnd K).toIntAlgHom
    obtain ⟨c, hc⟩ := (int_iff_lemma _).mpr (hs.mul hb)
    exact ⟨c, hc⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun x y => by show starRingEnd K (star x * y) = star y * x rw [starRingEnd_apply, star_mul', star_star, mul_comm]⟩ nondeg := by constructor · intro x hx have := hx 1 simpa using this · intro y hy have := hy 1 simpa using this inv := fun c γ x y => rfl nab_lat := fun c => ⟨by sho …`.
-/
theorem reg_good : (regCSD K G).Good 1 where
  symm := ⟨fun x y => by
    show starRingEnd K (star x * y) = star y * x
    rw [starRingEnd_apply, star_mul', star_star, mul_comm]⟩
  nondeg := by
    constructor
    · intro x hx
      have := hx 1
      simpa using this
    · intro y hy
      have := hy 1
      simpa using this
  inv := fun c γ x y => rfl
  nab_lat := fun c => ⟨by
    show (1 : Submodule (𝓞 K) K).FG
    rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _, by
    show Submodule.span K (((1 : Submodule (𝓞 K) K) : Set K)) = ⊤
    rw [eq_top_iff]
    intro x _
    have h1 : (1 : K) ∈ Submodule.span K (((1 : Submodule (𝓞 K) K) : Set K)) :=
      Submodule.subset_span (Submodule.one_le.mp le_rfl)
    simpa using Submodule.smul_mem _ x h1⟩
  del_le := fun c => le_rfl
  del_stable := fun c γ y hy => hy
  s_pos := Nat.one_pos
  dual_le := fun c y hy => by
    rw [Nat.cast_one, one_smul]
    exact (mem_dual_one K y).mp hy
  del_dual := fun c y hy => by
    rw [Nat.cast_one, one_smul]
    exact (mem_dual_one K y).mpr hy

/- English proof (translation)
Set `B : Matrix G (Fin (regCSD K G).dim) K` to `Matrix.of fun c i => (((regCSD K G).basis i).1 : G → K) c`. Establish `hH : (regCSD K G).H = Bᴴ * B`. Use extensionality with `i j`. Simplify using `only [CSD.H, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]`. Conclude with `reg_csum K G _ _`.

Establish `hmap : (regCSD K G).H.map v0.embedding = (B.map v0.embedding)ᴴ * (B.map v0.embedding)`. Rewrite using `[hH, Matrix.map_mul, Matrix.conjTranspose_map (f := v0.embedding) (fun a => h0 a)]`. Establish `hBI : ∀ x, B.mulVec x = (regCSD K G).I x`. Introduce `x`. Rewrite using `[CSD.I_eq_sum]`.

Use function extensionality and compare the values at `c`. Simplify using `only [Matrix.mulVec, dotProduct, B, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Establish `hinj : Function.Injective (Matrix.toLin' B)`. Introduce `x y hxy`.

Rewrite `hxy` using `[Matrix.toLin'_apply, Matrix.toLin'_apply, hBI, hBI]`. Conclude with `(regCSD K G).I_injective hxy`. Take `⟨g, hg⟩` from `(Matrix.toLin' B).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)`. Establish `hC : LinearMap.toMatrix' g * B = 1`. Establish `h` using `congrArg LinearMap.toMatrix' hg`.

Rewrite `h` using `[LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id]`. Then use the resulting hypothesis. Establish `hC' : (LinearMap.toMatrix' g).map v0.embedding * B.map v0.embedding = 1`. Rewrite using `[← Matrix.map_mul, hC, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hinj' : Function.Injective (B.map v0.embedding).mulVec`. Introduce `x y hxy`.

Establish `h` using `congrArg ((LinearMap.toMatrix' g).map v0.embedding).mulVec hxy`. Simplify `h` using `only [Matrix.mulVec_mulVec, hC', Matrix.one_mulVec]`. Rewrite using `[hmap]`. Conclude with `Matrix.PosDef.conjTranspose_mul_self _ hinj'`.
-/
theorem reg_H_posDef (v0 : InfinitePlace K) (h0 : IsConjAt v0) :
    ((regCSD K G).H.map v0.embedding).PosDef := by
  classical
  let B : Matrix G (Fin (regCSD K G).dim) K :=
    Matrix.of fun c i => (((regCSD K G).basis i).1 : G → K) c
  have hH : (regCSD K G).H = Bᴴ * B := by
    ext i j
    simp only [CSD.H, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact reg_csum K G _ _
  have hmap : (regCSD K G).H.map v0.embedding = (B.map v0.embedding)ᴴ * (B.map v0.embedding) := by
    rw [hH, Matrix.map_mul, Matrix.conjTranspose_map (f := v0.embedding) (fun a => h0 a)]
  have hBI : ∀ x, B.mulVec x = (regCSD K G).I x := by
    intro x
    rw [CSD.I_eq_sum]
    funext c
    simp only [Matrix.mulVec, dotProduct, B, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hinj : Function.Injective (Matrix.toLin' B) := by
    intro x y hxy
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hBI, hBI] at hxy
    exact (regCSD K G).I_injective hxy
  obtain ⟨g, hg⟩ := (Matrix.toLin' B).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  have hC : LinearMap.toMatrix' g * B = 1 := by
    have h := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h
  have hC' : (LinearMap.toMatrix' g).map v0.embedding * B.map v0.embedding = 1 := by
    rw [← Matrix.map_mul, hC, Matrix.map_one _ (map_zero _) (map_one _)]
  have hinj' : Function.Injective (B.map v0.embedding).mulVec := by
    intro x y hxy
    have h := congrArg ((LinearMap.toMatrix' g).map v0.embedding).mulVec hxy
    simpa only [Matrix.mulVec_mulVec, hC', Matrix.one_mulVec] using h
  rw [hmap]
  exact Matrix.PosDef.conjTranspose_mul_self _ hinj'

def aug : MonoidAlgebra K G →ₐ[K] K := MonoidAlgebra.lift K K G (1 : G →* K)

/- English proof (translation)
Unfold `aug`. Rewrite using `[MonoidAlgebra.lift_apply, Finsupp.sum_fintype]`. Simplify using the standard rewrite rules. Use `intro`. Simplify using the standard rewrite rules.
-/
theorem aug_eq_sum (a : MonoidAlgebra K G) : aug K G a = ∑ t : G, a.coeff t := by
  unfold aug
  rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype]
  · simp
  · intro
    simp

/- English proof (translation)
Rewrite using `[aug_eq_sum]`. Simplify using `only [idemOf_one_coeff, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Rewrite using `[one_div, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]`.
-/
theorem aug_idemOf_one : aug K G (idemOf ({fun _ : G => (1 : K)} : Finset (G → K))) = 1 := by
  rw [aug_eq_sum]
  simp only [idemOf_one_coeff, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [one_div, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

/- English proof (translation)
Unfold `lvlIdem aug`. Rewrite using `[map_sum]`. Establish `e : ∀ h : P, (MonoidAlgebra.lift K K G (1 : G →* K)) (MonoidAlgebra.single (h : G) ((Nat.card P : K)⁻¹ * (((1 : P →* Kˣ) h⁻¹ : Kˣ) : K))) = (Nat.card P : K)⁻¹`. Introduce `h`. Rewrite using `[MonoidAlgebra.lift_single]`.

Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_congr rfl fun h _ => e h, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')]`.
-/
theorem aug_lvlIdem_one (P : Subgroup G) : aug K G (lvlIdem P (1 : P →* Kˣ)) = 1 := by
  classical
  unfold lvlIdem aug
  rw [map_sum]
  have e : ∀ h : P, (MonoidAlgebra.lift K K G (1 : G →* K)) (MonoidAlgebra.single (h : G)
      ((Nat.card P : K)⁻¹ * (((1 : P →* Kˣ) h⁻¹ : Kˣ) : K))) = (Nat.card P : K)⁻¹ := by
    intro h
    rw [MonoidAlgebra.lift_single]
    simp
  rw [Finset.sum_congr rfl fun h _ => e h, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    nsmul_eq_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')]

/- English proof (translation)
Apply `v0dim_pos_lemma` to reduce the goal to its premises. Rewrite using `[← aug_eq_sum]`. Unfold `goodAt`. Rewrite using `[map_mul, aug_idemOf_one, aug_lvlIdem_one, mul_one]`. Conclude with `one_ne_zero`.
-/
theorem reg_V0dim_pos_lvl (P : Subgroup G) :
    0 < (regCSD K G).BaseDimension (regAct K G) ({fun _ : G => (1 : K)} : Finset (G → K)) P 1 := by
  apply v0dim_pos_lemma
  rw [← aug_eq_sum]
  unfold goodAt
  rw [map_mul, aug_idemOf_one, aug_lvlIdem_one, mul_one]
  exact one_ne_zero

/- English proof (translation)
Introduce `a`. Rewrite using `[star_trivial, eq_ratCast v0.embedding a, map_ratCast]`.
-/
theorem rat_isConjAt (v0 : InfinitePlace ℚ) : IsConjAt v0 := by
  intro a
  rw [star_trivial, eq_ratCast v0.embedding a, map_ratCast]

/- English proof (translation)
Establish `v0 : InfinitePlace ℚ` using `by first`. Consider the case `exact Rat.infinitePlace`. Consider the case `exact Classical.choice inferInstance`. Conclude with `⟨v0, rat_isConjAt v0, reg_good ℚ _, reg_H_posDef ℚ _ v0 (rat_isConjAt v0), regAct_good ℚ _, fun χ hχ => (Finset.mem_singleton.mp hχ) ▸ isAbsIrrChar_one ℚ _, reg_V0dim_pos_lvl ℚ _ P⟩`.
-/
theorem hyps_sat (P : Subgroup (Equiv.Perm (Fin 3))) :
    ∃ v0 : InfinitePlace ℚ, IsConjAt v0 ∧
      (regCSD ℚ (Equiv.Perm (Fin 3))).Good 1 ∧
      ((regCSD ℚ (Equiv.Perm (Fin 3))).H.map v0.embedding).PosDef ∧
      (regCSD ℚ (Equiv.Perm (Fin 3))).ActGood (regAct ℚ (Equiv.Perm (Fin 3))) ∧
      (∀ χ ∈ ({fun _ => (1 : ℚ)} : Finset (Equiv.Perm (Fin 3) → ℚ)), IsAbsIrrChar χ) ∧
      0 < (regCSD ℚ (Equiv.Perm (Fin 3))).BaseDimension (regAct ℚ (Equiv.Perm (Fin 3)))
        ({fun _ => (1 : ℚ)} : Finset (Equiv.Perm (Fin 3) → ℚ)) P 1 := by
  have v0 : InfinitePlace ℚ := by
    first
    | exact Rat.infinitePlace
    | exact Classical.choice inferInstance
  exact ⟨v0, rat_isConjAt v0, reg_good ℚ _, reg_H_posDef ℚ _ v0 (rat_isConjAt v0), regAct_good ℚ _,
    fun χ hχ => (Finset.mem_singleton.mp hχ) ▸ isAbsIrrChar_one ℚ _, reg_V0dim_pos_lvl ℚ _ P⟩

end Formalism.L2.DIV.Test
