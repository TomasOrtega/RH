import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_id isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)

namespace GlobalTheory.LieComb

open GlobalTheory.SqZero

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {v : Fin n → (epsR R ⟶ G)}

/- English proof (translation)
The claim follows from `isLieComb_iff_lieExp c w`.
-/
theorem isLieComb_iff_tanExp (c : Fin n → R) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = tanExp v c := isLieComb_iff_lieExp c w

/- English proof (translation)
The claim follows from `(isTan_iff _).1 (isTanOver_tanExp hv c)`.
-/
theorem isTangent_tanExp (hv : ∀ i, IsTangent (v i)) (c : Fin n → R) : IsTangent (tanExp v c) :=
  (isTan_iff _).1 (isTanOver_tanExp hv c)

def combHom (hv : ∀ i, IsTangent (v i)) :
    (Fin n → R) →+ Additive (sp (R₀ := R) (DualNumber R) ⟶ G) :=
  AddMonoidHom.mk' (fun c => Additive.ofMul (tanExp v c)) (fun c c' => by
    rw [← ofMul_mul]
    refine congrArg Additive.ofMul ?_
    rw [← lieExp_add hv _ _ _ _ (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _)
      (fun _ => by rw [← TrivSqZeroExt.inr_add]; exact TrivSqZeroExt.inr_mul_inr _ _ _)]
    exact lieExp_congr _ (fun i => TrivSqZeroExt.inr_add _ _ _) _ _)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `_ = (combHom hv (∑ i, c i • M i)).toMul`. Rewrite using `[map_sum, toMul_sum, tanExp, lieExp]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `(comp_lieExp v _ _ _).trans ?_` and prove the remaining obligations. Conclude with `lieExp_congr _ (fun j => by`.

Simplify using `[epsTo, dualTo_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.inl_mul_inr, mul_comm, smul_smul]) _ _`.
-/
theorem tanExp_tanExp (hv : ∀ i, IsTangent (v i)) {m : ℕ} (M : Fin m → Fin n → R)
    (c : Fin m → R) : tanExp (fun i => tanExp v (M i)) c = tanExp v (∑ i, c i • M i) := by
  change _ = (combHom hv (∑ i, c i • M i)).toMul
  rw [map_sum, toMul_sum, tanExp, lieExp]
  refine Finset.prod_congr rfl fun i _ => ?_
  refine (comp_lieExp v _ _ _).trans ?_
  exact lieExp_congr _ (fun j => by
    simp [epsTo, dualTo_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.inl_mul_inr,
      mul_comm, smul_smul]) _ _

/- English proof (translation)
Rewrite using `[tanExp, lieExp, Finset.prod_eq_single i]`. Establish `: ∀ h, epsTo R (inr ((Pi.single i (1 : R) : Fin n → R) i) : DualNumber R) h = AlgHom.id R _` using `fun h => DualNumber.algHom_ext (by`. Rewrite using `[epsTo_eps, Pi.single_eq_same]`. Use the proof step `rfl)`. Rewrite using `[this, spMap_id]`.

Conclude with `Category.id_comp _`. Introduce `j _ hj`. Conclude with `epsTo_zero_comp ((isTan_iff _).2 (hv j)) _ (by simp [Pi.single_eq_of_ne hj]) _`. Simplify using the standard rewrite rules.
-/
theorem tanExp_single (hv : ∀ i, IsTangent (v i)) (i : Fin n) :
    tanExp v (Pi.single i (1 : R)) = v i := by
  rw [tanExp, lieExp, Finset.prod_eq_single i]
  · have : ∀ h, epsTo R (inr ((Pi.single i (1 : R) : Fin n → R) i) : DualNumber R) h =
        AlgHom.id R _ := fun h => DualNumber.algHom_ext (by
      rw [epsTo_eps, Pi.single_eq_same]; rfl)
    rw [this, spMap_id]
    exact Category.id_comp _
  · intro j _ hj
    exact epsTo_zero_comp ((isTan_iff _).2 (hv j)) _ (by simp [Pi.single_eq_of_ne hj]) _
  · simp

/- English proof (translation)
Establish `key : ∀ c : Fin n → R, tanExp (fun i => tanExp v (M i)) c = tanExp v (Matrix.vecMul c M)` using `fun c => by`. Rewrite using `[Matrix.vecMul_eq_sum]`. Conclude with `tanExp_tanExp hv.1 (fun i => M i) c`. Take `⟨hinj, -⟩` from `isLieBasisOver_self hv`. Rewrite using `[← Matrix.isUnit_iff_isUnit_det]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `Matrix.vecMul_surjective_iff_isUnit.1 fun d => ?_` and prove the remaining obligations. Take `⟨c, hc, -⟩` from `h.2 _ (isTangent_tanExp hv.1 d)`. Rewrite `hc` using `[isLieComb_iff_tanExp, key]`.

Conclude with `⟨c, (hinj _ _ hc).symm⟩`. Introduce `h`. Use `⟨fun i => isTangent_tanExp hv.1 _, fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨d, hd, -⟩` from `hv.2 w hw`. Take `⟨c, hc⟩` from `Matrix.vecMul_surjective_iff_isUnit.2 h d`.

Establish `hc' : Matrix.vecMul c M = d` using `hc`. Rewrite `hd` using `[isLieComb_iff_tanExp]`. Use `⟨c, ?_, fun c' h' => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IsLieComb _ _ _`. Rewrite using `[isLieComb_iff_tanExp, key, hc', hd]`.

Express the relevant statement in the definitionally equal form `IsLieComb _ _ _ at h'`. Rewrite `h'` using `[isLieComb_iff_tanExp, key, hd, ← hc']`. Conclude with `Matrix.vecMul_injective_of_isUnit h (hinj _ _ h').symm`.
-/
theorem isLieBasis_iff_isUnit_det (hv : IsLieBasis v) (M : Matrix (Fin n) (Fin n) R) :
    IsLieBasis (fun i => tanExp v (M i)) ↔ IsUnit M.det := by
  have key : ∀ c : Fin n → R,
      tanExp (fun i => tanExp v (M i)) c = tanExp v (Matrix.vecMul c M) := fun c => by
    rw [Matrix.vecMul_eq_sum]
    exact tanExp_tanExp hv.1 (fun i => M i) c
  obtain ⟨hinj, -⟩ := isLieBasisOver_self hv
  rw [← Matrix.isUnit_iff_isUnit_det]
  constructor
  · intro h
    refine Matrix.vecMul_surjective_iff_isUnit.1 fun d => ?_
    obtain ⟨c, hc, -⟩ := h.2 _ (isTangent_tanExp hv.1 d)
    rw [isLieComb_iff_tanExp, key] at hc
    exact ⟨c, (hinj _ _ hc).symm⟩
  · intro h
    refine ⟨fun i => isTangent_tanExp hv.1 _, fun w hw => ?_⟩
    obtain ⟨d, hd, -⟩ := hv.2 w hw
    obtain ⟨c, hc⟩ := Matrix.vecMul_surjective_iff_isUnit.2 h d
    have hc' : Matrix.vecMul c M = d := hc
    rw [isLieComb_iff_tanExp] at hd
    refine ⟨c, ?_, fun c' h' => ?_⟩
    · change IsLieComb _ _ _
      rw [isLieComb_iff_tanExp, key, hc', hd]
    · change IsLieComb _ _ _ at h'
      rw [isLieComb_iff_tanExp, key, hd, ← hc'] at h'
      exact Matrix.vecMul_injective_of_isUnit h (hinj _ _ h').symm

/- English proof (translation)
Use `⟨fun c => ⟨tanExp v c, (isLieComb_iff_tanExp _ _).2 rfl, fun w hw => (isLieComb_iff_tanExp _ _).1 hw⟩, fun c w hw => ?_, fun m M v' c w hM hw => ?_, fun i => (isLieComb_iff_tanExp _ _).2 (tanExp_single hv i).symm, fun M v' hb hM => ?_⟩` and prove the remaining obligations. Rewrite using `[(isLieComb_iff_tanExp _ _).1 hw]`. Conclude with `isTangent_tanExp hv c`. Choose the witnesses or unpack the hypotheses as in `rfl : v' = fun i => tanExp v (M i) :=`. Use function extensionality and compare the values at `fun i => (isLieComb_iff_tanExp _ _).1 (hM i)`.

Rewrite `hw`, the goal using `[isLieComb_iff_tanExp]`. Rewrite using `[hw, tanExp_tanExp hv]`. Choose the witnesses or unpack the hypotheses as in `rfl : v' = fun i => tanExp v (M i) :=`. Use function extensionality and compare the values at `fun i => (isLieComb_iff_tanExp _ _).1 (hM i)`. Conclude with `isLieBasis_iff_isUnit_det hb M`.
-/
theorem lieComb_algebra (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (n : ℕ) (v : Fin n → (epsR R ⟶ G)) (hv : ∀ i, IsTangent (v i)) :
    (∀ c, ∃! w, IsLieComb c v w) ∧ (∀ c w, IsLieComb c v w → IsTangent w) ∧
    (∀ (m : ℕ) (M : Fin m → Fin n → R) (v' : Fin m → (epsR R ⟶ G)) (c : Fin m → R) (w),
      (∀ i, IsLieComb (M i) v (v' i)) → IsLieComb c v' w → IsLieComb (∑ i, c i • M i) v w) ∧
    (∀ i, IsLieComb (Pi.single i 1) v (v i)) ∧
    ∀ (M : Matrix (Fin n) (Fin n) R) (v' : Fin n → (epsR R ⟶ G)), IsLieBasis v →
      (∀ i, IsLieComb (M i) v (v' i)) → (IsLieBasis v' ↔ IsUnit M.det) := by
  refine ⟨fun c => ⟨tanExp v c, (isLieComb_iff_tanExp _ _).2 rfl,
    fun w hw => (isLieComb_iff_tanExp _ _).1 hw⟩, fun c w hw => ?_, fun m M v' c w hM hw => ?_,
    fun i => (isLieComb_iff_tanExp _ _).2 (tanExp_single hv i).symm, fun M v' hb hM => ?_⟩
  · rw [(isLieComb_iff_tanExp _ _).1 hw]
    exact isTangent_tanExp hv c
  · obtain rfl : v' = fun i => tanExp v (M i) :=
      funext fun i => (isLieComb_iff_tanExp _ _).1 (hM i)
    rw [isLieComb_iff_tanExp] at hw ⊢
    rw [hw, tanExp_tanExp hv]
  · obtain rfl : v' = fun i => tanExp v (M i) :=
      funext fun i => (isLieComb_iff_tanExp _ _).1 (hM i)
    exact isLieBasis_iff_isUnit_det hb M

end GlobalTheory.LieComb
