import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.GenSecInt

open GlobalTheory.PrimSec GlobalTheory.AbLaw

variable {X XK : Scheme.{0}} [IsIntegral X] {f : X ⟶ Sp ℤ} {j : XK ⟶ X} {fK : XK ⟶ Sp ℚ}
  (H : IsPullback j fK f (spMap (algebraMap ℤ ℚ)))
include H

/- English proof (translation)
Distinguish the cases in `hne : Nonempty U`. Use `letI := (j.app U).hom.toAlgebra haveI := isLocalization_app H hU haveI : CharZero Γ(X, U) := ((resG X (le_top : U ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X _)).1 hc`. Use `IsLocalization.injective (M := (nonZeroDivisors ℤ).map (AbLaw.cst f U)) Γ(XK, j ⁻¹ᵁ U) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨π, hπ, rfl⟩`. Use `mem_nonZeroDivisors_of_ne_zero ?_` and prove the remaining obligations.

Establish `e : AbLaw.cst f U π = (π : Γ(X, U))` using `map_intCast _ π`. Rewrite using `[e, Ne, Int.cast_eq_zero]`. Conclude with `nonZeroDivisors.ne_zero hπ`. Use `haveI : Subsingleton Γ(X, U) := by`. Establish `: U = ⊥`.

Rewrite using `[eq_bot_iff]`. Conclude with `fun x hx => (hne ⟨⟨x, hx⟩⟩).elim`. Substitute `this` using the available equality. Use `infer_instance`. Conclude with `fun a b _ => Subsingleton.elim a b`.
-/
theorem app_injective_of_affine (hc : CharZero Γ(X, ⊤)) {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective (j.app U).hom := by
  by_cases hne : Nonempty U
  · letI := (j.app U).hom.toAlgebra
    haveI := isLocalization_app H hU
    haveI : CharZero Γ(X, U) :=
      ((resG X (le_top : U ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X _)).1 hc
    refine IsLocalization.injective (M := (nonZeroDivisors ℤ).map (AbLaw.cst f U)) Γ(XK, j ⁻¹ᵁ U) ?_
    rintro _ ⟨π, hπ, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    have e : AbLaw.cst f U π = (π : Γ(X, U)) := map_intCast _ π
    rw [e, Ne, Int.cast_eq_zero]
    exact nonZeroDivisors.ne_zero hπ
  · haveI : Subsingleton Γ(X, U) := by
      have : U = ⊥ := by
        rw [eq_bot_iff]
        exact fun x hx => (hne ⟨⟨x, hx⟩⟩).elim
      subst this
      infer_instance
    exact fun a b _ => Subsingleton.elim a b

/- English proof (translation)
Introduce `a b h`. Use `X.sheaf.eq_of_locally_eq' (fun V : {V : X.affineOpens // V.1 ≤ U} => V.1.1) U (fun V => homOfLE V.2) ?_ a b fun V => ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩`.

Apply `app_injective_of_affine H hc V.1.2` to reduce the goal to its premises. Conclude with `(app_rs j V.2 a).trans ((congrArg _ h).trans (app_rs j V.2 b).symm)`.
-/
theorem app_injective (hc : CharZero Γ(X, ⊤)) (U : X.Opens) : Function.Injective (j.app U).hom := by
  intro a b h
  refine X.sheaf.eq_of_locally_eq' (fun V : {V : X.affineOpens // V.1 ≤ U} => V.1.1) U
    (fun V => homOfLE V.2) ?_ a b fun V => ?_
  · intro x hx
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩
  · apply app_injective_of_affine H hc V.1.2
    exact (app_rs j V.2 a).trans ((congrArg _ h).trans (app_rs j V.2 b).symm)

/- English proof (translation)
Use `choose V hV b hx hb using h`. Establish `hcov : U ≤ ⨆ x : U, V x.1 x.2` using `fun x hxU => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxU⟩, hx x hxU⟩`. Take `⟨s, hs, -⟩` from `X.sheaf.existsUnique_gluing' (fun x : U => V x.1 x.2) U (fun x => homOfLE (hV x.1 x.2)) hcov (fun x => b x.1 x.2) (fun x y => by`. Apply `app_injective H hc` to reduce the goal to its premises. Use `(app_rs j inf_le_left _).trans (Eq.trans ?_ (app_rs j inf_le_right _).symm)` and prove the remaining obligations.

Rewrite using `[hb, hb]`. Conclude with `(rs_rs _ _ _).trans (rs_rs _ _ _).symm)`. Use `⟨s, XK.sheaf.eq_of_locally_eq' (fun x : U => j ⁻¹ᵁ V x.1 x.2) (j ⁻¹ᵁ U) (fun x => homOfLE fun _ hy => hV x.1 x.2 hy) ?_ _ _ fun x => ?_⟩` and prove the remaining obligations. Introduce `y hy`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨j y, hy⟩, hx _ hy⟩`.

Conclude with `(app_rs j (hV x.1 x.2) s).symm.trans ((congrArg _ (hs x)).trans (hb x.1 x.2))`.
-/
theorem exists_extension (hc : CharZero Γ(X, ⊤)) {U : X.Opens} (t : Γ(XK, j ⁻¹ᵁ U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hV : V ≤ U) (b : Γ(X, V)), x ∈ V ∧
      (j.app V).hom b = rs XK (pre_le j hV) t) :
    ∃ b : Γ(X, U), (j.app U).hom b = t := by
  choose V hV b hx hb using h
  have hcov : U ≤ ⨆ x : U, V x.1 x.2 := fun x hxU =>
    TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxU⟩, hx x hxU⟩
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun x : U => V x.1 x.2) U
    (fun x => homOfLE (hV x.1 x.2)) hcov (fun x => b x.1 x.2) (fun x y => by
      apply app_injective H hc
      refine (app_rs j inf_le_left _).trans (Eq.trans ?_ (app_rs j inf_le_right _).symm)
      rw [hb, hb]
      exact (rs_rs _ _ _).trans (rs_rs _ _ _).symm)
  refine ⟨s, XK.sheaf.eq_of_locally_eq' (fun x : U => j ⁻¹ᵁ V x.1 x.2) (j ⁻¹ᵁ U)
    (fun x => homOfLE fun _ hy => hV x.1 x.2 hy) ?_ _ _ fun x => ?_⟩
  · intro y hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨j y, hy⟩, hx _ hy⟩
  · exact (app_rs j (hV x.1 x.2) s).symm.trans ((congrArg _ (hs x)).trans (hb x.1 x.2))

/- English proof (translation)
Establish `hx : ∀ x : X, ∃ (i : B.ι) (W : X.Opens), IsAffineOpen W ∧ x ∈ W ∧ W ≤ B.U i`. Introduce `x`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 (show x ∈ ⨆ i, B.U i from hB.cover ▸ trivial)`. Take `⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open hi (B.U i).isOpen`. Conclude with `⟨i, W, hW, hxW, hWU⟩`.

Use `choose ci Wx hWa hxW hWle using hx`. Take `⟨S, hS⟩` from `isCompact_univ.elim_finite_subcover (fun x => (Wx x : Set X)) (fun x => (Wx x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)`. Use `choose π b hπ hb using fun x => exists_numerator H (hWa x) (loc t (ci x) (hWle x))`. Set `c : ℤ` to `∏ x ∈ S, π x`. Establish `hc : algebraMap ℤ ℚ c ≠ 0`.

Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]`. Conclude with `Finset.prod_ne_zero_iff.2 fun x _ => hπ x`. Establish `hb' : ∀ x ∈ S, ∃ b' : Γ(X, Wx x), (j.app (Wx x)).hom b' = AbLaw.cst fK (j ⁻¹ᵁ Wx x) (algebraMap ℤ ℚ c) * loc t (ci x) (hWle x)`. Introduce `x hxS`. Use `⟨AbLaw.cst f (Wx x) (∏ y ∈ S.erase x, π y) * b x, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, app_cst H.w, hb, ← mul_assoc, ← map_mul, ← map_mul, Finset.prod_erase_mul _ _ hxS]`. Use `choose! b' hb' using hb'`. Establish `key : ∀ i, ∃ s : Γ(X, B.U i), (j.app (B.U i)).hom s = AbLaw.cst fK (j ⁻¹ᵁ B.U i) (algebraMap ℤ ℚ c) * loc t i le_rfl`. Introduce `i`. Use `exists_extension H hc0 _ fun x hx => ?_` and prove the remaining obligations.

Take `⟨z, hzS, hxz⟩` from `Set.mem_iUnion₂.1 (hS (Set.mem_univ x))`. Establish `hV : B.U i ⊓ Wx z ≤ B.U i` using `inf_le_left`. Establish `hk : B.U i ⊓ Wx z ≤ B.U (ci z)` using `inf_le_right.trans (hWle z)`. Use `⟨B.U i ⊓ Wx z, hV, rs X (le_inf hV hk) (B.g i (ci z)).val * rs X inf_le_right (b' z), ⟨hx, hxz⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, app_rs j (inf_le_right : B.U i ⊓ Wx z ≤ Wx z) (b' z), hb' z hzS, map_mul, rs_cst, rs_loc t (ci z) (hWle z) (inf_le_right : B.U i ⊓ Wx z ≤ Wx z), map_mul, rs_cst, rs_loc t i le_rfl hV, loc_trans t i (ci z) (le_rfl.trans hV) hk]`.

Expand and normalize the polynomial expressions, which then agree. Use `choose s hs using key`. Establish `hunit : ∀ W : XK.Opens, IsUnit (AbLaw.cst fK W (algebraMap ℤ ℚ c))` using `fun W => (IsUnit.mk0 _ hc).map _`. Use `⟨⟨s, fun i k => ?_⟩, fun y => ?_⟩` and prove the remaining obligations. Apply `app_injective H hc0` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `(j.app _).hom (rs X inf_le_left (s i)) = (j.app _).hom (_ * rs X inf_le_right (s k))`. Rewrite using `[map_mul, app_rs, app_rs, hs, hs, map_mul, map_mul, rs_cst, rs_cst, rs_loc t _ _ inf_le_left, rs_loc t _ _ inf_le_right, loc_trans t i k _ inf_le_right, rs_self]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem : ∀ i, y ∈ j ⁻¹ᵁ B.U i → (j y ∈ X.basicOpen (s i) ↔ y ∈ XK.basicOpen (t.f (fun _ => i)))`. Introduce `i hy`.

Express the relevant statement in the definitionally equal form `y ∈ j ⁻¹ᵁ X.basicOpen (s i) ↔ _`. Rewrite using `[Scheme.preimage_basicOpen]`. Express the relevant statement in the definitionally equal form `y ∈ XK.basicOpen ((j.app (B.U i)).hom (s i)) ↔ _`. Rewrite using `[hs, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (hunit _)]`. Conclude with `⟨fun h => (mem_basicOpen_rs _ _ hy).1 h.2, fun h => ⟨hy, (mem_basicOpen_rs _ _ hy).2 h⟩⟩`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 h`. Establish `hy : y ∈ j ⁻¹ᵁ B.U i` using `X.basicOpen_le (s i) hi`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, (hmem i hy).1 hi⟩`.

Introduce `h`. Take `⟨k, hk⟩` from `TopologicalSpace.Opens.mem_iSup.1 h`. Establish `hy : y ∈ j ⁻¹ᵁ B.U (k PUnit.unit)` using `Set.mem_iInter.1 (XK.basicOpen_le (t.f k) hk) PUnit.unit`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨k PUnit.unit, (hmem (k PUnit.unit) hy).2 hk⟩`.
-/
theorem exists_sec [CompactSpace X] (hc0 : CharZero Γ(X, ⊤)) (B : LB X) (hB : B.IsLB)
    (t : (B.pull j).Sec) : ∃ s : B.Sec, ∀ y : XK,
      j y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ↔ y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
  have hx : ∀ x : X, ∃ (i : B.ι) (W : X.Opens), IsAffineOpen W ∧ x ∈ W ∧ W ≤ B.U i := by
    intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show x ∈ ⨆ i, B.U i from hB.cover ▸ trivial)
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hi (B.U i).isOpen
    exact ⟨i, W, hW, hxW, hWU⟩
  choose ci Wx hWa hxW hWle using hx
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun x => (Wx x : Set X)) (fun x => (Wx x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  choose π b hπ hb using fun x => exists_numerator H (hWa x) (loc t (ci x) (hWle x))
  classical
  let c : ℤ := ∏ x ∈ S, π x
  have hc : algebraMap ℤ ℚ c ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    exact Finset.prod_ne_zero_iff.2 fun x _ => hπ x
  have hb' : ∀ x ∈ S, ∃ b' : Γ(X, Wx x), (j.app (Wx x)).hom b' =
      AbLaw.cst fK (j ⁻¹ᵁ Wx x) (algebraMap ℤ ℚ c) * loc t (ci x) (hWle x) := by
    intro x hxS
    refine ⟨AbLaw.cst f (Wx x) (∏ y ∈ S.erase x, π y) * b x, ?_⟩
    rw [map_mul, app_cst H.w, hb, ← mul_assoc, ← map_mul, ← map_mul, Finset.prod_erase_mul _ _ hxS]
  choose! b' hb' using hb'
  have key : ∀ i, ∃ s : Γ(X, B.U i), (j.app (B.U i)).hom s =
      AbLaw.cst fK (j ⁻¹ᵁ B.U i) (algebraMap ℤ ℚ c) * loc t i le_rfl := by
    intro i
    refine exists_extension H hc0 _ fun x hx => ?_
    obtain ⟨z, hzS, hxz⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ x))
    have hV : B.U i ⊓ Wx z ≤ B.U i := inf_le_left
    have hk : B.U i ⊓ Wx z ≤ B.U (ci z) := inf_le_right.trans (hWle z)
    refine ⟨B.U i ⊓ Wx z, hV, rs X (le_inf hV hk) (B.g i (ci z)).val * rs X inf_le_right (b' z), ⟨hx, hxz⟩, ?_⟩
    rw [map_mul, app_rs j (inf_le_right : B.U i ⊓ Wx z ≤ Wx z) (b' z), hb' z hzS, map_mul, rs_cst,
      rs_loc t (ci z) (hWle z) (inf_le_right : B.U i ⊓ Wx z ≤ Wx z), map_mul, rs_cst,
      rs_loc t i le_rfl hV,
      loc_trans t i (ci z) (le_rfl.trans hV) hk]
    ring
  choose s hs using key
  have hunit : ∀ W : XK.Opens, IsUnit (AbLaw.cst fK W (algebraMap ℤ ℚ c)) := fun W =>
    (IsUnit.mk0 _ hc).map _
  refine ⟨⟨s, fun i k => ?_⟩, fun y => ?_⟩
  · apply app_injective H hc0
    change (j.app _).hom (rs X inf_le_left (s i)) = (j.app _).hom (_ * rs X inf_le_right (s k))
    rw [map_mul, app_rs, app_rs, hs, hs, map_mul, map_mul, rs_cst, rs_cst,
      rs_loc t _ _ inf_le_left, rs_loc t _ _ inf_le_right, loc_trans t i k _ inf_le_right, rs_self]
    ring
  · have hmem : ∀ i, y ∈ j ⁻¹ᵁ B.U i →
        (j y ∈ X.basicOpen (s i) ↔ y ∈ XK.basicOpen (t.f (fun _ => i))) := by
      intro i hy
      change y ∈ j ⁻¹ᵁ X.basicOpen (s i) ↔ _
      rw [Scheme.preimage_basicOpen]
      change y ∈ XK.basicOpen ((j.app (B.U i)).hom (s i)) ↔ _
      rw [hs, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (hunit _)]
      exact ⟨fun h => (mem_basicOpen_rs _ _ hy).1 h.2, fun h => ⟨hy, (mem_basicOpen_rs _ _ hy).2 h⟩⟩
    constructor
    · intro h
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
      have hy : y ∈ j ⁻¹ᵁ B.U i := X.basicOpen_le (s i) hi
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, (hmem i hy).1 hi⟩
    · intro h
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
      have hy : y ∈ j ⁻¹ᵁ B.U (k PUnit.unit) := Set.mem_iInter.1 (XK.basicOpen_le (t.f k) hk) PUnit.unit
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨k PUnit.unit, (hmem (k PUnit.unit) hy).2 hk⟩

end GlobalTheory.GenSecInt

/- English proof (translation)
Introduce `k _ X _ p D h B hB t`. Use `haveI := h.isNoetherian`. Establish `H : IsPullback (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))) (Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))) (p ≫ spMap (Int.castRingHom k)) (spMap (algebraMap ℤ ℚ))` using `IsPullback.of_hasPullback _ _`. Conclude with `GlobalTheory.GenSecInt.exists_sec H h.charZero B hB t`.
-/
theorem GlobalTheory.GenSecInt.main : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (B : LB X), B.IsLB → ∀ t : (B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))).Sec, ∃ s : B.Sec, ∀ y : ↥(Limits.pullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))), (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))) y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ↔ y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
  intro k _ X _ p D h B hB t
  haveI := h.isNoetherian
  have H : IsPullback (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))
      (Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))
      (p ≫ spMap (Int.castRingHom k)) (spMap (algebraMap ℤ ℚ)) := IsPullback.of_hasPullback _ _
  exact GlobalTheory.GenSecInt.exists_sec H h.charZero B hB t
