import Mathlib
import GroundTheory.AutomorphicForms.SphericalPrincipal
import GroundTheory.AutomorphicForms.SphericalLaurent

noncomputable section

namespace GroundTheory.Automorphic

open MeasureTheory Matrix GLnLocal Iwasawa Parabolic HeckeAlgebra AddMonoidAlgebra
open scoped ValuativeRel

namespace Spherical

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

/- English proof (translation)
Rewrite using `[torusPow, torusPow, torusPow, ← map_mul]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[_root_.zpow_add]`.
-/
theorem torusPow_add (l l' : Fin n → ℤ) :
    torusPow F n (l + l') = torusPow F n l * torusPow F n l' := by
  rw [torusPow, torusPow, torusPow, ← map_mul]
  congr 1
  funext i
  simp [_root_.zpow_add]

/- English proof (translation)
Rewrite using `[torusPow, ← map_one (diagGL F n)]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.
-/
theorem torusPow_zero : torusPow F n 0 = 1 := by
  rw [torusPow, ← map_one (diagGL F n)]
  congr 1
  funext i
  simp

/- English proof (translation)
Rewrite using `[← map_mul, ← map_mul, mul_comm]`.
-/
theorem diagGL_mul_comm (a b : Fin n → Fˣ) : diagGL F n a * diagGL F n b = diagGL F n b * diagGL F n a := by
  rw [← map_mul, ← map_mul, mul_comm]

/- English proof (translation)
Simplify `iwasawaExponent_eq F n (unipotent F n).one_mem (integralGL F n).one_mem (l := (0 : Fin n → ℤ))` using `[torusPow_zero]`.
-/
theorem iwasawaExponent_one : iwasawaExponent F n (1 : GL (Fin n) F) = 0 := by
  simpa [torusPow_zero] using
    iwasawaExponent_eq F n (unipotent F n).one_mem (integralGL F n).one_mem (l := (0 : Fin n → ℤ))

/- English proof (translation)
Use `choose l e he using fun i => exists_zpow_mul_unit F (d i).ne_zero`. Use `⟨l, e, ?_⟩` and prove the remaining obligations. Rewrite using `[torusPow, ← map_mul]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Use `ext`. Simplify using `[he i, Units.val_zpow_eq_zpow_val, Units.coe_map]`.
-/
theorem exists_diagGL_eq_torusPow_mul (d : Fin n → Fˣ) :
    ∃ l : Fin n → ℤ, ∃ e : Fin n → (𝒪[F])ˣ,
      diagGL F n d = torusPow F n l * diagGL F n fun i => Units.map (𝒪[F]).subtype.toMonoidHom (e i) := by
  choose l e he using fun i => exists_zpow_mul_unit F (d i).ne_zero
  refine ⟨l, e, ?_⟩
  rw [torusPow, ← map_mul]
  congr 1
  funext i
  ext
  simp [he i, Units.val_zpow_eq_zpow_val, Units.coe_map]

def diagUnits {b : GL (Fin n) F} (hb : b ∈ borel F n) : Fin n → Fˣ :=
  fun i => Units.mk0 (b i i) (apply_self_ne_zero_of_mem_borel F n hb i)

/- English proof (translation)
Establish `hDinv : (diagGL F n (diagUnits hb))⁻¹ ∈ borel F n` using `(borel F n).inv_mem (diagGL_mem_borel F n _)`. Use `⟨(borel F n).mul_mem hb hDinv, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_apply_self_of_mem_borel F n hb hDinv, ← map_inv, coe_diagGL, diagonal_apply_eq]`. Simplify using `[diagUnits, apply_self_ne_zero_of_mem_borel F n hb i]`.
-/
theorem mul_inv_diagUnits_mem_unipotent {b : GL (Fin n) F} (hb : b ∈ borel F n) :
    b * (diagGL F n (diagUnits hb))⁻¹ ∈ unipotent F n := by
  have hDinv : (diagGL F n (diagUnits hb))⁻¹ ∈ borel F n :=
    (borel F n).inv_mem (diagGL_mem_borel F n _)
  refine ⟨(borel F n).mul_mem hb hDinv, fun i => ?_⟩
  rw [mul_apply_self_of_mem_borel F n hb hDinv, ← map_inv, coe_diagGL, diagonal_apply_eq]
  simp [diagUnits, apply_self_ne_zero_of_mem_borel F n hb i]

/- English proof (translation)
Take `⟨l, e, hde⟩` from `exists_diagGL_eq_torusPow_mul (diagUnits hb)`. Use `set D := diagGL F n (diagUnits hb)`. Use `set E : GL (Fin n) F := diagGL F n fun i => Units.map (𝒪[F]).subtype.toMonoidHom (e i)`. Establish `hE : E ∈ integralGL F n` using `diagGL_map_mem_integralGL F n e`. Establish `hu` using `mul_inv_diagUnits_mem_unipotent hb`.

Establish `key : ∀ g : GL (Fin n) F, iwasawaExponent F n (b * g) = l + iwasawaExponent F n g`. Introduce `g`. Take `⟨u', hu', k', hk', hg⟩` from `exists_eq_mul_torusPow_iwasawaExponent F n g`. Use `set lg := iwasawaExponent F n g with hlg`. Establish `hcomm : E * torusPow F n lg = torusPow F n lg * E` using `diagGL_mul_comm _ _`.

Establish `hD : D⁻¹ * torusPow F n l = E⁻¹`. Rewrite using `[hde, _root_.mul_inv_rev, inv_mul_cancel_right]`. Establish `: b * g = (b * D⁻¹ * (D * u' * D⁻¹)) * torusPow F n (l + lg) * (E * k')`. Rewrite using `[torusPow_add]`. Use `conv_lhs => rw [hg]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hD]`. Use `_ = _ := by group`. Rewrite using `[this]`. Use `iwasawaExponent_eq F n ((unipotent F n).mul_mem hu ?_) ((integralGL F n).mul_mem hE hk')` and prove the remaining obligations.

Conclude with `diagGL_mul_mul_inv_mem_unipotent F n hu' _`. Establish `hb1` using `key 1`. Rewrite `hb1` using `[mul_one, iwasawaExponent_one, add_zero]`. Rewrite using `[key, hb1]`.
-/
theorem iwasawaExponent_mul_of_mem_borel {b : GL (Fin n) F} (hb : b ∈ borel F n)
    (g : GL (Fin n) F) :
    iwasawaExponent F n (b * g) = iwasawaExponent F n b + iwasawaExponent F n g := by
  obtain ⟨l, e, hde⟩ := exists_diagGL_eq_torusPow_mul (diagUnits hb)
  set D := diagGL F n (diagUnits hb)
  set E : GL (Fin n) F := diagGL F n fun i => Units.map (𝒪[F]).subtype.toMonoidHom (e i)
  have hE : E ∈ integralGL F n := diagGL_map_mem_integralGL F n e
  have hu := mul_inv_diagUnits_mem_unipotent hb
  have key : ∀ g : GL (Fin n) F, iwasawaExponent F n (b * g) = l + iwasawaExponent F n g := by
    intro g
    obtain ⟨u', hu', k', hk', hg⟩ := exists_eq_mul_torusPow_iwasawaExponent F n g
    set lg := iwasawaExponent F n g with hlg
    have hcomm : E * torusPow F n lg = torusPow F n lg * E :=
      diagGL_mul_comm _ _
    have hD : D⁻¹ * torusPow F n l = E⁻¹ := by
      rw [hde, _root_.mul_inv_rev, inv_mul_cancel_right]
    have : b * g = (b * D⁻¹ * (D * u' * D⁻¹)) * torusPow F n (l + lg) * (E * k') := by
      rw [torusPow_add]
      conv_lhs => rw [hg]
      calc b * (u' * torusPow F n lg * k')
          = b * u' * (E⁻¹ * (E * torusPow F n lg)) * k' := by group
        _ = b * u' * (E⁻¹ * (torusPow F n lg * E)) * k' := by rw [hcomm]
        _ = b * u' * ((D⁻¹ * torusPow F n l) * (torusPow F n lg * E)) * k' := by
            rw [hD]
        _ = _ := by group
    rw [this]
    refine iwasawaExponent_eq F n ((unipotent F n).mul_mem hu ?_) ((integralGL F n).mul_mem hE hk')
    exact diagGL_mul_mul_inv_mem_unipotent F n hu' _
  have hb1 := key 1
  rw [mul_one, iwasawaExponent_one, add_zero] at hb1
  rw [key, hb1]

def unramifiedChar (w : Fin n → ℂˣ) : levi F n (id : Fin n → Fin n) →* ℂ where
  toFun t := monomialChar (iwasawaExponent F n t) w * invSqrtModular F n id (leviIncl t)
  map_one' := by simp [iwasawaExponent_one]
  map_mul' t t' := by
    have ht : (t : GL (Fin n) F) ∈ borel F n := levi_le_blockUpper t.2
    simp only [Subgroup.coe_mul, iwasawaExponent_mul_of_mem_borel ht, monomialChar_add, map_mul]
    ring

/- English proof (translation)
Establish `h` using `sqrtModular_mul_invSqrtModular p`. Establish `hs : sqrtModular F n id p = 1` using `by show ((NNReal.sqrt (Measure.modularCharacter p) : ℝ) : ℂ) = 1`. Rewrite using `[Measures.modularCharacter_eq_one_of_mem_integralGL p hp]`. Simplify using the standard rewrite rules. Rewrite `h` using `[hs, one_mul]`. Then use the resulting hypothesis.
-/
theorem invSqrtModular_eq_one {p : blockUpper F n (id : Fin n → Fin n)}
    (hp : (p : GL (Fin n) F) ∈ integralGL F n) : invSqrtModular F n id p = 1 := by
  have h := sqrtModular_mul_invSqrtModular p
  have hs : sqrtModular F n id p = 1 := by
    show ((NNReal.sqrt (Measure.modularCharacter p) : ℝ) : ℂ) = 1
    rw [Measures.modularCharacter_eq_one_of_mem_integralGL p hp]
    simp
  rwa [hs, one_mul] at h

/- English proof (translation)
Introduce `t ht`. Use `show monomialChar (iwasawaExponent F n t) w * invSqrtModular F n id (leviIncl t) = 1`. Establish `h0 : iwasawaExponent F n (t : GL (Fin n) F) = 0`. Simplify `iwasawaExponent_mul_of_mem_integralGL F n 1 ht` using `[iwasawaExponent_one]`. Rewrite using `[h0, monomialChar_zero, invSqrtModular_eq_one ht, one_mul]`.
-/
theorem isUnramified_unramifiedChar (w : Fin n → ℂˣ) : IsUnramified (unramifiedChar (F := F) w) := by
  intro t ht
  show monomialChar (iwasawaExponent F n t) w * invSqrtModular F n id (leviIncl t) = 1
  have h0 : iwasawaExponent F n (t : GL (Fin n) F) = 0 := by
    simpa [iwasawaExponent_one] using iwasawaExponent_mul_of_mem_integralGL F n 1 ht
  rw [h0, monomialChar_zero, invSqrtModular_eq_one ht, one_mul]

/- English proof (translation)
Establish `hb : (b : GL (Fin n) F) ∈ borel F n` using `b.2`. Establish `hD : ((leviProj F n id b : levi F n (id : Fin n → Fin n)) : GL (Fin n) F) = diagGL F n (diagUnits hb)`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Rewrite using `[coe_diagGL, leviProj_apply]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using `[diagUnits]`. Simplify using `[hij, diagonal_apply_ne _ hij]`. Rewrite using `[hD]`. Use `conv_rhs => rw [show (b : GL (Fin n) F) = (b * (diagGL F n (diagUnits hb))⁻¹) * diagGL F n (diagUnits hb) by group]`.

Rewrite using `[iwasawaExponent_mul_of_mem_unipotent F n (mul_inv_diagUnits_mem_unipotent hb)]`.
-/
theorem iwasawaExponent_leviProj (b : blockUpper F n (id : Fin n → Fin n)) :
    iwasawaExponent F n ((leviProj F n id b : levi F n (id : Fin n → Fin n)) : GL (Fin n) F) =
      iwasawaExponent F n (b : GL (Fin n) F) := by
  have hb : (b : GL (Fin n) F) ∈ borel F n := b.2
  have hD : ((leviProj F n id b : levi F n (id : Fin n → Fin n)) : GL (Fin n) F) =
      diagGL F n (diagUnits hb) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [coe_diagGL, leviProj_apply]
    by_cases hij : i = j
    · subst hij
      simp [diagUnits]
    · simp [hij, diagonal_apply_ne _ hij]
  rw [hD]
  conv_rhs => rw [show (b : GL (Fin n) F) = (b * (diagGL F n (diagUnits hb))⁻¹) *
    diagGL F n (diagUnits hb) by group]
  rw [iwasawaExponent_mul_of_mem_unipotent F n (mul_inv_diagUnits_mem_unipotent hb)]

/- English proof (translation)
Rewrite using `[borelChar_apply]`. Express the relevant statement in the definitionally equal form `sqrtModular F n id b * (monomialChar (iwasawaExponent F n ((leviProj F n id b : levi F n (id : Fin n → Fin n)) : GL (Fin n) F)) w * invSqrtModular F n id (leviIncl (leviProj F n id b))) = _`. Rewrite using `[iwasawaExponent_leviProj]`. Establish `: invSqrtModular F n id (leviIncl (leviProj F n id b)) = invSqrtModular F n id b` using `by show (sqrtModular F n id (leviIncl (leviProj F n id b)))⁻¹ = (sqrtModular F n id b)⁻¹`. Rewrite using `[sqrtModular_leviProj]`.

Rewrite using `[this, mul_left_comm, sqrtModular_mul_invSqrtModular, mul_one]`.
-/
theorem borelChar_unramifiedChar (w : Fin n → ℂˣ) (b : blockUpper F n (id : Fin n → Fin n)) :
    borelChar (unramifiedChar w) b = monomialChar (iwasawaExponent F n (b : GL (Fin n) F)) w := by
  rw [borelChar_apply]
  change sqrtModular F n id b * (monomialChar (iwasawaExponent F n
    ((leviProj F n id b : levi F n (id : Fin n → Fin n)) : GL (Fin n) F)) w *
      invSqrtModular F n id (leviIncl (leviProj F n id b))) = _
  rw [iwasawaExponent_leviProj]
  have : invSqrtModular F n id (leviIncl (leviProj F n id b)) = invSqrtModular F n id b := by
    show (sqrtModular F n id (leviIncl (leviProj F n id b)))⁻¹ = (sqrtModular F n id b)⁻¹
    rw [sqrtModular_leviProj]
  rw [this, mul_left_comm, sqrtModular_mul_invSqrtModular, mul_one]

/- English proof (translation)
Take `⟨b, k, hk, rfl⟩` from `exists_borel_mul g`. Rewrite using `[sphericalFun_mul (isUnramified_unramifiedChar w) b hk, borelChar_unramifiedChar, iwasawaExponent_mul_of_mem_integralGL F n _ hk]`.
-/
theorem sphericalFun_unramifiedChar (w : Fin n → ℂˣ) (g : GL (Fin n) F) :
    sphericalFun (unramifiedChar w) g = monomialChar (iwasawaExponent F n g) w := by
  obtain ⟨b, k, hk, rfl⟩ := exists_borel_mul g
  rw [sphericalFun_mul (isUnramified_unramifiedChar w) b hk, borelChar_unramifiedChar,
    iwasawaExponent_mul_of_mem_integralGL F n _ hk]

variable (F n) in

def integralOpen : OpenSubgroup (GL (Fin n) F) := ⟨integralGL F n, isOpen_integralGL F n⟩

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

def cosetSupport (h : SphericalHecke μ (F := F) (n := n)) :
    Finset (GL (Fin n) F ⧸ integralGL F n) :=
  (finite_image_mk_tsupport (integralOpen F n) (h : HeckeAlgebra μ).mem.2).toFinset

/- English proof (translation)
Assume the negation of the conclusion as `h0`. Conclude with `hx ((Set.Finite.mem_toFinset _).mpr ⟨x.out, subset_tsupport _ h0, QuotientGroup.out_eq' x⟩)`.
-/
theorem apply_out_eq_zero {h : SphericalHecke μ (F := F) (n := n)}
    {x : GL (Fin n) F ⧸ integralGL F n} (hx : x ∉ cosetSupport h) :
    (h : HeckeAlgebra μ) x.out = 0 := by
  by_contra h0
  exact hx ((Set.Finite.mem_toFinset _).mpr ⟨x.out, subset_tsupport _ h0, QuotientGroup.out_eq' x⟩)

/- English proof (translation)
Establish `hf : HasCompactSupport fun g => (h : HeckeAlgebra μ) g * sphericalFun (unramifiedChar w) g` using `(h : HeckeAlgebra μ).mem.2.mul_right`. Establish `hK : ∀ g, ∀ k ∈ integralOpen F n, (fun g => (h : HeckeAlgebra μ) g * sphericalFun (unramifiedChar w) g) (g * k) = (fun g => (h : HeckeAlgebra μ) g * sphericalFun (unramifiedChar w) g) g`. Introduce `g k hk`. Simplify using `only [sphericalFun_unramifiedChar, iwasawaExponent_mul_of_mem_integralGL F n g hk]`. Rewrite using `[(HeckeAlgebraLevel.val_mem _ _ h k hk g).2]`.

Rewrite using `[sphericalEigen, integral_eq_smul_finsum_coset μ (integralOpen F n) (isCompact_integralGL F n) hf hK, Complex.real_smul]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `(∑ᶠ x : GL (Fin n) F ⧸ integralGL F n, (h : HeckeAlgebra μ) x.out * sphericalFun (unramifiedChar w) x.out) = _`. Rewrite using `[finsum_eq_sum_of_support_subset (s := cosetSupport h)]`. Simplify using `only [sphericalFun_unramifiedChar]`.

Introduce `x hx`. Assume the negation of the conclusion as `hxs`. Conclude with `hx (by simp [apply_out_eq_zero hxs])`.
-/
theorem sphericalEigen_unramifiedChar (w : Fin n → ℂˣ) (h : SphericalHecke μ (F := F) (n := n)) :
    sphericalEigen (unramifiedChar w) μ h = (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) *
      ∑ x ∈ cosetSupport h, (h : HeckeAlgebra μ) x.out *
        monomialChar (iwasawaExponent F n x.out) w := by
  have hf : HasCompactSupport fun g => (h : HeckeAlgebra μ) g * sphericalFun (unramifiedChar w) g :=
    (h : HeckeAlgebra μ).mem.2.mul_right
  have hK : ∀ g, ∀ k ∈ integralOpen F n,
      (fun g => (h : HeckeAlgebra μ) g * sphericalFun (unramifiedChar w) g) (g * k) =
        (fun g => (h : HeckeAlgebra μ) g * sphericalFun (unramifiedChar w) g) g := by
    intro g k hk
    simp only [sphericalFun_unramifiedChar, iwasawaExponent_mul_of_mem_integralGL F n g hk]
    rw [(HeckeAlgebraLevel.val_mem _ _ h k hk g).2]
  rw [sphericalEigen, integral_eq_smul_finsum_coset μ (integralOpen F n)
    (isCompact_integralGL F n) hf hK, Complex.real_smul]
  congr 1
  change (∑ᶠ x : GL (Fin n) F ⧸ integralGL F n,
    (h : HeckeAlgebra μ) x.out * sphericalFun (unramifiedChar w) x.out) = _
  rw [finsum_eq_sum_of_support_subset (s := cosetSupport h)]
  · simp only [sphericalFun_unramifiedChar]
  · intro x hx
    by_contra hxs
    exact hx (by simp [apply_out_eq_zero hxs])

variable (μ) in

def satake (h : SphericalHecke μ (F := F) (n := n)) : LaurentRing n :=
  (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) •
    ∑ x ∈ cosetSupport h, single (iwasawaExponent F n x.out) ((h : HeckeAlgebra μ) x.out)

/- English proof (translation)
Rewrite using `[satake]`. Use `congr 1`. Rewrite using `[Finset.sum_subset (Finset.subset_union_left (s₂ := S)) fun x _ hx => by`. Rewrite using `[apply_out_eq_zero hx, AddMonoidAlgebra.single_zero]]`. Conclude with `(Finset.sum_subset (Finset.subset_union_right (s₁ := cosetSupport h)) fun x _ hx => by`.

Rewrite using `[hS x hx, AddMonoidAlgebra.single_zero]).symm`.
-/
theorem satake_eq_sum (h : SphericalHecke μ (F := F) (n := n))
    (S : Finset (GL (Fin n) F ⧸ integralGL F n)) (hS : ∀ x ∉ S, (h : HeckeAlgebra μ) x.out = 0) :
    satake μ h = (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) •
      ∑ x ∈ S, single (iwasawaExponent F n x.out) ((h : HeckeAlgebra μ) x.out) := by
  classical
  rw [satake]
  congr 1
  rw [Finset.sum_subset (Finset.subset_union_left (s₂ := S)) fun x _ hx => by
      rw [apply_out_eq_zero hx, AddMonoidAlgebra.single_zero]]
  exact (Finset.sum_subset (Finset.subset_union_right (s₁ := cosetSupport h)) fun x _ hx => by
      rw [hS x hx, AddMonoidAlgebra.single_zero]).symm

/- English proof (translation)
Rewrite using `[sphericalCharacter_apply, satake, map_smul, map_sum, sphericalEigen_unramifiedChar, smul_eq_mul]`. Use `congr 1`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[evalAt_single]`.
-/
theorem evalAt_satake (w : Fin n → ℂˣ) (h : SphericalHecke μ (F := F) (n := n)) :
    evalAt w (satake μ h) = sphericalCharacter μ (isUnramified_unramifiedChar w) h := by
  rw [sphericalCharacter_apply, satake, map_smul, map_sum, sphericalEigen_unramifiedChar,
    smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [evalAt_single]

variable (μ) in

def satakeHom : SphericalHecke μ (F := F) (n := n) →ₐ[ℂ] LaurentRing n where
  toFun := satake μ
  map_one' := eq_of_forall_evalAt fun w => by simp only [evalAt_satake, map_one]
  map_mul' a b := eq_of_forall_evalAt fun w => by simp only [evalAt_satake, map_mul]
  map_zero' := eq_of_forall_evalAt fun w => by simp only [evalAt_satake, map_zero]
  map_add' a b := eq_of_forall_evalAt fun w => by simp only [evalAt_satake, map_add]
  commutes' c := eq_of_forall_evalAt fun w => by simp only [evalAt_satake, AlgHom.commutes]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem satakeHom_apply (h : SphericalHecke μ (F := F) (n := n)) : satakeHom μ h = satake μ h := rfl

/- English proof (translation)
The claim follows from `AlgHom.ext fun h => evalAt_satake w h`.
-/
theorem evalAt_comp_satakeHom (w : Fin n → ℂˣ) :
    (evalAt w).comp (satakeHom μ) = sphericalCharacter μ (isUnramified_unramifiedChar (F := F) w) :=
  AlgHom.ext fun h => evalAt_satake w h

end Spherical

end GroundTheory.Automorphic
