import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSelfStar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.IdealMulPrincipal

noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG NumberField
open scoped Matrix

section Form

variable {E : Type} [Field E] [StarRing E] {m : ℕ} (J : Matrix (Fin m) (Fin m) E)

/- English proof (translation)
Simplify using `[hform, map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem hform_add_left' (x x' y : Fin m → E) :
    hform (starRingEnd E) J (x + x') y = hform (starRingEnd E) J x y + hform (starRingEnd E) J x' y := by
  simp [hform, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[hform, mul_add, Finset.sum_add_distrib]`.
-/
theorem hform_add_right' (x y y' : Fin m → E) :
    hform (starRingEnd E) J x (y + y') = hform (starRingEnd E) J x y + hform (starRingEnd E) J x y' := by
  simp [hform, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Unfold `hform`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul, starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_smul_left' (c : E) (x y : Fin m → E) :
    hform (starRingEnd E) J (c • x) y = star c * hform (starRingEnd E) J x y := by
  unfold hform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, starRingEnd_apply]
  ring

/- English proof (translation)
Unfold `hform`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_smul_right' (c : E) (x y : Fin m → E) :
    hform (starRingEnd E) J x (c • y) = c * hform (starRingEnd E) J x y := by
  unfold hform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Establish `hJ' : ∀ i j, J i j = star (J j i)`. Introduce `i j`. Establish `h` using `congrFun (congrFun hJ i) j`. Simplify using `only [cT, Matrix.transpose_apply, Matrix.map_apply, starRingEnd_apply] at h`. Conclude with `h.symm`.

Unfold `hform`. Simplify using `only [starRingEnd_apply, star_sum, star_mul', star_star]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hJ' j i]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_swap' (hJ : IsHerm (starRingEnd E) J) (x y : Fin m → E) :
    hform (starRingEnd E) J y x = star (hform (starRingEnd E) J x y) := by
  have hJ' : ∀ i j, J i j = star (J j i) := by
    intro i j
    have h := congrFun (congrFun hJ i) j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, starRingEnd_apply] at h
    exact h.symm
  unfold hform
  simp only [starRingEnd_apply, star_sum, star_mul', star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ' j i]
  ring

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Set `f : (Fin m → E) →ₗ[E] E` to `{ toFun := fun y => hform (starRingEnd E) J x y map_add' := fun y y' => hform_add_right' J x y y' map_smul' := fun c y => by simpa using hform_smul_right' J c x y }`. Establish `hle : Submodule.span E S ≤ LinearMap.ker f`. Rewrite using `[Submodule.span_le]`.

Introduce `z hz`. Conclude with `LinearMap.mem_ker.mpr (h z hz)`. Establish `hall : ∀ y, hform (starRingEnd E) J x y = 0`. Introduce `y`. Establish `hy : y ∈ Submodule.span E S`.

Rewrite using `[hS]`. Conclude with `Submodule.mem_top`. Conclude with `LinearMap.mem_ker.mp (hle hy)`. Establish `hv : (fun i => starRingEnd E (x i)) ᵥ* J = 0`. Use function extensionality and compare the values at `j`.

Establish `hj` using `hall (Pi.single j 1)`. Simplify `hj` using `[hform, Matrix.vecMul, dotProduct, Pi.single_apply]`. Establish `hv0` using `Matrix.eq_zero_of_vecMul_eq_zero hdet hv`. Apply `hx` to reduce the goal to its premises. Use function extensionality and compare the values at `i`.

Establish `hi` using `congrFun hv0 i`. Simplify using `using hi`.
-/
theorem hform_exists_ne (hdet : J.det ≠ 0) (S : Set (Fin m → E)) (hS : Submodule.span E S = ⊤)
    {x : Fin m → E} (hx : x ≠ 0) : ∃ z ∈ S, hform (starRingEnd E) J x z ≠ 0 := by
  by_contra h
  push_neg at h
  let f : (Fin m → E) →ₗ[E] E :=
    { toFun := fun y => hform (starRingEnd E) J x y
      map_add' := fun y y' => hform_add_right' J x y y'
      map_smul' := fun c y => by simpa using hform_smul_right' J c x y }
  have hle : Submodule.span E S ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    intro z hz
    exact LinearMap.mem_ker.mpr (h z hz)
  have hall : ∀ y, hform (starRingEnd E) J x y = 0 := by
    intro y
    have hy : y ∈ Submodule.span E S := by
      rw [hS]
      exact Submodule.mem_top
    exact LinearMap.mem_ker.mp (hle hy)
  have hv : (fun i => starRingEnd E (x i)) ᵥ* J = 0 := by
    funext j
    have hj := hall (Pi.single j 1)
    simpa [hform, Matrix.vecMul, dotProduct, Pi.single_apply] using hj
  have hv0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
  apply hx
  funext i
  have hi := congrFun hv0 i
  simpa using hi

end Form

/- English proof (translation)
Establish `h : IsIntegral ℤ (algebraMap (𝓞 E) E q)` using `by first`. Consider the case `exact NumberField.RingOfIntegers.isIntegral_coe q`. Consider the case `exact q.2`. Establish `h2 : IsIntegral ℤ (star (algebraMap (𝓞 E) E q))`. Establish `h3` using `h.map (starRingEnd E).toIntAlgHom`.

Use `first`. Consider the case `exact h3`. Consider the case `simpa using h3`. Conclude with `⟨⟨_, h2⟩, rfl⟩`.
-/
theorem star_int {E : Type} [Field E] [NumberField E] [StarRing E] (q : 𝓞 E) :
    ∃ q' : 𝓞 E, algebraMap (𝓞 E) E q' = star (algebraMap (𝓞 E) E q) := by
  have h : IsIntegral ℤ (algebraMap (𝓞 E) E q) := by
    first
      | exact NumberField.RingOfIntegers.isIntegral_coe q
      | exact q.2
  have h2 : IsIntegral ℤ (star (algebraMap (𝓞 E) E q)) := by
    have h3 := h.map (starRingEnd E).toIntAlgHom
    first
      | exact h3
      | simpa using h3
  exact ⟨⟨_, h2⟩, rfl⟩

/- English proof (translation)
Establish `hN' : (N : 𝓞 F) ≠ 0`. Introduce `h`. Establish `h2` using `congrArg (algebraMap (𝓞 F) F) h`. Simplify using `only [map_natCast, map_zero, Nat.cast_eq_zero] at h2`. Use linear arithmetic over natural numbers and integers.

Establish `hI : Ideal.span {(N : 𝓞 F)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hN'`. Use `haveI : Finite (𝓞 F ⧸ Ideal.span {(N : 𝓞 F)}) := by first`. Consider the case `exact @Finite.of_fintype _ (Ideal.fintypeQuotientOfFreeOfNeBot _ hI)`.

Consider the case `exact Ideal.finiteQuotientOfFreeOfNeBot _ hI`. Use `⟨Set.range (Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {(N : 𝓞 F)}))), Set.finite_range _, ?_⟩` and prove the remaining obligations. Introduce `f`. Use `⟨_, Set.mem_range_self (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 F)}) f), ?_⟩` and prove the remaining obligations. Establish `h` using `Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := Ideal.span {(N : 𝓞 F)})) (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 F)}) f)`.

Rewrite `h` using `[Ideal.Quotient.eq]`. Take `⟨g, hg⟩` from `Ideal.mem_span_singleton'.mp h`. Use `⟨-g, ?_⟩` and prove the remaining obligations. Take the linear combination `hg`.
-/
private theorem exists_finite_residue_reps_mod_natCast (F : Type) [Field F] [NumberField F] (N : ℕ) (hN : 0 < N) :
    ∃ T : Set (𝓞 F), T.Finite ∧ ∀ f : 𝓞 F, ∃ r ∈ T, ∃ g : 𝓞 F, f = r + (N : 𝓞 F) * g := by
  have hN' : (N : 𝓞 F) ≠ 0 := by
    intro h
    have h2 := congrArg (algebraMap (𝓞 F) F) h
    simp only [map_natCast, map_zero, Nat.cast_eq_zero] at h2
    omega
  have hI : Ideal.span {(N : 𝓞 F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hN'
  haveI : Finite (𝓞 F ⧸ Ideal.span {(N : 𝓞 F)}) := by
    first
      | exact @Finite.of_fintype _ (Ideal.fintypeQuotientOfFreeOfNeBot _ hI)
      | exact Ideal.finiteQuotientOfFreeOfNeBot _ hI
  refine ⟨Set.range (Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {(N : 𝓞 F)}))),
    Set.finite_range _, ?_⟩
  intro f
  refine ⟨_, Set.mem_range_self (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 F)}) f), ?_⟩
  have h := Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := Ideal.span {(N : 𝓞 F)}))
    (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 F)}) f)
  rw [Ideal.Quotient.eq] at h
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp h
  refine ⟨-g, ?_⟩
  linear_combination hg

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hCM m d hd`. Take `⟨B, hB⟩` from `hIB E`. Establish `hreps : ∀ k : ℕ, ∃ T : Set (𝓞 F), T.Finite ∧ ∀ f : 𝓞 F, ∃ r ∈ T, ∃ g : 𝓞 F, f = r + ((2 * d * (k + 1) : ℕ) : 𝓞 F) * g` using `fun k => exists_finite_residue_reps_mod_natCast F _ (Nat.mul_pos (Nat.mul_pos (by norm_num) hd) k.succ_pos)`. Use `choose T hTf hT using hreps`. Use `⟨⋃ k ∈ Set.Iio B, (fun r : 𝓞 F => !![(0 : E), ((d * (k + 1) : ℕ) : E); ((d * (k + 1) : ℕ) : E), algebraMap F E (algebraMap (𝓞 F) F r)]) '' T k, ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `(Set.finite_Iio B).biUnion fun k _ => (hTf k).image _`. Introduce `Γ hΓ`. Simplify using `only [Set.mem_iUnion, Set.mem_image] at hΓ`. Take `⟨k, _, r, _, rfl⟩` from `hΓ`. Establish `ha : ((d * (k + 1) : ℕ) : E) ≠ 0`.

Rewrite using `[Ne, Nat.cast_eq_zero]`. Conclude with `(Nat.mul_pos hd k.succ_pos).ne'`. Rewrite using `[Matrix.det_fin_two_of]`. Introduce `h`. Apply `mul_ne_zero ha ha` to reduce the goal to its premises.

Take the linear combination `-h`. Introduce `p hp x hxM hx0 hxx`. Simplify using `only [Lat, Set.mem_setOf_eq] at hp`. Take `⟨hJ, hdet, -, hspan, hint, hdual⟩` from `hp`. Establish `hinj : Function.Injective (algebraMap (𝓞 E) E)` using `by first`.

Consider the case `exact NumberField.RingOfIntegers.coe_injective`. Consider the case `exact IsFractionRing.injective (𝓞 E) E`. Consider the case `exact NoZeroSMulDivisors.algebraMap_injective (𝓞 E) E`. Consider the case `exact FaithfulSMul.algebraMap_injective (𝓞 E) E`. Take `⟨I, hIdef⟩ : ∃ I : Ideal (𝓞 E), ∀ g, g ∈ I ↔ ∃ y ∈ p.2, algebraMap (𝓞 E) E g = hform (starRingEnd E) p.1 x y` from `⟨{ carrier := {g | ∃ y ∈ p.2, algebraMap (𝓞 E) E g = hform (starRingEnd E) p.1 x y} add_mem' := by`.

Introduce and unpack `g g' ⟨y, hy, hg⟩ ⟨y', hy', hg'⟩`. Conclude with `⟨y + y', p.2.add_mem hy hy', by rw [map_add, hg, hg', hform_add_right']⟩`. Use the proof step `zero_mem' := ⟨0, p.2.zero_mem, by simp [hform]⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `r g ⟨y, hy, hg⟩`.

Use `⟨r • y, p.2.smul_mem r hy, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_mul, map_mul, hg, ← algebraMap_smul E r y, hform_smul_right'] },`. Use `fun g => Iff.rfl⟩`. Take `⟨z, hzM, hz⟩` from `hform_exists_ne p.1 hdet (p.2 : Set (Fin m → E)) hspan hx0`. Take `⟨g0, hg0⟩` from `hint x hxM z hzM`.

Establish `hI : I ≠ ⊥`. Introduce `hbot`. Establish `hmem : g0 ∈ I` using `(hIdef g0).mpr ⟨z, hzM, hg0⟩`. Rewrite `hmem` using `[hbot, Ideal.mem_bot]`. Apply `hz` to reduce the goal to its premises.

Rewrite using `[← hg0, hmem, map_zero]`. Take `⟨c, hcI, hc0, e, he1, heB, hdiv⟩` from `hB I hI`. Take `⟨y0, hy0M, hc⟩` from `(hIdef c).mp hcI`. Take `⟨k, rfl⟩ : ∃ k, e = k + 1` from `⟨e - 1, by omega⟩`. Establish `hc' : algebraMap (𝓞 E) E c ≠ 0` using `fun h => hc0 (hinj (by rw [h, map_zero]))`.

Establish `hsc : star (algebraMap (𝓞 E) E c) ≠ 0` using `star_ne_zero.mpr hc'`. Take `⟨t, ht⟩ : ∃ t : E, t * star (algebraMap (𝓞 E) E c) = ((k + 1 : ℕ) : E)` from `⟨_, div_mul_cancel₀ _ hsc⟩`. Establish `hts : star t * algebraMap (𝓞 E) E c = ((k + 1 : ℕ) : E)`. Establish `h` using `congrArg star ht`. Simplify `h` using `only [star_mul', star_star, star_natCast]`.

Establish `hw : ∀ z' ∈ p.2, hform (starRingEnd E) p.1 z' (t • x) ∈ (algebraMap (𝓞 E) E).range`. Introduce `z' hz'`. Take `⟨gz, hgz⟩` from `hint x hxM z' hz'`. Take `⟨q, hq⟩` from `hdiv gz ((hIdef gz).mpr ⟨z', hz', hgz⟩)`. Establish `hq' : ((k + 1 : ℕ) : E) * hform (starRingEnd E) p.1 x z' = algebraMap (𝓞 E) E c * algebraMap (𝓞 E) E q`.

Establish `h` using `congrArg (algebraMap (𝓞 E) E) hq`. Rewrite `h` using `[map_mul, map_mul, map_natCast, hgz]`. Conclude with `h`. Establish `E1 : ((k + 1 : ℕ) : E) * star (hform (starRingEnd E) p.1 x z') = star (algebraMap (𝓞 E) E c) * star (algebraMap (𝓞 E) E q)`. Establish `h` using `congrArg star hq'`.

Simplify `h` using `only [star_mul', star_natCast]`. Take `⟨q', hq''⟩` from `star_int q`. Use `⟨q', ?_⟩` and prove the remaining obligations. Rewrite using `[hq'', hform_smul_right', hform_swap' p.1 hJ x z']`. Apply `mul_left_cancel₀ hsc` to reduce the goal to its premises.

Take the linear combination `-E1 - star (hform (starRingEnd E) p.1 x z') * ht`. Establish `hv0M : (d : E) • (t • x) ∈ p.2` using `hdual (t • x) hw`. Establish `hv00 : hform (starRingEnd E) p.1 ((d : E) • (t • x)) ((d : E) • (t • x)) = 0`. Rewrite using `[hform_smul_left', hform_smul_left', hform_smul_right', hform_smul_right', hxx]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hv0y : hform (starRingEnd E) p.1 ((d : E) • (t • x)) y0 = ((d * (k + 1) : ℕ) : E)`. Rewrite using `[hform_smul_left', hform_smul_left', ← hc, hts, star_natCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Generalize the expression as in `(d : E) • (t • x) = v0 at hv0M hv00 hv0y`.

Take `⟨β, hβ⟩` from `hint y0 hy0M y0 hy0M`. Establish `hbstar : star (hform (starRingEnd E) p.1 y0 y0) = hform (starRingEnd E) p.1 y0 y0` using `(hform_swap' p.1 hJ y0 y0).symm`. Take `⟨f, hf⟩` from `(hCM.fixed _).mp hbstar`. Establish `hβint : IsIntegral ℤ (algebraMap (𝓞 E) E β)` using `by first`. Consider the case `exact NumberField.RingOfIntegers.isIntegral_coe β`.

Consider the case `exact β.2`. Establish `hfint : IsIntegral ℤ f`. Rewrite `hβint` using `[hβ, ← hf]`. Conclude with `(isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).mp hβint`. Take `⟨r, hrT, g, hfg⟩` from `hT k ⟨f, hfint⟩`.

Establish `hgint : IsIntegral ℤ (algebraMap F E (algebraMap (𝓞 F) F g))`. Establish `h1 : IsIntegral ℤ (algebraMap (𝓞 F) F g)` using `by first`. Consider the case `exact NumberField.RingOfIntegers.isIntegral_coe g`. Consider the case `exact g.2`. Conclude with `h1.map (algebraMap F E).toIntAlgHom`.

Take `⟨sE, hsE⟩ : ∃ sE : 𝓞 E, algebraMap (𝓞 E) E sE = -(algebraMap F E (algebraMap (𝓞 F) F g))` from `⟨⟨_, hgint.neg⟩, rfl⟩`. Establish `hsstar : star (algebraMap (𝓞 E) E sE) = algebraMap (𝓞 E) E sE`. Rewrite using `[hsE, star_neg, (hCM.fixed (algebraMap F E (algebraMap (𝓞 F) F g))).mpr ⟨_, rfl⟩]`. Establish `hv1M : y0 + sE • v0 ∈ p.2` using `p.2.add_mem hy0M (p.2.smul_mem sE hv0M)`. Establish `hsm : sE • v0 = (algebraMap (𝓞 E) E sE) • v0` using `(algebraMap_smul E sE v0).symm`.

Establish `hyv0 : hform (starRingEnd E) p.1 y0 v0 = ((d * (k + 1) : ℕ) : E)`. Rewrite using `[hform_swap' p.1 hJ v0 y0, hv0y, star_natCast]`. Establish `h01 : hform (starRingEnd E) p.1 v0 (y0 + sE • v0) = ((d * (k + 1) : ℕ) : E)`. Rewrite using `[hsm, hform_add_right', hform_smul_right', hv0y, hv00]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h10 : hform (starRingEnd E) p.1 (y0 + sE • v0) v0 = ((d * (k + 1) : ℕ) : E)`. Rewrite using `[hsm, hform_add_left', hform_smul_left', hyv0, hv00]`. Expand and normalize the polynomial expressions, which then agree. Establish `hfg' : f = algebraMap (𝓞 F) F r + ((2 * d * (k + 1) : ℕ) : F) * algebraMap (𝓞 F) F g`. Establish `h` using `congrArg (algebraMap (𝓞 F) F) hfg`.

Rewrite `h` using `[map_add, map_mul, map_natCast]`. Conclude with `h`. Establish `h11 : hform (starRingEnd E) p.1 (y0 + sE • v0) (y0 + sE • v0) = algebraMap F E (algebraMap (𝓞 F) F r)`. Rewrite using `[hsm]`. Simplify using `only [hform_add_left', hform_add_right', hform_smul_left', hform_smul_right']`.

Rewrite using `[hyv0, hv0y, hv00, hsstar, ← hf, hfg', hsE, map_add, map_mul, map_natCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨![v0, y0 + sE • v0], ?_, ?_⟩` and prove the remaining obligations. Introduce `i fin_cases i`.

Simplify using `using hv0M`. Simplify using `using hv1M`. Simplify using `only [Set.mem_iUnion, Set.mem_image]`. Use `⟨k, Set.mem_Iio.mpr (by omega), r, hrT, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [gram, h01, h10, h11, hv00]`.
-/
theorem partIso_of (hIB : IdealBoundAll) : PartIso := by
  intro F E _ _ _ _ _ _ hCM m d hd
  obtain ⟨B, hB⟩ := hIB E
  have hreps : ∀ k : ℕ, ∃ T : Set (𝓞 F), T.Finite ∧
      ∀ f : 𝓞 F, ∃ r ∈ T, ∃ g : 𝓞 F, f = r + ((2 * d * (k + 1) : ℕ) : 𝓞 F) * g :=
    fun k => exists_finite_residue_reps_mod_natCast F _ (Nat.mul_pos (Nat.mul_pos (by norm_num) hd) k.succ_pos)
  choose T hTf hT using hreps
  refine ⟨⋃ k ∈ Set.Iio B, (fun r : 𝓞 F => !![(0 : E), ((d * (k + 1) : ℕ) : E);
      ((d * (k + 1) : ℕ) : E), algebraMap F E (algebraMap (𝓞 F) F r)]) '' T k, ?_, ?_, ?_⟩
  · exact (Set.finite_Iio B).biUnion fun k _ => (hTf k).image _
  · intro Γ hΓ
    simp only [Set.mem_iUnion, Set.mem_image] at hΓ
    obtain ⟨k, _, r, _, rfl⟩ := hΓ
    have ha : ((d * (k + 1) : ℕ) : E) ≠ 0 := by
      rw [Ne, Nat.cast_eq_zero]
      exact (Nat.mul_pos hd k.succ_pos).ne'
    rw [Matrix.det_fin_two_of]
    intro h
    apply mul_ne_zero ha ha
    linear_combination -h
  · intro p hp x hxM hx0 hxx
    simp only [Lat, Set.mem_setOf_eq] at hp
    obtain ⟨hJ, hdet, -, hspan, hint, hdual⟩ := hp
    have hinj : Function.Injective (algebraMap (𝓞 E) E) := by
      first
        | exact NumberField.RingOfIntegers.coe_injective
        | exact IsFractionRing.injective (𝓞 E) E
        | exact NoZeroSMulDivisors.algebraMap_injective (𝓞 E) E
        | exact FaithfulSMul.algebraMap_injective (𝓞 E) E
    obtain ⟨I, hIdef⟩ : ∃ I : Ideal (𝓞 E), ∀ g, g ∈ I ↔
        ∃ y ∈ p.2, algebraMap (𝓞 E) E g = hform (starRingEnd E) p.1 x y :=
      ⟨{ carrier := {g | ∃ y ∈ p.2, algebraMap (𝓞 E) E g = hform (starRingEnd E) p.1 x y}
         add_mem' := by
           rintro g g' ⟨y, hy, hg⟩ ⟨y', hy', hg'⟩
           exact ⟨y + y', p.2.add_mem hy hy', by rw [map_add, hg, hg', hform_add_right']⟩
         zero_mem' := ⟨0, p.2.zero_mem, by simp [hform]⟩
         smul_mem' := by
           rintro r g ⟨y, hy, hg⟩
           refine ⟨r • y, p.2.smul_mem r hy, ?_⟩
           rw [smul_eq_mul, map_mul, hg, ← algebraMap_smul E r y, hform_smul_right'] },
        fun g => Iff.rfl⟩
    obtain ⟨z, hzM, hz⟩ := hform_exists_ne p.1 hdet (p.2 : Set (Fin m → E)) hspan hx0
    obtain ⟨g0, hg0⟩ := hint x hxM z hzM
    have hI : I ≠ ⊥ := by
      intro hbot
      have hmem : g0 ∈ I := (hIdef g0).mpr ⟨z, hzM, hg0⟩
      rw [hbot, Ideal.mem_bot] at hmem
      apply hz
      rw [← hg0, hmem, map_zero]
    obtain ⟨c, hcI, hc0, e, he1, heB, hdiv⟩ := hB I hI
    obtain ⟨y0, hy0M, hc⟩ := (hIdef c).mp hcI
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    have hc' : algebraMap (𝓞 E) E c ≠ 0 := fun h => hc0 (hinj (by rw [h, map_zero]))
    have hsc : star (algebraMap (𝓞 E) E c) ≠ 0 := star_ne_zero.mpr hc'
    obtain ⟨t, ht⟩ : ∃ t : E, t * star (algebraMap (𝓞 E) E c) = ((k + 1 : ℕ) : E) :=
      ⟨_, div_mul_cancel₀ _ hsc⟩
    have hts : star t * algebraMap (𝓞 E) E c = ((k + 1 : ℕ) : E) := by
      have h := congrArg star ht
      simpa only [star_mul', star_star, star_natCast] using h
    have hw : ∀ z' ∈ p.2, hform (starRingEnd E) p.1 z' (t • x) ∈ (algebraMap (𝓞 E) E).range := by
      intro z' hz'
      obtain ⟨gz, hgz⟩ := hint x hxM z' hz'
      obtain ⟨q, hq⟩ := hdiv gz ((hIdef gz).mpr ⟨z', hz', hgz⟩)
      have hq' : ((k + 1 : ℕ) : E) * hform (starRingEnd E) p.1 x z' =
          algebraMap (𝓞 E) E c * algebraMap (𝓞 E) E q := by
        have h := congrArg (algebraMap (𝓞 E) E) hq
        rw [map_mul, map_mul, map_natCast, hgz] at h
        exact h
      have E1 : ((k + 1 : ℕ) : E) * star (hform (starRingEnd E) p.1 x z') =
          star (algebraMap (𝓞 E) E c) * star (algebraMap (𝓞 E) E q) := by
        have h := congrArg star hq'
        simpa only [star_mul', star_natCast] using h
      obtain ⟨q', hq''⟩ := star_int q
      refine ⟨q', ?_⟩
      rw [hq'', hform_smul_right', hform_swap' p.1 hJ x z']
      apply mul_left_cancel₀ hsc
      linear_combination -E1 - star (hform (starRingEnd E) p.1 x z') * ht
    have hv0M : (d : E) • (t • x) ∈ p.2 := hdual (t • x) hw
    have hv00 : hform (starRingEnd E) p.1 ((d : E) • (t • x)) ((d : E) • (t • x)) = 0 := by
      rw [hform_smul_left', hform_smul_left', hform_smul_right', hform_smul_right', hxx]
      ring
    have hv0y : hform (starRingEnd E) p.1 ((d : E) • (t • x)) y0 = ((d * (k + 1) : ℕ) : E) := by
      rw [hform_smul_left', hform_smul_left', ← hc, hts, star_natCast]
      push_cast
      ring
    generalize (d : E) • (t • x) = v0 at hv0M hv00 hv0y
    obtain ⟨β, hβ⟩ := hint y0 hy0M y0 hy0M
    have hbstar : star (hform (starRingEnd E) p.1 y0 y0) = hform (starRingEnd E) p.1 y0 y0 :=
      (hform_swap' p.1 hJ y0 y0).symm
    obtain ⟨f, hf⟩ := (hCM.fixed _).mp hbstar
    have hβint : IsIntegral ℤ (algebraMap (𝓞 E) E β) := by
      first
        | exact NumberField.RingOfIntegers.isIntegral_coe β
        | exact β.2
    have hfint : IsIntegral ℤ f := by
      rw [hβ, ← hf] at hβint
      exact (isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).mp hβint
    obtain ⟨r, hrT, g, hfg⟩ := hT k ⟨f, hfint⟩
    have hgint : IsIntegral ℤ (algebraMap F E (algebraMap (𝓞 F) F g)) := by
      have h1 : IsIntegral ℤ (algebraMap (𝓞 F) F g) := by
        first
          | exact NumberField.RingOfIntegers.isIntegral_coe g
          | exact g.2
      exact h1.map (algebraMap F E).toIntAlgHom
    obtain ⟨sE, hsE⟩ : ∃ sE : 𝓞 E,
        algebraMap (𝓞 E) E sE = -(algebraMap F E (algebraMap (𝓞 F) F g)) := ⟨⟨_, hgint.neg⟩, rfl⟩
    have hsstar : star (algebraMap (𝓞 E) E sE) = algebraMap (𝓞 E) E sE := by
      rw [hsE, star_neg, (hCM.fixed (algebraMap F E (algebraMap (𝓞 F) F g))).mpr ⟨_, rfl⟩]
    have hv1M : y0 + sE • v0 ∈ p.2 := p.2.add_mem hy0M (p.2.smul_mem sE hv0M)
    have hsm : sE • v0 = (algebraMap (𝓞 E) E sE) • v0 := (algebraMap_smul E sE v0).symm
    have hyv0 : hform (starRingEnd E) p.1 y0 v0 = ((d * (k + 1) : ℕ) : E) := by
      rw [hform_swap' p.1 hJ v0 y0, hv0y, star_natCast]
    have h01 : hform (starRingEnd E) p.1 v0 (y0 + sE • v0) = ((d * (k + 1) : ℕ) : E) := by
      rw [hsm, hform_add_right', hform_smul_right', hv0y, hv00]
      ring
    have h10 : hform (starRingEnd E) p.1 (y0 + sE • v0) v0 = ((d * (k + 1) : ℕ) : E) := by
      rw [hsm, hform_add_left', hform_smul_left', hyv0, hv00]
      ring
    have hfg' : f = algebraMap (𝓞 F) F r + ((2 * d * (k + 1) : ℕ) : F) * algebraMap (𝓞 F) F g := by
      have h := congrArg (algebraMap (𝓞 F) F) hfg
      rw [map_add, map_mul, map_natCast] at h
      exact h
    have h11 : hform (starRingEnd E) p.1 (y0 + sE • v0) (y0 + sE • v0) =
        algebraMap F E (algebraMap (𝓞 F) F r) := by
      rw [hsm]
      simp only [hform_add_left', hform_add_right', hform_smul_left', hform_smul_right']
      rw [hyv0, hv0y, hv00, hsstar, ← hf, hfg', hsE, map_add, map_mul, map_natCast]
      push_cast
      ring
    refine ⟨![v0, y0 + sE • v0], ?_, ?_⟩
    · intro i
      fin_cases i
      · simpa using hv0M
      · simpa using hv1M
    · simp only [Set.mem_iUnion, Set.mem_image]
      refine ⟨k, Set.mem_Iio.mpr (by omega), r, hrT, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [gram, h01, h10, h11, hv00]

end PIW.AdelClassFin
