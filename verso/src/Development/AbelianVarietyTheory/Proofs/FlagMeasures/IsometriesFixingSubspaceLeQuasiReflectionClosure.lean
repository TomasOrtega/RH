import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeOfPerpEqBot

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.QReflGen

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Simplify using `[hf, add_mul, Finset.sum_add_distrib]`.
-/
theorem hf_add_l (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[hf, Finset.mul_sum, mul_assoc]`.
-/
theorem hf_smul_l (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L Hm (c • a) y = c * hf L Hm a y := by
  simp [hf, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `[hf, mul_add, Finset.sum_add_distrib]`.
-/
theorem hf_add_r (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L Hm y (a + b) = hf L Hm y a + hf L Hm y b := by
  simp [hf, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem hf_smul_r (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L Hm y (c • a) = L.cj c * hf L Hm y a := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Establish `h' : ∀ i j, L.cj (Hm i j) = Hm j i` using `fun i j => congrFun (congrFun h j) i`. Simplify using `only [hf, map_sum, map_mul, h', L.cj_cj]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem hf_cj (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (x y : Fin n → E) : L.cj (hf L Hm x y) = hf L Hm y x := by
  have h' : ∀ i j, L.cj (Hm i j) = Hm j i := fun i j => congrFun (congrFun h j) i
  simp only [hf, map_sum, map_mul, h', L.cj_cj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Set `g : (Fin n → E) ≃ₗ[E] (Fin n → E)` to `{ toFun := fun v => v + (c * hf L Hm v a) • a invFun := fun v => v + (L.cj c * hf L Hm v a) • a map_add' := by`. Introduce `v w`. Rewrite using `[hf_add_l]`. Use `module`. Use the proof step `map_smul' := by`.

Introduce `r v`. Rewrite using `[hf_smul_l]`. Simplify using `only [RingHom.id_apply]`. Use `module`. Use `left_inv := by`.

Introduce `v`. Simplify using `only [hf_add_l, hf_smul_l]`. Rewrite using `[add_assoc, ← add_smul]`. Establish `: c * hf L Hm v a + L.cj c * (hf L Hm v a + c * hf L Hm v a * hf L Hm a a) = 0`. Take the linear combination `hf L Hm v a * hc`.

Rewrite using `[this]`. Simplify using the standard rewrite rules. Use `right_inv := by`. Introduce `v`. Simplify using `only [hf_add_l, hf_smul_l]`.

Rewrite using `[add_assoc, ← add_smul]`. Establish `: L.cj c * hf L Hm v a + c * (hf L Hm v a + L.cj c * hf L Hm v a * hf L Hm a a) = 0`. Take the linear combination `hf L Hm v a * hc`. Rewrite using `[this]`. Simplify using `}`.

Use `⟨g, ⟨ha, ?_, c, fun v => rfl⟩, fun v => rfl⟩` and prove the remaining obligations. Introduce `v w`. Express the relevant statement in the definitionally equal form `hf L Hm (v + (c * hf L Hm v a) • a) (w + (c * hf L Hm w a) • a) = _`. Simplify using `only [hf_add_l, hf_add_r, hf_smul_l, hf_smul_r, map_mul, hf_cj L h]`. Take the linear combination `hf L Hm v a * hf L Hm a w * hc`.
-/
theorem exists_qrefl (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (a : Fin n → E) (ha : IsUnit (hf L Hm a a)) (c : E)
    (hc : c + L.cj c + c * L.cj c * hf L Hm a a = 0) :
    ∃ g, IsQRefl L Hm a g ∧ ∀ v, g v = v + (c * hf L Hm v a) • a := by
  let g : (Fin n → E) ≃ₗ[E] (Fin n → E) :=
    { toFun := fun v => v + (c * hf L Hm v a) • a
      invFun := fun v => v + (L.cj c * hf L Hm v a) • a
      map_add' := by
        intro v w
        rw [hf_add_l]; module
      map_smul' := by
        intro r v
        rw [hf_smul_l]; simp only [RingHom.id_apply]; module
      left_inv := by
        intro v
        simp only [hf_add_l, hf_smul_l]
        rw [add_assoc, ← add_smul]
        have : c * hf L Hm v a + L.cj c * (hf L Hm v a + c * hf L Hm v a * hf L Hm a a) = 0 := by
          linear_combination hf L Hm v a * hc
        rw [this]; simp
      right_inv := by
        intro v
        simp only [hf_add_l, hf_smul_l]
        rw [add_assoc, ← add_smul]
        have : L.cj c * hf L Hm v a + c * (hf L Hm v a + L.cj c * hf L Hm v a * hf L Hm a a) = 0 := by
          linear_combination hf L Hm v a * hc
        rw [this]; simp }
  refine ⟨g, ⟨ha, ?_, c, fun v => rfl⟩, fun v => rfl⟩
  intro v w
  change hf L Hm (v + (c * hf L Hm v a) • a) (w + (c * hf L Hm w a) • a) = _
  simp only [hf_add_l, hf_add_r, hf_smul_l, hf_smul_r, map_mul, hf_cj L h]
  linear_combination hf L Hm v a * hf L Hm a w * hc

/- English proof (translation)
Take `⟨a, rfl⟩` from `(L.cj_fix z).1 hz`. Establish `: a ≠ 0` using `by rintro rfl; simp at h0`. Conclude with `(IsUnit.mk0 a this).map _`.
-/
theorem unit_of_fix (L : LocE F E) {z : E} (hz : L.cj z = z) (h0 : z ≠ 0) : IsUnit z := by
  obtain ⟨a, rfl⟩ := (L.cj_fix z).1 hz
  have : a ≠ 0 := by rintro rfl; simp at h0
  exact (IsUnit.mk0 a this).map _

/- English proof (translation)
Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nontrivial_iff_subsingleton]`. Use `L.rank` as an intermediate fact. Rewrite `this` using `[Module.finrank_zero_of_subsingleton]`. Use linear arithmetic over natural numbers and integers.
-/
theorem nontriv (L : LocE F E) : Nontrivial E := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have := L.rank
  rw [Module.finrank_zero_of_subsingleton] at this
  omega

/- English proof (translation)
Establish `h1 : ∃ z : E, L.cj z ≠ z`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hs : Function.Surjective (Algebra.linearMap F E)` using `fun z => (L.cj_fix z).1 (h z)`. Use `LinearMap.finrank_le_finrank_of_surjective hs` as an intermediate fact.

Rewrite `this` using `[L.rank, Module.finrank_self]`. Use linear arithmetic over natural numbers and integers. Take `⟨z, hz⟩` from `h1`. Establish `hδ : L.cj (z - L.cj z) = -(z - L.cj z)` using `by simp [L.cj_cj]`. Take `⟨D, hD⟩` from `(L.cj_fix ((z - L.cj z) * (z - L.cj z))).1 (by rw [map_mul, hδ]; ring)`.

Use `⟨z - L.cj z, D, ?_, hδ, hD.symm⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Use `haveI := L.reduced`. Establish `: z - L.cj z = 0` using `IsNilpotent.eq_zero ⟨2, by rw [pow_two, ← hD]; simp⟩`. Conclude with `hz (sub_eq_zero.1 this).symm`.
-/
theorem exists_skew (L : LocE F E) :
    ∃ (δ : E) (D : F), D ≠ 0 ∧ L.cj δ = -δ ∧ δ * δ = algebraMap F E D := by
  have h1 : ∃ z : E, L.cj z ≠ z := by
    by_contra h
    push_neg at h
    have hs : Function.Surjective (Algebra.linearMap F E) := fun z => (L.cj_fix z).1 (h z)
    have := LinearMap.finrank_le_finrank_of_surjective hs
    rw [L.rank, Module.finrank_self] at this
    omega
  obtain ⟨z, hz⟩ := h1
  have hδ : L.cj (z - L.cj z) = -(z - L.cj z) := by simp [L.cj_cj]
  obtain ⟨D, hD⟩ := (L.cj_fix ((z - L.cj z) * (z - L.cj z))).1 (by rw [map_mul, hδ]; ring)
  refine ⟨z - L.cj z, D, ?_, hδ, hD.symm⟩
  rintro rfl
  haveI := L.reduced
  have : z - L.cj z = 0 := IsNilpotent.eq_zero ⟨2, by rw [pow_two, ← hD]; simp⟩
  exact hz (sub_eq_zero.1 this).symm

/- English proof (translation)
Establish `hp : (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c) ≠ 0`. Introduce `h0`. Apply `h` to reduce the goal to its premises. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using congrArg (fun p => Polynomial.coeff p 2) h0`.

Simplify using `using congrArg (fun p => Polynomial.coeff p 1) h0`. Simplify using `using congrArg (fun p => Polynomial.coeff p 0) h0`. Use `Polynomial.finite_setOf_isRoot hp` as an intermediate fact. Simplify `this` using `[Polynomial.IsRoot]`.
-/
theorem quad_finite {K : Type} [Field K] (a b c : K) (h : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) :
    {r : K | a * r ^ 2 + b * r + c = 0}.Finite := by
  have hp : (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c) ≠ 0 := by
    intro h0
    apply h
    refine ⟨?_, ?_, ?_⟩
    · simpa using congrArg (fun p => Polynomial.coeff p 2) h0
    · simpa using congrArg (fun p => Polynomial.coeff p 1) h0
    · simpa using congrArg (fun p => Polynomial.coeff p 0) h0
  have := Polynomial.finite_setOf_isRoot hp
  simpa [Polynomial.IsRoot] using this

/- English proof (translation)
Use `haveI := nontriv L`. Take `⟨δ, D, hD, hδ, hδ2⟩` from `exists_skew L`. Take `⟨τ, rfl⟩` from `(L.cj_fix t).1 htc`. Establish `hτ : τ ≠ 0` using `by rintro rfl; simp at ht`. Take `⟨A, hA⟩` from `(L.cj_fix (s + L.cj s)).1 (by simp [L.cj_cj, add_comm])`.

Take `⟨B, hB⟩` from `(L.cj_fix (δ * (s - L.cj s))).1 (by simp [L.cj_cj, hδ]; ring)`. Take `⟨N, hN⟩` from `(L.cj_fix (s * L.cj s)).1 (by simp [L.cj_cj, mul_comm])`. Establish `inj : Function.Injective (algebraMap F E)` using `(algebraMap F E).injective`. Establish `hrel : D * A ^ 2 - B ^ 2 = 4 * D * N`. Apply `inj` to reduce the goal to its premises.

Simplify using `only [map_sub, map_mul, map_pow, map_ofNat, hA, hB, hN, ← hδ2]`. Expand and normalize the polynomial expressions, which then agree. Establish `f1` using `quad_finite (1 : F) 0 (-D) (by simp)`. Establish `f2` using `quad_finite (A - 2 * τ) (-2 * B) (D * (A + 2 * τ)) (by`. Introduce and unpack `⟨h1, -, h3⟩`.

Establish `h4` using `(mul_eq_zero.1 h3).resolve_left hD`. Apply `hτ` to reduce the goal to its premises. Take the linear combination `(1 / 4 : F) * (h4 - h1))`. Establish `f3` using `quad_finite (τ * A - (τ ^ 2 + N)) (-2 * τ * B) (D * (τ * A + (τ ^ 2 + N))) (by`. Introduce and unpack `⟨h1, h2, h3⟩`.

Establish `h4` using `(mul_eq_zero.1 h3).resolve_left hD`. Establish `hA0 : A = 0`. Establish `: τ * A = 0` using `by linear_combination (1 / 2 : F) * (h4 + h1)`. Conclude with `(mul_eq_zero.1 this).resolve_left hτ`. Establish `hB0 : B = 0`.

Establish `: τ * B = 0` using `by linear_combination (-1 / 2 : F) * h2`. Conclude with `(mul_eq_zero.1 this).resolve_left hτ`. Establish `hN0 : N = 0`. Establish `: D * N = 0` using `by rw [hA0, hB0] at hrel; linear_combination (-1 / 4 : F) * hrel`. Conclude with `(mul_eq_zero.1 this).resolve_left hD`.

Apply `hτ` to reduce the goal to its premises. Establish `: τ ^ 2 = 0` using `by rw [hA0, hN0] at h1; linear_combination -h1`. Conclude with `pow_eq_zero_iff (two_ne_zero) |>.1 this)`. Take `⟨r, hr⟩` from `((f1.union f2).union f3).exists_notMem`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or] at hr`.

Take `⟨⟨r1, r2⟩, r3⟩` from `hr`. Establish `r1' : r ^ 2 - D ≠ 0` using `fun h => r1 (by linear_combination h)`. Use `set e : F := (r ^ 2 - D)⁻¹ with he`. Establish `he1 : e * (r ^ 2 - D) = 1` using `inv_mul_cancel₀ r1'`. Establish `he2 : algebraMap F E e * (algebraMap F E r ^ 2 - δ * δ) = 1`.

Rewrite using `[hδ2, ← map_pow, ← map_sub, ← map_mul, he1, map_one]`. Use `set u : E := algebraMap F E e * (algebraMap F E r + δ) ^ 2 with hu`. Establish `hcu : L.cj u = algebraMap F E e * (algebraMap F E r - δ) ^ 2`. Simplify using `[hu, hδ, sub_eq_add_neg]`. Establish `huu : u * L.cj u = 1`.

Rewrite using `[hcu, hu]`. Take the linear combination `(algebraMap F E e * (algebraMap F E r ^ 2 - δ * δ) + 1) * he2`. Establish `hT : L.cj u * s + u * L.cj s = algebraMap F E (e * ((r ^ 2 + D) * A - 2 * r * B))`. Rewrite using `[hcu, hu]`. Simplify using `only [map_sub, map_add, map_mul, map_pow, map_ofNat, hA, hB, ← hδ2]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hcb : L.cj (algebraMap F E τ - L.cj u * s) = algebraMap F E τ - u * L.cj s`. Simplify using `[L.cj_cj]`. Use `clear_value u`. Use `⟨u, huu, ?_, ?_⟩` and prove the remaining obligations.

Establish `: (algebraMap F E τ - L.cj u * s) * (algebraMap F E τ - u * L.cj s) = algebraMap F E (τ ^ 2 + N - τ * (e * ((r ^ 2 + D) * A - 2 * r * B)))`. Rewrite using `[map_sub, map_add, map_mul (algebraMap F E), ← hT, hN, map_pow]`. Take the linear combination `s * L.cj s * huu`. Use `isUnit_of_mul_isUnit_left (y := algebraMap F E τ - u * L.cj s) ?_` and prove the remaining obligations. Rewrite using `[this]`.

Use `(IsUnit.mk0 _ fun h => r3 ?_).map _` and prove the remaining obligations. Take the linear combination `(-(r ^ 2 - D)) * h - τ * ((r ^ 2 + D) * A - 2 * r * B) * he1`. Establish `: (algebraMap F E τ - L.cj u * s) + (algebraMap F E τ - u * L.cj s) = algebraMap F E (2 * τ - (e * ((r ^ 2 + D) * A - 2 * r * B)))`. Rewrite using `[map_sub, map_mul (algebraMap F E), ← hT, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hcb, this]`. Use `(IsUnit.mk0 _ fun h => r2 ?_).map _` and prove the remaining obligations. Take the linear combination `(-(r ^ 2 - D)) * h - ((r ^ 2 + D) * A - 2 * r * B) * he1`.
-/
theorem exists_norm_one [CharZero F] (L : LocE F E) (t s : E) (ht : IsUnit t) (htc : L.cj t = t) :
    ∃ u : E, u * L.cj u = 1 ∧ IsUnit (t - L.cj u * s) ∧
      IsUnit ((t - L.cj u * s) + L.cj (t - L.cj u * s)) := by
  haveI := nontriv L
  obtain ⟨δ, D, hD, hδ, hδ2⟩ := exists_skew L
  obtain ⟨τ, rfl⟩ := (L.cj_fix t).1 htc
  have hτ : τ ≠ 0 := by rintro rfl; simp at ht
  obtain ⟨A, hA⟩ := (L.cj_fix (s + L.cj s)).1 (by simp [L.cj_cj, add_comm])
  obtain ⟨B, hB⟩ := (L.cj_fix (δ * (s - L.cj s))).1 (by simp [L.cj_cj, hδ]; ring)
  obtain ⟨N, hN⟩ := (L.cj_fix (s * L.cj s)).1 (by simp [L.cj_cj, mul_comm])
  have inj : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  have hrel : D * A ^ 2 - B ^ 2 = 4 * D * N := by
    apply inj
    simp only [map_sub, map_mul, map_pow, map_ofNat, hA, hB, hN, ← hδ2]
    ring
  have f1 := quad_finite (1 : F) 0 (-D) (by simp)
  have f2 := quad_finite (A - 2 * τ) (-2 * B) (D * (A + 2 * τ)) (by
    rintro ⟨h1, -, h3⟩
    have h4 := (mul_eq_zero.1 h3).resolve_left hD
    apply hτ
    linear_combination (1 / 4 : F) * (h4 - h1))
  have f3 := quad_finite (τ * A - (τ ^ 2 + N)) (-2 * τ * B) (D * (τ * A + (τ ^ 2 + N))) (by
    rintro ⟨h1, h2, h3⟩
    have h4 := (mul_eq_zero.1 h3).resolve_left hD
    have hA0 : A = 0 := by
      have : τ * A = 0 := by linear_combination (1 / 2 : F) * (h4 + h1)
      exact (mul_eq_zero.1 this).resolve_left hτ
    have hB0 : B = 0 := by
      have : τ * B = 0 := by linear_combination (-1 / 2 : F) * h2
      exact (mul_eq_zero.1 this).resolve_left hτ
    have hN0 : N = 0 := by
      have : D * N = 0 := by rw [hA0, hB0] at hrel; linear_combination (-1 / 4 : F) * hrel
      exact (mul_eq_zero.1 this).resolve_left hD
    apply hτ
    have : τ ^ 2 = 0 := by rw [hA0, hN0] at h1; linear_combination -h1
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this)
  obtain ⟨r, hr⟩ := ((f1.union f2).union f3).exists_notMem
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hr
  obtain ⟨⟨r1, r2⟩, r3⟩ := hr
  have r1' : r ^ 2 - D ≠ 0 := fun h => r1 (by linear_combination h)
  set e : F := (r ^ 2 - D)⁻¹ with he
  have he1 : e * (r ^ 2 - D) = 1 := inv_mul_cancel₀ r1'
  have he2 : algebraMap F E e * (algebraMap F E r ^ 2 - δ * δ) = 1 := by
    rw [hδ2, ← map_pow, ← map_sub, ← map_mul, he1, map_one]
  set u : E := algebraMap F E e * (algebraMap F E r + δ) ^ 2 with hu
  have hcu : L.cj u = algebraMap F E e * (algebraMap F E r - δ) ^ 2 := by
    simp [hu, hδ, sub_eq_add_neg]
  have huu : u * L.cj u = 1 := by
    rw [hcu, hu]
    linear_combination (algebraMap F E e * (algebraMap F E r ^ 2 - δ * δ) + 1) * he2
  have hT : L.cj u * s + u * L.cj s = algebraMap F E (e * ((r ^ 2 + D) * A - 2 * r * B)) := by
    rw [hcu, hu]
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, hA, hB, ← hδ2]
    ring
  have hcb : L.cj (algebraMap F E τ - L.cj u * s) = algebraMap F E τ - u * L.cj s := by
    simp [L.cj_cj]
  clear_value u
  refine ⟨u, huu, ?_, ?_⟩
  · have : (algebraMap F E τ - L.cj u * s) * (algebraMap F E τ - u * L.cj s) =
        algebraMap F E (τ ^ 2 + N - τ * (e * ((r ^ 2 + D) * A - 2 * r * B))) := by
      rw [map_sub, map_add, map_mul (algebraMap F E), ← hT, hN, map_pow]
      linear_combination s * L.cj s * huu
    refine isUnit_of_mul_isUnit_left (y := algebraMap F E τ - u * L.cj s) ?_
    rw [this]
    refine (IsUnit.mk0 _ fun h => r3 ?_).map _
    linear_combination (-(r ^ 2 - D)) * h - τ * ((r ^ 2 + D) * A - 2 * r * B) * he1
  · have : (algebraMap F E τ - L.cj u * s) + (algebraMap F E τ - u * L.cj s) =
        algebraMap F E (2 * τ - (e * ((r ^ 2 + D) * A - 2 * r * B))) := by
      rw [map_sub, map_mul (algebraMap F E), ← hT, map_ofNat]
      ring
    rw [hcb, this]
    refine (IsUnit.mk0 _ fun h => r2 ?_).map _
    linear_combination (-(r ^ 2 - D)) * h - ((r ^ 2 + D) * A - 2 * r * B) * he1

/- English proof (translation)
Take `⟨u, huu, hb, hbb⟩` from `exists_norm_one L (hf L Hm x x) (hf L Hm x y) hx (hf_cj L h x x)`. Establish `haa : hf L Hm (x + (-u) • y) (x + (-u) • y) = (hf L Hm x x - L.cj u * hf L Hm x y) + L.cj (hf L Hm x x - L.cj u * hf L Hm x y)`. Simplify using `only [hf_add_l, hf_add_r, hf_smul_l, hf_smul_r, map_mul, map_sub, map_neg, hf_cj L h, L.cj_cj, hxy]`. Take the linear combination `hf L Hm x x * huu`. Establish `hxa : hf L Hm x (x + (-u) • y) = hf L Hm x x - L.cj u * hf L Hm x y`.

Simplify using `only [hf_add_r, hf_smul_r, map_neg]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨b, hb1⟩` from `hb.exists_left_inv`. Take `⟨t, ht1⟩` from `hx.exists_left_inv`. Establish `hb2` using `congrArg L.cj hb1`.

Establish `ht2` using `congrArg L.cj ht1`. Rewrite `hb2`, `ht2` using `[map_mul, map_one]`. Rewrite `ht2` using `[hf_cj L h]`. Establish `htt : L.cj t = t` using `by linear_combination t * ht2 - L.cj t * ht1`. Take `⟨σ, hσ, hσ'⟩` from `exists_qrefl L h (x + (-u) • y) (haa ▸ hbb) (-b) (by`.

Rewrite using `[haa, map_neg]`. Take the linear combination `L.cj b * hb1 + b * hb2)`. Take `⟨ρ, hρ, hρ'⟩` from `exists_qrefl L h y (hxy ▸ hx) ((u - 1) * t) (by`. Rewrite using `[hxy, map_mul, map_sub, map_one, htt]`. Take the linear combination `(u - 1) * (L.cj u - 1) * t * ht1 + t * huu)`.

Use `⟨u, σ, ρ, hσ, hρ, ?_⟩` and prove the remaining obligations. Rewrite using `[hσ', hρ', hxa, hxy, neg_mul, hb1, mul_assoc, ht1]`. Use `module`.
-/
theorem step [CharZero F] (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (x y : Fin n → E) (hx : IsUnit (hf L Hm x x)) (hxy : hf L Hm y y = hf L Hm x x) :
    ∃ (u : E) (σ ρ : (Fin n → E) ≃ₗ[E] (Fin n → E)),
      IsQRefl L Hm (x + (-u) • y) σ ∧ IsQRefl L Hm y ρ ∧ σ x = ρ y := by
  obtain ⟨u, huu, hb, hbb⟩ := exists_norm_one L (hf L Hm x x) (hf L Hm x y) hx (hf_cj L h x x)
  have haa : hf L Hm (x + (-u) • y) (x + (-u) • y) =
      (hf L Hm x x - L.cj u * hf L Hm x y) + L.cj (hf L Hm x x - L.cj u * hf L Hm x y) := by
    simp only [hf_add_l, hf_add_r, hf_smul_l, hf_smul_r, map_mul, map_sub, map_neg, hf_cj L h,
      L.cj_cj, hxy]
    linear_combination hf L Hm x x * huu
  have hxa : hf L Hm x (x + (-u) • y) = hf L Hm x x - L.cj u * hf L Hm x y := by
    simp only [hf_add_r, hf_smul_r, map_neg]; ring
  obtain ⟨b, hb1⟩ := hb.exists_left_inv
  obtain ⟨t, ht1⟩ := hx.exists_left_inv
  have hb2 := congrArg L.cj hb1
  have ht2 := congrArg L.cj ht1
  rw [map_mul, map_one] at hb2 ht2
  rw [hf_cj L h] at ht2
  have htt : L.cj t = t := by linear_combination t * ht2 - L.cj t * ht1
  obtain ⟨σ, hσ, hσ'⟩ := exists_qrefl L h (x + (-u) • y) (haa ▸ hbb) (-b) (by
    rw [haa, map_neg]
    linear_combination L.cj b * hb1 + b * hb2)
  obtain ⟨ρ, hρ, hρ'⟩ := exists_qrefl L h y (hxy ▸ hx) ((u - 1) * t) (by
    rw [hxy, map_mul, map_sub, map_one, htt]
    linear_combination (u - 1) * (L.cj u - 1) * t * ht1 + t * huu)
  refine ⟨u, σ, ρ, hσ, hρ, ?_⟩
  rw [hσ', hρ', hxa, hxy, neg_mul, hb1, mul_assoc, ht1]
  module

/- English proof (translation)
Take `⟨-, -, c, hc⟩` from `hg`. Rewrite using `[hc, hv]`. Simplify using the standard rewrite rules.
-/
theorem qrefl_fix (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} {a : Fin n → E}
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (hg : IsQRefl L Hm a g) {v : Fin n → E}
    (hv : hf L Hm v a = 0) : g v = v := by
  obtain ⟨-, -, c, hc⟩ := hg
  rw [hc, hv]; simp

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Introduce `g _ h1 h2`. Establish `: g = 1`. Apply `LinearEquiv.toLinearMap_injective` to reduce the goal to its premises.

Establish `hle : (⊤ : Submodule E (Fin n → E)) ≤ LinearMap.eqLocus g.toLinearMap (1 : (Fin n → E) ≃ₗ[E] (Fin n → E)).toLinearMap`. Rewrite using `[← hY, ← hw, sup_le_iff, Submodule.span_le]`. Use `⟨fun v hv => h1 v hv, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `h2 j (by simp)`.

Conclude with `LinearMap.ext fun v => hle (Submodule.mem_top (x := v))`. Rewrite using `[this]`. Conclude with `one_mem _`. Consider the case `insert i S hi ih`. Introduce `g hg h1 h2`.

Establish `hwp : w i ∈ perp L Hm Y` using `hw ▸ Submodule.subset_span ⟨i, rfl⟩`. Establish `hyp : g (w i) ∈ perp L Hm Y` using `fun z hz => by`. Rewrite using `[← h1 z hz, hg (w i) z]`. Conclude with `hwp z hz`. Take `⟨u, σ, ρ, hσ, hρ, hσρ⟩` from `step L h (w i) (g (w i)) (hu i) (hg _ _)`.

Establish `hap : w i + (-u) • g (w i) ∈ perp L Hm Y` using `add_mem hwp (Submodule.smul_mem _ _ hyp)`. Establish `mσ : σ ∈ Subgroup.closure {g | ∃ a ∈ perp L Hm Y, IsQRefl L Hm a g}` using `Subgroup.subset_closure ⟨_, hap, hσ⟩`. Establish `mρ : ρ ∈ Subgroup.closure {g | ∃ a ∈ perp L Hm Y, IsQRefl L Hm a g}` using `Subgroup.subset_closure ⟨_, hyp, hρ⟩`. Establish `key : ∀ v, σ v = ρ (g v) → (σ⁻¹ * ρ * g) v = v` using `fun v hv => by`. Express the relevant statement in the definitionally equal form `σ.symm (ρ (g v)) = v`.

Rewrite using `[← hv, LinearEquiv.symm_apply_apply]`. Establish `hg'` using `ih (σ⁻¹ * ρ * g) (mul_mem (mul_mem (inv_mem hσ.2.1) hρ.2.1) hg) (fun v hv => key v (by`. Rewrite using `[h1 v hv, qrefl_fix L hσ (by rw [← hf_cj L h, hap v hv, map_zero]), qrefl_fix L hρ (by rw [← hf_cj L h, hyp v hv, map_zero])]))`. Use the proof step `(fun j hj => key _ (by`. Distinguish the cases in `hji : j = i`.

Rewrite using `[hji]`. Conclude with `hσρ`. Establish `hj2` using `h2 j (by simp [hji, hj])`. Establish `h3 : hf L Hm (w j) (g (w i)) = 0`. Rewrite using `[← hj2, hg (w j) (w i)]`.

Conclude with `ho j i hji`. Rewrite using `[hj2, qrefl_fix L hσ (by rw [hf_add_r, hf_smul_r, h3, ho j i hji]; simp), qrefl_fix L hρ h3]))`. Establish `: g = ρ⁻¹ * σ * (σ⁻¹ * ρ * g)` using `by group`. Rewrite using `[this]`. Conclude with `mul_mem (mul_mem (inv_mem mρ) mσ) hg'`.
-/
theorem induct [CharZero F] (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (Y : Submodule E (Fin n → E)) (hY : Y ⊔ perp L Hm Y = ⊤) {d : ℕ} (w : Fin d → Fin n → E)
    (hw : Submodule.span E (Set.range w) = perp L Hm Y) (hu : ∀ i, IsUnit (hf L Hm (w i) (w i)))
    (ho : ∀ i j, i ≠ j → hf L Hm (w i) (w j) = 0) (S : Finset (Fin d)) :
    ∀ g ∈ isomG L Hm, (∀ v ∈ Y, g v = v) → (∀ j, j ∉ S → g (w j) = w j) →
      g ∈ Subgroup.closure {g | ∃ a ∈ perp L Hm Y, IsQRefl L Hm a g} := by
  induction S using Finset.induction_on with
  | empty =>
    intro g _ h1 h2
    have : g = 1 := by
      apply LinearEquiv.toLinearMap_injective
      have hle : (⊤ : Submodule E (Fin n → E)) ≤
          LinearMap.eqLocus g.toLinearMap (1 : (Fin n → E) ≃ₗ[E] (Fin n → E)).toLinearMap := by
        rw [← hY, ← hw, sup_le_iff, Submodule.span_le]
        refine ⟨fun v hv => h1 v hv, ?_⟩
        rintro _ ⟨j, rfl⟩
        exact h2 j (by simp)
      exact LinearMap.ext fun v => hle (Submodule.mem_top (x := v))
    rw [this]; exact one_mem _
  | insert i S hi ih =>
    intro g hg h1 h2
    have hwp : w i ∈ perp L Hm Y := hw ▸ Submodule.subset_span ⟨i, rfl⟩
    have hyp : g (w i) ∈ perp L Hm Y := fun z hz => by
      rw [← h1 z hz, hg (w i) z]; exact hwp z hz
    obtain ⟨u, σ, ρ, hσ, hρ, hσρ⟩ := step L h (w i) (g (w i)) (hu i) (hg _ _)
    have hap : w i + (-u) • g (w i) ∈ perp L Hm Y := add_mem hwp (Submodule.smul_mem _ _ hyp)
    have mσ : σ ∈ Subgroup.closure {g | ∃ a ∈ perp L Hm Y, IsQRefl L Hm a g} :=
      Subgroup.subset_closure ⟨_, hap, hσ⟩
    have mρ : ρ ∈ Subgroup.closure {g | ∃ a ∈ perp L Hm Y, IsQRefl L Hm a g} :=
      Subgroup.subset_closure ⟨_, hyp, hρ⟩
    have key : ∀ v, σ v = ρ (g v) → (σ⁻¹ * ρ * g) v = v := fun v hv => by
      change σ.symm (ρ (g v)) = v
      rw [← hv, LinearEquiv.symm_apply_apply]
    have hg' := ih (σ⁻¹ * ρ * g) (mul_mem (mul_mem (inv_mem hσ.2.1) hρ.2.1) hg)
      (fun v hv => key v (by
        rw [h1 v hv, qrefl_fix L hσ (by rw [← hf_cj L h, hap v hv, map_zero]),
          qrefl_fix L hρ (by rw [← hf_cj L h, hyp v hv, map_zero])]))
      (fun j hj => key _ (by
        by_cases hji : j = i
        · rw [hji]; exact hσρ
        · have hj2 := h2 j (by simp [hji, hj])
          have h3 : hf L Hm (w j) (g (w i)) = 0 := by
            rw [← hj2, hg (w j) (w i)]; exact ho j i hji
          rw [hj2, qrefl_fix L hσ (by rw [hf_add_r, hf_smul_r, h3, ho j i hji]; simp),
            qrefl_fix L hρ h3]))
    have : g = ρ⁻¹ * σ * (σ⁻¹ * ρ * g) := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem mρ) mσ) hg'

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L n Hm hH m x hx g hg`. Take `⟨-, hc, w, hw, hu, ho⟩` from `GlobalTheory.HermOrthBasis.orth_basis_perp L Hm hH m x hx`. Use `induct L hH.1 _ hc.sup_eq_top w hw hu ho Finset.univ g hg.1 (fun v hv => ?_) (by simp)` and prove the remaining obligations. Use `hg.2.2 v hv` as an intermediate fact. Rewrite `this` using `[Submodule.mem_bot, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem fixG_le_closure : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → fixG L Hm (Submodule.span E (Set.range x)) ≤ Subgroup.closure {g | ∃ a ∈ perp L Hm (Submodule.span E (Set.range x)), IsQRefl L Hm a g} := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH m x hx g hg
  obtain ⟨-, hc, w, hw, hu, ho⟩ := GlobalTheory.HermOrthBasis.orth_basis_perp L Hm hH m x hx
  refine induct L hH.1 _ hc.sup_eq_top w hw hu ho Finset.univ g hg.1 (fun v hv => ?_) (by simp)
  have := hg.2.2 v hv
  rwa [Submodule.mem_bot, sub_eq_zero] at this

end GlobalTheory.HL.QReflGen
