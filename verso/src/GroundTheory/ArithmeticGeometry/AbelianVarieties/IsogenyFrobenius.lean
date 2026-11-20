import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.Isogeny

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField

section Torsion

variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F)

noncomputable def yPoly (x : F) : F[X] :=
  X ^ 2 + C (E.a₁ * x + E.a₃) * X - C (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆)

/- English proof (translation)
Unfold `yPoly`. Use `compute_degree!`.
-/
theorem natDegree_yPoly (x : F) : (yPoly E x).natDegree = 2 := by
  unfold yPoly; compute_degree!

/- English proof (translation)
Introduce `h; have := natDegree_yPoly E x; rw [h, natDegree_zero] at this; exact absurd this (by norm_num)`.
-/
theorem yPoly_ne_zero (x : F) : yPoly E x ≠ 0 := by
  intro h; have := natDegree_yPoly E x; rw [h, natDegree_zero] at this; exact absurd this (by norm_num)

/- English proof (translation)
Rewrite `h` using `[equation_iff]`. Simplify using `only [yPoly, IsRoot, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]`. Take the linear combination `h`.
-/
theorem isRoot_yPoly {x y : F} (h : E.toAffine.Equation x y) : (yPoly E x).IsRoot y := by
  rw [equation_iff] at h
  simp only [yPoly, IsRoot, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  linear_combination h

/- English proof (translation)
Use `set S := (E.ΨSq n).roots.toFinset`. Use `set T : Finset (F × F) := S.biUnion fun x => ((yPoly E x).roots.toFinset).image fun y => (x, y)`. Establish `hT : T.card ≤ 2 * S.card`. Use `(Finset.card_biUnion_le).trans ?_` and prove the remaining obligations. Rewrite using `[mul_comm, ← smul_eq_mul, ← Finset.sum_const]`.

Use `Finset.sum_le_sum fun x _ => ?_` and prove the remaining obligations. Use `Finset.card_image_le.trans ?_` and prove the remaining obligations. Use `(Multiset.toFinset_card_le _).trans ?_` and prove the remaining obligations. Conclude with `(card_roots' _).trans (natDegree_yPoly E x).le`. Set `f : {P : E.toAffine.Point // n • P = 0} → Option (F × F)` to `fun P => match P.1 with`.

Consider the case `.zero => none`. Consider the case `.some x y _ => some (x, y)`. Establish `hf : Function.Injective f`. Introduce and unpack `⟨P, hP⟩ ⟨Q, hQ⟩ h`. Consider the cases of `P with`.

Consider the case `zero`. Consider the cases of `Q with`. Consider the case `zero => rfl`. Consider the case `some x y _ => exact absurd h (by simp [f])`. Consider the case `some x y hxy`.

Consider the cases of `Q with`. Consider the case `zero => exact absurd h (by simp [f])`. Consider the case `some x' y' _`. Simplify using `only [f, Option.some.injEq, Prod.mk.injEq] at h`. Take `⟨rfl, rfl⟩` from `h`.

Both sides reduce to the same expression. Establish `hrange : Set.range f ⊆ (T.insertNone : Set (Option (F × F)))`. Introduce and unpack `_ ⟨⟨P, hP⟩, rfl⟩`. Consider the cases of `P with`. Consider the case `zero => exact Finset.none_mem_insertNone`.

Consider the case `some x y hxy`. Establish `hx : (E.ΨSq n).eval x = 0`. Break down `(zsmul_eq_zero_iff_ΨSq E n _).mp hP with h0 | ⟨x', y', h', he, hx'⟩` into its components or cases. Conclude with `absurd h0 (Point.some_ne_zero hxy)`. Rewrite `he` using `[Point.some.injEq]`.

Rewrite using `[he.1]`. Conclude with `hx'`. Use `show some (x, y) ∈ (T.insertNone : Set _)`. Rewrite using `[Finset.mem_coe, Finset.some_mem_insertNone]`. Simplify using `only [T, S, Finset.mem_biUnion, Finset.mem_image, Multiset.mem_toFinset]`.

Use `⟨x, (mem_roots hn).mpr hx, y, ?_, rfl⟩` and prove the remaining obligations. Conclude with `(mem_roots (yPoly_ne_zero E x)).mpr (isRoot_yPoly E hxy.1)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_zsmul_eq_zero_le {n : ℤ} (hn : E.ΨSq n ≠ 0) :
    Nat.card {P : E.toAffine.Point // n • P = 0} ≤ 1 + 2 * (E.ΨSq n).roots.toFinset.card := by
  classical
  set S := (E.ΨSq n).roots.toFinset
  set T : Finset (F × F) := S.biUnion fun x => ((yPoly E x).roots.toFinset).image fun y => (x, y)
  have hT : T.card ≤ 2 * S.card := by
    refine (Finset.card_biUnion_le).trans ?_
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun x _ => ?_
    refine Finset.card_image_le.trans ?_
    refine (Multiset.toFinset_card_le _).trans ?_
    exact (card_roots' _).trans (natDegree_yPoly E x).le
  let f : {P : E.toAffine.Point // n • P = 0} → Option (F × F) := fun P =>
    match P.1 with
    | .zero => none
    | .some x y _ => some (x, y)
  have hf : Function.Injective f := by
    rintro ⟨P, hP⟩ ⟨Q, hQ⟩ h
    cases P with
    | zero =>
      cases Q with
      | zero => rfl
      | some x y _ => exact absurd h (by simp [f])
    | some x y hxy =>
      cases Q with
      | zero => exact absurd h (by simp [f])
      | some x' y' _ =>
        simp only [f, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
  have hrange : Set.range f ⊆ (T.insertNone : Set (Option (F × F))) := by
    rintro _ ⟨⟨P, hP⟩, rfl⟩
    cases P with
    | zero => exact Finset.none_mem_insertNone
    | some x y hxy =>
      have hx : (E.ΨSq n).eval x = 0 := by
        rcases (zsmul_eq_zero_iff_ΨSq E n _).mp hP with h0 | ⟨x', y', h', he, hx'⟩
        · exact absurd h0 (Point.some_ne_zero hxy)
        · rw [Point.some.injEq] at he; rw [he.1]; exact hx'
      show some (x, y) ∈ (T.insertNone : Set _)
      rw [Finset.mem_coe, Finset.some_mem_insertNone]
      simp only [T, S, Finset.mem_biUnion, Finset.mem_image, Multiset.mem_toFinset]
      refine ⟨x, (mem_roots hn).mpr hx, y, ?_, rfl⟩
      exact (mem_roots (yPoly_ne_zero E x)).mpr (isRoot_yPoly E hxy.1)
  calc Nat.card {P : E.toAffine.Point // n • P = 0}
      = Nat.card (Set.range f) := (Nat.card_range_of_injective hf).symm
    _ ≤ Nat.card (T.insertNone : Set (Option (F × F))) :=
        Nat.card_mono (Finset.finite_toSet _) hrange
    _ = T.card + 1 := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_insertNone]
    _ ≤ 1 + 2 * S.card := by omega

end Torsion

section TorsionP

variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F) [E.IsElliptic]
  (p : ℕ) [hp : Fact p.Prime] [CharP F p]

/- English proof (translation)
Rewrite using `[roots_pow, Multiset.toFinset_nsmul _ _ two_ne_zero]`.
-/
theorem roots_toFinset_sq (q : F[X]) : (q ^ 2).roots.toFinset = q.roots.toFinset := by
  rw [roots_pow, Multiset.toFinset_nsmul _ _ two_ne_zero]

/- English proof (translation)
Establish `hpodd : ¬ Even (p : ℤ)`. Rewrite using `[Int.even_coe_nat]`. Conclude with `fun h => hodd ((Nat.Prime.even_iff hp.out).mp h)`. Establish `hΨ : E.ΨSq p = E.preΨ p ^ 2`. Rewrite using `[ΨSq, if_neg hpodd, mul_one]`.

Establish `hne : E.ΨSq p ≠ 0` using `ΨSq_ne_zero_of_ne_zero E (by exact_mod_cast hp.out.ne_zero)`. Establish `hpre : E.preΨ p ≠ 0` using `fun h => hne (by rw [hΨ, h]; ring)`. Rewrite using `[hΨ, roots_toFinset_sq]`. Use `(Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)` and prove the remaining obligations. Establish `hle` using `E.natDegree_preΨ_le p`.

Establish `hco` using `E.coeff_preΨ p`. Simplify using `only [Int.natAbs_natCast, if_neg hpodd] at hle hco`. Establish `hc0 : (E.preΨ p).coeff ((p ^ 2 - 1) / 2) = 0`. Rewrite using `[hco]`. Conclude with `CharP.cast_eq_zero F p` after adjusting the coercions.

Establish `hlt : (E.preΨ p).natDegree ≠ (p ^ 2 - 1) / 2`. Introduce `h`. Apply `hpre` to reduce the goal to its premises. Rewrite using `[← leadingCoeff_eq_zero, leadingCoeff, h, hc0]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_roots_ΨSq_le_of_odd (hodd : p ≠ 2) :
    (E.ΨSq p).roots.toFinset.card ≤ (p ^ 2 - 1) / 2 - 1 := by
  have hpodd : ¬ Even (p : ℤ) := by
    rw [Int.even_coe_nat]
    exact fun h => hodd ((Nat.Prime.even_iff hp.out).mp h)
  have hΨ : E.ΨSq p = E.preΨ p ^ 2 := by
    rw [ΨSq, if_neg hpodd, mul_one]
  have hne : E.ΨSq p ≠ 0 := ΨSq_ne_zero_of_ne_zero E (by exact_mod_cast hp.out.ne_zero)
  have hpre : E.preΨ p ≠ 0 := fun h => hne (by rw [hΨ, h]; ring)
  rw [hΨ, roots_toFinset_sq]
  refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
  have hle := E.natDegree_preΨ_le p
  have hco := E.coeff_preΨ p
  simp only [Int.natAbs_natCast, if_neg hpodd] at hle hco
  have hc0 : (E.preΨ p).coeff ((p ^ 2 - 1) / 2) = 0 := by
    rw [hco]; exact_mod_cast CharP.cast_eq_zero F p
  have hlt : (E.preΨ p).natDegree ≠ (p ^ 2 - 1) / 2 := by
    intro h
    apply hpre
    rw [← leadingCoeff_eq_zero, leadingCoeff, h, hc0]
  omega

/- English proof (translation)
Substitute `h2` using the available equality. Establish `h2F : (2 : F) = 0` using `CharTwo.two_eq_zero`. Establish `h2X : (2 : F[X]) = 0` using `by rw [← C_ofNat, h2F, C_0]`. Establish `e : E.Ψ₂Sq = (C E.a₁ * X + C E.a₃) ^ 2 + 2 * (2 * X ^ 3 + C (2 * E.a₂) * X ^ 2 + C E.b₄ * X - C E.a₁ * C E.a₃ * X + C (2 * E.a₆))`. Simplify using `only [Ψ₂Sq, b₂, b₆, map_add, map_mul, map_pow, map_ofNat]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, h2X, zero_mul, add_zero]`.
-/
theorem Ψ₂Sq_eq_sq_of_two (h2 : p = 2) : E.Ψ₂Sq = (C E.a₁ * X + C E.a₃) ^ 2 := by
  subst h2
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have h2X : (2 : F[X]) = 0 := by rw [← C_ofNat, h2F, C_0]
  have e : E.Ψ₂Sq = (C E.a₁ * X + C E.a₃) ^ 2 + 2 * (2 * X ^ 3 + C (2 * E.a₂) * X ^ 2 +
      C E.b₄ * X - C E.a₁ * C E.a₃ * X + C (2 * E.a₆)) := by
    simp only [Ψ₂Sq, b₂, b₆, map_add, map_mul, map_pow, map_ofNat]
    ring
  rw [e, h2X, zero_mul, add_zero]

/- English proof (translation)
Establish `hne : E.ΨSq p ≠ 0` using `ΨSq_ne_zero_of_ne_zero E (by exact_mod_cast hp.out.ne_zero)`. Establish `hΨ : E.ΨSq p = (C E.a₁ * X + C E.a₃) ^ 2`. Rewrite using `[← Ψ₂Sq_eq_sq_of_two E p h2, h2]`. Conclude with `ΨSq_two E`. Rewrite using `[hΨ, roots_toFinset_sq]`.

Use `(Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)` and prove the remaining obligations. Use `compute_degree`.
-/
theorem card_roots_ΨSq_le_of_two (h2 : p = 2) : (E.ΨSq p).roots.toFinset.card ≤ 1 := by
  have hne : E.ΨSq p ≠ 0 := ΨSq_ne_zero_of_ne_zero E (by exact_mod_cast hp.out.ne_zero)
  have hΨ : E.ΨSq p = (C E.a₁ * X + C E.a₃) ^ 2 := by
    rw [← Ψ₂Sq_eq_sq_of_two E p h2, h2]; exact ΨSq_two E
  rw [hΨ, roots_toFinset_sq]
  refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
  compute_degree

/- English proof (translation)
Establish `hne : E.ΨSq p ≠ 0` using `ΨSq_ne_zero_of_ne_zero E (by exact_mod_cast hp.out.ne_zero)`. Use `(card_zsmul_eq_zero_le E hne).trans_lt ?_` and prove the remaining obligations. Distinguish the cases in `h2 : p = 2`. Use `card_roots_ΨSq_le_of_two E p h2` as an intermediate fact. Substitute `h2` using the available equality.

Use linear arithmetic over natural numbers and integers. Use `card_roots_ΨSq_le_of_odd E p h2` as an intermediate fact. Establish `hp3 : 3 ≤ p`. Use `hp.out.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hodd : p ^ 2 % 2 = 1`. Establish `: Odd p` using `hp.out.odd_of_ne_two h2`. Establish `: Odd (p ^ 2)` using `this.pow`. Conclude with `Nat.odd_iff.mp this`. Establish `h9 : 9 ≤ p ^ 2` using `by nlinarith`.

Use linear arithmetic over natural numbers and integers.
-/
theorem card_torsion_lt : Nat.card {P : E.toAffine.Point // (p : ℤ) • P = 0} < p ^ 2 := by
  have hne : E.ΨSq p ≠ 0 := ΨSq_ne_zero_of_ne_zero E (by exact_mod_cast hp.out.ne_zero)
  refine (card_zsmul_eq_zero_le E hne).trans_lt ?_
  by_cases h2 : p = 2
  · have := card_roots_ΨSq_le_of_two E p h2
    subst h2
    omega
  · have := card_roots_ΨSq_le_of_odd E p h2
    have hp3 : 3 ≤ p := by
      have := hp.out.two_le
      omega
    have hodd : p ^ 2 % 2 = 1 := by
      have : Odd p := hp.out.odd_of_ne_two h2
      have : Odd (p ^ 2) := this.pow
      exact Nat.odd_iff.mp this
    have h9 : 9 ≤ p ^ 2 := by nlinarith
    omega

end TorsionP

section Pow

variable {F : Type*} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]

instance charP_functionField : CharP E.toAffine.FunctionField p :=
  charP_of_injective_algebraMap (algebraMap F E.toAffine.FunctionField).injective p

noncomputable def powField : IntermediateField F E.toAffine.FunctionField :=
  F⟮genX E ^ p, genY E ^ p⟯

variable [PerfectRing F p]

noncomputable def frobImage (K : IntermediateField F E.toAffine.FunctionField) :
    IntermediateField F E.toAffine.FunctionField :=
  (K.toSubfield.map (frobenius E.toAffine.FunctionField p)).toIntermediateField fun c => by
    refine ⟨algebraMap F E.toAffine.FunctionField ((frobeniusEquiv F p).symm c),
      IntermediateField.algebraMap_mem K _, ?_⟩
    rw [frobenius_def, ← map_pow]
    congr 1
    exact frobenius_apply_frobeniusEquiv_symm F p c

/- English proof (translation)
Use `show z ∈ K.toSubfield.map (frobenius E.toAffine.FunctionField p) ↔ _`. Rewrite using `[Subfield.mem_map]`. Both sides reduce to the same expression.
-/
theorem mem_frobImage {K : IntermediateField F E.toAffine.FunctionField}
    {z : E.toAffine.FunctionField} : z ∈ frobImage E p K ↔ ∃ g ∈ K, g ^ p = z := by
  show z ∈ K.toSubfield.map (frobenius E.toAffine.FunctionField p) ↔ _
  rw [Subfield.mem_map]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hz`. Establish `hle : powField E p ≤ frobImage E p ⊤`. Rewrite using `[powField, adjoin_le_iff]`. Introduce and unpack `w (rfl | rfl)`.

Conclude with `(mem_frobImage E p).mpr ⟨genX E, trivial, rfl⟩`. Conclude with `(mem_frobImage E p).mpr ⟨genY E, trivial, rfl⟩`. Take `⟨g, -, hg⟩` from `(mem_frobImage E p).mp (hle hz)`. Conclude with `⟨g, hg⟩`. Introduce and unpack `⟨g, rfl⟩`.

Set `Q : IntermediateField F E.toAffine.FunctionField` to `((powField E p).toSubfield.comap (frobenius E.toAffine.FunctionField p)).toIntermediateField fun c => by show (algebraMap F _ c) ^ p ∈ powField E p`. Rewrite using `[← map_pow]`. Conclude with `IntermediateField.algebraMap_mem _ _`. Establish `htop : (⊤ : IntermediateField F E.toAffine.FunctionField) ≤ Q`. Rewrite using `[← adjoin_genX_genY E, adjoin_le_iff]`.

Introduce and unpack `w (rfl | rfl)`. Conclude with `(subset_adjoin F _ (by simp) : genX E ^ p ∈ powField E p)`. Conclude with `(subset_adjoin F _ (by simp) : genY E ^ p ∈ powField E p)`. Conclude with `htop trivial`.
-/
theorem mem_powField_iff (z : E.toAffine.FunctionField) :
    z ∈ powField E p ↔ ∃ g, g ^ p = z := by
  constructor
  · intro hz
    have hle : powField E p ≤ frobImage E p ⊤ := by
      rw [powField, adjoin_le_iff]
      rintro w (rfl | rfl)
      · exact (mem_frobImage E p).mpr ⟨genX E, trivial, rfl⟩
      · exact (mem_frobImage E p).mpr ⟨genY E, trivial, rfl⟩
    obtain ⟨g, -, hg⟩ := (mem_frobImage E p).mp (hle hz)
    exact ⟨g, hg⟩
  · rintro ⟨g, rfl⟩
    let Q : IntermediateField F E.toAffine.FunctionField :=
      ((powField E p).toSubfield.comap (frobenius E.toAffine.FunctionField p)).toIntermediateField
        fun c => by
          show (algebraMap F _ c) ^ p ∈ powField E p
          rw [← map_pow]; exact IntermediateField.algebraMap_mem _ _
    have htop : (⊤ : IntermediateField F E.toAffine.FunctionField) ≤ Q := by
      rw [← adjoin_genX_genY E, adjoin_le_iff]
      rintro w (rfl | rfl)
      · exact (subset_adjoin F _ (by simp) : genX E ^ p ∈ powField E p)
      · exact (subset_adjoin F _ (by simp) : genY E ^ p ∈ powField E p)
    exact htop trivial

/- English proof (translation)
Establish `hE0 : F⟮genX E ^ p⟯ = (F⟮(RatFunc.X : RatFunc F) ^ p⟯).map (ratEmb E)`. Rewrite using `[adjoin_map, Set.image_singleton, map_pow, ratEmb_X]`. Establish `hE1 : F⟮genX E⟯ = (⊤ : IntermediateField F (RatFunc F)).map (ratEmb E)`. Rewrite using `[map_top_eq_fieldRange, fieldRange_ratEmb]`. Establish `hX : (RatFunc.X : RatFunc F) ^ p = algebraMap F[X] (RatFunc F) (X ^ p)`.

Rewrite using `[map_pow, RatFunc.algebraMap_X]`. Rewrite using `[hE0, hE1, relfinrank_map_map, relfinrank_top_right, RatFunc.finrank_eq_max_natDegree, hX, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, natDegree_X_pow, natDegree_one, max_eq_left (Nat.zero_le _)]`.
-/
theorem relfinrank_adjoin_genX_pow :
    relfinrank F⟮genX E ^ p⟯ F⟮genX E⟯ = p := by
  have hE0 : F⟮genX E ^ p⟯ = (F⟮(RatFunc.X : RatFunc F) ^ p⟯).map (ratEmb E) := by
    rw [adjoin_map, Set.image_singleton, map_pow, ratEmb_X]
  have hE1 : F⟮genX E⟯ = (⊤ : IntermediateField F (RatFunc F)).map (ratEmb E) := by
    rw [map_top_eq_fieldRange, fieldRange_ratEmb]
  have hX : (RatFunc.X : RatFunc F) ^ p = algebraMap F[X] (RatFunc F) (X ^ p) := by
    rw [map_pow, RatFunc.algebraMap_X]
  rw [hE0, hE1, relfinrank_map_map, relfinrank_top_right, RatFunc.finrank_eq_max_natDegree, hX,
    RatFunc.num_algebraMap, RatFunc.denom_algebraMap, natDegree_X_pow, natDegree_one, max_eq_left
    (Nat.zero_le _)]

/- English proof (translation)
Introduce `h`. Establish `hle : F⟮genX E ^ p⟯ ≤ frobImage E p F⟮genX E⟯`. Rewrite using `[adjoin_le_iff]`. Introduce and unpack `w rfl`. Conclude with `(mem_frobImage E p).mpr ⟨genX E, mem_adjoin_simple_self F _, rfl⟩`.

Take `⟨g, hg, hgy⟩` from `(mem_frobImage E p).mp (hle h)`. Establish `: g = genY E` using `frobenius_inj E.toAffine.FunctionField p hgy`. Conclude with `genY_not_mem E (this ▸ hg)`.
-/
theorem genY_pow_not_mem : genY E ^ p ∉ F⟮genX E ^ p⟯ := by
  intro h
  have hle : F⟮genX E ^ p⟯ ≤ frobImage E p F⟮genX E⟯ := by
    rw [adjoin_le_iff]
    rintro w rfl
    exact (mem_frobImage E p).mpr ⟨genX E, mem_adjoin_simple_self F _, rfl⟩
  obtain ⟨g, hg, hgy⟩ := (mem_frobImage E p).mp (hle h)
  have : g = genY E := frobenius_inj E.toAffine.FunctionField p hgy
  exact genY_not_mem E (this ▸ hg)

/- English proof (translation)
Use `set K0 := F⟮genX E ^ p⟯`. Use `set w := genY E ^ p`. Establish `hx0 : genX E ^ p ∈ K0` using `mem_adjoin_simple_self F _`. Establish `hle : K0 ≤ powField E p` using `adjoin_simple_le_iff.mpr (subset_adjoin F _ (by simp))`. Establish `hext : K0⟮w⟯ = extendScalars hle`.

Apply `restrictScalars_injective F` to reduce the goal to its premises. Rewrite using `[adjoin_simple_adjoin_simple, extendScalars_restrictScalars]`. Both sides reduce to the same expression. Establish `hcst : ∀ a : F, algebraMap F E.toAffine.FunctionField a ∈ K0` using `fun a => IntermediateField.algebraMap_mem _ a`. Establish `hb : algebraMap F _ (E.a₁ ^ p) * genX E ^ p + algebraMap F _ (E.a₃ ^ p) ∈ K0` using `add_mem (mul_mem (hcst _) hx0) (hcst _)`.

Establish `hc : (genX E ^ p) ^ 3 + algebraMap F _ (E.a₂ ^ p) * (genX E ^ p) ^ 2 + algebraMap F _ (E.a₄ ^ p) * genX E ^ p + algebraMap F _ (E.a₆ ^ p) ∈ K0` using `add_mem (add_mem (add_mem (pow_mem hx0 3) (mul_mem (hcst _) (pow_mem hx0 2))) (mul_mem (hcst _) hx0)) (hcst _)`. Use `set q : K0[X] := X ^ 2 + C ⟨_, hb⟩ * X - C ⟨_, hc⟩`. Establish `hq : aeval w q = 0`. Establish `e` using `(equation_iff _ _).mp (equation_gen E)`. Simplify using `only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e`.

Establish `e'` using `congrArg (frobenius E.toAffine.FunctionField p) e`. Simplify using `only [map_add, map_mul, map_pow, frobenius_def] at e'`. Simplify using `only [q, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, w, IntermediateField.algebraMap_apply]`. Take the linear combination `e'`. Establish `hqdeg : q.natDegree = 2` using `by simp only [q]; compute_degree!`.

Establish `hq0 : q ≠ 0` using `fun h => by rw [h, natDegree_zero] at hqdeg; exact absurd hqdeg (by decide)`. Establish `hint : IsIntegral K0 w` using `(show IsAlgebraic K0 w from ⟨q, hq0, hq⟩).isIntegral`. Establish `hdeg : (minpoly K0 w).natDegree = 2`. Establish `hle2 : (minpoly K0 w).natDegree ≤ 2`. Rewrite using `[← hqdeg]`.

Conclude with `natDegree_le_of_dvd (minpoly.dvd K0 _ hq) hq0`. Establish `hne1 : (minpoly K0 w).natDegree ≠ 1`. Introduce `h1`. Rewrite `h1` using `[minpoly.natDegree_eq_one_iff]`. Take `⟨z, hz⟩` from `h1`.

Establish `hw : w ∈ K0` using `by rw [← hz]; exact z.2`. Conclude with `genY_pow_not_mem E p hw`. Establish `hpos` using `minpoly.natDegree_pos hint`. Use linear arithmetic over natural numbers and integers. Rewrite using `[relfinrank_eq_finrank_of_le hle, ← hext, adjoin.finrank hint, hdeg]`.
-/
theorem relfinrank_powField : relfinrank F⟮genX E ^ p⟯ (powField E p) = 2 := by
  set K0 := F⟮genX E ^ p⟯
  set w := genY E ^ p
  have hx0 : genX E ^ p ∈ K0 := mem_adjoin_simple_self F _
  have hle : K0 ≤ powField E p := adjoin_simple_le_iff.mpr (subset_adjoin F _ (by simp))
  have hext : K0⟮w⟯ = extendScalars hle := by
    apply restrictScalars_injective F
    rw [adjoin_simple_adjoin_simple, extendScalars_restrictScalars]
    rfl
  have hcst : ∀ a : F, algebraMap F E.toAffine.FunctionField a ∈ K0 := fun a => IntermediateField.algebraMap_mem _ a
  have hb : algebraMap F _ (E.a₁ ^ p) * genX E ^ p + algebraMap F _ (E.a₃ ^ p) ∈ K0 :=
    add_mem (mul_mem (hcst _) hx0) (hcst _)
  have hc : (genX E ^ p) ^ 3 + algebraMap F _ (E.a₂ ^ p) * (genX E ^ p) ^ 2 +
      algebraMap F _ (E.a₄ ^ p) * genX E ^ p + algebraMap F _ (E.a₆ ^ p) ∈ K0 :=
    add_mem (add_mem (add_mem (pow_mem hx0 3) (mul_mem (hcst _) (pow_mem hx0 2)))
      (mul_mem (hcst _) hx0)) (hcst _)
  set q : K0[X] := X ^ 2 + C ⟨_, hb⟩ * X - C ⟨_, hc⟩
  have hq : aeval w q = 0 := by
    have e := (equation_iff _ _).mp (equation_gen E)
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
    have e' := congrArg (frobenius E.toAffine.FunctionField p) e
    simp only [map_add, map_mul, map_pow, frobenius_def] at e'
    simp only [q, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, w,
      IntermediateField.algebraMap_apply]
    linear_combination e'
  have hqdeg : q.natDegree = 2 := by simp only [q]; compute_degree!
  have hq0 : q ≠ 0 := fun h => by rw [h, natDegree_zero] at hqdeg; exact absurd hqdeg (by decide)
  have hint : IsIntegral K0 w := (show IsAlgebraic K0 w from ⟨q, hq0, hq⟩).isIntegral
  have hdeg : (minpoly K0 w).natDegree = 2 := by
    have hle2 : (minpoly K0 w).natDegree ≤ 2 := by
      rw [← hqdeg]; exact natDegree_le_of_dvd (minpoly.dvd K0 _ hq) hq0
    have hne1 : (minpoly K0 w).natDegree ≠ 1 := by
      intro h1
      rw [minpoly.natDegree_eq_one_iff] at h1
      obtain ⟨z, hz⟩ := h1
      have hw : w ∈ K0 := by rw [← hz]; exact z.2
      exact genY_pow_not_mem E p hw
    have hpos := minpoly.natDegree_pos hint
    omega
  rw [relfinrank_eq_finrank_of_le hle, ← hext, adjoin.finrank hint, hdeg]

/- English proof (translation)
Establish `hx : F⟮genX E ^ p⟯ ≤ F⟮genX E⟯` using `adjoin_simple_le_iff.mpr (pow_mem (mem_adjoin_simple_self F _) p)`. Establish `hle : F⟮genX E ^ p⟯ ≤ powField E p` using `adjoin_simple_le_iff.mpr (subset_adjoin F _ (by simp))`. Establish `t1` using `relfinrank_mul_relfinrank hx (le_top : F⟮genX E⟯ ≤ ⊤)`. Establish `t2` using `relfinrank_mul_relfinrank hle (le_top : powField E p ≤ ⊤)`. Rewrite `t1` using `[relfinrank_adjoin_genX_pow, relfinrank_top_right, finrank_adjoin_genX]`.

Rewrite `t2` using `[relfinrank_powField, ← t1, relfinrank_top_right]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_powField : Module.finrank (powField E p) E.toAffine.FunctionField = p := by
  have hx : F⟮genX E ^ p⟯ ≤ F⟮genX E⟯ :=
    adjoin_simple_le_iff.mpr (pow_mem (mem_adjoin_simple_self F _) p)
  have hle : F⟮genX E ^ p⟯ ≤ powField E p := adjoin_simple_le_iff.mpr (subset_adjoin F _ (by simp))
  have t1 := relfinrank_mul_relfinrank hx (le_top : F⟮genX E⟯ ≤ ⊤)
  have t2 := relfinrank_mul_relfinrank hle (le_top : powField E p ≤ ⊤)
  rw [relfinrank_adjoin_genX_pow, relfinrank_top_right, finrank_adjoin_genX] at t1
  rw [relfinrank_powField, ← t1, relfinrank_top_right] at t2
  omega

end Pow

end GroundTheory.Arith.Abelian
