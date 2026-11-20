import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.UnramCard

/- English proof (translation)
Establish `h : Ideal.span {a * b} = a • Ideal.span {b}`. Rewrite using `[← Ideal.span_singleton_mul_span_singleton, ← Submodule.ideal_span_singleton_smul, smul_eq_mul]`. Rewrite using `[h]`. Establish `hi` using `Ideal.mulQuot_injective (Ideal.span {b}) ha`. Establish `hs` using `Ideal.quotOfMul_surjective (a := a) (Ideal.span {b})`.

Establish `he` using `Ideal.exact_mulQuot_quotOfMul (a := a) (Ideal.span {b})`. Rewrite using `[Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (Ideal.quotOfMul a (Ideal.span {b}))), Nat.card_congr (LinearMap.quotKerEquivOfSurjective _ hs).toEquiv, he.linearMap_ker_eq, ← Nat.card_congr (LinearEquiv.ofInjective _ hi).toEquiv, mul_comm]`.
-/
theorem card_quot_mul {R : Type*} [CommRing R] {a : R} (ha : a ∈ nonZeroDivisors R) (b : R) :
    Nat.card (R ⧸ Ideal.span {a * b}) =
      Nat.card (R ⧸ Ideal.span {a}) * Nat.card (R ⧸ Ideal.span {b}) := by
  have h : Ideal.span {a * b} = a • Ideal.span {b} := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← Submodule.ideal_span_singleton_smul,
      smul_eq_mul]
  rw [h]
  have hi := Ideal.mulQuot_injective (Ideal.span {b}) ha
  have hs := Ideal.quotOfMul_surjective (a := a) (Ideal.span {b})
  have he := Ideal.exact_mulQuot_quotOfMul (a := a) (Ideal.span {b})
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (Ideal.quotOfMul a (Ideal.span {b}))),
    Nat.card_congr (LinearMap.quotKerEquivOfSurjective _ hs).toEquiv, he.linearMap_ker_eq,
    ← Nat.card_congr (LinearEquiv.ofInjective _ hi).toEquiv, mul_comm]

/- English proof (translation)
Use `(Nat.card_congr (Ideal.quotientEquiv (Ideal.span {a}) (Ideal.span {c a}) c ?_).toEquiv).symm` and prove the remaining obligations. Rewrite using `[Ideal.map_span]`. Simplify using the standard rewrite rules.
-/
theorem card_quot_map {R : Type*} [CommRing R] (c : R ≃+* R) (a : R) :
    Nat.card (R ⧸ Ideal.span {c a}) = Nat.card (R ⧸ Ideal.span {a}) := by
  refine (Nat.card_congr (Ideal.quotientEquiv (Ideal.span {a}) (Ideal.span {c a}) c ?_).toEquiv).symm
  rw [Ideal.map_span]
  simp

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L ϖ hϖ δ hδ`. Take `⟨-, h2, -, -, h5, h6, -, -⟩` from `GlobalTheory.UnramOrder.order_facts L ϖ hϖ`. Take `⟨-, -, v3, v4⟩` from `GlobalTheory.UnramVal.vE_valuation L ϖ hϖ`. Take `⟨hcm, -, n, hn⟩` from `h2 δ δ.2`. Establish `hinj` using `GlobalTheory.UnramOrder.algebraMap_inj L`.

Establish `hE : Nontrivial E` using `hinj.nontrivial`. Establish `hn0 : (n : F) ≠ 0`. Introduce `h`. Rewrite `hn` using `[h, map_zero]`. Conclude with `(hδ.mul (hδ.map L.cj)).ne_zero hn`.

Rewrite using `[hn]`. Establish `hv : 0 ≤ vE L ϖ (algebraMap F E (n : F))` using `(v3 _ hn0).2 n.2`. Use `⟨hv, ?_⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `v4 _ hn0`. Take `⟨j, hj⟩` from `Int.eq_ofNat_of_zero_le hv`.

Rewrite `hu` using `[hj, zpow_natCast]`. Rewrite using `[hj, Int.toNat_natCast]`. Set `c : L.O ≃+* L.O` to `{ toFun := fun x => ⟨L.cj x, GlobalTheory.UnramOrder.cj_mem L x.2⟩ invFun := fun x => ⟨L.cj x, GlobalTheory.UnramOrder.cj_mem L x.2⟩ left_inv := fun x => Subtype.ext (L.cj_cj x) right_inv := fun x => Subtype.ext (L.cj_cj x) map_mul' := fun x y => Subtype.ext (map_mul L.cj (x : E) …`. Establish `hnz : δ ∈ nonZeroDivisors L.O`. Rewrite using `[mem_nonZeroDivisors_iff_right]`.

Introduce `x hx`. Establish `hx' : (x : E) * δ = 0` using `by exact_mod_cast congrArg Subtype.val hx`. Conclude with `Subtype.ext (hδ.mul_left_eq_zero.1 hx')`. Establish `hmul` using `card_quot_mul hnz (c δ)`. Rewrite `hmul` using `[card_quot_map]`.

Set `ι : 𝒪[F] →+* L.O` to `((algebraMap F E).comp (𝒪[F]).subtype).codRestrict L.O (fun x => (h5 _).2 x.2)`. Establish `hset : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)} = {ι (ϖ ^ j)}`. Use extensionality with `y`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Subtype.ext_iff]`. Both sides reduce to the same expression.

Establish `hprod : δ * c δ = ι (ϖ ^ j) * ι u`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(δ : E) * L.cj δ = algebraMap F E ((ϖ : F) ^ j) * algebraMap F E ((u : 𝒪[F]) : F)`. Rewrite using `[hn, ← map_mul, ← hu]`. Establish `h7` using `h6 j`.

Rewrite `h7` using `[hset]`. Rewrite `hmul` using `[hprod, Ideal.span_singleton_mul_right_unit (u.isUnit.map ι), h7, two_mul, pow_add]`. Conclude with `(Nat.mul_self_inj.1 hmul).symm`.
-/
theorem card_quot_eq_pow : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ δ : L.O, IsUnit (δ : E) → 0 ≤ vE L ϖ ((δ : E) * L.cj δ) ∧ Nat.card (L.O ⧸ Ideal.span {δ}) = resQ ϖ ^ (vE L ϖ ((δ : E) * L.cj δ)).toNat := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ δ hδ
  obtain ⟨-, h2, -, -, h5, h6, -, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  obtain ⟨-, -, v3, v4⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  obtain ⟨hcm, -, n, hn⟩ := h2 δ δ.2
  have hinj := GlobalTheory.UnramOrder.algebraMap_inj L
  have hE : Nontrivial E := hinj.nontrivial
  have hn0 : (n : F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hn
    exact (hδ.mul (hδ.map L.cj)).ne_zero hn
  rw [hn]
  have hv : 0 ≤ vE L ϖ (algebraMap F E (n : F)) := (v3 _ hn0).2 n.2
  refine ⟨hv, ?_⟩
  obtain ⟨u, hu⟩ := v4 _ hn0
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le hv
  rw [hj, zpow_natCast] at hu
  rw [hj, Int.toNat_natCast]
  let c : L.O ≃+* L.O :=
    { toFun := fun x => ⟨L.cj x, GlobalTheory.UnramOrder.cj_mem L x.2⟩
      invFun := fun x => ⟨L.cj x, GlobalTheory.UnramOrder.cj_mem L x.2⟩
      left_inv := fun x => Subtype.ext (L.cj_cj x)
      right_inv := fun x => Subtype.ext (L.cj_cj x)
      map_mul' := fun x y => Subtype.ext (map_mul L.cj (x : E) y)
      map_add' := fun x y => Subtype.ext (map_add L.cj (x : E) y) }
  have hnz : δ ∈ nonZeroDivisors L.O := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    have hx' : (x : E) * δ = 0 := by exact_mod_cast congrArg Subtype.val hx
    exact Subtype.ext (hδ.mul_left_eq_zero.1 hx')
  have hmul := card_quot_mul hnz (c δ)
  rw [card_quot_map] at hmul
  let ι : 𝒪[F] →+* L.O :=
    ((algebraMap F E).comp (𝒪[F]).subtype).codRestrict L.O (fun x => (h5 _).2 x.2)
  have hset : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)} = {ι (ϖ ^ j)} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Subtype.ext_iff]
    rfl
  have hprod : δ * c δ = ι (ϖ ^ j) * ι u := by
    apply Subtype.ext
    change (δ : E) * L.cj δ = algebraMap F E ((ϖ : F) ^ j) * algebraMap F E ((u : 𝒪[F]) : F)
    rw [hn, ← map_mul, ← hu]
  have h7 := h6 j
  rw [hset] at h7
  rw [hprod, Ideal.span_singleton_mul_right_unit (u.isUnit.map ι), h7, two_mul, pow_add] at hmul
  exact (Nat.mul_self_inj.1 hmul).symm

end GlobalTheory.UnramCard
