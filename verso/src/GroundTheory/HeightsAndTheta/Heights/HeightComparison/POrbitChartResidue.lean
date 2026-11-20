import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartResidue
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartMax
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartQuot
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartDehom
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

/- English proof (translation)
Use `isJacobsonRing_iff_prime_eq.mpr fun P hP ↦ ?_` and prove the remaining obligations. Distinguish the cases in `h : P = ⊥`. Substitute `h` using the available equality. Use `le_antisymm (fun a ha ↦ ?_) Ideal.le_jacobson` and prove the remaining obligations. Rewrite `ha` using `[Ideal.mem_jacobson_bot]`.

Establish `h1` using `Int.isUnit_iff.mp (ha 1)`. Establish `h2` using `Int.isUnit_iff.mp (ha (-1))`. Rewrite using `[Ideal.mem_bot]`. Use linear arithmetic over natural numbers and integers. Use `hP.isMaximal h` as an intermediate fact.

Conclude with `Ideal.jacobson_eq_self_of_isMaximal`.
-/
theorem int_isJacobsonRing : IsJacobsonRing ℤ := by
  refine isJacobsonRing_iff_prime_eq.mpr fun P hP ↦ ?_
  by_cases h : P = ⊥
  · subst h
    refine le_antisymm (fun a ha ↦ ?_) Ideal.le_jacobson
    rw [Ideal.mem_jacobson_bot] at ha
    have h1 := Int.isUnit_iff.mp (ha 1)
    have h2 := Int.isUnit_iff.mp (ha (-1))
    rw [Ideal.mem_bot]
    omega
  · have := hP.isMaximal h
    exact Ideal.jacobson_eq_self_of_isMaximal

/- English proof (translation)
Use `int_isJacobsonRing` as an intermediate fact. Establish `: Module.Finite ℤ F` using `finite_of_finite_type_of_isJacobsonRing ℤ F`. Establish `hq : q ≠ 0`. Introduce and unpack `rfl`. Establish `: CharZero F` using `CharP.charP_to_charZero F`.

Conclude with `Int.not_isField (isField_of_isIntegral_of_isField (fun a b h ↦ by simpa using h) (Field.toIsField F))`. Establish `hqp : q.Prime` using `(CharP.char_is_prime_or_zero F q).resolve_right hq`. Establish `: Fact q.Prime` using `⟨hqp⟩`. Set `: Algebra (ZMod q) F` to `ZMod.algebra F q`. Establish `: Module.Finite (ZMod q) F` using `Module.Finite.of_restrictScalars_finite ℤ (ZMod q) F`.

Establish `: Finite F` using `Module.finite_of_finite (ZMod q)`. Establish `: Fintype F` using `Fintype.ofFinite F`. Use `⟨hqp, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.length_eq_of_surjective (S := ℤ) (R := ZMod q) (M := F) (ZMod.intCast_surjective), Module.length_eq_finrank, ENat.toNat_natCast, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod q), ZMod.card]`.
-/
theorem natCard_eq_pow_length_of_finiteType (F : Type) [Field F] [Algebra.FiniteType ℤ F]
    (q : ℕ) [CharP F q] :
    q.Prime ∧ Nat.card F = q ^ (Module.length ℤ F).toNat := by
  have := int_isJacobsonRing
  have : Module.Finite ℤ F := finite_of_finite_type_of_isJacobsonRing ℤ F
  have hq : q ≠ 0 := by
    rintro rfl
    have : CharZero F := CharP.charP_to_charZero F
    exact Int.not_isField (isField_of_isIntegral_of_isField
      (fun a b h ↦ by simpa using h) (Field.toIsField F))
  have hqp : q.Prime := (CharP.char_is_prime_or_zero F q).resolve_right hq
  have : Fact q.Prime := ⟨hqp⟩
  let : Algebra (ZMod q) F := ZMod.algebra F q
  have : Module.Finite (ZMod q) F := Module.Finite.of_restrictScalars_finite ℤ (ZMod q) F
  have : Finite F := Module.finite_of_finite (ZMod q)
  have : Fintype F := Fintype.ofFinite F
  refine ⟨hqp, ?_⟩
  rw [Module.length_eq_of_surjective (S := ℤ) (R := ZMod q) (M := F) (ZMod.intCast_surjective),
    Module.length_eq_finrank, ENat.toNat_natCast, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod q), ZMod.card]

/- English proof (translation)
Introduce `ι _ _ _ n A x s hx hs V hV c hc`. Establish `hPV : orbitIdeal x ≤ V` using `le_sup_left.trans hV.1.1.2`. Establish `hrel : Geo.IsRelevant V` using `hV.2`. Establish `hxc : ∀ c' : (k : ι) → Fin (n k + 1), (∀ k, (X ⟨k, c' k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) → ∀ k, x k (c' k) ≠ 0`. Introduce `c' h k h0`.

Apply `h k` to reduce the goal to its premises. Apply `hPV` to reduce the goal to its premises. Rewrite using `[orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]`. Simplify using `[flatCone, h0]`. Use `set i : (k : ι) → Fin (n k + 1) := fun k ↦ (hrel k).choose`.

Establish `hi : ∀ k, (X ⟨k, i k⟩ : MvPolynomial (Coord n) ℤ) ∉ V` using `fun k ↦ (hrel k).choose_spec`. Take `⟨eQ⟩` from `hQ ι n x c (hxc c hc) V hPV`. Take `⟨hchar, ⟨eD⟩⟩` from `hD ι n A x s hx hs V hV i c hi hc`. Use `set J := V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, i k⟩ : MvPolynomial (Coord n) ℤ) - 1)`. Set `e : (chartRing x c ⧸ chartPoint x c V) ≃+* (MvPolynomial (Coord n) ℤ ⧸ J)` to `eQ.trans eD.symm`.

Use `hM ι n A x s hx hs V hV c hc` as an intermediate fact. Establish `hfield : IsField (MvPolynomial (Coord n) ℤ ⧸ J)` using `MulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance) e.symm.toMulEquiv`. Establish `: J.IsMaximal` using `(Ideal.Quotient.maximal_ideal_iff_isField_quotient J).mpr hfield`. Set `: Field (MvPolynomial (Coord n) ℤ ⧸ J)` to `Ideal.Quotient.field J`. Establish `hft : Algebra.FiniteType ℤ (MvPolynomial (Coord n) ℤ ⧸ J)` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ J) (Ideal.Quotient.mkₐ_surjective ℤ J)`.

Establish `: CharP (MvPolynomial (Coord n) ℤ ⧸ J) (Geo.charOf V)`. Prove the components needed by the constructor for the conclusion. Introduce `a`. Establish `hJC : ∀ b : ℤ, ((b : MvPolynomial (Coord n) ℤ ⧸ J) = 0 ↔ b ∈ V.comap (C : ℤ →+* _))`. Introduce `b`.

Rewrite using `[(map_intCast (Ideal.Quotient.mk J) b).symm.trans (congrArg _ (eq_intCast C b).symm), Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hchar]`. Rewrite using `[← Int.cast_natCast, hJC, Submodule.IsPrincipal.mem_iff_generator_dvd, ← Int.natAbs_dvd, Int.natCast_dvd_natCast]`. Both sides reduce to the same expression. Apply the tactic sequence `obtain ⟨-, hcard⟩ := @natCard_eq_pow_length_of_finiteType (MvPolynomial (Coord n) ℤ ⧸ J) _ (by convert hft using 1 <;> rfl) (Geo.charOf V) _`. Establish `hgeo : Geo.geoNum (ι` using `blockIdx n) 0 V Fin.elim0 = ((Module.length ℤ (MvPolynomial (Coord n) ℤ ⧸ J)).toNat : ℤ) := by`.

Simplify using `only [Geo.geoNum, dif_pos hrel]`. Both sides reduce to the same expression. Rewrite using `[hgeo, Nat.card_congr e.toEquiv, hcard, Nat.cast_pow, Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem OrbitChartResidue.proof (hM : OrbitChartMax.Statement) (hQ : OrbitChartQuot.Statement)
    (hD : OrbitChartDehom.Statement) : OrbitChartResidue.Statement := by
  intro ι _ _ _ n A x s hx hs V hV c hc
  have hPV : orbitIdeal x ≤ V := le_sup_left.trans hV.1.1.2
  have hrel : Geo.IsRelevant V := hV.2
  have hxc : ∀ c' : (k : ι) → Fin (n k + 1),
      (∀ k, (X ⟨k, c' k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) → ∀ k, x k (c' k) ≠ 0 := by
    intro c' h k h0
    apply h k
    apply hPV
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
    simp [flatCone, h0]
  set i : (k : ι) → Fin (n k + 1) := fun k ↦ (hrel k).choose
  have hi : ∀ k, (X ⟨k, i k⟩ : MvPolynomial (Coord n) ℤ) ∉ V := fun k ↦ (hrel k).choose_spec
  obtain ⟨eQ⟩ := hQ ι n x c (hxc c hc) V hPV
  obtain ⟨hchar, ⟨eD⟩⟩ := hD ι n A x s hx hs V hV i c hi hc
  set J := V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, i k⟩ : MvPolynomial (Coord n) ℤ) - 1)
  let e : (chartRing x c ⧸ chartPoint x c V) ≃+* (MvPolynomial (Coord n) ℤ ⧸ J) := eQ.trans eD.symm
  have := hM ι n A x s hx hs V hV c hc
  have hfield : IsField (MvPolynomial (Coord n) ℤ ⧸ J) :=
    MulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance)
      e.symm.toMulEquiv
  have : J.IsMaximal := (Ideal.Quotient.maximal_ideal_iff_isField_quotient J).mpr hfield
  let : Field (MvPolynomial (Coord n) ℤ ⧸ J) := Ideal.Quotient.field J
  have hft : Algebra.FiniteType ℤ (MvPolynomial (Coord n) ℤ ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ J)
      (Ideal.Quotient.mkₐ_surjective ℤ J)
  have : CharP (MvPolynomial (Coord n) ℤ ⧸ J) (Geo.charOf V) := by
    constructor
    intro a
    have hJC : ∀ b : ℤ, ((b : MvPolynomial (Coord n) ℤ ⧸ J) = 0 ↔ b ∈ V.comap (C : ℤ →+* _)) := by
      intro b
      rw [(map_intCast (Ideal.Quotient.mk J) b).symm.trans (congrArg _ (eq_intCast C b).symm),
        Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hchar]
    rw [← Int.cast_natCast, hJC, Submodule.IsPrincipal.mem_iff_generator_dvd, ← Int.natAbs_dvd,
      Int.natCast_dvd_natCast]
    rfl
  obtain ⟨-, hcard⟩ := @natCard_eq_pow_length_of_finiteType (MvPolynomial (Coord n) ℤ ⧸ J) _
    (by convert hft using 1 <;> rfl) (Geo.charOf V) _
  have hgeo : Geo.geoNum (ι := blockIdx n) 0 V Fin.elim0 =
      ((Module.length ℤ (MvPolynomial (Coord n) ℤ ⧸ J)).toNat : ℤ) := by
    simp only [Geo.geoNum, dif_pos hrel]
    rfl
  rw [hgeo, Nat.card_congr e.toEquiv, hcard, Nat.cast_pow, Real.log_pow]
  push_cast
  ring

end GroundTheory.Heights₂.Heights
