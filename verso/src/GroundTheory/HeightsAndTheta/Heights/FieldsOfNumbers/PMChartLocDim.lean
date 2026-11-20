import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsMChart
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocQuot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace MChartLocDim

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

/- English proof (translation)
Establish `h` using `IsWeightedHomogeneous.prod (R := F) (w := blockWeight ι) Finset.univ (fun k => (X ⟨k, u k⟩ : MRing ι F) ^ b k) (fun k => b k • blockWeight ι ⟨k, u k⟩) (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, u k⟩).pow (b k))`. Unfold `IsMultiHomog chartMonomial`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Simplify using `[blockWeight, Finset.sum_apply, Pi.single_apply]`.
-/
theorem chartMonomial_isMultiHomog (u : ∀ k, ι k) (b : K → ℕ) :
    IsMultiHomog (chartMonomial (F := F) u b) b := by
  have h := IsWeightedHomogeneous.prod (R := F) (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, u k⟩ : MRing ι F) ^ b k) (fun k => b k • blockWeight ι ⟨k, u k⟩)
    (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, u k⟩).pow (b k))
  unfold IsMultiHomog chartMonomial
  convert h using 1
  funext j
  simp [blockWeight, Finset.sum_apply, Pi.single_apply]

omit [DecidableEq K] in

/- English proof (translation)
Unfold `chartMonomial`. Rewrite using `[Ideal.IsPrime.prod_mem_iff]`. Introduce and unpack `⟨k, -, hk⟩`. Conclude with `hu k (Ideal.IsPrime.mem_of_pow_mem inferInstance _ hk)`.
-/
theorem chartMonomial_not_mem (Q : Ideal (MRing ι F)) [Q.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) (b : K → ℕ) : chartMonomial u b ∉ Q := by
  unfold chartMonomial
  rw [Ideal.IsPrime.prod_mem_iff]
  rintro ⟨k, -, hk⟩
  exact hu k (Ideal.IsPrime.mem_of_pow_mem inferInstance _ hk)

omit [Fintype K] [DecidableEq K] in

/- English proof (translation)
Rewrite using `[Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hg`.
-/
theorem algebraMap_mk_ne_zero (Q : Ideal (MRing ι F)) [Q.IsPrime] {g : MRing ι F} (hg : g ∉ Q) :
    algebraMap (MRing ι F ⧸ Q) (FractionRing (MRing ι F ⧸ Q)) (Ideal.Quotient.mk Q g) ≠ 0 := by
  rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  exact hg

omit [DecidableEq K] in

/- English proof (translation)
Rewrite using `[chartIdeal, RingHom.mem_ker, hp, div_eq_zero_iff, or_iff_left (algebraMap_mk_ne_zero Q (chartMonomial_not_mem Q u hu b)), IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`.
-/
theorem mem_chartIdeal_iff (Q : Ideal (MRing ι F)) [Q.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) {p h : MRing ι F} {b : K → ℕ}
    (hp : chartMap Q u p = algebraMap (MRing ι F ⧸ Q) (FractionRing (MRing ι F ⧸ Q))
      (Ideal.Quotient.mk Q h) / algebraMap (MRing ι F ⧸ Q) _ (Ideal.Quotient.mk Q (chartMonomial u b))) :
    p ∈ chartIdeal Q u ↔ h ∈ Q := by
  rw [chartIdeal, RingHom.mem_ker, hp, div_eq_zero_iff,
    or_iff_left (algebraMap_mk_ne_zero Q (chartMonomial_not_mem Q u hu b)),
    IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

omit [Fintype K] in

/- English proof (translation)
Establish `hr : (chartMap P u).range ≤ degZeroLoc P {W}`. Rewrite using `[chartMap, aeval_range, Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨v, rfl⟩`. Conclude with `div_mem_degZeroLoc P {W} (isWeightedHomogeneous_X F (blockWeight ι) v) (isWeightedHomogeneous_X F (blockWeight ι) ⟨v.1, u v.1⟩) (fun h => hu v.1 (hPW h)) (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hu v.1)`. Conclude with `hr ⟨p, rfl⟩`.
-/
theorem chartMap_mem (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) (p : MRing ι F) : chartMap P u p ∈ degZeroLoc P {W} := by
  have hr : (chartMap P u).range ≤ degZeroLoc P {W} := by
    rw [chartMap, aeval_range, Algebra.adjoin_le_iff]
    rintro _ ⟨v, rfl⟩
    exact div_mem_degZeroLoc P {W} (isWeightedHomogeneous_X F (blockWeight ι) v)
      (isWeightedHomogeneous_X F (blockWeight ι) ⟨v.1, u v.1⟩)
      (fun h => hu v.1 (hPW h)) (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hu v.1)
  exact hr ⟨p, rfl⟩

def toLoc (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) : (MRing ι F ⧸ chartIdeal P u) →+* degZeroLoc P {W} :=
  Ideal.Quotient.lift (chartIdeal P u)
    ((chartMap P u).toRingHom.codRestrict (degZeroLoc P {W}) (chartMap_mem P W hPW u hu))
    (fun _ ha => Subtype.ext (RingHom.mem_ker.mp ha))

end MChartLocDim

open MChartLocDim in

/- English proof (translation)
Introduce `F _ K _ _ ι _ P W _ _ hPW u hu`. Establish `huP : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P` using `fun k h => hu k (hPW h)`. Establish `hle : chartIdeal P u ≤ chartIdeal W u`. Introduce `p hp`. Take `⟨b, h, -, hQ⟩` from `h₃ F K ι u p`.

Conclude with `(mem_chartIdeal_iff W u hu (hQ W hu)).2 (hPW ((mem_chartIdeal_iff P u huP (hQ P huP)).1 hp))`. Use `set q := (chartIdeal W u).map (Ideal.Quotient.mk (chartIdeal P u))`. Establish `: q.IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hle)`. Set `_` to `(toLoc P W hPW u hu).toAlgebra`. Establish `hmap : ∀ p, ((algebraMap (MRing ι F ⧸ chartIdeal P u) (degZeroLoc P {W}) (Ideal.Quotient.mk _ p) : degZeroLoc P {W}) : FractionRing (MRing ι F ⧸ P)) = chartMap P u p` using `fun p => rfl`.

Establish `hmemq : ∀ p, Ideal.Quotient.mk (chartIdeal P u) p ∈ q ↔ p ∈ chartIdeal W u` using `fun p => Ideal.mem_quotient_iff_mem hle`. Establish `: IsLocalization.AtPrime (degZeroLoc P {W}) q`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨a, ha⟩`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective a`.

Establish `hpW : p ∉ chartIdeal W u` using `fun h => ha ((hmemq p).2 h)`. Take `⟨b, h, hh, hQ⟩` from `h₃ F K ι u p`. Establish `hhW : h ∉ W` using `fun h' => hpW ((mem_chartIdeal_iff W u hu (hQ W hu)).2 h')`. Establish `hinv` using `div_mem_degZeroLoc P {W} (chartMonomial_isMultiHomog u b) hh (fun h' => hhW (hPW h')) (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hhW)`. Use `IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_)` and prove the remaining obligations.

Rewrite using `[Subalgebra.coe_mul, hmap, hQ P huP, Subalgebra.coe_one, div_mul_div_comm, mul_comm, div_self]`. Conclude with `mul_ne_zero (algebraMap_mk_ne_zero P (chartMonomial_not_mem P u huP b)) (algebraMap_mk_ne_zero P (fun h' => hhW (hPW h')))`. Introduce and unpack `⟨x, hx⟩`. Take `⟨b, f, g, hf, hg, hgP, hgW, rfl⟩` from `h₁ F K ι P {W} (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; infer_instance) x hx`. Establish `hgW' : g ∉ W` using `hgW W rfl`.

Establish `hgq : Ideal.Quotient.mk (chartIdeal P u) g ∈ q.primeCompl` using `fun h' => hgW' ((mem_chartIdeal_iff W u hu (h₂ F K ι W u hu g b hg)).1 ((hmemq g).1 h'))`. Use `⟨(Ideal.Quotient.mk _ f, ⟨_, hgq⟩), Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Subalgebra.coe_mul, hmap, hmap, h₂ F K ι P u huP g b hg, h₂ F K ι P u huP f b hf]`. Establish `h1` using `algebraMap_mk_ne_zero P (chartMonomial_not_mem P u huP b)`. Establish `h2` using `algebraMap_mk_ne_zero P hgP`.

Clear the denominators using the available nonvanishing facts. Introduce `a c hac`. Use `⟨1, ?_⟩` and prove the remaining obligations. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Take `⟨p', rfl⟩` from `Ideal.Quotient.mk_surjective c`.

Establish `h` using `congrArg Subtype.val hac`. Rewrite `h` using `[hmap, hmap, ← sub_eq_zero, ← map_sub]`. Rewrite using `[Submonoid.coe_one, one_mul, one_mul]`. Conclude with `Ideal.Quotient.eq.mpr (RingHom.mem_ker.mpr h)`. Conclude with `IsLocalization.AtPrime.ringKrullDim_eq_height q (degZeroLoc P {W})`.
-/
theorem MChartLocDim.proof (h₁ : DegZeroLocQuot.Statement.{u}) (h₂ : MChartDehomog.Statement.{u})
    (h₃ : MChartHomog.Statement.{u}) : MChartLocDim.Statement.{u} := by
  intro F _ K _ _ ι _ P W _ _ hPW u hu
  have huP : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P := fun k h => hu k (hPW h)
  have hle : chartIdeal P u ≤ chartIdeal W u := by
    intro p hp
    obtain ⟨b, h, -, hQ⟩ := h₃ F K ι u p
    exact (mem_chartIdeal_iff W u hu (hQ W hu)).2 (hPW ((mem_chartIdeal_iff P u huP (hQ P huP)).1 hp))
  set q := (chartIdeal W u).map (Ideal.Quotient.mk (chartIdeal P u))
  have : q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hle)
  let _ := (toLoc P W hPW u hu).toAlgebra
  have hmap : ∀ p, ((algebraMap (MRing ι F ⧸ chartIdeal P u) (degZeroLoc P {W})
      (Ideal.Quotient.mk _ p) : degZeroLoc P {W}) : FractionRing (MRing ι F ⧸ P)) = chartMap P u p :=
    fun p => rfl
  have hmemq : ∀ p, Ideal.Quotient.mk (chartIdeal P u) p ∈ q ↔ p ∈ chartIdeal W u :=
    fun p => Ideal.mem_quotient_iff_mem hle
  have : IsLocalization.AtPrime (degZeroLoc P {W}) q := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨a, ha⟩
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      have hpW : p ∉ chartIdeal W u := fun h => ha ((hmemq p).2 h)
      obtain ⟨b, h, hh, hQ⟩ := h₃ F K ι u p
      have hhW : h ∉ W := fun h' => hpW ((mem_chartIdeal_iff W u hu (hQ W hu)).2 h')
      have hinv := div_mem_degZeroLoc P {W} (chartMonomial_isMultiHomog u b) hh (fun h' => hhW (hPW h'))
        (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hhW)
      refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_)
      rw [Subalgebra.coe_mul, hmap, hQ P huP, Subalgebra.coe_one,
        div_mul_div_comm, mul_comm, div_self]
      exact mul_ne_zero (algebraMap_mk_ne_zero P (chartMonomial_not_mem P u huP b))
        (algebraMap_mk_ne_zero P (fun h' => hhW (hPW h')))
    · rintro ⟨x, hx⟩
      obtain ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩ := h₁ F K ι P {W}
        (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; infer_instance) x hx
      have hgW' : g ∉ W := hgW W rfl
      have hgq : Ideal.Quotient.mk (chartIdeal P u) g ∈ q.primeCompl := fun h' =>
        hgW' ((mem_chartIdeal_iff W u hu (h₂ F K ι W u hu g b hg)).1 ((hmemq g).1 h'))
      refine ⟨(Ideal.Quotient.mk _ f, ⟨_, hgq⟩), Subtype.ext ?_⟩
      rw [Subalgebra.coe_mul, hmap, hmap, h₂ F K ι P u huP g b hg, h₂ F K ι P u huP f b hf]
      have h1 := algebraMap_mk_ne_zero P (chartMonomial_not_mem P u huP b)
      have h2 := algebraMap_mk_ne_zero P hgP
      field_simp
    · intro a c hac
      refine ⟨1, ?_⟩
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨p', rfl⟩ := Ideal.Quotient.mk_surjective c
      have h := congrArg Subtype.val hac
      rw [hmap, hmap, ← sub_eq_zero, ← map_sub] at h
      rw [Submonoid.coe_one, one_mul, one_mul]
      exact Ideal.Quotient.eq.mpr (RingHom.mem_ker.mpr h)
  exact IsLocalization.AtPrime.ringKrullDim_eq_height q (degZeroLoc P {W})

end

end GroundTheory.Heights₂.Heights.FieldNumbers
