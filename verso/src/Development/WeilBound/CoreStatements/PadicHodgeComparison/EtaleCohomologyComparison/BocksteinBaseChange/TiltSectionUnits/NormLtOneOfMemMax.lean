import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.IsUnitWitt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TiltSectionUnits.ResAbs

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

/- English proof (translation)
Establish `h : ((algebraMap ℤ_[l] K z : K) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])` using `rfl`. Rewrite using `[h, PadicAlgCl.norm_extends, PadicInt.norm_def]`.
-/
theorem norm_algebraMap_Zl (z : ℤ_[l]) : ‖((algebraMap ℤ_[l] K z : K) : PadicAlgCl l)‖ = ‖z‖ := by
  have h : ((algebraMap ℤ_[l] K z : K) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l]) := rfl
  rw [h, PadicAlgCl.norm_extends, PadicInt.norm_def]

def zToOK : ℤ_[l] →+* OK l K :=
  (algebraMap ℤ_[l] K).codRestrict (OK l K) fun z => (mem_OK _).2 (by
    rw [norm_algebraMap_Zl]; exact PadicInt.norm_le_one z)

abbrev algZ : Algebra ℤ_[l] (OK l K) := (zToOK (K := K)).toAlgebra

attribute [local instance] algZ

/- English proof (translation)
Conclude with `IsScalarTower.of_algebraMap_eq fun _ => rfl`.
-/
theorem towZ : IsScalarTower ℤ_[l] (OK l K) K := by
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

attribute [local instance] towZ

/- English proof (translation)
Establish `key : ∀ x : K, x ∈ OK l K ↔ IsIntegral ℤ_[l] x` using `fun x => by`. Rewrite using `[OK_eq, Subalgebra.mem_toSubring, mem_integralClosure_iff]`. Use `⟨Subtype.coe_injective, fun {x} => ⟨fun hx => ⟨⟨x, (key x).2 hx⟩, rfl⟩, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨y, rfl⟩`. Conclude with `(key y).1 y.2`.
-/
theorem closZ : IsIntegralClosure (OK l K) ℤ_[l] K := by
  have key : ∀ x : K, x ∈ OK l K ↔ IsIntegral ℤ_[l] x := fun x => by
    rw [OK_eq, Subalgebra.mem_toSubring, mem_integralClosure_iff]
  refine ⟨Subtype.coe_injective, fun {x} => ⟨fun hx => ⟨⟨x, (key x).2 hx⟩, rfl⟩, ?_⟩⟩
  rintro ⟨y, rfl⟩
  exact (key y).1 y.2

attribute [local instance] closZ

/- English proof (translation)
Conclude with `norm_algebraMap_Zl z`.
-/
theorem norm_zToOK (z : ℤ_[l]) : ‖(((algebraMap ℤ_[l] (OK l K) z : OK l K) : K) : PadicAlgCl l)‖ = ‖z‖ := by
  exact norm_algebraMap_Zl z

variable [FiniteDimensional ℚ_[l] K]

/- English proof (translation)
Conclude with `⟨fun z hz => PadicInt.isUnit_iff.2 ((norm_zToOK z).symm.trans ((isUnit_OK_iff _).1 hz))⟩`.
-/
theorem locZ : IsLocalHom (algebraMap ℤ_[l] (OK l K)) := by
  exact ⟨fun z hz => PadicInt.isUnit_iff.2 ((norm_zToOK z).symm.trans ((isUnit_OK_iff _).1 hz))⟩

attribute [local instance] locZ

/- English proof (translation)
Conclude with `IsIntegralClosure.finite ℤ_[l] ℚ_[l] K (OK l K)`.
-/
theorem finZ : Module.Finite ℤ_[l] (OK l K) := by
  exact IsIntegralClosure.finite ℤ_[l] ℚ_[l] K (OK l K)

attribute [local instance] finZ

/- English proof (translation)
Establish `: Finite (IsLocalRing.ResidueField ℤ_[l])` using `Finite.of_equiv _ PadicInt.residueField.symm.toEquiv`. Conclude with `Module.finite_of_finite (IsLocalRing.ResidueField ℤ_[l])`.
-/
theorem finite_res : Finite (IsLocalRing.ResidueField (OK l K)) := by
  have : Finite (IsLocalRing.ResidueField ℤ_[l]) := Finite.of_equiv _ PadicInt.residueField.symm.toEquiv
  exact Module.finite_of_finite (IsLocalRing.ResidueField ℤ_[l])

/- English proof (translation)
Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_OK_iff]`. Establish `h : ((((l : ℕ) : OK l K) : K) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])`. Simplify using the standard rewrite rules. Rewrite using `[h, PadicAlgCl.norm_extends, Padic.norm_p]`. Establish `h1 : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`.

Conclude with `(inv_lt_one_of_one_lt₀ h1).ne`.
-/
theorem l_mem_max : ((l : ℕ) : OK l K) ∈ IsLocalRing.maximalIdeal (OK l K) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_OK_iff]
  have h : ((((l : ℕ) : OK l K) : K) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by
    simp
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]
  have h1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  exact (inv_lt_one_of_one_lt₀ h1).ne

instance charP_res : CharP (IsLocalRing.ResidueField (OK l K)) l :=
  (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 (by
    rw [← map_natCast (IsLocalRing.residue (OK l K)), IsLocalRing.residue_eq_zero_iff]
    exact l_mem_max)

instance perf_res : PerfectRing (IsLocalRing.ResidueField (OK l K)) l := by
  have := finite_res (l := l) (K := K)
  infer_instance

/- English proof (translation)
Establish `hl : ((l : ℕ) : ℂ_[l]) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero`. Establish `hmem : (w : ℂ_[l]) / (l : ℂ_[l]) ∈ GroundTheory.PAdicHodge.normInteger ℂ_[l]`. Rewrite using `[GroundTheory.PAdicHodge.mem_normInteger, norm_div]`. Conclude with `div_le_one_of_le₀ h (norm_nonneg _)`. Rewrite using `[Ideal.mem_span_singleton']`.

Use `⟨⟨_, hmem⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hl]`.
-/
theorem mem_span_l_of_norm_le (w : OC l) (h : ‖(w : ℂ_[l])‖ ≤ ‖((l : ℕ) : ℂ_[l])‖) : w ∈ Ideal.span {((l : ℕ) : OC l)} := by
  have hl : ((l : ℕ) : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hmem : (w : ℂ_[l]) / (l : ℂ_[l]) ∈ GroundTheory.PAdicHodge.normInteger ℂ_[l] := by
    rw [GroundTheory.PAdicHodge.mem_normInteger, norm_div]
    exact div_le_one_of_le₀ h (norm_nonneg _)
  rw [Ideal.mem_span_singleton']
  refine ⟨⟨_, hmem⟩, ?_⟩
  apply Subtype.ext
  simp [hl]

/- English proof (translation)
Conclude with `PadicComplex.norm_extends l _`.
-/
theorem norm_okToOC (x : OK l K) : ‖((okToOC l K x : OC l) : ℂ_[l])‖ = ‖((x : K) : PadicAlgCl l)‖ := by
  exact PadicComplex.norm_extends l _

/- English proof (translation)
Establish `h : ((l : ℕ) : ℂ_[l]) = ((algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) : PadicAlgCl l) : ℂ_[l])`. Simplify using the standard rewrite rules. Rewrite using `[h, PadicComplex.norm_extends, PadicAlgCl.norm_extends]`. Conclude with `Padic.norm_p_lt_one`.
-/
theorem norm_l_lt_one : ‖((l : ℕ) : ℂ_[l])‖ < 1 := by
  have h : ((l : ℕ) : ℂ_[l]) = ((algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) : PadicAlgCl l) : ℂ_[l]) := by
    simp
  rw [h, PadicComplex.norm_extends, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

/- English proof (translation)
Rewrite `hm` using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_OK_iff]`. Conclude with `lt_of_le_of_ne (norm_OK_le m) hm`.
-/
theorem norm_lt_one_of_mem_max {m : OK l K} (hm : m ∈ IsLocalRing.maximalIdeal (OK l K)) :
    ‖((m : K) : PadicAlgCl l)‖ < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_OK_iff] at hm
  exact lt_of_le_of_ne (norm_OK_le m) hm

/- English proof (translation)
Use `haveI := OK_dvr (l := l) (K := K)`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible (OK l K)`. Establish `h1` using `norm_lt_one_of_irreducible hϖ`. Establish `h0 : 0 < ‖((l : ℕ) : ℂ_[l])‖` using `norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)`. Take `⟨N, hN⟩` from `exists_pow_lt_of_lt_one h0 h1`.

Use `⟨N, fun y hy => mem_span_l_of_norm_le _ ?_⟩` and prove the remaining obligations. Rewrite `hy` using `[hϖ.maximalIdeal_eq, Ideal.mem_span_singleton']`. Take `⟨u, rfl⟩` from `hy`. Establish `hu : ‖((u : K) : PadicAlgCl l)‖ ≤ 1` using `norm_OK_le u`. Establish `key : ‖(((u * ϖ : OK l K) : K) : PadicAlgCl l)‖ ≤ ‖((ϖ : K) : PadicAlgCl l)‖`.

Establish `e : (((u * ϖ : OK l K) : K) : PadicAlgCl l) = ((u : K) : PadicAlgCl l) * ((ϖ : K) : PadicAlgCl l)`. Use `norm_cast`. Rewrite using `[e, norm_mul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) hu`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[SubmonoidClass.coe_pow, norm_pow]`. Use `_ = ‖(((u * ϖ : OK l K) : K) : PadicAlgCl l)‖ ^ l ^ N := by rw [norm_okToOC]`. Use `_ ≤ ‖((ϖ : K) : PadicAlgCl l)‖ ^ l ^ N := pow_le_pow_left₀ (norm_nonneg _) key _`. Use `_ ≤ ‖((ϖ : K) : PadicAlgCl l)‖ ^ N := pow_le_pow_of_le_one (norm_nonneg _) h1.le (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le`. Use `_ ≤ ‖((l : ℕ) : ℂ_[l])‖ := hN.le`.
-/
theorem exists_pow_mem_span : ∃ n : ℕ, ∀ y ∈ IsLocalRing.maximalIdeal (OK l K),
    okToOC l K y ^ l ^ n ∈ Ideal.span {((l : ℕ) : OC l)} := by
  haveI := OK_dvr (l := l) (K := K)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (OK l K)
  have h1 := norm_lt_one_of_irreducible hϖ
  have h0 : 0 < ‖((l : ℕ) : ℂ_[l])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one h0 h1
  refine ⟨N, fun y hy => mem_span_l_of_norm_le _ ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hy
  obtain ⟨u, rfl⟩ := hy
  have hu : ‖((u : K) : PadicAlgCl l)‖ ≤ 1 := norm_OK_le u
  have key : ‖(((u * ϖ : OK l K) : K) : PadicAlgCl l)‖ ≤ ‖((ϖ : K) : PadicAlgCl l)‖ := by
    have e : (((u * ϖ : OK l K) : K) : PadicAlgCl l) = ((u : K) : PadicAlgCl l) * ((ϖ : K) : PadicAlgCl l) := by
      norm_cast
    rw [e, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hu
  calc ‖((okToOC l K (u * ϖ) ^ l ^ N : OC l) : ℂ_[l])‖
        = ‖((okToOC l K (u * ϖ) : OC l) : ℂ_[l])‖ ^ l ^ N := by
          rw [SubmonoidClass.coe_pow, norm_pow]
    _ = ‖(((u * ϖ : OK l K) : K) : PadicAlgCl l)‖ ^ l ^ N := by rw [norm_okToOC]
    _ ≤ ‖((ϖ : K) : PadicAlgCl l)‖ ^ l ^ N := pow_le_pow_left₀ (norm_nonneg _) key _
    _ ≤ ‖((ϖ : K) : PadicAlgCl l)‖ ^ N :=
          pow_le_pow_of_le_one (norm_nonneg _) h1.le (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
    _ ≤ ‖((l : ℕ) : ℂ_[l])‖ := hN.le

/- English proof (translation)
Introduce `l _ K _`. Take `⟨n, hn⟩` from `exists_pow_mem_span (l := l) (K := K)`. Take `⟨s, hs⟩` from `exists_tilt_section (p := l) (O := OC l) (R := OK l K) (okToOC l K) n hn`. Use `⟨⟨IsLocalRing.ResidueField (OK l K), IsLocalRing.residue (OK l K), IsLocalRing.residue_surjective, s, fun x => ?_⟩⟩` and prove the remaining obligations. Take `⟨a, m, hm, h⟩` from `hs x`.

Rewrite using `[h]`. Establish `ha : ‖(a : ℂ_[l])‖ ≤ 1` using `GroundTheory.PAdicHodge.mem_normInteger.1 a.2`. Establish `hm' : ‖((okToOC l K m : OC l) : ℂ_[l])‖ < 1`. Rewrite using `[norm_okToOC]`. Conclude with `norm_lt_one_of_mem_max hm`.

Establish `hla : ‖((((l : ℕ) : OC l) * a : OC l) : ℂ_[l])‖ < 1`. Establish `e : ((((l : ℕ) : OC l) * a : OC l) : ℂ_[l]) = ((l : ℕ) : ℂ_[l]) * (a : ℂ_[l])`. Use `norm_cast`. Rewrite using `[e, norm_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `e2 : ((((l : ℕ) : OC l) * a + okToOC l K m : OC l) : ℂ_[l]) = ((((l : ℕ) : OC l) * a : OC l) : ℂ_[l]) + ((okToOC l K m : OC l) : ℂ_[l])`. Use `norm_cast`. Rewrite using `[e2]`. Conclude with `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hla hm')`.
-/
theorem resEx : ResEx := by
  intro l _ K _
  obtain ⟨n, hn⟩ := exists_pow_mem_span (l := l) (K := K)
  obtain ⟨s, hs⟩ := exists_tilt_section (p := l) (O := OC l) (R := OK l K) (okToOC l K) n hn
  refine ⟨⟨IsLocalRing.ResidueField (OK l K), IsLocalRing.residue (OK l K),
    IsLocalRing.residue_surjective, s, fun x => ?_⟩⟩
  obtain ⟨a, m, hm, h⟩ := hs x
  rw [h]
  have ha : ‖(a : ℂ_[l])‖ ≤ 1 := GroundTheory.PAdicHodge.mem_normInteger.1 a.2
  have hm' : ‖((okToOC l K m : OC l) : ℂ_[l])‖ < 1 := by
    rw [norm_okToOC]
    exact norm_lt_one_of_mem_max hm
  have hla : ‖((((l : ℕ) : OC l) * a : OC l) : ℂ_[l])‖ < 1 := by
    have e : ((((l : ℕ) : OC l) * a : OC l) : ℂ_[l]) = ((l : ℕ) : ℂ_[l]) * (a : ℂ_[l]) := by
      norm_cast
    rw [e, norm_mul]
    calc ‖((l : ℕ) : ℂ_[l])‖ * ‖(a : ℂ_[l])‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ * 1 :=
          mul_le_mul_of_nonneg_left ha (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact norm_l_lt_one
  have e2 : ((((l : ℕ) : OC l) * a + okToOC l K m : OC l) : ℂ_[l]) =
      ((((l : ℕ) : OC l) * a : OC l) : ℂ_[l]) + ((okToOC l K m : OC l) : ℂ_[l]) := by
    norm_cast
  rw [e2]
  exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hla hm')

end CrystallineSemistableComparison
