import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationRingIntClosure
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.TwoAdicFirst

/- English proof (translation)
Use `fun_prop`.
-/
theorem cont_coe : Continuous fun z : ℤ_[2] => algebraMap ℚ_[2] ℂ_[2] (z : ℚ_[2]) := by
  fun_prop

/- English proof (translation)
Use `map_mem_closure (f := fun z : ℤ_[2] => algebraMap ℚ_[2] ℂ_[2] (z : ℚ_[2])) cont_coe (PadicInt.denseRange_natCast z) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨n, rfl⟩`. Conclude with `⟨n, by simp⟩`.
-/
theorem coe_mem_closure (z : ℤ_[2]) :
    algebraMap ℚ_[2] ℂ_[2] (z : ℚ_[2]) ∈ closure (Set.range (Nat.cast : ℕ → ℂ_[2])) := by
  refine map_mem_closure (f := fun z : ℤ_[2] => algebraMap ℚ_[2] ℂ_[2] (z : ℚ_[2])) cont_coe
    (PadicInt.denseRange_natCast z) ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨n, by simp⟩

/- English proof (translation)
Set `F : Polynomial ℤ_[2]` to `Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (2 * (k : ℤ_[2]))`. Establish `h0 : F.eval 0 = 2 * (k : ℤ_[2])` using `by simp [F]`. Establish `h1 : F.derivative.eval 0 = -1` using `by simp [F]`. Establish `hn : ‖F.eval 0‖ < ‖F.derivative.eval 0‖ ^ 2`. Rewrite using `[h0, h1, norm_neg, norm_one, one_pow, norm_mul]`.

Establish `h2 : ‖(2 : ℤ_[2])‖ < 1`. Use `PadicInt.norm_p (p := 2)` as an intermediate fact. Evaluate the numerical expressions using `at this`. Rewrite using `[this]`. Evaluate the numerical expressions.

Establish `hk : ‖(k : ℤ_[2])‖ ≤ 1` using `PadicInt.norm_le_one _`. Use polynomial arithmetic with `[norm_nonneg (k : ℤ_[2]), norm_nonneg (2 : ℤ_[2])]`. Take `⟨z, hz, -⟩` from `hensels_lemma hn`. Use `⟨z, ?_⟩` and prove the remaining obligations. Simplify `hz` using `[F]`.
-/
theorem exists_root (k : ℕ) : ∃ z : ℤ_[2], z ^ 2 - z + 2 * (k : ℤ_[2]) = 0 := by
  let F : Polynomial ℤ_[2] := Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (2 * (k : ℤ_[2]))
  have h0 : F.eval 0 = 2 * (k : ℤ_[2]) := by simp [F]
  have h1 : F.derivative.eval 0 = -1 := by simp [F]
  have hn : ‖F.eval 0‖ < ‖F.derivative.eval 0‖ ^ 2 := by
    rw [h0, h1, norm_neg, norm_one, one_pow, norm_mul]
    have h2 : ‖(2 : ℤ_[2])‖ < 1 := by
      have := PadicInt.norm_p (p := 2)
      norm_num at this
      rw [this]; norm_num
    have hk : ‖(k : ℤ_[2])‖ ≤ 1 := PadicInt.norm_le_one _
    nlinarith [norm_nonneg (k : ℤ_[2]), norm_nonneg (2 : ℤ_[2])]
  obtain ⟨z, hz, -⟩ := hensels_lemma hn
  refine ⟨z, ?_⟩
  simpa [F] using hz

open GlobalTheory.CompletedBasis

/- English proof (translation)
Take `⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 8 * k` from `⟨(d + 1) / 8, by omega⟩`. Take `⟨z, hz⟩` from `exists_root k`. Set `φ : ℤ_[2] →+* ℂ_[2]` to `(algebraMap ℚ_[2] ℂ_[2]).comp PadicInt.Coe.ringHom`. Use `set u : ℂ_[2] := φ (2 * z - 1) with hu`. Establish `hz' : φ z ^ 2 - φ z + 2 * (k : ℂ_[2]) = 0`.

Use `congrArg φ hz` as an intermediate fact. Simplify `this` using `only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast, map_zero]`. Establish `hk' : (d : ℂ_[2]) + 1 = 8 * (k : ℂ_[2])` using `by exact_mod_cast hk`. Establish `hu2 : u ^ 2 = -(d : ℂ_[2])`. Rewrite using `[hu]`.

Simplify using `only [map_sub, map_mul, map_ofNat, map_one]`. Take the linear combination `4 * hz' + hk'`. Establish `h : (s - u) * (s + u) = 0` using `by linear_combination hs - hu2`. Break down `mul_eq_zero.1 h with h | h` into its components or cases. Conclude with `⟨_, (sub_eq_zero.1 h).symm⟩`.

Use `⟨-(PadicInt.Coe.ringHom (2 * z - 1)), ?_⟩` and prove the remaining obligations. Rewrite using `[map_neg]`. Express the relevant statement in the definitionally equal form `-u = s`. Take the linear combination `-h`.
-/
theorem sq_neg_mem (d : ℕ) (hd : d % 8 = 7) {s : ℂ_[2]} (hs : s ^ 2 = -(d : ℂ_[2])) :
    s ∈ (algebraMap ℚ_[2] ℂ_[2]).fieldRange := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 8 * k := ⟨(d + 1) / 8, by omega⟩
  obtain ⟨z, hz⟩ := exists_root k
  let φ : ℤ_[2] →+* ℂ_[2] := (algebraMap ℚ_[2] ℂ_[2]).comp PadicInt.Coe.ringHom
  set u : ℂ_[2] := φ (2 * z - 1) with hu
  have hz' : φ z ^ 2 - φ z + 2 * (k : ℂ_[2]) = 0 := by
    have := congrArg φ hz
    simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast, map_zero] using this
  have hk' : (d : ℂ_[2]) + 1 = 8 * (k : ℂ_[2]) := by exact_mod_cast hk
  have hu2 : u ^ 2 = -(d : ℂ_[2]) := by
    rw [hu]
    simp only [map_sub, map_mul, map_ofNat, map_one]
    linear_combination 4 * hz' + hk'
  have h : (s - u) * (s + u) = 0 := by linear_combination hs - hu2
  rcases mul_eq_zero.1 h with h | h
  · exact ⟨_, (sub_eq_zero.1 h).symm⟩
  · refine ⟨-(PadicInt.Coe.ringHom (2 * z - 1)), ?_⟩
    rw [map_neg]
    change -u = s
    linear_combination -h

variable (D : D7) (lam : Qbar →+* ℂ_[2])

/- English proof (translation)
Set `S : Subfield D.host.E` to `((algebraMap ℚ_[2] ℂ_[2]).fieldRange).comap (rhoBase D lam)`. Set `F : IntermediateField ℚ D.host.E` to `S.toIntermediateField fun q => by`. Use `⟨(q : ℚ_[2]), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = rhoBase D lam (algebraMap ℚ D.host.E q)`. Rewrite using `[eq_ratCast, map_ratCast, map_ratCast]`.

Establish `hd16 : D.host.d % 16 = 7` using `D.host.hyp.2.2.2.1`. Establish `hb : D.host.sqd ∈ F`. Express the relevant statement in the definitionally equal form `rhoBase D lam (D.host.sqd) ∈ (algebraMap ℚ_[2] ℂ_[2]).fieldRange`. Use `sq_neg_mem D.host.d (by omega) ?_` and prove the remaining obligations. Rewrite using `[← map_pow, D.host.sqd_sq, map_neg, map_natCast]`.

Establish `hle : D.host.K ≤ F` using `IntermediateField.adjoin_simple_le_iff.2 hb`. Conclude with `hle x.2`.
-/
theorem rhoBase_mem_of_K (x : D.host.K) : rhoBase D lam (x : D.host.E) ∈ (algebraMap ℚ_[2] ℂ_[2]).fieldRange := by
  let S : Subfield D.host.E := ((algebraMap ℚ_[2] ℂ_[2]).fieldRange).comap (rhoBase D lam)
  let F : IntermediateField ℚ D.host.E := S.toIntermediateField fun q => by
    refine ⟨(q : ℚ_[2]), ?_⟩
    change _ = rhoBase D lam (algebraMap ℚ D.host.E q)
    rw [eq_ratCast, map_ratCast, map_ratCast]
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hb : D.host.sqd ∈ F := by
    change rhoBase D lam (D.host.sqd) ∈ (algebraMap ℚ_[2] ℂ_[2]).fieldRange
    refine sq_neg_mem D.host.d (by omega) ?_
    rw [← map_pow, D.host.sqd_sq, map_neg, map_natCast]
  have hle : D.host.K ≤ F := IntermediateField.adjoin_simple_le_iff.2 hb
  exact hle x.2

/- English proof (translation)
Take `⟨q, hq⟩` from `rhoBase_mem_of_K D lam (a : D.host.K)`. Establish `hq' : algebraMap ℚ_[2] ℂ_[2] q = rhoK D lam (a : D.host.K)` using `hq`. Establish `hn : ‖q‖ ≤ 1`. Use `norm_le_one_of_mem (rhoK D lam) (mem_intClosure (rhoK D lam) a)` as an intermediate fact. Rewrite `this` using `[← hq', norm_algebraMap']`. Then use the resulting hypothesis.

Use `coe_mem_closure ⟨q, hn⟩` as an intermediate fact. Rewrite `this` using `[show ((⟨q, hn⟩ : ℤ_[2]) : ℚ_[2]) = q from rfl, hq']`. Then use the resulting hypothesis.
-/
theorem rhoK_mem (a : 𝓞 D.host.K) :
    rhoK D lam (a : D.host.K) ∈ closure (Set.range (Nat.cast : ℕ → ℂ_[2])) := by
  obtain ⟨q, hq⟩ := rhoBase_mem_of_K D lam (a : D.host.K)
  have hq' : algebraMap ℚ_[2] ℂ_[2] q = rhoK D lam (a : D.host.K) := hq
  have hn : ‖q‖ ≤ 1 := by
    have := norm_le_one_of_mem (rhoK D lam) (mem_intClosure (rhoK D lam) a)
    rwa [← hq', norm_algebraMap'] at this
  have := coe_mem_closure ⟨q, hn⟩
  rwa [show ((⟨q, hn⟩ : ℤ_[2]) : ℚ_[2]) = q from rfl, hq'] at this

/- English proof (translation)
Introduce `D lam α hα`. Establish `h1 : α.1 ∈ (intClosure (rhoK D lam) : Set ℂ_[2])`. Rewrite using `[← fst_image_OKp]`. Conclude with `⟨α, hα, rfl⟩`. Rewrite `h1` using `[coe_intClosure]`.

Use `closure_minimal ?_ isClosed_closure h1` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `rhoK_mem D lam a`.
-/
theorem fst_mem_closure_natCast :
    ∀ (D : D7) (lam : Qbar →+* ℂ_[2]), ∀ α ∈ GL3Theta.OKp D lam,
      α.1 ∈ closure (Set.range (Nat.cast : ℕ → ℂ_[2])) := by
  intro D lam α hα
  have h1 : α.1 ∈ (intClosure (rhoK D lam) : Set ℂ_[2]) := by
    rw [← fst_image_OKp]
    exact ⟨α, hα, rfl⟩
  rw [coe_intClosure] at h1
  refine closure_minimal ?_ isClosed_closure h1
  rintro _ ⟨a, rfl⟩
  exact rhoK_mem D lam a

end GlobalTheory.TwoAdicFirst
