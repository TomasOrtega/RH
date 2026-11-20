import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDim
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalization
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePoint
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DegreeLatticePrimeScalingStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

namespace GlobalTheory.CompanionTheory.Ar.Num

/- English proof (translation)
Set `B` to `Algebra.adjoin ℤ (Set.range fun j => x j / x c)`. Set `I : Ideal B` to `{ carrier := {r | (r : Ω) * τ ∈ B} add_mem' := by`. Introduce `a b ha hb`. Establish `ha' : (a : Ω) * τ ∈ B` using `ha`. Establish `hb' : (b : Ω) * τ ∈ B` using `hb`.

Establish `h` using `add_mem ha' hb'`. Rewrite `h` using `[← add_mul]`. Conclude with `h`. Use the proof step `zero_mem' := by show ((0 : B) : Ω) * τ ∈ B`. Simplify using the standard rewrite rules.

Use the proof step `smul_mem' := by`. Introduce `r a ha`. Establish `ha' : (a : Ω) * τ ∈ B` using `ha`. Establish `h` using `mul_mem r.2 ha'`. Rewrite `h` using `[← _root_.mul_assoc]`.

Conclude with `h }`. Establish `hmem : (m : B) ∈ I.radical`. Rewrite using `[Ideal.radical_eq_sInf, Ideal.mem_sInf]`. Introduce and unpack `Q ⟨hIQ, hQ⟩`. Assume the negation of the conclusion as `hmQ`.

Take `⟨q, ⟨hqc, hq⟩, -⟩` from `chart_point_of_prime X Ω ξ ℤ κ x T c hc Q hQ`. Establish `hu : unitAt ξ q (((m : B) : B) : Ω)` using `(hq (m : B)).1 hmQ`. Establish `hu' : unitAt ξ q (m : Ω)` using `by simpa using hu`. Take `⟨s, hsB, hsu, hsτ⟩` from `(regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x T c q hqc τ).1 (hτ q hqc hu')`. Establish `hsQ : (⟨s, hsB⟩ : B) ∈ Q` using `hIQ hsτ`.

Conclude with `(hq ⟨s, hsB⟩).2 hsu hsQ`. Take `⟨n, hn⟩` from `hmem`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `h : (((m : B) ^ n : B) : Ω) * τ ∈ B` using `hn`. Simplify using `using h`.
-/
theorem exists_pow_mul_mem_chart {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {κ : Type} {x : κ → Ω} (T : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) (m : ℕ) (τ : Ω)
    (hτ : ∀ q : Cpt ξ, InChart ξ x c q → unitAt ξ q (m : Ω) → τ ∈ regAt ξ q) :
    ∃ n : ℕ, (m : Ω) ^ n * τ ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
  let B := Algebra.adjoin ℤ (Set.range fun j => x j / x c)
  let I : Ideal B :=
    { carrier := {r | (r : Ω) * τ ∈ B}
      add_mem' := by
        intro a b ha hb
        have ha' : (a : Ω) * τ ∈ B := ha
        have hb' : (b : Ω) * τ ∈ B := hb
        have h := add_mem ha' hb'
        rw [← add_mul] at h
        exact h
      zero_mem' := by
        show ((0 : B) : Ω) * τ ∈ B
        simp
      smul_mem' := by
        intro r a ha
        have ha' : (a : Ω) * τ ∈ B := ha
        have h := mul_mem r.2 ha'
        rw [← _root_.mul_assoc] at h
        exact h }
  have hmem : (m : B) ∈ I.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro Q ⟨hIQ, hQ⟩
    by_contra hmQ
    obtain ⟨q, ⟨hqc, hq⟩, -⟩ := chart_point_of_prime X Ω ξ ℤ κ x T c hc Q hQ
    have hu : unitAt ξ q (((m : B) : B) : Ω) := (hq (m : B)).1 hmQ
    have hu' : unitAt ξ q (m : Ω) := by simpa using hu
    obtain ⟨s, hsB, hsu, hsτ⟩ :=
      (regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x T c q hqc τ).1 (hτ q hqc hu')
    have hsQ : (⟨s, hsB⟩ : B) ∈ Q := hIQ hsτ
    exact (hq ⟨s, hsB⟩).2 hsu hsQ
  obtain ⟨n, hn⟩ := hmem
  refine ⟨n, ?_⟩
  have h : (((m : B) ^ n : B) : Ω) * τ ∈ B := hn
  simpa using h

/- English proof (translation)
Take `⟨w, rfl⟩` from `hd`. Take `⟨h0, -, hinv⟩` from `hm`. Establish `hc : (((p * w : ℕ) : Ω)) = (p : Ω) * (w : Ω)` using `by push_cast; ring`. Rewrite `h0`, `hinv` using `[hc]`. Establish `hp : (p : Ω) ≠ 0` using `left_ne_zero_of_mul h0`.

Establish `hw : (w : Ω) ≠ 0` using `right_ne_zero_of_mul h0`. Use `⟨hp, natCast_mem _ p, ?_⟩` and prove the remaining obligations. Establish `he : (p : Ω)⁻¹ = (w : Ω) * ((p : Ω) * (w : Ω))⁻¹` using `by field_simp`. Rewrite using `[he]`. Conclude with `mul_mem (natCast_mem _ w) hinv`.
-/
theorem unitAt_natCast_of_dvd {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (q : Cpt ξ) {p m : ℕ} (hd : p ∣ m) (hm : unitAt ξ q (m : Ω)) : unitAt ξ q (p : Ω) := by
  obtain ⟨w, rfl⟩ := hd
  obtain ⟨h0, -, hinv⟩ := hm
  have hc : (((p * w : ℕ) : Ω)) = (p : Ω) * (w : Ω) := by push_cast; ring
  rw [hc] at h0 hinv
  have hp : (p : Ω) ≠ 0 := left_ne_zero_of_mul h0
  have hw : (w : Ω) ≠ 0 := right_ne_zero_of_mul h0
  refine ⟨hp, natCast_mem _ p, ?_⟩
  have he : (p : Ω)⁻¹ = (w : Ω) * ((p : Ω) * (w : Ω))⁻¹ := by field_simp
  rw [he]
  exact mul_mem (natCast_mem _ w) hinv

variable {Ω' : Type} [Field Ω'] in

/- English proof (translation)
Take `⟨r, hr⟩` from `Submodule.mem_span_singleton.1 h`. Establish `hr' : (r : Ω') * w = v` using `hr`. Rewrite using `[← hr', mul_div_cancel_right₀ _ hw]`. Conclude with `r.2`.
-/
theorem div_mem_of_mem_span {R : Subring Ω'} {v w : Ω'} (hw : w ≠ 0) (h : v ∈ Submodule.span R {w}) :
    v / w ∈ R := by
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 h
  have hr' : (r : Ω') * w = v := hr
  rw [← hr', mul_div_cancel_right₀ _ hw]
  exact r.2

/- English proof (translation)
Establish `key : ∀ q : Cpt ξ, InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c q → unitAt ξ q ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) → Submodule.span (regAt ξ q) {(∏ k, y ⟨k, c k⟩ ^ a k) * e} = Submodule.span (regAt ξ q) {(∏ k, y ⟨k, c k⟩ ^ a' k) * e'}`. Introduce `q hq hm`. Establish `h1` using `hL.2 q (Set.mem_univ q) c hq`. Establish `h2` using `hL'.2 q (Set.mem_univ q) c hq`. Rewrite `h1`, `h2` using `[smul_eq_mul]`.

Rewrite using `[← h1, ← h2]`. Use `hS q fun p hp hf => hf ?_` and prove the remaining obligations. Conclude with `unitAt_natCast_of_dvd q (Finset.dvd_prod_of_mem (fun p : Nat.Primes => (p : ℕ)) hp) hm`. Establish `hy : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)`. Establish `hu : (∏ k, y ⟨k, c k⟩ ^ a k) * e ≠ 0` using `mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) hL.1`.

Establish `hu' : (∏ k, y ⟨k, c k⟩ ^ a' k) * e' ≠ 0` using `mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) hL'.1`. Prove the components needed by the constructor for the conclusion. Use `exists_pow_mul_mem_chart T hc _ _ fun q hq hm => div_mem_of_mem_span hu ?_` and prove the remaining obligations. Rewrite using `[key q hq hm]`. Conclude with `Submodule.mem_span_singleton_self _`.

Use `exists_pow_mul_mem_chart T hc _ _ fun q hq hm => div_mem_of_mem_span hu' ?_` and prove the remaining obligations. Rewrite using `[← key q hq hm]`. Conclude with `Submodule.mem_span_singleton_self _`.
-/
theorem exists_pow_chart_quotients {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}
    (T : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    {L L' : Lat ξ Ω} {a a' : K → ℤ} {e e' : Ω} (hL : L.IsDegOn Set.univ y a e)
    (hL' : L'.IsDegOn Set.univ y a' e') (S : Finset Nat.Primes)
    (hS : ∀ q : Cpt ξ, (∀ p ∈ S, ¬ InFibre ξ p q) → L q = L' q)
    (c : (k : K) → J k) (hc : ∏ k, y ⟨k, c k⟩ ≠ 0) :
    (∃ n : ℕ, ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) ^ n *
        (((∏ k, y ⟨k, c k⟩ ^ a' k) * e') / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) ∈
        Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)) ∧
      ∃ n : ℕ, ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) ^ n *
        (((∏ k, y ⟨k, c k⟩ ^ a k) * e) / ((∏ k, y ⟨k, c k⟩ ^ a' k) * e')) ∈
        Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) := by
  have key : ∀ q : Cpt ξ, InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c q →
      unitAt ξ q ((∏ p ∈ S, (p : ℕ) : ℕ) : Ω) →
      Submodule.span (regAt ξ q) {(∏ k, y ⟨k, c k⟩ ^ a k) * e} =
        Submodule.span (regAt ξ q) {(∏ k, y ⟨k, c k⟩ ^ a' k) * e'} := by
    intro q hq hm
    have h1 := hL.2 q (Set.mem_univ q) c hq
    have h2 := hL'.2 q (Set.mem_univ q) c hq
    rw [smul_eq_mul] at h1 h2
    rw [← h1, ← h2]
    refine hS q fun p hp hf => hf ?_
    exact unitAt_natCast_of_dvd q (Finset.dvd_prod_of_mem (fun p : Nat.Primes => (p : ℕ)) hp) hm
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)
  have hu : (∏ k, y ⟨k, c k⟩ ^ a k) * e ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) hL.1
  have hu' : (∏ k, y ⟨k, c k⟩ ^ a' k) * e' ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) hL'.1
  constructor
  · refine exists_pow_mul_mem_chart T hc _ _ fun q hq hm => div_mem_of_mem_span hu ?_
    rw [key q hq hm]
    exact Submodule.mem_span_singleton_self _
  · refine exists_pow_mul_mem_chart T hc _ _ fun q hq hm => div_mem_of_mem_span hu' ?_
    rw [← key q hq hm]
    exact Submodule.mem_span_singleton_self _

/- English proof (translation)
Introduce `X Ω _ ξ K _ _ J _ y T d hA L L' a a' e e' hL hL' S hS`. Establish `hrel : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0`. Introduce `k`. Take `⟨i, hi⟩` from `hA.2.1.2.2 k`. Use `⟨i, fun h0 => hi ?_⟩` and prove the remaining obligations.

Rewrite using `[mCoordIdeal, RingHom.mem_ker]`. Simplify using `[mConeMap, h0]`. Establish `hproj : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiProjPrime (pointIdeal ℤ y)` using `GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDim.isMultiProjPrime_pointIdeal y hrel`. Establish `he : e ≠ 0` using `hL.1`. Establish `he' : e' ≠ 0` using `hL'.1`.

Use `GlobalTheory.T.degree_lattice_prime_scaling K J Ω y hproj S a a' (e' / e) (div_ne_zero he' he) ?_ hA.2.2.1` and prove the remaining obligations. Introduce `c hc`. Establish `hc' : ∏ k, y ⟨k, c k⟩ ≠ 0` using `hc`. Take `⟨⟨n, hn⟩, ⟨n', hn'⟩⟩` from `exists_pow_chart_quotients T hL hL' S hS c hc'`. Establish `hy : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => Finset.prod_ne_zero_iff.1 hc' k (Finset.mem_univ k)`.

Establish `hY : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)`. Establish `hY' : (∏ k, y ⟨k, c k⟩ ^ a' k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `t ⟨A, hAm, rfl⟩`. Establish `hAm' : A ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)` using `hAm`.

Use `⟨n', _, ⟨_, mul_mem hn' hAm', rfl⟩, ?_⟩` and prove the remaining obligations. Generalize the expression as in `(∏ k, y ⟨k, c k⟩ ^ a k) = Y at hY`. Generalize the expression as in `(∏ k, y ⟨k, c k⟩ ^ a' k) = Y' at hY'`. Clear the denominators using the available nonvanishing facts. Introduce and unpack `t ⟨A, hAm, rfl⟩`.

Establish `hAm' : A ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)` using `hAm`. Use `⟨n, _, ⟨_, mul_mem hn hAm', rfl⟩, ?_⟩` and prove the remaining obligations. Generalize the expression as in `(∏ k, y ⟨k, c k⟩ ^ a k) = Y at hY`. Generalize the expression as in `(∏ k, y ⟨k, c k⟩ ^ a' k) = Y' at hY'`. Clear the denominators using the available nonvanishing facts.
-/
theorem lat_vertOff : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ d : ℕ, IsArithVar (mCoordIdeal y) (d + 1) → ∀ (L L' : Lat ξ Ω) (a a' : K → ℤ) (e e' : Ω), L.IsDegOn Set.univ y a e → L'.IsDegOn Set.univ y a' e' → ∀ S : Finset Nat.Primes, (∀ q : Cpt ξ, (∀ p ∈ S, ¬ InFibre ξ p q) → L q = L' q) → ∃ f g : MvPolynomial (Σ k, J k) ℤ, (⟨fun _ => a, fun _ => a', fun _ => f, fun _ => g⟩ : LocPair J ℤ Unit).IsVertOff (mCoordIdeal y) S ∧ aeval y f = e' / e * aeval y g := by
  intro X Ω _ ξ K _ _ J _ y T d hA L L' a a' e e' hL hL' S hS
  have hrel : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hA.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker]
    simp [mConeMap, h0]
  have hproj : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiProjPrime (pointIdeal ℤ y) :=
    GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDim.isMultiProjPrime_pointIdeal y hrel
  have he : e ≠ 0 := hL.1
  have he' : e' ≠ 0 := hL'.1
  refine GlobalTheory.T.degree_lattice_prime_scaling K J Ω y hproj S a a' (e' / e) (div_ne_zero he' he) ?_ hA.2.2.1
  intro c hc
  have hc' : ∏ k, y ⟨k, c k⟩ ≠ 0 := hc
  obtain ⟨⟨n, hn⟩, ⟨n', hn'⟩⟩ := exists_pow_chart_quotients T hL hL' S hS c hc'
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc' k (Finset.mem_univ k)
  have hY : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  have hY' : (∏ k, y ⟨k, c k⟩ ^ a' k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  constructor
  · rintro t ⟨A, hAm, rfl⟩
    have hAm' : A ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
        (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) := hAm
    refine ⟨n', _, ⟨_, mul_mem hn' hAm', rfl⟩, ?_⟩
    generalize (∏ k, y ⟨k, c k⟩ ^ a k) = Y at hY
    generalize (∏ k, y ⟨k, c k⟩ ^ a' k) = Y' at hY'
    field_simp
  · rintro t ⟨A, hAm, rfl⟩
    have hAm' : A ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
        (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) := hAm
    refine ⟨n, _, ⟨_, mul_mem hn hAm', rfl⟩, ?_⟩
    generalize (∏ k, y ⟨k, c k⟩ ^ a k) = Y at hY
    generalize (∏ k, y ⟨k, c k⟩ ^ a' k) = Y' at hY'
    field_simp

end GlobalTheory.CompanionTheory.Ar.Num
