import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CM4
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FormalExponentialAgree
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.CurveIdealPrimeReduction
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LatticeAreaPositivity.Bridge
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MkLeContinuumOfDenseRange

noncomputable section

namespace GlobalTheory.InertGenusOne

open Formalism.MainNotions.GL3Theta Formalism.L2.G.Pend PowerSeries Cardinal

section Transc

/- English proof (translation)
Establish `hA : #(algebraicClosure ℚ ℂ_[p]) ≤ ℵ₀`. Establish `: Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ_[p])` using `algebraicClosure.isAlgebraic ℚ ℂ_[p]`. Use `Algebra.IsAlgebraic.cardinalMk_le_max ℚ (algebraicClosure ℚ ℂ_[p])` as an intermediate fact. Rewrite `this` using `[Cardinal.mkRat, max_self]`. Then use the resulting hypothesis. Establish `htr : ∀ y : ℂ_[p], y ∉ algebraicClosure ℚ ℂ_[p] → Transcendental ℚ y` using `fun y hy h => hy (mem_algebraicClosure_iff.2 h)`.

Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x : ℂ_[p], x ∉ algebraicClosure ℚ ℂ_[p] := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `h1 : #ℂ_[p] ≤ #(algebraicClosure ℚ ℂ_[p])` using `Cardinal.mk_le_of_injective (f := fun y : ℂ_[p] => (⟨y, h y⟩ : algebraicClosure ℚ ℂ_[p])) (fun a b hab => congrArg Subtype.val hab)`. Establish `h2` using `h1.trans hA`.

Rewrite `h2` using `[GlobalTheory.PadicComplexIso.mk_padicComplex p]`. Conclude with `absurd Cardinal.aleph0_lt_continuum (not_lt.2 h2)`. Distinguish the cases in `hx1 : 1 < ‖x‖`. Conclude with `⟨x, htr x hx, hx1⟩`. Use `push_neg at hx1`.

Establish `hp0 : (p : ℂ_[p]) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero`. Establish `hpn : ‖(p : ℂ_[p])‖ < 1` using `Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one p`. Establish `hpi : 1 < ‖(p : ℂ_[p])⁻¹‖`. Rewrite using `[norm_inv]`. Conclude with `one_lt_inv₀ (norm_pos_iff.2 hp0) |>.2 hpn`.

Use `⟨x + (p : ℂ_[p])⁻¹, htr _ ?_, ?_⟩` and prove the remaining obligations. Introduce `hm`. Apply `hx` to reduce the goal to its premises. Establish `: x = (x + (p : ℂ_[p])⁻¹) - (p : ℂ_[p])⁻¹` using `by ring`. Rewrite using `[this]`.

Conclude with `sub_mem hm (inv_mem (natCast_mem _ p))`. Assume the negation of the conclusion as `hle push_neg at hle`. Establish `e : (p : ℂ_[p])⁻¹ = (x + (p : ℂ_[p])⁻¹) + -x` using `by ring`. Use `IsUltrametricDist.norm_add_le_max (x + (p : ℂ_[p])⁻¹) (-x)` as an intermediate fact. Rewrite `this` using `[← e, norm_neg]`.

Establish `: ‖(p : ℂ_[p])⁻¹‖ ≤ 1` using `this.trans (max_le hle hx1)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_transcendental_norm_gt (p : ℕ) [Fact p.Prime] :
    ∃ t : ℂ_[p], Transcendental ℚ t ∧ 1 < ‖t‖ := by
  have hA : #(algebraicClosure ℚ ℂ_[p]) ≤ ℵ₀ := by
    have : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ_[p]) := algebraicClosure.isAlgebraic ℚ ℂ_[p]
    have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ (algebraicClosure ℚ ℂ_[p])
    rwa [Cardinal.mkRat, max_self] at this
  have htr : ∀ y : ℂ_[p], y ∉ algebraicClosure ℚ ℂ_[p] → Transcendental ℚ y :=
    fun y hy h => hy (mem_algebraicClosure_iff.2 h)
  obtain ⟨x, hx⟩ : ∃ x : ℂ_[p], x ∉ algebraicClosure ℚ ℂ_[p] := by
    by_contra h
    push_neg at h
    have h1 : #ℂ_[p] ≤ #(algebraicClosure ℚ ℂ_[p]) :=
      Cardinal.mk_le_of_injective (f := fun y : ℂ_[p] => (⟨y, h y⟩ : algebraicClosure ℚ ℂ_[p]))
        (fun a b hab => congrArg Subtype.val hab)
    have h2 := h1.trans hA
    rw [GlobalTheory.PadicComplexIso.mk_padicComplex p] at h2
    exact absurd Cardinal.aleph0_lt_continuum (not_lt.2 h2)
  by_cases hx1 : 1 < ‖x‖
  · exact ⟨x, htr x hx, hx1⟩
  · push_neg at hx1
    have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
    have hpn : ‖(p : ℂ_[p])‖ < 1 := Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one p
    have hpi : 1 < ‖(p : ℂ_[p])⁻¹‖ := by
      rw [norm_inv]
      exact one_lt_inv₀ (norm_pos_iff.2 hp0) |>.2 hpn
    refine ⟨x + (p : ℂ_[p])⁻¹, htr _ ?_, ?_⟩
    · intro hm
      apply hx
      have : x = (x + (p : ℂ_[p])⁻¹) - (p : ℂ_[p])⁻¹ := by ring
      rw [this]
      exact sub_mem hm (inv_mem (natCast_mem _ p))
    · by_contra hle
      push_neg at hle
      have e : (p : ℂ_[p])⁻¹ = (x + (p : ℂ_[p])⁻¹) + -x := by ring
      have := IsUltrametricDist.norm_add_le_max (x + (p : ℂ_[p])⁻¹) (-x)
      rw [← e, norm_neg] at this
      have : ‖(p : ℂ_[p])⁻¹‖ ≤ 1 := this.trans (max_le hle hx1)
      linarith

/- English proof (translation)
Set `F` to `FractionRing (Polynomial ℚ)`. Establish `hzi : Function.Injective ((Polynomial.aeval z : Polynomial ℚ →ₐ[ℚ] ℂ).toRingHom)` using `transcendental_iff_injective.1 hz`. Establish `hti : Function.Injective ((Polynomial.aeval t : Polynomial ℚ →ₐ[ℚ] ℂ_[p]).toRingHom)` using `transcendental_iff_injective.1 ht`. Set `fz : F →+* ℂ` to `IsFractionRing.lift hzi`. Set `ft : F →+* ℂ_[p]` to `IsFractionRing.lift hti`.

Use `letI : Algebra F ℂ := fz.toAlgebra`. Use `letI : Algebra F ℂ_[p] := ft.toAlgebra`. Establish `hP : Countable (Polynomial ℚ)`. Use `Polynomial.cardinalMk_le_max (R := ℚ)` as an intermediate fact. Rewrite `this` using `[Cardinal.mkRat, max_self]`.

Conclude with `Cardinal.mk_le_aleph0_iff.1 this`. Establish `hF : Countable F`. Establish `hs : Function.Surjective (fun q : Polynomial ℚ × nonZeroDivisors (Polynomial ℚ) => IsLocalization.mk' F q.1 q.2)`. Introduce `w`. Take `⟨a, h⟩` from `IsLocalization.mk'_surjective (nonZeroDivisors (Polynomial ℚ)) w`.

Conclude with `⟨a, h⟩`. Conclude with `hs.countable`. Take `⟨e, he⟩` from `GlobalTheory.PadicComplexIso.exists_ringEquiv_over F ℂ ℂ_[p] Cardinal.mk_le_aleph0 (Cardinal.mk_complex ▸ Cardinal.aleph0_lt_continuum) (Cardinal.mk_complex.trans (GlobalTheory.PadicComplexIso.mk_padicComplex p).symm)`. Use `⟨e, ?_⟩` and prove the remaining obligations. Establish `h` using `he (algebraMap (Polynomial ℚ) F Polynomial.X)`.

Establish `h1 : algebraMap F ℂ (algebraMap (Polynomial ℚ) F Polynomial.X) = z`. Express the relevant statement in the definitionally equal form `fz _ = z`. Rewrite using `[IsFractionRing.lift_algebraMap]`. Simplify using the standard rewrite rules. Establish `h2 : algebraMap F ℂ_[p] (algebraMap (Polynomial ℚ) F Polynomial.X) = t`.

Express the relevant statement in the definitionally equal form `ft _ = t`. Rewrite using `[IsFractionRing.lift_algebraMap]`. Simplify using the standard rewrite rules. Rewrite `h` using `[h1, h2]`. Conclude with `h`.
-/
theorem exists_ringEquiv_transcendental (p : ℕ) [Fact p.Prime] {z : ℂ} (hz : Transcendental ℚ z) {t : ℂ_[p]}
    (ht : Transcendental ℚ t) : ∃ ι : ℂ ≃+* ℂ_[p], ι z = t := by
  let F := FractionRing (Polynomial ℚ)
  have hzi : Function.Injective ((Polynomial.aeval z : Polynomial ℚ →ₐ[ℚ] ℂ).toRingHom) :=
    transcendental_iff_injective.1 hz
  have hti : Function.Injective ((Polynomial.aeval t : Polynomial ℚ →ₐ[ℚ] ℂ_[p]).toRingHom) :=
    transcendental_iff_injective.1 ht
  let fz : F →+* ℂ := IsFractionRing.lift hzi
  let ft : F →+* ℂ_[p] := IsFractionRing.lift hti
  letI : Algebra F ℂ := fz.toAlgebra
  letI : Algebra F ℂ_[p] := ft.toAlgebra
  have hP : Countable (Polynomial ℚ) := by
    have := Polynomial.cardinalMk_le_max (R := ℚ)
    rw [Cardinal.mkRat, max_self] at this
    exact Cardinal.mk_le_aleph0_iff.1 this
  have hF : Countable F := by
    have hs : Function.Surjective
        (fun q : Polynomial ℚ × nonZeroDivisors (Polynomial ℚ) => IsLocalization.mk' F q.1 q.2) := by
      intro w
      obtain ⟨a, h⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (Polynomial ℚ)) w
      exact ⟨a, h⟩
    exact hs.countable
  obtain ⟨e, he⟩ := GlobalTheory.PadicComplexIso.exists_ringEquiv_over F ℂ ℂ_[p] Cardinal.mk_le_aleph0
    (Cardinal.mk_complex ▸ Cardinal.aleph0_lt_continuum)
    (Cardinal.mk_complex.trans (GlobalTheory.PadicComplexIso.mk_padicComplex p).symm)
  refine ⟨e, ?_⟩
  have h := he (algebraMap (Polynomial ℚ) F Polynomial.X)
  have h1 : algebraMap F ℂ (algebraMap (Polynomial ℚ) F Polynomial.X) = z := by
    change fz _ = z
    rw [IsFractionRing.lift_algebraMap]
    simp
  have h2 : algebraMap F ℂ_[p] (algebraMap (Polynomial ℚ) F Polynomial.X) = t := by
    change ft _ = t
    rw [IsFractionRing.lift_algebraMap]
    simp
  rw [h1, h2] at h
  exact h

end Transc

open Formalism.L2.Th1.CM in

/- English proof (translation)
Assume the negation of the conclusion as `hz`. Take `⟨t, ht, ht1⟩` from `exists_transcendental_norm_gt p`. Take `⟨ι, hι⟩` from `exists_ringEquiv_transcendental p hz ht`. Take `⟨g2, g3, -, -, n2, -, nd, μ, hμ, e2, e3⟩` from `hGood d L hsq hd4 hcm p h5 hpd ι`. Establish `hdμ : g2 ^ 3 - 27 * g3 ^ 2 = μ ^ 12`.

Establish `h1 : ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = 1` using `by rw [hdisc, map_one]`. Rewrite `h1` using `[map_sub, map_mul, map_pow, map_pow, map_ofNat]`. Rewrite using `[e2, e3]`. Take the linear combination `μ ^ 12 * h1`. Rewrite `nd` using `[hdμ, norm_pow]`.

Establish `hμ1 : ‖μ‖ = 1` using `(pow_eq_one_iff_of_nonneg (norm_nonneg μ) (by norm_num)).1 nd`. Rewrite `n2` using `[e2, norm_mul, norm_pow, hμ1, one_pow, one_mul, hι]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem isAlgebraic_g2_of_hasCMBy_of_disc_eq_one (hGood : CM2) (d : ℕ) (L : PeriodPair) (hsq : Squarefree d) (hd4 : d % 4 = 3)
    (hcm : HasCMBy d L) (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) (hpd : ¬ p ∣ d)
    (hdisc : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1) : IsAlgebraic ℚ L.g₂ := by
  by_contra hz
  obtain ⟨t, ht, ht1⟩ := exists_transcendental_norm_gt p
  obtain ⟨ι, hι⟩ := exists_ringEquiv_transcendental p hz ht
  obtain ⟨g2, g3, -, -, n2, -, nd, μ, hμ, e2, e3⟩ := hGood d L hsq hd4 hcm p h5 hpd ι
  have hdμ : g2 ^ 3 - 27 * g3 ^ 2 = μ ^ 12 := by
    have h1 : ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = 1 := by rw [hdisc, map_one]
    rw [map_sub, map_mul, map_pow, map_pow, map_ofNat] at h1
    rw [e2, e3]
    linear_combination μ ^ 12 * h1
  rw [hdμ, norm_pow] at nd
  have hμ1 : ‖μ‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg μ) (by norm_num)).1 nd
  rw [e2, norm_mul, norm_pow, hμ1, one_pow, one_mul, hι] at n2
  linarith

end GlobalTheory.InertGenusOne

namespace GlobalTheory.InertGenusOne

open Formalism.MainNotions.GL3Theta Formalism.L2.G.Pend PowerSeries

section Gen

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `hB` using `((Formalism.L2.Th1.D.kurIntegers p).1 x).2 ⟨hx, h1⟩`. Establish `hS : Formalism.L2.Th1.D.muPrime p = {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1}`. Use extensionality with `ζ`. Simplify using `only [Formalism.L2.Th1.D.muPrime, Set.mem_ofPred_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, h0, hn, h⟩`. Conclude with `⟨n, h0, Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn), h⟩`. Introduce and unpack `⟨n, h0, hn, h⟩`. Conclude with `⟨n, h0, (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.coprime_comm.mp hn), h⟩`.

Unfold `Formalism.L2.Th1.D.ringB Formalism.L2.Th1.D.ringA at hB`. Rewrite `hB` using `[hS]`. Conclude with `hB`.
-/
theorem mem_Wp_of_kur {x : ℂ_[p]} (hx : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) (h1 : ‖x‖ ≤ 1) : x ∈ Wp p := by
  have hp : p.Prime := Fact.out
  have hB := ((Formalism.L2.Th1.D.kurIntegers p).1 x).2 ⟨hx, h1⟩
  have hS : Formalism.L2.Th1.D.muPrime p = {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1} := by
    ext ζ
    simp only [Formalism.L2.Th1.D.muPrime, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, h0, hn, h⟩
      exact ⟨n, h0, Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn), h⟩
    · rintro ⟨n, h0, hn, h⟩
      exact ⟨n, h0, (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.coprime_comm.mp hn), h⟩
  unfold Formalism.L2.Th1.D.ringB Formalism.L2.Th1.D.ringA at hB
  rw [hS] at hB
  exact hB

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `hinj : Function.Injective (fun j : ℕ => p ^ (2 * j))`. Introduce `a b h`. Use `Nat.pow_right_injective hp.two_le h` as an intermediate fact. Simplify using `using this`.

Use extensionality with `n`. Simplify using `only [logF, Formalism.L2.Th1.CM.ltLog, coeff_mk]`. Use `split_ifs with h`. Establish `hj` using `Nat.find_spec h set j0 := Nat.find h`. Establish `hn : n = p ^ (2 * j0)` using `by rw [hj, ← pow_mul]`.

Rewrite using `[Finset.sum_eq_single j0]`. Rewrite using `[if_pos hn]`. Introduce `j _ hne`. Rewrite using `[if_neg]`. Introduce `h'`.

Conclude with `hne (hinj (h'.symm.trans hn))`. Introduce `hj0`. It suffices to derive a contradiction. Apply `hj0` to reduce the goal to its premises. Rewrite using `[Finset.mem_range, hn]`.

Establish `: j0 < p ^ j0` using `Nat.lt_pow_self hp.one_lt`. Establish `h2 : p ^ j0 ≤ p ^ (2 * j0)` using `Nat.pow_le_pow_right hp.pos (by omega)`. Use linear arithmetic over natural numbers and integers. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`.

Rewrite using `[if_neg]`. Introduce `h'`. Conclude with `h ⟨j, by rw [h', pow_mul]⟩`.
-/
theorem logF_eq : logF p = Formalism.L2.Th1.CM.ltLog ℂ_[p] p := by
  have hp : p.Prime := Fact.out
  have hinj : Function.Injective (fun j : ℕ => p ^ (2 * j)) := by
    intro a b h
    have := Nat.pow_right_injective hp.two_le h
    simpa using this
  ext n
  simp only [logF, Formalism.L2.Th1.CM.ltLog, coeff_mk]
  split_ifs with h
  · have hj := Nat.find_spec h
    set j0 := Nat.find h
    have hn : n = p ^ (2 * j0) := by rw [hj, ← pow_mul]
    rw [Finset.sum_eq_single j0]
    · rw [if_pos hn]
    · intro j _ hne
      rw [if_neg]
      intro h'
      exact hne (hinj (h'.symm.trans hn))
    · intro hj0
      exfalso
      apply hj0
      rw [Finset.mem_range, hn]
      have : j0 < p ^ j0 := Nat.lt_pow_self hp.one_lt
      have h2 : p ^ j0 ≤ p ^ (2 * j0) := Nat.pow_le_pow_right hp.pos (by omega)
      omega
  · apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    intro h'
    exact h ⟨j, by rw [h', pow_mul]⟩

/- English proof (translation)
Establish `hF` using `(Formalism.L2.Th1.A.CurveSer.wSer_fixed W).2`. Rewrite `hF` using `[Formalism.L2.Th1.A.CurveSer.wSer_eq]`. Unfold `Formalism.MainNotions.TaylorLogMetric.IsWq`. Simplify using `only [PowerSeries.algebraMap_eq]`. Apply `mul_left_cancel₀ (pow_ne_zero 3 (X_ne_zero (R := ℂ_[p])))` to reduce the goal to its premises.

Take the linear combination `hF`.
-/
theorem isWq_wU (W : WeierstrassCurve ℂ_[p]) : Formalism.MainNotions.TaylorLogMetric.IsWq W (Formalism.L2.Th1.A.wU W) := by
  have hF := (Formalism.L2.Th1.A.CurveSer.wSer_fixed W).2
  rw [Formalism.L2.Th1.A.CurveSer.wSer_eq] at hF
  unfold Formalism.MainNotions.TaylorLogMetric.IsWq
  simp only [PowerSeries.algebraMap_eq]
  apply mul_left_cancel₀ (pow_ne_zero 3 (X_ne_zero (R := ℂ_[p])))
  linear_combination hF

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `h` using `Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd (K := ℂ_[p]) (m := 4) hp (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one p) (by`. Introduce `hd`. Use `Nat.le_of_dvd (by norm_num) hd` as an intermediate fact. Use the proof step `omega)`.

Conclude with `h` after adjusting the coercions.
-/
theorem norm_four (h5 : 5 ≤ p) : ‖(4 : ℂ_[p])‖ = 1 := by
  have hp : p.Prime := Fact.out
  have h := Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd (K := ℂ_[p]) (m := 4) hp
    (Formalism.L2.Th1.D.UnramifiedCompletion.normL_lt_one p) (by
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega)
  exact_mod_cast h

/- English proof (translation)
Use `set S := Formalism.L2.Th1.A.shortW g2 g3 with hS`. Set `g : G1 p` to `⟨lam, Λ, C, Formalism.L2.Th1.A.wU S, Formalism.L2.Th1.A.expSer S⟩`. Establish `hgW : g.W = S` using `hW`. Establish `h4` using `norm_four (p := p) h5`. Establish `hWq : Formalism.MainNotions.TaylorLogMetric.IsWq g.W g.wq`.

Rewrite using `[hgW]`. Conclude with `isWq_wU S`. Take `⟨hx0, -, hLE, hEL, -⟩` from `Formalism.L2.Th1.A.expSpec ℂ_[p] S`. Establish `hfl : Formalism.MainNotions.TaylorLogMetric.flog S (Formalism.L2.Th1.A.wU S) = Formalism.L2.Th1.A.logSer S` using `Formalism.L2.KerInert.Dict.formal_logarithm_agree p S _ (isWq_wU S)`. Establish `hΔ : S.Δ = g2 ^ 3 - 27 * g3 ^ 2` using `(Formalism.L2.Th1.A.shortInv ℂ_[p] g2 g3).2.2.2`.

Establish `na4 : ‖S.a₄‖ ≤ 1`. Simplify using `only [hS, Formalism.L2.Th1.A.shortW, norm_div, norm_neg, h4, div_one]`. Conclude with `n2`. Establish `na6 : ‖S.a₆‖ ≤ 1`. Simplify using `only [hS, Formalism.L2.Th1.A.shortW, norm_div, norm_neg, h4, div_one]`.

Conclude with `n3`. Establish `hU : IsModelU lam Λ C` using `by show Formalism.MainNotions.TaylorLogMetric.IsIntP (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₁ ∧ Formalism.MainNotions.TaylorLogMetric.IsIntP (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₂ ∧ Formalism.MainNotions.TaylorLogMetric.IsIntP (C • Formalis …`. Rewrite using `[hW]`. Apply the tactic sequence `refine ⟨?_, ?_, ?_, na4, na6, by rw [hΔ]; exact nd⟩ <;> simp [Formalism.MainNotions.TaylorLogMetric.IsIntP, hS, Formalism.L2.Th1.A.shortW]`. Establish `hOk : g.Ok`.

Use `⟨hU, hWq, hx0, ?_⟩` and prove the remaining obligations. Use `show PowerSeries.subst (Formalism.L2.Th1.A.expSer S) (Formalism.MainNotions.TaylorLogMetric.flog g.W (Formalism.L2.Th1.A.wU S)) = PowerSeries.X`. Rewrite using `[hgW, hfl]`. Conclude with `hLE`. Establish `hM : ModelOverW lam Λ C` using `by show (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₁ ∈ Wp p ∧ (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₂ ∈ Wp p ∧ (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₃ ∈ Wp p ∧ (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₄ ∈ Wp …`.

Rewrite using `[hW]`. Use `⟨by simp [hS, Formalism.L2.Th1.A.shortW], by simp [hS, Formalism.L2.Th1.A.shortW], by simp [hS, Formalism.L2.Th1.A.shortW], mem_Wp_of_kur ?_ na4, mem_Wp_of_kur ?_ na6⟩` and prove the remaining obligations. Simplify using `only [hS, Formalism.L2.Th1.A.shortW]`. Conclude with `div_mem (neg_mem k2) (ofNat_mem _ 4)`. Simplify using `only [hS, Formalism.L2.Th1.A.shortW]`.

Conclude with `div_mem (neg_mem k3) (ofNat_mem _ 4)`. Establish `hpt : (g.pt (MvPowerSeries.C ε * logF p) : MvPowerSeries Unit ℂ_[p]) = (Formalism.L2.Th1.CM.uSer g2 g3).subst (PowerSeries.C ε * Formalism.L2.Th1.CM.ltLog ℂ_[p] p)` using `by show PowerSeries.subst (MvPowerSeries.C ε * logF p) (Formalism.L2.Th1.A.expSer S) = _`. Rewrite using `[hS, ← Formalism.L2.Th1.A.uSerEq, logF_eq]`. Both sides reduce to the same expression. Establish `hΘ : IntegralW (g.pt (MvPowerSeries.C ε * logF p) : MvPowerSeries Unit ℂ_[p])`.

Introduce `n`. Rewrite using `[hpt, Finsupp.unique_single n]`. Conclude with `mem_Wp_of_kur (hint (n ())).1 (hint (n ())).2`. Conclude with `⟨g, rfl, rfl, rfl, hOk, hM, ltIso_of' g hOk hε1 hΘ⟩`.
-/
theorem datum_of_short (h5 : 5 ≤ p) (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) (g2 g3 : ℂ_[p])
    (hW : C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ = Formalism.L2.Th1.A.shortW g2 g3)
    (k2 : g2 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) (k3 : g3 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) (n2 : ‖g2‖ ≤ 1) (n3 : ‖g3‖ ≤ 1)
    (nd : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1) (ε : ℂ_[p]) (hε1 : ‖ε‖ = 1)
    (hint : ∀ n : ℕ,
      PowerSeries.coeff n ((Formalism.L2.Th1.CM.uSer g2 g3).subst (PowerSeries.C ε * Formalism.L2.Th1.CM.ltLog ℂ_[p] p)) ∈
          Formalism.L2.Th1.CM.MaximalUnramifiedExtension p ∧
        ‖PowerSeries.coeff n ((Formalism.L2.Th1.CM.uSer g2 g3).subst
          (PowerSeries.C ε * Formalism.L2.Th1.CM.ltLog ℂ_[p] p))‖ ≤ 1) :
    ∃ g : G1 p, g.lam = lam ∧ g.abelian₂ = Λ ∧ g.C = C ∧ g.Ok ∧ ModelOverW g.lam g.abelian₂ g.C ∧ LTIso g := by
  set S := Formalism.L2.Th1.A.shortW g2 g3 with hS
  let g : G1 p := ⟨lam, Λ, C, Formalism.L2.Th1.A.wU S, Formalism.L2.Th1.A.expSer S⟩
  have hgW : g.W = S := hW
  have h4 := norm_four (p := p) h5
  have hWq : Formalism.MainNotions.TaylorLogMetric.IsWq g.W g.wq := by
    rw [hgW]; exact isWq_wU S
  obtain ⟨hx0, -, hLE, hEL, -⟩ := Formalism.L2.Th1.A.expSpec ℂ_[p] S
  have hfl : Formalism.MainNotions.TaylorLogMetric.flog S (Formalism.L2.Th1.A.wU S) = Formalism.L2.Th1.A.logSer S :=
    Formalism.L2.KerInert.Dict.formal_logarithm_agree p S _ (isWq_wU S)
  have hΔ : S.Δ = g2 ^ 3 - 27 * g3 ^ 2 := (Formalism.L2.Th1.A.shortInv ℂ_[p] g2 g3).2.2.2
  have na4 : ‖S.a₄‖ ≤ 1 := by
    simp only [hS, Formalism.L2.Th1.A.shortW, norm_div, norm_neg, h4, div_one]; exact n2
  have na6 : ‖S.a₆‖ ≤ 1 := by
    simp only [hS, Formalism.L2.Th1.A.shortW, norm_div, norm_neg, h4, div_one]; exact n3
  have hU : IsModelU lam Λ C := by
    show Formalism.MainNotions.TaylorLogMetric.IsIntP (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₁ ∧ Formalism.MainNotions.TaylorLogMetric.IsIntP (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₂ ∧
      Formalism.MainNotions.TaylorLogMetric.IsIntP (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₃ ∧ Formalism.MainNotions.TaylorLogMetric.IsIntP (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₄ ∧
      Formalism.MainNotions.TaylorLogMetric.IsIntP (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₆ ∧ ‖(C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).Δ‖ = 1
    rw [hW]
    refine ⟨?_, ?_, ?_, na4, na6, by rw [hΔ]; exact nd⟩ <;> simp [Formalism.MainNotions.TaylorLogMetric.IsIntP, hS, Formalism.L2.Th1.A.shortW]
  have hOk : g.Ok := by
    refine ⟨hU, hWq, hx0, ?_⟩
    show PowerSeries.subst (Formalism.L2.Th1.A.expSer S) (Formalism.MainNotions.TaylorLogMetric.flog g.W (Formalism.L2.Th1.A.wU S)) = PowerSeries.X
    rw [hgW, hfl]
    exact hLE
  have hM : ModelOverW lam Λ C := by
    show (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₁ ∈ Wp p ∧ (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₂ ∈ Wp p ∧
      (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₃ ∈ Wp p ∧ (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₄ ∈ Wp p ∧
      (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ).a₆ ∈ Wp p
    rw [hW]
    refine ⟨by simp [hS, Formalism.L2.Th1.A.shortW], by simp [hS, Formalism.L2.Th1.A.shortW],
      by simp [hS, Formalism.L2.Th1.A.shortW], mem_Wp_of_kur ?_ na4, mem_Wp_of_kur ?_ na6⟩
    · simp only [hS, Formalism.L2.Th1.A.shortW]
      exact div_mem (neg_mem k2) (ofNat_mem _ 4)
    · simp only [hS, Formalism.L2.Th1.A.shortW]
      exact div_mem (neg_mem k3) (ofNat_mem _ 4)
  have hpt : (g.pt (MvPowerSeries.C ε * logF p) : MvPowerSeries Unit ℂ_[p]) =
      (Formalism.L2.Th1.CM.uSer g2 g3).subst (PowerSeries.C ε * Formalism.L2.Th1.CM.ltLog ℂ_[p] p) := by
    show PowerSeries.subst (MvPowerSeries.C ε * logF p) (Formalism.L2.Th1.A.expSer S) = _
    rw [hS, ← Formalism.L2.Th1.A.uSerEq, logF_eq]
    rfl
  have hΘ : IntegralW (g.pt (MvPowerSeries.C ε * logF p) : MvPowerSeries Unit ℂ_[p]) := by
    intro n
    rw [hpt, Finsupp.unique_single n]
    exact mem_Wp_of_kur (hint (n ())).1 (hint (n ())).2
  exact ⟨g, rfl, rfl, rfl, hOk, hM, ltIso_of' g hOk hε1 hΘ⟩

end Gen

section Lattice

open NumberField Formalism.BasicNotions
open Formalism.L2.GlobalTheoryTheory Formalism.MainNotions Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

/- English proof (translation)
The claim follows from `Formalism.L2.Th1.F2.lattice_ideal_lattice_holds D.host.K D.host.d (discriminant_mod_four D) ⟨D.host.sqrtMinusD, br_sqrt_mem D⟩ (br_sqrt_sq D) (br_finrank_K D) (brPhi D) cc δ hcc hδ`.
-/
theorem lamOf_lat (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hcc : cc ≠ ⊥) (hδ : δ ≠ 0) :
    Formalism.L2.Th1.F2.IsLat (TaylorLogMetric.lamOf D cc δ) ∧ Formalism.L2.Th1.F2.HasCM D.host.d (TaylorLogMetric.lamOf D cc δ) :=
  Formalism.L2.Th1.F2.lattice_ideal_lattice_holds D.host.K D.host.d (discriminant_mod_four D) ⟨D.host.sqrtMinusD, br_sqrt_mem D⟩
    (br_sqrt_sq D) (br_finrank_K D) (brPhi D) cc δ hcc hδ

end Lattice

end GlobalTheory.InertGenusOne

namespace GlobalTheory.InertGenusOne

open Formalism.MainNotions.GL3Theta Formalism.L2.G.Pend NumberField Formalism.BasicNotions

/- English proof (translation)
The claim follows from `dif_pos a.2`.
-/
theorem lamC_coe {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (a : Formalism.MainNotions.TaylorLogMetric.Qbar) :
    Formalism.MainNotions.TaylorLogMetric.lamC lam (a : ℂ) = lam a := dif_pos a.2

/- English proof (translation)
Introduce `D cc δ hcurve hδ12 p _ hcop h5 hIn lam`. Establish `hp : p.Prime` using `Fact.out`. Establish `hcc : cc ≠ ⊥` using `hcurve.1`. Establish `hδ : δ ≠ 0` using `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcurve δ hδ12`. Take `⟨⟨L, hL⟩, hCM⟩` from `lamOf_lat D cc δ hcc hδ`.

Establish `hL' : (L.lattice : Set ℂ) = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ` using `by rw [← hL]; rfl`. Take `⟨e2, e3⟩` from `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L hL'`. Establish `hdisc : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1`. Establish `h` using `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcurve δ hδ12`. Rewrite using `[← e2, ← e3]`.

Conclude with `h`. Establish `hdp : D.host.d.Prime` using `D.host.hyp.2.1`. Establish `hd4 : D.host.d % 4 = 3` using `by have := D.host.hyp.2.2.2.1; omega`. Establish `hns : ¬ IsSquare ((-(D.host.d : ℤ) : ℤ) : ZMod p)` using `ZMod.nonsquare_of_jacobiSym_eq_neg_one hIn`. Establish `hsq' : ¬ ∃ a : ZMod p, a ^ 2 = -(D.host.d : ZMod p)`.

Introduce and unpack `⟨a, ha⟩; apply hns; exact ⟨a, by push_cast; rw [← ha]; ring⟩`. Establish `hpd : ¬ p ∣ D.host.d`. Introduce `h`. Apply `hsq'` to reduce the goal to its premises. Use `⟨0, ?_⟩` and prove the remaining obligations.

Rewrite using `[(ZMod.natCast_eq_zero_iff _ _).2 h]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcmby : Formalism.L2.Th1.CM.HasCMBy D.host.d L`. Introduce `ω hω`. Establish `h1` using `hCM ω (by rw [← hL]; exact hω)`.

Rewrite `h1` using `[← hL]`. Establish `e : Formalism.L2.Th1.CM.omegaK D.host.d = Formalism.L2.Th1.F.cmTheta 1 D.host.d`. Unfold `Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `h1`. Establish `hg2 : L.g₂ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar` using `mem_algebraicClosure_iff.2 (isAlgebraic_g2_of_hasCMBy_of_disc_eq_one hGood D.host.d L hdp.squarefree hd4 hcmby p h5 hpd hdisc)`. Establish `hg3 : L.g₃ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar`. Establish `h3sq : L.g₃ ^ 2 = (L.g₂ ^ 3 - 1) / 27` using `by rw [← hdisc]; ring`.

Establish `hm : L.g₃ ^ 2 ∈ Formalism.MainNotions.TaylorLogMetric.Qbar`. Rewrite using `[h3sq]`. Establish `h27 : (27 : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar`. Establish `h : ((27 : ℕ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar` using `natCast_mem _ 27`. Simplify using `using h`.

Conclude with `div_mem (sub_mem (pow_mem hg2 3) (one_mem _)) h27`. Conclude with `mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (by norm_num : 0 < 2) (mem_algebraicClosure_iff.1 hm))`. Use `set a2 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₂, hg2⟩ with ha2`. Use `set a3 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₃, hg3⟩ with ha3`. Take `⟨ι, hι⟩` from `GlobalTheory.PadicComplexIso.exists_ringEquiv_extending p lam`.

Take `⟨g2', g3', hG⟩` from `hGood D.host.d L hdp.squarefree hd4 hcmby p h5 hpd ι`. Take `⟨ε, -, hε1, hεint⟩` from `hHt D.host.d L hdp.squarefree hd4 hcmby p h5 hpd hsq' ι g2' g3' hG`. Take `⟨k2, k3, n2, n3, nd, μ, hμ, hg2', hg3'⟩` from `hG`. Set `C : WeierstrassCurve.VariableChange ℂ_[p]` to `⟨(Units.mk0 μ hμ)⁻¹, 0, 0, 0⟩`. Establish `ea4 : Formalism.MainNotions.TaylorLogMetric.lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g2 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / 4) = -(ι L.g₂) / 4`.

Establish `: -(Formalism.MainNotions.TaylorLogMetric.g2 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / 4 = ((-a2 / 4 : Formalism.MainNotions.TaylorLogMetric.Qbar) : ℂ)`. Rewrite using `[e2]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[this, lamC_coe, map_div₀, map_neg, map_ofNat, ← hι a2]`.

Establish `ea6 : Formalism.MainNotions.TaylorLogMetric.lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g3 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / 4) = -(ι L.g₃) / 4`. Establish `: -(Formalism.MainNotions.TaylorLogMetric.g3 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / 4 = ((-a3 / 4 : Formalism.MainNotions.TaylorLogMetric.Qbar) : ℂ)`. Rewrite using `[e3]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[this, lamC_coe, map_div₀, map_neg, map_ofNat, ← hι a3]`. Establish `hW : C • Formalism.MainNotions.TaylorLogMetric.wModel lam (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.A.shortW g2' g3'`. Establish `hw : Formalism.MainNotions.TaylorLogMetric.wModel lam (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) = ⟨0, 0, 0, -(ι L.g₂) / 4, -(ι L.g₃) / 4⟩`. Simplify using `only [Formalism.MainNotions.TaylorLogMetric.wModel, ea4, ea6]`. Rewrite using `[hw]`.

Apply the tactic sequence `ext <;> simp [C, Formalism.L2.Th1.A.shortW, hg2', hg3', WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄, WeierstrassCurve.variableChange_a₆] <;> ring`. Take `⟨g, hgl, hgL, -, hOk, hM, hLT⟩` from `datum_of_short h5 lam (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) C g2' g3' hW k2 k3 n2 n3 nd ε hε1 hεint`. Conclude with `⟨g, hgl, ⟨hcurve, hcop, hδ12, hgL, hOk⟩, hM, hLT⟩`.
-/
theorem datum_exists_coprime (hGood : Formalism.L2.Th1.CM.CM2) (hHt : Formalism.L2.Th1.CM.CM3) : Formalism.L2.KerInert.GenusOneModelExists := by
  intro D cc δ hcurve hδ12 p _ hcop h5 hIn lam
  have hp : p.Prime := Fact.out
  have hcc : cc ≠ ⊥ := hcurve.1
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcurve δ hδ12

  obtain ⟨⟨L, hL⟩, hCM⟩ := lamOf_lat D cc δ hcc hδ
  have hL' : (L.lattice : Set ℂ) = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ := by rw [← hL]; rfl
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L hL'
  have hdisc : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by
    have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcurve δ hδ12
    rw [← e2, ← e3]
    exact h

  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hd4 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
  have hns : ¬ IsSquare ((-(D.host.d : ℤ) : ℤ) : ZMod p) := ZMod.nonsquare_of_jacobiSym_eq_neg_one hIn
  have hsq' : ¬ ∃ a : ZMod p, a ^ 2 = -(D.host.d : ZMod p) := by
    rintro ⟨a, ha⟩; apply hns; exact ⟨a, by push_cast; rw [← ha]; ring⟩
  have hpd : ¬ p ∣ D.host.d := by
    intro h; apply hsq'; refine ⟨0, ?_⟩
    rw [(ZMod.natCast_eq_zero_iff _ _).2 h]; ring
  have hcmby : Formalism.L2.Th1.CM.HasCMBy D.host.d L := by
    intro ω hω
    have h1 := hCM ω (by rw [← hL]; exact hω)
    rw [← hL] at h1
    have e : Formalism.L2.Th1.CM.omegaK D.host.d = Formalism.L2.Th1.F.cmTheta 1 D.host.d := by
      unfold Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta; push_cast; ring
    rw [e]; exact h1

  have hg2 : L.g₂ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar :=
    mem_algebraicClosure_iff.2 (isAlgebraic_g2_of_hasCMBy_of_disc_eq_one hGood D.host.d L hdp.squarefree hd4 hcmby p h5 hpd hdisc)
  have hg3 : L.g₃ ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
    have h3sq : L.g₃ ^ 2 = (L.g₂ ^ 3 - 1) / 27 := by rw [← hdisc]; ring
    have hm : L.g₃ ^ 2 ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
      rw [h3sq]
      have h27 : (27 : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := by
        have h : ((27 : ℕ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := natCast_mem _ 27
        simpa using h
      exact div_mem (sub_mem (pow_mem hg2 3) (one_mem _)) h27
    exact mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (by norm_num : 0 < 2) (mem_algebraicClosure_iff.1 hm))
  set a2 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₂, hg2⟩ with ha2
  set a3 : Formalism.MainNotions.TaylorLogMetric.Qbar := ⟨L.g₃, hg3⟩ with ha3
  obtain ⟨ι, hι⟩ := GlobalTheory.PadicComplexIso.exists_ringEquiv_extending p lam

  obtain ⟨g2', g3', hG⟩ := hGood D.host.d L hdp.squarefree hd4 hcmby p h5 hpd ι
  obtain ⟨ε, -, hε1, hεint⟩ := hHt D.host.d L hdp.squarefree hd4 hcmby p h5 hpd hsq' ι g2' g3' hG
  obtain ⟨k2, k3, n2, n3, nd, μ, hμ, hg2', hg3'⟩ := hG

  let C : WeierstrassCurve.VariableChange ℂ_[p] := ⟨(Units.mk0 μ hμ)⁻¹, 0, 0, 0⟩
  have ea4 : Formalism.MainNotions.TaylorLogMetric.lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g2 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / 4) = -(ι L.g₂) / 4 := by
    have : -(Formalism.MainNotions.TaylorLogMetric.g2 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / 4 = ((-a2 / 4 : Formalism.MainNotions.TaylorLogMetric.Qbar) : ℂ) := by
      rw [e2]; push_cast; rfl
    rw [this, lamC_coe, map_div₀, map_neg, map_ofNat, ← hι a2]
  have ea6 : Formalism.MainNotions.TaylorLogMetric.lamC lam (-(Formalism.MainNotions.TaylorLogMetric.g3 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / 4) = -(ι L.g₃) / 4 := by
    have : -(Formalism.MainNotions.TaylorLogMetric.g3 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / 4 = ((-a3 / 4 : Formalism.MainNotions.TaylorLogMetric.Qbar) : ℂ) := by
      rw [e3]; push_cast; rfl
    rw [this, lamC_coe, map_div₀, map_neg, map_ofNat, ← hι a3]
  have hW : C • Formalism.MainNotions.TaylorLogMetric.wModel lam (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.A.shortW g2' g3' := by
    have hw : Formalism.MainNotions.TaylorLogMetric.wModel lam (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) = ⟨0, 0, 0, -(ι L.g₂) / 4, -(ι L.g₃) / 4⟩ := by
      simp only [Formalism.MainNotions.TaylorLogMetric.wModel, ea4, ea6]
    rw [hw]
    ext <;> simp [C, Formalism.L2.Th1.A.shortW, hg2', hg3', WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆] <;> ring
  obtain ⟨g, hgl, hgL, -, hOk, hM, hLT⟩ :=
    datum_of_short h5 lam (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) C g2' g3' hW k2 k3 n2 n3 nd ε hε1 hεint
  exact ⟨g, hgl, ⟨hcurve, hcop, hδ12, hgL, hOk⟩, hM, hLT⟩

/- English proof (translation)
Introduce `hGood hHt _ D cc δ hcurve hδ12 p _ h5 hIn lam`. Take `⟨cc', δ', hc', hd', hcop, hlat⟩` from `Formalism.L2.KerInert.curve_ideal_prime D cc δ hcurve hδ12 p hIn`. Take `⟨g, hgl, hAt, hM, hLT⟩` from `datum_exists_coprime hGood hHt D cc' δ' hc' hd' p hcop h5 hIn lam`. Conclude with `⟨cc', δ', g, hc', hd', hlat.symm, hgl, hAt, hM, hLT⟩`.
-/
theorem datum_exists_lattice : Formalism.L2.Th1.CM.CM2 → Formalism.L2.Th1.CM.CM3 → Formalism.L2.Th1.CM.CM4 →
    Formalism.L2.KerInert.GenusOneModelExistsLattice := by
  intro hGood hHt _ D cc δ hcurve hδ12 p _ h5 hIn lam
  obtain ⟨cc', δ', hc', hd', hcop, hlat⟩ := Formalism.L2.KerInert.curve_ideal_prime D cc δ hcurve hδ12 p hIn
  obtain ⟨g, hgl, hAt, hM, hLT⟩ := datum_exists_coprime hGood hHt D cc' δ' hc' hd' p hcop h5 hIn lam
  exact ⟨cc', δ', g, hc', hd', hlat.symm, hgl, hAt, hM, hLT⟩

end GlobalTheory.InertGenusOne
