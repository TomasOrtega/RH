import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntSerOfIsWq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralBoundedSeriesLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SqThD
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSigmaStarTranslatePowDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeDerivWeierstrassPParameterSeriesBouStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTaylorCombinationParameterSeriesAlgebraStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ThetaTransl
open GlobalTheory.EvenTheta

variable {p : ℕ} [Fact p.Prime]

def GoodAt (g : GL3Theta.G1 p) (k : ℕ) (F : ℂ → ℂ) : Prop :=
  AlgEnt F ∧ ∃ B : PowerSeries ℂ_[p], BddSer B ∧ g.atU F = ePhi1 g.lam g.abelian₂ g.C g.wq ^ k * B

/- English proof (translation)
The claim follows from `((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 f h hf hh).2.2`.
-/
theorem bdd_mul {f h : PowerSeries ℂ_[p]} (hf : BddSer f) (hh : BddSer h) : BddSer (f * h) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 f h hf hh).2.2

/- English proof (translation)
The claim follows from `((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 f h hf hh).1`.
-/
theorem bdd_add {f h : PowerSeries ℂ_[p]} (hf : BddSer f) (hh : BddSer h) : BddSer (f + h) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 f h hf hh).1

/- English proof (translation)
The claim follows from `((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 f h hf hh).2.1`.
-/
theorem bdd_sub {f h : PowerSeries ℂ_[p]} (hf : BddSer f) (hh : BddSer h) : BddSer (f - h) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 f h hf hh).2.1

/- English proof (translation)
The claim follows from `((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 c).1`.
-/
theorem bdd_C (c : ℂ_[p]) : BddSer (PowerSeries.C c) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 c).1

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, (GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.2.1⟩`.
-/
theorem bdd_X : BddSer (PowerSeries.X : PowerSeries ℂ_[p]) :=
  ⟨1, (GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.2.1⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨0, fun n => by simp⟩`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `bdd_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem bdd_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℂ_[p]) (h : ∀ i ∈ s, BddSer (f i)) :
    BddSer (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun n => by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact bdd_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Establish `h : (1 : ℂ) ∈ Qbar` using `one_mem _`. Rewrite using `[lamC, dif_pos h]`. Conclude with `map_one lam`.
-/
theorem lamC_one (lam : Qbar →+* ℂ_[p]) : lamC lam 1 = 1 := by
  have h : (1 : ℂ) ∈ Qbar := one_mem _
  rw [lamC, dif_pos h]
  exact map_one lam

/- English proof (translation)
Take `⟨hFa, B, hB, hFe⟩` from `hF`. Take `⟨hGa, B', hB', hGe⟩` from `hG`. Take `⟨ha, he⟩` from `((GlobalTheory.SerTransport.transport p g).1 F G hFa hGa).1`. Use `⟨ha, B * B', bdd_mul hB hB', ?_⟩` and prove the remaining obligations. Rewrite using `[he, hFe, hGe, pow_add]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem good_mul {g : GL3Theta.G1 p} {k l : ℕ} {F G : ℂ → ℂ} (hF : GoodAt g k F) (hG : GoodAt g l G) :
    GoodAt g (k + l) (fun z => F z * G z) := by
  obtain ⟨hFa, B, hB, hFe⟩ := hF
  obtain ⟨hGa, B', hB', hGe⟩ := hG
  obtain ⟨ha, he⟩ := ((GlobalTheory.SerTransport.transport p g).1 F G hFa hGa).1
  refine ⟨ha, B * B', bdd_mul hB hB', ?_⟩
  rw [he, hFe, hGe, pow_add]
  ring

/- English proof (translation)
Take `⟨ha, he⟩` from `(GlobalTheory.SerTransport.transport p g).2.1 1 (one_mem _)`. Use `⟨ha, 1, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using bdd_C (p := p) 1`. Rewrite using `[he, lamC_one, map_one, pow_zero, one_mul]`.
-/
theorem good_one (g : GL3Theta.G1 p) : GoodAt g 0 (fun _ => (1 : ℂ)) := by
  obtain ⟨ha, he⟩ := (GlobalTheory.SerTransport.transport p g).2.1 1 (one_mem _)
  refine ⟨ha, 1, ?_, ?_⟩
  · simpa using bdd_C (p := p) 1
  · rw [he, lamC_one, map_one, pow_zero, one_mul]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using good_one g`. Consider the case `succ n ih`. Use `good_mul ih hF` as an intermediate fact. Simplify using `only [← pow_succ] at this`.

Rewrite `this` using `[show k * n + k = k * (n + 1) by ring]`. Then use the resulting hypothesis.
-/
theorem good_pow {g : GL3Theta.G1 p} {k : ℕ} {F : ℂ → ℂ} (hF : GoodAt g k F) (n : ℕ) :
    GoodAt g (k * n) (fun z => F z ^ n) := by
  induction n with
  | zero => simpa using good_one g
  | succ n ih =>
    have := good_mul ih hF
    simp only [← pow_succ] at this
    rwa [show k * n + k = k * (n + 1) by ring] at this

/- English proof (translation)
The claim follows from `e ▸ h`.
-/
theorem good_congr {g : GL3Theta.G1 p} {k l : ℕ} {F : ℂ → ℂ} (h : GoodAt g k F) (e : k = l) : GoodAt g l F :=
  e ▸ h

/- English proof (translation)
Establish `hpow : ∀ {H : ℂ → ℂ}, AlgEnt H → ∀ k : ℕ, AlgEnt (fun z => H z ^ k) ∧ g.atU (fun z => H z ^ k) = g.atU H ^ k`. Introduce `H hH k`. Proceed by induction on `k with`. Consider the case `zero`. Take `⟨ha, he⟩` from `(GlobalTheory.SerTransport.transport p g).2.1 1 (one_mem _)`.

Simplify using `only [pow_zero]`. Conclude with `⟨ha, by rw [he, lamC_one, map_one]⟩`. Consider the case `succ k ih`. Take `⟨ha, he⟩` from `((GlobalTheory.SerTransport.transport p g).1 _ H ih.1 hH).1`. Simplify using `only [pow_succ]`.

Conclude with `⟨ha, by rw [he, ih.2]⟩`. Take `⟨h1, e1⟩` from `hpow hF m`. Take `⟨h2, e2⟩` from `hpow hG n`. Take `⟨ha, he⟩` from `((GlobalTheory.SerTransport.transport p g).1 _ _ h1 h2).1`. Conclude with `⟨ha, by rw [he, e1, e2]⟩`.
-/
theorem atU_mul_pow {g : GL3Theta.G1 p} {F G : ℂ → ℂ} (hF : AlgEnt F) (hG : AlgEnt G) (m n : ℕ) :
    AlgEnt (fun z => F z ^ m * G z ^ n) ∧ g.atU (fun z => F z ^ m * G z ^ n) = g.atU F ^ m * g.atU G ^ n := by
  have hpow : ∀ {H : ℂ → ℂ}, AlgEnt H → ∀ k : ℕ, AlgEnt (fun z => H z ^ k) ∧
      g.atU (fun z => H z ^ k) = g.atU H ^ k := by
    intro H hH k
    induction k with
    | zero =>
      obtain ⟨ha, he⟩ := (GlobalTheory.SerTransport.transport p g).2.1 1 (one_mem _)
      simp only [pow_zero]
      exact ⟨ha, by rw [he, lamC_one, map_one]⟩
    | succ k ih =>
      obtain ⟨ha, he⟩ := ((GlobalTheory.SerTransport.transport p g).1 _ H ih.1 hH).1
      simp only [pow_succ]
      exact ⟨ha, by rw [he, ih.2]⟩
  obtain ⟨h1, e1⟩ := hpow hF m
  obtain ⟨h2, e2⟩ := hpow hG n
  obtain ⟨ha, he⟩ := ((GlobalTheory.SerTransport.transport p g).1 _ _ h1 h2).1
  exact ⟨ha, by rw [he, e1, e2]⟩

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `D p _ cc δ g hg t ht N hN hNt`. Take `⟨hcc, -, hδ, hΛ, hok⟩` from `hg`. Establish `hcrv : Crv D cc δ` using `⟨hcc, hδ⟩`. Establish `hG` using `(GlobalTheory.InducedType.induced_type D).1`. Take `⟨hlat, -, hdisc, -, -⟩` from `GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv`.

Take `⟨⟨-, h2, h3⟩, hwp⟩` from `(GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv`. Establish `huse` using `(GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1`. Simplify using `only [tor0] at h2 h3`. Rewrite `hlat`, `hdisc`, `h2`, `h3`, `hwp`, `huse` using `[← hΛ]`. Establish `hlat' : IsLat g.abelian₂` using `hlat`.

Establish `halg : ∀ x, InRationalLattice g.abelian₂ x → AlgEnt (U1 g.abelian₂ x (sgStar g.abelian₂))` using `fun x hx => ⟨by`. Use `hlat'.differentiable` as an intermediate fact. Unfold `U1`. Use the proof step `fun_prop, huse x hx⟩`. Establish `hU0 : U1 g.abelian₂ 0 (sgStar g.abelian₂) = sgStar g.abelian₂`.

Use function extensionality and compare the values at `z`. Simplify using `[U1]`. Establish `hsg : AlgEnt (sgStar g.abelian₂)` using `hU0 ▸ halg 0 ⟨1, one_pos, by simp⟩`. Establish `htq : InRationalLattice g.abelian₂ t` using `⟨N, hN, hNt⟩`. Establish `hP` using `halg t htq`.

Establish `htn` using `ht.1`. Establish `hwt : wpF g.abelian₂ t ∈ Qbar` using `(hwp t htq htn).1`. Take `⟨hu1, hwq1, -, he0, hsgU⟩` from `GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc`. Use `set e := ePhi1 g.lam g.abelian₂ g.C g.wq with he_def`. Use `set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε_def`.

Establish `he : e ≠ 0` using `fun h => by rw [h, map_zero] at he0; exact zero_ne_one he0`. Establish `gσ : GoodAt g 1 (sgStar g.abelian₂)` using `⟨hsg, PowerSeries.C ε * PowerSeries.X, bdd_mul (bdd_C ε) bdd_X, by rw [hsgU]; ring⟩`. Take `⟨hSa, hSe⟩` from `GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 hsg t htn hwt`. Establish `gS : GoodAt g 2 (sqTh g.abelian₂ t)` using `⟨hSa, lineSer g.wq⁻¹ (xAt g t), bdd_sub ⟨1, hwq1⟩ (bdd_mul (bdd_C _) (by rw [sq]; exact bdd_mul (bdd_X (p := p)) (bdd_X (p := p)))), hSe⟩`. Take `⟨hTa, w, hw, hTe⟩` from `GlobalTheory.T.sigmaStarCubeDerivWeierstrassP_parameterSeries_bounded p g hok hlat' h2 h3 hdisc hsg t htn hwt`.

Establish `gT : GoodAt g 3 (sqThD g.abelian₂ t)` using `⟨hTa, w, hw, hTe⟩`. Take `⟨I, a, b, hle, hid⟩` from `GlobalTheory.T.exists_sigmaStar_translate_pow_decomposition g.abelian₂ hlat' t N hN hNt t htn`. Set `φ : Fin (I + 1) ⊕ Fin (I + 1) → ℂ → ℂ` to `Sum.elim (fun i z => sgStar g.abelian₂ z ^ (2 * (I - (i : ℕ)) + 3) * sqTh g.abelian₂ t z ^ (i : ℕ)) (fun j z => sgStar g.abelian₂ z ^ (2 * (I - (j : ℕ))) * sqTh g.abelian₂ t z ^ (j : ℕ) * sqThD g.abelian₂ t z)`. Set `c : Fin (I + 1) ⊕ Fin (I + 1) → ℂ` to `Sum.elim (fun i => a i) (fun j => b j)`. Establish `gφ : ∀ k, GoodAt g (2 * I + 3) (φ k)`.

Introduce and unpack `(i | j)`. Establish `hi` using `i.isLt`. Conclude with `good_congr (good_mul (good_pow gσ (2 * (I - (i : ℕ)) + 3)) (good_pow gS (i : ℕ))) (by omega)`. Establish `hj` using `j.isLt`. Conclude with `good_congr (good_mul (good_mul (good_pow gσ (2 * (I - (j : ℕ)))) (good_pow gS (j : ℕ))) gT) (by omega)`.

Take `⟨hEa, hEe⟩` from `atU_mul_pow (g := g) hsg hP (2 * I + 3 - N) N`. Establish `hEq : ∀ z, sgStar g.abelian₂ z ^ (2 * I + 3 - N) * U1 g.abelian₂ t (sgStar g.abelian₂) z ^ N = ∑ k, c k * φ k z`. Introduce `z`. Rewrite using `[hid z, Fintype.sum_sum_type]`. Use `congr 1`.

Rewrite using `[← Fin.sum_univ_eq_sum_range]`. Both sides reduce to the same expression. Rewrite using `[← Fin.sum_univ_eq_sum_range]`. Both sides reduce to the same expression. Take `⟨a', -, hlin⟩` from `GlobalTheory.T.algebraicTaylorCombination_parameterSeries_algebraic p g _ φ c _ hEa (fun k => (gφ k).1) hEq`.

Use `choose B hB hBe using fun k => (gφ k).2`. Establish `hS : BddSer (∑ k, PowerSeries.C (lamC g.lam (a' k)) * B k)` using `bdd_sum _ _ fun k _ => bdd_mul (bdd_C _) (hB k)`. Rewrite `hlin` using `[hEe, hsgU]`. Simplify using `only [hBe] at hlin`. Establish `hPe : g.atU (U1 g.abelian₂ t (sgStar g.abelian₂)) = e * tau g t`.

Rewrite using `[tau, ← mul_assoc, PowerSeries.mul_inv_cancel _ (by rw [he0]; exact one_ne_zero), one_mul]`. Rewrite `hlin` using `[hPe]`. Use `set K := 2 * I + 3 - N with hKd`. Establish `hK : K + N = 2 * I + 3` using `Nat.sub_add_cancel hle`. Establish `hsum : ∑ k, PowerSeries.C (lamC g.lam (a' k)) * (e ^ (2 * I + 3) * B k) = e ^ (2 * I + 3) * ∑ k, PowerSeries.C (lamC g.lam (a' k)) * B k`.

Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring`. Establish `hleft : (PowerSeries.C ε * PowerSeries.X * e) ^ K * (e * tau g t) ^ N = e ^ (2 * I + 3) * (PowerSeries.C (ε ^ K) * (PowerSeries.X ^ K * tau g t ^ N))`. Rewrite using `[← hK, pow_add, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `key` using `hleft.symm.trans (hlin.trans hsum)`.

Establish `key2` using `mul_left_cancel₀ (pow_ne_zero _ he) key`. Take `⟨C0, hC0⟩` from `hS`. Use `⟨C0, fun n => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (PowerSeries.coeff (n + K)) key2`. Rewrite `h1` using `[PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel]`.

Establish `h2` using `hC0 (n + K)`. Rewrite `h2` using `[← h1, norm_mul, norm_pow, hu1, one_pow, one_mul]`. Conclude with `h2`.
-/
theorem tau_pow_bdd : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → ∀ t : ℂ, GL3Theta.Tors1 p g.abelian₂ t → ∀ N : ℕ, 0 < N → (N : ℂ) * t ∈ g.abelian₂ →
      GlobalTheory.EvenTheta.BddSer (GlobalTheory.ThetaTransl.tau g t ^ N) := by
  intro D p _ cc δ g hg t ht N hN hNt
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, hdisc, -, -⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat hdisc h2 h3 hwp huse
  have hlat' : IsLat g.abelian₂ := hlat
  have halg : ∀ x, InRationalLattice g.abelian₂ x → AlgEnt (U1 g.abelian₂ x (sgStar g.abelian₂)) := fun x hx => ⟨by
    have := hlat'.differentiable
    unfold U1
    fun_prop, huse x hx⟩
  have hU0 : U1 g.abelian₂ 0 (sgStar g.abelian₂) = sgStar g.abelian₂ := by
    funext z; simp [U1]
  have hsg : AlgEnt (sgStar g.abelian₂) := hU0 ▸ halg 0 ⟨1, one_pos, by simp⟩
  have htq : InRationalLattice g.abelian₂ t := ⟨N, hN, hNt⟩
  have hP := halg t htq
  have htn := ht.1
  have hwt : wpF g.abelian₂ t ∈ Qbar := (hwp t htq htn).1
  obtain ⟨hu1, hwq1, -, he0, hsgU⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc
  set e := ePhi1 g.lam g.abelian₂ g.C g.wq with he_def
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε_def
  have he : e ≠ 0 := fun h => by rw [h, map_zero] at he0; exact zero_ne_one he0
  have gσ : GoodAt g 1 (sgStar g.abelian₂) :=
    ⟨hsg, PowerSeries.C ε * PowerSeries.X, bdd_mul (bdd_C ε) bdd_X, by rw [hsgU]; ring⟩
  obtain ⟨hSa, hSe⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 hsg t htn hwt
  have gS : GoodAt g 2 (sqTh g.abelian₂ t) := ⟨hSa, lineSer g.wq⁻¹ (xAt g t),
    bdd_sub ⟨1, hwq1⟩ (bdd_mul (bdd_C _) (by rw [sq]; exact bdd_mul (bdd_X (p := p)) (bdd_X (p := p)))), hSe⟩
  obtain ⟨hTa, w, hw, hTe⟩ := GlobalTheory.T.sigmaStarCubeDerivWeierstrassP_parameterSeries_bounded p g hok hlat' h2 h3 hdisc hsg t htn hwt
  have gT : GoodAt g 3 (sqThD g.abelian₂ t) := ⟨hTa, w, hw, hTe⟩
  obtain ⟨I, a, b, hle, hid⟩ := GlobalTheory.T.exists_sigmaStar_translate_pow_decomposition g.abelian₂ hlat' t N hN hNt t htn
  let φ : Fin (I + 1) ⊕ Fin (I + 1) → ℂ → ℂ := Sum.elim
    (fun i z => sgStar g.abelian₂ z ^ (2 * (I - (i : ℕ)) + 3) * sqTh g.abelian₂ t z ^ (i : ℕ))
    (fun j z => sgStar g.abelian₂ z ^ (2 * (I - (j : ℕ))) * sqTh g.abelian₂ t z ^ (j : ℕ) * sqThD g.abelian₂ t z)
  let c : Fin (I + 1) ⊕ Fin (I + 1) → ℂ := Sum.elim (fun i => a i) (fun j => b j)
  have gφ : ∀ k, GoodAt g (2 * I + 3) (φ k) := by
    rintro (i | j)
    · have hi := i.isLt
      exact good_congr (good_mul (good_pow gσ (2 * (I - (i : ℕ)) + 3)) (good_pow gS (i : ℕ))) (by omega)
    · have hj := j.isLt
      exact good_congr (good_mul (good_mul (good_pow gσ (2 * (I - (j : ℕ)))) (good_pow gS (j : ℕ))) gT)
        (by omega)
  obtain ⟨hEa, hEe⟩ := atU_mul_pow (g := g) hsg hP (2 * I + 3 - N) N
  have hEq : ∀ z, sgStar g.abelian₂ z ^ (2 * I + 3 - N) * U1 g.abelian₂ t (sgStar g.abelian₂) z ^ N = ∑ k, c k * φ k z := by
    intro z
    rw [hid z, Fintype.sum_sum_type]
    congr 1
    · rw [← Fin.sum_univ_eq_sum_range]; rfl
    · rw [← Fin.sum_univ_eq_sum_range]; rfl
  obtain ⟨a', -, hlin⟩ := GlobalTheory.T.algebraicTaylorCombination_parameterSeries_algebraic p g _ φ c _ hEa (fun k => (gφ k).1) hEq
  choose B hB hBe using fun k => (gφ k).2
  have hS : BddSer (∑ k, PowerSeries.C (lamC g.lam (a' k)) * B k) :=
    bdd_sum _ _ fun k _ => bdd_mul (bdd_C _) (hB k)
  rw [hEe, hsgU] at hlin
  simp only [hBe] at hlin
  have hPe : g.atU (U1 g.abelian₂ t (sgStar g.abelian₂)) = e * tau g t := by
    rw [tau, ← mul_assoc, PowerSeries.mul_inv_cancel _ (by rw [he0]; exact one_ne_zero), one_mul]
  rw [hPe] at hlin
  set K := 2 * I + 3 - N with hKd
  have hK : K + N = 2 * I + 3 := Nat.sub_add_cancel hle
  have hsum : ∑ k, PowerSeries.C (lamC g.lam (a' k)) * (e ^ (2 * I + 3) * B k) =
      e ^ (2 * I + 3) * ∑ k, PowerSeries.C (lamC g.lam (a' k)) * B k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have hleft : (PowerSeries.C ε * PowerSeries.X * e) ^ K * (e * tau g t) ^ N =
      e ^ (2 * I + 3) * (PowerSeries.C (ε ^ K) * (PowerSeries.X ^ K * tau g t ^ N)) := by
    rw [← hK, pow_add, map_pow]; ring
  have key := hleft.symm.trans (hlin.trans hsum)
  have key2 := mul_left_cancel₀ (pow_ne_zero _ he) key
  obtain ⟨C0, hC0⟩ := hS
  refine ⟨C0, fun n => ?_⟩
  have h1 := congrArg (PowerSeries.coeff (n + K)) key2
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel] at h1
  have h2 := hC0 (n + K)
  rw [← h1, norm_mul, norm_pow, hu1, one_pow, one_mul] at h2
  exact h2

end GlobalTheory.ThetaTransl
