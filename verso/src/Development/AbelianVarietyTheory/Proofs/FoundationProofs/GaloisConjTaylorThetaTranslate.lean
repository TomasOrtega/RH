import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisTaylorSeriesCanonicalOddThetaAllStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SecondDerivSigmaProductAtZero

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Filter Topology PeriodPair

namespace GlobalTheory.JetConj

/- English proof (translation)
Take `⟨w₁, w₂, h, rfl⟩` from `h`. Use `⟨⟨w₁, w₂, h⟩, fun z => ?_⟩` and prove the remaining obligations. Simplify using `[AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]`.
-/
lemma exists_periodPair {Λ : AddSubgroup ℂ}
    (h : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    ∃ L : PeriodPair, ∀ z, z ∈ Λ ↔ z ∈ L.lattice := by
  obtain ⟨w₁, w₂, h, rfl⟩ := h
  refine ⟨⟨w₁, w₂, h⟩, fun z => ?_⟩
  simp [AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]

/- English proof (translation)
Use `⟨L.ω₁, L.ω₂, L.indep, ?_⟩` and prove the remaining obligations. Use extensionality with `z`. Simplify using `[h, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]`.
-/
lemma exists_basis_of_periodPair {Λ : AddSubgroup ℂ} {L : PeriodPair} (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂} := by
  refine ⟨L.ω₁, L.ω₂, L.indep, ?_⟩
  ext z
  simp [h, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]

variable {Λ : AddSubgroup ℂ} {L : PeriodPair}

/- English proof (translation)
Take `⟨⟨a, b, -, -⟩, c, -, d, -⟩` from `GlobalTheory.OddTheta.sgStar_laws Λ (exists_basis_of_periodPair h)`. Take `⟨-, -, -, -, e, -⟩` from `GlobalTheory.LatticeInvariants.invariants_dictionary L Λ h`. Use `⟨a, b, fun z => (c z).trans (h z), fun u v hu hv => ?_⟩` and prove the remaining obligations. Rewrite `hu`, `hv` using `[← h]`. Rewrite using `[← (e u hu).1, ← (e v hv).1]`.

Conclude with `d u v hu hv`.
-/
lemma isSigmaLike_sgStar (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) : IsSigmaLike L (sgStar Λ) := by
  obtain ⟨⟨a, b, -, -⟩, c, -, d, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ (exists_basis_of_periodPair h)
  obtain ⟨-, -, -, -, e, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ h
  refine ⟨a, b, fun z => (c z).trans (h z), fun u v hu hv => ?_⟩
  rw [← h] at hu hv
  rw [← (e u hu).1, ← (e v hv).1]
  exact d u v hu hv

/- English proof (translation)
Unfold `U1`. Use `fun_prop`.
-/
lemma differentiable_U1 {G : ℂ → ℂ} (hG : Differentiable ℂ G) (x : ℂ) : Differentiable ℂ (U1 Λ x G) := by
  unfold U1
  fun_prop

/- English proof (translation)
Take `⟨⟨-, -, -, a⟩, -⟩` from `GlobalTheory.OddTheta.sgStar_laws Λ (exists_basis_of_periodPair h)`. Use function extensionality and compare the values at `z`. Establish `: x ∈ Λ`. Use `Λ.add_mem hx hx` as an intermediate fact. Rewrite `this` using `[add_halves]`. Then use the resulting hypothesis.

Rewrite using `[a x this, if_pos hx, one_mul]`.
-/
lemma thetaTranslate_canonicalOddTheta_of_half_mem (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) {x : ℂ} (hx : x / 2 ∈ Λ) :
    U1 Λ x (sgStar Λ) = sgStar Λ := by
  obtain ⟨⟨-, -, -, a⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ (exists_basis_of_periodPair h)
  funext z
  have : x ∈ Λ := by
    have := Λ.add_mem hx hx
    rwa [add_halves] at this
  rw [a x this, if_pos hx, one_mul]

/- English proof (translation)
Unfold `U1 divQuot`. Rewrite using `[mul_pow, ← Complex.exp_nat_mul]`. Establish `: -(Real.pi : ℂ) * (n * z) * (starRingEnd ℂ) (n * u) / (area Λ : ℂ) - (Real.pi : ℂ) * (n * u) * (starRingEnd ℂ) (n * u) / (2 * (area Λ : ℂ)) = ((n ^ 2 : ℕ) : ℂ) * (-(Real.pi : ℂ) * z * (starRingEnd ℂ) u / (area Λ : ℂ) - (Real.pi : ℂ) * u * (starRingEnd ℂ) u / (2 * (area Λ : ℂ)))`. Simplify using `only [map_mul, map_natCast]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts.
-/
lemma thetaTranslate_natCast_mul {G : ℂ → ℂ} {u z : ℂ} (hz : G (z + u) ≠ 0) (n : ℕ) :
    U1 Λ (n * u) G (n * z) = U1 Λ u G z ^ (n ^ 2) * divQuot G u n z := by
  unfold U1 divQuot
  rw [mul_pow, ← Complex.exp_nat_mul]
  have : -(Real.pi : ℂ) * (n * z) * (starRingEnd ℂ) (n * u) / (area Λ : ℂ) -
      (Real.pi : ℂ) * (n * u) * (starRingEnd ℂ) (n * u) / (2 * (area Λ : ℂ)) =
      ((n ^ 2 : ℕ) : ℂ) * (-(Real.pi : ℂ) * z * (starRingEnd ℂ) u / (area Λ : ℂ) -
      (Real.pi : ℂ) * u * (starRingEnd ℂ) u / (2 * (area Λ : ℂ))) := by
    simp only [map_mul, map_natCast]
    push_cast
    ring
  rw [this]
  field_simp

/- English proof (translation)
Establish `hs' : (s : ℂ) ^ 2 = 1` using `by exact_mod_cast hs`. Unfold `U1`. Rewrite using `[mul_assoc (G _), ← Complex.exp_add]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [map_mul, Complex.conj_ofReal]`. Use `push_cast`. Take the linear combination `(-((Real.pi : ℂ) * u * (starRingEnd ℂ) u / (2 * (area Λ : ℂ)))) * hs'`.
-/
lemma thetaTranslate_zero_at_shifted_point (G : ℂ → ℂ) (u : ℂ) (N s : ℝ) (hs : s ^ 2 = 1) :
    U1 Λ ((N + s : ℝ) * u) G 0 = U1 Λ (N * u) G (s * u) *
      Complex.exp (-((Real.pi : ℂ) * u * (starRingEnd ℂ) u / (2 * (area Λ : ℂ)))) := by
  have hs' : (s : ℂ) ^ 2 = 1 := by exact_mod_cast hs
  unfold U1
  rw [mul_assoc (G _), ← Complex.exp_add]
  congr 2
  · push_cast; ring
  · simp only [map_mul, Complex.conj_ofReal]
    push_cast
    linear_combination (-((Real.pi : ℂ) * u * (starRingEnd ℂ) u / (2 * (area Λ : ℂ)))) * hs'

/- English proof (translation)
Establish `H` using `isSigmaLike_sgStar h`. Take `⟨⟨-, -, hodd, hq⟩, -⟩` from `GlobalTheory.OddTheta.sgStar_laws Λ (exists_basis_of_periodPair h)`. Establish `hu' : 0 + u ∉ L.lattice` using `by simpa [← h] using hu`. Establish `hev : ∀ᶠ z in 𝓝 0, sgStar Λ (z + u) ≠ 0` using `(eventually_add_notMem L hu').mono fun z hz => mt (H.zero_iff _).1 hz`. Establish `h0 : sgStar Λ (0 + u) ≠ 0` using `hev.self_of_nhds`.

Establish `hc : U1 Λ u (sgStar Λ) 0 ≠ 0` using `mul_ne_zero h0 (Complex.exp_ne_zero _)`. Use `⟨fun z => U1 Λ u (sgStar Λ) z ^ ((2 * m) ^ 2), ((differentiable_U1 H.diff u).analyticAt 0).fun_pow _, pow_ne_zero _ hc, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hev] with z hz using thetaTranslate_natCast_mul hz _`. Use `filter_upwards [hev] with z hz`. Rewrite using `[← pow_mul, show (2 * m) ^ 2 * m ^ 2 = (2 * m ^ 2) ^ 2 by ring, ← thetaTranslate_natCast_mul hz, thetaTranslate_canonicalOddTheta_of_half_mem h]`.

Use `hN using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e1` using `thetaTranslate_natCast_mul (Λ := Λ) h0 (k + 2)`. Establish `e2` using `thetaTranslate_natCast_mul (Λ := Λ) h0 k`.

Establish `f1` using `thetaTranslate_zero_at_shifted_point (Λ := Λ) (sgStar Λ) u (k + 1) 1 (by norm_num)`. Establish `f2` using `thetaTranslate_zero_at_shifted_point (Λ := Λ) (sgStar Λ) u (k + 1) (-1) (by norm_num)`. Establish `hN' : ((k + 1 : ℝ) : ℂ) * u ∈ Λ`. Rewrite `hN` using `[hk]`. Conclude with `hN` after adjusting the coercions.

Rewrite `f1`, `f2` using `[hq _ hN']`. Rewrite `f1` using `[show ((k + 1 + 1 : ℝ) : ℂ) = ((k + 2 : ℕ) : ℂ) by push_cast; ring]`. Rewrite `f2` using `[show ((k + 1 + -1 : ℝ) : ℂ) = ((k : ℕ) : ℂ) by push_cast; ring]`. Rewrite `e1`, `e2` using `[mul_zero]`. Rewrite `f1` using `[e1, Complex.ofReal_one, one_mul u]`.

Rewrite `f2` using `[e2, Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul u, hodd]`. Establish `hψ : divQuot (sgStar Λ) u (k + 2) 0 ≠ 0`. Introduce `e`. Rewrite `f1` using `[e, mul_zero]`. Rewrite `h0` using `[zero_add]`.

Use `mul_ne_zero (mul_ne_zero ?_ h0) (Complex.exp_ne_zero _) f1.symm` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> norm_num`. Rewrite using `[eq_mul_inv_iff_mul_eq₀ hψ]`. Apply `mul_left_cancel₀ (pow_ne_zero (k ^ 2) hc)` to reduce the goal to its premises. Rewrite `f1` using `[show (k + 2) ^ 2 = k ^ 2 + (2 * m) ^ 2 by nlinarith, pow_add]`.

Take the linear combination `f1 + f2`.
-/
lemma translate_facts (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) {u : ℂ} (hu : u ∉ Λ) {m k : ℕ}
    (hk : m ^ 2 = k + 1) (hN : ((m ^ 2 : ℕ) : ℂ) * u ∈ Λ) :
    ∃ K : ℂ → ℂ, AnalyticAt ℂ K 0 ∧ K 0 ≠ 0 ∧
      ((fun z => U1 Λ ((2 * m : ℕ) * u) (sgStar Λ) ((2 * m : ℕ) * z)) =ᶠ[𝓝 0]
        fun z => K z * divQuot (sgStar Λ) u (2 * m) z) ∧
      ((fun z => sgStar Λ ((2 * m ^ 2 : ℕ) * z)) =ᶠ[𝓝 0]
        fun z => K z ^ (m ^ 2) * divQuot (sgStar Λ) u (2 * m ^ 2) z) ∧
      K 0 = (0 - divQuot (sgStar Λ) u k 0) * (divQuot (sgStar Λ) u (k + 2) 0)⁻¹ := by
  have H := isSigmaLike_sgStar h
  obtain ⟨⟨-, -, hodd, hq⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ (exists_basis_of_periodPair h)
  have hu' : 0 + u ∉ L.lattice := by simpa [← h] using hu
  have hev : ∀ᶠ z in 𝓝 0, sgStar Λ (z + u) ≠ 0 :=
    (eventually_add_notMem L hu').mono fun z hz => mt (H.zero_iff _).1 hz
  have h0 : sgStar Λ (0 + u) ≠ 0 := hev.self_of_nhds
  have hc : U1 Λ u (sgStar Λ) 0 ≠ 0 := mul_ne_zero h0 (Complex.exp_ne_zero _)
  refine ⟨fun z => U1 Λ u (sgStar Λ) z ^ ((2 * m) ^ 2),
    ((differentiable_U1 H.diff u).analyticAt 0).fun_pow _, pow_ne_zero _ hc, ?_, ?_, ?_⟩
  · filter_upwards [hev] with z hz using thetaTranslate_natCast_mul hz _
  · filter_upwards [hev] with z hz
    rw [← pow_mul, show (2 * m) ^ 2 * m ^ 2 = (2 * m ^ 2) ^ 2 by ring, ← thetaTranslate_natCast_mul hz,
      thetaTranslate_canonicalOddTheta_of_half_mem h]
    convert hN using 1
    push_cast
    ring
  · have e1 := thetaTranslate_natCast_mul (Λ := Λ) h0 (k + 2)
    have e2 := thetaTranslate_natCast_mul (Λ := Λ) h0 k
    have f1 := thetaTranslate_zero_at_shifted_point (Λ := Λ) (sgStar Λ) u (k + 1) 1 (by norm_num)
    have f2 := thetaTranslate_zero_at_shifted_point (Λ := Λ) (sgStar Λ) u (k + 1) (-1) (by norm_num)
    have hN' : ((k + 1 : ℝ) : ℂ) * u ∈ Λ := by
      rw [hk] at hN
      exact_mod_cast hN
    rw [hq _ hN'] at f1 f2
    rw [show ((k + 1 + 1 : ℝ) : ℂ) = ((k + 2 : ℕ) : ℂ) by push_cast; ring] at f1
    rw [show ((k + 1 + -1 : ℝ) : ℂ) = ((k : ℕ) : ℂ) by push_cast; ring] at f2
    rw [mul_zero] at e1 e2
    rw [e1, Complex.ofReal_one, one_mul u] at f1
    rw [e2, Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul u, hodd] at f2
    have hψ : divQuot (sgStar Λ) u (k + 2) 0 ≠ 0 := by
      intro e
      rw [e, mul_zero] at f1
      rw [zero_add] at h0
      refine mul_ne_zero (mul_ne_zero ?_ h0) (Complex.exp_ne_zero _) f1.symm
      split_ifs <;> norm_num
    rw [eq_mul_inv_iff_mul_eq₀ hψ]
    apply mul_left_cancel₀ (pow_ne_zero (k ^ 2) hc)
    rw [show (k + 2) ^ 2 = k ^ 2 + (2 * m) ^ 2 by nlinarith, pow_add] at f1
    linear_combination f1 + f2

/- English proof (translation)
Establish `hn : (n.factorial : ℂ) ≠ 0` using `by exact_mod_cast n.factorial_ne_zero`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `M.mul_mem h (natCast_mem M n.factorial)` as an intermediate fact. Rewrite `this` using `[coef1, div_mul_cancel₀ _ hn]`. Then use the resulting hypothesis.

Conclude with `fun h => M.div_mem h (natCast_mem M _)`.
-/
lemma taylorCoeff_mem_iff_iteratedDeriv_mem {M : IntermediateField ℚ ℂ} {f : ℂ → ℂ} {n : ℕ} :
    coef1 f n ∈ M ↔ iteratedDeriv n f 0 ∈ M := by
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  constructor
  · intro h
    have := M.mul_mem h (natCast_mem M n.factorial)
    rwa [coef1, div_mul_cancel₀ _ hn] at this
  · exact fun h => M.div_mem h (natCast_mem M _)

/- English proof (translation)
Rewrite using `[mem_graph]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, e⟩`. Conclude with `⟨h, by rw [cj, TaylorLogMetric.liftM, dif_pos h, e]⟩`. Introduce and unpack `⟨h, e⟩`.

Conclude with `⟨h, by rwa [cj, TaylorLogMetric.liftM, dif_pos h] at e⟩`.
-/
lemma mem_graph_iff_cj {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {a b : ℂ} :
    (a, b) ∈ graph M ρ ↔ a ∈ M ∧ cj M ρ a = b := by
  rw [mem_graph]
  constructor
  · rintro ⟨h, e⟩
    exact ⟨h, by rw [cj, TaylorLogMetric.liftM, dif_pos h, e]⟩
  · rintro ⟨h, e⟩
    exact ⟨h, by rwa [cj, TaylorLogMetric.liftM, dif_pos h] at e⟩

/- English proof (translation)
Establish `hn : (n.factorial : ℂ) ≠ 0` using `by exact_mod_cast n.factorial_ne_zero`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Simplify `pair_mul h (hS.2 _ _ (pair_natCast S n.factorial))` using `[coef1, div_eq_mul_inv]`. Introduce `h`.

Simplify `pair_mul h (pair_natCast S n.factorial)` using `[coef1, hn]`.
-/
lemma pair_iteratedDeriv_iff {S : Subring (ℂ × ℂ)} (hS : IsFieldGraph S) {f g : ℂ → ℂ} {n : ℕ} :
    (iteratedDeriv n f 0, iteratedDeriv n g 0) ∈ S ↔ (coef1 f n, coef1 g n) ∈ S := by
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  constructor
  · intro h
    simpa [coef1, div_eq_mul_inv] using pair_mul h (hS.2 _ _ (pair_natCast S n.factorial))
  · intro h
    simpa [coef1, hn] using pair_mul h (pair_natCast S n.factorial)

/- English proof (translation)
Conclude with `⟨fun h => (mem_graph.1 h).1, fun h => mem_graph.2 ⟨h, rfl⟩⟩`.
-/
lemma mem_graph_val {M : IntermediateField ℚ ℂ} {a : ℂ} : (a, a) ∈ graph M M.val ↔ a ∈ M := by
  exact ⟨fun h => (mem_graph.1 h).1, fun h => mem_graph.2 ⟨h, rfl⟩⟩

/- English proof (translation)
Take `⟨a2, a3, hd, -, -, -, hex⟩` from `GlobalTheory.LatticeInvariants.invariants_dictionary L Λ h`. Establish `m2 : (g2 Λ, cj M ρ (g2 Λ)) ∈ graph M ρ` using `mem_graph_iff_cj.2 ⟨h2, rfl⟩`. Establish `m3 : (g3 Λ, cj M ρ (g3 Λ)) ∈ graph M ρ` using `mem_graph_iff_cj.2 ⟨h3, rfl⟩`. Establish `md` using `pair_sub (pair_mul m2 (pair_mul m2 m2)) (pair_mul (pair_natCast _ 27) (pair_mul m3 m3))`. Take `⟨L', b2, b3⟩` from `hex (cj M ρ (g2 Λ)) (cj M ρ (g3 Λ)) (by`.

Introduce `e`. Apply `hd` to reduce the goal to its premises. Use `((isFieldGraph_graph M ρ).1 _ _ md).2 (by push_cast; linear_combination e)` as an intermediate fact. Unfold `TaylorLogMetric.discr`. Move the coercions through the operations in `at this`.

Take the linear combination `this)`. Take `⟨c2, c3, -, -, -, huniq, -⟩` from `GlobalTheory.LatticeInvariants.invariants_dictionary L' L'.lattice.toAddSubgroup (fun _ => Iff.rfl)`. Establish `hs` using `Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ => g2 Λ' = ρ (TaylorLogMetric.liftM M (g2 Λ)) ∧ g3 Λ' = ρ (TaylorLogMetric.liftM M (g3 Λ))) ⟨L'.lattice.toAddSubgroup, c2.trans b2, c3.trans b3⟩`. Establish `e : lamConj M ρ Λ = L'.lattice.toAddSubgroup` using `huniq _ (hs.1.trans (c2.trans b2).symm) (hs.2.trans (c3.trans b3).symm)`. Use `⟨L', fun z => by rw [e]; rfl, ?_⟩` and prove the remaining obligations.

Rewrite using `[← a2, b2]`. Conclude with `m2`.
-/
lemma exists_periodPair_lamConj (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) {M : IntermediateField ℚ ℂ}
    (ρ : M →ₐ[ℚ] ℂ) (h2 : g2 Λ ∈ M) (h3 : g3 Λ ∈ M) :
    ∃ L' : PeriodPair, (∀ z, z ∈ lamConj M ρ Λ ↔ z ∈ L'.lattice) ∧ (L.g₂, L'.g₂) ∈ graph M ρ := by
  obtain ⟨a2, a3, hd, -, -, -, hex⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ h
  have m2 : (g2 Λ, cj M ρ (g2 Λ)) ∈ graph M ρ := mem_graph_iff_cj.2 ⟨h2, rfl⟩
  have m3 : (g3 Λ, cj M ρ (g3 Λ)) ∈ graph M ρ := mem_graph_iff_cj.2 ⟨h3, rfl⟩
  have md := pair_sub (pair_mul m2 (pair_mul m2 m2))
    (pair_mul (pair_natCast _ 27) (pair_mul m3 m3))
  obtain ⟨L', b2, b3⟩ := hex (cj M ρ (g2 Λ)) (cj M ρ (g3 Λ)) (by
    intro e
    apply hd
    have := ((isFieldGraph_graph M ρ).1 _ _ md).2 (by push_cast; linear_combination e)
    unfold TaylorLogMetric.discr
    push_cast at this
    linear_combination this)
  obtain ⟨c2, c3, -, -, -, huniq, -⟩ :=
    GlobalTheory.LatticeInvariants.invariants_dictionary L' L'.lattice.toAddSubgroup (fun _ => Iff.rfl)
  have hs := Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ =>
    g2 Λ' = ρ (TaylorLogMetric.liftM M (g2 Λ)) ∧ g3 Λ' = ρ (TaylorLogMetric.liftM M (g3 Λ)))
    ⟨L'.lattice.toAddSubgroup, c2.trans b2, c3.trans b3⟩
  have e : lamConj M ρ Λ = L'.lattice.toAddSubgroup :=
    huniq _ (hs.1.trans (c2.trans b2).symm) (hs.2.trans (c3.trans b3).symm)
  refine ⟨L', fun z => by rw [e]; rfl, ?_⟩
  rw [← a2, b2]
  exact m2

/- English proof (translation)
Introduce `D cc δ hc M ρ hK h2 h3 x x' m hm hmx hA hM n`. Establish `hlat` using `(GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ hc).1`. Establish `hsg` using `GlobalTheory.T.galois_taylorSeries_canonicalOddTheta_all D cc δ hc M ρ hK h2 h3`. Establish `hst` using `(GlobalTheory.ConjPoint.galStar_holds D cc δ hc M ρ hK h2 h3).2.2.2.2.2.1`. Generalize the expression as in `lamOf D cc δ = Λ at *`.

Take `⟨L, hL⟩` from `exists_periodPair hlat`. Take `⟨L', hL', hg⟩` from `exists_periodPair_lamConj hL ρ h2 h3`. Establish `hm2 : ((2 * m : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast (by omega : 2 * m ≠ 0)`. Establish `hm3 : ((2 * m ^ 2 : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast (by positivity : 2 * m ^ 2 ≠ 0)`. Unfold `Adp1 at hA`.

Take `⟨u, rfl⟩ : ∃ u, x = (2 * m : ℕ) * u` from `⟨x / (2 * m : ℕ), by field_simp⟩`. Take `⟨u', rfl⟩ : ∃ u, x' = (2 * m : ℕ) * u` from `⟨x' / (2 * m : ℕ), by field_simp⟩`. Rewrite `hA` using `[mul_div_cancel_left₀ _ hm2, mul_div_cancel_left₀ _ hm2]`. Establish `hN : ((m ^ 2 : ℕ) : ℂ) * u ∈ Λ`. Use `hmx using 1` and compare the differences between its conclusion and the goal.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hN'` using `(hst (m ^ 2) u u' hA).1 hN`. Establish `half : ∀ {Λ : AddSubgroup ℂ} {u : ℂ}, u ∈ Λ → ((2 * m : ℕ) : ℂ) * u / 2 ∈ Λ`. Introduce `Λ u hu`.

Use `Λ.nsmul_mem hu m` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Break down `hA with ⟨hu, hu'⟩ | ⟨hu, hu', p1, p2, p3, p4⟩` into its components or cases. Rewrite `hM`, the goal using `[thetaTranslate_canonicalOddTheta_of_half_mem hL (half hu)]`. Rewrite using `[thetaTranslate_canonicalOddTheta_of_half_mem hL' (half hu')]`. Conclude with `hsg hM n`. Establish `H` using `isSigmaLike_sgStar hL`.

Establish `H'` using `isSigmaLike_sgStar hL'`. Take `⟨-, -, -, -, e, -⟩` from `GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL`. Take `⟨-, -, -, -, e', -⟩` from `GlobalTheory.LatticeInvariants.invariants_dictionary L' _ hL'`. Rewrite `p1`, `p3` using `[(e u hu).1]`. Rewrite `p2`, `p4` using `[(e u hu).2]`.

Rewrite `p3` using `[(e' u' hu').1]`. Rewrite `p4` using `[(e' u' hu').2]`. Establish `hS` using `isFieldGraph_graph M ρ`. Establish `hS0` using `isFieldGraph_graph M M.val`. Establish `huL : u ∉ L.lattice` using `mt (hL u).2 hu`.

Establish `ψ` using `jetRel_divQuot hS H H' huL (mt (hL' u').2 hu') hg (mem_graph_iff_cj.2 ⟨p1, p3.symm⟩) (mem_graph_iff_cj.2 ⟨p2, p4.symm⟩)`. Establish `ψ0` using `jetRel_divQuot hS0 H H huL huL (mem_graph_val.2 (mem_graph_iff_cj.1 hg).1) (mem_graph_val.2 p1) (mem_graph_val.2 p2)`. Take `⟨k, hk⟩ : ∃ k, m ^ 2 = k + 1` from `Nat.exists_eq_succ_of_ne_zero (by positivity)`. Take `⟨K, a1, a2, a3, a4, a5⟩` from `translate_facts hL hu hk hN`. Take `⟨K', b1, -, b3, b4, b5⟩` from `translate_facts hL' hu' hk hN'`.

Establish `dG` using `differentiable_U1 (Λ := Λ) H.diff ((2 * m : ℕ) * u)`. Establish `dG'` using `differentiable_U1 (Λ := lamConj M ρ Λ) H'.diff ((2 * m : ℕ) * u')`. Establish `G0 : JetRel (graph M M.val) (U1 Λ ((2 * m : ℕ) * u) (sgStar Λ)) (U1 Λ ((2 * m : ℕ) * u) (sgStar Λ))` using `⟨dG.analyticAt 0, dG.analyticAt 0, fun n => mem_graph_val.2 (taylorCoeff_mem_iff_iteratedDeriv_mem.1 (hM n))⟩`. Establish `K0 : JetRel (graph M M.val) K K` using `JetRel.of_mul hS0 a1 a1 (ψ0 (2 * m)) (H.divQuot_ne huL (by omega)) ((G0.comp_mul dG dG (pair_natCast _ _)).congr a3 a3)`. Establish `s0 : JetRel (graph M M.val) (sgStar Λ) (sgStar Λ)` using `JetRel.of_comp_mul hS0 H.diff H.diff hm3 (pair_natCast _ _) (((K0.pow _).mul (ψ0 _)).congr a4.symm a4.symm)`.

Establish `sM : ∀ n, coef1 (sgStar Λ) n ∈ M` using `fun n => taylorCoeff_mem_iff_iteratedDeriv_mem.2 (mem_graph_val.1 (s0.2.2 n))`. Establish `s1 : JetRel (graph M ρ) (sgStar Λ) (sgStar (lamConj M ρ Λ))` using `⟨H.diff.analyticAt 0, H'.diff.analyticAt 0, fun n => (pair_iteratedDeriv_iff hS).2 (mem_graph_iff_cj.2 ⟨sM n, hsg sM n⟩)⟩`. Establish `K2 : JetRel (graph M ρ) (fun z => K z ^ (m ^ 2)) (fun z => K' z ^ (m ^ 2))` using `JetRel.of_mul hS (a1.fun_pow _) (b1.fun_pow _) (ψ (2 * m ^ 2)) (H.divQuot_ne huL (by positivity)) ((s1.comp_mul H.diff H'.diff (pair_natCast _ _)).congr a4 b4)`. Establish `K1 : JetRel (graph M ρ) K K'` using `JetRel.of_pow hS a1 b1 (by positivity) K2 (by`. Rewrite using `[a5, b5]`.

Conclude with `pair_mul (pair_sub (Subring.zero_mem _) (ψ k).zero) (hS.2 _ _ (ψ (k + 2)).zero)) a2`. Establish `G1` using `JetRel.of_comp_mul hS dG dG' hm2 (pair_natCast _ _) ((K1.mul (ψ _)).congr a3.symm b3.symm)`. Conclude with `(mem_graph_iff_cj.1 ((pair_iteratedDeriv_iff hS).1 (G1.2.2 n))).2`.
-/
theorem galois_translate_sgStar : ∀ D : D7, gal1 D := by
  intro D cc δ hc M ρ hK h2 h3 x x' m hm hmx hA hM n
  have hlat := (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ hc).1
  have hsg := GlobalTheory.T.galois_taylorSeries_canonicalOddTheta_all D cc δ hc M ρ hK h2 h3
  have hst := (GlobalTheory.ConjPoint.galStar_holds D cc δ hc M ρ hK h2 h3).2.2.2.2.2.1
  generalize lamOf D cc δ = Λ at *
  obtain ⟨L, hL⟩ := exists_periodPair hlat
  obtain ⟨L', hL', hg⟩ := exists_periodPair_lamConj hL ρ h2 h3
  have hm2 : ((2 * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * m ≠ 0)
  have hm3 : ((2 * m ^ 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : 2 * m ^ 2 ≠ 0)
  unfold Adp1 at hA
  obtain ⟨u, rfl⟩ : ∃ u, x = (2 * m : ℕ) * u := ⟨x / (2 * m : ℕ), by field_simp⟩
  obtain ⟨u', rfl⟩ : ∃ u, x' = (2 * m : ℕ) * u := ⟨x' / (2 * m : ℕ), by field_simp⟩
  rw [mul_div_cancel_left₀ _ hm2, mul_div_cancel_left₀ _ hm2] at hA
  have hN : ((m ^ 2 : ℕ) : ℂ) * u ∈ Λ := by
    convert hmx using 1
    push_cast
    ring
  have hN' := (hst (m ^ 2) u u' hA).1 hN
  have half : ∀ {Λ : AddSubgroup ℂ} {u : ℂ}, u ∈ Λ → ((2 * m : ℕ) : ℂ) * u / 2 ∈ Λ := by
    intro Λ u hu
    have := Λ.nsmul_mem hu m
    convert this using 1
    rw [nsmul_eq_mul]
    push_cast
    ring
  rcases hA with ⟨hu, hu'⟩ | ⟨hu, hu', p1, p2, p3, p4⟩
  · rw [thetaTranslate_canonicalOddTheta_of_half_mem hL (half hu)] at hM ⊢
    rw [thetaTranslate_canonicalOddTheta_of_half_mem hL' (half hu')]
    exact hsg hM n
  have H := isSigmaLike_sgStar hL
  have H' := isSigmaLike_sgStar hL'
  obtain ⟨-, -, -, -, e, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL
  obtain ⟨-, -, -, -, e', -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L' _ hL'
  rw [(e u hu).1] at p1 p3
  rw [(e u hu).2] at p2 p4
  rw [(e' u' hu').1] at p3
  rw [(e' u' hu').2] at p4
  have hS := isFieldGraph_graph M ρ
  have hS0 := isFieldGraph_graph M M.val
  have huL : u ∉ L.lattice := mt (hL u).2 hu
  have ψ := jetRel_divQuot hS H H' huL (mt (hL' u').2 hu') hg
    (mem_graph_iff_cj.2 ⟨p1, p3.symm⟩) (mem_graph_iff_cj.2 ⟨p2, p4.symm⟩)
  have ψ0 := jetRel_divQuot hS0 H H huL huL (mem_graph_val.2 (mem_graph_iff_cj.1 hg).1)
    (mem_graph_val.2 p1) (mem_graph_val.2 p2)
  obtain ⟨k, hk⟩ : ∃ k, m ^ 2 = k + 1 := Nat.exists_eq_succ_of_ne_zero (by positivity)
  obtain ⟨K, a1, a2, a3, a4, a5⟩ := translate_facts hL hu hk hN
  obtain ⟨K', b1, -, b3, b4, b5⟩ := translate_facts hL' hu' hk hN'
  have dG := differentiable_U1 (Λ := Λ) H.diff ((2 * m : ℕ) * u)
  have dG' := differentiable_U1 (Λ := lamConj M ρ Λ) H'.diff ((2 * m : ℕ) * u')

  have G0 : JetRel (graph M M.val) (U1 Λ ((2 * m : ℕ) * u) (sgStar Λ)) (U1 Λ ((2 * m : ℕ) * u) (sgStar Λ)) :=
    ⟨dG.analyticAt 0, dG.analyticAt 0, fun n => mem_graph_val.2 (taylorCoeff_mem_iff_iteratedDeriv_mem.1 (hM n))⟩
  have K0 : JetRel (graph M M.val) K K :=
    JetRel.of_mul hS0 a1 a1 (ψ0 (2 * m)) (H.divQuot_ne huL (by omega))
      ((G0.comp_mul dG dG (pair_natCast _ _)).congr a3 a3)
  have s0 : JetRel (graph M M.val) (sgStar Λ) (sgStar Λ) :=
    JetRel.of_comp_mul hS0 H.diff H.diff hm3 (pair_natCast _ _)
      (((K0.pow _).mul (ψ0 _)).congr a4.symm a4.symm)
  have sM : ∀ n, coef1 (sgStar Λ) n ∈ M := fun n => taylorCoeff_mem_iff_iteratedDeriv_mem.2 (mem_graph_val.1 (s0.2.2 n))
  have s1 : JetRel (graph M ρ) (sgStar Λ) (sgStar (lamConj M ρ Λ)) :=
    ⟨H.diff.analyticAt 0, H'.diff.analyticAt 0, fun n =>
      (pair_iteratedDeriv_iff hS).2 (mem_graph_iff_cj.2 ⟨sM n, hsg sM n⟩)⟩
  have K2 : JetRel (graph M ρ) (fun z => K z ^ (m ^ 2)) (fun z => K' z ^ (m ^ 2)) :=
    JetRel.of_mul hS (a1.fun_pow _) (b1.fun_pow _) (ψ (2 * m ^ 2)) (H.divQuot_ne huL (by positivity))
      ((s1.comp_mul H.diff H'.diff (pair_natCast _ _)).congr a4 b4)
  have K1 : JetRel (graph M ρ) K K' :=
    JetRel.of_pow hS a1 b1 (by positivity) K2 (by
      rw [a5, b5]
      exact pair_mul (pair_sub (Subring.zero_mem _) (ψ k).zero) (hS.2 _ _ (ψ (k + 2)).zero)) a2
  have G1 := JetRel.of_comp_mul hS dG dG' hm2 (pair_natCast _ _) ((K1.mul (ψ _)).congr a3.symm b3.symm)
  exact (mem_graph_iff_cj.1 ((pair_iteratedDeriv_iff hS).1 (G1.2.2 n))).2

end GlobalTheory.JetConj
