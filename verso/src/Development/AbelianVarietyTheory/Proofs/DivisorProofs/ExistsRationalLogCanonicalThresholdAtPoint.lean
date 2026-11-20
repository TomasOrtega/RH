import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalMultipleAddQWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCanonicalAtIffOfIsLogCanonicalLocalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalLocalEquationAddSmulDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTestDivisorsKltLcPencilBoundariesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

/- English proof (translation)
Introduce `hP X _ _ _ p n hp hn Δ m G D B x hm hG hD hB hk hnk`. Use `haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1`. Take `⟨mD, D₀, hmD, -, rfl⟩` from `hD`. Take `⟨m', B₀, hm', -, rfl⟩` from `hB`. Take `⟨η, hη, hG₁⟩` from `isLogCanonicalMultiple_add_qWeil X p n Δ m mD G D₀ hm hmD hG`.

Establish `hm₁ : 0 < m * mD` using `Nat.mul_pos hm hmD`. Take `⟨S, hSf, hS⟩` from `GlobalTheory.T.finite_test_divisors_klt_lc_pencil_boundaries hP X p n hp hn η (m * mD) (mD • G + m • D₀) B₀ hη hm₁`. Take `⟨g, hg⟩` from `(mD • G + m • D₀).exists_isEqn x`. Take `⟨f, hf⟩` from `B₀.exists_isEqn x`. Establish `hL` using `hG₁ x g hg`.

Establish `hBf : ∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → qWeil B₀ m' z = (E.ord f : ℚ) / m'`. Introduce `z hz E hE`. Take `⟨V, hV, hfV⟩` from `hf.exists_nhds`. Rewrite using `[qWeil, (hfV z (hz.mem_open V.isOpen hV)).mult_eq, ← hE.ord_eq]`. Establish `hm'0 : (m' : ℚ) ≠ 0` using `by exact_mod_cast hm'.ne'`.

Take `⟨a, ha⟩ : ∃ a : DivOver p → ℚ, ∀ E, a E = discrep E η (m * mD) g` from `⟨_, fun _ => rfl⟩`. Take `⟨t, ht⟩ : ∃ t : DivOver p → ℚ, ∀ E, t E = (E.ord f : ℚ) / m'` from `⟨_, fun _ => rfl⟩`. Establish `hrw (c : ℚ) (E : DivOver p) : a E - c * t E = discrep E η (m * mD) g - c / m' * E.ord f`. Rewrite using `[ha, ht]`. Expand and normalize the polynomial expressions, which then agree.

Establish `step (c : ℚ) : ∃ (m'' : ℕ) (g'' : X.functionFieldˣ), 0 < m'' ∧ IsLogEqn p (Δ + qWeil D₀ mD + c • qWeil B₀ m') η x m'' g'' ∧ ∀ E : DivOver p, discrep E η m'' g'' = a E - c * t E`. Take `⟨m'', g'', h1, h2, h3⟩` from `GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n (Δ + qWeil D₀ mD) (qWeil B₀ m') η x (m * mD) m' g f c hm₁ hm' hL hBf`. Conclude with `⟨m'', g'', h1, h2, fun E => by rw [h3, ha, ht]⟩`. Establish `hka : ∀ E : DivOver p, E.Through x → -1 < a E` using `fun E hE => by`. Rewrite using `[ha]`.

Conclude with `(hL.kltAt_iff hn hη hm₁).1 hk E hE`. Choose the witnesses or unpack the hypotheses as in `⟨E₀, hE₀S, hE₀x, hE₀⟩ : ∃ E ∈ S, E.Through x ∧ a E - 1 * t E ≤ -1 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Take `⟨m₁', g₁, hm₁', hL₁, hd₁⟩` from `step 1`.

Rewrite `hL₁` using `[one_smul]`. Use `hnk ((hL₁.kltAt_iff hn hη hm₁').2 fun E hE => ?_)` and prove the remaining obligations. Rewrite using `[hd₁, hrw]`. Use `(hS x g f (1 / m') hg hf).1 (fun E' hE' hE'x => ?_) E hE` and prove the remaining obligations. Rewrite using `[← hrw]`.

Conclude with `hc E' hE' hE'x`. Establish `hT0 : E₀ ∈ {E | E ∈ S ∧ E.Through x ∧ 0 < t E}` using `⟨hE₀S, hE₀x, by have := hka E₀ hE₀x; linarith⟩`. Take `⟨E₁, ⟨hE₁S, hE₁x, hE₁t⟩, hmin⟩` from `Set.exists_min_image {E | E ∈ S ∧ E.Through x ∧ 0 < t E} (fun E => (1 + a E) / t E) (hSf.subset fun E hE => hE.1) ⟨E₀, hT0⟩`. Establish `hE₁a` using `hka E₁ hE₁x`. Use `⟨(1 + a E₁) / t E₁, div_pos (by linarith) hE₁t, ?_, ?_⟩` and prove the remaining obligations.

Use `(hmin E₀ hT0).trans ?_` and prove the remaining obligations. Rewrite using `[div_le_one hT0.2.2]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨m'', g'', hm'', hL'', hd''⟩` from `step ((1 + a E₁) / t E₁)`. Use `⟨(lcAt_iff_of_isLogEqn X p n hp hn _ η x m'' g'' hη hm'' hL'').2 fun E hE => ?_, fun hk' => ?_⟩` and prove the remaining obligations.

Rewrite using `[hd'', hrw]`. Use `(hS x g f ((1 + a E₁) / t E₁ / m') hg hf).2 (fun E' hE' hE'x => ?_) E hE` and prove the remaining obligations. Rewrite using `[← hrw]`. Distinguish the cases in `htE : 0 < t E'`. Use `hmin E' ⟨hE', hE'x, htE⟩` as an intermediate fact.

Rewrite `this` using `[le_div_iff₀ htE]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h0 : 0 ≤ (1 + a E₁) / t E₁` using `(div_pos (by linarith) hE₁t).le`. Use `hka E' hE'x` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Use `(hL''.kltAt_iff hn hη hm'').1 hk' E₁ hE₁x` as an intermediate fact. Rewrite `this` using `[hd'', div_mul_cancel₀ _ hE₁t.ne']`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_threshold_lcAt_not_kltAt : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (D B : X → ℚ) (x : X), 0 < m → IsLogCanonicalMultiple p n Δ m G → IsQCart D → IsQCart B → KltAt p n (Δ + D) x → ¬ KltAt p n (Δ + D + B) x → ∃ c : ℚ, 0 < c ∧ c ≤ 1 ∧ LcAt p n (Δ + D + c • B) x ∧ ¬ KltAt p n (Δ + D + c • B) x := by
  intro hP X _ _ _ p n hp hn Δ m G D B x hm hG hD hB hk hnk
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  obtain ⟨mD, D₀, hmD, -, rfl⟩ := hD
  obtain ⟨m', B₀, hm', -, rfl⟩ := hB
  obtain ⟨η, hη, hG₁⟩ := isLogCanonicalMultiple_add_qWeil X p n Δ m mD G D₀ hm hmD hG
  have hm₁ : 0 < m * mD := Nat.mul_pos hm hmD
  obtain ⟨S, hSf, hS⟩ :=
    GlobalTheory.T.finite_test_divisors_klt_lc_pencil_boundaries hP X p n hp hn η (m * mD) (mD • G + m • D₀) B₀ hη hm₁
  obtain ⟨g, hg⟩ := (mD • G + m • D₀).exists_isEqn x
  obtain ⟨f, hf⟩ := B₀.exists_isEqn x
  have hL := hG₁ x g hg
  have hBf : ∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → qWeil B₀ m' z = (E.ord f : ℚ) / m' := by
    intro z hz E hE
    obtain ⟨V, hV, hfV⟩ := hf.exists_nhds
    rw [qWeil, (hfV z (hz.mem_open V.isOpen hV)).mult_eq, ← hE.ord_eq]
  have hm'0 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  obtain ⟨a, ha⟩ : ∃ a : DivOver p → ℚ, ∀ E, a E = discrep E η (m * mD) g := ⟨_, fun _ => rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : DivOver p → ℚ, ∀ E, t E = (E.ord f : ℚ) / m' := ⟨_, fun _ => rfl⟩
  have hrw (c : ℚ) (E : DivOver p) :
      a E - c * t E = discrep E η (m * mD) g - c / m' * E.ord f := by
    rw [ha, ht]; ring
  have step (c : ℚ) : ∃ (m'' : ℕ) (g'' : X.functionFieldˣ), 0 < m'' ∧
      IsLogEqn p (Δ + qWeil D₀ mD + c • qWeil B₀ m') η x m'' g'' ∧
      ∀ E : DivOver p, discrep E η m'' g'' = a E - c * t E := by
    obtain ⟨m'', g'', h1, h2, h3⟩ :=
      GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n (Δ + qWeil D₀ mD) (qWeil B₀ m') η x (m * mD) m' g f c hm₁ hm' hL hBf
    exact ⟨m'', g'', h1, h2, fun E => by rw [h3, ha, ht]⟩
  have hka : ∀ E : DivOver p, E.Through x → -1 < a E := fun E hE => by
    rw [ha]; exact (hL.kltAt_iff hn hη hm₁).1 hk E hE

  obtain ⟨E₀, hE₀S, hE₀x, hE₀⟩ : ∃ E ∈ S, E.Through x ∧ a E - 1 * t E ≤ -1 := by
    by_contra hc
    push_neg at hc
    obtain ⟨m₁', g₁, hm₁', hL₁, hd₁⟩ := step 1
    rw [one_smul] at hL₁
    refine hnk ((hL₁.kltAt_iff hn hη hm₁').2 fun E hE => ?_)
    rw [hd₁, hrw]
    refine (hS x g f (1 / m') hg hf).1 (fun E' hE' hE'x => ?_) E hE
    rw [← hrw]
    exact hc E' hE' hE'x
  have hT0 : E₀ ∈ {E | E ∈ S ∧ E.Through x ∧ 0 < t E} :=
    ⟨hE₀S, hE₀x, by have := hka E₀ hE₀x; linarith⟩
  obtain ⟨E₁, ⟨hE₁S, hE₁x, hE₁t⟩, hmin⟩ :=
    Set.exists_min_image {E | E ∈ S ∧ E.Through x ∧ 0 < t E} (fun E => (1 + a E) / t E)
      (hSf.subset fun E hE => hE.1) ⟨E₀, hT0⟩
  have hE₁a := hka E₁ hE₁x
  refine ⟨(1 + a E₁) / t E₁, div_pos (by linarith) hE₁t, ?_, ?_⟩
  · refine (hmin E₀ hT0).trans ?_
    rw [div_le_one hT0.2.2]
    linarith
  obtain ⟨m'', g'', hm'', hL'', hd''⟩ := step ((1 + a E₁) / t E₁)
  refine ⟨(lcAt_iff_of_isLogEqn X p n hp hn _ η x m'' g'' hη hm'' hL'').2 fun E hE => ?_,
    fun hk' => ?_⟩
  · rw [hd'', hrw]
    refine (hS x g f ((1 + a E₁) / t E₁ / m') hg hf).2 (fun E' hE' hE'x => ?_) E hE
    rw [← hrw]
    by_cases htE : 0 < t E'
    · have := hmin E' ⟨hE', hE'x, htE⟩
      rw [le_div_iff₀ htE] at this
      linarith
    · have h0 : 0 ≤ (1 + a E₁) / t E₁ := (div_pos (by linarith) hE₁t).le
      have := hka E' hE'x
      nlinarith
  · have := (hL''.kltAt_iff hn hη hm'').1 hk' E₁ hE₁x
    rw [hd'', div_mul_cancel₀ _ hE₁t.ne'] at this
    linarith

end GlobalTheory.PairStep
