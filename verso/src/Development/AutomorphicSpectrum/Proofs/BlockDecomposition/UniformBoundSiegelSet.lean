import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeOfBound
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.BoxVolumes.ExistsMeasureLeProd
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

noncomputable section

namespace GlobalTheory.CompanionTheory.Conc.TailU

open GlobalTheory.CompanionTheory.SlabGlue An

/- English proof (translation)
Establish `hY : IsCompact (Set.univ.pi fun _ : Fin n => Set.Icc (-(n : ℝ)) n)` using `isCompact_univ_pi fun _ => isCompact_Icc`. Establish `hc : Continuous fun p : AdelicGLn.AdelicGL K n × (Fin n → ℝ) × AdelicGLn.AdelicGL K n => p.1 * tor K (x + p.2.1) * p.2.2` using `(continuous_fst.mul (JSqIntGlue.continuous_tor.comp (continuous_const.add (continuous_fst.comp continuous_snd)))).mul (continuous_snd.comp continuous_snd)`. Use `(hω.prod (hY.prod (isCompact_maxCompact (K := K) (n := n)))).image hc using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨b, hb, y, hy, k, hk, rfl⟩`. Conclude with `⟨(b, y, k), ⟨hb, fun i _ => abs_le.1 (hy i), hk⟩, rfl⟩`. Introduce and unpack `⟨⟨b, y, k⟩, ⟨hb, hy, hk⟩, rfl⟩`. Conclude with `⟨b, hb, y, fun i => abs_le.2 (hy i trivial), k, hk, rfl⟩`.
-/
theorem isCompact_box {K : Type} [Field K] [NumberField K] {n : ℕ} {ω : Set (AdelicGLn.AdelicGL K n)}
    (hω : IsCompact ω) (x : Fin n → ℝ) :
    IsCompact {g : AdelicGLn.AdelicGL K n | ∃ b ∈ ω, ∃ y : Fin n → ℝ, (∀ i, |y i| ≤ n) ∧
      ∃ k ∈ maxCompact (K := K) (n := n), g = b * tor K (x + y) * k} := by
  have hY : IsCompact (Set.univ.pi fun _ : Fin n => Set.Icc (-(n : ℝ)) n) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hc : Continuous fun p : AdelicGLn.AdelicGL K n × (Fin n → ℝ) × AdelicGLn.AdelicGL K n =>
      p.1 * tor K (x + p.2.1) * p.2.2 :=
    (continuous_fst.mul (JSqIntGlue.continuous_tor.comp
      (continuous_const.add (continuous_fst.comp continuous_snd)))).mul
      (continuous_snd.comp continuous_snd)
  convert (hω.prod (hY.prod (isCompact_maxCompact (K := K) (n := n)))).image hc using 1
  ext g
  constructor
  · rintro ⟨b, hb, y, hy, k, hk, rfl⟩
    exact ⟨(b, y, k), ⟨hb, fun i _ => abs_le.1 (hy i), hk⟩, rfl⟩
  · rintro ⟨⟨b, y, k⟩, ⟨hb, hy, hk⟩, rfl⟩
    exact ⟨b, hb, y, fun i => abs_le.2 (hy i trivial), k, hk, rfl⟩

/- English proof (translation)
Take `⟨Cv, hCv⟩` from `boxvol_holds K n μ ω hω hωB`. Take `⟨C, hC⟩` from `hB ω hω hωB (|t₀| + 2 * n) (maxCompact (K := K) (n := n) : Set _) isCompact_maxCompact`. Set `box : (Fin n → ℝ) → Set (AdelicGLn.AdelicGL K n)` to `fun x => {g | ∃ b ∈ ω, ∃ y : Fin n → ℝ, (∀ i, |y i| ≤ n) ∧ ∃ k ∈ maxCompact (K := K) (n := n), g = b * tor K (x + y) * k}`. Set `X : (Fin (n - 1) → ℕ) → Fin n → ℝ` to `fun s => part n fun j => -t₀ + s j`. Set `a : Fin (n - 1) → ℝ` to `fun j => 2 * (κ ((j : ℕ) + 1) - rho K n ((j : ℕ) + 1))`.

Set `E : ℝ` to `∑ r ∈ Finset.range n, |κ r| * (2 * n)`. Set `D : ℝ` to `(max C 0 * Real.exp E) ^ 2 * Cv * Real.exp (-t₀ * ∑ j, a j)`. Establish `ha : ∀ j, a j < 0`. Introduce `j`. Establish `hj` using `j.2`.

Use `hκ ((j : ℕ) + 1) (by omega) (by omega)` as an intermediate fact. Use `show 2 * (κ ((j : ℕ) + 1) - rho K n ((j : ℕ) + 1)) < 0`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hXs : ∀ s (j : Fin (n - 1)), sr (X s) ((j : ℕ) + 1) = -t₀ + s j` using `fun s j => sr_part _ j`. Establish `hcover : slab ω t₀ ⊆ ⋃ s, box (X s)`.

Introduce and unpack `g ⟨b, hb, x, hx, hlast, k, hk, rfl⟩`. Set `s : Fin (n - 1) → ℕ` to `fun j => ⌊sr x ((j : ℕ) + 1) + t₀⌋₊`. Use `Set.mem_iUnion.2 ⟨s, b, hb, x - X s, ?_, k, hk, ?_⟩` and prove the remaining obligations. Use `abs_y_le _ ?_ ?_` and prove the remaining obligations. Introduce `i hi`.

Establish `: X s i = 0` using `part_last _ i hi`. Simplify `hlast i hi` using `[this]`. Introduce `j`. Establish `e : sr x ((j : ℕ) + 1) = sr (X s) ((j : ℕ) + 1) + sr (x - X s) ((j : ℕ) + 1)`. Rewrite using `[← sr_add, add_sub_cancel]`.

Rewrite `e` using `[hXs]`. Establish `h0 : 0 ≤ sr x ((j : ℕ) + 1) + t₀`. Use `hx ((j : ℕ) + 1)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : ((s j : ℕ) : ℝ) ≤ sr x ((j : ℕ) + 1) + t₀` using `Nat.floor_le h0`.

Establish `h2 : sr x ((j : ℕ) + 1) + t₀ < (s j : ℕ) + 1` using `Nat.lt_floor_add_one _`. Apply the tactic sequence `constructor <;> linarith`. Rewrite using `[add_sub_cancel]`. Establish `hbox : ∀ i s, ∫⁻ g in box (X s), ‖f i g‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal D * ∏ j, ENNReal.ofReal (Real.exp (a j * s j))`. Introduce `i s`.

Set `S : ℝ` to `∑ r ∈ Finset.range n, κ r * sr (X s) r`. Set `W : ℝ` to `max C 0 * Real.exp E * Real.exp S`. Establish `hW0 : 0 ≤ W` using `by positivity`. Establish `hnorm : ∀ g ∈ box (X s), ‖f i g‖ₑ ^ 2 ≤ ENNReal.ofReal (W ^ 2)`. Introduce and unpack `g ⟨b, hb, y, hy, k, hk, rfl⟩`.

Establish `hsr : ∀ r, -(|t₀| + 2 * n) ≤ sr (X s + y) r`. Introduce `r`. Distinguish the cases in `hr : 0 < r ∧ r < n`. Rewrite using `[sr_add]`. Establish `h1 : sr (X s) r = -t₀ + s ⟨r - 1, by omega⟩`.

Use `hXs s ⟨r - 1, by omega⟩` as an intermediate fact. Simplify using `only at this`. Rewrite `this` using `[Nat.sub_add_cancel hr.1]`. Then use the resulting hypothesis. Establish `h2` using `abs_le.1 (abs_sr_le y hy r)`. Establish `h3 : (0 : ℝ) ≤ (s ⟨r - 1, by omega⟩ : ℕ)` using `Nat.cast_nonneg _`.

Establish `h4` using `le_abs_self t₀`. Rewrite using `[h1]`. Combine the linear relations using `[h2.1]`. Establish `: sr (X s + y) r = 0` using `by simp [sr, hr]`. Rewrite using `[this]`.

Establish `: (0 : ℝ) ≤ n` using `Nat.cast_nonneg _`. Use `abs_nonneg t₀` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `hC i b hb (X s + y) hsr k hk`. Establish `h2 : ∑ r ∈ Finset.range n, κ r * sr (X s + y) r ≤ S + E` using `by show _ ≤ ∑ r ∈ Finset.range n, κ r * sr (X s) r + ∑ r ∈ Finset.range n, |κ r| * (2 * n)`.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum fun r _ => ?_` and prove the remaining obligations. Rewrite using `[sr_add, mul_add]`. Establish `h3 : κ r * sr y r ≤ |κ r| * (2 * n)`. Combine the equalities or inequalities in the displayed calculation.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : ‖f i (b * tor K (X s + y) * k)‖ ≤ W`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.exp_add]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]`. Conclude with `ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h3 2)`. Establish `hmeas : Measurable fun g => ‖f i g‖ₑ ^ 2` using `((hf i).measurable.enorm).pow_const 2`. Establish `hexp : W ^ 2 * (Cv * Real.exp (-∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r)) = D * ∏ j, Real.exp (a j * s j)`. Establish `e1 : ∑ r ∈ Finset.range n, κ r * sr (X s) r = ∑ j : Fin (n - 1), κ ((j : ℕ) + 1) * (-t₀ + s j)`.

Rewrite using `[sum_range_sr]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [hXs]`. Establish `e2 : ∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r = ∑ j : Fin (n - 1), 2 * rho K n ((j : ℕ) + 1) * (-t₀ + s j)`. Rewrite using `[sum_range_sr (fun r => 2 * rho K n r)]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [hXs]`.

Establish `e3 : 2 * S - ∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r = -t₀ * ∑ j, a j + ∑ j, a j * s j` using `by show 2 * ∑ r ∈ Finset.range n, κ r * sr (X s) r - _ = _`. Rewrite using `[e1, e2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `show _ = -t₀ * (2 * (κ ((j : ℕ) + 1) - rho K n ((j : ℕ) + 1))) + (2 * (κ ((j : ℕ) + 1) - rho K n ((j : ℕ) + 1))) * s j`. Expand and normalize the polynomial expressions, which then agree.

Establish `e4 : Real.exp S ^ 2 * Real.exp (-∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r) = Real.exp (-t₀ * ∑ j, a j) * ∏ j, Real.exp (a j * s j)`. Rewrite using `[← Real.exp_sum, ← Real.exp_add, ← e3, ← Real.exp_nat_mul, ← Real.exp_add]`. Use `congr 1`. Use `show (max C 0 * Real.exp E * Real.exp S) ^ 2 * _ = (max C 0 * Real.exp E) ^ 2 * Cv * Real.exp (-t₀ * ∑ j, a j) * _`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Conclude with `hCv (X s)`. Use `_ = ENNReal.ofReal (D * ∏ j, Real.exp (a j * s j)) := by`. Rewrite using `[← ENNReal.ofReal_mul (by positivity), hexp]`. Use `_ = _ := by`.

Rewrite using `[ENNReal.ofReal_mul' (Finset.prod_nonneg fun j _ => (Real.exp_pos _).le), ENNReal.ofReal_prod_of_nonneg fun j _ => (Real.exp_pos _).le]`. Establish `hsum : ∑' s : Fin (n - 1) → ℕ, ∏ j, ENNReal.ofReal (Real.exp (a j * s j)) ≠ ⊤` using `tsum_pi_prod_ne_top (n - 1) (fun j k => ENNReal.ofReal (Real.exp (a j * k))) fun j => tsum_exp_ne_top (ha j)`. Set `G : (Fin (n - 1) → ℕ) → ℝ≥0∞` to `fun s => ENNReal.ofReal D * ∏ j, ENNReal.ofReal (Real.exp (a j * s j))`. Establish `hG : ∑' s, G s ≠ ⊤` using `by show ∑' s : Fin (n - 1) → ℕ, ENNReal.ofReal D * ∏ j, ENNReal.ofReal (Real.exp (a j * s j)) ≠ ⊤`. Rewrite using `[ENNReal.tsum_mul_left]`.

Conclude with `ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsum`. Take `⟨F, hF⟩` from `((tendsto_order.1 (ENNReal.tendsto_tsum_compl_atTop_zero hG)).2 η hη).exists`. Use `⟨⋃ s ∈ F, box (X s), F.isCompact_biUnion fun s _ => isCompact_box hω (X s), fun i => ?_⟩` and prove the remaining obligations. Establish `hsub : slab ω t₀ \ ⋃ s ∈ F, box (X s) ⊆ ⋃ s : {s // s ∉ F}, box (X s)`. Introduce and unpack `g ⟨hg, hgF⟩`.

Take `⟨s, hs⟩` from `Set.mem_iUnion.1 (hcover hg)`. Use `Set.mem_iUnion.2 ⟨⟨s, fun hsF => hgF ?_⟩, hs⟩` and prove the remaining obligations. Conclude with `Set.mem_biUnion hsF hs`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tail_lib (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (AdelicGLn.AdelicGL K n))
    [μ.IsHaarMeasure] (ι : Type) (f : ι → AdelicGLn.AdelicGL K n → ℂ) (κ : ℕ → ℝ)
    (hf : ∀ i, Continuous (f i)) (hB : UBnd f κ) (hκ : ∀ r, 0 < r → r < n → κ r < An.rho K n r)
    (ω : Set (AdelicGLn.AdelicGL K n)) (hω : IsCompact ω)
    (hωB : ω ⊆ (adelicBorel (K := K) (n := n) : Set _)) (t₀ : ℝ) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ Ω : Set (AdelicGLn.AdelicGL K n), IsCompact Ω ∧ ∀ i, ∫⁻ g in An.slab ω t₀ \ Ω, ‖f i g‖ₑ ^ 2 ∂μ ≤ η := by
  obtain ⟨Cv, hCv⟩ := boxvol_holds K n μ ω hω hωB
  obtain ⟨C, hC⟩ := hB ω hω hωB (|t₀| + 2 * n) (maxCompact (K := K) (n := n) : Set _)
    isCompact_maxCompact
  let box : (Fin n → ℝ) → Set (AdelicGLn.AdelicGL K n) := fun x =>
    {g | ∃ b ∈ ω, ∃ y : Fin n → ℝ, (∀ i, |y i| ≤ n) ∧ ∃ k ∈ maxCompact (K := K) (n := n),
      g = b * tor K (x + y) * k}
  let X : (Fin (n - 1) → ℕ) → Fin n → ℝ := fun s => part n fun j => -t₀ + s j
  let a : Fin (n - 1) → ℝ := fun j => 2 * (κ ((j : ℕ) + 1) - rho K n ((j : ℕ) + 1))
  let E : ℝ := ∑ r ∈ Finset.range n, |κ r| * (2 * n)
  let D : ℝ := (max C 0 * Real.exp E) ^ 2 * Cv * Real.exp (-t₀ * ∑ j, a j)
  have ha : ∀ j, a j < 0 := by
    intro j
    have hj := j.2
    have := hκ ((j : ℕ) + 1) (by omega) (by omega)
    show 2 * (κ ((j : ℕ) + 1) - rho K n ((j : ℕ) + 1)) < 0
    linarith
  have hXs : ∀ s (j : Fin (n - 1)), sr (X s) ((j : ℕ) + 1) = -t₀ + s j := fun s j => sr_part _ j

  have hcover : slab ω t₀ ⊆ ⋃ s, box (X s) := by
    rintro g ⟨b, hb, x, hx, hlast, k, hk, rfl⟩
    let s : Fin (n - 1) → ℕ := fun j => ⌊sr x ((j : ℕ) + 1) + t₀⌋₊
    refine Set.mem_iUnion.2 ⟨s, b, hb, x - X s, ?_, k, hk, ?_⟩
    · refine abs_y_le _ ?_ ?_
      · intro i hi
        have : X s i = 0 := part_last _ i hi
        simpa [this] using hlast i hi
      · intro j
        have e : sr x ((j : ℕ) + 1) = sr (X s) ((j : ℕ) + 1) + sr (x - X s) ((j : ℕ) + 1) := by
          rw [← sr_add, add_sub_cancel]
        rw [hXs] at e
        have h0 : 0 ≤ sr x ((j : ℕ) + 1) + t₀ := by
          have := hx ((j : ℕ) + 1)
          linarith
        have h1 : ((s j : ℕ) : ℝ) ≤ sr x ((j : ℕ) + 1) + t₀ := Nat.floor_le h0
        have h2 : sr x ((j : ℕ) + 1) + t₀ < (s j : ℕ) + 1 := Nat.lt_floor_add_one _
        constructor <;> linarith
    · rw [add_sub_cancel]

  have hbox : ∀ i s, ∫⁻ g in box (X s), ‖f i g‖ₑ ^ 2 ∂μ ≤
      ENNReal.ofReal D * ∏ j, ENNReal.ofReal (Real.exp (a j * s j)) := by
    intro i s
    let S : ℝ := ∑ r ∈ Finset.range n, κ r * sr (X s) r
    let W : ℝ := max C 0 * Real.exp E * Real.exp S
    have hW0 : 0 ≤ W := by positivity
    have hnorm : ∀ g ∈ box (X s), ‖f i g‖ₑ ^ 2 ≤ ENNReal.ofReal (W ^ 2) := by
      rintro g ⟨b, hb, y, hy, k, hk, rfl⟩
      have hsr : ∀ r, -(|t₀| + 2 * n) ≤ sr (X s + y) r := by
        intro r
        by_cases hr : 0 < r ∧ r < n
        · rw [sr_add]
          have h1 : sr (X s) r = -t₀ + s ⟨r - 1, by omega⟩ := by
            have := hXs s ⟨r - 1, by omega⟩
            simp only at this
            rwa [Nat.sub_add_cancel hr.1] at this
          have h2 := abs_le.1 (abs_sr_le y hy r)
          have h3 : (0 : ℝ) ≤ (s ⟨r - 1, by omega⟩ : ℕ) := Nat.cast_nonneg _
          have h4 := le_abs_self t₀
          rw [h1]
          linarith [h2.1]
        · have : sr (X s + y) r = 0 := by simp [sr, hr]
          rw [this]
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
          have := abs_nonneg t₀
          linarith
      have h1 := hC i b hb (X s + y) hsr k hk
      have h2 : ∑ r ∈ Finset.range n, κ r * sr (X s + y) r ≤ S + E := by
        show _ ≤ ∑ r ∈ Finset.range n, κ r * sr (X s) r + ∑ r ∈ Finset.range n, |κ r| * (2 * n)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun r _ => ?_
        rw [sr_add, mul_add]
        have h3 : κ r * sr y r ≤ |κ r| * (2 * n) := by
          calc κ r * sr y r ≤ |κ r * sr y r| := le_abs_self _
            _ = |κ r| * |sr y r| := abs_mul _ _
            _ ≤ |κ r| * (2 * n) := mul_le_mul_of_nonneg_left (abs_sr_le y hy r) (abs_nonneg _)
        linarith
      have h3 : ‖f i (b * tor K (X s + y) * k)‖ ≤ W := by
        calc _ ≤ C * Real.exp (∑ r ∈ Finset.range n, κ r * sr (X s + y) r) := h1
          _ ≤ max C 0 * Real.exp (∑ r ∈ Finset.range n, κ r * sr (X s + y) r) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
          _ ≤ max C 0 * Real.exp (S + E) :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) (le_max_right _ _)
          _ = W := by
              show _ = max C 0 * Real.exp E * Real.exp S
              rw [Real.exp_add]; ring
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h3 2)
    have hmeas : Measurable fun g => ‖f i g‖ₑ ^ 2 := ((hf i).measurable.enorm).pow_const 2
    have hexp : W ^ 2 * (Cv * Real.exp (-∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r))
        = D * ∏ j, Real.exp (a j * s j) := by
      have e1 : ∑ r ∈ Finset.range n, κ r * sr (X s) r
          = ∑ j : Fin (n - 1), κ ((j : ℕ) + 1) * (-t₀ + s j) := by
        rw [sum_range_sr]
        exact Finset.sum_congr rfl fun j _ => by rw [hXs]
      have e2 : ∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r
          = ∑ j : Fin (n - 1), 2 * rho K n ((j : ℕ) + 1) * (-t₀ + s j) := by
        rw [sum_range_sr (fun r => 2 * rho K n r)]
        exact Finset.sum_congr rfl fun j _ => by rw [hXs]
      have e3 : 2 * S - ∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r
          = -t₀ * ∑ j, a j + ∑ j, a j * s j := by
        show 2 * ∑ r ∈ Finset.range n, κ r * sr (X s) r - _ = _
        rw [e1, e2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        show _ = -t₀ * (2 * (κ ((j : ℕ) + 1) - rho K n ((j : ℕ) + 1)))
          + (2 * (κ ((j : ℕ) + 1) - rho K n ((j : ℕ) + 1))) * s j
        ring
      have e4 : Real.exp S ^ 2 * Real.exp (-∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r)
          = Real.exp (-t₀ * ∑ j, a j) * ∏ j, Real.exp (a j * s j) := by
        rw [← Real.exp_sum, ← Real.exp_add, ← e3, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
      show (max C 0 * Real.exp E * Real.exp S) ^ 2 * _ = (max C 0 * Real.exp E) ^ 2 * Cv * Real.exp (-t₀ * ∑ j, a j) * _
      calc _ = (max C 0 * Real.exp E) ^ 2 * Cv * (Real.exp S ^ 2 *
              Real.exp (-∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r)) := by ring
        _ = _ := by rw [e4]; ring
    calc ∫⁻ g in box (X s), ‖f i g‖ₑ ^ 2 ∂μ
        ≤ ENNReal.ofReal (W ^ 2) * μ (box (X s)) :=
          setLIntegral_le_of_bound μ hmeas _ _ hnorm
      _ ≤ ENNReal.ofReal (W ^ 2) * ENNReal.ofReal
            (Cv * Real.exp (-∑ r ∈ Finset.range n, 2 * rho K n r * sr (X s) r)) := by
          gcongr
          exact hCv (X s)
      _ = ENNReal.ofReal (D * ∏ j, Real.exp (a j * s j)) := by
          rw [← ENNReal.ofReal_mul (by positivity), hexp]
      _ = _ := by
          rw [ENNReal.ofReal_mul' (Finset.prod_nonneg fun j _ => (Real.exp_pos _).le),
            ENNReal.ofReal_prod_of_nonneg fun j _ => (Real.exp_pos _).le]
  have hsum : ∑' s : Fin (n - 1) → ℕ, ∏ j, ENNReal.ofReal (Real.exp (a j * s j)) ≠ ⊤ :=
    tsum_pi_prod_ne_top (n - 1) (fun j k => ENNReal.ofReal (Real.exp (a j * k)))
      fun j => tsum_exp_ne_top (ha j)
  let G : (Fin (n - 1) → ℕ) → ℝ≥0∞ := fun s =>
    ENNReal.ofReal D * ∏ j, ENNReal.ofReal (Real.exp (a j * s j))
  have hG : ∑' s, G s ≠ ⊤ := by
    show ∑' s : Fin (n - 1) → ℕ, ENNReal.ofReal D * ∏ j, ENNReal.ofReal (Real.exp (a j * s j)) ≠ ⊤
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsum
  obtain ⟨F, hF⟩ := ((tendsto_order.1 (ENNReal.tendsto_tsum_compl_atTop_zero hG)).2 η hη).exists
  refine ⟨⋃ s ∈ F, box (X s), F.isCompact_biUnion fun s _ => isCompact_box hω (X s), fun i => ?_⟩
  have hsub : slab ω t₀ \ ⋃ s ∈ F, box (X s) ⊆ ⋃ s : {s // s ∉ F}, box (X s) := by
    rintro g ⟨hg, hgF⟩
    obtain ⟨s, hs⟩ := Set.mem_iUnion.1 (hcover hg)
    refine Set.mem_iUnion.2 ⟨⟨s, fun hsF => hgF ?_⟩, hs⟩
    exact Set.mem_biUnion hsF hs
  calc ∫⁻ g in slab ω t₀ \ ⋃ s ∈ F, box (X s), ‖f i g‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ g in ⋃ s : {s // s ∉ F}, box (X s), ‖f i g‖ₑ ^ 2 ∂μ := lintegral_mono_set hsub
    _ ≤ ∑' s : {s // s ∉ F}, ∫⁻ g in box (X s), ‖f i g‖ₑ ^ 2 ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' s : {s // s ∉ F}, G s := ENNReal.tsum_le_tsum fun s => hbox i s
    _ ≤ η := hF.le

/- English proof (translation)
Introduce `K _ _ n m hb μ _ ι f κ hf hB hκ ω hω hωB t₀ η hη`. Establish `e : m = measurableSpace_adelicGL` using `hb.measurable_eq`. Substitute `e` using the available equality. Conclude with `tail_lib K n μ ι f κ hf hB hκ ω hω hωB t₀ η hη`.
-/
theorem tail_unif : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (AdelicGLn.AdelicGL K n)] [BorelSpace (AdelicGLn.AdelicGL K n)] (μ : Measure (AdelicGLn.AdelicGL K n)) [μ.IsHaarMeasure] (ι : Type)
  (f : ι → AdelicGLn.AdelicGL K n → ℂ) (κ : ℕ → ℝ), (∀ i, Continuous (f i)) → UBnd f κ → (∀ r, 0 < r → r < n → κ r < An.rho K n r) →
  ∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set _) → ∀ (t₀ : ℝ) (η : ℝ≥0∞), 0 < η →
  ∃ Ω : Set (AdelicGLn.AdelicGL K n), IsCompact Ω ∧ ∀ i, ∫⁻ g in An.slab ω t₀ \ Ω, ‖f i g‖ₑ ^ 2 ∂μ ≤ η := by
  intro K _ _ n m hb μ _ ι f κ hf hB hκ ω hω hωB t₀ η hη
  have e : m = measurableSpace_adelicGL := hb.measurable_eq
  subst e
  exact tail_lib K n μ ι f κ hf hB hκ ω hω hωB t₀ η hη

end GlobalTheory.CompanionTheory.Conc.TailU

end
