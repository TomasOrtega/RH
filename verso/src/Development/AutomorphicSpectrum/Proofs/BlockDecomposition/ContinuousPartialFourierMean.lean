import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanTransport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

open GlobalTheory.CompanionTheory.PcB (chz_norm continuous_chz)

variable {D : D7} {n ρ p : ℕ}

/- English proof (translation)
The claim follows from `Continuous.matrix_transpose (Continuous.matrix_map continuous_id GlobalTheory.AnnihBox.continuous_cA')`.
-/
theorem continuous_adjMx : Continuous (adj : Mx D ρ p → Mx D p ρ) :=
  Continuous.matrix_transpose (Continuous.matrix_map continuous_id GlobalTheory.AnnihBox.continuous_cA')

/- English proof (translation)
Establish `h1 : Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p => (u.1 : Mx D ρ ρ)` using `continuous_subtype_val.comp continuous_fst`. Establish `h2 : Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p => u.2.1` using `continuous_fst.comp continuous_snd`. Establish `h3 : Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p => adj u.2.1` using `continuous_adjMx.comp h2`. Establish `h4 : Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p => (u.2.2 : Mx D p p)` using `continuous_subtype_val.comp (continuous_snd.comp continuous_snd)`. Establish `hbl : Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p => bl hn (u.1 : Mx D ρ ρ) u.2.1 (adj u.2.1) (u.2.2 : Mx D p p)`.

Unfold `bl`. Conclude with `(Continuous.matrix_fromBlocks h1 h2 h3 h4).matrix_submatrix _ _`. Unfold `bT`. Conclude with `hbl.subtype_mk _`.
-/
theorem continuous_bT (hn : ρ + p = n) :
    Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p => bT hn u.1 u.2.1 u.2.2 := by
  have h1 : Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p => (u.1 : Mx D ρ ρ) :=
    continuous_subtype_val.comp continuous_fst
  have h2 : Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p => u.2.1 :=
    continuous_fst.comp continuous_snd
  have h3 : Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p => adj u.2.1 :=
    continuous_adjMx.comp h2
  have h4 : Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p => (u.2.2 : Mx D p p) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have hbl : Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p =>
      bl hn (u.1 : Mx D ρ ρ) u.2.1 (adj u.2.1) (u.2.2 : Mx D p p) := by
    unfold bl
    exact (Continuous.matrix_fromBlocks h1 h2 h3 h4).matrix_submatrix _ _
  unfold bT
  exact hbl.subtype_mk _

/- English proof (translation)
Take `⟨K, hK, hcov⟩` from `GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := n)`. Take `⟨B, hB⟩` from `hK.exists_bound_of_continuousOn hΦ.continuousOn`. Use `⟨B, fun x => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ, hγx⟩` from `hcov x`. Rewrite using `[← hper γ hγ x]`.

Conclude with `hB _ hγx`.
-/
theorem exists_bound_of_isPer (Φ : hermA D n → ℂ) (hΦ : Continuous Φ) (hper : IsPer Φ) :
    ∃ B : ℝ, ∀ x, ‖Φ x‖ ≤ B := by
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := n)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hΦ.continuousOn
  refine ⟨B, fun x => ?_⟩
  obtain ⟨γ, hγ, hγx⟩ := hcov x
  rw [← hper γ hγ x]
  exact hB _ hγx

/- English proof (translation)
Take `⟨K, hK, hcov⟩` from `GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := n)`. Establish `hc : Continuous fun w : hermA D n × hermA D n => ‖Φ (w.2 + w.1) - Φ w.2‖` using `((hΦ.comp (continuous_snd.add continuous_fst)).sub (hΦ.comp continuous_snd)).norm`. Establish `hev : ∀ᶠ v in 𝓝 (0 : hermA D n), ∀ k ∈ K, ‖Φ (k + v) - Φ k‖ < ε`. Use `hK.eventually_forall_of_forall_eventually fun k _ => ?_` and prove the remaining obligations. Establish `h0 : ‖Φ (k + 0) - Φ k‖ < ε`.

Simplify using `using hε`. Conclude with `(hc.tendsto ((0 : hermA D n), k)).eventually (gt_mem_nhds h0)`. Use `filter_upwards [hev] with v hv a`. Take `⟨γ, hγ, hγa⟩` from `hcov a`. Establish `h1` using `hv _ hγa`.

Rewrite `h1` using `[add_assoc, hper γ hγ, hper γ hγ]`. Then use the resulting hypothesis.
-/
private theorem eventually_uniform_continuity_of_isPer (Φ : hermA D n → ℂ) (hΦ : Continuous Φ) (hper : IsPer Φ) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ v in 𝓝 (0 : hermA D n), ∀ a, ‖Φ (a + v) - Φ a‖ < ε := by
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := n)
  have hc : Continuous fun w : hermA D n × hermA D n => ‖Φ (w.2 + w.1) - Φ w.2‖ :=
    ((hΦ.comp (continuous_snd.add continuous_fst)).sub (hΦ.comp continuous_snd)).norm
  have hev : ∀ᶠ v in 𝓝 (0 : hermA D n), ∀ k ∈ K, ‖Φ (k + v) - Φ k‖ < ε := by
    refine hK.eventually_forall_of_forall_eventually fun k _ => ?_
    have h0 : ‖Φ (k + 0) - Φ k‖ < ε := by
      simpa using hε
    exact (hc.tendsto ((0 : hermA D n), k)).eventually (gt_mem_nhds h0)
  filter_upwards [hev] with v hv a
  obtain ⟨γ, hγ, hγa⟩ := hcov a
  have h1 := hv _ hγa
  rwa [add_assoc, hper γ hγ, hper γ hγ] at h1

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `show bl hn (z + z').1 (x + x') (GlobalTheory.MixModel.adj (x + x')) (y + y').1 = bl hn z.1 x (GlobalTheory.MixModel.adj x) y.1 + bl hn z'.1 x' (GlobalTheory.MixModel.adj x') y'.1`. Rewrite using `[GlobalTheory.CompanionTheory.PcB.blockMatrix_add', GlobalTheory.MixModel.adj_add]`. Both sides reduce to the same expression.
-/
private theorem bT_add (hn : ρ + p = n) (z z' : hermA D ρ) (x x' : Mx D ρ p) (y y' : hermA D p) :
    bT hn (z + z') (x + x') (y + y') = bT hn z x y + bT hn z' x' y' := by
  apply Subtype.ext
  show bl hn (z + z').1 (x + x') (GlobalTheory.MixModel.adj (x + x')) (y + y').1 =
    bl hn z.1 x (GlobalTheory.MixModel.adj x) y.1 + bl hn z'.1 x' (GlobalTheory.MixModel.adj x') y'.1
  rw [GlobalTheory.CompanionTheory.PcB.blockMatrix_add', GlobalTheory.MixModel.adj_add]
  rfl

/- English proof (translation)
Take `⟨B, hB⟩` from `exists_bound_of_isPer Φ hΦ hper`. Establish `hchz` using `continuous_chz hψ b₀`. Establish `hnorm` using `chz_norm hψ b₀`. Take `⟨-, -, hz1⟩` from `m.hz`. Take `⟨-, -, hμ1⟩` from `m.hμ`.

Establish `hlz : m.lz.restrict m.𝓖 Set.univ < ⊤`. Rewrite using `[Measure.restrict_apply_univ, hz1]`. Conclude with `ENNReal.one_lt_top`. Establish `hμf : m.μ.restrict m.𝓕 Set.univ < ⊤`. Rewrite using `[Measure.restrict_apply_univ, hμ1]`.

Conclude with `ENNReal.one_lt_top`. Use `haveI : IsFiniteMeasure (m.lz.restrict m.𝓖) := ⟨hlz⟩`. Use `haveI : IsFiniteMeasure (m.μ.restrict m.𝓕) := ⟨hμf⟩`. Establish `hrz : (m.lz.restrict m.𝓖 Set.univ).toReal = 1`. Rewrite using `[Measure.restrict_apply_univ, hz1, ENNReal.toReal_one]`.

Establish `hrμ : (m.μ.restrict m.𝓕 Set.univ).toReal = 1`. Rewrite using `[Measure.restrict_apply_univ, hμ1, ENNReal.toReal_one]`. Use `haveI : OpensMeasurableSpace (Mx D ρ ρ) := ⟨le_rfl⟩`. Use `haveI : OpensMeasurableSpace (Mx D ρ p) := ⟨le_rfl⟩`. Use `haveI : OpensMeasurableSpace (hermA D ρ) := Subtype.opensMeasurableSpace (hermA D ρ : Set (Mx D ρ ρ))`.

Establish `hb0 : bT hn (0 : hermA D ρ) (0 : Mx D ρ p) (0 : hermA D p) = 0`. Simplify using `using bT_add hn (0 : hermA D ρ) 0 (0 : Mx D ρ p) 0 (0 : hermA D p) 0`. Establish `hgb : ∀ (x : Mx D ρ p) (y : hermA D p) (z : hermA D ρ), ‖Φ (bT hn z x y) * conj (chz ψ b₀ z)‖ ≤ B`. Introduce `x y z`. Rewrite using `[norm_mul, Complex.norm_conj, hnorm, mul_one]`.

Conclude with `hB _`. Establish `hmz : ∀ (x : Mx D ρ p) (y : hermA D p), AEStronglyMeasurable (fun z => Φ (bT hn z x y) * conj (chz ψ b₀ z)) (m.lz.restrict m.𝓖)`. Introduce `x y`. Establish `hc : Continuous fun z : hermA D ρ => ((z, (x, y)) : hermA D ρ × Mx D ρ p × hermA D p)` using `continuous_id.prodMk continuous_const`. Conclude with `((hΦ.comp ((continuous_bT hn).comp hc)).mul (Complex.continuous_conj.comp hchz)).aestronglyMeasurable`.

Establish `hint : ∀ (x : Mx D ρ p) (y : hermA D p), Integrable (fun z => Φ (bT hn z x y) * conj (chz ψ b₀ z)) (m.lz.restrict m.𝓖)` using `fun x y => (integrable_const B).mono' (hmz x y) (ae_of_all _ fun z => hgb x y z)`. Establish `hE : ∀ (y y' : hermA D p) (x x' : Mx D ρ p) (δ : ℝ), (∀ a, ‖Φ (a + bT hn 0 (x' - x) (y' - y)) - Φ a‖ ≤ δ) → ‖(∫ z in m.𝓖, Φ (bT hn z x' y') * conj (chz ψ b₀ z) ∂m.lz) - ∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz‖ ≤ δ`. Introduce `y y' x x' δ hδ`. Establish `hpt : ∀ z : hermA D ρ, ‖Φ (bT hn z x' y') * conj (chz ψ b₀ z) - Φ (bT hn z x y) * conj (chz ψ b₀ z)‖ ≤ δ`. Introduce `z`.

Establish `hs : bT hn z x' y' = bT hn z x y + bT hn 0 (x' - x) (y' - y)`. Establish `h` using `bT_add hn z 0 x (x' - x) y (y' - y)`. Establish `h1 : x + (x' - x) = x'` using `by abel`. Establish `h2 : y + (y' - y) = y'` using `by abel`. Rewrite `h` using `[add_zero, h1, h2]`.

Conclude with `h`. Rewrite using `[← sub_mul, norm_mul, Complex.norm_conj, hnorm, mul_one, hs]`. Conclude with `hδ _`. Rewrite using `[← integral_sub (hint x' y') (hint x y)]`. Establish `h2 : ‖∫ z, (Φ (bT hn z x' y') * conj (chz ψ b₀ z) - Φ (bT hn z x y) * conj (chz ψ b₀ z)) ∂(m.lz.restrict m.𝓖)‖ ≤ δ * (m.lz.restrict m.𝓖 Set.univ).toReal` using `norm_integral_le_of_norm_le_const (ae_of_all _ hpt)`.

Rewrite `h2` using `[hrz, mul_one]`. Conclude with `h2`. Establish `hIB : ∀ (x : Mx D ρ p) (y : hermA D p), ‖∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz‖ ≤ B`. Introduce `x y`. Establish `h : ‖∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz‖ ≤ B * (m.lz.restrict m.𝓖 Set.univ).toReal` using `norm_integral_le_of_norm_le_const (ae_of_all _ fun z => hgb x y z)`.

Rewrite `h` using `[hrz, mul_one]`. Then use the resulting hypothesis. Establish `hIc : ∀ y : hermA D p, Continuous fun x : Mx D ρ p => ∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz`. Introduce `y`. Use `continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_` and prove the remaining obligations. Establish `hv : Tendsto (fun x : Mx D ρ p => bT hn (0 : hermA D ρ) (x - x₀) (y - y)) (𝓝 x₀) (𝓝 0)`.

Establish `hc : Continuous fun x : Mx D ρ p => bT hn (0 : hermA D ρ) (x - x₀) (y - y)` using `(continuous_bT hn).comp (continuous_const.prodMk ((continuous_id.sub continuous_const).prodMk continuous_const))`. Simplify `hc.tendsto x₀` using `[hb0]`. Use `filter_upwards [hv.eventually (eventually_uniform_continuity_of_isPer Φ hΦ hper (half_pos hε))] with x hx`. Rewrite using `[dist_eq_norm]`. Conclude with `(hE y y x₀ x (ε / 2) fun a => (hx a).le).trans_lt (half_lt_self hε)`.

Establish `hin : ∀ y : hermA D p, Integrable (fun x => ∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz) (m.μ.restrict m.𝓕)` using `fun y => (integrable_const B).mono' (hIc y).aestronglyMeasurable (ae_of_all _ fun x => hIB x y)`. Unfold `pm`. Use `continuous_iff_continuousAt.2 fun y₀ => Metric.tendsto_nhds.2 fun ε hε => ?_` and prove the remaining obligations. Establish `hv : Tendsto (fun y : hermA D p => bT hn (0 : hermA D ρ) (0 : Mx D ρ p) (y - y₀)) (𝓝 y₀) (𝓝 0)`. Establish `hc : Continuous fun y : hermA D p => bT hn (0 : hermA D ρ) (0 : Mx D ρ p) (y - y₀)` using `(continuous_bT hn).comp (continuous_const.prodMk (continuous_const.prodMk (continuous_id.sub continuous_const)))`.

Simplify `hc.tendsto y₀` using `[hb0]`. Use `filter_upwards [hv.eventually (eventually_uniform_continuity_of_isPer Φ hΦ hper (half_pos hε))] with y hy`. Rewrite using `[dist_eq_norm, ← integral_sub (hin y) (hin y₀)]`. Establish `hpt : ∀ x : Mx D ρ p, ‖(∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz) - ∫ z in m.𝓖, Φ (bT hn z x y₀) * conj (chz ψ b₀ z) ∂m.lz‖ ≤ ε / 2`. Introduce `x`.

Use `hE y₀ y x x (ε / 2) fun a => ?_` and prove the remaining obligations. Rewrite using `[sub_self]`. Conclude with `(hy a).le`. Establish `h2 : ‖∫ x, ((∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz) - ∫ z in m.𝓖, Φ (bT hn z x y₀) * conj (chz ψ b₀ z) ∂m.lz) ∂(m.μ.restrict m.𝓕)‖ ≤ ε / 2 * (m.μ.restrict m.𝓕 Set.univ).toReal` using `norm_integral_le_of_norm_le_const (ae_of_all _ hpt)`. Rewrite `h2` using `[hrμ, mul_one]`.

Conclude with `h2.trans_lt (half_lt_self hε)`.
-/
theorem continuous_pm (hn : ρ + p = n) (m : Meas D ρ p) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (Φ : hermA D n → ℂ) (hΦ : Continuous Φ)
    (hper : IsPer Φ) : Continuous (pm hn m ψ b₀ Φ) := by
  obtain ⟨B, hB⟩ := exists_bound_of_isPer Φ hΦ hper
  have hchz := continuous_chz hψ b₀
  have hnorm := chz_norm hψ b₀
  obtain ⟨-, -, hz1⟩ := m.hz
  obtain ⟨-, -, hμ1⟩ := m.hμ
  have hlz : m.lz.restrict m.𝓖 Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ, hz1]; exact ENNReal.one_lt_top
  have hμf : m.μ.restrict m.𝓕 Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ, hμ1]; exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (m.lz.restrict m.𝓖) := ⟨hlz⟩
  haveI : IsFiniteMeasure (m.μ.restrict m.𝓕) := ⟨hμf⟩
  have hrz : (m.lz.restrict m.𝓖 Set.univ).toReal = 1 := by
    rw [Measure.restrict_apply_univ, hz1, ENNReal.toReal_one]
  have hrμ : (m.μ.restrict m.𝓕 Set.univ).toReal = 1 := by
    rw [Measure.restrict_apply_univ, hμ1, ENNReal.toReal_one]
  haveI : OpensMeasurableSpace (Mx D ρ ρ) := ⟨le_rfl⟩
  haveI : OpensMeasurableSpace (Mx D ρ p) := ⟨le_rfl⟩
  haveI : OpensMeasurableSpace (hermA D ρ) :=
    Subtype.opensMeasurableSpace (hermA D ρ : Set (Mx D ρ ρ))
  have hb0 : bT hn (0 : hermA D ρ) (0 : Mx D ρ p) (0 : hermA D p) = 0 := by
    simpa using bT_add hn (0 : hermA D ρ) 0 (0 : Mx D ρ p) 0 (0 : hermA D p) 0
  have hgb : ∀ (x : Mx D ρ p) (y : hermA D p) (z : hermA D ρ),
      ‖Φ (bT hn z x y) * conj (chz ψ b₀ z)‖ ≤ B := by
    intro x y z
    rw [norm_mul, Complex.norm_conj, hnorm, mul_one]
    exact hB _
  have hmz : ∀ (x : Mx D ρ p) (y : hermA D p),
      AEStronglyMeasurable (fun z => Φ (bT hn z x y) * conj (chz ψ b₀ z)) (m.lz.restrict m.𝓖) := by
    intro x y
    have hc : Continuous fun z : hermA D ρ => ((z, (x, y)) : hermA D ρ × Mx D ρ p × hermA D p) :=
      continuous_id.prodMk continuous_const
    exact ((hΦ.comp ((continuous_bT hn).comp hc)).mul
      (Complex.continuous_conj.comp hchz)).aestronglyMeasurable
  have hint : ∀ (x : Mx D ρ p) (y : hermA D p),
      Integrable (fun z => Φ (bT hn z x y) * conj (chz ψ b₀ z)) (m.lz.restrict m.𝓖) := fun x y =>
    (integrable_const B).mono' (hmz x y) (ae_of_all _ fun z => hgb x y z)
  have hE : ∀ (y y' : hermA D p) (x x' : Mx D ρ p) (δ : ℝ),
      (∀ a, ‖Φ (a + bT hn 0 (x' - x) (y' - y)) - Φ a‖ ≤ δ) →
      ‖(∫ z in m.𝓖, Φ (bT hn z x' y') * conj (chz ψ b₀ z) ∂m.lz) -
        ∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz‖ ≤ δ := by
    intro y y' x x' δ hδ
    have hpt : ∀ z : hermA D ρ, ‖Φ (bT hn z x' y') * conj (chz ψ b₀ z) -
        Φ (bT hn z x y) * conj (chz ψ b₀ z)‖ ≤ δ := by
      intro z
      have hs : bT hn z x' y' = bT hn z x y + bT hn 0 (x' - x) (y' - y) := by
        have h := bT_add hn z 0 x (x' - x) y (y' - y)
        have h1 : x + (x' - x) = x' := by abel
        have h2 : y + (y' - y) = y' := by abel
        rw [add_zero, h1, h2] at h
        exact h
      rw [← sub_mul, norm_mul, Complex.norm_conj, hnorm, mul_one, hs]
      exact hδ _
    rw [← integral_sub (hint x' y') (hint x y)]
    have h2 : ‖∫ z, (Φ (bT hn z x' y') * conj (chz ψ b₀ z) -
        Φ (bT hn z x y) * conj (chz ψ b₀ z)) ∂(m.lz.restrict m.𝓖)‖ ≤
        δ * (m.lz.restrict m.𝓖 Set.univ).toReal :=
      norm_integral_le_of_norm_le_const (ae_of_all _ hpt)
    rw [hrz, mul_one] at h2
    exact h2
  have hIB : ∀ (x : Mx D ρ p) (y : hermA D p),
      ‖∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz‖ ≤ B := by
    intro x y
    have h : ‖∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz‖ ≤
        B * (m.lz.restrict m.𝓖 Set.univ).toReal :=
      norm_integral_le_of_norm_le_const (ae_of_all _ fun z => hgb x y z)
    rwa [hrz, mul_one] at h
  have hIc : ∀ y : hermA D p,
      Continuous fun x : Mx D ρ p => ∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz := by
    intro y
    refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
    have hv : Tendsto (fun x : Mx D ρ p => bT hn (0 : hermA D ρ) (x - x₀) (y - y)) (𝓝 x₀) (𝓝 0) := by
      have hc : Continuous fun x : Mx D ρ p => bT hn (0 : hermA D ρ) (x - x₀) (y - y) :=
        (continuous_bT hn).comp
          (continuous_const.prodMk ((continuous_id.sub continuous_const).prodMk continuous_const))
      simpa [hb0] using hc.tendsto x₀
    filter_upwards [hv.eventually (eventually_uniform_continuity_of_isPer Φ hΦ hper (half_pos hε))] with x hx
    rw [dist_eq_norm]
    exact (hE y y x₀ x (ε / 2) fun a => (hx a).le).trans_lt (half_lt_self hε)
  have hin : ∀ y : hermA D p, Integrable
      (fun x => ∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz) (m.μ.restrict m.𝓕) := fun y =>
    (integrable_const B).mono' (hIc y).aestronglyMeasurable (ae_of_all _ fun x => hIB x y)
  unfold pm
  refine continuous_iff_continuousAt.2 fun y₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hv : Tendsto (fun y : hermA D p => bT hn (0 : hermA D ρ) (0 : Mx D ρ p) (y - y₀)) (𝓝 y₀) (𝓝 0) := by
    have hc : Continuous fun y : hermA D p => bT hn (0 : hermA D ρ) (0 : Mx D ρ p) (y - y₀) :=
      (continuous_bT hn).comp
        (continuous_const.prodMk (continuous_const.prodMk (continuous_id.sub continuous_const)))
    simpa [hb0] using hc.tendsto y₀
  filter_upwards [hv.eventually (eventually_uniform_continuity_of_isPer Φ hΦ hper (half_pos hε))] with y hy
  rw [dist_eq_norm, ← integral_sub (hin y) (hin y₀)]
  have hpt : ∀ x : Mx D ρ p, ‖(∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz) -
      ∫ z in m.𝓖, Φ (bT hn z x y₀) * conj (chz ψ b₀ z) ∂m.lz‖ ≤ ε / 2 := by
    intro x
    refine hE y₀ y x x (ε / 2) fun a => ?_
    rw [sub_self]
    exact (hy a).le
  have h2 : ‖∫ x, ((∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz) -
      ∫ z in m.𝓖, Φ (bT hn z x y₀) * conj (chz ψ b₀ z) ∂m.lz) ∂(m.μ.restrict m.𝓕)‖ ≤
      ε / 2 * (m.μ.restrict m.𝓕 Set.univ).toReal :=
    norm_integral_le_of_norm_le_const (ae_of_all _ hpt)
  rw [hrμ, mul_one] at h2
  exact h2.trans_lt (half_lt_self hε)

end GlobalTheory.CompanionTheory.PcFc
