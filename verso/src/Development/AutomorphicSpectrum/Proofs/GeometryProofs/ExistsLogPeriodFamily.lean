import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUniformisationOfAbelianSchemeLaws
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtended
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyExponentialLocallyStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeDiscreteFreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodHolomorphicContinuationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodSetClosedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeSpansStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionSectionEqOfConnectedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPeriodsFiniteQuotientStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHodgeMatrixStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeOnPuncturedDiscStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraTail
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.Link

open GroundTheory.Heights₂.Heights.Regular

section Hol

variable {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']

/- English proof (translation)
Introduce `U f`. Establish `hset : {w ∈ W | ⊤ ≤ y (φ w) ⁻¹ᵁ U} = W ∩ φ ⁻¹' {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U}`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨h1, hm h1, h2⟩`. Introduce and unpack `⟨h1, -, h2⟩`. Conclude with `⟨h1, h2⟩`. Use `⟨by rw [hset]; exact hφ.continuousOn.isOpen_inter_preimage hW (hy U f).1, ?_⟩` and prove the remaining obligations. Use `DifferentiableOn.comp (g := fun b => valAt' (y b) U f) (t := {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U}) (hy U f).2 (hφ.mono fun w hw => hw.1) ?_` and prove the remaining obligations.

Introduce `w hw`. Conclude with `⟨hm hw.1, hw.2⟩`.
-/
theorem isHolTo_pull {X : Scheme.{0}} {B : Set V} {y : V → (Sp ℂ ⟶ X)} (hy : IsHolTo B y)
    {W : Set V'} (hW : IsOpen W) {φ : V' → V} (hφ : DifferentiableOn ℂ φ W) (hm : Set.MapsTo φ W B) :
    IsHolTo W (fun w => y (φ w)) := by
  intro U f
  have hset : {w ∈ W | ⊤ ≤ y (φ w) ⁻¹ᵁ U} = W ∩ φ ⁻¹' {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext w
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hm h1, h2⟩
    · rintro ⟨h1, -, h2⟩
      exact ⟨h1, h2⟩
  refine ⟨by rw [hset]; exact hφ.continuousOn.isOpen_inter_preimage hW (hy U f).1, ?_⟩
  refine DifferentiableOn.comp (g := fun b => valAt' (y b) U f) (t := {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U})
    (hy U f).2 (hφ.mono fun w hw => hw.1) ?_
  intro w hw
  exact ⟨hm hw.1, hw.2⟩

end Hol

section Fam

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g n : ℕ}
  {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B B' : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}

def restrict (e : FamExp G M B ψ) (hB' : IsOpen B') (h : B' ⊆ B) : FamExp G M B' ψ where
  ex := e.ex
  add b hb := e.add b (h hb)
  hol := isHolTo_pull e.hol (hB'.prod isOpen_univ) differentiableOn_id fun p hp => ⟨h hp.1, hp.2⟩
  diff b hb := e.diff b (h hb)
  log b hb := e.log b (h hb)

/- English proof (translation)
Establish `h` using `e.add b hb 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `(left_eq_mul.mp h)`.
-/
theorem ex_zero (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) : e.ex b 0 = 1 := by
  have h := e.add b hb 0 0
  rw [add_zero] at h
  exact (left_eq_mul.mp h)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using ex_zero e hb`. Consider the case `succ k ih => rw [Nat.cast_succ, add_smul, _root_.one_smul, e.add b hb, ih, pow_succ]`.
-/
theorem ex_nsmul (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (y : Fin g → ℂ) (k : ℕ) :
    e.ex b ((k : ℂ) • y) = e.ex b y ^ k := by
  induction k with
  | zero => simpa using ex_zero e hb
  | succ k ih => rw [Nat.cast_succ, add_smul, _root_.one_smul, e.add b hb, ih, pow_succ]

def perGrp (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) : AddSubgroup (Fin g → ℂ) where
  carrier := e.per b
  zero_mem' := ex_zero e hb
  add_mem' := by
    intro x y hx hy
    have hx' : e.ex b x = 1 := hx
    have hy' : e.ex b y = 1 := hy
    show e.ex b (x + y) = 1
    rw [e.add b hb, hx', hy', _root_.one_mul]
  neg_mem' := by
    intro x hx
    have hx' : e.ex b x = 1 := hx
    show e.ex b (-x) = 1
    have h := e.add b hb (-x) x
    rw [neg_add_cancel, ex_zero e hb, hx', _root_.mul_one] at h
    exact h.symm

/- English proof (translation)
Establish `h : AddSubgroup.closure (e.per b) = perGrp e hb`. Establish `h' : e.per b = ((perGrp e hb : AddSubgroup (Fin g → ℂ)) : Set (Fin g → ℂ))` using `rfl`. Rewrite using `[h', AddSubgroup.closure_eq]`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem mem_closure_per (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (p : Fin g → ℂ) :
    p ∈ AddSubgroup.closure (e.per b) ↔ p ∈ e.per b := by
  have h : AddSubgroup.closure (e.per b) = perGrp e hb := by
    have h' : e.per b = ((perGrp e hb : AddSubgroup (Fin g → ℂ)) : Set (Fin g → ℂ)) := rfl
    rw [h', AddSubgroup.closure_eq]
  rw [h]
  rfl

end Fam

section Geo

variable {n a : ℕ}

/- English proof (translation)
Establish `hρ' : (ρ : ℂ) ≠ 0` using `by exact_mod_cast hρ.ne'`. Establish `hn : ‖(ρ : ℂ) • z‖ = ρ * ‖z‖`. Rewrite using `[norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le]`. Simplify using `only [punct, Set.mem_setOf_eq, mem_ball_zero_iff, hn, Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, hρ', false_or]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨by nlinarith, h2⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨by nlinarith, h2⟩`.
-/
theorem smul_mem_punct {ρ : ℝ} (hρ : 0 < ρ) {z : Fin n → ℂ} :
    (ρ : ℂ) • z ∈ punct n a ρ ↔ z ∈ punct n a 1 := by
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hn : ‖(ρ : ℂ) • z‖ = ρ * ‖z‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  simp only [punct, Set.mem_setOf_eq, mem_ball_zero_iff, hn, Pi.smul_apply, smul_eq_mul, ne_eq,
    mul_eq_zero, hρ', false_or]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, h2⟩

/- English proof (translation)
Establish `hn : ‖(ρ : ℂ) • z‖ = ρ * ‖z‖`. Rewrite using `[norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le]`. Rewrite `hz`, the goal using `[mem_ball_zero_iff]`. Rewrite using `[hn]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem smul_mem_ball {ρ : ℝ} (hρ : 0 < ρ) {z : Fin n → ℂ} (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    (ρ : ℂ) • z ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
  have hn : ‖(ρ : ℂ) • z‖ = ρ * ‖z‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  rw [mem_ball_zero_iff] at hz ⊢
  rw [hn]
  nlinarith

/- English proof (translation)
Introduce `_ h` and use `h.1`.
-/
theorem punct_subset_ball {ρ : ℝ} : punct n a ρ ⊆ Metric.ball (0 : Fin n → ℂ) ρ := fun _ h => h.1

/- English proof (translation)
Use `⟨?_, fun i hi => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_ball_zero_iff, pi_norm_lt_iff one_pos]`. Introduce `k`. Distinguish the cases in `hk : k.val < a`. Establish `hre` using `hw.1 ⟨k.val, hk⟩`.

Establish `hcast : Fin.castLE h ⟨k.val, hk⟩ = k` using `Fin.ext rfl`. Rewrite `hre` using `[hcast]`. Simplify using `only [expCover, if_pos hk]`. Rewrite using `[Complex.norm_exp]`. Rewrite using `[← Real.exp_zero]`.

Conclude with `Real.exp_lt_exp.2 hre`. Simplify using `only [expCover, if_neg hk]`. Conclude with `hw.2 k (not_lt.mp hk)`. Simplify using `only [expCover, if_pos hi]`. Conclude with `Complex.exp_ne_zero _`.
-/
theorem expCover_mem_punct (h : a ≤ n) {w : Fin n → ℂ} (hw : w ∈ logCover h) :
    expCover a w ∈ punct n a 1 := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
    intro k
    by_cases hk : k.val < a
    · have hre := hw.1 ⟨k.val, hk⟩
      have hcast : Fin.castLE h ⟨k.val, hk⟩ = k := Fin.ext rfl
      rw [hcast] at hre
      simp only [expCover, if_pos hk]
      rw [Complex.norm_exp]
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.2 hre
    · simp only [expCover, if_neg hk]
      exact hw.2 k (not_lt.mp hk)
  · simp only [expCover, if_pos hi]
    exact Complex.exp_ne_zero _

/- English proof (translation)
Set `c : ℕ → ℝ` to `fun k => 1 / ((k : ℝ) + 1) / 2`. Establish `hc0 : ∀ k, 0 < c k` using `fun k => by positivity`. Establish `hc1 : ∀ k, c k < 1` using `fun k => by`. Establish `h1 : 1 / ((k : ℝ) + 1) ≤ 1`. Rewrite using `[div_le_one (by positivity)]`.

Establish `: (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: c k = 1 / ((k : ℝ) + 1) / 2` using `rfl`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hct : Tendsto c atTop (𝓝 0)`.

Establish `h` using `(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2`. Rewrite `h` using `[zero_div]`. Conclude with `h`. Use `⟨fun k _ => (c k : ℂ), ?_, fun k => ⟨?_, fun i _ => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[tendsto_pi_nhds]`.

Introduce `i`. Establish `h` using `(Complex.continuous_ofReal.tendsto 0).comp hct`. Rewrite `h` using `[Complex.ofReal_zero]`. Conclude with `h`. Rewrite using `[mem_ball_zero_iff, pi_norm_lt_iff one_pos]`.

Introduce `i`. Rewrite using `[Complex.norm_real, Real.norm_of_nonneg (hc0 k).le]`. Conclude with `hc1 k`. Use `show ((c k : ℝ) : ℂ) ≠ 0`. Conclude with `(hc0 k).ne'` after adjusting the coercions.
-/
theorem exists_seq_punct : ∃ u : ℕ → (Fin n → ℂ), Tendsto u atTop (𝓝 0) ∧ ∀ k, u k ∈ punct n a 1 := by
  let c : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) / 2
  have hc0 : ∀ k, 0 < c k := fun k => by positivity
  have hc1 : ∀ k, c k < 1 := fun k => by
    have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have : c k = 1 / ((k : ℝ) + 1) / 2 := rfl
    linarith
  have hct : Tendsto c atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
    rw [zero_div] at h
    exact h
  refine ⟨fun k _ => (c k : ℂ), ?_, fun k => ⟨?_, fun i _ => ?_⟩⟩
  · rw [tendsto_pi_nhds]
    intro i
    have h := (Complex.continuous_ofReal.tendsto 0).comp hct
    rw [Complex.ofReal_zero] at h
    exact h
  · rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
    intro i
    rw [Complex.norm_real, Real.norm_of_nonneg (hc0 k).le]
    exact hc1 k
  · show ((c k : ℝ) : ℂ) ≠ 0
    exact_mod_cast (hc0 k).ne'

end Geo

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Ydd5.main s c hc f hf`.
-/
theorem exists_radius_le {I : Type} (s : Finset I) (c : ℝ) (hc : 0 < c) (f : I → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ c ∧ ∀ i ∈ s, ρ ≤ f i :=
  _root_.UpperTheory.Reformulated.B.Ydd5.main s c hc f hf

/- English proof (translation)
Set `bs` to `Module.Free.chooseBasis ℤ Γ₀`. Use `choose εs ss hε hd h0 hq using fun j => hsp (bs j)`. Take `⟨ρ, hρ0, hρc, hρ⟩` from `exists_radius_le Finset.univ c hc εs hε`. Establish `hsub : ∀ j, Metric.ball (0 : Fin n → ℂ) ρ ⊆ Metric.ball 0 (εs j)` using `fun j => Metric.ball_subset_ball (hρ j (Finset.mem_univ j))`. Use `⟨ρ, hρ0, hρc, fun x b => ∑ j, ((bs.repr x j : ℤ) : ℂ) • ss j b, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `x`. Conclude with `DifferentiableOn.fun_sum fun j _ => ((hd j).mono (hsub j)).fun_const_smul _`. Introduce `x`. Establish `hx : (x : Fin g → ℂ) = ∑ j, (bs.repr x j) • ((bs j : Γ₀) : Fin g → ℂ)`. Establish `h` using `congrArg Γ₀.subtype (bs.sum_repr x)`.

Rewrite `h` using `[map_sum]`. Simplify using `only [map_smul, Submodule.subtype_apply] at h`. Conclude with `h.symm`. Simplify using `only [h0]`. Rewrite using `[hx]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Conclude with `Int.cast_smul_eq_zsmul ℂ _ _`. Introduce `x y b`. Simplify using `only [map_add, Finsupp.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]`. Introduce `x b hb`.

Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Int.cast_smul_eq_zsmul]`. Conclude with `zsmul_mem (hq j b (hsub j hb)) _`.
-/
theorem exists_additive_sections {n g : ℕ} (Γ₀ : Submodule ℤ (Fin g → ℂ)) [Module.Free ℤ Γ₀] [Module.Finite ℤ Γ₀]
    (Q : (Fin n → ℂ) → AddSubgroup (Fin g → ℂ)) (c : ℝ) (hc : 0 < c)
    (hsp : ∀ x : Γ₀, ∃ (ε : ℝ) (s : (Fin n → ℂ) → (Fin g → ℂ)), 0 < ε ∧
      DifferentiableOn ℂ s (Metric.ball 0 ε) ∧ s 0 = x ∧ ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ε, s b ∈ Q b) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ c ∧ ∃ S : Γ₀ → (Fin n → ℂ) → (Fin g → ℂ),
      (∀ x, DifferentiableOn ℂ (S x) (Metric.ball 0 ρ)) ∧ (∀ x, S x 0 = x) ∧
      (∀ x y b, S (x + y) b = S x b + S y b) ∧ ∀ x, ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, S x b ∈ Q b := by
  classical
  let bs := Module.Free.chooseBasis ℤ Γ₀
  choose εs ss hε hd h0 hq using fun j => hsp (bs j)
  obtain ⟨ρ, hρ0, hρc, hρ⟩ := exists_radius_le Finset.univ c hc εs hε
  have hsub : ∀ j, Metric.ball (0 : Fin n → ℂ) ρ ⊆ Metric.ball 0 (εs j) := fun j =>
    Metric.ball_subset_ball (hρ j (Finset.mem_univ j))
  refine ⟨ρ, hρ0, hρc, fun x b => ∑ j, ((bs.repr x j : ℤ) : ℂ) • ss j b, ?_, ?_, ?_, ?_⟩
  · intro x
    exact DifferentiableOn.fun_sum fun j _ => ((hd j).mono (hsub j)).fun_const_smul _
  · intro x
    have hx : (x : Fin g → ℂ) = ∑ j, (bs.repr x j) • ((bs j : Γ₀) : Fin g → ℂ) := by
      have h := congrArg Γ₀.subtype (bs.sum_repr x)
      rw [map_sum] at h
      simp only [map_smul, Submodule.subtype_apply] at h
      exact h.symm
    simp only [h0]
    rw [hx]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Int.cast_smul_eq_zsmul ℂ _ _
  · intro x y b
    simp only [map_add, Finsupp.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]
  · intro x b hb
    refine sum_mem fun j _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact zsmul_mem (hq j b (hsub j hb)) _

section Carry

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Establish `hhol : ∀ u : (Fin n → ℂ) → (Fin g → ℂ), DifferentiableOn ℂ u (Metric.ball 0 ρ) → IsHolTo (Metric.ball 0 ρ) (fun b => (e.ex b ((N : ℂ)⁻¹ • u b)).left)` using `fun u hu => isHolTo_pull (φ := fun b => (b, (N : ℂ)⁻¹ • u b)) e.hol Metric.isOpen_ball (differentiableOn_id.prodMk (hu.fun_const_smul _)) (fun b hb => ⟨hb, trivial⟩)`. Establish `htor : ∀ u : (Fin n → ℂ) → (Fin g → ℂ), (∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, u b ∈ e.per b) → ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, e.ex b ((N : ℂ)⁻¹ • u b) ^ N = 1` using `fun u hu b hb => by`. Establish `hNc : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Rewrite using `[← ex_nsmul e hb, smul_smul, mul_inv_cancel₀ hNc, _root_.one_smul]`. Conclude with `hu b hb`.

Conclude with `GlobalTheory.T.torsion_section_eq_of_connected (Sp R) t.G t.PP t.cub n N (Metric.ball 0 ρ) (fun b => spMap (ψ b)) (fun b => e.ex b ((N : ℂ)⁻¹ • s b)) (fun b => e.ex b ((N : ℂ)⁻¹ • s' b)) ζ 0 hN Metric.isOpen_ball (convex_ball _ _).isPreconnected (Metric.mem_ball_self hρ) (hhol s …`.
-/
theorem cubWeil_carry {R : Type} [CommRing R] {t : SAB H (Sp R)} {g n : ℕ} {M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)}
    {ρ : ℝ} {ψ : (Fin n → ℂ) → (R →+* ℂ)} (e : FamExp t.G M (Metric.ball 0 ρ) ψ) (hρ : 0 < ρ) (N : ℕ) (hN : 0 < N)
    (s s' : (Fin n → ℂ) → (Fin g → ℂ)) (hs : DifferentiableOn ℂ s (Metric.ball 0 ρ))
    (hs' : DifferentiableOn ℂ s' (Metric.ball 0 ρ)) (hp : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, s b ∈ e.per b)
    (hp' : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, s' b ∈ e.per b) (ζ : ℂˣ)
    (h0 : GlobalTheory.UU.CubWeil t.cub N (e.ex 0 ((N : ℂ)⁻¹ • s 0)) (e.ex 0 ((N : ℂ)⁻¹ • s' 0)) (unitOn ζ)) :
    ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ,
      GlobalTheory.UU.CubWeil t.cub N (e.ex b ((N : ℂ)⁻¹ • s b)) (e.ex b ((N : ℂ)⁻¹ • s' b)) (unitOn ζ) := by
  have hhol : ∀ u : (Fin n → ℂ) → (Fin g → ℂ), DifferentiableOn ℂ u (Metric.ball 0 ρ) →
      IsHolTo (Metric.ball 0 ρ) (fun b => (e.ex b ((N : ℂ)⁻¹ • u b)).left) := fun u hu =>
    isHolTo_pull (φ := fun b => (b, (N : ℂ)⁻¹ • u b)) e.hol Metric.isOpen_ball
      (differentiableOn_id.prodMk (hu.fun_const_smul _)) (fun b hb => ⟨hb, trivial⟩)
  have htor : ∀ u : (Fin n → ℂ) → (Fin g → ℂ), (∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, u b ∈ e.per b) →
      ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, e.ex b ((N : ℂ)⁻¹ • u b) ^ N = 1 := fun u hu b hb => by
    have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    rw [← ex_nsmul e hb, smul_smul, mul_inv_cancel₀ hNc, _root_.one_smul]
    exact hu b hb
  exact GlobalTheory.T.torsion_section_eq_of_connected (Sp R) t.G t.PP t.cub n N (Metric.ball 0 ρ) (fun b => spMap (ψ b))
    (fun b => e.ex b ((N : ℂ)⁻¹ • s b)) (fun b => e.ex b ((N : ℂ)⁻¹ • s' b)) ζ 0 hN Metric.isOpen_ball
    (convex_ball _ _).isPreconnected (Metric.mem_ball_self hρ) (hhol s hs) (hhol s' hs')
    (fun b hb => ⟨htor s hp b hb, htor s' hp' b hb, (Over.w _).trans (Over.w _).symm⟩) h0

end Carry

/- English proof (translation)
Establish `hNc : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Take `⟨m, hm⟩` from `Complex.exp_eq_one_iff.1 (by simpa using h.symm)`. Establish `hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `Complex.two_pi_I_ne_zero`. Rewrite `hm` using `[div_eq_iff hNc]`. Establish `h4 : (2 * Real.pi * Complex.I : ℂ) * ((r : ℂ) + N * m) = 0` using `by linear_combination -hm`.

Establish `h5 : (r : ℂ) + N * m = 0` using `(mul_eq_zero.1 h4).resolve_left hc`. Use `⟨-m, ?_⟩` and prove the remaining obligations. Establish `h6 : (r : ℂ) = ((N * (-m : ℤ) : ℝ) : ℂ)`. Use `push_cast`. Take the linear combination `h5`.

Conclude with `h6` after adjusting the coercions.
-/
theorem exists_int_of_exp_eq_one {r : ℝ} {N : ℕ} (hN : 0 < N)
    (h : ((1 : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ) / N)) :
    ∃ k : ℤ, r = N * k := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 (by simpa using h.symm)
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  rw [div_eq_iff hNc] at hm
  have h4 : (2 * Real.pi * Complex.I : ℂ) * ((r : ℂ) + N * m) = 0 := by linear_combination -hm
  have h5 : (r : ℂ) + N * m = 0 := (mul_eq_zero.1 h4).resolve_left hc
  refine ⟨-m, ?_⟩
  have h6 : (r : ℂ) = ((N * (-m : ℤ) : ℝ) : ℂ) := by
    push_cast
    linear_combination h5
  exact_mod_cast h6

/- English proof (translation)
Introduce `E _ _ _ H D l Xo σ n a C hpq hσ`. Take `⟨g', ty, hty⟩` from `GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q`. Take `⟨FU⟩` from `GlobalTheory.familyUnif_of_laws GlobalTheory.abelianSchemeLaws_all.1 E H D l Xo σ g' ty hpq hσ hty`. Establish `hsemi : IsSemiAbelian C.t.G` using `C.t.semi`. Take `⟨ε, hε, hεB, ⟨e₀⟩⟩` from `GlobalTheory.T.exists_family_exponential_locally C.R C.t.G C.g n C.M (Metric.ball 0 1) C.ψ hsemi.smooth C.hol 0 (Metric.mem_ball_self one_pos)`.

Establish `h0ε : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ε` using `Metric.mem_ball_self hε`. Take `⟨Γ₀, hΓ₀, -, hfin, hfree⟩` from `GlobalTheory.T.period_lattice_discrete_free C.R C.t.G C.g n C.M _ C.ψ e₀ 0 h0ε`. Set `Q : (Fin n → ℂ) → AddSubgroup (Fin C.g → ℂ)` to `fun b => AddSubgroup.closure (e₀.per b)`. Establish `hQ : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ε, ∀ p, p ∈ Q b ↔ p ∈ e₀.per b` using `fun b hb p => mem_closure_per e₀ hb p`. Establish `hsp : ∀ x : Γ₀, ∃ (ε' : ℝ) (s : (Fin n → ℂ) → (Fin C.g → ℂ)), 0 < ε' ∧ DifferentiableOn ℂ s (Metric.ball 0 ε') ∧ s 0 = x ∧ ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ε', s b ∈ Q b`.

Introduce `x`. Take `⟨ε', s, h0, hsub, hd, hs0, hs⟩` from `GlobalTheory.T.period_holomorphic_continuation C.R C.t.G C.g n C.M _ C.ψ e₀ Metric.isOpen_ball 0 h0ε x (by rw [← hΓ₀]; exact x.2)`. Conclude with `⟨ε', s, h0, hd, hs0, fun b hb => (hQ b (hsub hb) _).2 (hs b hb)⟩`. Take `⟨ρ, hρ0, hρc, S, hSd, hS0, hSa, hSq⟩` from `exists_additive_sections Γ₀ Q (min 1 ε) (lt_min one_pos hε) hsp`. Establish `hρ1 : ρ ≤ 1` using `hρc.trans (min_le_left _ _)`.

Establish `hball : Metric.ball (0 : Fin n → ℂ) ρ ⊆ Metric.ball 0 ε` using `Metric.ball_subset_ball (hρc.trans (min_le_right _ _))`. Establish `hball1 : Metric.ball (0 : Fin n → ℂ) ρ ⊆ Metric.ball 0 1` using `Metric.ball_subset_ball hρ1`. Establish `h0ρ : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ρ` using `Metric.mem_ball_self hρ0`. Set `e : FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ` to `restrict e₀ Metric.isOpen_ball hball`. Establish `hQ' : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ p, p ∈ Q b ↔ p ∈ e.per b` using `fun b hb p => hQ b (hball hb) p`.

Establish `hΓ₀' : (Γ₀ : Set (Fin C.g → ℂ)) = e.per 0` using `hΓ₀`. Establish `hSp : ∀ x, ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, S x b ∈ e.per b` using `fun x b hb => (hQ' b hb _).1 (hSq x b hb)`. Take `⟨i, Hf, hrank, hopen, hloc⟩` from `GlobalTheory.T.boundary_chart_hodge_matrix E H D l Xo σ n a C g' ty FU ρ e hρ0 hρ1`. Take `⟨hfreeL, hfinL, -⟩` from `GlobalTheory.Coisotropic.lattice_rank E H (FU.Di i)`. Establish `hU : ∀ z ∈ punct n a 1, (ρ : ℂ) • z ∈ punct n a ρ` using `fun z hz => (smul_mem_punct hρ0).2 hz`.

Establish `hsm : Differentiable ℂ (fun z : Fin n → ℂ => (ρ : ℂ) • z)` using `differentiable_id.fun_const_smul _`. Establish `key : ∃ L : Flat.LogPeriods n a C.g (FU.Di i).La, L.H = (fun z => Hf ((ρ : ℂ) • z)) ∧ ∀ w ∈ logCover L.a_le, (L.P w).range = Q ((ρ : ℂ) • expCover a w)`. Use `GlobalTheory.T.period_lattice_on_punctured_disc n a C.g C.a_le (FU.Di i).La (FU.Di i).EF (fun z => Q ((ρ : ℂ) • z)) (fun z => Hf ((ρ : ℂ) • z)) (punct n a 1) Γ₀ (fun x z => S x ((ρ : ℂ) • z)) rfl hrank (FU.Di i).alt (FU.Di i).unimod ?_ ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Conclude with `fun z hz => ⟨(hopen _ (hU z hz)).1, fun x hx => (hopen _ (hU z hz)).2.1 x hx⟩`. Introduce `z₀ hz₀`.

Take `⟨N, hNo, hzN, hNp, P, hPd, hP⟩` from `hloc _ (hU z₀ hz₀)`. Use `⟨(fun z => (ρ : ℂ) • z) ⁻¹' N, hNo.preimage hsm.continuous, hzN, fun z hz => (smul_mem_punct hρ0).1 (hNp hz), fun z => P ((ρ : ℂ) • z), fun x => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Conclude with `(hPd x).comp hsm.differentiableOn (fun z hz => hz)`. Take `⟨h1, h2, h3⟩` from `hP _ hz`. Use `⟨h1, ?_, h3⟩` and prove the remaining obligations.

Use extensionality with `p`. Establish `h4 : p ∈ (P ((ρ : ℂ) • z)).range ↔ p ∈ e.per ((ρ : ℂ) • z)`. Rewrite using `[← SetLike.mem_coe, h2]`. Rewrite using `[h4]`. Conclude with `(hQ' _ (punct_subset_ball (hNp hz)) p).symm`.

Introduce `x`. Use `⟨(hSd x).comp hsm.differentiableOn (fun z hz => smul_mem_ball hρ0 hz), ?_, fun z hz => hSq x _ (smul_mem_ball hρ0 hz.1)⟩` and prove the remaining obligations. Use `show S x ((ρ : ℂ) • 0) = x`. Rewrite using `[smul_zero]`. Conclude with `hS0 x`.

Conclude with `fun x y z => hSa x y _`. Introduce `s hs hsU`. Take `⟨u, hu, huU⟩` from `exists_seq_punct (n := n) (a := a)`. Establish `hρc' : (ρ : ℂ) ≠ 0` using `by exact_mod_cast hρ0.ne'`. Establish `htend : Tendsto (fun k => (ρ : ℂ) • u k) atTop (𝓝 0)`.

Establish `h` using `hu.const_smul (ρ : ℂ)`. Rewrite `h` using `[smul_zero]`. Then use the resulting hypothesis. Establish `hcl` using `GlobalTheory.T.period_set_closed C.R C.t.G C.g n C.M (Metric.ball 0 ρ) C.ψ e hsemi.separated ⟨Metric.isOpen_ball, fun r => (C.hol.2 r).mono hball1⟩ 0 h0ρ (fun b => s ((ρ : ℂ)⁻¹ • b)) (ContinuousAt.comp_of_eq hs (continuous_const_smul _).continuousAt (smul_zero _)) (htend.frequent …`. Use `⟨punct_subset_ball (hU _ (huU k)), ?_⟩` and prove the remaining obligations. Use `show s ((ρ : ℂ)⁻¹ • (ρ : ℂ) • u k) ∈ e.per ((ρ : ℂ) • u k)`.

Rewrite using `[smul_smul, inv_mul_cancel₀ hρc', _root_.one_smul]`. Conclude with `(hQ' _ (punct_subset_ball (hU _ (huU k))) _).1 (hsU _ (huU k)))))`. Establish `h0 : s 0 ∈ e.per 0` using `by simpa using hcl`. Rewrite `h0` using `[← hΓ₀']`. Conclude with `h0`.

Rewrite using `[hΓ₀']`. Conclude with `GlobalTheory.T.period_lattice_spans C.R C.t.G C.g n C.M _ C.ψ e hsemi 0 h0ρ`. Introduce `N hN`. Take `⟨T, hT, hTw⟩` from `GlobalTheory.T.torsion_periods_finite_quotient E H C.R C.t C.g n C.M (Metric.ball 0 ρ) C.ψ e C.dim 0 h0ρ Γ₀ hΓ₀' N hN`. Use `⟨T, hT, fun x y hx z hz => ?_⟩` and prove the remaining obligations.

Establish `hb` using `hU z hz`. Establish `hbm` using `punct_subset_ball hb`. Establish `hc` using `cubWeil_carry e hρ0 N hN (S x) (S y) (hSd x) (hSd y) (hSp x) (hSp y) 1 (by`. Rewrite using `[hS0 x, hS0 y]`. Establish `h1 : unitOn (1 : ℂˣ) = 1` using `map_one _`.

Rewrite using `[h1]`. Conclude with `hTw x y hx) _ hbm`. Establish `hz'` using `(hopen _ hb).2.2.2 N 1 hN _ (hSp x _ hbm) _ (hSp y _ hbm) hc`. Conclude with `exists_int_of_exp_eq_one hN hz'`. Take `⟨L, hLH, hLr⟩` from `key`.

Use `⟨ρ, (FU.Di i).La, inferInstance, L, e, hρ0, hρ1, fun w hw => ?_⟩` and prove the remaining obligations. Establish `hz1` using `expCover_mem_punct L.a_le hw`. Establish `hzρ` using `hU _ hz1`. Establish `hzb` using `punct_subset_ball hzρ`. Establish `hmem : ∀ x, L.P w x ∈ e.per ((ρ : ℂ) • expCover a w)` using `fun x => by`.

Establish `h : L.P w x ∈ (L.P w).range` using `⟨x, rfl⟩`. Rewrite `h` using `[hLr w hw]`. Conclude with `(hQ' _ hzb _).1 h`. Use `⟨fun p => ⟨fun hp => ?_, ?_⟩, fun N ζ x x' hN hc => ?_⟩` and prove the remaining obligations. Establish `h : p ∈ (L.P w).range`.

Rewrite using `[hLr w hw]`. Conclude with `(hQ' _ hzb _).2 hp`. Conclude with `h`. Introduce and unpack `⟨x, rfl⟩`. Conclude with `hmem x`.

Establish `h1` using `(hopen _ hzρ).2.2.2 N ζ hN _ (hmem x) _ (hmem x') hc`. Establish `h2` using `L.im w hw x x'`. Rewrite `h2` using `[hLH]`. Establish `h3 : ∀ r : ℝ, r = ((L.E x x' : ℤ) : ℝ) → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ) / N) → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((L.E x x' : ℤ) : ℂ) / N)` using `fun r hr h => by`. Rewrite using `[h, hr]`.

Use `push_cast`. Both sides reduce to the same expression. Conclude with `h3 _ h2 h1`.
-/
theorem exists_logPeriods_famExp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → ∃ (ρ : ℝ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a C.g Λ) (e : Flat.FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ), 0 < ρ ∧ ρ ≤ 1 ∧ (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, (∀ p, p ∈ e.per ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ↔ ∃ x, L.P w x = p) ∧ ∀ (N : ℕ) (ζ : ℂˣ) (x x' : Λ), 0 < N → GlobalTheory.UU.CubWeil C.t.cub N (e.ex ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ((N : ℂ)⁻¹ • L.P w x)) (e.ex ((ρ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a w) ((N : ℂ)⁻¹ • L.P w x')) (unitOn ζ) → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((L.E x x' : ℤ) : ℂ) / N)) := by
  intro E _ _ _ H D l Xo σ n a C hpq hσ
  obtain ⟨g', ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  obtain ⟨FU⟩ := GlobalTheory.familyUnif_of_laws GlobalTheory.abelianSchemeLaws_all.1 E H D l Xo σ g' ty hpq hσ hty
  have hsemi : IsSemiAbelian C.t.G := C.t.semi
  obtain ⟨ε, hε, hεB, ⟨e₀⟩⟩ := GlobalTheory.T.exists_family_exponential_locally C.R C.t.G C.g n C.M (Metric.ball 0 1) C.ψ hsemi.smooth C.hol 0
    (Metric.mem_ball_self one_pos)
  have h0ε : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ε := Metric.mem_ball_self hε
  obtain ⟨Γ₀, hΓ₀, -, hfin, hfree⟩ := GlobalTheory.T.period_lattice_discrete_free C.R C.t.G C.g n C.M _ C.ψ e₀ 0 h0ε
  let Q : (Fin n → ℂ) → AddSubgroup (Fin C.g → ℂ) := fun b => AddSubgroup.closure (e₀.per b)
  have hQ : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ε, ∀ p, p ∈ Q b ↔ p ∈ e₀.per b := fun b hb p =>
    mem_closure_per e₀ hb p
  have hsp : ∀ x : Γ₀, ∃ (ε' : ℝ) (s : (Fin n → ℂ) → (Fin C.g → ℂ)), 0 < ε' ∧
      DifferentiableOn ℂ s (Metric.ball 0 ε') ∧ s 0 = x ∧ ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ε', s b ∈ Q b := by
    intro x
    obtain ⟨ε', s, h0, hsub, hd, hs0, hs⟩ := GlobalTheory.T.period_holomorphic_continuation C.R C.t.G C.g n C.M _ C.ψ e₀ Metric.isOpen_ball 0 h0ε x
      (by rw [← hΓ₀]; exact x.2)
    exact ⟨ε', s, h0, hd, hs0, fun b hb => (hQ b (hsub hb) _).2 (hs b hb)⟩
  obtain ⟨ρ, hρ0, hρc, S, hSd, hS0, hSa, hSq⟩ := exists_additive_sections Γ₀ Q (min 1 ε) (lt_min one_pos hε) hsp
  have hρ1 : ρ ≤ 1 := hρc.trans (min_le_left _ _)
  have hball : Metric.ball (0 : Fin n → ℂ) ρ ⊆ Metric.ball 0 ε :=
    Metric.ball_subset_ball (hρc.trans (min_le_right _ _))
  have hball1 : Metric.ball (0 : Fin n → ℂ) ρ ⊆ Metric.ball 0 1 := Metric.ball_subset_ball hρ1
  have h0ρ : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ρ := Metric.mem_ball_self hρ0
  let e : FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ := restrict e₀ Metric.isOpen_ball hball
  have hQ' : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ p, p ∈ Q b ↔ p ∈ e.per b := fun b hb p => hQ b (hball hb) p
  have hΓ₀' : (Γ₀ : Set (Fin C.g → ℂ)) = e.per 0 := hΓ₀
  have hSp : ∀ x, ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, S x b ∈ e.per b := fun x b hb =>
    (hQ' b hb _).1 (hSq x b hb)
  obtain ⟨i, Hf, hrank, hopen, hloc⟩ := GlobalTheory.T.boundary_chart_hodge_matrix E H D l Xo σ n a C g' ty FU ρ e hρ0 hρ1
  obtain ⟨hfreeL, hfinL, -⟩ := GlobalTheory.Coisotropic.lattice_rank E H (FU.Di i)
  have hU : ∀ z ∈ punct n a 1, (ρ : ℂ) • z ∈ punct n a ρ := fun z hz => (smul_mem_punct hρ0).2 hz
  have hsm : Differentiable ℂ (fun z : Fin n → ℂ => (ρ : ℂ) • z) := differentiable_id.fun_const_smul _
  have key : ∃ L : Flat.LogPeriods n a C.g (FU.Di i).La, L.H = (fun z => Hf ((ρ : ℂ) • z)) ∧
      ∀ w ∈ logCover L.a_le, (L.P w).range = Q ((ρ : ℂ) • expCover a w) := by
    refine GlobalTheory.T.period_lattice_on_punctured_disc n a C.g C.a_le (FU.Di i).La (FU.Di i).EF (fun z => Q ((ρ : ℂ) • z))
      (fun z => Hf ((ρ : ℂ) • z)) (punct n a 1) Γ₀ (fun x z => S x ((ρ : ℂ) • z)) rfl hrank (FU.Di i).alt
      (FU.Di i).unimod ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact fun z hz => ⟨(hopen _ (hU z hz)).1, fun x hx => (hopen _ (hU z hz)).2.1 x hx⟩
    · intro z₀ hz₀
      obtain ⟨N, hNo, hzN, hNp, P, hPd, hP⟩ := hloc _ (hU z₀ hz₀)
      refine ⟨(fun z => (ρ : ℂ) • z) ⁻¹' N, hNo.preimage hsm.continuous, hzN,
        fun z hz => (smul_mem_punct hρ0).1 (hNp hz), fun z => P ((ρ : ℂ) • z), fun x => ?_, fun z hz => ?_⟩
      · exact (hPd x).comp hsm.differentiableOn (fun z hz => hz)
      · obtain ⟨h1, h2, h3⟩ := hP _ hz
        refine ⟨h1, ?_, h3⟩
        ext p
        have h4 : p ∈ (P ((ρ : ℂ) • z)).range ↔ p ∈ e.per ((ρ : ℂ) • z) := by
          rw [← SetLike.mem_coe, h2]
        rw [h4]
        exact (hQ' _ (punct_subset_ball (hNp hz)) p).symm
    · intro x
      refine ⟨(hSd x).comp hsm.differentiableOn (fun z hz => smul_mem_ball hρ0 hz), ?_,
        fun z hz => hSq x _ (smul_mem_ball hρ0 hz.1)⟩
      show S x ((ρ : ℂ) • 0) = x
      rw [smul_zero]
      exact hS0 x
    · exact fun x y z => hSa x y _
    · intro s hs hsU
      obtain ⟨u, hu, huU⟩ := exists_seq_punct (n := n) (a := a)
      have hρc' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
      have htend : Tendsto (fun k => (ρ : ℂ) • u k) atTop (𝓝 0) := by
        have h := hu.const_smul (ρ : ℂ)
        rwa [smul_zero] at h
      have hcl := GlobalTheory.T.period_set_closed C.R C.t.G C.g n C.M (Metric.ball 0 ρ) C.ψ e hsemi.separated
        ⟨Metric.isOpen_ball, fun r => (C.hol.2 r).mono hball1⟩ 0 h0ρ (fun b => s ((ρ : ℂ)⁻¹ • b))
        (ContinuousAt.comp_of_eq hs (continuous_const_smul _).continuousAt (smul_zero _))
        (htend.frequently (Eventually.frequently (Eventually.of_forall fun k => by
          refine ⟨punct_subset_ball (hU _ (huU k)), ?_⟩
          show s ((ρ : ℂ)⁻¹ • (ρ : ℂ) • u k) ∈ e.per ((ρ : ℂ) • u k)
          rw [smul_smul, inv_mul_cancel₀ hρc', _root_.one_smul]
          exact (hQ' _ (punct_subset_ball (hU _ (huU k))) _).1 (hsU _ (huU k)))))
      have h0 : s 0 ∈ e.per 0 := by simpa using hcl
      rw [← hΓ₀'] at h0
      exact h0
    · rw [hΓ₀']
      exact GlobalTheory.T.period_lattice_spans C.R C.t.G C.g n C.M _ C.ψ e hsemi 0 h0ρ
    · intro N hN
      obtain ⟨T, hT, hTw⟩ := GlobalTheory.T.torsion_periods_finite_quotient E H C.R C.t C.g n C.M (Metric.ball 0 ρ) C.ψ e C.dim 0 h0ρ Γ₀ hΓ₀' N hN
      refine ⟨T, hT, fun x y hx z hz => ?_⟩
      have hb := hU z hz
      have hbm := punct_subset_ball hb
      have hc := cubWeil_carry e hρ0 N hN (S x) (S y) (hSd x) (hSd y) (hSp x) (hSp y) 1 (by
        rw [hS0 x, hS0 y]
        have h1 : unitOn (1 : ℂˣ) = 1 := map_one _
        rw [h1]
        exact hTw x y hx) _ hbm
      have hz' := (hopen _ hb).2.2.2 N 1 hN _ (hSp x _ hbm) _ (hSp y _ hbm) hc
      exact exists_int_of_exp_eq_one hN hz'
  obtain ⟨L, hLH, hLr⟩ := key
  refine ⟨ρ, (FU.Di i).La, inferInstance, L, e, hρ0, hρ1, fun w hw => ?_⟩
  have hz1 := expCover_mem_punct L.a_le hw
  have hzρ := hU _ hz1
  have hzb := punct_subset_ball hzρ
  have hmem : ∀ x, L.P w x ∈ e.per ((ρ : ℂ) • expCover a w) := fun x => by
    have h : L.P w x ∈ (L.P w).range := ⟨x, rfl⟩
    rw [hLr w hw] at h
    exact (hQ' _ hzb _).1 h
  refine ⟨fun p => ⟨fun hp => ?_, ?_⟩, fun N ζ x x' hN hc => ?_⟩
  · have h : p ∈ (L.P w).range := by
      rw [hLr w hw]
      exact (hQ' _ hzb _).2 hp
    exact h
  · rintro ⟨x, rfl⟩
    exact hmem x
  · have h1 := (hopen _ hzρ).2.2.2 N ζ hN _ (hmem x) _ (hmem x') hc
    have h2 := L.im w hw x x'
    rw [hLH] at h2
    have h3 : ∀ r : ℝ, r = ((L.E x x' : ℤ) : ℝ) →
        (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ) / N) →
        (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((L.E x x' : ℤ) : ℂ) / N) := fun r hr h => by
      rw [h, hr]
      push_cast
      rfl
    exact h3 _ h2 h1

end GlobalTheory.CompanionTheory.Ar.Flat.Link
