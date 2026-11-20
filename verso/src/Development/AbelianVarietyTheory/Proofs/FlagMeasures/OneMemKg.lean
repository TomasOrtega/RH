import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientIntegrableMajorant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletedTensorDiscreteSeriesIrreducibleFormalDe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountedVectorIsCuspFormStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.Dec.CuspAll

/- English proof (translation)
Use `⟨(Formalism.UG.stabGL I.Lf).one_mem, fun y _ => ⟨0, I.Lf.zero_mem, ?_⟩⟩` and prove the remaining obligations. Establish `: I.fmat 1 = 1` using `rfl`. Simplify using `[this]`.
-/
theorem one_mem_Kg (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  refine ⟨(Formalism.UG.stabGL I.Lf).one_mem, fun y _ => ⟨0, I.Lf.zero_mem, ?_⟩⟩
  have : I.fmat 1 = 1 := rfl
  simp [this]

/- English proof (translation)
Introduce `k hk`. Take `⟨hT2, -, hsc, -⟩` from `GlobalTheory.CongTop.adelic_topology B.I`. Take `⟨R1, Rm, Rn, -⟩` from `GlobalTheory.RightRegFund.rightReg_unitary_continuous B`. Take `⟨-, -, -, -, -, hinv, -⟩` from `B.e_adm`. Take `⟨-, hT⟩` from `B.Re_spec`.

Establish `p1 : (fun g : B.I.Gf => B.R (1, g)) 1 = 1` using `R1`. Establish `pm : ∀ a b : B.I.Gf, B.R (1, a * b) = B.R (1, a) * B.R (1, b)`. Introduce `a b`. Rewrite using `[← Rm]`. Simplify using the standard rewrite rules.

Establish `pn : ∀ (g : B.I.Gf) v, ‖B.R (1, g) v‖ = ‖v‖` using `fun g v => Rn _ v`. Conclude with `GlobalTheory.IdemProj.op_fixed B.μf (fun g => B.R (1, g)) p1 pm pn B.e B.Re hT k (fun x => by simpa using hinv x k hk 1 (one_mem_Kg B.I B.g))`.
-/
theorem re_fixed (B : RowsAut) : ∀ k ∈ B.I.Kg B.g, (B.R (1, k)).comp B.Re = B.Re := by
  intro k hk
  obtain ⟨hT2, -, hsc, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨R1, Rm, Rn, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  obtain ⟨-, -, -, -, -, hinv, -⟩ := B.e_adm
  obtain ⟨-, hT⟩ := B.Re_spec
  have p1 : (fun g : B.I.Gf => B.R (1, g)) 1 = 1 := R1
  have pm : ∀ a b : B.I.Gf, B.R (1, a * b) = B.R (1, a) * B.R (1, b) := by
    intro a b; rw [← Rm]; simp
  have pn : ∀ (g : B.I.Gf) v, ‖B.R (1, g) v‖ = ‖v‖ := fun g v => Rn _ v
  exact GlobalTheory.IdemProj.op_fixed B.μf (fun g => B.R (1, g)) p1 pm pn B.e B.Re hT k
    (fun x => by simpa using hinv x k hk 1 (one_mem_Kg B.I B.g))

/- English proof (translation)
Take `⟨hc, hm, hi⟩` from `GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl`. Establish `h0` using `hi 0 le_rfl (fun v => by`. Break down `Nat.eq_zero_or_pos (rkR (B.I.ε v)) with hq | hq` into its components or cases. Conclude with `Or.inl hq`. Use `right`.

Establish `hle : rkR (B.I.ε v) ≤ B.I.n`. Unfold `rkR`. Use `(min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))` and prove the remaining obligations. Establish `h1 : (0 : ℝ) < rkR (B.I.ε v)` using `by exact_mod_cast hq`. Establish `h2 : ((rkR (B.I.ε v) : ℕ) : ℝ) ≤ B.I.n` using `by exact_mod_cast hle`.

Establish `h3` using `Real.sqrt_pos.2 h1`. Establish `h4` using `hb v`. Establish `h5 : (0 : ℝ) < B.I.n` using `h1.trans_le h2`. Establish `h6 : (B.I.n : ℝ) * rkR (B.I.ε v) ≤ (B.I.n : ℝ) ^ 2` using `by nlinarith`. Establish `h7 : 0 < (B.I.n : ℝ) ^ 2 * Real.sqrt (rkR (B.I.ε v))` using `by positivity`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right h6 h3.le])`. Simplify using `only [zero_mul, Real.exp_zero, mul_one] at h0`. Conclude with `h0.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hm)`.
-/
theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d)
    (hl : LocDec B h) (hb : HBig B 40 h) : Integrable (ph B d) (muInf B.I) := by
  obtain ⟨hc, hm, hi⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl
  have h0 := hi 0 le_rfl (fun v => by
    rcases Nat.eq_zero_or_pos (rkR (B.I.ε v)) with hq | hq
    · exact Or.inl hq
    · right
      have hle : rkR (B.I.ε v) ≤ B.I.n := by
        unfold rkR
        refine (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
      have h1 : (0 : ℝ) < rkR (B.I.ε v) := by exact_mod_cast hq
      have h2 : ((rkR (B.I.ε v) : ℕ) : ℝ) ≤ B.I.n := by exact_mod_cast hle
      have h3 := Real.sqrt_pos.2 h1
      have h4 := hb v
      have h5 : (0 : ℝ) < B.I.n := h1.trans_le h2
      have h6 : (B.I.n : ℝ) * rkR (B.I.ε v) ≤ (B.I.n : ℝ) ^ 2 := by nlinarith
      have h7 : 0 < (B.I.n : ℝ) ^ 2 * Real.sqrt (rkR (B.I.ε v)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h6 h3.le])
  simp only [zero_mul, Real.exp_zero, mul_one] at h0
  exact h0.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hm)

/- English proof (translation)
Introduce `hS B d h hd hg hgap hl hb T hT`. Take `⟨-, hcomm, ⟨Rφ, hR⟩, -⟩` from `GlobalTheory.GlobProj.globalProj_holds B d hd (integrable_ph B d h hd hl hb)`. Take `⟨-, hirr, -, hw, -⟩` from `GlobalTheory.Dec.tensorRep B d hd`. Establish `hle : B.I.eHom B.σs B.μf B.fund B.R B.Re ≤ B.I.HomS B.σs B.μf B.fund B.R`. Introduce and unpack `_ ⟨A, hA, rfl⟩ g`.

Use `show (B.Re.comp A).comp (B.σs g) = (B.R (g, 1)).comp (B.Re.comp A)`. Rewrite using `[ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, hcomm g, ContinuousLinearMap.comp_assoc]`. Take `⟨S, hSm, hScl, hSst, -⟩` from `GlobalTheory.CuspSubspace.cuspidal_closed_stable B`. Use `⟨hle hT, fun u => ⟨?_, fun k hk => ?_⟩⟩` and prove the remaining obligations. Establish `hw' : T (B.tens B.w) ∈ S`.

Rewrite using `[hSm]`. Conclude with `GlobalTheory.T.countedVector_isCuspForm hS B d h hd hg hgap hl hb Rφ hR T hT`. Establish `hcl : IsClosed ((S.comap (T : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund) : Submodule ℂ B.Hs) : Set B.Hs)` using `hScl.preimage T.continuous`. Break down `hirr _ hcl (fun g v hv => by` into its components or cases. Establish `e` using `congrArg (fun A : B.Hs →L[ℂ] B.I.L2 B.μf B.fund => A v) (hle hT g)`.

Simplify using `only [ContinuousLinearMap.comp_apply] at e`. Use `show T (B.σs g v) ∈ S`. Rewrite using `[e]`. Conclude with `hSst _ _ hv) with h0 | h0`. Establish `: B.tens B.w ∈ S.comap (T : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund)` using `hw'`.

Rewrite `this` using `[h0, Submodule.mem_bot]`. Rewrite `hw` using `[this]`. Simplify using `at hw`. Establish `: u ∈ S.comap (T : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund)` using `by rw [h0]; trivial`. Conclude with `(hSm _).1 this`.

Take `⟨A, -, hA⟩` from `hT`. Rewrite using `[← hA]`. Conclude with `congrArg (fun C : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => C (A u)) (re_fixed B k hk)`.
-/
theorem cusp_all : GlobalTheory.DSId.StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → ∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, A ∈ B.I.HomS B.σs B.μf B.fund B.R ∧ ∀ u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (A u)) ∧ ∀ k ∈ B.I.Kg B.g, B.R (1, k) (A u) = A u := by
  intro hS B d h hd hg hgap hl hb T hT
  obtain ⟨-, hcomm, ⟨Rφ, hR⟩, -⟩ := GlobalTheory.GlobProj.globalProj_holds B d hd (integrable_ph B d h hd hl hb)
  obtain ⟨-, hirr, -, hw, -⟩ := GlobalTheory.Dec.tensorRep B d hd
  have hle : B.I.eHom B.σs B.μf B.fund B.R B.Re ≤ B.I.HomS B.σs B.μf B.fund B.R := by
    rintro _ ⟨A, hA, rfl⟩ g
    show (B.Re.comp A).comp (B.σs g) = (B.R (g, 1)).comp (B.Re.comp A)
    rw [ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  obtain ⟨S, hSm, hScl, hSst, -⟩ := GlobalTheory.CuspSubspace.cuspidal_closed_stable B
  refine ⟨hle hT, fun u => ⟨?_, fun k hk => ?_⟩⟩
  · have hw' : T (B.tens B.w) ∈ S := by
      rw [hSm]
      exact GlobalTheory.T.countedVector_isCuspForm hS B d h hd hg hgap hl hb Rφ hR T hT
    have hcl : IsClosed ((S.comap (T : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund) : Submodule ℂ B.Hs) : Set B.Hs) :=
      hScl.preimage T.continuous
    rcases hirr _ hcl (fun g v hv => by
      have e := congrArg (fun A : B.Hs →L[ℂ] B.I.L2 B.μf B.fund => A v) (hle hT g)
      simp only [ContinuousLinearMap.comp_apply] at e
      show T (B.σs g v) ∈ S
      rw [e]
      exact hSst _ _ hv) with h0 | h0
    · have : B.tens B.w ∈ S.comap (T : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund) := hw'
      rw [h0, Submodule.mem_bot] at this
      rw [this] at hw
      simp at hw
    · have : u ∈ S.comap (T : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund) := by rw [h0]; trivial
      exact (hSm _).1 this
  · obtain ⟨A, -, hA⟩ := hT
    rw [← hA]
    exact congrArg (fun C : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => C (A u)) (re_fixed B k hk)

end GlobalTheory.Dec.CuspAll
