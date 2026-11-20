import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.OrthZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TwtrContOfMem
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.SplitCentreMulTor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open NumberField GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

/- English proof (translation)
Take `⟨C, hC⟩` from `(hS.image hf).isBounded.exists_norm_le`. Establish `h1 : f 1 = 0`. Use `hm 1 1` as an intermediate fact. Rewrite `this` using `[mul_one]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hp : ∀ m : ℕ, f (k ^ m) = m * f k`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp [h1]`. Consider the case `succ m ih => rw [pow_succ, hm, ih]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < |f k|` using `abs_pos.2 hne`. Take `⟨m, hmC⟩` from `exists_nat_gt (C / |f k|)`.

Establish `hb` using `hC _ ⟨k ^ m, hk m, rfl⟩`. Rewrite `hb` using `[hp, Real.norm_eq_abs, abs_mul, Nat.abs_cast]`. Rewrite `hmC` using `[div_lt_iff₀ hpos]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem zero_of_powers_compact {G : Type*} [Monoid G] [TopologicalSpace G] (f : G → ℝ) (hf : Continuous f)
    (hm : ∀ x y, f (x * y) = f x + f y) (S : Set G) (hS : IsCompact S) (k : G) (hk : ∀ m : ℕ, k ^ m ∈ S) : f k = 0 := by
  obtain ⟨C, hC⟩ := (hS.image hf).isBounded.exists_norm_le
  have h1 : f 1 = 0 := by
    have := hm 1 1
    rw [mul_one] at this
    linarith
  have hp : ∀ m : ℕ, f (k ^ m) = m * f k := by
    intro m
    induction m with
    | zero => simp [h1]
    | succ m ih => rw [pow_succ, hm, ih]; push_cast; ring
  by_contra hne
  have hpos : 0 < |f k| := abs_pos.2 hne
  obtain ⟨m, hmC⟩ := exists_nat_gt (C / |f k|)
  have hb := hC _ ⟨k ^ m, hk m, rfl⟩
  rw [hp, Real.norm_eq_abs, abs_mul, Nat.abs_cast] at hb
  rw [div_lt_iff₀ hpos] at hmC
  linarith

/- English proof (translation)
Establish `hu : Continuous (Unitary.toUnits : Kinf E n → _)` using `Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩`. Conclude with `GlobalTheory.CuspQuot.continuous_infGL.comp hu`.
-/
private theorem continuous_kI (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Continuous (kI E n) := by
  have hu : Continuous (Unitary.toUnits : Kinf E n → _) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩
  exact GlobalTheory.CuspQuot.continuous_infGL.comp hu

/- English proof (translation)
Introduce `E _ _ _ n`. Establish `hc` using `DiscreteGroups.T1.G.continuous_logAbs_det (E := E) (n := n)`. Establish `hm` using `DiscreteGroups.T1.G.Dcy.logAbs_det_mul' (E := E) (n := n)`. Use `⟨fun k => ?_, fun K hK k hk => ?_⟩` and prove the remaining obligations. Use `haveI : CompactSpace (Kinf E n) := GlobalTheory.KinfCompactness.compactSpace_Kinf E n`.

Conclude with `zero_of_powers_compact _ hc hm (Set.range (kI E n)) (isCompact_range (continuous_kI E n)) _ fun m => ⟨k ^ m, map_pow _ _ _⟩`. Conclude with `zero_of_powers_compact _ hc hm (finGL E n '' (K : Set _)) (hK.image GlobalTheory.BCT.GlobLev.continuous_finGL_ad) _ fun m => ⟨k ^ m, K.pow_mem hk m, map_pow _ _ _⟩`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.detZero_pf :
    DetZero := by
  intro E _ _ _ n
  have hc := DiscreteGroups.T1.G.continuous_logAbs_det (E := E) (n := n)
  have hm := DiscreteGroups.T1.G.Dcy.logAbs_det_mul' (E := E) (n := n)
  refine ⟨fun k => ?_, fun K hK k hk => ?_⟩
  · haveI : CompactSpace (Kinf E n) := GlobalTheory.KinfCompactness.compactSpace_Kinf E n
    exact zero_of_powers_compact _ hc hm (Set.range (kI E n)) (isCompact_range (continuous_kI E n)) _
      fun m => ⟨k ^ m, map_pow _ _ _⟩
  · exact zero_of_powers_compact _ hc hm (finGL E n '' (K : Set _))
      (hK.image GlobalTheory.BCT.GlobLev.continuous_finGL_ad) _ fun m => ⟨k ^ m, K.pow_mem hk m, map_pow _ _ _⟩
