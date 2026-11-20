import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

/- English proof (translation)
Unfold `kerH`. Rewrite using `[← finsum_comp_equiv (Equiv.mulLeft γ)]`. Use `finsum_congr fun δ => ?_` and prove the remaining obligations. Use `congr 1`. Simplify using `only [Equiv.coe_mulLeft, Subgroup.coe_mul, _root_.mul_inv_rev]`.

Use `group`.
-/
private theorem kerH_left {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (φ : H E n 0 → ℂ) (γ : ratH E n 0) (x y : H E n 0) :
    kerH φ ((γ : H E n 0) * x) y = kerH φ x y := by
  unfold kerH
  rw [← finsum_comp_equiv (Equiv.mulLeft γ)]
  refine finsum_congr fun δ => ?_
  congr 1
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, _root_.mul_inv_rev]
  group

/- English proof (translation)
Introduce `hA hK E _ _ _ n ι _ s Φ T hΦ hT h g hg x i`. Take `⟨k, k', hk⟩` from `vecsEx E n 0 s.D ι Φ Φ T T 0 hΦ hΦ hT hT`. Establish `hF : Continuous fun x => inner ℂ (s.k₁ x i) h` using `((s.vecs.cont i).1).inner continuous_const`. Establish `hG : Continuous fun x => inner ℂ (k x i) g` using `((hk.cont i).1).inner continuous_const`. Establish `hIF : Inv fun x => inner ℂ (s.k₁ x i) h` using `fun γ x => by`.

Simplify using `only [(hK E n ι s).1 γ x]`. Establish `hIG : Inv fun x => inner ℂ (k x i) g` using `fun γ x => by`. Simplify using `only [hk.rep₁, kerH_left]`. Establish `hae : ∀ᵐ x ∂s.D.ν, ldet x ∈ (Set.univ : Set ℝ) → inner ℂ (s.k₁ x i) h = inner ℂ (k x i) g`. Establish `h1` using `s.o₁ h i`.

Establish `h2` using `hT g i`. Rewrite `h1` using `[hg]`. Use `filter_upwards [h1, h2] with y a1 a2 _`. Rewrite using `[s.vecs.rep₁, hk.rep₁, ← a1, a2]`. Use `hA E n s.D _ _ Set.univ hF hG hIF hIG isOpen_univ hae x (Set.mem_univ _)` as an intermediate fact.

Rewrite using `[this, hk.rep₁]`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.pointRep_pf :
    AeEq → KInv → PointRep := by
  intro hA hK E _ _ _ n ι _ s Φ T hΦ hT h g hg x i
  obtain ⟨k, k', hk⟩ := vecsEx E n 0 s.D ι Φ Φ T T 0 hΦ hΦ hT hT
  have hF : Continuous fun x => inner ℂ (s.k₁ x i) h :=
    ((s.vecs.cont i).1).inner continuous_const
  have hG : Continuous fun x => inner ℂ (k x i) g := ((hk.cont i).1).inner continuous_const
  have hIF : Inv fun x => inner ℂ (s.k₁ x i) h := fun γ x => by
    simp only [(hK E n ι s).1 γ x]
  have hIG : Inv fun x => inner ℂ (k x i) g := fun γ x => by
    simp only [hk.rep₁, kerH_left]
  have hae : ∀ᵐ x ∂s.D.ν, ldet x ∈ (Set.univ : Set ℝ) →
      inner ℂ (s.k₁ x i) h = inner ℂ (k x i) g := by
    have h1 := s.o₁ h i
    have h2 := hT g i
    rw [hg] at h1
    filter_upwards [h1, h2] with y a1 a2 _
    rw [s.vecs.rep₁, hk.rep₁, ← a1, a2]
  have := hA E n s.D _ _ Set.univ hF hG hIF hIG isOpen_univ hae x (Set.mem_univ _)
  rw [this, hk.rep₁]
