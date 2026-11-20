import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalSplitStabilizerDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSplitPlaceFinitePointsOffPrimesOfSupportedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOfStabiliserMulInvEqStandardLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VertexLatticeEqAtMulSplitSupportedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VertexLatticeCoordsRationalPointMulEqCoordMatrixStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryCoordinateOfRationalPointDefiniteVe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D T L sc G W S X hX l hl x`. Establish `erefl : ∀ {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Formalism.MainNotions.TaylorLogMetric.EqAt D l L L` using `fun L => ⟨1, Nat.coprime_one_left l, fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩`. Establish `esymm : ∀ {N : ℕ} {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}, Formalism.MainNotions.TaylorLogMetric.EqAt D l L L₁ → Formalism.MainNotions.TaylorLogMetric.EqAt D l L₁ L` using `fun ⟨s, hs, h1, h2⟩ => ⟨s, hs, h2, h1⟩`. Establish `etrans : ∀ {N : ℕ} {L L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}, Formalism.MainNotions.TaylorLogMetric.EqAt D l L L₁ → Formalism.MainNotions.TaylorLogMetric.EqAt D l L₁ L₂ → Formalism.MainNotions.TaylorLogMetric.EqAt D l L L₂`. Introduce `N L L₁ L₂ h h'`.

Take `⟨s, hs, h1, h2⟩` from `h`. Take `⟨t, ht, h1', h2'⟩` from `h'`. Use `⟨t * s, Nat.Coprime.mul_left ht hs, fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Use `h1' _ (h1 x hx)` as an intermediate fact. Rewrite `this` using `[smul_smul, ← Nat.cast_mul]`. Then use the resulting hypothesis.

Use `h2 _ (h2' x hx)` as an intermediate fact. Rewrite `this` using `[smul_smul, ← Nat.cast_mul, mul_comm]`. Then use the resulting hypothesis. Take `⟨r, s, k, hr, hs, hk, e⟩` from `GlobalTheory.T.exists_rational_split_stabilizer_decomposition (G.V X) (S.N.fr X) (∏ q ∈ ({l} : Finset ℕ), q) (by simpa using hl.pos) (x * S.N.u X)`. Establish `hs'` using `GlobalTheory.T.mem_splitPlaceFinitePointsOffPrimes_of_supported _ {l} s hs`. Establish `hB` using `GlobalTheory.T.latticeOf_stabiliser_mul_inv_eq_standardLattice S X hX k hk`.

Establish `key : ∀ s' ∈ GlobalTheory.MovedKappaEx.splitOff (G.V X) {l}, ∀ y : FinPt G X, Formalism.MainNotions.TaylorLogMetric.EqAt D l (latAt S X (s' * y)) (latAt S X y)`. Introduce `s' hs'`. Proceed by induction on `hs' using Subgroup.closure_induction with`. Consider the case `mem g hg`. Take `⟨e, he, hoff, hsupp⟩` from `hg`.

Conclude with `fun y => GlobalTheory.T.vertexLattice_eqAt_mul_splitSupported S X hX l hl e he (hoff l (Finset.mem_singleton_self l)) g y hsupp`. Consider the case `one => exact fun y => by rw [one_mul]; exact erefl _`. Consider the case `mul a b _ _ ha hb => exact fun y => by rw [mul_assoc]; exact etrans (ha (b * y)) (hb y)`. Consider the case `inv a _ ha`. Introduce `y`.

Use `ha (a⁻¹ * y)` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Conclude with `esymm this`. Establish `h1` using `key s hs' (k * (S.N.u X)⁻¹)`. Rewrite `h1` using `[hB]`.

Establish `hr' : GlobalTheory.MovedKappaEx.RatFin (G.V X) r⁻¹`. Take `⟨γ, hγ, hγr⟩` from `hr`. Use `⟨γ⁻¹, inv_mem hγ, ?_⟩` and prove the remaining obligations. Rewrite using `[map_inv, hγr, Subgroup.coe_inv, map_inv]`. Take `⟨U, hU⟩` from `GlobalTheory.RatMoveJets.exists_unitary_ratCoord S X hX r⁻¹ hr'`.

Use `⟨r⁻¹, U, hU, GlobalTheory.T.vertexLatticeCoords_rationalPoint_mul_eq_coordMatrix S X _ U hU x, ?_⟩` and prove the remaining obligations. Establish `hx : r⁻¹ * x = s * (k * (S.N.u X)⁻¹)`. Rewrite using `[inv_mul_eq_iff_eq_mul, ← mul_assoc, ← mul_assoc, ← e, mul_inv_cancel_right]`. Rewrite using `[hx]`. Conclude with `h1`.
-/
theorem UpperTheory.WildA.toStd :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ) (X : Node), DefNode D.R.m X → ∀ l : ℕ, l.Prime → ∀ x : FinPt G X,
      ∃ (r : FinPt G X) (U : Matrix.unitaryGroup (Fin (G.V X).rank) D.host.E), GlobalTheory.RatMoveJets.RatCoord _ (S.N.fr X) r U ∧
        latAt S X (r * x) = SDLat.smulLat U.1 (latAt S X x) ∧ Formalism.MainNotions.TaylorLogMetric.EqAt D l (latAt S X (r * x)) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) := by
  intro D T L sc G W S X hX l hl x
  have erefl : ∀ {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Formalism.MainNotions.TaylorLogMetric.EqAt D l L L := fun L =>
    ⟨1, Nat.coprime_one_left l, fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩
  have esymm : ∀ {N : ℕ} {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)},
      Formalism.MainNotions.TaylorLogMetric.EqAt D l L L₁ → Formalism.MainNotions.TaylorLogMetric.EqAt D l L₁ L := fun ⟨s, hs, h1, h2⟩ => ⟨s, hs, h2, h1⟩
  have etrans : ∀ {N : ℕ} {L L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)},
      Formalism.MainNotions.TaylorLogMetric.EqAt D l L L₁ → Formalism.MainNotions.TaylorLogMetric.EqAt D l L₁ L₂ → Formalism.MainNotions.TaylorLogMetric.EqAt D l L L₂ := by
    intro N L L₁ L₂ h h'
    obtain ⟨s, hs, h1, h2⟩ := h
    obtain ⟨t, ht, h1', h2'⟩ := h'
    refine ⟨t * s, Nat.Coprime.mul_left ht hs, fun x hx => ?_, fun x hx => ?_⟩
    · have := h1' _ (h1 x hx)
      rwa [smul_smul, ← Nat.cast_mul] at this
    · have := h2 _ (h2' x hx)
      rwa [smul_smul, ← Nat.cast_mul, mul_comm] at this
  obtain ⟨r, s, k, hr, hs, hk, e⟩ := GlobalTheory.T.exists_rational_split_stabilizer_decomposition (G.V X) (S.N.fr X) (∏ q ∈ ({l} : Finset ℕ), q)
    (by simpa using hl.pos) (x * S.N.u X)
  have hs' := GlobalTheory.T.mem_splitPlaceFinitePointsOffPrimes_of_supported _ {l} s hs
  have hB := GlobalTheory.T.latticeOf_stabiliser_mul_inv_eq_standardLattice S X hX k hk
  have key : ∀ s' ∈ GlobalTheory.MovedKappaEx.splitOff (G.V X) {l}, ∀ y : FinPt G X,
      Formalism.MainNotions.TaylorLogMetric.EqAt D l (latAt S X (s' * y)) (latAt S X y) := by
    intro s' hs'
    induction hs' using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨e, he, hoff, hsupp⟩ := hg
      exact fun y => GlobalTheory.T.vertexLattice_eqAt_mul_splitSupported S X hX l hl e he (hoff l (Finset.mem_singleton_self l)) g y hsupp
    | one => exact fun y => by rw [one_mul]; exact erefl _
    | mul a b _ _ ha hb => exact fun y => by rw [mul_assoc]; exact etrans (ha (b * y)) (hb y)
    | inv a _ ha =>
      intro y
      have := ha (a⁻¹ * y)
      rw [mul_inv_cancel_left] at this
      exact esymm this
  have h1 := key s hs' (k * (S.N.u X)⁻¹)
  rw [hB] at h1
  have hr' : GlobalTheory.MovedKappaEx.RatFin (G.V X) r⁻¹ := by
    obtain ⟨γ, hγ, hγr⟩ := hr
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    rw [map_inv, hγr, Subgroup.coe_inv, map_inv]
  obtain ⟨U, hU⟩ := GlobalTheory.RatMoveJets.exists_unitary_ratCoord S X hX r⁻¹ hr'
  refine ⟨r⁻¹, U, hU, GlobalTheory.T.vertexLatticeCoords_rationalPoint_mul_eq_coordMatrix S X _ U hU x, ?_⟩
  have hx : r⁻¹ * x = s * (k * (S.N.u X)⁻¹) := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← mul_assoc, ← e, mul_inv_cancel_right]
  rw [hx]
  exact h1
