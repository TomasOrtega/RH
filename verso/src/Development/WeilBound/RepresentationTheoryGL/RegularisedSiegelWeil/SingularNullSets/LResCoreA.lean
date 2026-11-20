import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryClosureLocalComponentsOpen

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LResCore

open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

variable {D : D7} {n : ℕ}

/- English proof (translation)
Introduce `k hk`. Take `⟨hK, hA⟩` from `Subgroup.mem_inf.1 hk`. Rewrite `hA` using `[mem_atPts]`. Rewrite using `[KOff, mem_levelOff]`. Use `⟨hA.1, fun w hw => hA.2 w ?_, fun w _ => ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.mem_singleton]`. Introduce and unpack `rfl`. Conclude with `hv hw`. Distinguish the cases in `hwv : w = v`. Substitute `hwv` using the available equality.

Establish `h1 : k ∈ levelOpen D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n))` using `hK.1`. Conclude with `Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 h1 w)`. Rewrite using `[hA.2 w (by rwa [Finset.mem_singleton])]`. Conclude with `one_mem _`.
-/
theorem kAt_le_kOff {v : Pl D} {S : Finset (Pl D)} (hv : v ∉ S) : KAt D n v ≤ KOff D n S := by
  intro k hk
  obtain ⟨hK, hA⟩ := Subgroup.mem_inf.1 hk
  rw [mem_atPts] at hA
  rw [KOff, mem_levelOff]
  refine ⟨hA.1, fun w hw => hA.2 w ?_, fun w _ => ?_⟩
  · rw [Finset.mem_singleton]
    rintro rfl
    exact hv hw
  · by_cases hwv : w = v
    · subst hwv
      have h1 : k ∈ levelOpen D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) := hK.1
      exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 h1 w)
    · rw [hA.2 w (by rwa [Finset.mem_singleton])]
      exact one_mem _

/- English proof (translation)
Establish `: Submodule.IsLattice D.host.E (stdLattice D.host.E (n + n))` using `isLattice_stdLattice`. Establish `hK : IsCompact (K D n : Set (G D n))` using `isCompact_levelAll (isCMExt_host D) _ _ _`. Establish `e : (atPts D.sp.cm.sig (Jst D n) {v} : Set (G D n)) = (finPts D.sp.cm.sig (Jst D n) : Set (G D n)) ∩ ⋂ w, ⋂ (_ : w ∉ ({v} : Finset (Pl D))), (proj D.sp.cm.sig (Jst D n) w) ⁻¹' {1}`. Use extensionality with `k`. Simplify using `only [SetLike.mem_coe, mem_atPts, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]`.

Establish `hA : IsClosed (atPts D.sp.cm.sig (Jst D n) {v} : Set (G D n))`. Rewrite using `[e]`. Conclude with `(isClosed_finPts _ _).inter (isClosed_iInter fun w => isClosed_iInter fun _ => isClosed_singleton.preimage (continuous_proj _ _ w))`. Establish `e2 : (KAt D n v : Set (G D n)) = (K D n : Set (G D n)) ∩ (atPts D.sp.cm.sig (Jst D n) {v} : Set (G D n))` using `Subgroup.coe_inf _ _`. Rewrite using `[e2]`.

Conclude with `hK.inter_right hA`.
-/
theorem isCompact_kAt (v : Pl D) : IsCompact (KAt D n v : Set (G D n)) := by
  have : Submodule.IsLattice D.host.E (stdLattice D.host.E (n + n)) := isLattice_stdLattice
  have hK : IsCompact (K D n : Set (G D n)) := isCompact_levelAll (isCMExt_host D) _ _ _
  have e : (atPts D.sp.cm.sig (Jst D n) {v} : Set (G D n)) = (finPts D.sp.cm.sig (Jst D n) : Set (G D n)) ∩
      ⋂ w, ⋂ (_ : w ∉ ({v} : Finset (Pl D))), (proj D.sp.cm.sig (Jst D n) w) ⁻¹' {1} := by
    ext k
    simp only [SetLike.mem_coe, mem_atPts, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
  have hA : IsClosed (atPts D.sp.cm.sig (Jst D n) {v} : Set (G D n)) := by
    rw [e]
    exact (isClosed_finPts _ _).inter (isClosed_iInter fun w => isClosed_iInter fun _ =>
      isClosed_singleton.preimage (continuous_proj _ _ w))
  have e2 : (KAt D n v : Set (G D n)) = (K D n : Set (G D n)) ∩ (atPts D.sp.cm.sig (Jst D n) {v} : Set (G D n)) :=
    Subgroup.coe_inf _ _
  rw [e2]
  exact hK.inter_right hA

/- English proof (translation)
Establish `: CompactSpace K₀` using `isCompact_iff_compactSpace.mp h`. Use `⟨Measure.haarMeasure ⊤, inferInstance, ⟨?_⟩⟩` and prove the remaining obligations. Simplify using `using Measure.haarMeasure_self (G := K₀) (K₀ := ⊤)`.
-/
theorem exists_haar_prob {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X]
    [BorelSpace X] (K₀ : Subgroup X) (h : IsCompact (K₀ : Set X)) :
    ∃ ν : Measure K₀, ν.IsHaarMeasure ∧ IsProbabilityMeasure ν := by
  have : CompactSpace K₀ := isCompact_iff_compactSpace.mp h
  refine ⟨Measure.haarMeasure ⊤, inferInstance, ⟨?_⟩⟩
  simpa using Measure.haarMeasure_self (G := K₀) (K₀ := ⊤)

/- English proof (translation)
Introduce `q hq a ha g`. Take `⟨m, u, b, rfl, hm, hu⟩` from `GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hq a ha`. Establish `e' : ωB (m * u * g) Φ = ωB m (ωB u (ωB g Φ))`. Rewrite using `[map_mul, map_mul]`. Both sides reduce to the same expression.

Establish `z1 : ((0 : Mx D B.rank n) ⬝ a.1 : Mx D B.rank n) = 0` using `Matrix.zero_mul _`. Establish `z2 : GlobalTheory.StdUnn.inner B (0 : Mx D B.rank n) 0 = 0`. Rewrite using `[GlobalTheory.StdUnn.inner, adj_zero, Matrix.zero_mul]`. Establish `e3 : ((B.rank : ℂ) / 2) = (t : ℂ) / 2 + (n : ℂ) / 2`. Rewrite using `[hB]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `show (ωB (m * u * g) Φ).1 0 = _ * _ * (ωB g Φ).1 0`. Rewrite using `[e', hω.levi m a hm, hω.unip u b hu, z1, z2, e3]`. Simplify using `[halfTr]`.
-/
theorem isLaw_sw {t : ℕ} {B : HSp D} (hB : B.rank = n + t) {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
    {θ : InfFam D} {μB : Measure (Mx D B.rank n)} {ωB : G D n →* Module.End ℂ (schwartzA θ B.rank n)}
    (hω : IsWeilSch ψ χ θ B μB ωB) (Φ : schwartzA θ B.rank n) :
    IsLaw χ ((t : ℂ) / 2) (fun g => (ωB g Φ).1 0) := by
  intro q hq a ha g
  obtain ⟨m, u, b, rfl, hm, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hq a ha
  have e' : ωB (m * u * g) Φ = ωB m (ωB u (ωB g Φ)) := by
    rw [map_mul, map_mul]; rfl
  have z1 : ((0 : Mx D B.rank n) ⬝ a.1 : Mx D B.rank n) = 0 := Matrix.zero_mul _
  have z2 : GlobalTheory.StdUnn.inner B (0 : Mx D B.rank n) 0 = 0 := by
    rw [GlobalTheory.StdUnn.inner, adj_zero, Matrix.zero_mul]
  have e3 : ((B.rank : ℂ) / 2) = (t : ℂ) / 2 + (n : ℂ) / 2 := by
    rw [hB]; push_cast; ring
  show (ωB (m * u * g) Φ).1 0 = _ * _ * (ωB g Φ).1 0
  rw [e', hω.levi m a hm, hω.unip u b hu, z1, z2, e3]
  simp [halfTr]

/- English proof (translation)
Simplify using `only [theta, map_mul]`. Both sides reduce to the same expression.
-/
theorem theta_mul {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n))
    (Ψ : schwartzA θ V.rank n) (g u : G D n) (h : GA D V) : theta ω Ψ (g * u) h = theta ω (ω u Ψ) g h := by
  simp only [theta, map_mul]
  rfl

end PositivityTheory.Rg.Rsw.L.LResCore

end
