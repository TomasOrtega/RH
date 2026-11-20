import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingSecsOfClsEq
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAmpleTensorAmplePowProjective
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CutOutSections

/- English proof (translation)
Apply `DVR.SecOps.sec_ext` to reduce the goal to its premises. Introduce `k`. Establish `hk : Y.basicOpen (s.f k) = ⊥` using `le_bot_iff.1 ((basicOpen_le_nonzeroLocus s k).trans h.le)`. Rewrite `hk` using `[AlgebraicGeometry.basicOpen_eq_bot_iff]`. Rewrite using `[hk]`.

Both sides reduce to the same expression.
-/
theorem sec_eq_zero_of_nonzeroLocus_eq_bot {Y : Scheme.{0}} [IsReduced Y] {M : LB Y} (s : M.Sec)
    (h : nonzeroLocus s = ⊥) : s = 0 := by
  apply DVR.SecOps.sec_ext
  intro k
  have hk : Y.basicOpen (s.f k) = ⊥ := le_bot_iff.1 ((basicOpen_le_nonzeroLocus s k).trans h.le)
  rw [AlgebraicGeometry.basicOpen_eq_bot_iff] at hk
  rw [hk]
  rfl

/- English proof (translation)
Use `(hN.eventually_isGenerated_tens_lbPow (LB.isLB_triv X)).mono fun k hk => ?_` and prove the remaining obligations. Take `⟨c, u, hu⟩` from `hk`. Establish `hP` using `isLB_lbPow hN.isLB k`. Establish `hT` using `isLB_tens (LB.isLB_triv X) hP`. Take `⟨v, hv⟩` from `CechPic.exists_generating_secs_of_cls_eq X _ _ hT hP (by rw [CechPic.cls_tens (LB.isLB_triv X) hP, cls_triv, zero_add]) (Fin c) u hu`.

Conclude with `⟨c, v, hv⟩`.
-/
theorem eventually_isGenerated_lbPow {X : Scheme.{0}} {N : LB X} (hN : IsAmpleLB N) :
    ∀ᶠ k in atTop, IsGenerated (lbPow N k) := by
  refine (hN.eventually_isGenerated_tens_lbPow (LB.isLB_triv X)).mono fun k hk => ?_
  obtain ⟨c, u, hu⟩ := hk
  have hP := isLB_lbPow hN.isLB k
  have hT := isLB_tens (LB.isLB_triv X) hP
  obtain ⟨v, hv⟩ := CechPic.exists_generating_secs_of_cls_eq X _ _ hT hP
    (by rw [CechPic.cls_tens (LB.isLB_triv X) hP, cls_triv, zero_add]) (Fin c) u hu
  exact ⟨c, v, hv⟩

/- English proof (translation)
Introduce `X _ _ p hp N Z hN`. Establish `: AlgebraicGeometry.IsNoetherian X` using `isNoetherian_of_isProjOver hp`. Set `U : X.Opens` to `⟨(Z : Set X)ᶜ, Z.isClosed.isOpen_compl⟩`. Establish `hloc : ∀ y : U, ∃ n, 1 ≤ n ∧ ∃ s : (lbPow N n).Sec, (y : X) ∈ nonzeroLocus s ∧ nonzeroLocus s ≤ U ∧ IsAffineOpen (nonzeroLocus s)` using `fun y => hN.exists_affine_le y.2`. Use `choose n hn s hys hle _ using hloc`.

Establish `hc : IsCompact (U : Set X)` using `NoetherianSpace.isCompact _`. Take `⟨T, hT⟩` from `hc.elim_finite_subcover (fun y : U => (nonzeroLocus (s y) : Set X)) (fun y => (nonzeroLocus (s y)).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hys ⟨y, hy⟩⟩)`. Take `⟨m, -, t, ht⟩` from `exists_common_pow (fun y : T => n y) (fun y => hn y) (fun y => s y)`. Take `⟨K, hK⟩` from `eventually_atTop.1 (eventually_isGenerated_lbPow hN)`. Use `eventually_atTop.2 ⟨K + m, fun l hl => ?_⟩` and prove the remaining obligations.

Take `⟨c, g, hg⟩` from `hK (l - m) (by omega)`. Establish `hml : m + (l - m) = l` using `by omega`. Set `κ' : T × Fin c → (lbPow N l).Sec` to `fun q => secCast hml (secMul (t q.1) (g q.2))`. Establish `hκ' : ∀ q, nonzeroLocus (κ' q) = nonzeroLocus (s q.1) ⊓ nonzeroLocus (g q.2)` using `fun q => by`. Simplify using `only [κ', nonzeroLocus_secCast, nonzeroLocus_secMul, ht]`.

Establish `hb : ∀ q, ∀ y ∈ Z, y ∉ nonzeroLocus (κ' q)` using `fun q y hy h => by`. Rewrite `h` using `[hκ']`. Conclude with `hle _ h.1 hy`. Take `⟨r, ⟨e⟩⟩` from `Finite.exists_equiv_fin (T × Fin c)`. Use `⟨r, fun i => κ' (e.symm i), fun i => ?_, fun i => hb _, fun y hy => ?_⟩` and prove the remaining obligations.

Use `ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z` as an intermediate fact. Apply `sec_eq_zero_of_nonzeroLocus_eq_bot` to reduce the goal to its premises. Rewrite using `[GlobalTheory.nonzeroLocus_secPull]`. Use `le_bot_iff.1 fun z hz => ?_` and prove the remaining obligations. Establish `hz' : redι Z z ∈ (Z : Set X)`.

Rewrite using `[← range_redι Z]`. Conclude with `Set.mem_range_self z`. Conclude with `hb _ _ hz' hz`. Take `⟨a, ha', hya'⟩` from `Set.mem_iUnion₂.1 (hT hy)`. Take `⟨j, hj⟩` from `Opens.mem_iSup.1 (hg.ge (Set.mem_univ y))`.

Use `⟨e (⟨a, ha'⟩, j), ?_⟩` and prove the remaining obligations. Use `show y ∈ nonzeroLocus (κ' (e.symm (e (⟨a, ha'⟩, j))))`. Rewrite using `[e.symm_apply_apply, hκ']`. Conclude with `⟨hya', hj⟩`.
-/
theorem eventually_exists_secs_cutting_out : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (Z : Closeds X), IsAmpleLB N → ∀ᶠ l in atTop, ∃ (r : ℕ) (κ : Fin r → (lbPow N l).Sec), (∀ i, GlobalTheory.secPull (κ i) (redι Z) = 0) ∧ (∀ i, ∀ y ∈ Z, y ∉ nonzeroLocus (κ i)) ∧ ∀ y, y ∉ Z → ∃ i, y ∈ nonzeroLocus (κ i) := by
  intro X _ _ p hp N Z hN
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  let U : X.Opens := ⟨(Z : Set X)ᶜ, Z.isClosed.isOpen_compl⟩
  have hloc : ∀ y : U, ∃ n, 1 ≤ n ∧ ∃ s : (lbPow N n).Sec, (y : X) ∈ nonzeroLocus s ∧
      nonzeroLocus s ≤ U ∧ IsAffineOpen (nonzeroLocus s) := fun y => hN.exists_affine_le y.2
  choose n hn s hys hle _ using hloc
  have hc : IsCompact (U : Set X) := NoetherianSpace.isCompact _
  obtain ⟨T, hT⟩ := hc.elim_finite_subcover (fun y : U => (nonzeroLocus (s y) : Set X))
    (fun y => (nonzeroLocus (s y)).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hys ⟨y, hy⟩⟩)
  obtain ⟨m, -, t, ht⟩ := exists_common_pow (fun y : T => n y) (fun y => hn y) (fun y => s y)
  obtain ⟨K, hK⟩ := eventually_atTop.1 (eventually_isGenerated_lbPow hN)
  refine eventually_atTop.2 ⟨K + m, fun l hl => ?_⟩
  obtain ⟨c, g, hg⟩ := hK (l - m) (by omega)
  have hml : m + (l - m) = l := by omega
  let κ' : T × Fin c → (lbPow N l).Sec := fun q => secCast hml (secMul (t q.1) (g q.2))
  have hκ' : ∀ q, nonzeroLocus (κ' q) = nonzeroLocus (s q.1) ⊓ nonzeroLocus (g q.2) := fun q => by
    simp only [κ', nonzeroLocus_secCast, nonzeroLocus_secMul, ht]
  have hb : ∀ q, ∀ y ∈ Z, y ∉ nonzeroLocus (κ' q) := fun q y hy h => by
    rw [hκ'] at h
    exact hle _ h.1 hy
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin (T × Fin c)
  refine ⟨r, fun i => κ' (e.symm i), fun i => ?_, fun i => hb _, fun y hy => ?_⟩
  · have := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
    apply sec_eq_zero_of_nonzeroLocus_eq_bot
    rw [GlobalTheory.nonzeroLocus_secPull]
    refine le_bot_iff.1 fun z hz => ?_
    have hz' : redι Z z ∈ (Z : Set X) := by
      rw [← range_redι Z]
      exact Set.mem_range_self z
    exact hb _ _ hz' hz
  · obtain ⟨a, ha', hya'⟩ := Set.mem_iUnion₂.1 (hT hy)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hg.ge (Set.mem_univ y))
    refine ⟨e (⟨a, ha'⟩, j), ?_⟩
    show y ∈ nonzeroLocus (κ' (e.symm (e (⟨a, ha'⟩, j))))
    rw [e.symm_apply_apply, hκ']
    exact ⟨hya', hj⟩

end GlobalTheory.CutOutSections
