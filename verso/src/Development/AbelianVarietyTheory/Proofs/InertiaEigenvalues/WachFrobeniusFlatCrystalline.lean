import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingsCyclotomic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiFree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.PhiFlat

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

/- English proof (translation)
Rewrite using `[← algebraMap_smul W.EE a y, W.φD_smul, W.φE_ext, algebraMap_smul]`. Both sides reduce to the same expression.
-/
theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (y : W.DD T) :
    W.φD T (a • y) = W.φA a • W.φD T y := by
  rw [← algebraMap_smul W.EE a y, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

/- English proof (translation)
Use `set S := Submodule.span W.EE (Set.range fun j => W.φD T (bN j)) with hS`. Establish `hA : Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))) ≤ S.restrictScalars (LetA O n)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Establish `hy' : y = ∑ m, bN.repr ⟨y, hy⟩ m • (bN m : W.DD T)`.

Establish `h0` using `congrArg Subtype.val (bN.sum_repr ⟨y, hy⟩)`. Rewrite `h0` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at h0`. Conclude with `h0.symm`. Rewrite using `[hy', map_sum]`.

Use `Submodule.sum_mem _ fun m _ => ?_` and prove the remaining obligations. Rewrite using `[φD_smulA, ← algebraMap_smul W.EE, Submodule.restrictScalars_mem]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self m))`. Establish `hb : ∀ j, (bN j : W.DD T) ∈ S`. Introduce `j`.

Take `⟨k, hk⟩` from `W.N_φinv T (bN j) (bN j).2`. Express the relevant statement in the definitionally equal form `W.Q ^ k • (bN j : W.DD T) ∈ _ at hk`. Establish `h1` using `hA hk`. Rewrite `h1` using `[Submodule.restrictScalars_mem]`. Take `⟨u, hu⟩` from `hQ.pow k`.

Establish `h2 : (bN j : W.DD T) = ((u⁻¹ : W.EEˣ) : W.EE) • (W.Q ^ k • (bN j : W.DD T))`. Rewrite using `[← algebraMap_smul W.EE (W.Q ^ k), smul_smul, map_pow, ← hu, Units.inv_mul, one_smul]`. Rewrite using `[h2]`. Conclude with `S.smul_mem _ h1`. Set `bD : Module.Basis (Fin r) W.EE (W.DD T)` to `(W.N_base T hT).basis bN`.

Establish `hbD : ∀ j, bD j = (bN j : W.DD T)` using `fun j => by simp [bD, IsBaseChange.basis_apply]`. Rewrite using `[eq_top_iff, ← bD.span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Rewrite using `[hbD]`. Conclude with `hb j`.
-/
theorem span_φ (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) {r : ℕ}
    (bN : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (hQ : IsUnit (algebraMap (LetA O n) W.EE W.Q)) :
    Submodule.span W.EE (Set.range fun j => W.φD T (bN j)) = ⊤ := by
  set S := Submodule.span W.EE (Set.range fun j => W.φD T (bN j)) with hS
  have hA : Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))) ≤ S.restrictScalars (LetA O n) := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y = ∑ m, bN.repr ⟨y, hy⟩ m • (bN m : W.DD T) := by
      have h0 := congrArg Subtype.val (bN.sum_repr ⟨y, hy⟩)
      rw [Submodule.coe_sum] at h0
      simp only [Submodule.coe_smul] at h0
      exact h0.symm
    rw [hy', map_sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [φD_smulA, ← algebraMap_smul W.EE, Submodule.restrictScalars_mem]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self m))
  have hb : ∀ j, (bN j : W.DD T) ∈ S := by
    intro j
    obtain ⟨k, hk⟩ := W.N_φinv T (bN j) (bN j).2
    change W.Q ^ k • (bN j : W.DD T) ∈ _ at hk
    have h1 := hA hk
    rw [Submodule.restrictScalars_mem] at h1
    obtain ⟨u, hu⟩ := hQ.pow k
    have h2 : (bN j : W.DD T) = ((u⁻¹ : W.EEˣ) : W.EE) • (W.Q ^ k • (bN j : W.DD T)) := by
      rw [← algebraMap_smul W.EE (W.Q ^ k), smul_smul, map_pow, ← hu, Units.inv_mul, one_smul]
    rw [h2]
    exact S.smul_mem _ h1
  let bD : Module.Basis (Fin r) W.EE (W.DD T) := (W.N_base T hT).basis bN
  have hbD : ∀ j, bD j = (bN j : W.DD T) := fun j => by simp [bD, IsBaseChange.basis_apply]
  rw [eq_top_iff, ← bD.span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  rw [hbD]
  exact hb j

/- English proof (translation)
Establish `hsp` using `span_φ W T hT bN hQ`. Set `c : Module.Basis (Fin r) W.EE (W.DD T)` to `basisOfTopLeSpanOfCardEqFinrank (fun j => W.φD T (bN j)) hsp.ge (by rw [hr, Fintype.card_fin])`. Establish `hli : LinearIndependent W.EE (fun j => W.φD T (bN j))`. Use `c.linearIndependent` as an intermediate fact. Rewrite `this` using `[coe_basisOfTopLeSpanOfCardEqFinrank]`. Then use the resulting hypothesis.

Use `set a : Fin l → Fin r → LetA O n := fun j m => bN.repr ⟨z j, hz j⟩ m with ha`. Establish `hzj : ∀ j, z j = ∑ m, a j m • (bN m : W.DD T)`. Introduce `j`. Establish `h0` using `congrArg Subtype.val (bN.sum_repr ⟨z j, hz j⟩)`. Rewrite `h0` using `[Submodule.coe_sum]`.

Simplify using `only [Submodule.coe_smul] at h0`. Conclude with `h0.symm`. Use `set e : Fin l → LetA O n := fun j => fun _ => ((1 : PowerSeries O) + PowerSeries.X) ^ (j : ℕ) with he`. Establish `hexp : ∑ m, algebraMap (LetA O n) W.EE (∑ j, e j * W.φA (a j m)) • W.φD T (bN m) = 0`. Rewrite using `[← hsum]`.

Repeatedly rewrite using `[algebraMap_smul, hzj, map_sum, φD_smulA, Finset.smul_sum, smul_smul, Finset.sum_smul]`. Conclude with `Finset.sum_comm`. Establish `hc : ∀ m, ∑ j, e j * W.φA (a j m) = 0`. Introduce `m`. Use `Fintype.linearIndependent_iff.1 hli _ hexp m` as an intermediate fact.

Conclude with `W.EE_inj (by rw [this, map_zero])`. Establish `hzero : ∀ j m, a j m = 0`. Introduce `j m`. Use function extensionality and compare the values at `k`. Establish `h1` using `congrFun (hc m) (k + 1)`.

Simplify using `only [Finset.sum_apply, Pi.mul_apply, he, LocWach.φA, letφ, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply, add_sub_cancel_right, Pi.zero_apply] at h1`. Conclude with `congrFun (hφ₀ (fun j => a j m k) h1) j`. Introduce `j`. Rewrite using `[hzj j]`. Simplify using `[hzero]`.
-/
theorem phi_flat (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) {r : ℕ}
    (bN : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (hQ : IsUnit (algebraMap (LetA O n) W.EE W.Q))
    [Nontrivial W.EE] (hr : Module.finrank W.EE (W.DD T) = r) (l : ℕ)
    (hφ₀ : ∀ w : Fin l → PowerSeries O, ∑ j : Fin l, (1 + PowerSeries.X) ^ (j : ℕ) * W.φ₀ (w j) = 0 → w = 0)
    (z : Fin l → W.DD T) (hz : ∀ j, z j ∈ W.N T)
    (hsum : ∑ j : Fin l, (fun _ => ((1 : PowerSeries O) + PowerSeries.X) ^ (j : ℕ) : LetA O n) • W.φD T (z j) = 0) :
    ∀ j, z j = 0 := by
  have hsp := span_φ W T hT bN hQ
  let c : Module.Basis (Fin r) W.EE (W.DD T) :=
    basisOfTopLeSpanOfCardEqFinrank (fun j => W.φD T (bN j)) hsp.ge (by rw [hr, Fintype.card_fin])
  have hli : LinearIndependent W.EE (fun j => W.φD T (bN j)) := by
    have := c.linearIndependent
    rwa [coe_basisOfTopLeSpanOfCardEqFinrank] at this
  set a : Fin l → Fin r → LetA O n := fun j m => bN.repr ⟨z j, hz j⟩ m with ha
  have hzj : ∀ j, z j = ∑ m, a j m • (bN m : W.DD T) := by
    intro j
    have h0 := congrArg Subtype.val (bN.sum_repr ⟨z j, hz j⟩)
    rw [Submodule.coe_sum] at h0
    simp only [Submodule.coe_smul] at h0
    exact h0.symm
  set e : Fin l → LetA O n := fun j => fun _ => ((1 : PowerSeries O) + PowerSeries.X) ^ (j : ℕ) with he
  have hexp : ∑ m, algebraMap (LetA O n) W.EE (∑ j, e j * W.φA (a j m)) • W.φD T (bN m) = 0 := by
    rw [← hsum]
    simp_rw [algebraMap_smul, hzj, map_sum, φD_smulA, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hc : ∀ m, ∑ j, e j * W.φA (a j m) = 0 := by
    intro m
    have := Fintype.linearIndependent_iff.1 hli _ hexp m
    exact W.EE_inj (by rw [this, map_zero])
  have hzero : ∀ j m, a j m = 0 := by
    intro j m
    funext k
    have h1 := congrFun (hc m) (k + 1)
    simp only [Finset.sum_apply, Pi.mul_apply, he, LocWach.φA, letφ, AlgHom.pi_apply, AlgHom.comp_apply,
      Pi.evalAlgHom_apply, add_sub_cancel_right, Pi.zero_apply] at h1
    exact congrFun (hφ₀ (fun j => a j m k) h1) j
  intro j
  rw [hzj j]
  simp [hzero]

end Generic

end GlobalTheory.NL.PhiFlat

namespace GlobalTheory.NL.PhiFlat

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `D HW F l _ K s LL h W T hT z hz hsum`. Take `⟨bN⟩` from `GlobalTheory.NL.N_basis D HW F l K s LL h T hT`. Establish `hQ : IsUnit (algebraMap (AA K LL) W.EE W.Q)`. Use `((GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.2.2 0).2` as an intermediate fact. Rewrite `this` using `[pow_zero, AlgHom.one_apply]`.

Conclude with `this`. Take `⟨χ, -, hφ, -⟩` from `GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h`. Take `⟨hdvr, hcpl, hnu⟩` from `GlobalTheory.FinExtIntegers.dvr_complete LL`. Establish `hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0`. Introduce `h0`.

Use `congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0` as an intermediate fact. Simplify using `[(Fact.out : l.Prime).ne_zero] at this`. Use `haveI : Nontrivial W.EE := ⟨⟨algebraMap (AA K LL) W.EE 0, algebraMap (AA K LL) W.EE 1, fun h0 => zero_ne_one (W.EE_inj h0)⟩⟩`. Use `GlobalTheory.NL.PhiFlat.phi_flat W T hT bN hQ (W.DD_free T).2 l ?_ z hz hsum` and prove the remaining obligations. Introduce `w hw`.

Take `⟨y, -, huniq⟩` from `GlobalTheory.Cyc.phi_free l (↥(OL LL)) hl0 hnu 0`. Rewrite `hw` using `[hφ]`. Establish `e1` using `huniq w hw.symm`. Establish `e2` using `huniq 0 (by simp)`. Rewrite using `[e1, e2]`.
-/
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ z : Fin l → W.DD T, (∀ j, z j ∈ W.N T) → ∑ j : Fin l, (fun _ => ((1 : PowerSeries ↥(OL LL)) + PowerSeries.X) ^ (j : ℕ) : AA K LL) • W.φD T (z j) = 0 → ∀ j, z j = 0 := by
  intro D HW F l _ K s LL h W T hT z hz hsum
  obtain ⟨bN⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  have hQ : IsUnit (algebraMap (AA K LL) W.EE W.Q) := by
    have := ((GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.2.2 0).2
    rw [pow_zero, AlgHom.one_apply] at this
    exact this
  obtain ⟨χ, -, hφ, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  obtain ⟨hdvr, hcpl, hnu⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
    simp [(Fact.out : l.Prime).ne_zero] at this
  haveI : Nontrivial W.EE :=
    ⟨⟨algebraMap (AA K LL) W.EE 0, algebraMap (AA K LL) W.EE 1, fun h0 => zero_ne_one (W.EE_inj h0)⟩⟩
  refine GlobalTheory.NL.PhiFlat.phi_flat W T hT bN hQ (W.DD_free T).2 l ?_ z hz hsum
  intro w hw
  obtain ⟨y, -, huniq⟩ := GlobalTheory.Cyc.phi_free l (↥(OL LL)) hl0 hnu 0
  rw [hφ] at hw
  have e1 := huniq w hw.symm
  have e2 := huniq 0 (by simp)
  rw [e1, e2]

end GlobalTheory.NL.PhiFlat
