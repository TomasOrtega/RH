import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NegGram
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryGroupNegFormCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegDefiniteSelfDualStabilizerVolumeOneStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianSpaceOppositeFormSignatureConditionStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeStabilizerDoubleCosetsClassRestMassStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NegVol

open Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold

variable {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') {Γ K : Subgroup G} {Γ' K' : Subgroup G'}
  (hΓ : ∀ h, h ∈ Γ ↔ φ h ∈ Γ') (hK : ∀ h, h ∈ K ↔ φ h ∈ K')

def stabEquiv (g' : G') : stab Γ K (φ.symm g') ≃ stab Γ' K' g' where
  toFun γ := ⟨⟨φ γ.1, (hΓ _).mp γ.1.2⟩, by
    have h := (hK _).mp γ.2
    simp only [stab, Set.mem_setOf_eq] at h ⊢
    simpa [map_mul, map_inv] using h⟩
  invFun γ := ⟨⟨φ.symm γ.1, (hΓ _).mpr (by simpa using γ.1.2)⟩, by
    have h := γ.2
    simp only [stab, Set.mem_setOf_eq] at h ⊢
    rw [hK]
    simpa [map_mul, map_inv] using h⟩
  left_inv γ := by ext; simp
  right_inv γ := by ext; simp

include hΓ hK in
/- English proof (translation)
Use `⟨fun x => ?_, fun i j γ γ' k k' h => ?_, fun i => ?_, fun i => Nat.card_congr (stabEquiv φ hΓ hK (g' i))⟩` and prove the remaining obligations. Take `⟨i, γ, k, hx⟩` from `hcov (φ x)`. Use `⟨i, ⟨φ.symm γ, (hΓ _).mpr (by simpa using γ.2)⟩, ⟨φ.symm k, (hK _).mpr (by simpa using k.2)⟩, ?_⟩` and prove the remaining obligations. Apply `φ.injective` to reduce the goal to its premises. Simplify using `[map_mul, hx]`.

Use `hdisj i j ⟨φ γ, (hΓ _).mp γ.2⟩ ⟨φ γ', (hΓ _).mp γ'.2⟩ ⟨φ k, (hK _).mp k.2⟩ ⟨φ k', (hK _).mp k'.2⟩ ?_` and prove the remaining obligations. Use `congrArg φ h` as an intermediate fact. Simplify `this` using `[map_mul]`. Use `(hfin i).to_subtype` as an intermediate fact. Conclude with `Set.finite_coe_iff.mp (Finite.of_equiv _ (stabEquiv φ hΓ hK (g' i)).symm)`.
-/
theorem transport {ι : Type*} (g' : ι → G')
    (hcov : ∀ x : G', ∃ i, ∃ γ : Γ', ∃ k : K', x = (γ : G') * g' i * k)
    (hdisj : ∀ i j (γ γ' : Γ') (k k' : K'), (γ : G') * g' i * k = (γ' : G') * g' j * k' → i = j)
    (hfin : ∀ i, (stab Γ' K' (g' i)).Finite) :
    (∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * φ.symm (g' i) * k) ∧
    (∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * φ.symm (g' i) * k = (γ' : G) * φ.symm (g' j) * k' → i = j) ∧
    (∀ i, (stab Γ K (φ.symm (g' i))).Finite) ∧
    (∀ i, Nat.card (stab Γ K (φ.symm (g' i))) = Nat.card (stab Γ' K' (g' i))) := by
  refine ⟨fun x => ?_, fun i j γ γ' k k' h => ?_, fun i => ?_, fun i => Nat.card_congr (stabEquiv φ hΓ hK (g' i))⟩
  · obtain ⟨i, γ, k, hx⟩ := hcov (φ x)
    refine ⟨i, ⟨φ.symm γ, (hΓ _).mpr (by simpa using γ.2)⟩, ⟨φ.symm k, (hK _).mpr (by simpa using k.2)⟩, ?_⟩
    apply φ.injective
    simp [map_mul, hx]
  · refine hdisj i j ⟨φ γ, (hΓ _).mp γ.2⟩ ⟨φ γ', (hΓ _).mp γ'.2⟩ ⟨φ k, (hK _).mp k.2⟩ ⟨φ k', (hK _).mp k'.2⟩ ?_
    have := congrArg φ h
    simpa [map_mul] using this
  · have := (hfin i).to_subtype
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ (stabEquiv φ hΓ hK (g' i)).symm)

end GlobalTheory.NegVol

namespace GlobalTheory.NegVol

/- English proof (translation)
Introduce `D hT W n hW hsig`. Use `set W' := GlobalTheory.NegSpace.neg W with hW'def`. Establish `hW' : W'.SigOK` using `GlobalTheory.T.hermitianSpaceOppositeForm_signatureCondition _ W hW`. Establish `hn : n = W.rank`. Use `Formalism.BasicNotions.sig_sum W hW D.host.φ₀` as an intermediate fact.

Rewrite `this` using `[hsig]`. Simplify using `using this`. Establish `hsig' : ∀ τ, W'.sig τ = (W'.rank, 0)`. Introduce `τ`. Rewrite using `[GlobalTheory.NegSpace.neg_sig, hsig τ, GlobalTheory.NegSpace.neg_rank, ← hn]`.

Take `⟨⟨μ, hμ⟩, hall⟩` from `hT W 0 n hW hsig`. Take `⟨⟨𝓕, h𝓕⟩, hF⟩` from `hall μ hμ`. Take `⟨⟨μ', hμ'⟩, hall'⟩` from `hT W' W'.rank 0 hW' hsig'`. Take `⟨⟨𝓕', h𝓕'⟩, hF'⟩` from `hall' μ' hμ'`. Take `⟨φ, -, hΓ, hS⟩` from `GlobalTheory.T.unitaryGroup_neg_form_compatible D.host.F D.host.E D.sp.cm.sig W.rank W.gram (-W.gram) rfl`.

Take `⟨m, g', hcov', hdisj', -⟩` from `GlobalTheory.T.lattice_stabilizer_doubleCosets_classRest_mass D W' hW' hsig'`. Establish `hfin' : ∀ i, (Unfold.stab (GamA D W') (StabFin.SFin D.sp.cm.sig W'.gram (L0c D W')) (g' i)).Finite` using `fun i => StabFin.stab_finite W' D.sp.cm.sig (fun _ => rfl) (fun τ => D.sp.cm.cmUnram.2.1 τ) hW' hsig' _ (fun k hk y hy => (hk y).mp hy) (g' i)`. Take `⟨hcov, hdisj, hfin, hcard⟩` from `transport φ.toMulEquiv (Γ := GamA D W) (K := StabFin.SFin D.sp.cm.sig W.gram (L0c D W)) (Γ' := (GamA D W' : Subgroup (HA (AF D.host.F) D.sp.cm.sig (-W.gram)))) (K' := (StabFin.SFin D.sp.cm.sig W'.gram (L0c D W') : Subgroup (HA (AF D.host.F) D.sp.cm.sig (-W.gram)))) hΓ (hS _) g' h …`. Establish `hK1 : μ (StabFin.SFin D.sp.cm.sig W.gram (L0c D W) : Set _) = 1` using `GlobalTheory.T.negDefinite_selfDualStabilizer_volume_one D W n hW hsig μ hμ`. Take `⟨θ, hθ⟩` from `hμ'.2.1`.

Take `⟨A, hA⟩` from `(hμ'.2.2 θ hθ).1`. Establish `hK1' : μ' (StabFin.SFin D.sp.cm.sig W'.gram (L0c D W') : Set _) = 1`. Establish `hK : KSub D W' W'.rank 0 θ A = StabFin.SFin D.sp.cm.sig W'.gram (L0c D W')` using `SetLike.coe_injective (StabFin.KSub_eq D W' hW' hsig' θ hθ A hA)`. Rewrite using `[← hK]`. Conclude with `measure_KSub D W' W'.rank μ' hμ' θ hθ A hA`.

Use `Unfold.borelHA D.sp.cm.sig W.gram` as an intermediate fact. Use `Unfold.borelHA D.sp.cm.sig W'.gram` as an intermediate fact. Use `haveI := hμ.1`. Use `haveI := hμ'.1`. Use `haveI := Unfold.measurableMulHA D.sp.cm.sig W.gram`.

Use `haveI := Unfold.measurableMulHA D.sp.cm.sig W'.gram`. Use `haveI : Countable (GamA D W) := Unfold.countableGamma D.sp.cm.sig W.gram`. Use `haveI : Countable (GamA D W') := Unfold.countableGamma D.sp.cm.sig W'.gram`. Establish `e` using `Unfold.measure_fd_toReal μ (StabFin.isOpen_SFin W D.sp.cm.sig).measurableSet hK1 _ hcov hdisj hfin h𝓕`. Establish `e'` using `Unfold.measure_fd_toReal μ' (StabFin.isOpen_SFin W' D.sp.cm.sig).measurableSet hK1' g' hcov' hdisj' hfin' h𝓕'`.

Rewrite `e` using `[hF 𝓕 h𝓕, ENNReal.toReal_ofReal (D.vol_pos W).le]`. Rewrite `e'` using `[hF' 𝓕' h𝓕', ENNReal.toReal_ofReal (D.vol_pos W').le]`. Rewrite using `[e, e']`. Conclude with `Finset.sum_congr rfl fun i _ => congrArg (fun k : ℕ => ((k : ℝ))⁻¹) (hcard i)`.
-/
theorem vol_neg_eq : ∀ D : D7, VolTie D → ∀ (W : HSpace D.host.E) (n : ℕ), W.SigOK → (∀ τ, W.sig τ = (0, n)) →
    D.vol W = D.vol (GlobalTheory.NegSpace.neg W) := by
  intro D hT W n hW hsig
  set W' := GlobalTheory.NegSpace.neg W with hW'def
  have hW' : W'.SigOK := GlobalTheory.T.hermitianSpaceOppositeForm_signatureCondition _ W hW
  have hn : n = W.rank := by
    have := Formalism.BasicNotions.sig_sum W hW D.host.φ₀
    rw [hsig] at this; simpa using this
  have hsig' : ∀ τ, W'.sig τ = (W'.rank, 0) := by
    intro τ
    rw [GlobalTheory.NegSpace.neg_sig, hsig τ, GlobalTheory.NegSpace.neg_rank, ← hn]

  obtain ⟨⟨μ, hμ⟩, hall⟩ := hT W 0 n hW hsig
  obtain ⟨⟨𝓕, h𝓕⟩, hF⟩ := hall μ hμ
  obtain ⟨⟨μ', hμ'⟩, hall'⟩ := hT W' W'.rank 0 hW' hsig'
  obtain ⟨⟨𝓕', h𝓕'⟩, hF'⟩ := hall' μ' hμ'

  obtain ⟨φ, -, hΓ, hS⟩ := GlobalTheory.T.unitaryGroup_neg_form_compatible D.host.F D.host.E D.sp.cm.sig W.rank W.gram (-W.gram) rfl

  obtain ⟨m, g', hcov', hdisj', -⟩ := GlobalTheory.T.lattice_stabilizer_doubleCosets_classRest_mass D W' hW' hsig'
  have hfin' : ∀ i, (Unfold.stab (GamA D W') (StabFin.SFin D.sp.cm.sig W'.gram (L0c D W')) (g' i)).Finite :=
    fun i => StabFin.stab_finite W' D.sp.cm.sig (fun _ => rfl) (fun τ => D.sp.cm.cmUnram.2.1 τ) hW' hsig' _
      (fun k hk y hy => (hk y).mp hy) (g' i)
  obtain ⟨hcov, hdisj, hfin, hcard⟩ := transport φ.toMulEquiv
    (Γ := GamA D W) (K := StabFin.SFin D.sp.cm.sig W.gram (L0c D W))
    (Γ' := (GamA D W' : Subgroup (HA (AF D.host.F) D.sp.cm.sig (-W.gram))))
    (K' := (StabFin.SFin D.sp.cm.sig W'.gram (L0c D W') : Subgroup (HA (AF D.host.F) D.sp.cm.sig (-W.gram)))) hΓ (hS _) g' hcov' hdisj' hfin'

  have hK1 : μ (StabFin.SFin D.sp.cm.sig W.gram (L0c D W) : Set _) = 1 := GlobalTheory.T.negDefinite_selfDualStabilizer_volume_one D W n hW hsig μ hμ
  obtain ⟨θ, hθ⟩ := hμ'.2.1
  obtain ⟨A, hA⟩ := (hμ'.2.2 θ hθ).1
  have hK1' : μ' (StabFin.SFin D.sp.cm.sig W'.gram (L0c D W') : Set _) = 1 := by
    have hK : KSub D W' W'.rank 0 θ A = StabFin.SFin D.sp.cm.sig W'.gram (L0c D W') :=
      SetLike.coe_injective (StabFin.KSub_eq D W' hW' hsig' θ hθ A hA)
    rw [← hK]; exact measure_KSub D W' W'.rank μ' hμ' θ hθ A hA
  have := Unfold.borelHA D.sp.cm.sig W.gram
  have := Unfold.borelHA D.sp.cm.sig W'.gram
  haveI := hμ.1
  haveI := hμ'.1
  haveI := Unfold.measurableMulHA D.sp.cm.sig W.gram
  haveI := Unfold.measurableMulHA D.sp.cm.sig W'.gram
  haveI : Countable (GamA D W) := Unfold.countableGamma D.sp.cm.sig W.gram
  haveI : Countable (GamA D W') := Unfold.countableGamma D.sp.cm.sig W'.gram
  have e := Unfold.measure_fd_toReal μ (StabFin.isOpen_SFin W D.sp.cm.sig).measurableSet hK1 _ hcov hdisj hfin h𝓕
  have e' := Unfold.measure_fd_toReal μ' (StabFin.isOpen_SFin W' D.sp.cm.sig).measurableSet hK1' g' hcov' hdisj'
    hfin' h𝓕'
  rw [hF 𝓕 h𝓕, ENNReal.toReal_ofReal (D.vol_pos W).le] at e
  rw [hF' 𝓕' h𝓕', ENNReal.toReal_ofReal (D.vol_pos W').le] at e'
  rw [e, e']
  exact Finset.sum_congr rfl fun i _ => congrArg (fun k : ℕ => ((k : ℝ))⁻¹) (hcard i)

end GlobalTheory.NegVol
