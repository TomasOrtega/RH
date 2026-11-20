import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolMulPosLeConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLatticeStabilizerNormalisingSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PowEqZeroOfMemHermitianFrameUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeStabilizerCommensurableUnramifiedHermitiaStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CongruenceSubgroupLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarInvVolumeConjModularCharacterStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentStabilizesSomeLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeStabilizerInfLeConjNormalisingSubgroupStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[Subgroup.mem_pointwise_smul_iff_inv_smul_mem]`. Simplify using `only [MulAut.smul_def, MulAut.conj_inv_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Use `H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Introduce `hx`. Conclude with `H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh`.
-/
theorem volSt_conj_self {G : Type} [Group G] (H : Subgroup G) {h : G} (hh : h ∈ H) :
    MulAut.conj h • H = H := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply]
  constructor
  · intro hx
    have := H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)
    simpa [mul_assoc] using this
  · intro hx
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh

/- English proof (translation)
Rewrite using `[Subgroup.smul_inf, volSt_conj_self H hh]`. Use `congr 1`. Use extensionality with `g`. Rewrite using `[Subgroup.mem_pointwise_smul_iff_inv_smul_mem]`. Simplify using `only [MulAut.smul_def, MulAut.conj_inv_apply, MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]`.
-/
theorem volSt_inf_stab_smul {G X : Type} [Group G] [MulAction G X] (H : Subgroup G) {h : G} (hh : h ∈ H)
    (x : X) : H ⊓ MulAction.stabilizer G (h • x) = MulAut.conj h • (H ⊓ MulAction.stabilizer G x) := by
  rw [Subgroup.smul_inf, volSt_conj_self H hh]
  congr 1
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply, MulAction.mem_stabilizer_iff, mul_smul,
    inv_smul_eq_iff]

/- English proof (translation)
Take `⟨Λ1, hΛ1, hK0, -⟩` from `GlobalTheory.T.exists_lattice_stabilizer_normalising_subgroup L r k S 1 S.N.one_mem 1 S.N'.one_mem`. Establish `hK : S.K0 = S.St ⊓ stabL L Λ1` using `hK0.symm`. Establish `hc : ∀ Λ, IsLat L Λ → S.K0.relIndex (S.St ⊓ stabL L Λ) ≠ 0 ∧ (S.St ⊓ stabL L Λ).relIndex S.K0 ≠ 0`. Introduce `Λ hΛ`. Rewrite using `[hK]`.

Conclude with `⟨(GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ Λ1 hΛ hΛ1 S.St).1, (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ1 Λ hΛ1 hΛ S.St).1⟩`. Establish `hconj : ∀ h ∈ S.St, S.K0.relIndex (MulAut.conj h • S.K0) ≠ 0 ∧ (MulAut.conj h • S.K0).relIndex S.K0 ≠ 0`. Introduce `h hh`. Establish `e : MulAut.conj h • S.K0 = S.St ⊓ stabL L (h • Λ1)`. Rewrite using `[hK]`.

Conclude with `(volSt_inf_stab_smul S.St hh Λ1).symm`. Rewrite using `[e]`. Conclude with `hc _ ((GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ1 Λ1 hΛ1 hΛ1 S.St).2 h).1`. Establish `hle : S.K0 ≤ S.St` using `by rw [hK]; exact inf_le_left`. Establish `hmod` using `(GlobalTheory.T.haarInvVolume_conj_modular_character S.St S.K0 hle hconj).2.2.2`.

Establish `hone : ∀ h ∈ S.St, invVol S.K0 (MulAut.conj h • S.K0) = 1`. Introduce `h hh`. Take `⟨Λ, hΛ, hs⟩` from `GlobalTheory.T.unipotent_stabilizes_some_lattice L h _ (GlobalTheory.T.pow_eq_zero_of_mem_hermitianFrameUnipotent L r k S h hh.1)`. Conclude with `(hmod _ (hc Λ hΛ).1 (hc Λ hΛ).2 h hh).2 (volSt_conj_self _ ⟨hh, hs⟩)`. Establish `hinv : ∀ K' : Subgroup S.GLV, S.K0.relIndex K' ≠ 0 → K'.relIndex S.K0 ≠ 0 → ∀ h ∈ S.St, invVol S.K0 (MulAut.conj h • K') = invVol S.K0 K'`.

Introduce `K' h1 h2 h hh`. Rewrite using `[(hmod K' h1 h2 h hh).1, hone h hh, one_mul]`. Use `⟨fun Λ hΛ => ⟨(hc Λ hΛ).1, (hc Λ hΛ).2, fun h hh => ?_⟩, ?_⟩` and prove the remaining obligations. Unfold `Frames.mu`. Rewrite using `[volSt_inf_stab_smul S.St hh Λ]`.

Conclude with `hinv _ (hc Λ hΛ).1 (hc Λ hΛ).2 h hh`. Introduce and unpack `C ⟨n, hn, n', hn', hC⟩`. Take `⟨Λ, hΛ, e1, e2, e3⟩` from `GlobalTheory.T.exists_lattice_stabilizer_normalising_subgroup L r k S n hn n' hn'`. Rewrite `e2`, `e3` using `[← hC]`. Take `⟨⟨K, hKm, hKi, -⟩, -⟩` from `GlobalTheory.T.congruence_subgroup_lattice_stabilizer L S.ϖ S.ϖ_irr Λ hΛ 1`.

Establish `a1 : S.K0.relIndex (S.St ⊓ MulAction.stabilizer S.GLV C) ≠ 0` using `fun h0 => (hc Λ hΛ).1 (Subgroup.relIndex_eq_zero_of_le_right e2 h0)`. Establish `b1 : K.relIndex (S.St ⊓ stabL L Λ) ≠ 0` using `fun h0 => hKi (Subgroup.relIndex_eq_zero_of_le_right inf_le_right h0)`. Establish `b2 : (K ⊓ (S.St ⊓ stabL L Λ)) ≤ S.St ⊓ MulAction.stabilizer S.GLV C` using `fun g hg => ⟨hg.2.1, e3 g hg.2 ((hKm g).1 hg.1).2⟩`. Establish `b3 : (S.St ⊓ MulAction.stabilizer S.GLV C).relIndex (S.St ⊓ stabL L Λ) ≠ 0`. Introduce `h0`.

Use `Subgroup.relIndex_eq_zero_of_le_left b2 h0` as an intermediate fact. Rewrite `this` using `[Subgroup.inf_relIndex_right]`. Conclude with `b1 this`. Establish `a2 : (S.St ⊓ MulAction.stabilizer S.GLV C).relIndex S.K0 ≠ 0` using `Subgroup.relIndex_ne_zero_trans b3 (hc Λ hΛ).2`. Use `⟨a1, a2, ?_, fun h hh => ?_⟩` and prove the remaining obligations.

Take `⟨h, hh, hw, -⟩` from `GlobalTheory.T.latticeStabilizer_inf_le_conj_normalisingSubgroup L r k S n hn`. Establish `c1 : S.St ⊓ MulAction.stabilizer S.GLV C ≤ MulAut.conj h • S.K0` using `e2.trans (e1.le.trans (inf_le_left.trans hw))`. Establish `c2` using `(invVol_mul_pos_le_conj S.K0 (MulAut.conj h • S.K0) _ (hconj h hh).1 (hconj h hh).2 a1 a2).2.2.1 c1`. Establish `c3` using `Subgroup.relIndex_ne_zero_trans a2 (hconj h hh).1`. Unfold `Frames.wC`.

Rewrite using `[c2, hone h hh, one_mul]`. Conclude with `Nat.one_le_iff_ne_zero.2 c3` after adjusting the coercions. Unfold `Frames.wC`. Rewrite using `[volSt_inf_stab_smul S.St hh C]`. Conclude with `hinv _ a1 a2 h hh`.
-/
theorem volSt {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)
    (r k : ℕ) (S : Frames L r k) :
    (∀ Λ, IsLat L Λ → S.K0.relIndex (S.St ⊓ MulAction.stabilizer S.GLV Λ) ≠ 0 ∧
      (S.St ⊓ MulAction.stabilizer S.GLV Λ).relIndex S.K0 ≠ 0 ∧ ∀ h ∈ S.St, S.mu (h • Λ) = S.mu Λ) ∧
    ∀ C, S.IsCls C → S.K0.relIndex (S.St ⊓ MulAction.stabilizer S.GLV C) ≠ 0 ∧
      (S.St ⊓ MulAction.stabilizer S.GLV C).relIndex S.K0 ≠ 0 ∧ 1 ≤ S.wC C ∧
      ∀ h ∈ S.St, S.wC (h • C) = S.wC C := by
  obtain ⟨Λ1, hΛ1, hK0, -⟩ := GlobalTheory.T.exists_lattice_stabilizer_normalising_subgroup L r k S 1 S.N.one_mem 1 S.N'.one_mem
  have hK : S.K0 = S.St ⊓ stabL L Λ1 := hK0.symm
  have hc : ∀ Λ, IsLat L Λ → S.K0.relIndex (S.St ⊓ stabL L Λ) ≠ 0 ∧
      (S.St ⊓ stabL L Λ).relIndex S.K0 ≠ 0 := by
    intro Λ hΛ
    rw [hK]
    exact ⟨(GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ Λ1 hΛ hΛ1 S.St).1, (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ1 Λ hΛ1 hΛ S.St).1⟩
  have hconj : ∀ h ∈ S.St, S.K0.relIndex (MulAut.conj h • S.K0) ≠ 0 ∧
      (MulAut.conj h • S.K0).relIndex S.K0 ≠ 0 := by
    intro h hh
    have e : MulAut.conj h • S.K0 = S.St ⊓ stabL L (h • Λ1) := by
      rw [hK]; exact (volSt_inf_stab_smul S.St hh Λ1).symm
    rw [e]
    exact hc _ ((GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ1 Λ1 hΛ1 hΛ1 S.St).2 h).1
  have hle : S.K0 ≤ S.St := by rw [hK]; exact inf_le_left
  have hmod := (GlobalTheory.T.haarInvVolume_conj_modular_character S.St S.K0 hle hconj).2.2.2
  have hone : ∀ h ∈ S.St, invVol S.K0 (MulAut.conj h • S.K0) = 1 := by
    intro h hh
    obtain ⟨Λ, hΛ, hs⟩ := GlobalTheory.T.unipotent_stabilizes_some_lattice L h _ (GlobalTheory.T.pow_eq_zero_of_mem_hermitianFrameUnipotent L r k S h hh.1)
    exact (hmod _ (hc Λ hΛ).1 (hc Λ hΛ).2 h hh).2 (volSt_conj_self _ ⟨hh, hs⟩)
  have hinv : ∀ K' : Subgroup S.GLV, S.K0.relIndex K' ≠ 0 → K'.relIndex S.K0 ≠ 0 → ∀ h ∈ S.St,
      invVol S.K0 (MulAut.conj h • K') = invVol S.K0 K' := by
    intro K' h1 h2 h hh
    rw [(hmod K' h1 h2 h hh).1, hone h hh, one_mul]
  refine ⟨fun Λ hΛ => ⟨(hc Λ hΛ).1, (hc Λ hΛ).2, fun h hh => ?_⟩, ?_⟩
  · unfold Frames.mu
    rw [volSt_inf_stab_smul S.St hh Λ]
    exact hinv _ (hc Λ hΛ).1 (hc Λ hΛ).2 h hh
  rintro C ⟨n, hn, n', hn', hC⟩
  obtain ⟨Λ, hΛ, e1, e2, e3⟩ := GlobalTheory.T.exists_lattice_stabilizer_normalising_subgroup L r k S n hn n' hn'
  rw [← hC] at e2 e3
  obtain ⟨⟨K, hKm, hKi, -⟩, -⟩ := GlobalTheory.T.congruence_subgroup_lattice_stabilizer L S.ϖ S.ϖ_irr Λ hΛ 1
  have a1 : S.K0.relIndex (S.St ⊓ MulAction.stabilizer S.GLV C) ≠ 0 :=
    fun h0 => (hc Λ hΛ).1 (Subgroup.relIndex_eq_zero_of_le_right e2 h0)
  have b1 : K.relIndex (S.St ⊓ stabL L Λ) ≠ 0 :=
    fun h0 => hKi (Subgroup.relIndex_eq_zero_of_le_right inf_le_right h0)
  have b2 : (K ⊓ (S.St ⊓ stabL L Λ)) ≤ S.St ⊓ MulAction.stabilizer S.GLV C :=
    fun g hg => ⟨hg.2.1, e3 g hg.2 ((hKm g).1 hg.1).2⟩
  have b3 : (S.St ⊓ MulAction.stabilizer S.GLV C).relIndex (S.St ⊓ stabL L Λ) ≠ 0 := by
    intro h0
    have := Subgroup.relIndex_eq_zero_of_le_left b2 h0
    rw [Subgroup.inf_relIndex_right] at this
    exact b1 this
  have a2 : (S.St ⊓ MulAction.stabilizer S.GLV C).relIndex S.K0 ≠ 0 :=
    Subgroup.relIndex_ne_zero_trans b3 (hc Λ hΛ).2
  refine ⟨a1, a2, ?_, fun h hh => ?_⟩
  · obtain ⟨h, hh, hw, -⟩ := GlobalTheory.T.latticeStabilizer_inf_le_conj_normalisingSubgroup L r k S n hn
    have c1 : S.St ⊓ MulAction.stabilizer S.GLV C ≤ MulAut.conj h • S.K0 :=
      e2.trans (e1.le.trans (inf_le_left.trans hw))
    have c2 := (invVol_mul_pos_le_conj S.K0 (MulAut.conj h • S.K0) _ (hconj h hh).1 (hconj h hh).2
      a1 a2).2.2.1 c1
    have c3 := Subgroup.relIndex_ne_zero_trans a2 (hconj h hh).1
    unfold Frames.wC
    rw [c2, hone h hh, one_mul]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 c3
  · unfold Frames.wC
    rw [volSt_inf_stab_smul S.St hh C]
    exact hinv _ a1 a2 h hh

end GlobalTheory.HL
