import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPhiGammaModelCharacterEqStandardStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPhiGammaModelExtensionCocyclePairStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCoboundariesOfHerrPairCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleSplitOfContracting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleLetterDataWindowArithmetic

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.CharSplit

/- English proof (translation)
Introduce `k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 e he1 het z hz`. Take `⟨N, b, g, hmod, hrep, hzz⟩` from `GlobalTheory.T.exists_phiGammaModel_extension_cocycle_pair F M h1 h2 h3 _ z hz`. Establish `hN : N = M.Nχ e` using `GlobalTheory.T.twistedPhiGammaModel_character_eq_standard F M h1 h2 h3 e (by omega) het N hmod`. Substitute `hN` using the available equality. Apply `GlobalTheory.T.mem_coboundaries_of_herrPair_coboundary F _ z b g hrep` to reduce the goal to its premises.

Establish `hlat` using `fun i => M.χ_lat e (by omega) het i`. Use `set J : ZMod n → ℕ := fun i => if Dt.ty i = LType.G then (Dt.w i).toNat else (Dt.wst i - e).toNat with hJ`. Establish `hJG : ∀ i, Dt.ty i = LType.G → J i = (Dt.w i).toNat` using `fun i h => by simp [hJ, h]`. Establish `hJB : ∀ i, Dt.ty i = LType.Bd → J i = (Dt.wst i - e).toNat` using `fun i h => by simp [hJ, h]`. Establish `hsmall : ∀ i (j : ℕ), j ≤ J i → e + (j : ℤ) < l`.

Introduce `i j hj`. Establish `hT` using `h1 i`. Establish `hw` using `GlobalTheory.WindowArith.windows (k := k) Dt h1 h2 h3 i`. Consider the cases of `hty : Dt.ty i with`. Consider the case `G`.

Take `⟨-, -, hw1, hw2⟩` from `hw.2.2.1 hty`. Rewrite `hj` using `[hJG i hty]`. Use linear arithmetic over natural numbers and integers. Consider the case `Bd`. Take `⟨-, -, hb1, hb2⟩` from `hw.2.2.2 hty`.

Rewrite `hj` using `[hJB i hty]`. Use linear arithmetic over natural numbers and integers. Take `⟨m, -, hm⟩` from `GlobalTheory.PhiGam.cocycle_split_of_contracting R (F.D (chr (M.ω ^ (-e)))) (M.Nχ e) J (fun i => (hlat i).1) (fun i => (hlat i).2.1) (fun i => by rw [(hlat i).2.2.1]; exact sh_le_sh_of_le he1 _) (fun i j hj1 hjJ => by`. Rewrite using `[(hlat i).2.2.2]`. Unfold `resCount`.

Simplify using `only [Multiset.card_eq_zero, Multiset.filter_eq_nil, Multiset.mem_singleton, forall_eq]`. Introduce `hcast`. Establish `h0 : ((e + (j : ℤ) : ℤ) : k) = 0`. Move the coercions through the operations in `at hcast ⊢`. Take the linear combination `hcast`.

Rewrite `h0` using `[CharP.intCast_eq_zero_iff k l]`. Establish `hle` using `Int.le_of_dvd (by omega) h0`. Use `hsmall i j hjJ` as an intermediate fact. Use the proof step `omega)`. Use `b g (fun i => (hzz i).1) (fun i => (hzz i).2.1)`.

Use the proof step `(fun i => by`. Establish `hw` using `GlobalTheory.WindowArith.windows (k := k) Dt h1 h2 h3 i`. Consider the cases of `hty : Dt.ty i with`. Consider the case `G`. Establish `hb` using `(hzz i).2.2.1 hty`.

Establish `h` using `(hw.2.2.1 hty).2.2.1`. Establish `hJi : ((J i : ℕ) : ℤ) = Dt.w i`. Rewrite using `[hJG i hty]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hJi]`.

Conclude with `hb`. Consider the case `Bd`. Establish `hb` using `((hzz i).2.2.2 hty).1`. Establish `h` using `(hw.2.2.2 hty).2.2.1`. Rewrite `hb` using `[(hlat i).2.2.1, sh_sh_eq]`.

Establish `hJi : -((J i : ℕ) : ℤ) = -Dt.wst i + e`. Rewrite using `[hJB i hty]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hJi]`. Conclude with `hb)`.

Rewrite using `[herrB_eq_range]`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[herrD_apply]`. Conclude with `Prod.ext (funext fun i => ((hm i).1).symm) (funext fun i => ((hm i).2).symm)`.
-/
theorem admissibleCocycle_negCharPower_mem_coboundaries : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), 1 ≤ e → e < Dt.t → ∀ z ∈ M.twistedModelAdmissibleCocycles (chr (M.ω ^ (-e))), z ∈ cob (chr (M.ω ^ (-e))) := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 e he1 het z hz
  obtain ⟨N, b, g, hmod, hrep, hzz⟩ := GlobalTheory.T.exists_phiGammaModel_extension_cocycle_pair F M h1 h2 h3 _ z hz
  have hN : N = M.Nχ e := GlobalTheory.T.twistedPhiGammaModel_character_eq_standard F M h1 h2 h3 e (by omega) het N hmod
  subst hN
  apply GlobalTheory.T.mem_coboundaries_of_herrPair_coboundary F _ z b g hrep

  have hlat := fun i => M.χ_lat e (by omega) het i

  set J : ZMod n → ℕ := fun i =>
    if Dt.ty i = LType.G then (Dt.w i).toNat else (Dt.wst i - e).toNat with hJ
  have hJG : ∀ i, Dt.ty i = LType.G → J i = (Dt.w i).toNat := fun i h => by simp [hJ, h]
  have hJB : ∀ i, Dt.ty i = LType.Bd → J i = (Dt.wst i - e).toNat := fun i h => by simp [hJ, h]

  have hsmall : ∀ i (j : ℕ), j ≤ J i → e + (j : ℤ) < l := by
    intro i j hj
    have hT := h1 i
    have hw := GlobalTheory.WindowArith.windows (k := k) Dt h1 h2 h3 i
    cases hty : Dt.ty i with
    | G =>
      obtain ⟨-, -, hw1, hw2⟩ := hw.2.2.1 hty
      rw [hJG i hty] at hj
      omega
    | Bd =>
      obtain ⟨-, -, hb1, hb2⟩ := hw.2.2.2 hty
      rw [hJB i hty] at hj
      omega
  obtain ⟨m, -, hm⟩ := GlobalTheory.PhiGam.cocycle_split_of_contracting R (F.D (chr (M.ω ^ (-e)))) (M.Nχ e) J
    (fun i => (hlat i).1) (fun i => (hlat i).2.1)
    (fun i => by rw [(hlat i).2.2.1]; exact sh_le_sh_of_le he1 _)
    (fun i j hj1 hjJ => by
      rw [(hlat i).2.2.2]
      unfold resCount
      classical
      simp only [Multiset.card_eq_zero, Multiset.filter_eq_nil, Multiset.mem_singleton, forall_eq]
      intro hcast
      have h0 : ((e + (j : ℤ) : ℤ) : k) = 0 := by
        push_cast at hcast ⊢
        linear_combination hcast
      rw [CharP.intCast_eq_zero_iff k l] at h0
      have hle := Int.le_of_dvd (by omega) h0
      have := hsmall i j hjJ
      omega)
    b g (fun i => (hzz i).1) (fun i => (hzz i).2.1)
    (fun i => by
      have hw := GlobalTheory.WindowArith.windows (k := k) Dt h1 h2 h3 i
      cases hty : Dt.ty i with
      | G =>
        have hb := (hzz i).2.2.1 hty
        have h := (hw.2.2.1 hty).2.2.1
        have hJi : ((J i : ℕ) : ℤ) = Dt.w i := by
          rw [hJG i hty]
          omega
        rw [hJi]
        exact hb
      | Bd =>
        have hb := ((hzz i).2.2.2 hty).1
        have h := (hw.2.2.2 hty).2.2.1
        rw [(hlat i).2.2.1, sh_sh_eq] at hb
        have hJi : -((J i : ℕ) : ℤ) = -Dt.wst i + e := by
          rw [hJB i hty]
          omega
        rw [hJi]
        exact hb)
  rw [herrB_eq_range]
  refine ⟨m, ?_⟩
  rw [herrD_apply]
  exact Prod.ext (funext fun i => ((hm i).1).symm) (funext fun i => ((hm i).2).symm)

end GlobalTheory.CharSplit
