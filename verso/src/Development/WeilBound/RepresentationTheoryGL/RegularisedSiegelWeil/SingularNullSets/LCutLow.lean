import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutLowB

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LCutLow

open GlobalTheory.CompanionTheory.PcFc (chn)

variable {D : D7} {n : ℕ}

/- English proof (translation)
Rewrite using `[AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 t)]`.
-/
theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (t : AF D.host.F) : conj (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 t)]

/- English proof (translation)
Introduce `γ hγ g` and use `by unfold cutR refine Finset.sum_congr rfl fun x _ => ?_ rw [mul_assoc, hinv γ hγ]`.
-/
theorem cutR_left {nb : hermA D n → G D n} {v : Pl D} (C : Cut D n v) {F : G D n → ℂ} (hinv : LeftInv (GF D n) F) :
    LeftInv (GF D n) (cutR nb C F) := fun γ hγ g => by
  unfold cutR
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_assoc, hinv γ hγ]

/- English proof (translation)
Unfold `cutR`. Conclude with `continuous_finsetSum _ fun x _ => continuous_const.mul (hF.comp (continuous_id.mul continuous_const))`.
-/
theorem cutR_cont {nb : hermA D n → G D n} {v : Pl D} (C : Cut D n v) {F : G D n → ℂ} (hF : Continuous F) :
    Continuous (cutR nb C F) := by
  unfold cutR
  exact continuous_finsetSum _ fun x _ => continuous_const.mul (hF.comp (continuous_id.mul continuous_const))

/- English proof (translation)
Unfold `cutR`. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Establish `e : g * k * nb x = g * nb x * ((nb x)⁻¹ * k * nb x)` using `by group`. Rewrite using `[e, hK _ (conj_mem_KAt hnb C hk hkv hx)]`.
-/
theorem cutR_lev {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (C : Cut D n v) {F : G D n → ℂ}
    (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g) {k : G D n} (hk : k ∈ lev nb C.s)
    (hkv : k ∈ atPts D.sp.cm.sig (Jst D n) {v}) (g : G D n) : cutR nb C F (g * k) = cutR nb C F g := by
  unfold cutR
  refine Finset.sum_congr rfl fun x hx => ?_
  have e : g * k * nb x = g * nb x * ((nb x)⁻¹ * k * nb x) := by group
  rw [e, hK _ (conj_mem_KAt hnb C hk hkv hx)]

/- English proof (translation)
Rewrite using `[fc_cutR hψ hC hF hinv C β hg]`. Distinguish the cases in `h : ∀ x : hermA D n, IntAt v x → pch ψ x.1 (rat β.1) = 1`. Rewrite using `[hkill β hβ h, zero_mul]`. Use `push Not at h`. Take `⟨x, hx, hne⟩` from `h`.

Establish `e` using `fc_fix hψ hC hinv hK β hx hg`. Establish `h0 : (1 - pch ψ x.1 (rat β.1)) * fc ψ lam 𝓖 nb F β g = 0` using `by rw [sub_mul, one_mul, ← e, sub_self]`. Rewrite using `[(mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 (Ne.symm hne)), mul_zero]`.
-/
theorem fc_cutR_low {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {nb : hermA D n → G D n}
    {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (hC : CoefData (D := D) (n := n) nb lam 𝓖) {F : G D n → ℂ}
    (hF : Continuous F) (hinv : LeftInv (GF D n) F) {v : Pl D} (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g)
    (C : Cut D n v) {r : ℕ} (hkill : C.Kills ψ r) (β : HermE D n) (hβ : β.1.rank < r) {g : G D n}
    (hg : proj D.sp.cm.sig (Jst D n) v g = 1) : fc ψ lam 𝓖 nb (cutR nb C F) β g = 0 := by
  rw [fc_cutR hψ hC hF hinv C β hg]
  by_cases h : ∀ x : hermA D n, IntAt v x → pch ψ x.1 (rat β.1) = 1
  · rw [hkill β hβ h, zero_mul]
  · push Not at h
    obtain ⟨x, hx, hne⟩ := h
    have e := fc_fix hψ hC hinv hK β hx hg
    have h0 : (1 - pch ψ x.1 (rat β.1)) * fc ψ lam 𝓖 nb F β g = 0 := by rw [sub_mul, one_mul, ← e, sub_self]
    rw [(mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 (Ne.symm hne)), mul_zero]

/- English proof (translation)
Take `⟨lam, 𝓖, hcov⟩` from `GlobalTheory.CompanionTheory.HermVol.exists_isCovolOneH D n`. Establish `hC : CoefData (D` using `D) (n := n) nb lam 𝓖 := ⟨hnb, hcov⟩`. Establish `hco : ∀ β : HermE D n, ∫ x in 𝓖, cutR nb C F (nb x * g) * conj (pch ψ x.1 (rat β.1)) ∂lam = 0`. Introduce `β`. Establish `e : ∫ x in 𝓖, cutR nb C F (nb x * g) * conj (pch ψ x.1 (rat β.1)) ∂lam = fc ψ lam 𝓖 nb (cutR nb C F) β g`.

Rewrite using `[fc_eq]`. Use `integral_congr_ae (.of_forall fun b => ?_)` and prove the remaining obligations. Use `show _ * conj (pch ψ b.1 (rat β.1)) = _ * chn ψ β b`. Rewrite using `[pch_rat, conj_psi hψ, chn_eq]`. Rewrite using `[e]`.

Distinguish the cases in `hβ : β.1.rank < r`. Conclude with `fc_cutR_low hψ hC hF hinv hK C hkill β hβ hg`. Rewrite using `[fc_cutR hψ hC hF hinv C β hg, hR nb lam 𝓖 hC β (not_lt.1 hβ) g, mul_zero]`. Establish `key` using `hFP D n ψ hψ lam 𝓖 hcov (fun b => cutR nb C F (nb b * g)) (cont_nb (cutR_cont C hF) hnb g) (fun γ hγ b => per_nb (cutR_left C hinv) hnb g γ hγ b) hco`. Establish `h0` using `congrFun key 0`.

Simplify using `only [GlobalTheory.CompanionTheory.FourierN.nb_zero hnb, one_mul, Pi.zero_apply] at h0`. Conclude with `h0`.
-/
theorem vanish_at {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (hFP : FourierPt) {nb : hermA D n → G D n}
    (hnb : IsNMap nb) {v : Pl D} (C : Cut D n v) {r : ℕ} (hkill : C.Kills ψ r) {F : G D n → ℂ} (hF : Continuous F)
    (hinv : LeftInv (GF D n) F) (hK : ∀ k ∈ KAt D n v, ∀ g, F (g * k) = F g) (hR : RankLT ψ F r) {g : G D n}
    (hg : proj D.sp.cm.sig (Jst D n) v g = 1) : cutR nb C F g = 0 := by
  obtain ⟨lam, 𝓖, hcov⟩ := GlobalTheory.CompanionTheory.HermVol.exists_isCovolOneH D n
  have hC : CoefData (D := D) (n := n) nb lam 𝓖 := ⟨hnb, hcov⟩
  have hco : ∀ β : HermE D n, ∫ x in 𝓖, cutR nb C F (nb x * g) * conj (pch ψ x.1 (rat β.1)) ∂lam = 0 := by
    intro β
    have e : ∫ x in 𝓖, cutR nb C F (nb x * g) * conj (pch ψ x.1 (rat β.1)) ∂lam = fc ψ lam 𝓖 nb (cutR nb C F) β g := by
      rw [fc_eq]
      refine integral_congr_ae (.of_forall fun b => ?_)
      show _ * conj (pch ψ b.1 (rat β.1)) = _ * chn ψ β b
      rw [pch_rat, conj_psi hψ, chn_eq]
    rw [e]
    by_cases hβ : β.1.rank < r
    · exact fc_cutR_low hψ hC hF hinv hK C hkill β hβ hg
    · rw [fc_cutR hψ hC hF hinv C β hg, hR nb lam 𝓖 hC β (not_lt.1 hβ) g, mul_zero]
  have key := hFP D n ψ hψ lam 𝓖 hcov (fun b => cutR nb C F (nb b * g)) (cont_nb (cutR_cont C hF) hnb g)
    (fun γ hγ b => per_nb (cutR_left C hinv) hnb g γ hγ b) hco
  have h0 := congrFun key 0
  simp only [GlobalTheory.CompanionTheory.FourierN.nb_zero hnb, one_mul, Pi.zero_apply] at h0
  exact h0

end PositivityTheory.Rg.Rsw.L.LCutLow

namespace PositivityTheory.Rg.Rsw.L

open LCutLow in
/- English proof (translation)
Introduce `hFP hWA D n r ψ hψ nb hnb v C hkill F hF hinv hK`. Establish `hlev : ∀ k ∈ lev nb C.s, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ∀ g, cutR nb C F (g * k) = cutR nb C F g` using `fun k hk hkv g => cutR_lev hnb C hK hk hkv g`. Use `⟨fun hR => ?_, ⟨lev nb C.s, isOpen_lev nb C.s, hlev⟩, fun lam 𝓖 hC β g hg => ⟨fc_cutR hψ hC hF hinv C β hg, fun hβ => fc_cutR_low hψ hC hF hinv hK C hkill β hβ hg⟩⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Take `⟨γ, hγ, g', hg', k, hk, hkv, rfl⟩` from `hWA D n v (lev nb C.s) (isOpen_lev nb C.s) g`.

Use `show cutR nb C F (γ * g' * k) = 0`. Rewrite using `[hlev k hk hkv, cutR_left C hinv γ hγ g']`. Conclude with `vanish_at hψ hFP hnb C hkill hF hinv hK hR hg'`.
-/
theorem cutLow : FourierPt → WeakApproximationFinitePlace → CutLow := by
  intro hFP hWA D n r ψ hψ nb hnb v C hkill F hF hinv hK
  have hlev : ∀ k ∈ lev nb C.s, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ∀ g, cutR nb C F (g * k) = cutR nb C F g :=
    fun k hk hkv g => cutR_lev hnb C hK hk hkv g
  refine ⟨fun hR => ?_, ⟨lev nb C.s, isOpen_lev nb C.s, hlev⟩, fun lam 𝓖 hC β g hg =>
    ⟨fc_cutR hψ hC hF hinv C β hg, fun hβ => fc_cutR_low hψ hC hF hinv hK C hkill β hβ hg⟩⟩
  funext g
  obtain ⟨γ, hγ, g', hg', k, hk, hkv, rfl⟩ := hWA D n v (lev nb C.s) (isOpen_lev nb C.s) g
  show cutR nb C F (γ * g' * k) = 0
  rw [hlev k hk hkv, cutR_left C hinv γ hγ g']
  exact vanish_at hψ hFP hnb C hkill hF hinv hK hR hg'

end PositivityTheory.Rg.Rsw.L

end
