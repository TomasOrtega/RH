import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCC
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CMeasSbox
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.KapEqParts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan

noncomputable section

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S

/- English proof (translation)
Introduce `D X u FdN hF`. Take `⟨hFm, hFex, hFu⟩` from `hF`. Take `⟨B, hBm, hBd, hB0, hlaw⟩` from `hL X u`. Take `⟨σ, hσm, hσ⟩` from `hS X u`. Take `⟨hNO, hNOmul, hNOinv, τ, hτ, hset⟩` from `hN X u`.

Take `⟨-, hmulN, hinvN⟩` from `Formalism.L2.SG.Pf.psiInfChar_holds D X u`. Use `set NO := Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u`. Establish `hinj : Set.InjOn (blk X u) (X.NinfU u)` using `fun s hs s' hs' h => LsNc5.kapInj D X u hs hs' (by rw [kap_eq_Φc, kap_eq_Φc, h])`. Use `set K' := blk X u '' (FdN ∩ X.NinfU u) with hK'def`. Establish `hK'eq : K' = σ ⁻¹' FdN`.

Use extensionality with `t`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, ⟨hsF, hsN⟩, rfl⟩ show σ (blk X u s) ∈ FdN`. Rewrite using `[hinj (hσ _).1 hsN (hσ _).2]`. Conclude with `hsF`.

Introduce `ht`. Conclude with `⟨σ t, ⟨ht, (hσ t).1⟩, (hσ t).2⟩`. Establish `hK'm : MeasurableSet K'` using `by rw [hK'eq]; exact hσm hFm`. Establish `hmulB : ∀ δ ∈ X.NinfU u, ∀ g : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q, Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B (blk X u δ) g = blk X u (δ * σ g)`. Introduce `δ hδ g`.

Rewrite using `[hlaw δ hδ (σ g) (hσ g).1, (hσ g).2]`. Establish `hinv : ∀ γ : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q, (∀ p, γ p - τ p γ ∈ cLat X u p) → ∃ γ' : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q, (∀ p, γ' p - τ p γ' ∈ cLat X u p) ∧ ∀ g, Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ' (Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ g) = …`. Introduce `γ hγ`. Take `⟨δ, hδ, rfl⟩` from `(hset γ).2 hγ`. Establish `hδN` using `hNO hδ`.

Establish `hδiN` using `hNO (hNOinv δ hδ)`. Use `⟨blk X u δ⁻¹, (hset _).1 ⟨δ⁻¹, hNOinv δ hδ, rfl⟩, fun g => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `hg` using `hσ g`. Establish `hdg : δ * σ g ∈ X.NinfU u` using `(hmulN δ hδN (σ g) hg.1).1`. Rewrite using `[hmulB δ hδN g, ← hlaw δ⁻¹ hδiN (δ * σ g) hdg, inv_mul_cancel_left, hg.2]`.

Establish `hg` using `hσ g`. Establish `hdg : δ⁻¹ * σ g ∈ X.NinfU u` using `(hmulN δ⁻¹ hδiN (σ g) hg.1).1`. Rewrite using `[hmulB δ⁻¹ hδiN g, ← hlaw δ hδN (δ⁻¹ * σ g) hdg, mul_inv_cancel_left, hg.2]`. Establish `hKd : ∀ x : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q, ∃! γ : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q, (∀ p, γ p - τ p γ ∈ cLat X u p) ∧ Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ x ∈ K'`. Introduce `x`.

Use `set g := σ x`. Establish `hg` using `hσ x`. Take `⟨δ, hδ, hδF⟩` from `hFex g`. Establish `hδN` using `hNO hδ`. Use `⟨blk X u δ, ⟨(hset _).1 ⟨δ, hδ, rfl⟩, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hmulB δ hδN x]`. Conclude with `⟨δ * g, ⟨hδF, (hmulN δ hδN g hg.1).1⟩, rfl⟩`. Introduce and unpack `γ' ⟨hγ', hγ'K⟩`. Take `⟨δ', hδ', rfl⟩` from `(hset γ').2 hγ'`. Establish `hδ'N` using `hNO hδ'`.

Rewrite `hγ'K` using `[hmulB δ' hδ'N x]`. Take `⟨s, ⟨hsF, hsN⟩, hs⟩` from `hγ'K`. Establish `hs' : s = δ' * g` using `hinj hsN (hmulN δ' hδ'N g hg.1).1 hs`. Establish `h1 : δ' * δ⁻¹ = 1` using `hFu (δ * g) hδF (δ' * δ⁻¹) (hNOmul δ' hδ' δ⁻¹ (hNOinv δ hδ)) (by`. Rewrite using `[show δ' * δ⁻¹ * (δ * g) = δ' * g by group, ← hs']; exact hsF)`.

Rewrite using `[mul_inv_eq_one.1 h1]`. Establish `hfd : ∀ p, ∃ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k p), MeasurableSet F ∧ ∀ v, ∃! a : cLat X u p, (a : CSpc (InfinitePlace X.B.I.F) D.R.k p) + v ∈ F` using `fun p => (hB X u p).2.1`. Use `choose F hF hFd using hfd`. Establish `hcount : ∀ p, Countable (cLat X u p)` using `fun p => (hB X u p).1`. Establish `hmain` using `Formalism.L2.SG.NGCut.SplitEmbedding.triFundT (CBlk D.R.rS) (CSpc (InfinitePlace X.B.I.F) D.R.k) (cMeas (InfinitePlace X.B.I.F) D.R.k) cHgt B hBm hBd hB0 τ hτ (cLat X u) hinv F hF hFd K' hK'm hKd`.

Establish `hvol : ∀ p, cMeas (InfinitePlace X.B.I.F) D.R.k p (F p) = ENNReal.ofReal (cVal X u p)` using `fun p => (hB X u p).2.2 (F p) (hF p) (hFd p)`. Establish `hcv : ∀ p, 0 ≤ cVal X u p`. Introduce `p`. Apply the tactic sequence `rcases p with ((p | b) | (p | a)) <;> simp only [cVal]`. Conclude with `mul_nonneg (pow_nonneg (by norm_num) _) (Real.rpow_nonneg (abs_nonneg _) _)`.

Use `mul_nonneg (mul_nonneg ?_ (pow_nonneg (by norm_num) _)) (Real.rpow_nonneg (abs_nonneg _) _)` and prove the remaining obligations. Conclude with `pow_nonneg (show (0 : ℝ) ≤ Formalism.L2.SG.RealObj.Tw (D := D) u from Nat.cast_nonneg _) _`. Conclude with `mul_nonneg (pow_nonneg (by norm_num) _) (Real.rpow_nonneg (abs_nonneg _) _)`. Conclude with `Real.rpow_nonneg (abs_nonneg _) _`. Establish `himg : LsNc5.kap X u '' (FdN ∩ X.NinfU u) = Ψc ⁻¹' K'`.

Use extensionality with `y`. Simplify using `only [Set.mem_image, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, rfl⟩`. Rewrite using `[kap_eq_Φc, Ψc_Φc]`.

Conclude with `⟨s, hs, rfl⟩`. Introduce and unpack `⟨s, hs, hsy⟩`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[kap_eq_Φc, hsy, Φc_Ψc]`. Rewrite using `[himg]`.

Use `⟨measurable_Ψc hK'm, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_Φc, Measure.map_apply measurable_Φc (measurable_Ψc hK'm)]`. Establish `hpre : Φc ⁻¹' (Ψc ⁻¹' K') = K'`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Ψc_Φc]`.

Rewrite using `[hpre, hmain, Finset.prod_congr rfl fun p _ => hvol p, ← ENNReal.ofReal_prod_of_nonneg fun p _ => hcv p, hP]`.
-/
theorem coordCovol_of_cut (hL : KapLaw) (hS : KapSurj) (hN : NOfib) (hB : BlockCovol)
    (hP : ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word), ∏ p, cVal X u p = LsNc5.covolN X u / LsNc5.twoU X) :
    LsNc5.CoordCovol := by
  intro D X u FdN hF
  obtain ⟨hFm, hFex, hFu⟩ := hF
  obtain ⟨B, hBm, hBd, hB0, hlaw⟩ := hL X u
  obtain ⟨σ, hσm, hσ⟩ := hS X u
  obtain ⟨hNO, hNOmul, hNOinv, τ, hτ, hset⟩ := hN X u
  obtain ⟨-, hmulN, hinvN⟩ := Formalism.L2.SG.Pf.psiInfChar_holds D X u
  set NO := Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u
  have hinj : Set.InjOn (blk X u) (X.NinfU u) := fun s hs s' hs' h =>
    LsNc5.kapInj D X u hs hs' (by rw [kap_eq_Φc, kap_eq_Φc, h])
  set K' := blk X u '' (FdN ∩ X.NinfU u) with hK'def
  have hK'eq : K' = σ ⁻¹' FdN := by
    ext t; constructor
    · rintro ⟨s, ⟨hsF, hsN⟩, rfl⟩
      show σ (blk X u s) ∈ FdN
      rw [hinj (hσ _).1 hsN (hσ _).2]; exact hsF
    · intro ht; exact ⟨σ t, ⟨ht, (hσ t).1⟩, (hσ t).2⟩
  have hK'm : MeasurableSet K' := by rw [hK'eq]; exact hσm hFm

  have hmulB : ∀ δ ∈ X.NinfU u, ∀ g : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q,
      Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B (blk X u δ) g = blk X u (δ * σ g) := by
    intro δ hδ g
    rw [hlaw δ hδ (σ g) (hσ g).1, (hσ g).2]
  have hinv : ∀ γ : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q, (∀ p, γ p - τ p γ ∈ cLat X u p) →
      ∃ γ' : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q, (∀ p, γ' p - τ p γ' ∈ cLat X u p) ∧
        ∀ g, Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ' (Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ g) = g ∧ Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ (Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ' g) = g := by
    intro γ hγ
    obtain ⟨δ, hδ, rfl⟩ := (hset γ).2 hγ
    have hδN := hNO hδ
    have hδiN := hNO (hNOinv δ hδ)
    refine ⟨blk X u δ⁻¹, (hset _).1 ⟨δ⁻¹, hNOinv δ hδ, rfl⟩, fun g => ⟨?_, ?_⟩⟩
    · have hg := hσ g
      have hdg : δ * σ g ∈ X.NinfU u := (hmulN δ hδN (σ g) hg.1).1
      rw [hmulB δ hδN g, ← hlaw δ⁻¹ hδiN (δ * σ g) hdg, inv_mul_cancel_left, hg.2]
    · have hg := hσ g
      have hdg : δ⁻¹ * σ g ∈ X.NinfU u := (hmulN δ⁻¹ hδiN (σ g) hg.1).1
      rw [hmulB δ⁻¹ hδiN g, ← hlaw δ hδN (δ⁻¹ * σ g) hdg, mul_inv_cancel_left, hg.2]
  have hKd : ∀ x : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q, ∃! γ : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q,
      (∀ p, γ p - τ p γ ∈ cLat X u p) ∧ Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ x ∈ K' := by
    intro x
    set g := σ x
    have hg := hσ x
    obtain ⟨δ, hδ, hδF⟩ := hFex g
    have hδN := hNO hδ
    refine ⟨blk X u δ, ⟨(hset _).1 ⟨δ, hδ, rfl⟩, ?_⟩, ?_⟩
    · rw [hmulB δ hδN x]
      exact ⟨δ * g, ⟨hδF, (hmulN δ hδN g hg.1).1⟩, rfl⟩
    · rintro γ' ⟨hγ', hγ'K⟩
      obtain ⟨δ', hδ', rfl⟩ := (hset γ').2 hγ'
      have hδ'N := hNO hδ'
      rw [hmulB δ' hδ'N x] at hγ'K
      obtain ⟨s, ⟨hsF, hsN⟩, hs⟩ := hγ'K
      have hs' : s = δ' * g := hinj hsN (hmulN δ' hδ'N g hg.1).1 hs
      have h1 : δ' * δ⁻¹ = 1 := hFu (δ * g) hδF (δ' * δ⁻¹) (hNOmul δ' hδ' δ⁻¹ (hNOinv δ hδ)) (by
        rw [show δ' * δ⁻¹ * (δ * g) = δ' * g by group, ← hs']; exact hsF)
      rw [mul_inv_eq_one.1 h1]
  have hfd : ∀ p, ∃ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k p), MeasurableSet F ∧
      ∀ v, ∃! a : cLat X u p, (a : CSpc (InfinitePlace X.B.I.F) D.R.k p) + v ∈ F := fun p => (hB X u p).2.1
  choose F hF hFd using hfd
  have hcount : ∀ p, Countable (cLat X u p) := fun p => (hB X u p).1
  have hmain := Formalism.L2.SG.NGCut.SplitEmbedding.triFundT (CBlk D.R.rS) (CSpc (InfinitePlace X.B.I.F) D.R.k) (cMeas (InfinitePlace X.B.I.F) D.R.k)
    cHgt B hBm hBd hB0 τ hτ (cLat X u) hinv F hF hFd K' hK'm hKd
  have hvol : ∀ p, cMeas (InfinitePlace X.B.I.F) D.R.k p (F p) = ENNReal.ofReal (cVal X u p) :=
    fun p => (hB X u p).2.2 (F p) (hF p) (hFd p)
  have hcv : ∀ p, 0 ≤ cVal X u p := by
    intro p
    rcases p with ((p | b) | (p | a)) <;> simp only [cVal]
    · exact mul_nonneg (pow_nonneg (by norm_num) _) (Real.rpow_nonneg (abs_nonneg _) _)
    · refine mul_nonneg (mul_nonneg ?_ (pow_nonneg (by norm_num) _)) (Real.rpow_nonneg (abs_nonneg _) _)
      exact pow_nonneg (show (0 : ℝ) ≤ Formalism.L2.SG.RealObj.Tw (D := D) u from Nat.cast_nonneg _) _
    · exact mul_nonneg (pow_nonneg (by norm_num) _) (Real.rpow_nonneg (abs_nonneg _) _)
    · exact Real.rpow_nonneg (abs_nonneg _) _

  have himg : LsNc5.kap X u '' (FdN ∩ X.NinfU u) = Ψc ⁻¹' K' := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [kap_eq_Φc, Ψc_Φc]
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, hsy⟩
      refine ⟨s, hs, ?_⟩
      rw [kap_eq_Φc, hsy, Φc_Ψc]
  rw [himg]
  refine ⟨measurable_Ψc hK'm, ?_⟩
  rw [← map_Φc, Measure.map_apply measurable_Φc (measurable_Ψc hK'm)]
  have hpre : Φc ⁻¹' (Ψc ⁻¹' K') = K' := by
    ext x; simp only [Set.mem_preimage, Ψc_Φc]
  rw [hpre, hmain, Finset.prod_congr rfl fun p _ => hvol p, ← ENNReal.ofReal_prod_of_nonneg fun p _ => hcv p, hP]

end Formalism.L2.SG.Pf.NcReal.JX
