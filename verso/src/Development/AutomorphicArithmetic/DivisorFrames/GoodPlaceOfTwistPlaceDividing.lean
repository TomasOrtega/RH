import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open Formalism.CohomologicalDescent.DepthNonnegative (NablaT)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Y cX ex Csz p j P W hD w hw hW v hv`. Establish `hL` using `p.charW.base.lev`. Establish `hl` using `Formalism.EigenvalueLevelCeiling.plc_prime w`. Establish `key : ∀ q : ℕ, q.Prime → q ≠ Formalism.EigenvalueLevelCeiling.plc w → ((q : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal`. Introduce `q hq hne hqv`.

Establish `hc : IsCoprime ((q : ℕ) : 𝓞 D.host.E) ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E)` using `Nat.Coprime.cast ((Nat.coprime_primes hq hl).2 hne)`. Take `⟨a, b, hab⟩` from `hc`. Conclude with `v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left a hqv) (v.asIdeal.mul_mem_left b hv)))`. Establish `hsp : Formalism.EigenvalueLevelCeiling.plc w ∉ Formalism.MainNotions.JumpSetsAlt.excSet D` using `hD.special ▸ hW.2.2.2`. Establish `hunr : (p.R.xiH (p.R.mu w)).UnrAt v`.

Take `⟨ψ, Q, hψ, e⟩` from `p.charW.tup.mu_on w hw`. Establish `e' : p.R.xiH (p.R.mu w) = p.R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψ` using `e`. Establish `hd : (p.R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).UnrAt v`. Unfold `Formalism.L2.Host.CharFrame.delAt`. Use `split_ifs`.

Use `p.R.C.isDel'.unr v (key _ D.host.pde'_prime fun h => hsp ?_)` and prove the remaining obligations. Rewrite using `[← h]`. Simplify using `[Formalism.MainNotions.JumpSetsAlt.excSet]`. Use `p.R.C.isDel.unr v (key _ D.host.pde_prime fun h => hsp ?_)` and prove the remaining obligations. Rewrite using `[← h]`.

Simplify using `[Formalism.MainNotions.JumpSetsAlt.excSet]`. Introduce `x hx`. Establish `a1` using `hd x hx`. Establish `a2` using `hψ.atl v hv x`. Rewrite using `[e']`.

Express the relevant statement in the definitionally equal form `(p.R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).loc v x * ψ.loc v x = 1`. Rewrite using `[a1, a2, mul_one]`. Introduce `PP hPP`. Break down `hPP with hPP | hPP` into its components or cases. Take `⟨k, hk⟩` from `(hL.Pg PP).1 hPP`.

Establish `hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal`. Establish `h1` using `p.R.C.P.pb_over k`. Establish `hk' : PP.under (𝓞 D.host.K) = p.R.C.P.pb k` using `hk`. Rewrite `h1` using `[← hk']`. Establish `h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal` using `h1`.

Rewrite `h2` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hn : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal`. Use `key _ (D.host.g_prime k) fun h => ?_` and prove the remaining obligations. Establish `h1` using `hD.big k`. Establish `h2` using `hW.2.1`.

Rewrite `h1` using `[h]`. Conclude with `absurd h1 (not_lt.2 h2)`. Use `⟨fun e => hn (e ▸ hg), fun hc => hn ?_⟩` and prove the remaining obligations. Take `⟨c', h1, h2⟩` from `hc _ hg`. Establish `: c' = ((D.host.g k : ℕ) : 𝓞 D.host.E)`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Establish `e1 : (((D.host.g k : ℕ) : 𝓞 D.host.E) : D.host.E) = ((D.host.g k : ℕ) : D.host.E)` using `map_natCast (algebraMap (𝓞 D.host.E) D.host.E) _`. Establish `h3 : (c' : D.host.E) = star (((D.host.g k : ℕ) : 𝓞 D.host.E) : D.host.E)` using `h2`. Rewrite `h3` using `[e1, star_natCast, ← e1]`. Conclude with `h3`.

Conclude with `this ▸ h1`. Conclude with `⟨fun e => (hL.Q_ram (p.R.mu w) v).2 (Or.inl (e ▸ hPP)) hunr, fun hc => (hL.Q_ram (p.R.mu w) v).2 (Or.inr ⟨PP, hPP, hc⟩) hunr⟩`.
-/
theorem UpperTheory.good_place_of_twist_place_dividing :
    ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
        {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W →
        ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → ∀ v : HeightOneSpectrum (𝓞 D.host.E),
          ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal → GlobalTheory.Hk3.Good p.R.toRealDat (p.R.mu w) v := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j P W hD w hw hW v hv
  have hL := p.charW.base.lev
  have hl := Formalism.EigenvalueLevelCeiling.plc_prime w
  have key : ∀ q : ℕ, q.Prime → q ≠ Formalism.EigenvalueLevelCeiling.plc w → ((q : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by
    intro q hq hne hqv
    have hc : IsCoprime ((q : ℕ) : 𝓞 D.host.E) ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes hq hl).2 hne)
    obtain ⟨a, b, hab⟩ := hc
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left a hqv) (v.asIdeal.mul_mem_left b hv)))
  have hsp : Formalism.EigenvalueLevelCeiling.plc w ∉ Formalism.MainNotions.JumpSetsAlt.excSet D := hD.special ▸ hW.2.2.2
  have hunr : (p.R.xiH (p.R.mu w)).UnrAt v := by
    obtain ⟨ψ, Q, hψ, e⟩ := p.charW.tup.mu_on w hw
    have e' : p.R.xiH (p.R.mu w) = p.R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψ := e
    have hd : (p.R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).UnrAt v := by
      unfold Formalism.L2.Host.CharFrame.delAt
      split_ifs
      · refine p.R.C.isDel'.unr v (key _ D.host.pde'_prime fun h => hsp ?_)
        rw [← h]
        simp [Formalism.MainNotions.JumpSetsAlt.excSet]
      · refine p.R.C.isDel.unr v (key _ D.host.pde_prime fun h => hsp ?_)
        rw [← h]
        simp [Formalism.MainNotions.JumpSetsAlt.excSet]
    intro x hx
    have a1 := hd x hx
    have a2 := hψ.atl v hv x
    rw [e']
    change (p.R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).loc v x * ψ.loc v x = 1
    rw [a1, a2, mul_one]
  intro PP hPP
  rcases hPP with hPP | hPP
  · obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPP
    have hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      have h1 := p.R.C.P.pb_over k
      have hk' : PP.under (𝓞 D.host.K) = p.R.C.P.pb k := hk
      rw [← hk'] at h1
      have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h1
      rwa [map_natCast] at h2
    have hn : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by
      refine key _ (D.host.g_prime k) fun h => ?_
      have h1 := hD.big k
      have h2 := hW.2.1
      rw [h] at h1
      exact absurd h1 (not_lt.2 h2)
    refine ⟨fun e => hn (e ▸ hg), fun hc => hn ?_⟩
    obtain ⟨c', h1, h2⟩ := hc _ hg
    have : c' = ((D.host.g k : ℕ) : 𝓞 D.host.E) := by
      apply RingOfIntegers.ext
      have e1 : (((D.host.g k : ℕ) : 𝓞 D.host.E) : D.host.E) = ((D.host.g k : ℕ) : D.host.E) := map_natCast (algebraMap (𝓞 D.host.E) D.host.E) _
      have h3 : (c' : D.host.E) = star (((D.host.g k : ℕ) : 𝓞 D.host.E) : D.host.E) := h2
      rw [e1, star_natCast, ← e1] at h3
      exact h3
    exact this ▸ h1
  · exact ⟨fun e => (hL.Q_ram (p.R.mu w) v).2 (Or.inl (e ▸ hPP)) hunr,
      fun hc => (hL.Q_ram (p.R.mu w) v).2 (Or.inr ⟨PP, hPP, hc⟩) hunr⟩
