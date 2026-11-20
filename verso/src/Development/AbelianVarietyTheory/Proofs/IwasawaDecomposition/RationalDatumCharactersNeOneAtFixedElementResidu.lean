import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.HeightCounting

/- English proof (translation)
Introduce `D cf Rw low Pq S hL eig θ Bs hr i kv h1`. Use `haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩`. Take `⟨θ', hθ', hψ⟩` from `Bs.exp.psiU_gen i true`. Establish `hu : Formalism.L2.NX.tvAt (p` using `fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) hr kv ∈ D.nexp.U := by`. Rewrite using `[Bs.exp.U_eq]`.

Conclude with `Formalism.L2.NX.tvAt_mem hr _`. Establish `hu' : Formalism.L2.NX.tvAt (p` using `fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) hr kv ∈ Formalism.IndefR.NX.U D.nd := Formalism.L2.NX.tvAt_mem hr _`. Establish `e` using `Bs.psiU i true _ hu hu'`. Establish `e2 : psiUOf D.nd (NX.xiRed D) θ ⟨_, hu'⟩ = θ kv.1 (Multiplicative.ofAdd (NX.xiRed D kv))` using `psiXi_tvAt (p := fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) (NX.xiRed D) (fun kv => θ kv.1) hr kv`. Establish `e3 : D.nexp.psiU i true ⟨_, hu⟩ = θ' kv (Multiplicative.ofAdd 1)` using `(hψ ⟨_, hu⟩).trans (Formalism.L2.NX.stdVal_tvAt θ' hr kv)`.

Rewrite `e` using `[e2, h1, e3]`. Use `Formalism.L2.NX.char_one_ne (θ' kv) (hθ' hr kv) (Units.ext (e.trans ?_))` and prove the remaining obligations. Conclude with `map_one (readLL0 S i true)`.
-/
theorem theta_xiRed_ne_one : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ), SideB D cf Rw low Pq S hL eig θ →
    2 ≤ D.R.r → D.ntw.Tw → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), θ kv.1 (Multiplicative.ofAdd (NX.xiRed D kv)) ≠ 1 := by
  classical
  intro D cf Rw low Pq S hL eig θ Bs hr i kv h1
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  obtain ⟨θ', hθ', hψ⟩ := Bs.exp.psiU_gen i true
  have hu : Formalism.L2.NX.tvAt (p := fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) hr kv ∈ D.nexp.U := by
    rw [Bs.exp.U_eq]; exact Formalism.L2.NX.tvAt_mem hr _
  have hu' : Formalism.L2.NX.tvAt (p := fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) hr kv ∈ Formalism.IndefR.NX.U D.nd :=
    Formalism.L2.NX.tvAt_mem hr _
  have e := Bs.psiU i true _ hu hu'
  have e2 : psiUOf D.nd (NX.xiRed D) θ ⟨_, hu'⟩ = θ kv.1 (Multiplicative.ofAdd (NX.xiRed D kv)) :=
    psiXi_tvAt (p := fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) (NX.xiRed D) (fun kv => θ kv.1) hr kv
  have e3 : D.nexp.psiU i true ⟨_, hu⟩ = θ' kv (Multiplicative.ofAdd 1) :=
    (hψ ⟨_, hu⟩).trans (Formalism.L2.NX.stdVal_tvAt θ' hr kv)
  rw [e2, h1, e3] at e
  refine Formalism.L2.NX.char_one_ne (θ' kv) (hθ' hr kv) (Units.ext (e.trans ?_))
  exact map_one (readLL0 S i true)

end GlobalTheory.HeightCounting
