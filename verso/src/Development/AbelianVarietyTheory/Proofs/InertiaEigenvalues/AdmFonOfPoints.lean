import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientExtensionDecomposition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineAndJumps
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.HubFon

/- English proof (translation)
Establish `hc` using `D.ntypes.g_cond k`. Establish `hq8` using `D.host.hyp.2.2.1`. Establish `hd16` using `D.host.hyp.2.2.2.1`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h1 : D.host.g k % D.host.q = 1`. Rewrite using `[← Nat.mod_mod_of_dvd _ (show D.host.q ∣ D.host.QS * D.host.q * D.host.d from ⟨D.host.QS * D.host.d, by ring⟩), hc]`. Conclude with `Nat.mod_eq_of_lt (by omega)`. Rewrite `h1` using `[h, Nat.mod_self]`. Use linear arithmetic over natural numbers and integers.

Introduce `h`. Establish `h1 : D.host.g k % D.host.d = 1`. Rewrite using `[← Nat.mod_mod_of_dvd _ (show D.host.d ∣ D.host.QS * D.host.q * D.host.d from ⟨D.host.QS * D.host.q, by ring⟩), hc]`. Conclude with `Nat.mod_eq_of_lt (by omega)`. Rewrite `h1` using `[h, Nat.mod_self]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem g_ne_q_d (D : D7) (k : Fin 2) : D.host.g k ≠ D.host.q ∧ D.host.g k ≠ D.host.d := by
  have hc := D.ntypes.g_cond k
  have hq8 := D.host.hyp.2.2.1
  have hd16 := D.host.hyp.2.2.2.1
  constructor
  · intro h
    have h1 : D.host.g k % D.host.q = 1 := by
      rw [← Nat.mod_mod_of_dvd _ (show D.host.q ∣ D.host.QS * D.host.q * D.host.d from
        ⟨D.host.QS * D.host.d, by ring⟩), hc]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h, Nat.mod_self] at h1
    omega
  · intro h
    have h1 : D.host.g k % D.host.d = 1 := by
      rw [← Nat.mod_mod_of_dvd _ (show D.host.d ∣ D.host.QS * D.host.q * D.host.d from
        ⟨D.host.QS * D.host.q, by ring⟩), hc]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h, Nat.mod_self] at h1
    omega

/- English proof (translation)
Introduce `hF D _L hG hJa r ρ hP i hi w hw C`. Take `⟨ep, hJ⟩` from `hJa`. Establish `hl : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d` using `hi.1.1`. Establish `h0 : D.nd.l i ≠ D.host.g 0`. Apply the tactic sequence `intro h; rcases hl with e | e <;> rw [e] at h`.

Conclude with `(g_ne_q_d D 0).1 h.symm`. Conclude with `(g_ne_q_d D 0).2 h.symm`. Establish `h1 : D.nd.l i ≠ D.host.g 1`. Apply the tactic sequence `intro h; rcases hl with e | e <;> rw [e] at h`. Conclude with `(g_ne_q_d D 1).1 h.symm`.

Conclude with `(g_ne_q_d D 1).2 h.symm`. Take `⟨π₀, hπ₀⟩` from `hi.2`. Establish `hg0 : π₀ ∈ D.nd.Zgood i` using `(D.Zgood_tie i π₀).2 hπ₀`. Establish `hZ0` using `LargeLevelLemmas.zgoodSubsetZ i hg0`. Establish `hd0 : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D` using `D) i (r i) (ρ i) π₀ := by`.

Take `⟨e, he⟩` from `(hP.compl i π₀ hZ0).rho`. Conclude with `⟨e, fun g u => he g u⟩`. Establish `hc` using `(GlobalTheory.CrysFromGTwo.main hF D i (r i) (ρ i) π₀ (hP.good i) (hG i _ (hP.good i)) h0 h1 hd0 w hw C).2`. Establish `K` using `GlobalTheory.TateDualCrys.crystalline_and_jumps D i w hw (D.locT (D.nd.l i)) C.LL C.le (r i) (ρ i) (fun x => (hc x).2)`. Use `⟨fun V1 _ _ _ _ _ ρ1 hs => K.1 V1 ρ1 hs, fun π hπ => ?_⟩` and prove the remaining obligations.

Establish `hZ` using `LargeLevelLemmas.zgoodSubsetZ i hπ`. Establish `hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t` using `D.R.t) (r i π) (ρ i π) (D.nd.chi i) e := by`. Take `⟨e, he⟩` from `(hP.compl i π hZ).rho`. Conclude with `⟨e, fun g u => he g u⟩`. Use `K.2 π hdec (fun τ a => ?_)` and prove the remaining obligations.

Take `⟨g, ρ', -, hx, -⟩` from `hJ i (r i) (hP.good i) w hw C τ`. Use `(hx π a).2.1` as an intermediate fact. Rewrite using `[this]`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem main : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D), AdmissibleParameterJ.DeRhamFamilyAway D → AdmissibleParameterJ.ConclusionJa D → ∀ (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ := by
  intro hF D _L hG hJa r ρ hP i hi w hw C
  obtain ⟨ep, hJ⟩ := hJa
  have hl : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d := hi.1.1
  have h0 : D.nd.l i ≠ D.host.g 0 := by
    intro h; rcases hl with e | e <;> rw [e] at h
    · exact (g_ne_q_d D 0).1 h.symm
    · exact (g_ne_q_d D 0).2 h.symm
  have h1 : D.nd.l i ≠ D.host.g 1 := by
    intro h; rcases hl with e | e <;> rw [e] at h
    · exact (g_ne_q_d D 1).1 h.symm
    · exact (g_ne_q_d D 1).2 h.symm
  obtain ⟨π₀, hπ₀⟩ := hi.2
  have hg0 : π₀ ∈ D.nd.Zgood i := (D.Zgood_tie i π₀).2 hπ₀
  have hZ0 := LargeLevelLemmas.zgoodSubsetZ i hg0
  have hd0 : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i (r i) (ρ i) π₀ := by
    obtain ⟨e, he⟩ := (hP.compl i π₀ hZ0).rho
    exact ⟨e, fun g u => he g u⟩
  have hc := (GlobalTheory.CrysFromGTwo.main hF D i (r i) (ρ i) π₀ (hP.good i) (hG i _ (hP.good i)) h0 h1 hd0 w hw C).2
  have K := GlobalTheory.TateDualCrys.crystalline_and_jumps D i w hw (D.locT (D.nd.l i)) C.LL C.le (r i) (ρ i)
    (fun x => (hc x).2)
  refine ⟨fun V1 _ _ _ _ _ ρ1 hs => K.1 V1 ρ1 hs, fun π hπ => ?_⟩
  have hZ := LargeLevelLemmas.zgoodSubsetZ i hπ
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r i π) (ρ i π) (D.nd.chi i) e := by
    obtain ⟨e, he⟩ := (hP.compl i π hZ).rho
    exact ⟨e, fun g u => he g u⟩
  refine K.2 π hdec (fun τ a => ?_)
  obtain ⟨g, ρ', -, hx, -⟩ := hJ i (r i) (hP.good i) w hw C τ
  have := (hx π a).2.1
  rw [this]
  split_ifs <;> norm_num

end GlobalTheory.HubFon
