import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOpenPrincipalCongruenceFinitelyManyPrimesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeReductionEqOneOfLocalComponentOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.LevelFacts

variable {D : D7}

/- English proof (translation)
Take `⟨hr, ξ, hL⟩` from `hs.lev`. Rewrite using `[hL]`. Conclude with `⟨rfl, rfl⟩`.
-/
theorem places_of_stage {c : Com D} {j : ℕ} {s : PiLocalization₂ D} (hs : s.Is c j) : s.L.Pg = c.Pg ∧ s.L.Q = ∅ := by
  obtain ⟨hr, ξ, hL⟩ := hs.lev
  rw [hL]
  exact ⟨rfl, rfl⟩

/- English proof (translation)
Take `⟨hPg, hQ⟩` from `places_of_stage hs`. Establish `h' : ∀ PP, PP ∈ s.L.Pg ∨ PP ∈ s.L.Q → redFn s.β PP (Lev.finE s.V k) = 1`. Introduce and unpack `PP (h | h)`. Conclude with `hr PP (hPg ▸ h)`. Rewrite `h` using `[hQ]`.

Simplify using `at h`. Use `⟨⟨hk, GlobalTheory.LevSplit.mem_lev_of_red D.sp.cm s.V.gram s.β s.L _ (GlobalTheory.LevSplit.finE_mem_UA s.V k) hS h'⟩, ?_⟩` and prove the remaining obligations. Unfold `Lev.levChi`. Rewrite using `[GlobalTheory.LevSplit.levFn_eq_one s.β s.L _ h', Units.val_one]`.
-/
theorem mem_levG_of_red {c : Com D} {j : ℕ} {s : PiLocalization₂ D} (hs : s.Is c j) {k : GA D s.V} (hk : k ∈ GfC s.V)
    (hS : Lev.finE s.V k ∈ St s.β) (hr : ∀ PP ∈ c.Pg, redFn s.β PP (Lev.finE s.V k) = 1) :
    k ∈ Lev.levG s.V s.β s.L ∧ Lev.levChi s.V s.β s.L k = 1 := by
  obtain ⟨hPg, hQ⟩ := places_of_stage hs
  have h' : ∀ PP, PP ∈ s.L.Pg ∨ PP ∈ s.L.Q → redFn s.β PP (Lev.finE s.V k) = 1 := by
    rintro PP (h | h)
    · exact hr PP (hPg ▸ h)
    · rw [hQ] at h; simp at h
  refine ⟨⟨hk, GlobalTheory.LevSplit.mem_lev_of_red D.sp.cm s.V.gram s.β s.L _ (GlobalTheory.LevSplit.finE_mem_UA s.V k) hS h'⟩, ?_⟩
  unfold Lev.levChi
  rw [GlobalTheory.LevSplit.levFn_eq_one s.β s.L _ h', Units.val_one]

/- English proof (translation)
The claim follows from `parLev_St (lev_le_parLev hk.2)`.
-/
theorem finE_mem_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {k : GA D V}
    (hk : k ∈ Lev.levG V β L) : Lev.finE V k ∈ St β :=
  parLev_St (lev_le_parLev hk.2)

/- English proof (translation)
Rewrite using `[GlobalTheory.AdelicU.GfC_eq]`. Conclude with `GlobalTheory.AdelicU.mem_finPts.2 (by simp)`.
-/
theorem emb_mem_GfC (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (k : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v) :
    GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k ∈ GfC V := by
  rw [GlobalTheory.AdelicU.GfC_eq]
  exact GlobalTheory.AdelicU.mem_finPts.2 (by simp)

/- English proof (translation)
Take `⟨n, hn, h⟩` from `(GlobalTheory.LevSplit.levFn_finOrd β L (Lev.finE V k)).exists_pow_eq_one`. Establish `h2 : (Lev.levChi V β L k) ^ n = 1`. Unfold `Lev.levChi`. Rewrite using `[← Units.val_pow_eq_pow_val, h, Units.val_one]`. Conclude with `Complex.norm_eq_one_of_pow_eq_one h2 hn.ne'`.
-/
theorem levChi_norm {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (k : GA D V) :
    ‖Lev.levChi V β L k‖ = 1 := by
  obtain ⟨n, hn, h⟩ := (GlobalTheory.LevSplit.levFn_finOrd β L (Lev.finE V k)).exists_pow_eq_one
  have h2 : (Lev.levChi V β L k) ^ n = 1 := by
    unfold Lev.levChi
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h2 hn.ne'

/- English proof (translation)
Establish `e` using `(levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩`. Establish `e' : levFn β L (Lev.finE V k * Lev.finE V k') = levFn β L (Lev.finE V k) * levFn β L (Lev.finE V k')` using `e`. Unfold `Lev.levChi`. Rewrite using `[map_mul, e', Units.val_mul]`.
-/
theorem levChi_mul {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {k k' : GA D V}
    (hk : k ∈ Lev.levG V β L) (hk' : k' ∈ Lev.levG V β L) :
    Lev.levChi V β L (k * k') = Lev.levChi V β L k * Lev.levChi V β L k' := by
  have e := (levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩
  have e' : levFn β L (Lev.finE V k * Lev.finE V k') = levFn β L (Lev.finE V k) * levFn β L (Lev.finE V k') := e
  unfold Lev.levChi
  rw [map_mul, e', Units.val_mul]

end GlobalTheory.ChainOnto.LevelFacts

namespace GlobalTheory.ChainOnto.LevelFacts

/- English proof (translation)
Introduce `D c _ j _ s hs`. Establish `hfr` using `hs.frame`. Establish `hPS : ∀ PP ∈ c.Pg, PP.under (𝓞 D.host.F) ∈ c.S` using `fun PP hPP => by classical`. Unfold `Com.S`. Conclude with `Finset.mem_image_of_mem _ hPP`.

Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨U, hU, hUk⟩` from `GlobalTheory.T.exists_open_principal_congruence_finitely_many_primes D s.V s.β c.Pg`. Conclude with `⟨U, hU, fun k hk hkf => mem_levG_of_red hs hkf (hUk k hk).1 (hUk k hk).2⟩`. Introduce `v hv k hk`. Establish `hSt : Lev.finE s.V (GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v k) ∈ St s.β`.

Use `(GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D s.V s.β s.Λ hfr _).2 fun w => ?_` and prove the remaining obligations. Distinguish the cases in `e : w = v`. Substitute `e` using the available equality. Rewrite using `[GlobalTheory.AdelicU.proj_emb_self]`. Conclude with `hk`.

Rewrite using `[GlobalTheory.AdelicU.proj_emb_ne _ _ e]`. Conclude with `one_mem _`. Use `mem_levG_of_red hs (emb_mem_GfC s.V v k) hSt fun PP hPP => ?_` and prove the remaining obligations. Use `GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D s.V s.β _ PP hSt ?_` and prove the remaining obligations. Establish `hne : PP.under (𝓞 D.host.F) ≠ v` using `fun e => hv (e ▸ hPS PP hPP)`.

Conclude with `GlobalTheory.AdelicU.proj_emb_ne _ _ hne k`. Introduce `k hk v`. Conclude with `(GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D s.V s.β s.Λ hfr k).1 (finE_mem_St hk) v`. Introduce `k hkf hint h1`. Establish `hSt : Lev.finE s.V k ∈ St s.β`.

Use `(GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D s.V s.β s.Λ hfr k).2 fun v => ?_` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ c.S`. Rewrite using `[h1 v hv]`. Conclude with `one_mem _`. Conclude with `hint v hv`.

Conclude with `mem_levG_of_red hs hkf hSt fun PP hPP => GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D s.V s.β k PP hSt (h1 _ (hPS PP hPP))`. Introduce `k hk k' hk'`. Conclude with `levChi_mul hk hk'`. Introduce `k _`. Conclude with `levChi_norm s.β s.L k`.
-/
theorem levFacts : ∀ D : D7, LevFacts D := by
  intro D c _ j _ s hs
  have hfr := hs.frame
  have hPS : ∀ PP ∈ c.Pg, PP.under (𝓞 D.host.F) ∈ c.S := fun PP hPP => by
    classical
    unfold Com.S
    exact Finset.mem_image_of_mem _ hPP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨U, hU, hUk⟩ := GlobalTheory.T.exists_open_principal_congruence_finitely_many_primes D s.V s.β c.Pg
    exact ⟨U, hU, fun k hk hkf => mem_levG_of_red hs hkf (hUk k hk).1 (hUk k hk).2⟩
  · intro v hv k hk
    have hSt : Lev.finE s.V (GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v k) ∈ St s.β := by
      refine (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D s.V s.β s.Λ hfr _).2 fun w => ?_
      by_cases e : w = v
      · subst e
        rw [GlobalTheory.AdelicU.proj_emb_self]
        exact hk
      · rw [GlobalTheory.AdelicU.proj_emb_ne _ _ e]
        exact one_mem _
    refine mem_levG_of_red hs (emb_mem_GfC s.V v k) hSt fun PP hPP => ?_
    · refine GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D s.V s.β _ PP hSt ?_
      have hne : PP.under (𝓞 D.host.F) ≠ v := fun e => hv (e ▸ hPS PP hPP)
      exact GlobalTheory.AdelicU.proj_emb_ne _ _ hne k
  · intro k hk v
    exact (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D s.V s.β s.Λ hfr k).1 (finE_mem_St hk) v
  · intro k hkf hint h1
    have hSt : Lev.finE s.V k ∈ St s.β := by
      refine (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D s.V s.β s.Λ hfr k).2 fun v => ?_
      by_cases hv : v ∈ c.S
      · rw [h1 v hv]; exact one_mem _
      · exact hint v hv
    exact mem_levG_of_red hs hkf hSt fun PP hPP => GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D s.V s.β k PP hSt (h1 _ (hPS PP hPP))
  · intro k hk k' hk'
    exact levChi_mul hk hk'
  · intro k _
    exact levChi_norm s.β s.L k

end GlobalTheory.ChainOnto.LevelFacts
