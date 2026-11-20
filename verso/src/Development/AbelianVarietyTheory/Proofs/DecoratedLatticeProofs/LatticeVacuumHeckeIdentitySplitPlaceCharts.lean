import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentVacuumHyperspecialDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPrimeLabelOperatorsEqChartHeckeOperatorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.HSplitChart

/- English proof (translation)
Unfold `GlobalTheory.Hk3.opOf GlobalTheory.Hk3.dualC GlobalTheory.Hk3.splitC`. Rewrite using `[Finsupp.mapDomain_finset_sum, ← Finsupp.sum_finset_sum_index]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.mapDomain_single, Finsupp.sum_single_index, Finsupp.sum_single_index, one_smul]`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Introduce `a`. Simplify using the standard rewrite rules. Introduce `a b1 b2`. Simplify using `[add_smul]`.
-/
lemma opOf_dualC_splitC {D : D7} {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M]
    (π : GA D V →* Module.End ℂ M) (P : Formalism.L2.DIV.Pl D.host.E) (n : ℕ) (z : ℕ → ℂ) :
    GlobalTheory.Hk3.opOf π P (GlobalTheory.Hk3.dualC (GlobalTheory.Hk3.splitC n z)) =
      ∑ j ∈ Finset.range (n + 1), z j • GlobalTheory.Hk3.opOf π P (Finsupp.single (dualLab (splitLab n j)) 1) := by
  unfold GlobalTheory.Hk3.opOf GlobalTheory.Hk3.dualC GlobalTheory.Hk3.splitC
  rw [Finsupp.mapDomain_finset_sum, ← Finsupp.sum_finset_sum_index]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finsupp.mapDomain_single, Finsupp.sum_single_index, Finsupp.sum_single_index, one_smul]
    · simp
    · simp
  · intro a; simp
  · intro a b1 b2; simp [add_smul]

/- English proof (translation)
Introduce `D ψ S T χS χT om hW t ht v w h hsp hunr eS eT hcS hcT f hf`. Take `⟨hA, hB, hC, hD, hE⟩` from `GlobalTheory.T.splitPlace_idempotent_vacuum_hyperspecial_dictionary D v w h`. Establish `hconj : Formalism.DivisionValues.conjPl w ≠ w` using `hA.1 hsp`. Establish `huS : GlobalTheory.Hk3.UnrPl w χS` using `hB χS (fun w' hw' => (hunr w' hw').1)`. Establish `huT : GlobalTheory.Hk3.UnrPl w χT` using `hB χT (fun w' hw' => (hunr w' hw').2)`.

Take `⟨hfix, hmatch⟩` from `GlobalTheory.Hk3.SplitMatch.match_split ψ S T χS χT om w hW hconj huS huT`. Establish `hvac : GlobalTheory.Hk3.IsVacAt ψ S T w f` using `hD ψ S T f hf`. Establish `hK : ∀ k ∈ Kv S v, ∀ k' ∈ Kv T v, om (embV S v k, embV T v k') f = f`. Introduce `k hk k' hk'`. Conclude with `hfix f hvac _ ((hC S _).2 ⟨k, hk, rfl⟩) _ ((hC T _).2 ⟨k', hk', rfl⟩)`.

Use `⟨hK, ?_⟩` and prove the remaining obligations. Introduce `ϖ hϖ k hk`. Take `⟨e, ϖ', x, he, h1, h2, hx, hval⟩` from `hE hsp χS (hunr w h).1`. Establish `hχS` using `hval χS (hunr w h).1`. Establish `hχT` using `hval χT (hunr w h).2`.

Establish `hM` using `(hmatch e ϖ' x t he h1 h2 hx).1 ht k hk f hvac`. Establish `hTfix : ∀ k ∈ Kv T v, (om.comp (MonoidHom.inr _ _)) (embV T v k) f = f`. Introduce `k hk`. Simplify using `using hK 1 (one_mem _) k hk`. Establish `hSfix : ∀ k ∈ Kv S v, (om.comp (MonoidHom.inl _ _)) (embV S v k) f = f`.

Introduce `k hk`. Simplify using `using hK k hk 1 (one_mem _)`. Rewrite using `[← (GlobalTheory.T.split_prime_label_operators_eq_chart_hecke_operators D T v w h hsp eT hcT _ (om.comp (MonoidHom.inr _ _)) f hTfix ϖ hϖ k hk).1, ← hM, opOf_dualC_splitC, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, (GlobalTheory.T.split_prime_label_operators_eq_chart_hecke_operators D S v w h hsp eS hcS _ (om.comp (MonoidHom.inl _ _)) f hSfix ϖ hϖ j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).2, hχS, hχT]`.

Both sides reduce to the same expression.
-/
theorem hecke_vac_split_chart : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ t : ℕ, T.rank = S.rank + t → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χS w' ∧ UnrAt χT w') → ∀ eS eT, IsSplitChart D.sp.cm.sig S.gram (frameLat S) h eS → IsSplitChart D.sp.cm.sig T.gram (frameLat T) h eT → ∀ f, VacFin ψ S T v f → (∀ k ∈ Kv S v, ∀ k' ∈ Kv T v, om (embV S v k, embV T v k') f = f) ∧ ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ k ≤ T.rank, heckeVec (((om.comp (MonoidHom.inr _ _)).comp (embV T v)).comp eT.symm.toMonoidHom) (KGL w T.rank) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) f = ∑ j ∈ Finset.range (S.rank + 1), (if j ≤ k then (qV D.host.E w : ℂ) ^ ((S.rank - j) * (k - j)) * (Formalism.L2.Col.gaussBin (qV D.host.E w) t (k - j) : ℂ) * (((val (F := D.host.F) χS w : ℂˣ) : ℂ) * (Real.sqrt (qV D.host.E w) : ℂ) ^ S.rank)⁻¹ ^ k * (((val (F := D.host.F) χT w : ℂˣ) : ℂ) * (Real.sqrt (qV D.host.E w) : ℂ) ^ T.rank) ^ j else 0) • heckeVec (((om.comp (MonoidHom.inl _ _)).comp (embV S v)).comp eS.symm.toMonoidHom) (KGL w S.rank) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) f := by
  intro D ψ S T χS χT om hW t ht v w h hsp hunr eS eT hcS hcT f hf
  obtain ⟨hA, hB, hC, hD, hE⟩ := GlobalTheory.T.splitPlace_idempotent_vacuum_hyperspecial_dictionary D v w h
  have hconj : Formalism.DivisionValues.conjPl w ≠ w := hA.1 hsp
  have huS : GlobalTheory.Hk3.UnrPl w χS := hB χS (fun w' hw' => (hunr w' hw').1)
  have huT : GlobalTheory.Hk3.UnrPl w χT := hB χT (fun w' hw' => (hunr w' hw').2)
  obtain ⟨hfix, hmatch⟩ := GlobalTheory.Hk3.SplitMatch.match_split ψ S T χS χT om w hW hconj huS huT
  have hvac : GlobalTheory.Hk3.IsVacAt ψ S T w f := hD ψ S T f hf
  have hK : ∀ k ∈ Kv S v, ∀ k' ∈ Kv T v, om (embV S v k, embV T v k') f = f := by
    intro k hk k' hk'
    exact hfix f hvac _ ((hC S _).2 ⟨k, hk, rfl⟩) _ ((hC T _).2 ⟨k', hk', rfl⟩)
  refine ⟨hK, ?_⟩
  intro ϖ hϖ k hk
  obtain ⟨e, ϖ', x, he, h1, h2, hx, hval⟩ := hE hsp χS (hunr w h).1
  have hχS := hval χS (hunr w h).1
  have hχT := hval χT (hunr w h).2
  have hM := (hmatch e ϖ' x t he h1 h2 hx).1 ht k hk f hvac
  have hTfix : ∀ k ∈ Kv T v, (om.comp (MonoidHom.inr _ _)) (embV T v k) f = f := by
    intro k hk; simpa using hK 1 (one_mem _) k hk
  have hSfix : ∀ k ∈ Kv S v, (om.comp (MonoidHom.inl _ _)) (embV S v k) f = f := by
    intro k hk; simpa using hK k hk 1 (one_mem _)
  rw [← (GlobalTheory.T.split_prime_label_operators_eq_chart_hecke_operators D T v w h hsp eT hcT _ (om.comp (MonoidHom.inr _ _)) f hTfix ϖ hϖ k hk).1, ← hM,
    opOf_dualC_splitC, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [LinearMap.smul_apply, (GlobalTheory.T.split_prime_label_operators_eq_chart_hecke_operators D S v w h hsp eS hcS _ (om.comp (MonoidHom.inl _ _)) f hSfix ϖ hϖ j
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).2, hχS, hχT]
  rfl

end GlobalTheory.ChainOnto.HSplitChart
