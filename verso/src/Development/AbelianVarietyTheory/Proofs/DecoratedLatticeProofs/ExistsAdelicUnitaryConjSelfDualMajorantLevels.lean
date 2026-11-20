import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjStabilizersSelfDualLatticesUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanMajorantStabilisersConjugateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonAdjointHeckeOperatorEqDualLabel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers

open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EisCont.LevelConj

section Glue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

omit [NumberField E] in

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨1, by simp, fun v _ => map_one _, fun w => map_one _⟩`. Consider the case `insert u S hu ih`. Take `⟨g, h1, h2, h3⟩` from `ih`. Use `⟨emb σ J u (x u) * g, fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul]`. Distinguish the cases in `e : v = u`. Substitute `e` using the available equality. Rewrite using `[proj_emb_self, h2 v hu, mul_one]`. Rewrite using `[proj_emb_ne σ J e, one_mul, h1 v ((Finset.mem_insert.1 hv).resolve_left e)]`.

Rewrite `hv` using `[Finset.mem_insert, not_or]`. Rewrite using `[map_mul, proj_emb_ne σ J hv.1, one_mul, h2 v hv.2]`. Rewrite using `[map_mul, projArch_emb, one_mul, h3]`.
-/
theorem exists_proj_eq (x : ∀ v, GLoc σ J v) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ g : GAd σ J, (∀ v ∈ S, proj σ J v g = x v) ∧ (∀ v ∉ S, proj σ J v g = 1) ∧ ∀ w, projArch σ J w g = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, fun v _ => map_one _, fun w => map_one _⟩
  | insert u S hu ih =>
    obtain ⟨g, h1, h2, h3⟩ := ih
    refine ⟨emb σ J u (x u) * g, fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
    · rw [map_mul]
      by_cases e : v = u
      · subst e
        rw [proj_emb_self, h2 v hu, mul_one]
      · rw [proj_emb_ne σ J e, one_mul, h1 v ((Finset.mem_insert.1 hv).resolve_left e)]
    · rw [Finset.mem_insert, not_or] at hv
      rw [map_mul, proj_emb_ne σ J hv.1, one_mul, h2 v hv.2]
    · rw [map_mul, projArch_emb, one_mul, h3]

omit [NumberField E] in

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨1, by simp, fun v _ => map_one _, fun w => map_one _⟩`. Consider the case `insert u S hu ih`. Take `⟨g, h1, h2, h3⟩` from `ih`. Use `⟨embArch σ J u (x u) * g, fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul]`. Distinguish the cases in `e : v = u`. Substitute `e` using the available equality. Rewrite using `[projArch_embArch_self, h2 v hu, mul_one]`. Rewrite using `[projArch_embArch_ne σ J e, one_mul, h1 v ((Finset.mem_insert.1 hv).resolve_left e)]`.

Rewrite `hv` using `[Finset.mem_insert, not_or]`. Rewrite using `[map_mul, projArch_embArch_ne σ J hv.1, one_mul, h2 v hv.2]`. Rewrite using `[map_mul, proj_embArch, one_mul, h3]`.
-/
theorem exists_projArch_eq (x : ∀ w, GArch σ J w) (S : Finset (InfinitePlace F)) :
    ∃ g : GAd σ J, (∀ w ∈ S, projArch σ J w g = x w) ∧ (∀ w ∉ S, projArch σ J w g = 1) ∧ ∀ v, proj σ J v g = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, fun v _ => map_one _, fun w => map_one _⟩
  | insert u S hu ih =>
    obtain ⟨g, h1, h2, h3⟩ := ih
    refine ⟨embArch σ J u (x u) * g, fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
    · rw [map_mul]
      by_cases e : v = u
      · subst e
        rw [projArch_embArch_self, h2 v hu, mul_one]
      · rw [projArch_embArch_ne σ J e, one_mul, h1 v ((Finset.mem_insert.1 hv).resolve_left e)]
    · rw [Finset.mem_insert, not_or] at hv
      rw [map_mul, projArch_embArch_ne σ J hv.1, one_mul, h2 v hv.2]
    · rw [map_mul, proj_embArch, one_mul, h3]

/- English proof (translation)
Use `choose x hx using hf`. Use `choose y hy using hi`. Establish `hS` using `Filter.eventually_cofinite.1 (eventually_latLoc_eq F L L')`. Take `⟨g, g1, g2, g3⟩` from `exists_proj_eq σ J x hS.toFinset`. Take `⟨h, h1, -, h3⟩` from `exists_projArch_eq σ J y Finset.univ`.

Use `⟨g * h, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_levelAll, mem_levelAll]`. Use `and_congr (forall_congr' fun v => ?_) (forall_congr' fun w => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_inv, map_mul, h3, mul_one]`. Distinguish the cases in `hv : v ∈ hS.toFinset`.

Rewrite using `[g1 v hv]`. Conclude with `hx v _`. Establish `e : latLoc F L v = latLoc F L' v` using `by simpa using hv`. Rewrite using `[g2 v hv, inv_one, one_mul, mul_one, mem_stabLoc, mem_stabLoc, e]`. Rewrite using `[map_mul, map_mul, map_inv, map_mul, g3, one_mul, h1 w (Finset.mem_univ w)]`.

Conclude with `hy w _`.
-/
theorem exists_conj_of_local {L L' : Submodule (𝓞 E) (Fin n → E)} (hL : Submodule.IsLattice E L)
    (hL' : Submodule.IsLattice E L') (a a' : GL (Fin n) (AF F ⊗[F] E))
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ g : GLoc σ J v, ∀ k : GLoc σ J v,
      k ∈ stabLoc σ J L' v ↔ g⁻¹ * k * g ∈ stabLoc σ J L v)
    (hi : ∀ w : InfinitePlace F, ∃ g : GArch σ J w, ∀ k : GArch σ J w,
      k ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) a') ↔
        g⁻¹ * k * g ∈ stabArch σ J w (Formalism.UG.bc (compInf F E w) a)) :
    ∃ g : GAd σ J, ∀ k : GAd σ J, k ∈ levelAll σ J L' a' ↔ g⁻¹ * k * g ∈ levelAll σ J L a := by
  choose x hx using hf
  choose y hy using hi
  have hS := Filter.eventually_cofinite.1 (eventually_latLoc_eq F L L')
  obtain ⟨g, g1, g2, g3⟩ := exists_proj_eq σ J x hS.toFinset
  obtain ⟨h, h1, -, h3⟩ := exists_projArch_eq σ J y Finset.univ
  refine ⟨g * h, fun k => ?_⟩
  rw [mem_levelAll, mem_levelAll]
  refine and_congr (forall_congr' fun v => ?_) (forall_congr' fun w => ?_)
  · rw [map_mul, map_mul, map_inv, map_mul, h3, mul_one]
    by_cases hv : v ∈ hS.toFinset
    · rw [g1 v hv]
      exact hx v _
    · have e : latLoc F L v = latLoc F L' v := by simpa using hv
      rw [g2 v hv, inv_one, one_mul, mul_one, mem_stabLoc, mem_stabLoc, e]
  · rw [map_mul, map_mul, map_inv, map_mul, g3, one_mul, h1 w (Finset.mem_univ w)]
    exact hy w _

end Glue

/- English proof (translation)
Introduce `D T L L' a a' h h'`. Establish `hc` using `isCMExt_host D`. Establish `hJ` using `isHermND_gram T`. Establish `hf` using `fun v => GlobalTheory.T.exists_conj_stabilizers_selfDual_lattices_unramified D.host.F D.host.E D.sp.cm.sig hc (GlobalTheory.HeckeAdjoint.unramified_host D) T.rank T.gram hJ L L' h.lat h'.lat v (h.dual v) (h'.dual v)`. Establish `hi` using `fun w => GlobalTheory.T.archimedean_majorant_stabilisers_conjugate D.host.F D.host.E D.sp.cm.sig hc T.rank T.gram hJ a a' h.maj h'.maj w`.

Take `⟨g, hg⟩` from `exists_conj_of_local D.sp.cm.sig T.gram h.lat h'.lat a a' hf hi`. Conclude with `⟨g, fun k => hg k⟩`.
-/
theorem exists_conj : ∀ (D : D7) (T : HSp D) (L L' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (a a' : GL (Fin T.rank) (AE D)), IsLevel T L a → IsLevel T L' a' → ∃ g : GA D T, ∀ k : GA D T, k ∈ lev T L' a' ↔ g⁻¹ * k * g ∈ lev T L a := by
  intro D T L L' a a' h h'
  have hc := isCMExt_host D
  have hJ := isHermND_gram T
  have hf := fun v => GlobalTheory.T.exists_conj_stabilizers_selfDual_lattices_unramified D.host.F D.host.E D.sp.cm.sig hc (GlobalTheory.HeckeAdjoint.unramified_host D) T.rank T.gram
    hJ L L' h.lat h'.lat v (h.dual v) (h'.dual v)
  have hi := fun w => GlobalTheory.T.archimedean_majorant_stabilisers_conjugate D.host.F D.host.E D.sp.cm.sig hc T.rank T.gram hJ a a' h.maj h'.maj w
  obtain ⟨g, hg⟩ := exists_conj_of_local D.sp.cm.sig T.gram h.lat h'.lat a a' hf hi
  exact ⟨g, fun k => hg k⟩

end GlobalTheory.EisCont.LevelConj
