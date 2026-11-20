import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOpen

noncomputable section

open scoped Quaternion Topology

namespace GlobalTheory.QSA

namespace TraceOpenPi

variable {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] {a b : ∀ i, R i}

def comp (i : ι) (x : ℍ[∀ i, R i, a, b]) : ℍ[R i, a i, b i] :=
  ⟨x.re i, x.imI i, x.imJ i, x.imK i⟩

def glue (u : ∀ i, ℍ[R i, a i, b i]) : ℍ[∀ i, R i, a, b] :=
  ⟨fun i => (u i).re, fun i => (u i).imI, fun i => (u i).imJ, fun i => (u i).imK⟩

/- English proof (translation)
Apply the tactic sequence `ext <;> rfl`.
-/
theorem glue_comp (x : ℍ[∀ i, R i, a, b]) : glue (fun i => comp i x) = x := by
  ext <;> rfl

/- English proof (translation)
Simplify using `[nrm, comp]`.
-/
theorem nrm_comp (i : ι) (x : ℍ[∀ i, R i, a, b]) : nrm (comp i x) = nrm x i := by
  simp [nrm, comp]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[nrm, glue]`.
-/
theorem nrm_glue (u : ∀ i, ℍ[R i, a i, b i]) : nrm (glue u) = fun i => nrm (u i) := by
  funext i
  simp [nrm, glue]

/- English proof (translation)
Use function extensionality and compare the values at `k i`. Apply the tactic sequence `fin_cases k <;> rfl`.
-/
theorem coords_glue (u : ∀ i, ℍ[R i, a i, b i]) : coords (glue u) = fun k i => coords (u i) k := by
  funext k i
  fin_cases k <;> rfl

/- English proof (translation)
Use `continuous_induced_rng.2 ?_` and prove the remaining obligations. Establish `: (coords ∘ (glue : (∀ i, ℍ[R i, a i, b i]) → ℍ[∀ i, R i, a, b])) = fun u k i => coords (u i) k`. Use function extensionality and compare the values at `u`. Conclude with `coords_glue u`. Rewrite using `[this]`.

Use `continuous_pi fun k => continuous_pi fun i => ?_` and prove the remaining obligations. Establish `hc : Continuous (coords : ℍ[R i, a i, b i] → Fin 4 → R i)` using `continuous_induced_dom`. Conclude with `((continuous_apply k).comp hc).comp (continuous_apply i)`.
-/
theorem continuous_glue [∀ i, TopologicalSpace (R i)] :
    Continuous (glue : (∀ i, ℍ[R i, a i, b i]) → ℍ[∀ i, R i, a, b]) := by
  refine continuous_induced_rng.2 ?_
  have : (coords ∘ (glue : (∀ i, ℍ[R i, a i, b i]) → ℍ[∀ i, R i, a, b])) =
      fun u k i => coords (u i) k := by
    funext u
    exact coords_glue u
  rw [this]
  refine continuous_pi fun k => continuous_pi fun i => ?_
  have hc : Continuous (coords : ℍ[R i, a i, b i] → Fin 4 → R i) := continuous_induced_dom
  exact ((continuous_apply k).comp hc).comp (continuous_apply i)

end TraceOpenPi

open TraceOpenPi in

/- English proof (translation)
Introduce `ι _ R _ _ a b h g hg W hW`. Establish `hgi : ∀ i, nrm (comp i g) = 1` using `fun i => by`. Rewrite using `[nrm_comp, hg]`. Both sides reduce to the same expression. Establish `hW' : glue ⁻¹' W ∈ 𝓝 (fun i => comp i g)`.

Use `continuous_glue.continuousAt.preimage_mem_nhds ?_` and prove the remaining obligations. Rewrite using `[glue_comp]`. Conclude with `hW`. Rewrite `hW'` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, -, V, hV, hVW⟩` from `hW'`.

Establish `hO` using `fun i => h i (comp i g) (hgi i) (V i) (hV i)`. Use `choose O hOo hOn hOt using hO`. Use `⟨Set.univ.pi O, isOpen_set_pi Set.finite_univ fun i _ => hOo i, Set.univ_pi_nonempty_iff.2 hOn, fun t ht => ?_⟩` and prove the remaining obligations. Establish `ht'` using `fun i => hOt i (t i) (ht i (Set.mem_univ i))`. Use `choose u huV hun hur using ht'`.

Use `⟨glue u, hVW fun i _ => huV i, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[nrm_glue]`. Use function extensionality and compare the values at `i`. Conclude with `hun i`. Use function extensionality and compare the values at `i`.

Conclude with `hur i`.
-/
theorem traceOpen_pi : ∀ (ι : Type) [Fintype ι] (R : ι → Type) [∀ i, CommRing (R i)]
    [∀ i, TopologicalSpace (R i)] (a b : ∀ i, R i),
    (∀ i, TraceOpen (R i) (a i) (b i)) → TraceOpen (∀ i, R i) a b := by
  intro ι _ R _ _ a b h g hg W hW
  have hgi : ∀ i, nrm (comp i g) = 1 := fun i => by
    rw [nrm_comp, hg]; rfl
  have hW' : glue ⁻¹' W ∈ 𝓝 (fun i => comp i g) := by
    refine continuous_glue.continuousAt.preimage_mem_nhds ?_
    rw [glue_comp]; exact hW
  rw [nhds_pi, Filter.mem_pi] at hW'
  obtain ⟨I, -, V, hV, hVW⟩ := hW'
  have hO := fun i => h i (comp i g) (hgi i) (V i) (hV i)
  choose O hOo hOn hOt using hO
  refine ⟨Set.univ.pi O, isOpen_set_pi Set.finite_univ fun i _ => hOo i,
    Set.univ_pi_nonempty_iff.2 hOn, fun t ht => ?_⟩
  have ht' := fun i => hOt i (t i) (ht i (Set.mem_univ i))
  choose u huV hun hur using ht'
  refine ⟨glue u, hVW fun i _ => huV i, ?_, ?_⟩
  · rw [nrm_glue]; funext i; exact hun i
  · funext i; exact hur i

end GlobalTheory.QSA
