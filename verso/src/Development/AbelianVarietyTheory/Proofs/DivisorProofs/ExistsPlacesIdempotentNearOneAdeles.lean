import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section
namespace GlobalTheory

open Filter

/- English proof (translation)
Set `x : Finset (HeightOneSpectrum (𝓞 F)) → Π v : HeightOneSpectrum (𝓞 F), ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))` to `fun T v => if v ∈ T then ⟨1, (v.adicCompletionIntegers F).one_mem⟩ else ⟨0, (v.adicCompletionIntegers F).zero_mem⟩`. Set `one' : Π v : HeightOneSpectrum (𝓞 F), ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))` to `fun v => ⟨1, (v.adicCompletionIntegers F).one_mem⟩`. Set `sm` to `RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite`. Set `e : Finset (HeightOneSpectrum (𝓞 F)) → AF F` to `fun T => ((1 : Ainf F), (sm (x T) : Af F))`. Establish `hx : Tendsto x atTop (𝓝 one')`.

Rewrite using `[tendsto_pi_nhds]`. Introduce `v`. Apply `tendsto_atTop_of_eventually_const (i₀ := {v})` to reduce the goal to its premises. Introduce `T hT`. Simplify using `[x, one', hT (Finset.mem_singleton_self v)]`.

Establish `h1 : (sm one' : Af F) = 1`. Use extensionality with `v`. Both sides reduce to the same expression. Establish `he : Tendsto e atTop (𝓝 (1 : AF F))`. Establish `hc : Continuous sm` using `RestrictedProduct.isEmbedding_structureMap.continuous`.

Establish `h2 : Tendsto (fun T => (sm (x T) : Af F)) atTop (𝓝 (1 : Af F))`. Establish `h3` using `(hc.tendsto one').comp hx`. Rewrite `h3` using `[h1]`. Conclude with `h3`. Conclude with `Tendsto.prodMk_nhds tendsto_const_nhds h2`.

Take `⟨T, hT⟩` from `(he.eventually hU).exists`. Use `⟨Finset.univ, T, e T, ⟨?_, ?_, ?_, ?_⟩, hT⟩` and prove the remaining obligations. Introduce `w _`. Both sides reduce to the same expression. Introduce `w hw`.

Conclude with `absurd (Finset.mem_univ w) hw`. Introduce `v hv show ((x T v : v.adicCompletion F)) = 1`. Simplify using `[x, hv]`. Introduce `v hv show ((x T v : v.adicCompletion F)) = 0`. Simplify using `[x, hv]`.
-/
theorem placesIdem_mem_nhds_one (F : Type) [Field F] [NumberField F] (U : Set (AF F)) (hU : U ∈ 𝓝 (1 : AF F)) :
    ∃ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F),
      IsPlacesIdem S₁ S₂ ε ∧ ε ∈ U := by
  classical
  let x : Finset (HeightOneSpectrum (𝓞 F)) → Π v : HeightOneSpectrum (𝓞 F),
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun T v => if v ∈ T then ⟨1, (v.adicCompletionIntegers F).one_mem⟩ else ⟨0, (v.adicCompletionIntegers F).zero_mem⟩
  let one' : Π v : HeightOneSpectrum (𝓞 F), ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun v => ⟨1, (v.adicCompletionIntegers F).one_mem⟩
  let sm := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
  let e : Finset (HeightOneSpectrum (𝓞 F)) → AF F := fun T => ((1 : Ainf F), (sm (x T) : Af F))
  have hx : Tendsto x atTop (𝓝 one') := by
    rw [tendsto_pi_nhds]
    intro v
    apply tendsto_atTop_of_eventually_const (i₀ := {v})
    intro T hT
    simp [x, one', hT (Finset.mem_singleton_self v)]
  have h1 : (sm one' : Af F) = 1 := by
    ext v; rfl
  have he : Tendsto e atTop (𝓝 (1 : AF F)) := by
    have hc : Continuous sm := RestrictedProduct.isEmbedding_structureMap.continuous
    have h2 : Tendsto (fun T => (sm (x T) : Af F)) atTop (𝓝 (1 : Af F)) := by
      have h3 := (hc.tendsto one').comp hx
      rw [h1] at h3
      exact h3
    exact Tendsto.prodMk_nhds tendsto_const_nhds h2
  obtain ⟨T, hT⟩ := (he.eventually hU).exists
  refine ⟨Finset.univ, T, e T, ⟨?_, ?_, ?_, ?_⟩, hT⟩
  · intro w _; rfl
  · intro w hw; exact absurd (Finset.mem_univ w) hw
  · intro v hv
    show ((x T v : v.adicCompletion F)) = 1
    simp [x, hv]
  · intro v hv
    show ((x T v : v.adicCompletion F)) = 0
    simp [x, hv]

/- English proof (translation)
Introduce `F _ _ U hU` and use `placesIdem_mem_nhds_one F U hU`.
-/
theorem placesIdem_tendsto_one : ∀ (F : Type) [Field F] [NumberField F], ∀ U : Set (AF F), U ∈ 𝓝 (1 : AF F) →
    ∃ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F),
      IsPlacesIdem S₁ S₂ ε ∧ ε ∈ U :=
  fun F _ _ U hU => placesIdem_mem_nhds_one F U hU

end GlobalTheory
