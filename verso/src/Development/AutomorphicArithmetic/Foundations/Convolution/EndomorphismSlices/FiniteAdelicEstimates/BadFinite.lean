import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.CuspReadPTrue
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.ReadOne
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.ValLim
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.InfLimit
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.KgFacts
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.SatCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Places

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

/- English proof (translation)
Take `⟨-, hcp, -, -⟩` from `UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.places E`. Establish `hinj : Function.Injective (cPl : Pl E → Pl E)` using `fun x y h => by`. Rewrite using `[← (hcp x).1, ← (hcp y).1, h]`. Use `(Z.finite_toSet.union (Z.finite_toSet.preimage hinj.injOn)).subset fun w hw => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hc`.

Conclude with `hw ⟨fun h => hc (Or.inl h), fun h => hc (Or.inr h)⟩`.
-/
private theorem bad_finite {E : Type} [Field E] [NumberField E] [IsCMField E] (Z : Finset (Pl E)) :
    {w : Pl E | ¬ Off Z w}.Finite := by
  obtain ⟨-, hcp, -, -⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.places E
  have hinj : Function.Injective (cPl : Pl E → Pl E) := fun x y h => by
    rw [← (hcp x).1, ← (hcp y).1, h]
  refine (Z.finite_toSet.union (Z.finite_toSet.preimage hinj.injOn)).subset fun w hw => ?_
  by_contra hc
  exact hw ⟨fun h => hc (Or.inl h), fun h => hc (Or.inr h)⟩

/- English proof (translation)
Take `⟨-, hcp, -, hsec⟩` from `UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.places E`. Establish `key : ∀ u ∈ T, Off Z u` using `fun u hu => by`. Use `⟨Finset.disjoint_left.1 hd hu, fun hc => ?_⟩` and prove the remaining obligations. Establish `e` using `(hsec S hS u).2 (hT u hu) (hZ _ hc).1`. Rewrite `hc` using `[e]`.

Conclude with `Finset.disjoint_left.1 hd hu hc`. Break down `hw with h | h` into its components or cases. Conclude with `key w h`. Establish `h'` using `key _ h`. Rewrite `h'` using `[Off, (hcp w).1]`.

Conclude with `⟨h'.2, h'.1⟩`.
-/
private theorem off_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {S : Set (Pl E)}
    (hS : IsSection S) {Z T : Finset (Pl E)} (hZ : SplitIn S Z) (hT : ∀ w ∈ T, w ∈ S)
    (hd : Disjoint T Z) (w : Pl E) (hw : w ∈ T ∨ cPl w ∈ T) : Off Z w := by
  obtain ⟨-, hcp, -, hsec⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.places E
  have key : ∀ u ∈ T, Off Z u := fun u hu => by
    refine ⟨Finset.disjoint_left.1 hd hu, fun hc => ?_⟩
    have e := (hsec S hS u).2 (hT u hu) (hZ _ hc).1
    rw [e] at hc
    exact Finset.disjoint_left.1 hd hu hc
  rcases hw with h | h
  · exact key w h
  · have h' := key _ h
    rw [Off, (hcp w).1] at h'
    exact ⟨h'.2, h'.1⟩

/- English proof (translation)
Introduce `P hP E _ _ _ a b l₁ l₂`. Take `⟨W₁, W₂, hW₁, hW₂, hR⟩` from `readOne E a b l₁ l₂`. Use `⟨W₁, hW₁, fun D A S Z L hS hZ X hX hXc => ?_⟩` and prove the remaining obligations. Take `⟨o₁, -, k₁⟩` from `kgFacts E a S Z L.L₁ hS hZ (fun w => ⟨L.open₁ w, L.le₁ w⟩) (fun w hw => (L.off w hw).1)`. Take `⟨o₂, -, k₂⟩` from `kgFacts E b S Z L.L₂ hS hZ (fun w => ⟨L.open₂ w, L.le₂ w⟩) (fun w hw => (L.off w hw).2)`.

Establish `off_of : ∀ {w : Pl E}, w ∉ {w : Pl E | ¬ Off Z w} → Off Z w` using `fun h => Classical.byContradiction fun hn => h hn`. Establish `of_off : ∀ {w : Pl E}, Off Z w → w ∉ {w : Pl E | ¬ Off Z w}` using `fun h h' => h' h`. Take `⟨J₁, hJ₁, D₁, C₁, a₁, p₁, r₁⟩` from `hP E a (Kg S L.L₁) W₁ {w | ¬ Off Z w} (mW l₁) X o₁ hW₁ (bad_finite Z) (fun w hw k hk => k₁ w (off_of hw) k hk) hX hXc`. Take `⟨J₂, hJ₂, D₂, C₂, a₂, p₂, r₂⟩` from `hP E b (Kg S L.L₂) W₂ {w | ¬ Off Z w} (mW l₂) ∅ o₂ hW₂ (bad_finite Z) (fun w hw k hk => k₂ w (off_of hw) k hk) Set.subsingleton_empty (fun π h => absurd h (Set.notMem_empty π))`. Use `⟨J₁ × J₂, inferInstance, fun j => D₁ j.1, fun j => D₂ j.2, fun j => C₁ j.1, fun j => C₂ j.2, fun j => ⟨(a₁ j.1).1, fun w hw => ⟨(a₁ j.1).2 w (of_off hw), (a₂ j.2).2 w (of_off hw)⟩⟩, fun j => ⟨p₁ j.1, p₂ j.2⟩, ?_⟩` and prove the remaining obligations.

Introduce `T e₁ e₂ g s hT hd hSees harch hReal`. Take `⟨sk, f, hsk, hf⟩` from `hReal`. Establish `hr` using `fun k => hR D A S Z L hS hZ T e₁ e₂ (sk k) (f k) hT hd (hf k).1 (hf k).2.1`. Use `choose χa χb φ₁ φ₂ B₁ B₂ ha hb hsl n₁ u₁ t₁ c₁ n₂ u₂ t₂ c₂ hoff hv using hr`. Take `⟨h0, ca, cb⟩` from `infLimit E a b l₁ l₂ D A S Z L T e₁ e₂ s sk χa χb harch hsk ha hb`.

Take `⟨j₁, s₁, hs₁, q₁⟩` from `r₁ φ₁ (fun k => mOf (χa k)) B₁ (fun k => ⟨n₁ k, u₁ k, t₁ k, c₁ k, fun w hw => (hoff k w (off_of hw)).2.2.1, fun π hπ ψ hψ z => by`. Take `⟨i, m₂, hi⟩` from `hsl k`. Conclude with `hSees (f k) (hf k).2.2 i m₂ (φ₁ k) hi (n₁ k) (t₁ k) π hπ ψ hψ z⟩) ca`. Take `⟨j₂, s₂, hs₂, q₂⟩` from `r₂ (fun k => φ₂ (s₁ k)) (fun k => mOf (χb (s₁ k))) (fun k => B₂ (s₁ k)) (fun k => ⟨n₂ _, u₂ _, t₂ _, c₂ _, fun w hw => (hoff _ w (off_of hw)).2.2.2, fun π hπ => absurd hπ (Set.notMem_empty π)⟩) (fun τ ε hε => hs₁.tendsto_atTop.eventually (cb τ ε hε))`. Use `⟨(j₁, j₂), ?_⟩` and prove the remaining obligations.

Establish `hut : Tendsto (fun k => s₁ (s₂ k)) atTop atTop` using `(hs₁.comp hs₂).tendsto_atTop`. Establish `lim₁ : Tendsto (fun k => val T e₁ e₂ (B₁ (s₁ (s₂ k))) (B₂ (s₁ (s₂ k)))) atTop (𝓝 (val T e₁ e₂ (C₁ j₁) (C₂ j₂)))`. Use `valLim E a b T e₁ e₂ _ _ _ _ fun w hw => ?_` and prove the remaining obligations. Establish `hw' : Off Z w` using `off_of_mem hS hZ hT.1 hd w hw`. Conclude with `⟨satCard E a (D₁ j₁) w _ ((a₁ j₁).2 w (of_off hw')), satCard E b (D₂ j₂) w _ ((a₂ j₂).2 w (of_off hw')), fun k => ⟨(hoff _ w hw').1, (hoff _ w hw').2.1⟩, fun i => (q₁ w (of_off hw') i).comp hs₂.tendsto_atTop, fun i => q₂ w (of_off hw') i⟩`.

Establish `hne : s (.inl ()) ≠ 0` using `by rw [h0]; exact one_ne_zero`. Establish `lim₂` using `((hsk (.inr (.inr (.inr ())))).div (hsk (.inl ())) hne).comp hut`. Rewrite `lim₂` using `[h0, div_one]`. Conclude with `tendsto_nhds_unique (lim₂.congr fun k => hv _) lim₁`.
-/
theorem rRead : RRead := by
  intro P hP E _ _ _ a b l₁ l₂
  obtain ⟨W₁, W₂, hW₁, hW₂, hR⟩ := readOne E a b l₁ l₂
  refine ⟨W₁, hW₁, fun D A S Z L hS hZ X hX hXc => ?_⟩
  obtain ⟨o₁, -, k₁⟩ := kgFacts E a S Z L.L₁ hS hZ (fun w => ⟨L.open₁ w, L.le₁ w⟩)
    (fun w hw => (L.off w hw).1)
  obtain ⟨o₂, -, k₂⟩ := kgFacts E b S Z L.L₂ hS hZ (fun w => ⟨L.open₂ w, L.le₂ w⟩)
    (fun w hw => (L.off w hw).2)
  have off_of : ∀ {w : Pl E}, w ∉ {w : Pl E | ¬ Off Z w} → Off Z w :=
    fun h => Classical.byContradiction fun hn => h hn
  have of_off : ∀ {w : Pl E}, Off Z w → w ∉ {w : Pl E | ¬ Off Z w} := fun h h' => h' h
  obtain ⟨J₁, hJ₁, D₁, C₁, a₁, p₁, r₁⟩ := hP E a (Kg S L.L₁) W₁ {w | ¬ Off Z w} (mW l₁) X o₁ hW₁
    (bad_finite Z) (fun w hw k hk => k₁ w (off_of hw) k hk) hX hXc
  obtain ⟨J₂, hJ₂, D₂, C₂, a₂, p₂, r₂⟩ := hP E b (Kg S L.L₂) W₂ {w | ¬ Off Z w} (mW l₂) ∅ o₂ hW₂
    (bad_finite Z) (fun w hw k hk => k₂ w (off_of hw) k hk) Set.subsingleton_empty
    (fun π h => absurd h (Set.notMem_empty π))
  refine ⟨J₁ × J₂, inferInstance, fun j => D₁ j.1, fun j => D₂ j.2, fun j => C₁ j.1, fun j => C₂ j.2,
    fun j => ⟨(a₁ j.1).1, fun w hw => ⟨(a₁ j.1).2 w (of_off hw), (a₂ j.2).2 w (of_off hw)⟩⟩,
    fun j => ⟨p₁ j.1, p₂ j.2⟩, ?_⟩
  intro T e₁ e₂ g s hT hd hSees harch hReal
  obtain ⟨sk, f, hsk, hf⟩ := hReal
  have hr := fun k => hR D A S Z L hS hZ T e₁ e₂ (sk k) (f k) hT hd (hf k).1 (hf k).2.1
  choose χa χb φ₁ φ₂ B₁ B₂ ha hb hsl n₁ u₁ t₁ c₁ n₂ u₂ t₂ c₂ hoff hv using hr
  obtain ⟨h0, ca, cb⟩ := infLimit E a b l₁ l₂ D A S Z L T e₁ e₂ s sk χa χb harch hsk ha hb
  obtain ⟨j₁, s₁, hs₁, q₁⟩ := r₁ φ₁ (fun k => mOf (χa k)) B₁
    (fun k => ⟨n₁ k, u₁ k, t₁ k, c₁ k, fun w hw => (hoff k w (off_of hw)).2.2.1, fun π hπ ψ hψ z => by
      obtain ⟨i, m₂, hi⟩ := hsl k
      exact hSees (f k) (hf k).2.2 i m₂ (φ₁ k) hi (n₁ k) (t₁ k) π hπ ψ hψ z⟩) ca
  obtain ⟨j₂, s₂, hs₂, q₂⟩ := r₂ (fun k => φ₂ (s₁ k)) (fun k => mOf (χb (s₁ k))) (fun k => B₂ (s₁ k))
    (fun k => ⟨n₂ _, u₂ _, t₂ _, c₂ _, fun w hw => (hoff _ w (off_of hw)).2.2.2,
      fun π hπ => absurd hπ (Set.notMem_empty π)⟩)
    (fun τ ε hε => hs₁.tendsto_atTop.eventually (cb τ ε hε))
  refine ⟨(j₁, j₂), ?_⟩
  have hut : Tendsto (fun k => s₁ (s₂ k)) atTop atTop := (hs₁.comp hs₂).tendsto_atTop
  have lim₁ : Tendsto (fun k => val T e₁ e₂ (B₁ (s₁ (s₂ k))) (B₂ (s₁ (s₂ k)))) atTop
      (𝓝 (val T e₁ e₂ (C₁ j₁) (C₂ j₂))) := by
    refine valLim E a b T e₁ e₂ _ _ _ _ fun w hw => ?_
    have hw' : Off Z w := off_of_mem hS hZ hT.1 hd w hw
    exact ⟨satCard E a (D₁ j₁) w _ ((a₁ j₁).2 w (of_off hw')),
      satCard E b (D₂ j₂) w _ ((a₂ j₂).2 w (of_off hw')),
      fun k => ⟨(hoff _ w hw').1, (hoff _ w hw').2.1⟩,
      fun i => (q₁ w (of_off hw') i).comp hs₂.tendsto_atTop,
      fun i => q₂ w (of_off hw') i⟩
  have hne : s (.inl ()) ≠ 0 := by rw [h0]; exact one_ne_zero
  have lim₂ := ((hsk (.inr (.inr (.inr ())))).div (hsk (.inl ())) hne).comp hut
  rw [h0, div_one] at lim₂
  exact tendsto_nhds_unique (lim₂.congr fun k => hv _) lim₁

end UpperTheory.Zero.ConvolutionTheory.EB
