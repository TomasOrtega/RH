import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.XgDefs

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

/- English proof (translation)
Establish `hf` using `Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w 2) (GlobalTheory.LFun.Tj_mem_hecke (n := 2) hϖ j).2`. Use `⟨hf.toFinset, fun F => finsum_eq_sum_of_support_subset _ fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[Set.Finite.coe_toFinset]`. Conclude with `left_ne_zero_of_mul hx`.
-/
private theorem finsum_Tj_eq {E : Type} [Field E] [NumberField E] {w : H.P E} {ϖ : w.adicCompletion E}
    (hϖ : Formalism.UG.IsUnifV E w ϖ) (j : ℕ) :
    ∃ t : Finset (GL (Fin 2) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w 2),
      ∀ F : GL (Fin 2) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w 2 → ℂ,
        ∑ᶠ x, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j x.out * F x =
          ∑ x ∈ t, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j x.out * F x := by
  have hf := Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w 2)
    (GlobalTheory.LFun.Tj_mem_hecke (n := 2) hϖ j).2
  refine ⟨hf.toFinset, fun F => finsum_eq_sum_of_support_subset _ fun x hx => ?_⟩
  rw [Set.Finite.coe_toFinset]
  exact left_ne_zero_of_mul hx

/- English proof (translation)
Introduce `E _ _ w ι s c φ B hs hF hE`. Take `⟨i₀, -⟩` from `hs`. Use `⟨fun g k hk => ?_, fun g => ⟨(hE i₀ g).card, fun y k hk => ?_, fun ϖ hϖ j hj y => ?_⟩⟩` and prove the remaining obligations. Simplify using `only [fun i => hF i g k hk]`. Simplify using `only [fun i => (hE i g).inv y k hk]`.

Take `⟨t, ht⟩` from `finsum_Tj_eq (w := w) hϖ j`. Rewrite using `[ht]`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `e` using `(hE i g).eig ϖ hϖ j hj y`. Rewrite `e` using `[ht]`. Rewrite using `[mul_left_comm, ← e, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun x _ => mul_left_comm _ _ _`.
-/
theorem UpperTheory.fixed_and_heckeEigen_of_finset_linearCombination :
    ∀ (E : Type) [Field E] [NumberField E] (w : H.P E) (ι : Type) (s : Finset ι) (c : ι → ℂ) (φ : ι → GL (Fin 2) (A E) → ℂ) (B : Multiset ℂˣ), s.Nonempty → (∀ i, H.Fix w (φ i)) → (∀ i, EigAt w B (φ i)) → H.Fix w (fun g => ∑ i ∈ s, c i * φ i g) ∧ EigAt w B (fun g => ∑ i ∈ s, c i * φ i g) := by
  intro E _ _ w ι s c φ B hs hF hE
  obtain ⟨i₀, -⟩ := hs
  refine ⟨fun g k hk => ?_, fun g => ⟨(hE i₀ g).card, fun y k hk => ?_, fun ϖ hϖ j hj y => ?_⟩⟩
  · simp only [fun i => hF i g k hk]
  · simp only [fun i => (hE i g).inv y k hk]
  · obtain ⟨t, ht⟩ := finsum_Tj_eq (w := w) hϖ j
    rw [ht]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e := (hE i g).eig ϖ hϖ j hj y
    rw [ht] at e
    rw [mul_left_comm, ← e, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => mul_left_comm _ _ _
