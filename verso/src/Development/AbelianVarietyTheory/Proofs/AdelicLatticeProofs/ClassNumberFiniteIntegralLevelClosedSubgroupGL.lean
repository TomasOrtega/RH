import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AdelicPairReducedBasisStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GlFreeAlgebraToSpecialLinearEmbInjectiveHomStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsQGroupWeilRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GlFreeAlgebraEmbIntegralAndRationalStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteAdelicDoubleCosetsOfRationalSLSubgroupStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.ClassFin

/- English proof (translation)
Introduce `F _ _ n S hS`. Take `⟨R, _, _, R₀, _, b, hAP, hred, hb, hint⟩` from `GlobalTheory.T.adelic_pair_reduced_basis F _ (NumberField.RingOfIntegers.basis F)`. Take `⟨Γ, hΓ, hcorr⟩` from `GlobalTheory.T.exists_isQGroup_weilRestriction_alt F _ (NumberField.integralBasis F) n S hS`. Establish `hbF : ∀ i, b i = algebraMap F (FiniteAdeleRing (𝓞 F) F) (NumberField.integralBasis F i)`. Introduce `i`.

Rewrite using `[hb i, NumberField.integralBasis_apply]`. Establish `hA` using `hcorr R (FiniteAdeleRing (𝓞 F) F) b hbF`. Establish `hQ` using `hcorr ℚ F (NumberField.integralBasis F) (fun i => rfl)`. Take `⟨T₀, hT₀, hdec⟩` from `GlobalTheory.T.finiteAdelicDoubleCosets_of_rational_SL_subgroup _ Γ R R₀ hΓ hAP`. Set `lift : Matrix ((Fin n × _) ⊕ Unit) ((Fin n × _) ⊕ Unit) R → GL (Fin n) (FiniteAdeleRing (𝓞 F) F)` to `fun s => if h : ∃ g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧ s = GlobalTheory.ClassFin.emb b g then h.choose …`.

Establish `hlift : ∀ s ∈ pts Γ R, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((lift s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧ s = GlobalTheory.ClassFin.emb b (lift s)`. Introduce `s hs`. Establish `h` using `hA.1 s hs`. Simplify using `only [lift, dif_pos h]`. Conclude with `h.choose_spec`.

Take `⟨hemb1, hembmul, -, hembinj⟩` from `GlobalTheory.T.glFreeAlgebraToSpecialLinearEmb_injective_hom R (FiniteAdeleRing (𝓞 F) F) _ (Fin n) b`. Use `⟨T₀.image lift, ?_, ?_⟩` and prove the remaining obligations. Introduce `t ht`. Take `⟨s, hs, rfl⟩` from `Finset.mem_image.1 ht`. Conclude with `(hlift s (hT₀ s hs)).1`.

Introduce `x hx`. Take `⟨γ₀, hγ₀, s, hs, u₀, hu₀, hu₀int, hx₀⟩` from `hdec _ (hA.2 hred x hx)`. Take `⟨γ, hγS, rfl⟩` from `hQ.1 γ₀ hγ₀`. Take `⟨u, huS, rfl⟩` from `hA.1 u₀ hu₀`. Take `⟨hsS, hsemb⟩` from `hlift s (hT₀ s hs)`.

Establish `h1 : ∀ i, b.repr 1 i ∈ R₀`. Use `(hint 1).1 ?_` and prove the remaining obligations. Introduce `v`. Conclude with `(HeightOneSpectrum.adicCompletionIntegers F v).one_mem`. Establish `hunits` using `GlobalTheory.T.glFreeAlgebraEmb_integral_and_rational.1 R _ _ (Fin n) b R₀ u h1 hu₀int`.

Use `⟨γ, hγS, lift s, Finset.mem_image_of_mem lift hs, u, huS, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Conclude with `⟨(hint _).2 (fun k => (hunits i j k).1), (hint _).2 (fun k => (hunits i j k).2)⟩`. Apply `hembinj` to reduce the goal to its premises. Simplify using `only [hembmul]`.

Rewrite using `[hx₀, ← hsemb, GlobalTheory.T.glFreeAlgebraEmb_integral_and_rational.2 F _ (NumberField.integralBasis F) (Fin n) R _ b hbF γ]`.
-/
theorem classFinite_integralLevel : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), (∀ (B : Type) [CommRing B] [Algebra F B], (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((1 : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) ∧ (∀ g h : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g * h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) ∧ ∀ g : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g⁻¹ : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) → ∃ T : Finset (GL (Fin n) (FiniteAdeleRing (𝓞 F) F)), (∀ s ∈ T, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0)) ∧ ∀ x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) → ∃ γ : GL (Fin n) F, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((γ : GL (Fin n) (F)) : Matrix (Fin n) (Fin n) (F)) ij.1 ij.2) P = 0) ∧ ∃ s ∈ T, ∃ u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧ (∀ i j, (∀ v, (((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ (∀ v, ((((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)) ∧ x = Units.map (RingHom.mapMatrix (algebraMap F (FiniteAdeleRing (𝓞 F) F))).toMonoidHom γ * s * u := by
  intro F _ _ n S hS
  classical

  obtain ⟨R, _, _, R₀, _, b, hAP, hred, hb, hint⟩ :=
    GlobalTheory.T.adelic_pair_reduced_basis F _ (NumberField.RingOfIntegers.basis F)
  obtain ⟨Γ, hΓ, hcorr⟩ := GlobalTheory.T.exists_isQGroup_weilRestriction_alt F _ (NumberField.integralBasis F) n S hS
  have hbF : ∀ i, b i = algebraMap F (FiniteAdeleRing (𝓞 F) F) (NumberField.integralBasis F i) := by
    intro i
    rw [hb i, NumberField.integralBasis_apply]
  have hA := hcorr R (FiniteAdeleRing (𝓞 F) F) b hbF
  have hQ := hcorr ℚ F (NumberField.integralBasis F) (fun i => rfl)
  obtain ⟨T₀, hT₀, hdec⟩ := GlobalTheory.T.finiteAdelicDoubleCosets_of_rational_SL_subgroup _ Γ R R₀ hΓ hAP

  let lift : Matrix ((Fin n × _) ⊕ Unit) ((Fin n × _) ⊕ Unit) R → GL (Fin n) (FiniteAdeleRing (𝓞 F) F) :=
    fun s => if h : ∃ g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F),
        (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n =>
          ((g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧
        s = GlobalTheory.ClassFin.emb b g then h.choose else 1
  have hlift : ∀ s ∈ pts Γ R, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n =>
      ((lift s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧
      s = GlobalTheory.ClassFin.emb b (lift s) := by
    intro s hs
    have h := hA.1 s hs
    simp only [lift, dif_pos h]
    exact h.choose_spec
  obtain ⟨hemb1, hembmul, -, hembinj⟩ := GlobalTheory.T.glFreeAlgebraToSpecialLinearEmb_injective_hom R (FiniteAdeleRing (𝓞 F) F) _ (Fin n) b
  refine ⟨T₀.image lift, ?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    exact (hlift s (hT₀ s hs)).1
  · intro x hx
    obtain ⟨γ₀, hγ₀, s, hs, u₀, hu₀, hu₀int, hx₀⟩ := hdec _ (hA.2 hred x hx)
    obtain ⟨γ, hγS, rfl⟩ := hQ.1 γ₀ hγ₀
    obtain ⟨u, huS, rfl⟩ := hA.1 u₀ hu₀
    obtain ⟨hsS, hsemb⟩ := hlift s (hT₀ s hs)
    have h1 : ∀ i, b.repr 1 i ∈ R₀ := by
      refine (hint 1).1 ?_
      intro v
      exact (HeightOneSpectrum.adicCompletionIntegers F v).one_mem
    have hunits := GlobalTheory.T.glFreeAlgebraEmb_integral_and_rational.1 R _ _ (Fin n) b R₀ u h1 hu₀int
    refine ⟨γ, hγS, lift s, Finset.mem_image_of_mem lift hs, u, huS, ?_, ?_⟩
    · intro i j
      exact ⟨(hint _).2 (fun k => (hunits i j k).1), (hint _).2 (fun k => (hunits i j k).2)⟩
    · apply hembinj
      simp only [hembmul]
      rw [hx₀, ← hsemb, GlobalTheory.T.glFreeAlgebraEmb_integral_and_rational.2 F _ (NumberField.integralBasis F) (Fin n) R _ b hbF γ]

end GlobalTheory.ClassFin
