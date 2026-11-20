import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroMemBoxF
import GroundTheory.AutomorphicForms.ReductionFinite

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
open IsDedekindDomain

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov.Simple.NormBound

open GroundTheory.Automorphic.Reduction

/- English proof (translation)
Establish `hone : (1 : ℝ) ≤ ∏ a ∈ S, b a`. Use `Finset.prod_le_prod (s := S) (f := fun _ => (1 : ℝ)) (g := b) (fun _ _ => zero_le_one) hb` as an intermediate fact. Simplify using `using this`. Distinguish the cases in `hf : (Function.mulSupport f).Finite`. Use `set c : α → ℝ := fun a => if a ∈ S then b a else 1 with hc`.

Establish `hcs : Function.mulSupport c ⊆ (S : Set α)` using `fun a ha => by`. Assume the negation of the conclusion as `h`. Conclude with `ha (by simp only [hc]; exact if_neg fun h' => h (Finset.mem_coe.2 h'))`. Establish `hcf : (Function.mulSupport c).Finite` using `S.finite_toSet.subset hcs`. Establish `hle : ∏ᶠ a, f a ≤ ∏ᶠ a, c a` using `finprod_le_finprod_of_nonneg hf hcf h0 fun a => by`.

Simplify using `only [hc]`. Use `split_ifs with h`. Conclude with `hS a h`. Conclude with `h1 a h`. Rewrite `hle` using `[finprod_eq_prod_of_mulSupport_subset c hcs]`.

Use `hle.trans (le_of_eq (Finset.prod_congr rfl fun a ha => ?_))` and prove the remaining obligations. Simplify using `only [hc]`. Rewrite using `[if_pos ha]`. Rewrite using `[finprod_of_infinite_mulSupport hf]`. Conclude with `hone`.
-/
theorem finprod_le_prod_of_le {α : Type*} {f b : α → ℝ} (S : Finset α) (h0 : ∀ a, 0 ≤ f a)
    (hS : ∀ a ∈ S, f a ≤ b a) (hb : ∀ a ∈ S, 1 ≤ b a) (h1 : ∀ a, a ∉ S → f a ≤ 1) :
    ∏ᶠ a, f a ≤ ∏ a ∈ S, b a := by
  classical
  have hone : (1 : ℝ) ≤ ∏ a ∈ S, b a := by
    have := Finset.prod_le_prod (s := S) (f := fun _ => (1 : ℝ)) (g := b)
      (fun _ _ => zero_le_one) hb
    simpa using this
  by_cases hf : (Function.mulSupport f).Finite
  · set c : α → ℝ := fun a => if a ∈ S then b a else 1 with hc
    have hcs : Function.mulSupport c ⊆ (S : Set α) := fun a ha => by
      by_contra h
      exact ha (by simp only [hc]; exact if_neg fun h' => h (Finset.mem_coe.2 h'))
    have hcf : (Function.mulSupport c).Finite := S.finite_toSet.subset hcs
    have hle : ∏ᶠ a, f a ≤ ∏ᶠ a, c a :=
      finprod_le_finprod_of_nonneg hf hcf h0 fun a => by
        simp only [hc]
        split_ifs with h
        · exact hS a h
        · exact h1 a h
    rw [finprod_eq_prod_of_mulSupport_subset c hcs] at hle
    refine hle.trans (le_of_eq (Finset.prod_congr rfl fun a ha => ?_))
    simp only [hc]
    rw [if_pos ha]
  · rw [finprod_of_infinite_mulSupport hf]
    exact hone

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

def integralOutside (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (Fin N → AF F) :=
  {y | ∀ i, ∀ v, v ∉ S → (y i).2 v ∈ v.adicCompletionIntegers F}

/- English proof (translation)
Establish `h` using `RestrictedProduct.isOpen_forall_imp_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (fun v => Valued.isOpen_valuationSubring _) (p := fun v => v ∉ S)`. Establish `h2 : IsOpen {a : AF F | ∀ v, v ∉ S → a.2 v ∈ v.adicCompletionIntegers F}` using `h.preimage continuous_snd`. Establish `: integralOutside (N` using `N) S = ⋂ i : Fin N, (fun y : Fin N → AF F => y i) ⁻¹' {a : AF F | ∀ v, v ∉ S → a.2 v ∈ v.adicCompletionIntegers F} := by`. Use extensionality with `y`. Simplify using `only [integralOutside, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]`.

Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun i => h2.preimage (continuous_apply i)`.
-/
theorem isOpen_integralOutside (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (integralOutside (N := N) S) := by
  have h := RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _) (p := fun v => v ∉ S)
  have h2 : IsOpen {a : AF F | ∀ v, v ∉ S → a.2 v ∈ v.adicCompletionIntegers F} :=
    h.preimage continuous_snd
  have : integralOutside (N := N) S = ⋂ i : Fin N, (fun y : Fin N → AF F => y i) ⁻¹'
      {a : AF F | ∀ v, v ∉ S → a.2 v ∈ v.adicCompletionIntegers F} := by
    ext y
    simp only [integralOutside, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  exact isOpen_iInter_of_finite fun i => h2.preimage (continuous_apply i)

/- English proof (translation)
Establish `h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i, (y i).2 v ∈ v.adicCompletionIntegers F` using `Filter.eventually_all.2 fun i => (y i).2.2`. Establish `hfin` using `Filter.eventually_cofinite.1 h`. Use `⟨hfin.toFinset, fun i v hv => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Conclude with `hv (hfin.mem_toFinset.2 fun h' => hc (h' i))`.
-/
theorem exists_mem_integralOutside (y : Fin N → AF F) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), y ∈ integralOutside S := by
  have h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i, (y i).2 v ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => (y i).2.2
  have hfin := Filter.eventually_cofinite.1 h
  refine ⟨hfin.toFinset, fun i v hv => ?_⟩
  by_contra hc
  exact hv (hfin.mem_toFinset.2 fun h' => hc (h' i))

/- English proof (translation)
Take `⟨T, hT⟩` from `hD.elim_finite_subcover (fun S : Finset (HeightOneSpectrum (𝓞 F)) => integralOutside (N := N) S) isOpen_integralOutside (fun y _ => by`. Take `⟨S, hS⟩` from `exists_mem_integralOutside y`. Conclude with `Set.mem_iUnion.2 ⟨S, hS⟩)`. Use `⟨T.sup id, fun y hy i v hv => ?_⟩` and prove the remaining obligations. Take `⟨S, hS, hyS⟩` from `Set.mem_iUnion₂.1 (hT hy)`.

Conclude with `hyS i v fun h => hv (Finset.mem_sup.2 ⟨S, hS, h⟩)`.
-/
theorem exists_finset_subset_integralOutside {D : Set (Fin N → AF F)} (hD : IsCompact D) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), D ⊆ integralOutside S := by
  classical
  obtain ⟨T, hT⟩ := hD.elim_finite_subcover
    (fun S : Finset (HeightOneSpectrum (𝓞 F)) => integralOutside (N := N) S)
    isOpen_integralOutside (fun y _ => by
      obtain ⟨S, hS⟩ := exists_mem_integralOutside y
      exact Set.mem_iUnion.2 ⟨S, hS⟩)
  refine ⟨T.sup id, fun y hy i v hv => ?_⟩
  obtain ⟨S, hS, hyS⟩ := Set.mem_iUnion₂.1 (hT hy)
  exact hyS i v fun h => hv (Finset.mem_sup.2 ⟨S, hS, h⟩)

/- English proof (translation)
The claim follows from `(pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => (Valued.toNormedField.norm_le_one_iff).2 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h i))`.
-/
theorem norm_finComp_le_one {y : Fin N → AF F} {v : HeightOneSpectrum (𝓞 F)}
    (h : ∀ i, (y i).2 v ∈ v.adicCompletionIntegers F) : ‖finComp v y‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i =>
    (Valued.toNormedField.norm_le_one_iff).2
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h i))

/- English proof (translation)
The claim follows from `continuous_euclidNorm.comp (continuous_pi fun i => (continuous_apply w).comp (continuous_fst.comp (continuous_apply i)))`.
-/
theorem continuous_euclidNorm_infComp (w : InfinitePlace F) :
    Continuous fun y : Fin N → AF F => euclidNorm (infComp w y) :=
  continuous_euclidNorm.comp (continuous_pi fun i =>
    (continuous_apply w).comp (continuous_fst.comp (continuous_apply i)))

/- English proof (translation)
The claim follows from `(continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp (continuous_apply i))).norm`.
-/
theorem continuous_norm_finComp (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun y : Fin N → AF F => ‖finComp v y‖ :=
  (continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp
    (continuous_snd.comp (continuous_apply i))).norm

end GlobalTheory.CompanionTheory.RedCov.Simple.NormBound

namespace GlobalTheory.CompanionTheory.RedCov.Simple

open GroundTheory.Automorphic.Reduction NormBound in

/- English proof (translation)
Introduce `F _ _ N D hD`. Take `⟨S, hS⟩` from `exists_finset_subset_integralOutside hD`. Use `choose a ha1 ha using fun w : InfinitePlace F => exists_one_le_bound hD (continuous_euclidNorm_infComp (N := N) w)`. Use `choose b hb1 hb using fun v : HeightOneSpectrum (𝓞 F) => exists_one_le_bound hD (continuous_norm_finComp (N := N) v)`. Establish `hA : (1 : ℝ) ≤ ∏ w, a w ^ w.mult`.

Use `Finset.prod_le_prod (s := Finset.univ) (f := fun _ : InfinitePlace F => (1 : ℝ)) (g := fun w => a w ^ w.mult) (fun _ _ => zero_le_one) (fun w _ => one_le_pow₀ (ha1 w))` as an intermediate fact. Simplify using `using this`. Establish `hB : (1 : ℝ) ≤ ∏ v ∈ S, b v`. Use `Finset.prod_le_prod (s := S) (f := fun _ => (1 : ℝ)) (g := b) (fun _ _ => zero_le_one) (fun v _ => hb1 v)` as an intermediate fact. Simplify using `using this`.

Use `⟨(∏ w, a w ^ w.mult) * ∏ v ∈ S, b v, by positivity, fun y hy => ?_⟩` and prove the remaining obligations. Use `mul_le_mul ?_ ?_ (finprod_nonneg fun _ => norm_nonneg _) (by positivity)` and prove the remaining obligations. Conclude with `Finset.prod_le_prod (fun w _ => pow_nonneg (euclidNorm_nonneg _) _) fun w _ => pow_le_pow_left₀ (euclidNorm_nonneg _) (ha w y hy) _`. Conclude with `finprod_le_prod_of_le S (fun _ => norm_nonneg _) (fun v _ => hb v y hy) (fun v _ => hb1 v) fun v hv => norm_finComp_le_one fun i => hS hy i v hv`.
-/
theorem exists_adelicNorm_le_of_isCompact :
    ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (D : Set (Fin N → AF F)), IsCompact D →
      ∃ P : ℝ, 0 < P ∧ ∀ y ∈ D, GroundTheory.Automorphic.Reduction.adelicNorm y ≤ P := by
  intro F _ _ N D hD
  classical
  obtain ⟨S, hS⟩ := exists_finset_subset_integralOutside hD
  choose a ha1 ha using fun w : InfinitePlace F =>
    exists_one_le_bound hD (continuous_euclidNorm_infComp (N := N) w)
  choose b hb1 hb using fun v : HeightOneSpectrum (𝓞 F) =>
    exists_one_le_bound hD (continuous_norm_finComp (N := N) v)
  have hA : (1 : ℝ) ≤ ∏ w, a w ^ w.mult := by
    have := Finset.prod_le_prod (s := Finset.univ) (f := fun _ : InfinitePlace F => (1 : ℝ))
      (g := fun w => a w ^ w.mult) (fun _ _ => zero_le_one)
      (fun w _ => one_le_pow₀ (ha1 w))
    simpa using this
  have hB : (1 : ℝ) ≤ ∏ v ∈ S, b v := by
    have := Finset.prod_le_prod (s := S) (f := fun _ => (1 : ℝ)) (g := b)
      (fun _ _ => zero_le_one) (fun v _ => hb1 v)
    simpa using this
  refine ⟨(∏ w, a w ^ w.mult) * ∏ v ∈ S, b v, by positivity, fun y hy => ?_⟩
  refine mul_le_mul ?_ ?_ (finprod_nonneg fun _ => norm_nonneg _) (by positivity)
  · exact Finset.prod_le_prod (fun w _ => pow_nonneg (euclidNorm_nonneg _) _)
      fun w _ => pow_le_pow_left₀ (euclidNorm_nonneg _) (ha w y hy) _
  · exact finprod_le_prod_of_le S (fun _ => norm_nonneg _) (fun v _ => hb v y hy)
      (fun v _ => hb1 v) fun v hv => norm_finComp_le_one fun i => hS hy i v hv

end GlobalTheory.CompanionTheory.RedCov.Simple

end
