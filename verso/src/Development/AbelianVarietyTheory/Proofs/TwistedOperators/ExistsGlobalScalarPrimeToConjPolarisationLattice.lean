import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlacesProductIdealProperOddCoprime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPeriodIdealLocalGeneratorAtSplitPoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

noncomputable section

namespace GlobalTheory.GenChoice

/- English proof (translation)
Take `⟨a, I, ha, hAI⟩` from `FractionalIdeal.exists_eq_spanSingleton_mul A`. Establish `hI : I ≠ ⊥`. Introduce and unpack `rfl`. Apply `hA` to reduce the goal to its premises. Rewrite using `[hAI, FractionalIdeal.coeIdeal_bot, mul_zero]`.

Establish `hinj` using `IsFractionRing.injective R K`. Choose the witnesses or unpack the hypotheses as in `⟨g, hgI, hg0, hgQ⟩ : ∃ g ∈ I, g ≠ 0 ∧ ∀ i ∈ Qs, ¬ Ideal.span {g} ≤ I * Q i := by`. Break down `Qs.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩` into its components or cases. Take `⟨g, hg, hg0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI`. Conclude with `⟨g, hg, hg0, by simp⟩`.

Establish `hQp0 : (∏ i ∈ Qs, Q i) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i hi => hQ0 i hi`. Take `⟨g, hg⟩` from `IsDedekindDomain.exists_sup_span_eq (Ideal.mul_le_left : I * (∏ i ∈ Qs, Q i) ≤ I) (mul_ne_zero hI hQp0)`. Establish `hgI : g ∈ I`. Rewrite using `[← hg]`. Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)`.

Establish `key : ∀ i ∈ Qs, ¬ Ideal.span {g} ≤ I * Q i`. Introduce `i hi h`. Establish `hle : (∏ j ∈ Qs, Q j) ≤ Q i` using `Ideal.prod_le_inf.trans (Finset.inf_le hi)`. Establish `h1 : I ≤ I * Q i`. Combine the equalities or inequalities in the displayed calculation.

Establish `h2 : I * Q i = I * ⊤`. Rewrite using `[Ideal.mul_top]`. Conclude with `le_antisymm Ideal.mul_le_left h1`. Conclude with `(hQ i hi).ne_top (mul_left_cancel₀ hI h2)`. Use `⟨g, hgI, ?_, key⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Apply `key i0 hi0` to reduce the goal to its premises. Rewrite using `[Ideal.span_singleton_eq_bot.2 rfl]`. Conclude with `bot_le`. Take `⟨J, hJ⟩` from `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hgI)`.

Establish `hJQ : ∀ i ∈ Qs, ¬ J ≤ Q i` using `fun i hi h => hgQ i hi (by rw [hJ]; exact Ideal.mul_mono_right h)`. Choose the witnesses or unpack the hypotheses as in `⟨s, hsJ, hsQ⟩ : ∃ s ∈ J, ∀ i ∈ Qs, s ∉ Q i := by`. Break down `Qs.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩` into its components or cases. Conclude with `⟨0, J.zero_mem, by simp⟩`. Assume the negation of the conclusion as `hcon push_neg at hcon`.

Establish `hsub : (J : Set R) ⊆ ⋃ i ∈ (Qs : Set ι), (Q i : Set R)`. Introduce `x hx`. Take `⟨i, hi, hxi⟩` from `hcon x hx`. Conclude with `Set.mem_biUnion hi hxi`. Take `⟨i, hi, hle⟩` from `(Ideal.subset_union_prime i0 i0 (fun i hi _ _ => hQ i hi)).1 hsub`.

Conclude with `hJQ i hi hle`. Establish `ha' : algebraMap R K a ≠ 0`. Introduce `h; exact ha (hinj (by rw [h, map_zero]))`. Establish `hg' : algebraMap R K g ≠ 0`. Introduce `h; exact hg0 (hinj (by rw [h, map_zero]))`.

Use `⟨(algebraMap R K a)⁻¹ * algebraMap R K g, mul_ne_zero (inv_ne_zero ha') hg', s, hsQ, ?_, ?_⟩` and prove the remaining obligations. Introduce `c hc`. Rewrite `hc` using `[hAI, FractionalIdeal.mem_singleton_mul]`. Take `⟨y, hy, rfl⟩` from `hc`. Take `⟨x, hx, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hy`.

Establish `hxs : x * s ∈ Ideal.span {g}`. Rewrite using `[hJ]`. Conclude with `Ideal.mul_mem_mul hx hsJ`. Take `⟨r, hr⟩` from `Ideal.mem_span_singleton'.1 hxs`. Use `⟨r, ?_⟩` and prove the remaining obligations.

Establish `hr' : algebraMap R K r * algebraMap R K g = algebraMap R K x * algebraMap R K s`. Rewrite using `[← map_mul, ← map_mul, hr]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `hr'`. Rewrite using `[hAI, FractionalIdeal.mem_singleton_mul]`.

Use `⟨algebraMap R K (s * g), FractionalIdeal.mem_coeIdeal_of_mem _ (I.mul_mem_left s hgI), ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_gen_avoid {R K ι : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (A : FractionalIdeal (nonZeroDivisors R) K) (hA : A ≠ 0) (Qs : Finset ι)
    (Q : ι → Ideal R) (hQ : ∀ i ∈ Qs, (Q i).IsPrime) (hQ0 : ∀ i ∈ Qs, Q i ≠ ⊥) :
    ∃ γ : K, γ ≠ 0 ∧ ∃ s : R, (∀ i ∈ Qs, s ∉ Q i) ∧
      (∀ c ∈ A, ∃ r : R, algebraMap R K r = algebraMap R K s * γ⁻¹ * c) ∧
      algebraMap R K s * γ ∈ A := by
  obtain ⟨a, I, ha, hAI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul A
  have hI : I ≠ ⊥ := by
    rintro rfl
    apply hA
    rw [hAI, FractionalIdeal.coeIdeal_bot, mul_zero]
  have hinj := IsFractionRing.injective R K
  obtain ⟨g, hgI, hg0, hgQ⟩ : ∃ g ∈ I, g ≠ 0 ∧ ∀ i ∈ Qs, ¬ Ideal.span {g} ≤ I * Q i := by
    rcases Qs.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
    · obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      exact ⟨g, hg, hg0, by simp⟩
    · have hQp0 : (∏ i ∈ Qs, Q i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i hi => hQ0 i hi
      obtain ⟨g, hg⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.mul_le_left : I * (∏ i ∈ Qs, Q i) ≤ I)
        (mul_ne_zero hI hQp0)
      have hgI : g ∈ I := by
        rw [← hg]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)
      have key : ∀ i ∈ Qs, ¬ Ideal.span {g} ≤ I * Q i := by
        intro i hi h
        have hle : (∏ j ∈ Qs, Q j) ≤ Q i := Ideal.prod_le_inf.trans (Finset.inf_le hi)
        have h1 : I ≤ I * Q i := by
          calc I = I * (∏ j ∈ Qs, Q j) ⊔ Ideal.span {g} := hg.symm
            _ ≤ I * Q i := sup_le (Ideal.mul_mono_right hle) h
        have h2 : I * Q i = I * ⊤ := by
          rw [Ideal.mul_top]; exact le_antisymm Ideal.mul_le_left h1
        exact (hQ i hi).ne_top (mul_left_cancel₀ hI h2)
      refine ⟨g, hgI, ?_, key⟩
      rintro rfl
      apply key i0 hi0
      rw [Ideal.span_singleton_eq_bot.2 rfl]
      exact bot_le
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hgI)
  have hJQ : ∀ i ∈ Qs, ¬ J ≤ Q i := fun i hi h => hgQ i hi (by rw [hJ]; exact Ideal.mul_mono_right h)
  obtain ⟨s, hsJ, hsQ⟩ : ∃ s ∈ J, ∀ i ∈ Qs, s ∉ Q i := by
    rcases Qs.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
    · exact ⟨0, J.zero_mem, by simp⟩
    · by_contra hcon
      push_neg at hcon
      have hsub : (J : Set R) ⊆ ⋃ i ∈ (Qs : Set ι), (Q i : Set R) := by
        intro x hx
        obtain ⟨i, hi, hxi⟩ := hcon x hx
        exact Set.mem_biUnion hi hxi
      obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime i0 i0 (fun i hi _ _ => hQ i hi)).1 hsub
      exact hJQ i hi hle
  have ha' : algebraMap R K a ≠ 0 := by
    intro h; exact ha (hinj (by rw [h, map_zero]))
  have hg' : algebraMap R K g ≠ 0 := by
    intro h; exact hg0 (hinj (by rw [h, map_zero]))
  refine ⟨(algebraMap R K a)⁻¹ * algebraMap R K g, mul_ne_zero (inv_ne_zero ha') hg', s, hsQ, ?_, ?_⟩
  · intro c hc
    rw [hAI, FractionalIdeal.mem_singleton_mul] at hc
    obtain ⟨y, hy, rfl⟩ := hc
    obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    have hxs : x * s ∈ Ideal.span {g} := by
      rw [hJ]; exact Ideal.mul_mem_mul hx hsJ
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hxs
    refine ⟨r, ?_⟩
    have hr' : algebraMap R K r * algebraMap R K g = algebraMap R K x * algebraMap R K s := by
      rw [← map_mul, ← map_mul, hr]
    field_simp
    linear_combination hr'
  · rw [hAI, FractionalIdeal.mem_singleton_mul]
    refine ⟨algebraMap R K (s * g), FractionalIdeal.mem_coeIdeal_of_mem _ (I.mul_mem_left s hgI), ?_⟩
    rw [map_mul]
    field_simp

/- English proof (translation)
Introduce `D n Λ ΛT h P`. Take `⟨γ, hγ, s, hsQ, hint, hmem⟩` from `exists_gen_avoid D.host.AA (GlobalTheory.FinPl.LocGen.AA_ne_zero D) P (fun PP => conjI PP.asIdeal) (fun PP _ => by rw [GlobalTheory.LiftIdeal.conjI_eq_map]; exact (GlobalTheory.LiftIdeal.isMaximal_map D PP).isPrime) (fun PP _ => by`. Rewrite using `[GlobalTheory.LiftIdeal.conjI_eq_map, Ne, Ideal.map_eq_bot_iff_of_injective (f := ((GlobalTheory.LiftIdeal.conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E))) (GlobalTheory.LiftIdeal.conjO D).injective]`. Conclude with `PP.ne_bot)`. Use `⟨γ, hγ, s, hsQ, ?_, ?_⟩` and prove the remaining obligations.

Introduce `v hv`. Establish `hv'` using `(h v).1 hv`. Proceed by induction on `hv' using AddSubgroup.closure_induction with`. Consider the case `mem u hu`. Take `⟨c, hc, t, ht, rfl⟩` from `hu`.

Take `⟨r, hr⟩` from `hint c hc`. Rewrite using `[smul_smul]`. Establish `: ((s : D.host.E) * γ⁻¹ * c) = algebraMap (𝓞 D.host.E) D.host.E r`. Rewrite using `[hr]`. Rewrite using `[this, algebraMap_smul]`.

Conclude with `ΛT.smul_mem r ht`. Consider the case `zero => rw [smul_zero]`. Conclude with `ΛT.zero_mem`. Consider the case `add x y _ _ hx hy`. Rewrite using `[smul_add]`.

Conclude with `ΛT.add_mem (hx ((h x).2 ‹_›)) (hy ((h y).2 ‹_›))`. Consider the case `neg x _ hx`. Rewrite using `[smul_neg]`. Conclude with `ΛT.neg_mem (hx ((h x).2 ‹_›))`. Introduce `v hv`.

Rewrite using `[h]`. Conclude with `AddSubgroup.subset_closure ⟨(s : D.host.E) * γ, hmem, v, hv, rfl⟩`.
-/
theorem exists_global_scalar_prime_to_conj_polarisationLattice : ∀ (D : D7) (n : ℕ) (Λ ΛT : Lt D.host.E n), IsAA Λ ΛT → ∀ P : Finset (Formalism.L2.DIV.Pl D.host.E), ∃ γ : D.host.E, γ ≠ 0 ∧ ∃ s : 𝓞 D.host.E, (∀ PP ∈ P, s ∉ conjI PP.asIdeal) ∧ (∀ v ∈ Λ, ((s : D.host.E) * γ⁻¹) • v ∈ ΛT) ∧ (∀ v ∈ ΛT, ((s : D.host.E) * γ) • v ∈ Λ) := by
  intro D n Λ ΛT h P
  obtain ⟨γ, hγ, s, hsQ, hint, hmem⟩ := exists_gen_avoid D.host.AA (GlobalTheory.FinPl.LocGen.AA_ne_zero D) P
    (fun PP => conjI PP.asIdeal)
    (fun PP _ => by rw [GlobalTheory.LiftIdeal.conjI_eq_map]; exact (GlobalTheory.LiftIdeal.isMaximal_map D PP).isPrime)
    (fun PP _ => by
      rw [GlobalTheory.LiftIdeal.conjI_eq_map, Ne, Ideal.map_eq_bot_iff_of_injective (f := ((GlobalTheory.LiftIdeal.conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E))) (GlobalTheory.LiftIdeal.conjO D).injective]
      exact PP.ne_bot)
  refine ⟨γ, hγ, s, hsQ, ?_, ?_⟩
  · intro v hv
    have hv' := (h v).1 hv
    induction hv' using AddSubgroup.closure_induction with
    | mem u hu =>
      obtain ⟨c, hc, t, ht, rfl⟩ := hu
      obtain ⟨r, hr⟩ := hint c hc
      rw [smul_smul]
      have : ((s : D.host.E) * γ⁻¹ * c) = algebraMap (𝓞 D.host.E) D.host.E r := by
        rw [hr]
      rw [this, algebraMap_smul]
      exact ΛT.smul_mem r ht
    | zero => rw [smul_zero]; exact ΛT.zero_mem
    | add x y _ _ hx hy =>
      rw [smul_add]; exact ΛT.add_mem (hx ((h x).2 ‹_›)) (hy ((h y).2 ‹_›))
    | neg x _ hx =>
      rw [smul_neg]; exact ΛT.neg_mem (hx ((h x).2 ‹_›))
  · intro v hv
    rw [h]
    exact AddSubgroup.subset_closure ⟨(s : D.host.E) * γ, hmem, v, hv, rfl⟩

end GlobalTheory.GenChoice
