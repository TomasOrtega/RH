import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ I hfg hne ι _ Q hQ`. Set `F : FractionalIdeal (nonZeroDivisors (𝓞 E)) E` to `⟨I, FractionalIdeal.isFractional_of_fg hfg⟩`. Establish `hFcoe : (F : Submodule (𝓞 E) E) = I` using `rfl`. Establish `hF0 : F ≠ 0`. Introduce `h`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[← hFcoe, h, FractionalIdeal.coe_zero]`. Establish `hinj : Function.Injective (algebraMap (𝓞 E) E)` using `FaithfulSMul.algebraMap_injective _ _`. Establish `hint : ∀ s ∈ F⁻¹, ∀ a ∈ I, ∃ o : 𝓞 E, (o : E) = s * a`. Introduce `s hs a ha`.

Establish `h1` using `(FractionalIdeal.mem_inv_iff hF0).1 hs a ha`. Rewrite `h1` using `[← FractionalIdeal.mem_coe, FractionalIdeal.coe_one]`. Take `⟨o, ho⟩` from `Submodule.mem_one.1 h1`. Conclude with `⟨o, ho⟩`. Establish `key : ∀ P : Ideal (𝓞 E), P ≠ ⊤ → ∃ s ∈ F⁻¹, ∃ a ∈ I, ∃ o : 𝓞 E, (o : E) = s * a ∧ o ∉ P`.

Introduce `P hP`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hP` to reduce the goal to its premises. Establish `hle : ((F * F⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) ≤ Submodule.map (Algebra.linearMap (𝓞 E) E) P`.

Rewrite using `[FractionalIdeal.coe_mul, Submodule.mul_le]`. Introduce `m hm n hn`. Take `⟨o, ho⟩` from `hint n hn m hm`. Use `Submodule.mem_map.2 ⟨o, h n hn m hm o ho, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm, ← ho]`.

Both sides reduce to the same expression. Rewrite `hle` using `[mul_inv_cancel₀ hF0, FractionalIdeal.coe_one]`. Establish `h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E)` using `Submodule.mem_one.2 ⟨1, map_one _⟩`. Take `⟨p, hp, hp1⟩` from `Submodule.mem_map.1 (hle h1)`. Establish `: p = 1` using `hinj (by rw [map_one]; exact hp1)`.

Conclude with `(Ideal.eq_top_iff_one P).2 (this ▸ hp)`. Use `choose! sf hsf af haf of hof hof' using key`. Establish `hc : ∀ P' P : Ideal (𝓞 E), P'.IsMaximal → P.IsMaximal → P' ≠ P → ∃ c ∈ P', c ∉ P`. Introduce `P' P hP' hP hne'`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hne' (hP'.eq_of_le hP.ne_top h)`. Use `choose! c hc1 hc2 using hc`. Take `⟨M0, hM0⟩` from `Ideal.exists_maximal (𝓞 E)`. Set `T : Finset (Ideal (𝓞 E))` to `insert M0 (Finset.univ.image Q)`.

Establish `hT : ∀ P ∈ T, P.IsMaximal`. Introduce `P hP`. Break down `Finset.mem_insert.1 hP with h | h` into its components or cases. Conclude with `h ▸ hM0`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 h`.

Conclude with `hQ i`. Set `u : Ideal (𝓞 E) → 𝓞 E` to `fun P => ∏ P' ∈ T.erase P, c P' P`. Establish `hu1 : ∀ P ∈ T, u P ∉ P`. Introduce `P hP hmem`. Use `haveI := (hT P hP).isPrime`.

Take `⟨P', hP', hcP⟩` from `Ideal.IsPrime.prod_mem_iff.1 hmem`. Conclude with `hc2 P' P (hT P' (Finset.mem_of_mem_erase hP')) (hT P hP) (Finset.ne_of_mem_erase hP') hcP`. Establish `hu2 : ∀ P ∈ T, ∀ P' ∈ T, P' ≠ P → u P ∈ P'`. Introduce `P hP P' hP' hne'`. Establish `hm : P' ∈ T.erase P` using `Finset.mem_erase.2 ⟨hne', hP'⟩`.

Use `show ∏ P'' ∈ T.erase P, c P'' P ∈ P'`. Rewrite using `[← Finset.mul_prod_erase _ _ hm]`. Conclude with `Ideal.mul_mem_right _ _ (hc1 P' P (hT P' hP') (hT P hP) hne')`. Set `s : E` to `∑ P ∈ T, (u P : E) * sf P`. Establish `hs : s ∈ F⁻¹`.

Use `Submodule.sum_mem _ (fun P hP => ?_)` and prove the remaining obligations. Use `Submodule.smul_mem ((F⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) (u P) (hsf P (hT P hP).ne_top)` as an intermediate fact. Rewrite `this` using `[Algebra.smul_def]`. Then use the resulting hypothesis. Establish `main : ∀ P0 ∈ T, ∃ o : 𝓞 E, (o : E) = s * af P0 ∧ o ∉ P0`. Introduce `P0 hP0`.

Establish `hP0t` using `(hT P0 hP0).ne_top`. Establish `hterm : ∀ P ∈ T, ∃ o : 𝓞 E, (o : E) = sf P * af P0` using `fun P hP => hint _ (hsf P (hT P hP).ne_top) _ (haf P0 hP0t)`. Use `choose! w hw using hterm`. Use `⟨∑ P ∈ T, u P * w P, ?_, ?_⟩` and prove the remaining obligations. Use `push_cast`.

Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl (fun P hP => ?_)` and prove the remaining obligations. Rewrite using `[mul_assoc, ← hw P hP]`. Introduce `hmem haveI := (hT P0 hP0).isPrime`. Rewrite `hmem` using `[← Finset.add_sum_erase _ _ hP0]`.

Establish `hrest : ∑ P ∈ T.erase P0, u P * w P ∈ P0` using `Ideal.sum_mem _ (fun P hP => Ideal.mul_mem_right _ _ (hu2 P (Finset.mem_of_mem_erase hP) P0 hP0 (Finset.ne_of_mem_erase hP).symm))`. Establish `h2 : u P0 * w P0 ∈ P0`. Use `P0.sub_mem hmem hrest` as an intermediate fact. Simplify using `using this`. Establish `hwo : w P0 = of P0` using `hinj (by show (w P0 : E) = (of P0 : E)`.

Rewrite using `[hw P0 hP0, hof P0 hP0t])`. Break down `Ideal.IsPrime.mem_or_mem ‹_› h2 with h3 | h3` into its components or cases. Conclude with `hu1 P0 hP0 h3`. Conclude with `hof' P0 hP0t (hwo ▸ h3)`. Use `⟨s, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `hs0`. Take `⟨o, ho, hno⟩` from `main M0 (Finset.mem_insert_self _ _)`. Rewrite `ho` using `[hs0, zero_mul]`. Establish `: o = 0` using `hinj (by rw [map_zero]; exact ho)`. Conclude with `hno (this ▸ M0.zero_mem)`.

Introduce `a ha`. Take `⟨o, ho⟩` from `hint s hs a ha`. Rewrite using `[← ho]`. Conclude with `o.isIntegral_coe`. Introduce `i`.

Establish `hi : Q i ∈ T` using `Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))`. Take `⟨o, ho, hno⟩` from `main (Q i) hi`. Conclude with `⟨af (Q i), haf _ (hQ i).ne_top, o, ho, hno⟩`.
-/
theorem exists_scale_integral_not_le_maximal :
  ∀ (E : Type) [Field E] [NumberField E] (I : Submodule (𝓞 E) E), I.FG → I ≠ ⊥ →
    ∀ (ι : Type) [Fintype ι] (Q : ι → Ideal (𝓞 E)), (∀ i, (Q i).IsMaximal) →
    ∃ s : E, s ≠ 0 ∧ (∀ a ∈ I, IsIntegral ℤ (s * a)) ∧ ∀ i, ∃ a ∈ I, ∃ o : 𝓞 E, (o : E) = s * a ∧ o ∉ Q i := by
  intro E _ _ I hfg hne ι _ Q hQ
  classical
  let F : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨I, FractionalIdeal.isFractional_of_fg hfg⟩
  have hFcoe : (F : Submodule (𝓞 E) E) = I := rfl
  have hF0 : F ≠ 0 := by
    intro h
    apply hne
    rw [← hFcoe, h, FractionalIdeal.coe_zero]
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := FaithfulSMul.algebraMap_injective _ _
  have hint : ∀ s ∈ F⁻¹, ∀ a ∈ I, ∃ o : 𝓞 E, (o : E) = s * a := by
    intro s hs a ha
    have h1 := (FractionalIdeal.mem_inv_iff hF0).1 hs a ha
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one] at h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 h1
    exact ⟨o, ho⟩
  have key : ∀ P : Ideal (𝓞 E), P ≠ ⊤ →
      ∃ s ∈ F⁻¹, ∃ a ∈ I, ∃ o : 𝓞 E, (o : E) = s * a ∧ o ∉ P := by
    intro P hP
    by_contra h
    push_neg at h
    apply hP
    have hle : ((F * F⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) ≤
        Submodule.map (Algebra.linearMap (𝓞 E) E) P := by
      rw [FractionalIdeal.coe_mul, Submodule.mul_le]
      intro m hm n hn
      obtain ⟨o, ho⟩ := hint n hn m hm
      refine Submodule.mem_map.2 ⟨o, h n hn m hm o ho, ?_⟩
      rw [mul_comm, ← ho]; rfl
    rw [mul_inv_cancel₀ hF0, FractionalIdeal.coe_one] at hle
    have h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.2 ⟨1, map_one _⟩
    obtain ⟨p, hp, hp1⟩ := Submodule.mem_map.1 (hle h1)
    have : p = 1 := hinj (by rw [map_one]; exact hp1)
    exact (Ideal.eq_top_iff_one P).2 (this ▸ hp)
  choose! sf hsf af haf of hof hof' using key
  have hc : ∀ P' P : Ideal (𝓞 E), P'.IsMaximal → P.IsMaximal → P' ≠ P → ∃ c ∈ P', c ∉ P := by
    intro P' P hP' hP hne'
    by_contra h
    push_neg at h
    exact hne' (hP'.eq_of_le hP.ne_top h)
  choose! c hc1 hc2 using hc
  obtain ⟨M0, hM0⟩ := Ideal.exists_maximal (𝓞 E)
  let T : Finset (Ideal (𝓞 E)) := insert M0 (Finset.univ.image Q)
  have hT : ∀ P ∈ T, P.IsMaximal := by
    intro P hP
    rcases Finset.mem_insert.1 hP with h | h
    · exact h ▸ hM0
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      exact hQ i
  let u : Ideal (𝓞 E) → 𝓞 E := fun P => ∏ P' ∈ T.erase P, c P' P
  have hu1 : ∀ P ∈ T, u P ∉ P := by
    intro P hP hmem
    haveI := (hT P hP).isPrime
    obtain ⟨P', hP', hcP⟩ := Ideal.IsPrime.prod_mem_iff.1 hmem
    exact hc2 P' P (hT P' (Finset.mem_of_mem_erase hP')) (hT P hP) (Finset.ne_of_mem_erase hP') hcP
  have hu2 : ∀ P ∈ T, ∀ P' ∈ T, P' ≠ P → u P ∈ P' := by
    intro P hP P' hP' hne'
    have hm : P' ∈ T.erase P := Finset.mem_erase.2 ⟨hne', hP'⟩
    show ∏ P'' ∈ T.erase P, c P'' P ∈ P'
    rw [← Finset.mul_prod_erase _ _ hm]
    exact Ideal.mul_mem_right _ _ (hc1 P' P (hT P' hP') (hT P hP) hne')
  let s : E := ∑ P ∈ T, (u P : E) * sf P
  have hs : s ∈ F⁻¹ := by
    refine Submodule.sum_mem _ (fun P hP => ?_)
    have := Submodule.smul_mem ((F⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) (u P) (hsf P (hT P hP).ne_top)
    rwa [Algebra.smul_def] at this

  have main : ∀ P0 ∈ T, ∃ o : 𝓞 E, (o : E) = s * af P0 ∧ o ∉ P0 := by
    intro P0 hP0
    have hP0t := (hT P0 hP0).ne_top
    have hterm : ∀ P ∈ T, ∃ o : 𝓞 E, (o : E) = sf P * af P0 :=
      fun P hP => hint _ (hsf P (hT P hP).ne_top) _ (haf P0 hP0t)
    choose! w hw using hterm
    refine ⟨∑ P ∈ T, u P * w P, ?_, ?_⟩
    · push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun P hP => ?_)
      rw [mul_assoc, ← hw P hP]
    · intro hmem
      haveI := (hT P0 hP0).isPrime
      rw [← Finset.add_sum_erase _ _ hP0] at hmem
      have hrest : ∑ P ∈ T.erase P0, u P * w P ∈ P0 :=
        Ideal.sum_mem _ (fun P hP => Ideal.mul_mem_right _ _
          (hu2 P (Finset.mem_of_mem_erase hP) P0 hP0 (Finset.ne_of_mem_erase hP).symm))
      have h2 : u P0 * w P0 ∈ P0 := by
        have := P0.sub_mem hmem hrest
        simpa using this
      have hwo : w P0 = of P0 := hinj (by
        show (w P0 : E) = (of P0 : E)
        rw [hw P0 hP0, hof P0 hP0t])
      rcases Ideal.IsPrime.mem_or_mem ‹_› h2 with h3 | h3
      · exact hu1 P0 hP0 h3
      · exact hof' P0 hP0t (hwo ▸ h3)
  refine ⟨s, ?_, ?_, ?_⟩
  · intro hs0
    obtain ⟨o, ho, hno⟩ := main M0 (Finset.mem_insert_self _ _)
    rw [hs0, zero_mul] at ho
    have : o = 0 := hinj (by rw [map_zero]; exact ho)
    exact hno (this ▸ M0.zero_mem)
  · intro a ha
    obtain ⟨o, ho⟩ := hint s hs a ha
    rw [← ho]
    exact o.isIntegral_coe
  · intro i
    have hi : Q i ∈ T := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    obtain ⟨o, ho, hno⟩ := main (Q i) hi
    exact ⟨af (Q i), haf _ (hQ i).ne_top, o, ho, hno⟩

end GlobalTheory
