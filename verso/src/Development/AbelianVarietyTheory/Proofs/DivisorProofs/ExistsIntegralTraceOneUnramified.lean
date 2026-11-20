import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutMemAdelicCompletionIntegral

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

noncomputable section

namespace GlobalTheory.LieDisc

/- English proof (translation)
Introduce `E _ _ _ hE`. Establish `: Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)` using `hE`. Set `σ` to `IsCMField.ringOfIntegersComplexConj E`. Set `I : Ideal (𝓞 (maximalRealSubfield E))` to `{ carrier := {a | ∃ t : 𝓞 E, algebraMap _ (𝓞 E) a = t + σ t} add_mem' := by`. Introduce and unpack `a b ⟨s, hs⟩ ⟨t, ht⟩`.

Conclude with `⟨s + t, by rw [map_add, hs, ht, map_add]; ring⟩`. Use the proof step `zero_mem' := ⟨0, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c a ⟨t, ht⟩`. Use `⟨algebraMap _ (𝓞 E) c * t, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_eq_mul, map_mul, ht, map_mul, AlgEquiv.commutes]`. Use `ring }`. Establish `hI : I = ⊤`. Assume the negation of the conclusion as `hI`. Take `⟨m, hm, hIm⟩` from `Ideal.exists_le_maximal _ hI`.

Take `⟨P, hP, hPm⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) m (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) (𝓞 E))]; exact bot_le)`. Establish `htr : ∀ t : 𝓞 E, t + σ t ∈ P`. Introduce `t`. Establish `hco : ((t + σ t : 𝓞 E) : E) = (t : E) + IsCMField.complexConj E t`. Rewrite using `[← IsCMField.coe_ringOfIntegersComplexConj]`.

Both sides reduce to the same expression. Establish `hfix` using `(IsCMField.complexConj_eq_self_iff E ((t : E) + IsCMField.complexConj E t)).1 (by`. Rewrite using `[map_add, IsCMField.complexConj_apply_apply, add_comm])`. Establish `hi : IsIntegral ℤ (⟨_, hfix⟩ : maximalRealSubfield E)`. Establish `h0 : IsIntegral ℤ ((t + σ t : 𝓞 E) : E)` using `(t + σ t).isIntegral_coe`.

Rewrite `h0` using `[hco]`. Conclude with `(isIntegral_algebraMap_iff (algebraMap (maximalRealSubfield E) E).injective).1 h0`. Set `a : 𝓞 (maximalRealSubfield E)` to `⟨_, hi⟩`. Establish `hA : algebraMap _ (𝓞 E) a = t + σ t`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Rewrite using `[hco]`. Both sides reduce to the same expression. Establish `h1 : a ∈ Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) P` using `hPm ▸ hIm ⟨t, hA⟩`. Conclude with `hA ▸ Ideal.mem_comap.1 h1`. Establish `hσ : ∃ s, σ.toAlgHom s ≠ s`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Apply `IsCMField.complexConj_ne_one E` to reduce the goal to its premises. Use extensionality with `x`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 E) x`.

Establish `hc' : ∀ s : 𝓞 E, IsCMField.complexConj E (algebraMap (𝓞 E) E s) = algebraMap (𝓞 E) E s` using `fun s => congrArg (fun z : 𝓞 E => (z : E)) (hc s)`. Simplify using `[hc']`. Take `⟨t, ht⟩` from `GlobalTheory.UCls.Det.exists_sub_notMem σ.toAlgHom hσ P hP.ne_top`. Apply `ht` to reduce the goal to its premises. Establish `h2` using `P.sub_mem (htr t) (P.mul_mem_right (σ t) (htr 1))`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `t - σ t = t + σ t - (1 + σ 1) * σ t`. Rewrite using `[map_one]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨t, ht⟩ : (1 : 𝓞 (maximalRealSubfield E)) ∈ I` from `hI ▸ Submodule.mem_top`.

Use `⟨(t : E), t.isIntegral_coe, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun z : 𝓞 E => (z : E)) ht`. Rewrite `h` using `[map_one]`. Express the relevant statement in the definitionally equal form `(1 : E) = (t : E) + ((σ t : 𝓞 E) : E) at h`. Rewrite `h` using `[IsCMField.coe_ringOfIntegersComplexConj]`.

Rewrite using `[cc]`. Conclude with `h.symm`.
-/
theorem exists_integral_add_cc_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    Unr E → ∃ t : E, IsIntegral ℤ t ∧ t + cc t = 1 := by
  intro E _ _ _ hE
  have : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := hE
  let σ := IsCMField.ringOfIntegersComplexConj E
  let I : Ideal (𝓞 (maximalRealSubfield E)) :=
    { carrier := {a | ∃ t : 𝓞 E, algebraMap _ (𝓞 E) a = t + σ t}
      add_mem' := by
        rintro a b ⟨s, hs⟩ ⟨t, ht⟩
        exact ⟨s + t, by rw [map_add, hs, ht, map_add]; ring⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨t, ht⟩
        refine ⟨algebraMap _ (𝓞 E) c * t, ?_⟩
        rw [smul_eq_mul, map_mul, ht, map_mul, AlgEquiv.commutes]
        ring }
  have hI : I = ⊤ := by
    by_contra hI
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal _ hI
    obtain ⟨P, hP, hPm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) m
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1
        (FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) (𝓞 E))]; exact bot_le)
    have htr : ∀ t : 𝓞 E, t + σ t ∈ P := by
      intro t
      have hco : ((t + σ t : 𝓞 E) : E) = (t : E) + IsCMField.complexConj E t := by
        rw [← IsCMField.coe_ringOfIntegersComplexConj]
        rfl
      have hfix := (IsCMField.complexConj_eq_self_iff E ((t : E) + IsCMField.complexConj E t)).1 (by
        rw [map_add, IsCMField.complexConj_apply_apply, add_comm])
      have hi : IsIntegral ℤ (⟨_, hfix⟩ : maximalRealSubfield E) := by
        have h0 : IsIntegral ℤ ((t + σ t : 𝓞 E) : E) := (t + σ t).isIntegral_coe
        rw [hco] at h0
        exact (isIntegral_algebraMap_iff (algebraMap (maximalRealSubfield E) E).injective).1 h0
      let a : 𝓞 (maximalRealSubfield E) := ⟨_, hi⟩
      have hA : algebraMap _ (𝓞 E) a = t + σ t := by
        apply RingOfIntegers.ext
        rw [hco]
        rfl
      have h1 : a ∈ Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) P := hPm ▸ hIm ⟨t, hA⟩
      exact hA ▸ Ideal.mem_comap.1 h1
    have hσ : ∃ s, σ.toAlgHom s ≠ s := by
      by_contra hc
      push Not at hc
      apply IsCMField.complexConj_ne_one E
      ext x
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
      have hc' : ∀ s : 𝓞 E, IsCMField.complexConj E (algebraMap (𝓞 E) E s) = algebraMap (𝓞 E) E s :=
        fun s => congrArg (fun z : 𝓞 E => (z : E)) (hc s)
      simp [hc']
    obtain ⟨t, ht⟩ := GlobalTheory.UCls.Det.exists_sub_notMem σ.toAlgHom hσ P hP.ne_top
    apply ht
    have h2 := P.sub_mem (htr t) (P.mul_mem_right (σ t) (htr 1))
    convert h2 using 1
    change t - σ t = t + σ t - (1 + σ 1) * σ t
    rw [map_one]
    ring
  obtain ⟨t, ht⟩ : (1 : 𝓞 (maximalRealSubfield E)) ∈ I := hI ▸ Submodule.mem_top
  refine ⟨(t : E), t.isIntegral_coe, ?_⟩
  have h := congrArg (fun z : 𝓞 E => (z : E)) ht
  rw [map_one] at h
  change (1 : E) = (t : E) + ((σ t : 𝓞 E) : E) at h
  rw [IsCMField.coe_ringOfIntegersComplexConj] at h
  rw [cc]
  exact h.symm

end GlobalTheory.LieDisc
