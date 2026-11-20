import Formalism.CharacterColumnKernels.Statement

namespace Formalism.NG

/- English proof (translation)
Introduce `O B Ω _ _ _ _ _ _ _ _ _ _ hinj b hb`. Assume the negation of the conclusion as `hb0`. Establish `hnil : b ∉ sInf (minimalPrimes B)`. Rewrite using `[minimalPrimes, Ideal.sInf_minimalPrimes]`. Introduce `h`.

Establish `h' : b ∈ nilradical B` using `h`. Rewrite `h'` using `[nilradical_eq_zero]`. Conclude with `hb0 h'`. Choose the witnesses or unpack the hypotheses as in `⟨P, hP, hbP⟩ : ∃ P ∈ minimalPrimes B, b ∉ P := by`. Rewrite `hnil` using `[Ideal.mem_sInf]`.

Use `push Not at hnil`. Conclude with `hnil`. Establish `hPprime : P.IsPrime` using `hP.1.1`. Establish `hcomap : P.comap (algebraMap O B) = ⊥`. Rewrite using `[eq_bot_iff]`.

Introduce `a ha`. Rewrite using `[Ideal.mem_bot]`. Assume the negation of the conclusion as `ha0`. Establish `hnzd : algebraMap O B a ∈ nonZeroDivisors B`. Rewrite using `[mem_nonZeroDivisors_iff_right]`.

Introduce `x hx`. Establish `hs : a • x = 0` using `by rw [Algebra.smul_def, mul_comm, hx]`. Conclude with `(smul_eq_zero.mp hs).resolve_left ha0`. Conclude with `Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hP) ha hnzd`. Establish `: IsDomain (B ⧸ P)` using `Ideal.Quotient.isDomain P`.

Establish `hinjS : Function.Injective (algebraMap O (B ⧸ P))`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Establish `ha' : algebraMap O B a ∈ P`. Rewrite `ha` using `[IsScalarTower.algebraMap_apply O B (B ⧸ P), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `ha`. Establish `: a ∈ P.comap (algebraMap O B)` using `ha'`. Rewrite `this` using `[hcomap]`. Conclude with `(Ideal.mem_bot).mp this`. Establish `: Module.IsTorsionFree O (B ⧸ P)` using `Module.isTorsionFree_iff_algebraMap_injective.mpr hinjS`.

Establish `: Module.IsTorsionFree O Ω` using `Module.isTorsionFree_iff_algebraMap_injective.mpr hinj`. Establish `: Algebra.IsIntegral O (B ⧸ P)` using `Algebra.IsIntegral.of_finite O (B ⧸ P)`. Set `L : (B ⧸ P) →ₐ[O] Ω` to `IsAlgClosed.lift`. Establish `hker : RingHom.ker (L : (B ⧸ P) →+* Ω) = ⊥`. Apply `Ideal.eq_bot_of_comap_eq_bot (R := O)` to reduce the goal to its premises.

Rewrite using `[eq_bot_iff]`. Introduce `a ha`. Rewrite `ha` using `[Ideal.mem_comap, RingHom.mem_ker]`. Establish `: algebraMap O Ω a = 0`. Rewrite using `[← L.commutes a]`.

Conclude with `ha`. Rewrite using `[Ideal.mem_bot]`. Conclude with `hinj (by rw [this, map_zero])`. Establish `hφ` using `hb (L.comp (Ideal.Quotient.mkₐ O P))`. Establish `hmem : Ideal.Quotient.mk P b ∈ RingHom.ker (L : (B ⧸ P) →+* Ω)`.

Rewrite using `[RingHom.mem_ker]`. Conclude with `hφ`. Rewrite `hmem` using `[hker, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hbP hmem`.
-/
theorem points : StatPoints := by
  intro O B Ω _ _ _ _ _ _ _ _ _ _ hinj b hb
  by_contra hb0
  have hnil : b ∉ sInf (minimalPrimes B) := by
    rw [minimalPrimes, Ideal.sInf_minimalPrimes]
    intro h
    have h' : b ∈ nilradical B := h
    rw [nilradical_eq_zero] at h'
    exact hb0 h'
  obtain ⟨P, hP, hbP⟩ : ∃ P ∈ minimalPrimes B, b ∉ P := by
    rw [Ideal.mem_sInf] at hnil
    push Not at hnil
    exact hnil
  have hPprime : P.IsPrime := hP.1.1
  have hcomap : P.comap (algebraMap O B) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_bot]
    by_contra ha0
    have hnzd : algebraMap O B a ∈ nonZeroDivisors B := by
      rw [mem_nonZeroDivisors_iff_right]
      intro x hx
      have hs : a • x = 0 := by rw [Algebra.smul_def, mul_comm, hx]
      exact (smul_eq_zero.mp hs).resolve_left ha0
    exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hP) ha hnzd
  have : IsDomain (B ⧸ P) := Ideal.Quotient.isDomain P
  have hinjS : Function.Injective (algebraMap O (B ⧸ P)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have ha' : algebraMap O B a ∈ P := by
      rw [IsScalarTower.algebraMap_apply O B (B ⧸ P), Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem] at ha
      exact ha
    have : a ∈ P.comap (algebraMap O B) := ha'
    rw [hcomap] at this
    exact (Ideal.mem_bot).mp this
  have : Module.IsTorsionFree O (B ⧸ P) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinjS
  have : Module.IsTorsionFree O Ω := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have : Algebra.IsIntegral O (B ⧸ P) := Algebra.IsIntegral.of_finite O (B ⧸ P)
  let L : (B ⧸ P) →ₐ[O] Ω := IsAlgClosed.lift
  have hker : RingHom.ker (L : (B ⧸ P) →+* Ω) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := O)
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    have : algebraMap O Ω a = 0 := by
      rw [← L.commutes a]; exact ha
    rw [Ideal.mem_bot]
    exact hinj (by rw [this, map_zero])
  have hφ := hb (L.comp (Ideal.Quotient.mkₐ O P))
  have hmem : Ideal.Quotient.mk P b ∈ RingHom.ker (L : (B ⧸ P) →+* Ω) := by
    rw [RingHom.mem_ker]
    exact hφ
  rw [hker, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
  exact hbP hmem

end Formalism.NG
