import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SatakeDualWeyl.StatementG
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix

namespace GlobalTheory.SelfDualGenus

open IsDedekindDomain NumberField in
open scoped TensorProduct Matrix in

/- English proof (translation)
Unfold `_root_.Formalism.UG.IsInertAt`. Establish `key : ∀ P' : Ideal (𝓞 E), P'.IsMaximal → Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) P' = v.asIdeal → P' ≤ P.asIdeal`. Introduce `P' hP' hcomap z hz`. Distinguish the cases in `hz0 : z = 0`. Rewrite using `[hz0]`.

Conclude with `P.asIdeal.zero_mem`. Rewrite using `[hP z hz0]`. Introduce `hmem`. Rewrite `hmem` using `[_root_.GlobalTheory.SelfDualGenus.mem_semiLoc_iff]`. Take `⟨t, ht, hint⟩` from `hmem`.

Establish `hzE : (z : E) ≠ 0` using `by exact_mod_cast hz0`. Set `w : 𝓞 E` to `⟨_, hint⟩`. Establish `hzw : z * w = algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) t`. Apply `NumberField.RingOfIntegers.ext` to reduce the goal to its premises. Use `show (z : E) * (((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) t : 𝓞 E) : E) * (z : E)⁻¹) = _`.

Clear the denominators using the available nonvanishing facts. Apply `ht` to reduce the goal to its premises. Rewrite using `[← hcomap, Ideal.mem_comap, ← hzw]`. Conclude with `P'.mul_mem_right _ hz`. Establish `hker : RingHom.ker (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ v.asIdeal`.

Introduce `a ha`. Rewrite `ha` using `[RingHom.mem_ker]`. Establish `ha0 : a = 0` using `FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) (𝓞 E) (by rw [ha, map_zero])`. Rewrite using `[ha0]`. Conclude with `v.asIdeal.zero_mem`.

Take `⟨P0, hP0, hP0c⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal hker`. Establish `hP0P : P0 = P.asIdeal` using `hP0.eq_of_le P.isPrime.ne_top (key P0 hP0 hP0c)`. Establish `hcP : Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) P.asIdeal = v.asIdeal`. Rewrite using `[← hP0P, hP0c]`. Establish `hQP : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal ≤ P.asIdeal`.

Rewrite using `[Ideal.map_le_iff_le_comap, hcP]`. Take `⟨x, y, hyx, hyP, hyP2⟩` from `hx`. Establish `hyx' : y = algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) x`. Apply `NumberField.RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[hyx]`.

Both sides reduce to the same expression. Establish `hxv : x ∈ v.asIdeal`. Rewrite using `[← hcP, Ideal.mem_comap, ← hyx']`. Conclude with `hyP`. Establish `hyQ : y ∈ Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal`.

Rewrite using `[hyx']`. Conclude with `Ideal.mem_map_of_mem _ hxv`. Take `⟨J, hJ⟩` from `Ideal.dvd_iff_le.2 hQP`. Distinguish the cases in `hJtop : J = ⊤`. Rewrite using `[hJ, hJtop, Ideal.mul_top]`.

It suffices to derive a contradiction. Take `⟨P'', hP'', hJP''⟩` from `Ideal.exists_le_maximal J hJtop`. Establish `hQP'' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal ≤ P''`. Rewrite using `[hJ]`. Conclude with `Ideal.mul_le_right.trans hJP''`.

Establish `hcP'' : Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) P'' = v.asIdeal`. Use `(v.isMaximal.eq_of_le (Ideal.comap_ne_top _ hP''.ne_top) ?_).symm` and prove the remaining obligations. Rewrite using `[← Ideal.map_le_iff_le_comap]`. Conclude with `hQP''`. Establish `hJP : J ≤ P.asIdeal` using `hJP''.trans (key P'' hP'' hcP'')`.

Apply `hyP2` to reduce the goal to its premises. Rewrite using `[pow_two]`. Use `hJ ▸ hyQ` as an intermediate fact. Conclude with `Ideal.mul_mono_right hJP this`.
-/
theorem _root_.GlobalTheory.SelfDualGenus.isInertAt_of_unique_unramified (E : Type) [Field E] [NumberField E] [IsCMField E]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E))
    (hP : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ (x : E)⁻¹ ∉ _root_.GlobalTheory.SelfDualGenus.semiLoc v))
    (hx : ∃ x : 𝓞 (maximalRealSubfield E), ∃ y : 𝓞 E,
      (y : E) = algebraMap (maximalRealSubfield E) E (x : maximalRealSubfield E) ∧
        y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2) :
    _root_.Formalism.UG.IsInertAt (maximalRealSubfield E) E v P := by
  unfold _root_.Formalism.UG.IsInertAt
  have key : ∀ P' : Ideal (𝓞 E), P'.IsMaximal →
      Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) P' = v.asIdeal → P' ≤ P.asIdeal := by
    intro P' hP' hcomap z hz
    by_cases hz0 : z = 0
    · rw [hz0]; exact P.asIdeal.zero_mem
    rw [hP z hz0]
    intro hmem
    rw [_root_.GlobalTheory.SelfDualGenus.mem_semiLoc_iff] at hmem
    obtain ⟨t, ht, hint⟩ := hmem
    have hzE : (z : E) ≠ 0 := by exact_mod_cast hz0
    let w : 𝓞 E := ⟨_, hint⟩
    have hzw : z * w = algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) t := by
      apply NumberField.RingOfIntegers.ext
      show (z : E) * (((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) t : 𝓞 E) : E) * (z : E)⁻¹) = _
      field_simp
    apply ht
    rw [← hcomap, Ideal.mem_comap, ← hzw]
    exact P'.mul_mem_right _ hz
  have hker : RingHom.ker (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ v.asIdeal := by
    intro a ha
    rw [RingHom.mem_ker] at ha
    have ha0 : a = 0 := FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) (𝓞 E)
      (by rw [ha, map_zero])
    rw [ha0]; exact v.asIdeal.zero_mem
  obtain ⟨P0, hP0, hP0c⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal hker
  have hP0P : P0 = P.asIdeal := hP0.eq_of_le P.isPrime.ne_top (key P0 hP0 hP0c)
  have hcP : Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) P.asIdeal = v.asIdeal := by
    rw [← hP0P, hP0c]
  have hQP : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal ≤ P.asIdeal := by
    rw [Ideal.map_le_iff_le_comap, hcP]
  obtain ⟨x, y, hyx, hyP, hyP2⟩ := hx
  have hyx' : y = algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) x := by
    apply NumberField.RingOfIntegers.ext
    rw [hyx]
    rfl
  have hxv : x ∈ v.asIdeal := by
    rw [← hcP, Ideal.mem_comap, ← hyx']; exact hyP
  have hyQ : y ∈ Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal := by
    rw [hyx']; exact Ideal.mem_map_of_mem _ hxv
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hQP
  by_cases hJtop : J = ⊤
  · rw [hJ, hJtop, Ideal.mul_top]
  exfalso
  obtain ⟨P'', hP'', hJP''⟩ := Ideal.exists_le_maximal J hJtop
  have hQP'' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal ≤ P'' := by
    rw [hJ]; exact Ideal.mul_le_right.trans hJP''
  have hcP'' : Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) P'' = v.asIdeal := by
    refine (v.isMaximal.eq_of_le (Ideal.comap_ne_top _ hP''.ne_top) ?_).symm
    rw [← Ideal.map_le_iff_le_comap]; exact hQP''
  have hJP : J ≤ P.asIdeal := hJP''.trans (key P'' hP'' hcP'')
  apply hyP2
  rw [pow_two]
  have := hJ ▸ hyQ
  exact Ideal.mul_mono_right hJP this

end GlobalTheory.SelfDualGenus
