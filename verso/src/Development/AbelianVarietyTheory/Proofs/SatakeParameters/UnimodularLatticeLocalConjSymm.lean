import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO

noncomputable section

namespace GlobalTheory.GO.UniExt

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

/- English proof (translation)
Unfold `localization₂ locS`. Conclude with `Iff.rfl`.
-/
private theorem mem_localization_iff_exists_smul_mem {N : Submodule (𝓞 E) (Sp E n)} (Q : HeightOneSpectrum (𝓞 E))
    (x : Sp E n) : x ∈ localization₂ Q.asIdeal N ↔ ∃ s ∉ Q.asIdeal, s • x ∈ N := by
  unfold localization₂ locS
  exact Iff.rfl

/- English proof (translation)
Unfold `IsUnimodular dual at hu`. Use `conv_lhs => rw [← hu]`. Simplify using `only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]`.
-/
private theorem mem_iff_hStd_integral_of_isUnimodular {N : Submodule (𝓞 E) (Sp E n)}
    (hu : IsUnimodular (hStd E n) N) (x : Sp E n) :
    x ∈ N ↔ ∀ y ∈ N, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = hStd E n y x := by
  unfold IsUnimodular dual at hu
  conv_lhs => rw [← hu]
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]

/- English proof (translation)
Rewrite using `[← algebraMap_smul E a y, LinearMap.map_smulₛₗ₂, smul_eq_mul]`. Both sides reduce to the same expression.
-/
private theorem hStd_smul_left (a : 𝓞 E) (y z : Sp E n) :
    hStd E n (a • y) z = algebraMap (𝓞 E) E (cO E a) * hStd E n y z := by
  rw [← algebraMap_smul E a y, LinearMap.map_smulₛₗ₂, smul_eq_mul]
  rfl

/- English proof (translation)
Rewrite using `[← algebraMap_smul E a z, map_smul, smul_eq_mul]`.
-/
private theorem hStd_smul_right (a : 𝓞 E) (y z : Sp E n) :
    hStd E n y (a • z) = algebraMap (𝓞 E) E a * hStd E n y z := by
  rw [← algebraMap_smul E a z, map_smul, smul_eq_mul]

/- English proof (translation)
Unfold `conjPrime₂`. Use `show cO E t ∈ Ideal.comap (cO E) P.asIdeal ↔ _`. Rewrite using `[Ideal.mem_comap]`. Establish `htt : cO E (cO E t) = t` using `RingOfIntegers.ext (star_star (t : E))`. Rewrite using `[htt]`.
-/
private theorem cO_mem_conjP_iff (P : HeightOneSpectrum (𝓞 E)) (t : 𝓞 E) :
    cO E t ∈ (conjPrime₂ P).asIdeal ↔ t ∈ P.asIdeal := by
  unfold conjPrime₂
  show cO E t ∈ Ideal.comap (cO E) P.asIdeal ↔ _
  rw [Ideal.mem_comap]
  have htt : cO E (cO E t) = t := RingOfIntegers.ext (star_star (t : E))
  rw [htt]

/- English proof (translation)
Rewrite using `[mem_localization_iff_exists_smul_mem]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, hsx⟩ y hy`. Take `⟨t, ht, hty⟩` from `(mem_localization_iff_exists_smul_mem P y).1 hy`. Take `⟨r, hr⟩` from `(mem_iff_hStd_integral_of_isUnimodular hu (s • x)).1 hsx (t • y) hty`.

Unfold `IntAt`. Use `⟨r, cO E t * s, ?_, ?_⟩` and prove the remaining obligations. Introduce `hmem`. Break down `(conjPrime₂ P).isPrime.mem_or_mem hmem with h | h` into its components or cases. Conclude with `ht ((cO_mem_conjP_iff P t).1 h)`.

Conclude with `hs h`. Rewrite using `[hr, hStd_smul_left, hStd_smul_right, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Introduce `H classical`. Take `⟨S, hS⟩` from `hl`.

Establish `hloc : ∀ y ∈ S, ∃ s : 𝓞 E, s ∉ (conjPrime₂ P).asIdeal ∧ ∃ r : 𝓞 E, algebraMap (𝓞 E) E s * hStd E n y x = algebraMap (𝓞 E) E r`. Introduce `y hy`. Establish `hyN : y ∈ N` using `hS ▸ Submodule.subset_span hy`. Establish `hyl : y ∈ localization₂ P.asIdeal N` using `(mem_localization_iff_exists_smul_mem P y).2 ⟨1, (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, by rwa [one_smul]⟩`. Establish `hint` using `H y hyl`.

Unfold `IntAt at hint`. Take `⟨r, s, hs, h⟩` from `hint`. Conclude with `⟨s, hs, r, h⟩`. Use `choose! u hu0 w hw using hloc`. Use `⟨∏ y ∈ S, u y, ?_, ?_⟩` and prove the remaining obligations.

Introduce `hmem`. Take `⟨y, hy, hyu⟩` from `(Ideal.IsPrime.prod_mem_iff (hp := (conjPrime₂ P).isPrime)).1 hmem`. Conclude with `hu0 y hy hyu`. Rewrite using `[mem_iff_hStd_integral_of_isUnimodular hu]`. Introduce `y hy`.

Rewrite `hy` using `[← hS]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Use `⟨(∏ y ∈ S.erase z, u y) * w z, ?_⟩` and prove the remaining obligations. Rewrite using `[hStd_smul_right, ← Finset.mul_prod_erase S u hz, map_mul, map_mul, ← hw z hz]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨ra, hra⟩` from `ha`. Take `⟨rb, hrb⟩` from `hb`.

Conclude with `⟨ra + rb, by rw [map_add, hra, hrb, map_add, LinearMap.add_apply]⟩`. Consider the case `smul a z _ hz`. Take `⟨rz, hrz⟩` from `hz`. Conclude with `⟨cO E a * rz, by rw [hStd_smul_left, map_mul, hrz]⟩`.
-/
theorem mem_localization_conj_iff {N : Submodule (𝓞 E) (Sp E n)} (hl : N.FG) (hu : IsUnimodular (hStd E n) N)
    (P : HeightOneSpectrum (𝓞 E)) (x : Sp E n) :
    x ∈ localization₂ (conjPrime₂ P).asIdeal N ↔ ∀ y ∈ localization₂ P.asIdeal N, IntAt (conjPrime₂ P) (hStd E n y x) := by
  rw [mem_localization_iff_exists_smul_mem]
  constructor
  · rintro ⟨s, hs, hsx⟩ y hy
    obtain ⟨t, ht, hty⟩ := (mem_localization_iff_exists_smul_mem P y).1 hy
    obtain ⟨r, hr⟩ := (mem_iff_hStd_integral_of_isUnimodular hu (s • x)).1 hsx (t • y) hty
    unfold IntAt
    refine ⟨r, cO E t * s, ?_, ?_⟩
    · intro hmem
      rcases (conjPrime₂ P).isPrime.mem_or_mem hmem with h | h
      · exact ht ((cO_mem_conjP_iff P t).1 h)
      · exact hs h
    · rw [hr, hStd_smul_left, hStd_smul_right, map_mul]
      ring
  · intro H
    classical
    obtain ⟨S, hS⟩ := hl
    have hloc : ∀ y ∈ S, ∃ s : 𝓞 E, s ∉ (conjPrime₂ P).asIdeal ∧
        ∃ r : 𝓞 E, algebraMap (𝓞 E) E s * hStd E n y x = algebraMap (𝓞 E) E r := by
      intro y hy
      have hyN : y ∈ N := hS ▸ Submodule.subset_span hy
      have hyl : y ∈ localization₂ P.asIdeal N :=
        (mem_localization_iff_exists_smul_mem P y).2 ⟨1, (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, by rwa [one_smul]⟩
      have hint := H y hyl
      unfold IntAt at hint
      obtain ⟨r, s, hs, h⟩ := hint
      exact ⟨s, hs, r, h⟩
    choose! u hu0 w hw using hloc
    refine ⟨∏ y ∈ S, u y, ?_, ?_⟩
    · intro hmem
      obtain ⟨y, hy, hyu⟩ := (Ideal.IsPrime.prod_mem_iff (hp := (conjPrime₂ P).isPrime)).1 hmem
      exact hu0 y hy hyu
    · rw [mem_iff_hStd_integral_of_isUnimodular hu]
      intro y hy
      rw [← hS] at hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        refine ⟨(∏ y ∈ S.erase z, u y) * w z, ?_⟩
        rw [hStd_smul_right, ← Finset.mul_prod_erase S u hz, map_mul, map_mul, ← hw z hz]
        ring
      | zero => exact ⟨0, by simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨ra, hra⟩ := ha
        obtain ⟨rb, hrb⟩ := hb
        exact ⟨ra + rb, by rw [map_add, hra, hrb, map_add, LinearMap.add_apply]⟩
      | smul a z _ hz =>
        obtain ⟨rz, hrz⟩ := hz
        exact ⟨cO E a * rz, by rw [hStd_smul_left, map_mul, hrz]⟩

/- English proof (translation)
Unfold `conjPrime₂`. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Simplify using `only [Ideal.comap_comap]`. Unfold `cO`. Establish `hid : (RingOfIntegers.mapRingHom (starRingEnd E)).comp (RingOfIntegers.mapRingHom (starRingEnd E)) = RingHom.id (𝓞 E)` using `RingHom.ext fun x => RingOfIntegers.ext (star_star (x : E))`.

Rewrite using `[hid, Ideal.comap_id]`.
-/
theorem conjP_involutive (Q : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ Q) = Q := by
  unfold conjPrime₂
  apply HeightOneSpectrum.ext
  simp only [Ideal.comap_comap]
  unfold cO
  have hid : (RingOfIntegers.mapRingHom (starRingEnd E)).comp
      (RingOfIntegers.mapRingHom (starRingEnd E)) = RingHom.id (𝓞 E) :=
    RingHom.ext fun x => RingOfIntegers.ext (star_star (x : E))
  rw [hid, Ideal.comap_id]

/- English proof (translation)
Introduce `x hx`. Assume the negation of the conclusion as `hnx`. Set `I : Ideal (𝓞 E)` to `N'.comap (LinearMap.toSpanSingleton (𝓞 E) (Sp E n) x)`. Establish `hI : I ≠ ⊤`. Introduce `htop`.

Apply `hnx` to reduce the goal to its premises. Establish `h1 : (1 : 𝓞 E) ∈ I` using `htop ▸ Submodule.mem_top`. Simplify `h1` using `[I]`. Take `⟨M, hM, hIM⟩` from `Ideal.exists_le_maximal I hI`. Establish `hMb : M ≠ ⊥`.

Introduce and unpack `rfl`. Conclude with `RingOfIntegers.not_isField (K := E) (Ring.isField_iff_maximal_bot.2 hM)`. Set `Q : HeightOneSpectrum (𝓞 E)` to `⟨M, hM.isPrime, hMb⟩`. Establish `hxQ : x ∈ localization₂ Q.asIdeal N'`. Rewrite using `[← h Q]`.

Conclude with `(mem_localization_iff_exists_smul_mem Q x).2 ⟨1, (Ideal.ne_top_iff_one _).1 hM.ne_top, by rwa [one_smul]⟩`. Take `⟨s, hs, hsx⟩` from `(mem_localization_iff_exists_smul_mem Q x).1 hxQ`. Conclude with `hs (hIM (by simpa [I] using hsx))`.
-/
theorem le_of_forall_localized_eq {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal N = localization₂ Q.asIdeal N') : N ≤ N' := by
  intro x hx
  by_contra hnx
  let I : Ideal (𝓞 E) := N'.comap (LinearMap.toSpanSingleton (𝓞 E) (Sp E n) x)
  have hI : I ≠ ⊤ := by
    intro htop
    apply hnx
    have h1 : (1 : 𝓞 E) ∈ I := htop ▸ Submodule.mem_top
    simpa [I] using h1
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  have hMb : M ≠ ⊥ := by
    rintro rfl
    exact RingOfIntegers.not_isField (K := E) (Ring.isField_iff_maximal_bot.2 hM)
  let Q : HeightOneSpectrum (𝓞 E) := ⟨M, hM.isPrime, hMb⟩
  have hxQ : x ∈ localization₂ Q.asIdeal N' := by
    rw [← h Q]
    exact (mem_localization_iff_exists_smul_mem Q x).2 ⟨1, (Ideal.ne_top_iff_one _).1 hM.ne_top, by rwa [one_smul]⟩
  obtain ⟨s, hs, hsx⟩ := (mem_localization_iff_exists_smul_mem Q x).1 hxQ
  exact hs (hIM (by simpa [I] using hsx))

/- English proof (translation)
Introduce `E _ _ _ n N N' hl hu hl' hu'`. Establish `part1 : ∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal N = localization₂ Q.asIdeal N' → localization₂ (conjPrime₂ Q).asIdeal N = localization₂ (conjPrime₂ Q).asIdeal N'`. Introduce `Q hQ`. Use extensionality with `x`. Rewrite using `[mem_localization_conj_iff hl.fg hu Q x, mem_localization_conj_iff hl'.fg hu' Q x, hQ]`.

Use `⟨part1, fun hor => ?_⟩` and prove the remaining obligations. Establish `hall : ∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal N = localization₂ Q.asIdeal N'`. Introduce `Q`. Break down `hor Q with h | h` into its components or cases. Conclude with `h`.

Establish `h'` using `part1 (conjPrime₂ Q) h`. Rewrite `h'` using `[conjP_involutive]`. Then use the resulting hypothesis. Conclude with `le_antisymm (le_of_forall_localized_eq hall) (le_of_forall_localized_eq fun Q => (hall Q).symm)`.
-/
theorem unimodular_ext : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (N N' : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E N → IsUnimodular (hStd E n) N → Submodule.IsLattice E N' → IsUnimodular (hStd E n) N' → (∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal N = localization₂ Q.asIdeal N' → localization₂ (conjPrime₂ Q).asIdeal N = localization₂ (conjPrime₂ Q).asIdeal N') ∧ ((∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal N = localization₂ Q.asIdeal N' ∨ localization₂ (conjPrime₂ Q).asIdeal N = localization₂ (conjPrime₂ Q).asIdeal N') → N = N') := by
  intro E _ _ _ n N N' hl hu hl' hu'
  have part1 : ∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal N = localization₂ Q.asIdeal N' →
      localization₂ (conjPrime₂ Q).asIdeal N = localization₂ (conjPrime₂ Q).asIdeal N' := by
    intro Q hQ
    ext x
    rw [mem_localization_conj_iff hl.fg hu Q x, mem_localization_conj_iff hl'.fg hu' Q x, hQ]
  refine ⟨part1, fun hor => ?_⟩
  have hall : ∀ Q : HeightOneSpectrum (𝓞 E), localization₂ Q.asIdeal N = localization₂ Q.asIdeal N' := by
    intro Q
    rcases hor Q with h | h
    · exact h
    · have h' := part1 (conjPrime₂ Q) h
      rwa [conjP_involutive] at h'
  exact le_antisymm (le_of_forall_localized_eq hall) (le_of_forall_localized_eq fun Q => (hall Q).symm)

end GlobalTheory.GO.UniExt
