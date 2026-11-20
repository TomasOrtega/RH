import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsNormRepresentation
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd

open NumberField

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.U0

open WA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

def toK (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (t : 𝓞 F) : K :=
  algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem algebraMap_int_F_to_K_eq_algebraMap_coe (t : 𝓞 F) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := rfl

/- English proof (translation)
Apply `Submonoid.subset_closure` to reduce the goal to its premises. Use `⟨ht, fun u hu => ?_⟩` and prove the remaining obligations. Establish `hfix : star (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t)) = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t)`. Rewrite using `[algebraMap_int_F_to_K_eq_algebraMap_coe]`. Conclude with `(hF _).2 ⟨(t : F), rfl⟩`.

Rewrite `hu` using `[hfix]`. Establish `hu' : u = algebraMap (𝓞 F) (𝓞 K) t` using `IsFractionRing.injective (𝓞 K) K hu`. Rewrite using `[hu']`. Conclude with `ht`.
-/
theorem mem_hcompl_of_notMem (hF : IsFixF K F) {P : Ideal (𝓞 K)} (hP : P.IsPrime) {t : 𝓞 F}
    (ht : t ∉ P.comap (algebraMap (𝓞 F) (𝓞 K))) :
    algebraMap (𝓞 F) (𝓞 K) t ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P := by
  apply Submonoid.subset_closure
  refine ⟨ht, fun u hu => ?_⟩
  have hfix : star (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t)) =
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) := by
    rw [algebraMap_int_F_to_K_eq_algebraMap_coe]
    exact (hF _).2 ⟨(t : F), rfl⟩
  rw [hfix] at hu
  have hu' : u = algebraMap (𝓞 F) (𝓞 K) t := IsFractionRing.injective (𝓞 K) K hu
  rw [hu']
  exact ht

/- English proof (translation)
The claim follows from `show _ ∈ Formalism.HermitianLatticesTheory.locR (K := K) P from (WA.mem_locR_iff hP _).2 ⟨r, s, hs, rfl⟩`.
-/
theorem div_mem_locRing {P : Ideal (𝓞 K)} (hP : P.IsPrime) (r : 𝓞 K) {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P) :
    algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s ∈ locRing P :=
  show _ ∈ Formalism.HermitianLatticesTheory.locR (K := K) P from (WA.mem_locR_iff hP _).2 ⟨r, s, hs, rfl⟩

/- English proof (translation)
Take `⟨f, hf⟩` from `(hF _).1 hx`. Establish `h1 : IsIntegral ℤ (algebraMap F K f)`. Rewrite using `[hf]`. Conclude with `NumberField.RingOfIntegers.isIntegral_coe x`. Establish `hint : IsIntegral ℤ f` using `(isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F K) (algebraMap F K).injective).mp h1`.

Use `⟨⟨f, hint⟩, ?_⟩` and prove the remaining obligations. Apply `NumberField.RingOfIntegers.ext` to reduce the goal to its premises. Conclude with `hf`.
-/
private theorem exists_int_preimage_of_star_fixed (hF : IsFixF K F) (x : 𝓞 K)
    (hx : star (algebraMap (𝓞 K) K x) = algebraMap (𝓞 K) K x) :
    ∃ t : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) t = x := by
  obtain ⟨f, hf⟩ := (hF _).1 hx
  have h1 : IsIntegral ℤ (algebraMap F K f) := by
    rw [hf]
    exact NumberField.RingOfIntegers.isIntegral_coe x
  have hint : IsIntegral ℤ f :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F K) (algebraMap F K).injective).mp h1
  refine ⟨⟨f, hint⟩, ?_⟩
  apply NumberField.RingOfIntegers.ext
  exact hf

/- English proof (translation)
Use `haveI := hP`. Take `⟨r, s, hs, rfl⟩` from `(WA.mem_locR_iff hP _).1 ha`. Establish `hs1 : s ∉ P` using `Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem P s hs`. Establish `hs2 : conjO K s ∉ P` using `Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem P _ (WA.conjO_mem_hcompl hs)`. Establish `hsK : algebraMap (𝓞 K) K s ≠ 0` using `WA.algebraMap_ne_zero_of_mem_hcompl hP hs`.

Establish `hs'K : algebraMap (𝓞 K) K (conjO K s) ≠ 0` using `WA.algebraMap_ne_zero_of_mem_hcompl hP (WA.conjO_mem_hcompl hs)`. Establish `hconj : algebraMap (𝓞 K) K (conjO K s) = star (algebraMap (𝓞 K) K s)` using `rfl`. Establish `hNfix : star (algebraMap (𝓞 K) K (s * conjO K s)) = algebraMap (𝓞 K) K (s * conjO K s)`. Rewrite using `[map_mul, hconj, star_mul, star_star, mul_comm]`. Establish `hMfix : star (algebraMap (𝓞 K) K (r * conjO K s)) = algebraMap (𝓞 K) K (r * conjO K s)`.

Establish `e : algebraMap (𝓞 K) K (r * conjO K s) = (algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) * algebraMap (𝓞 K) K (s * conjO K s)`. Rewrite using `[map_mul, map_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, star_mul', hfix, hNfix]`. Take `⟨tN, htN⟩` from `exists_int_preimage_of_star_fixed hF _ hNfix`.

Take `⟨tM, htM⟩` from `exists_int_preimage_of_star_fixed hF _ hMfix`. Use `⟨tM, tN, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Rewrite `h` using `[Ideal.mem_comap, htN]`. Conclude with `(hP.mem_or_mem h).elim hs1 hs2`.

Unfold `toK`. Rewrite using `[htM, htN, map_mul, map_mul, mul_div_mul_right _ _ hs'K]`.
-/
theorem exists_frac_of_fixed (hF : IsFixF K F) {P : Ideal (𝓞 K)} (hP : P.IsPrime) {a : K}
    (ha : a ∈ locRing P) (hfix : star a = a) :
    ∃ t s : 𝓞 F, s ∉ P.comap (algebraMap (𝓞 F) (𝓞 K)) ∧ a = toK K t / toK K s := by
  haveI := hP
  obtain ⟨r, s, hs, rfl⟩ := (WA.mem_locR_iff hP _).1 ha
  have hs1 : s ∉ P := Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem P s hs
  have hs2 : conjO K s ∉ P := Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem P _ (WA.conjO_mem_hcompl hs)
  have hsK : algebraMap (𝓞 K) K s ≠ 0 := WA.algebraMap_ne_zero_of_mem_hcompl hP hs
  have hs'K : algebraMap (𝓞 K) K (conjO K s) ≠ 0 :=
    WA.algebraMap_ne_zero_of_mem_hcompl hP (WA.conjO_mem_hcompl hs)
  have hconj : algebraMap (𝓞 K) K (conjO K s) = star (algebraMap (𝓞 K) K s) := rfl
  have hNfix : star (algebraMap (𝓞 K) K (s * conjO K s)) = algebraMap (𝓞 K) K (s * conjO K s) := by
    rw [map_mul, hconj, star_mul, star_star, mul_comm]
  have hMfix : star (algebraMap (𝓞 K) K (r * conjO K s)) = algebraMap (𝓞 K) K (r * conjO K s) := by
    have e : algebraMap (𝓞 K) K (r * conjO K s) =
        (algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) * algebraMap (𝓞 K) K (s * conjO K s) := by
      rw [map_mul, map_mul]
      field_simp
    rw [e, star_mul', hfix, hNfix]
  obtain ⟨tN, htN⟩ := exists_int_preimage_of_star_fixed hF _ hNfix
  obtain ⟨tM, htM⟩ := exists_int_preimage_of_star_fixed hF _ hMfix
  refine ⟨tM, tN, ?_, ?_⟩
  · intro h
    rw [Ideal.mem_comap, htN] at h
    exact (hP.mem_or_mem h).elim hs1 hs2
  · unfold toK
    rw [htM, htN, map_mul, map_mul, mul_div_mul_right _ _ hs'K]

/- English proof (translation)
Establish `hPp : P.IsPrime` using `hP.isPrime`. Use `haveI := hPp`. Establish `hPne : P ≠ ⊥` using `(Ideal.bot_lt_of_maximal P (NumberField.RingOfIntegers.not_isField K)).ne'`. Take `⟨x, hxP, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hPne`. Establish `hcx : algebraMap (𝓞 K) K (conjO K x) = star (algebraMap (𝓞 K) K x)` using `rfl`.

Establish `hxfix : star (algebraMap (𝓞 K) K (x * conjO K x)) = algebraMap (𝓞 K) K (x * conjO K x)`. Rewrite using `[map_mul, hcx, star_mul, star_star, mul_comm]`. Take `⟨n0, hn0⟩` from `exists_int_preimage_of_star_fixed hF _ hxfix`. Establish `hn0mem : n0 ∈ P.comap (algebraMap (𝓞 F) (𝓞 K))`. Rewrite using `[Ideal.mem_comap, hn0]`.

Conclude with `P.mul_mem_right _ hxP`. Establish `hn0ne : n0 ≠ 0`. Introduce `h`. Rewrite `hn0` using `[h, map_zero]`. Establish `e : algebraMap (𝓞 K) K x * star (algebraMap (𝓞 K) K x) = 0`.

Rewrite using `[← hcx, ← map_mul, ← hn0, map_zero]`. Break down `mul_eq_zero.1 e with h1 | h1` into its components or cases. Conclude with `hx0 (IsFractionRing.injective (𝓞 K) K (by rw [h1, map_zero]))`. Conclude with `hx0 (IsFractionRing.injective (𝓞 K) K (by rw [star_eq_zero.1 h1, map_zero]))`. Establish `h𝔭ne : P.comap (algebraMap (𝓞 F) (𝓞 K)) ≠ ⊥` using `fun h => hn0ne (by`.

Rewrite `hn0mem` using `[h]`. Conclude with `(Submodule.mem_bot _).1 hn0mem)`. Establish `h𝔭p : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsPrime` using `inferInstance`. Establish `h𝔭max : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal` using `h𝔭p.isMaximal h𝔭ne`. Establish `h𝔭top : P.comap (algebraMap (𝓞 F) (𝓞 K)) ≠ ⊤` using `h𝔭max.ne_top`.

Establish `hlt` using `Ideal.pow_right_strictAnti (P.comap (algebraMap (𝓞 F) (𝓞 K))) h𝔭ne h𝔭top (show 1 < 2 by norm_num)`. Take `⟨π₀, hπ₀, hπ₀2⟩` from `SetLike.exists_of_lt hlt`. Use `replace hπ₀ : π₀ ∈ P.comap (algebraMap (𝓞 F) (𝓞 K)) := by simpa using hπ₀`. Use `replace hπ₀2 : π₀ ∉ P.comap (algebraMap (𝓞 F) (𝓞 K)) ^ 2 := hπ₀2`. Establish `hdvd : P.comap (algebraMap (𝓞 F) (𝓞 K)) ∣ Ideal.span {π₀}` using `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hπ₀)`.

Take `⟨𝔞, h𝔞⟩` from `hdvd`. Establish `hnle : ¬ 𝔞 ≤ P.comap (algebraMap (𝓞 F) (𝓞 K))` using `fun hle => hπ₀2 (by`. Establish `hs : Ideal.span {π₀} ≤ P.comap (algebraMap (𝓞 F) (𝓞 K)) ^ 2`. Rewrite using `[h𝔞, sq]`. Conclude with `Ideal.mul_mono_right hle`.

Conclude with `hs (Ideal.mem_span_singleton_self π₀))`. Take `⟨c, hc𝔞, hc𝔭⟩` from `SetLike.not_le_iff_exists.1 hnle`. Establish `hA : ∀ z ∈ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))), ∃ w : 𝓞 K, algebraMap (𝓞 F) (𝓞 K) c * z = algebraMap (𝓞 F) (𝓞 K) π₀ * w`. Introduce `z hz`. Establish `hle : Ideal.span {c} * P.comap (algebraMap (𝓞 F) (𝓞 K)) ≤ Ideal.span {π₀}` using `Ideal.span_singleton_mul_le_iff.2 fun y hy => by`.

Rewrite using `[h𝔞, mul_comm c y]`. Conclude with `Ideal.mul_mem_mul hy hc𝔞`. Establish `hmap : Ideal.span {algebraMap (𝓞 F) (𝓞 K) c} * extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ Ideal.span {algebraMap (𝓞 F) (𝓞 K) π₀}`. Unfold `extP`. Establish `e1` using `Ideal.map_mono (f := algebraMap (𝓞 F) (𝓞 K)) hle`.

Rewrite `e1` using `[Ideal.map_mul, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]`. Conclude with `e1`. Establish `hm : algebraMap (𝓞 F) (𝓞 K) c * z ∈ Ideal.span {algebraMap (𝓞 F) (𝓞 K) π₀}` using `hmap (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hz)`. Take `⟨w, hw⟩` from `Ideal.mem_span_singleton'.1 hm`. Conclude with `⟨w, by rw [← hw, mul_comm]⟩`.

Establish `hιπ₀P : algebraMap (𝓞 F) (𝓞 K) π₀ ∈ P` using `hπ₀`. Establish `hπ₀ne : π₀ ≠ 0` using `fun h => hπ₀2 (by rw [h]; exact Ideal.zero_mem _)`. Establish `hπne : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) π₀) ≠ 0`. Introduce `h`. Rewrite `h` using `[algebraMap_int_F_to_K_eq_algebraMap_coe, map_eq_zero]`.

Conclude with `hπ₀ne (NumberField.RingOfIntegers.coe_eq_zero_iff.1 h)`. Establish `hπfix : star (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) π₀)) = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) π₀)`. Rewrite using `[algebraMap_int_F_to_K_eq_algebraMap_coe]`. Conclude with `(hF _).2 ⟨_, rfl⟩`. Establish `hcH : algebraMap (𝓞 F) (𝓞 K) c ∈ Formalism.HermitianLatticesTheory.hcompl (K` using `K) P := mem_hcompl_of_notMem hF hPp hc𝔭`.

Establish `hcK : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) c) ≠ 0` using `WA.algebraMap_ne_zero_of_mem_hcompl hPp hcH`. Use `⟨algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) π₀), ⟨?_, hπfix, hπne, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `div_mem_locRing hPp (algebraMap (𝓞 F) (𝓞 K) π₀) (Formalism.HermitianLatticesTheory.hcompl (K := K) P).one_mem`. Rewrite `h1` using `[map_one, div_one]`. Then use the resulting hypothesis. Introduce `s hs hsfix`.

Take `⟨t, n, hn, hst⟩` from `exists_frac_of_fixed hF hPp hs hsfix`. Establish `hnH` using `mem_hcompl_of_notMem hF hPp hn`. Establish `hnK : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) n) ≠ 0` using `WA.algebraMap_ne_zero_of_mem_hcompl hPp hnH`. Distinguish the cases in `ht : t ∈ P.comap (algebraMap (𝓞 F) (𝓞 K))`. Use `right`.

Take `⟨w, hw⟩` from `hA (algebraMap (𝓞 F) (𝓞 K) t) (Ideal.mem_map_of_mem _ ht)`. Use `show s * (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) π₀))⁻¹ ∈ locRing P`. Establish `e` using `congrArg (algebraMap (𝓞 K) K) hw`. Rewrite `e` using `[map_mul, map_mul]`. Establish `e2 : s * (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) π₀))⁻¹ = algebraMap (𝓞 K) K w / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) c * algebraMap (𝓞 F) (𝓞 K) n)`.

Rewrite using `[hst, map_mul]`. Unfold `toK`. Clear the denominators using the available nonvanishing facts. Take the linear combination `e`. Rewrite using `[e2]`.

Conclude with `div_mem_locRing hPp w (Submonoid.mul_mem _ hcH hnH)`. Use `left`. Establish `htH` using `mem_hcompl_of_notMem hF hPp ht`. Establish `htK : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0` using `WA.algebraMap_ne_zero_of_mem_hcompl hPp htH`. Use `⟨?_, hs, ?_⟩` and prove the remaining obligations.

Rewrite using `[hst]`. Conclude with `div_ne_zero htK hnK`. Rewrite using `[hst, inv_div]`. Conclude with `div_mem_locRing hPp _ htH`. Introduce `s hs`.

Establish `hs' : s ∈ Formalism.HermitianLatticesTheory.locR (K` using `K) P := hs`. Take `⟨r, u, hu, rfl⟩` from `(WA.mem_locR_iff hPp _).1 hs'`. Establish `hu1 : u ∉ P` using `Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem P u hu`. Establish `hu2 : conjO K u ∉ P` using `Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem P _ (WA.conjO_mem_hcompl hu)`. Establish `huK : algebraMap (𝓞 K) K u ≠ 0` using `WA.algebraMap_ne_zero_of_mem_hcompl hPp hu`.

Establish `hvP : u + algebraMap (𝓞 F) (𝓞 K) π₀ * r ∉ P` using `fun h => hu1 (by`. Establish `h2` using `P.sub_mem h (P.mul_mem_right r hιπ₀P)`. Rewrite using `[add_sub_cancel_right] at h2)` and apply the resulting hypothesis. Establish `hcu : algebraMap (𝓞 K) K (conjO K u) = star (algebraMap (𝓞 K) K u)` using `rfl`. Establish `hcr : algebraMap (𝓞 K) K (conjO K r) = star (algebraMap (𝓞 K) K r)` using `rfl`.

Establish `hcv : algebraMap (𝓞 K) K (conjO K (u + algebraMap (𝓞 F) (𝓞 K) π₀ * r)) = star (algebraMap (𝓞 K) K (u + algebraMap (𝓞 F) (𝓞 K) π₀ * r))` using `rfl`. Establish `hconjv : conjO K (u + algebraMap (𝓞 F) (𝓞 K) π₀ * r) = conjO K u + algebraMap (𝓞 F) (𝓞 K) π₀ * conjO K r`. Apply `IsFractionRing.injective (𝓞 K) K` to reduce the goal to its premises. Rewrite using `[hcv]`. Simplify using `only [map_add, map_mul, star_add, star_mul', hπfix, hcu, hcr]`.

Establish `hvH : u + algebraMap (𝓞 F) (𝓞 K) π₀ * r ∈ Formalism.HermitianLatticesTheory.hcompl (K` using `K) P := by`. Apply `Submonoid.subset_closure` to reduce the goal to its premises. Use `⟨hvP, fun t ht => ?_⟩` and prove the remaining obligations. Establish `htv : t = conjO K (u + algebraMap (𝓞 F) (𝓞 K) π₀ * r)` using `IsFractionRing.injective (𝓞 K) K (by rw [ht, hcv])`. Rewrite using `[htv, hconjv]`.

Introduce `h`. Conclude with `hu2 (by`. Establish `h2` using `P.sub_mem h (P.mul_mem_right (conjO K r) hιπ₀P)`. Rewrite using `[add_sub_cancel_right] at h2)` and apply the resulting hypothesis. Establish `hvK : algebraMap (𝓞 K) K (u + algebraMap (𝓞 F) (𝓞 K) π₀ * r) ≠ 0` using `WA.algebraMap_ne_zero_of_mem_hcompl hPp hvH`.

Establish `e : 1 + algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) π₀) * (algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K u) = algebraMap (𝓞 K) K (u + algebraMap (𝓞 F) (𝓞 K) π₀ * r) / algebraMap (𝓞 K) K u`. Rewrite using `[map_add, map_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Use `⟨div_ne_zero hvK huK, div_mem_locRing hPp _ hu, ?_⟩` and prove the remaining obligations.

Rewrite using `[inv_div]`. Conclude with `div_mem_locRing hPp _ hvH`. Introduce `z hz`. Take `⟨w, hw⟩` from `hA z hz`. Use `show algebraMap (𝓞 K) K z * (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) π₀))⁻¹ ∈ locRing P`.

Establish `e` using `congrArg (algebraMap (𝓞 K) K) hw`. Rewrite `e` using `[map_mul, map_mul]`. Establish `e2 : algebraMap (𝓞 K) K z * (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) π₀))⁻¹ = algebraMap (𝓞 K) K w / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) c)`. Clear the denominators using the available nonvanishing facts. Take the linear combination `e`.

Rewrite using `[e2]`. Conclude with `div_mem_locRing hPp w hcH`. Introduce `z hz`. Establish `hz' : algebraMap (𝓞 K) K z * (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) π₀))⁻¹ * (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) π₀))⁻¹ ∈ Formalism.HermitianLatticesTheory.locR (K` using `K) P := hz`. Take `⟨r, u, hu, hru⟩` from `(WA.mem_locR_iff hPp _).1 hz'`.

Establish `huK : algebraMap (𝓞 K) K u ≠ 0` using `WA.algebraMap_ne_zero_of_mem_hcompl hPp hu`. Establish `e1 : z * u = r * (algebraMap (𝓞 F) (𝓞 K) π₀) ^ 2`. Apply `IsFractionRing.injective (𝓞 K) K` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, map_pow]`. Clear denominators, using `at hru` for the nonvanishing conditions.

Take the linear combination `hru`. Establish `hu1 : u ∉ P` using `Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem P u hu`. Establish `hu2 : conjO K u ∉ P` using `Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem P _ (WA.conjO_mem_hcompl hu)`. Establish `hcu : algebraMap (𝓞 K) K (conjO K u) = star (algebraMap (𝓞 K) K u)` using `rfl`. Establish `hNfix : star (algebraMap (𝓞 K) K (u * conjO K u)) = algebraMap (𝓞 K) K (u * conjO K u)`.

Rewrite using `[map_mul, hcu, star_mul, star_star, mul_comm]`. Take `⟨n, hn⟩` from `exists_int_preimage_of_star_fixed hF _ hNfix`. Establish `hn𝔭 : n ∉ P.comap (algebraMap (𝓞 F) (𝓞 K))`. Introduce `h`. Rewrite `h` using `[Ideal.mem_comap, hn]`.

Conclude with `(hPp.mem_or_mem h).elim hu1 hu2`. Take `⟨y, i, hi, hyi⟩` from `h𝔭max.exists_inv hn𝔭`. Establish `hzN : z * algebraMap (𝓞 F) (𝓞 K) n ∈ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ^ 2`. Rewrite using `[hn, ← mul_assoc, e1]`. Apply `Ideal.mul_mem_right` to reduce the goal to its premises.

Apply `Ideal.mul_mem_left` to reduce the goal to its premises. Conclude with `Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hπ₀) 2`. Establish `hi2 : algebraMap (𝓞 F) (𝓞 K) (i * i) ∈ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ^ 2`. Rewrite using `[map_mul, sq]`. Conclude with `Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hi) (Ideal.mem_map_of_mem _ hi)`.

Establish `h1 : (1 : 𝓞 F) = y * (y * n + 2 * i) * n + i * i`. Take the linear combination `(-(y * n + i + 1)) * hyi`. Establish `hz2 : z = algebraMap (𝓞 F) (𝓞 K) (y * (y * n + 2 * i)) * (z * algebraMap (𝓞 F) (𝓞 K) n) + z * algebraMap (𝓞 F) (𝓞 K) (i * i)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1]`.

Simplify using `only [map_add, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hz2]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hzN) (Ideal.mul_mem_left _ _ hi2)`.
-/
theorem exists_isUnif (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) :
    ∃ π : K, IsUnif (locRing P) π ∧
      (∀ z ∈ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))), Dv (locRing P) π (algebraMap (𝓞 K) K z)) ∧
      ∀ z : 𝓞 K, Dv (locRing P) π (algebraMap (𝓞 K) K z * π⁻¹) →
        z ∈ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ^ 2 := by
  have hPp : P.IsPrime := hP.isPrime
  haveI := hPp
  have hPne : P ≠ ⊥ := (Ideal.bot_lt_of_maximal P (NumberField.RingOfIntegers.not_isField K)).ne'
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPne
  have hcx : algebraMap (𝓞 K) K (conjO K x) = star (algebraMap (𝓞 K) K x) := rfl
  have hxfix : star (algebraMap (𝓞 K) K (x * conjO K x)) = algebraMap (𝓞 K) K (x * conjO K x) := by
    rw [map_mul, hcx, star_mul, star_star, mul_comm]
  obtain ⟨n0, hn0⟩ := exists_int_preimage_of_star_fixed hF _ hxfix
  have hn0mem : n0 ∈ P.comap (algebraMap (𝓞 F) (𝓞 K)) := by
    rw [Ideal.mem_comap, hn0]
    exact P.mul_mem_right _ hxP
  have hn0ne : n0 ≠ 0 := by
    intro h
    rw [h, map_zero] at hn0
    have e : algebraMap (𝓞 K) K x * star (algebraMap (𝓞 K) K x) = 0 := by
      rw [← hcx, ← map_mul, ← hn0, map_zero]
    rcases mul_eq_zero.1 e with h1 | h1
    · exact hx0 (IsFractionRing.injective (𝓞 K) K (by rw [h1, map_zero]))
    · exact hx0 (IsFractionRing.injective (𝓞 K) K (by rw [star_eq_zero.1 h1, map_zero]))
  have h𝔭ne : P.comap (algebraMap (𝓞 F) (𝓞 K)) ≠ ⊥ := fun h => hn0ne (by
    rw [h] at hn0mem
    exact (Submodule.mem_bot _).1 hn0mem)
  have h𝔭p : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsPrime := inferInstance
  have h𝔭max : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal := h𝔭p.isMaximal h𝔭ne
  have h𝔭top : P.comap (algebraMap (𝓞 F) (𝓞 K)) ≠ ⊤ := h𝔭max.ne_top
  have hlt := Ideal.pow_right_strictAnti (P.comap (algebraMap (𝓞 F) (𝓞 K))) h𝔭ne h𝔭top
    (show 1 < 2 by norm_num)
  obtain ⟨π₀, hπ₀, hπ₀2⟩ := SetLike.exists_of_lt hlt
  replace hπ₀ : π₀ ∈ P.comap (algebraMap (𝓞 F) (𝓞 K)) := by simpa using hπ₀
  replace hπ₀2 : π₀ ∉ P.comap (algebraMap (𝓞 F) (𝓞 K)) ^ 2 := hπ₀2
  have hdvd : P.comap (algebraMap (𝓞 F) (𝓞 K)) ∣ Ideal.span {π₀} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hπ₀)
  obtain ⟨𝔞, h𝔞⟩ := hdvd
  have hnle : ¬ 𝔞 ≤ P.comap (algebraMap (𝓞 F) (𝓞 K)) := fun hle => hπ₀2 (by
    have hs : Ideal.span {π₀} ≤ P.comap (algebraMap (𝓞 F) (𝓞 K)) ^ 2 := by
      rw [h𝔞, sq]
      exact Ideal.mul_mono_right hle
    exact hs (Ideal.mem_span_singleton_self π₀))
  obtain ⟨c, hc𝔞, hc𝔭⟩ := SetLike.not_le_iff_exists.1 hnle
  have hA : ∀ z ∈ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))),
      ∃ w : 𝓞 K, algebraMap (𝓞 F) (𝓞 K) c * z = algebraMap (𝓞 F) (𝓞 K) π₀ * w := by
    intro z hz
    have hle : Ideal.span {c} * P.comap (algebraMap (𝓞 F) (𝓞 K)) ≤ Ideal.span {π₀} :=
      Ideal.span_singleton_mul_le_iff.2 fun y hy => by
        rw [h𝔞, mul_comm c y]
        exact Ideal.mul_mem_mul hy hc𝔞
    have hmap : Ideal.span {algebraMap (𝓞 F) (𝓞 K) c} * extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤
        Ideal.span {algebraMap (𝓞 F) (𝓞 K) π₀} := by
      unfold extP
      have e1 := Ideal.map_mono (f := algebraMap (𝓞 F) (𝓞 K)) hle
      rw [Ideal.map_mul, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton] at e1
      exact e1
    have hm : algebraMap (𝓞 F) (𝓞 K) c * z ∈ Ideal.span {algebraMap (𝓞 F) (𝓞 K) π₀} :=
      hmap (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hz)
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hm
    exact ⟨w, by rw [← hw, mul_comm]⟩
  have hιπ₀P : algebraMap (𝓞 F) (𝓞 K) π₀ ∈ P := hπ₀
  have hπ₀ne : π₀ ≠ 0 := fun h => hπ₀2 (by rw [h]; exact Ideal.zero_mem _)
  have hπne : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) π₀) ≠ 0 := by
    intro h
    rw [algebraMap_int_F_to_K_eq_algebraMap_coe, map_eq_zero] at h
    exact hπ₀ne (NumberField.RingOfIntegers.coe_eq_zero_iff.1 h)
  have hπfix : star (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) π₀)) =
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) π₀) := by
    rw [algebraMap_int_F_to_K_eq_algebraMap_coe]
    exact (hF _).2 ⟨_, rfl⟩
  have hcH : algebraMap (𝓞 F) (𝓞 K) c ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P := mem_hcompl_of_notMem hF hPp hc𝔭
  have hcK : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) c) ≠ 0 :=
    WA.algebraMap_ne_zero_of_mem_hcompl hPp hcH
  refine ⟨algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) π₀), ⟨?_, hπfix, hπne, ?_, ?_⟩, ?_, ?_⟩
  · have h1 := div_mem_locRing hPp (algebraMap (𝓞 F) (𝓞 K) π₀) (Formalism.HermitianLatticesTheory.hcompl (K := K) P).one_mem
    rwa [map_one, div_one] at h1
  · intro s hs hsfix
    obtain ⟨t, n, hn, hst⟩ := exists_frac_of_fixed hF hPp hs hsfix
    have hnH := mem_hcompl_of_notMem hF hPp hn
    have hnK : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) n) ≠ 0 :=
      WA.algebraMap_ne_zero_of_mem_hcompl hPp hnH
    by_cases ht : t ∈ P.comap (algebraMap (𝓞 F) (𝓞 K))
    · right
      obtain ⟨w, hw⟩ := hA (algebraMap (𝓞 F) (𝓞 K) t) (Ideal.mem_map_of_mem _ ht)
      show s * (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) π₀))⁻¹ ∈ locRing P
      have e := congrArg (algebraMap (𝓞 K) K) hw
      rw [map_mul, map_mul] at e
      have e2 : s * (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) π₀))⁻¹ =
          algebraMap (𝓞 K) K w / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) c * algebraMap (𝓞 F) (𝓞 K) n) := by
        rw [hst, map_mul]
        unfold toK
        field_simp
        linear_combination e
      rw [e2]
      exact div_mem_locRing hPp w (Submonoid.mul_mem _ hcH hnH)
    · left
      have htH := mem_hcompl_of_notMem hF hPp ht
      have htK : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 :=
        WA.algebraMap_ne_zero_of_mem_hcompl hPp htH
      refine ⟨?_, hs, ?_⟩
      · rw [hst]
        exact div_ne_zero htK hnK
      · rw [hst, inv_div]
        exact div_mem_locRing hPp _ htH
  · intro s hs
    have hs' : s ∈ Formalism.HermitianLatticesTheory.locR (K := K) P := hs
    obtain ⟨r, u, hu, rfl⟩ := (WA.mem_locR_iff hPp _).1 hs'
    have hu1 : u ∉ P := Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem P u hu
    have hu2 : conjO K u ∉ P := Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem P _ (WA.conjO_mem_hcompl hu)
    have huK : algebraMap (𝓞 K) K u ≠ 0 := WA.algebraMap_ne_zero_of_mem_hcompl hPp hu
    have hvP : u + algebraMap (𝓞 F) (𝓞 K) π₀ * r ∉ P := fun h => hu1 (by
      have h2 := P.sub_mem h (P.mul_mem_right r hιπ₀P)
      rwa [add_sub_cancel_right] at h2)
    have hcu : algebraMap (𝓞 K) K (conjO K u) = star (algebraMap (𝓞 K) K u) := rfl
    have hcr : algebraMap (𝓞 K) K (conjO K r) = star (algebraMap (𝓞 K) K r) := rfl
    have hcv : algebraMap (𝓞 K) K (conjO K (u + algebraMap (𝓞 F) (𝓞 K) π₀ * r)) =
        star (algebraMap (𝓞 K) K (u + algebraMap (𝓞 F) (𝓞 K) π₀ * r)) := rfl
    have hconjv : conjO K (u + algebraMap (𝓞 F) (𝓞 K) π₀ * r) =
        conjO K u + algebraMap (𝓞 F) (𝓞 K) π₀ * conjO K r := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [hcv]
      simp only [map_add, map_mul, star_add, star_mul', hπfix, hcu, hcr]
    have hvH : u + algebraMap (𝓞 F) (𝓞 K) π₀ * r ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P := by
      apply Submonoid.subset_closure
      refine ⟨hvP, fun t ht => ?_⟩
      have htv : t = conjO K (u + algebraMap (𝓞 F) (𝓞 K) π₀ * r) :=
        IsFractionRing.injective (𝓞 K) K (by rw [ht, hcv])
      rw [htv, hconjv]
      intro h
      exact hu2 (by
        have h2 := P.sub_mem h (P.mul_mem_right (conjO K r) hιπ₀P)
        rwa [add_sub_cancel_right] at h2)
    have hvK : algebraMap (𝓞 K) K (u + algebraMap (𝓞 F) (𝓞 K) π₀ * r) ≠ 0 :=
      WA.algebraMap_ne_zero_of_mem_hcompl hPp hvH
    have e : 1 + algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) π₀) *
        (algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K u) =
        algebraMap (𝓞 K) K (u + algebraMap (𝓞 F) (𝓞 K) π₀ * r) / algebraMap (𝓞 K) K u := by
      rw [map_add, map_mul]
      field_simp
    rw [e]
    refine ⟨div_ne_zero hvK huK, div_mem_locRing hPp _ hu, ?_⟩
    rw [inv_div]
    exact div_mem_locRing hPp _ hvH
  · intro z hz
    obtain ⟨w, hw⟩ := hA z hz
    show algebraMap (𝓞 K) K z * (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) π₀))⁻¹ ∈ locRing P
    have e := congrArg (algebraMap (𝓞 K) K) hw
    rw [map_mul, map_mul] at e
    have e2 : algebraMap (𝓞 K) K z * (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) π₀))⁻¹ =
        algebraMap (𝓞 K) K w / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) c) := by
      field_simp
      linear_combination e
    rw [e2]
    exact div_mem_locRing hPp w hcH
  · intro z hz
    have hz' : algebraMap (𝓞 K) K z * (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) π₀))⁻¹ *
        (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) π₀))⁻¹ ∈ Formalism.HermitianLatticesTheory.locR (K := K) P := hz
    obtain ⟨r, u, hu, hru⟩ := (WA.mem_locR_iff hPp _).1 hz'
    have huK : algebraMap (𝓞 K) K u ≠ 0 := WA.algebraMap_ne_zero_of_mem_hcompl hPp hu
    have e1 : z * u = r * (algebraMap (𝓞 F) (𝓞 K) π₀) ^ 2 := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [map_mul, map_mul, map_pow]
      field_simp at hru
      linear_combination hru
    have hu1 : u ∉ P := Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem P u hu
    have hu2 : conjO K u ∉ P := Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem P _ (WA.conjO_mem_hcompl hu)
    have hcu : algebraMap (𝓞 K) K (conjO K u) = star (algebraMap (𝓞 K) K u) := rfl
    have hNfix : star (algebraMap (𝓞 K) K (u * conjO K u)) = algebraMap (𝓞 K) K (u * conjO K u) := by
      rw [map_mul, hcu, star_mul, star_star, mul_comm]
    obtain ⟨n, hn⟩ := exists_int_preimage_of_star_fixed hF _ hNfix
    have hn𝔭 : n ∉ P.comap (algebraMap (𝓞 F) (𝓞 K)) := by
      intro h
      rw [Ideal.mem_comap, hn] at h
      exact (hPp.mem_or_mem h).elim hu1 hu2
    obtain ⟨y, i, hi, hyi⟩ := h𝔭max.exists_inv hn𝔭
    have hzN : z * algebraMap (𝓞 F) (𝓞 K) n ∈ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ^ 2 := by
      rw [hn, ← mul_assoc, e1]
      apply Ideal.mul_mem_right
      apply Ideal.mul_mem_left
      exact Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hπ₀) 2
    have hi2 : algebraMap (𝓞 F) (𝓞 K) (i * i) ∈ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ^ 2 := by
      rw [map_mul, sq]
      exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hi) (Ideal.mem_map_of_mem _ hi)
    have h1 : (1 : 𝓞 F) = y * (y * n + 2 * i) * n + i * i := by
      linear_combination (-(y * n + i + 1)) * hyi
    have hz2 : z = algebraMap (𝓞 F) (𝓞 K) (y * (y * n + 2 * i)) * (z * algebraMap (𝓞 F) (𝓞 K) n) +
        z * algebraMap (𝓞 F) (𝓞 K) (i * i) := by
      calc z = z * algebraMap (𝓞 F) (𝓞 K) 1 := by rw [map_one, mul_one]
        _ = _ := by
          rw [h1]
          simp only [map_add, map_mul]
          ring
    rw [hz2]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hzN) (Ideal.mul_mem_left _ _ hi2)

end Formalism.HermitianLattices.Ext.L3.U0
