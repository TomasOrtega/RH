import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropTermSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.QuotSectionsFiniteSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistBundleToSubSystem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace SectionCount.Drop.Term

section Cancel

variable {R : Type*} [CommRing R] {Ω : Type w} [Field Ω] [Algebra R Ω]

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hzP` to reduce the goal to its premises. Establish `h1 : Submodule.span R {z} * Z' ≤ P`. Rewrite using `[Submodule.mul_le]`.

Introduce `m hm n hn`. Take `⟨r, rfl⟩` from `Submodule.mem_span_singleton.mp hm`. Rewrite using `[smul_mul_assoc]`. Use `P.smul_mem r (hcon n hn ?_)` and prove the remaining obligations. Rewrite using `[← hZ]`.

Conclude with `Submodule.mul_mem_mul hz hn`. Establish `h2 : z ∈ Submodule.span R {z} * Z' * Z`. Rewrite using `[mul_assoc, mul_comm Z' Z, hZ, mul_one]`. Conclude with `Submodule.mem_span_singleton_self z`. Conclude with `mul_le_mul' h1 le_rfl h2`.
-/
theorem exists_mul_not_mem {P Z Z' : Submodule R Ω} (hZ : Z * Z' = 1) {z : Ω} (hz : z ∈ Z)
    (hzP : z ∉ P * Z) : ∃ z' ∈ Z', z * z' ∈ (1 : Submodule R Ω) ∧ z * z' ∉ P := by
  by_contra hcon
  push Not at hcon
  apply hzP
  have h1 : Submodule.span R {z} * Z' ≤ P := by
    rw [Submodule.mul_le]
    intro m hm n hn
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hm
    rw [smul_mul_assoc]
    refine P.smul_mem r (hcon n hn ?_)
    rw [← hZ]
    exact Submodule.mul_mem_mul hz hn
  have h2 : z ∈ Submodule.span R {z} * Z' * Z := by
    rw [mul_assoc, mul_comm Z' Z, hZ, mul_one]
    exact Submodule.mem_span_singleton_self z
  exact mul_le_mul' h1 le_rfl h2

/- English proof (translation)
Assume the negation of the conclusion as `hyP`. Take `⟨l', hl', hl1, hlP⟩` from `exists_mul_not_mem hL hs hsP`. Take `⟨m', hm', hm1, hmP⟩` from `exists_mul_not_mem hM hy hyP`. Establish `h : s * l' * (y * m') ∈ P`. Establish `h1 : s * y * (l' * m') ∈ P * (L * M) * (L' * M')` using `Submodule.mul_mem_mul hsy (Submodule.mul_mem_mul hl' hm')`.

Establish `h2 : P * (L * M) * (L' * M') = P`. Rewrite using `[show P * (L * M) * (L' * M') = P * ((L * L') * (M * M')) by ring, hL, hM, mul_one, mul_one]`. Rewrite `h1` using `[h2]`. Rewrite using `[show s * l' * (y * m') = s * y * (l' * m') by ring]` and apply the resulting hypothesis. Conclude with `(hP _ hl1 _ hm1 h).elim hlP hmP`.
-/
theorem mem_of_mul_mem {P L L' M M' : Submodule R Ω} (hL : L * L' = 1) (hM : M * M' = 1)
    (hP : ∀ a ∈ (1 : Submodule R Ω), ∀ b ∈ (1 : Submodule R Ω), a * b ∈ P → a ∈ P ∨ b ∈ P)
    {s y : Ω} (hs : s ∈ L) (hsP : s ∉ P * L) (hy : y ∈ M) (hsy : s * y ∈ P * (L * M)) :
    y ∈ P * M := by
  by_contra hyP
  obtain ⟨l', hl', hl1, hlP⟩ := exists_mul_not_mem hL hs hsP
  obtain ⟨m', hm', hm1, hmP⟩ := exists_mul_not_mem hM hy hyP
  have h : s * l' * (y * m') ∈ P := by
    have h1 : s * y * (l' * m') ∈ P * (L * M) * (L' * M') :=
      Submodule.mul_mem_mul hsy (Submodule.mul_mem_mul hl' hm')
    have h2 : P * (L * M) * (L' * M') = P := by
      rw [show P * (L * M) * (L' * M') = P * ((L * L') * (M * M')) by ring, hL, hM, mul_one, mul_one]
    rw [h2] at h1
    rwa [show s * l' * (y * m') = s * y * (l' * m') by ring]
  exact (hP _ hl1 _ hm1 h).elim hlP hmP

end Cancel

section Ideal

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {pp : Ideal (Poly k N)}

/- English proof (translation)
Establish `hxi : x i ≠ 0` using `(mem_support x).mp (I.2.2 hi)`. Use `Submodule.subset_span ⟨X i, X i, 1, hp, X_mem_monos hi, isHomogeneous_X k i, isHomogeneous_X k i, ?_⟩` and prove the remaining obligations. Rewrite using `[aeval_X, div_self hxi]`.
-/
theorem one_mem_idealMod {I : Chart x} {i : Fin (N + 1)} (hi : i ∈ I.1) (hp : (X i : Poly k N) ∈ pp) :
    (1 : Ω) ∈ idealMod pp I := by
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  refine Submodule.subset_span ⟨X i, X i, 1, hp, X_mem_monos hi, isHomogeneous_X k i,
    isHomogeneous_X k i, ?_⟩
  rw [aeval_X, div_self hxi]

/- English proof (translation)
Use `hW` as an intermediate fact. Introduce `h1`. Take `⟨g, s, d, hg, hs, hgd, hsd, h1g⟩` from `idealMod_mem_form pp I h1`. Establish `hs0` using `eval_ne_zero_of_mem_monos I hs`. Rewrite `h1g` using `[eq_div_iff hs0, one_mul]`.

Establish `hgs : g - s ∈ pp` using `hle ((mem_primeOf_of_isHomogeneous x (hgd.sub hsd)).mpr (by`. Rewrite using `[map_sub, h1g, sub_self]))`. Establish `hsp : s ∈ pp`. Use `pp.sub_mem hg hgs` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis.

Conclude with `monos_not_mem (pp := pp) hI hs hsp`.
-/
theorem one_not_mem_idealMod (hW : pp.IsPrime) (hle : primeOf (S := k) x ≤ pp) {I : Chart x}
    (hI : ∀ i ∈ I.1, (X i : Poly k N) ∉ pp) : (1 : Ω) ∉ idealMod pp I := by
  have := hW
  intro h1
  obtain ⟨g, s, d, hg, hs, hgd, hsd, h1g⟩ := idealMod_mem_form pp I h1
  have hs0 := eval_ne_zero_of_mem_monos I hs
  rw [eq_div_iff hs0, one_mul] at h1g
  have hgs : g - s ∈ pp := hle ((mem_primeOf_of_isHomogeneous x (hgd.sub hsd)).mpr (by
    rw [map_sub, h1g, sub_self]))
  have hsp : s ∈ pp := by
    have := pp.sub_mem hg hgs
    rwa [sub_sub_cancel] at this
  exact monos_not_mem (pp := pp) hI hs hsp

/- English proof (translation)
Use `hW` as an intermediate fact. Introduce `a ha b hb hab`. Take `⟨a', rfl⟩` from `Submodule.mem_one.mp ha`. Take `⟨b', rfl⟩` from `Submodule.mem_one.mp hb`. Take `⟨f, s, e, hs, hf, hse, hfa⟩` from `a'.2`.

Take `⟨g, t, e', ht, hg, hte, hgb⟩` from `b'.2`. Express the relevant statement in the definitionally equal form `(a' : Ω) * (b' : Ω) ∈ idealMod pp I at hab`. Take `⟨h, m, d, hh, hm, hhd, hmd, hab'⟩` from `idealMod_mem_form pp I hab`. Establish `hs0` using `eval_ne_zero_of_mem_monos I hs`. Establish `ht0` using `eval_ne_zero_of_mem_monos I ht`.

Establish `hm0` using `eval_ne_zero_of_mem_monos I hm`. Rewrite `hab'` using `[hfa, hgb, div_mul_div_comm, div_eq_div_iff (mul_ne_zero hs0 ht0) hm0]`. Establish `hval : aeval x (f * g * m - h * (s * t)) = 0`. Simplify using `only [map_sub, map_mul]`. Take the linear combination `hab'`.

Establish `h1 : (f * g * m).IsHomogeneous (e + e' + d)` using `(hf.mul hg).mul hmd`. Establish `h2 : (h * (s * t)).IsHomogeneous (e + e' + d)`. Use `hhd.mul (hse.mul hte)` as an intermediate fact. Rewrite `this` using `[show d + (e + e') = e + e' + d by ring]`. Then use the resulting hypothesis. Establish `hmem : f * g * m - h * (s * t) ∈ pp` using `hle ((mem_primeOf_of_isHomogeneous x (h1.sub h2)).mpr hval)`.

Establish `hfgm : f * g * m ∈ pp`. Use `pp.add_mem hmem (pp.mul_mem_right (s * t) hh)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Establish `hfg : f * g ∈ pp` using `(hW.mem_or_mem hfgm).resolve_right (monos_not_mem hI hm)`. Break down `hW.mem_or_mem hfg with hfp | hgp` into its components or cases.

Use `left`. Express the relevant statement in the definitionally equal form `(a' : Ω) ∈ idealMod pp I`. Rewrite using `[hfa]`. Conclude with `Submodule.subset_span ⟨f, s, e, hfp, hs, hf, hse, rfl⟩`. Use `right`.

Express the relevant statement in the definitionally equal form `(b' : Ω) ∈ idealMod pp I`. Rewrite using `[hgb]`. Conclude with `Submodule.subset_span ⟨g, t, e', hgp, ht, hg, hte, rfl⟩`.
-/
theorem idealMod_prime (hW : pp.IsPrime) (hle : primeOf (S := k) x ≤ pp) {I : Chart x}
    (hI : ∀ i ∈ I.1, (X i : Poly k N) ∉ pp) :
    ∀ a ∈ (1 : Submodule (chartRing k x I) Ω), ∀ b ∈ (1 : Submodule (chartRing k x I) Ω),
      a * b ∈ idealMod pp I → a ∈ idealMod pp I ∨ b ∈ idealMod pp I := by
  have := hW
  intro a ha b hb hab
  obtain ⟨a', rfl⟩ := Submodule.mem_one.mp ha
  obtain ⟨b', rfl⟩ := Submodule.mem_one.mp hb
  obtain ⟨f, s, e, hs, hf, hse, hfa⟩ := a'.2
  obtain ⟨g, t, e', ht, hg, hte, hgb⟩ := b'.2
  change (a' : Ω) * (b' : Ω) ∈ idealMod pp I at hab
  obtain ⟨h, m, d, hh, hm, hhd, hmd, hab'⟩ := idealMod_mem_form pp I hab
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have ht0 := eval_ne_zero_of_mem_monos I ht
  have hm0 := eval_ne_zero_of_mem_monos I hm
  rw [hfa, hgb, div_mul_div_comm, div_eq_div_iff (mul_ne_zero hs0 ht0) hm0] at hab'
  have hval : aeval x (f * g * m - h * (s * t)) = 0 := by
    simp only [map_sub, map_mul]
    linear_combination hab'
  have h1 : (f * g * m).IsHomogeneous (e + e' + d) := (hf.mul hg).mul hmd
  have h2 : (h * (s * t)).IsHomogeneous (e + e' + d) := by
    have := hhd.mul (hse.mul hte)
    rwa [show d + (e + e') = e + e' + d by ring] at this
  have hmem : f * g * m - h * (s * t) ∈ pp :=
    hle ((mem_primeOf_of_isHomogeneous x (h1.sub h2)).mpr hval)
  have hfgm : f * g * m ∈ pp := by
    have := pp.add_mem hmem (pp.mul_mem_right (s * t) hh)
    rwa [sub_add_cancel] at this
  have hfg : f * g ∈ pp := (hW.mem_or_mem hfgm).resolve_right (monos_not_mem hI hm)
  rcases hW.mem_or_mem hfg with hfp | hgp
  · left
    change (a' : Ω) ∈ idealMod pp I
    rw [hfa]
    exact Submodule.subset_span ⟨f, s, e, hfp, hs, hf, hse, rfl⟩
  · right
    change (b' : Ω) ∈ idealMod pp I
    rw [hgb]
    exact Submodule.subset_span ⟨g, t, e', hgp, ht, hg, hte, rfl⟩

/- English proof (translation)
Take `⟨g, m, e, hg, hm, hge, hme, rfl⟩` from `idealMod_mem_form pp K ha`. Take `⟨i, hi⟩` from `I.2.1`. Establish `hxi : x i ≠ 0` using `(mem_support x).mp (I.2.2 hi)`. Establish `hm0` using `eval_ne_zero_of_mem_monos K hm`. Establish `hX0 : aeval x (X i ^ e : Poly k N) ≠ 0`.

Rewrite using `[map_pow, aeval_X]`. Conclude with `pow_ne_zero _ hxi`. Use `⟨⟨aeval x m / aeval x (X i ^ e), m, X i ^ e, e, pow_mem (X_mem_monos hi) e, hme, isHomogeneous_X_pow i e, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[isUnit_iff_exists_inv]`. Use `⟨⟨aeval x (X i ^ e) / aeval x m, X i ^ e, m, e, hm, isHomogeneous_X_pow i e, hme, rfl⟩, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `aeval x m / aeval x (X i ^ e) * (aeval x (X i ^ e) / aeval x m) = 1`. Clear the denominators using the available nonvanishing facts. Express the relevant statement in the definitionally equal form `aeval x m / aeval x (X i ^ e) * (aeval x g / aeval x m) ∈ idealMod pp I`. Use `Submodule.subset_span ⟨g, X i ^ e, e, hg, pow_mem (X_mem_monos hi) e, hge, isHomogeneous_X_pow i e, ?_⟩` and prove the remaining obligations.

Clear the denominators using the available nonvanishing facts.
-/
theorem exists_isUnit_mul_mem_idealMod {I K : Chart x} (h : I.1 ⊆ K.1) {a : Ω}
    (ha : a ∈ idealMod pp K) :
    ∃ u : chartRing k x I, IsUnit (chartIncl h u) ∧ (u : Ω) * a ∈ idealMod pp I := by
  obtain ⟨g, m, e, hg, hm, hge, hme, rfl⟩ := idealMod_mem_form pp K ha
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have hm0 := eval_ne_zero_of_mem_monos K hm
  have hX0 : aeval x (X i ^ e : Poly k N) ≠ 0 := by
    rw [map_pow, aeval_X]; exact pow_ne_zero _ hxi
  refine ⟨⟨aeval x m / aeval x (X i ^ e), m, X i ^ e, e, pow_mem (X_mem_monos hi) e, hme,
    isHomogeneous_X_pow i e, rfl⟩, ?_, ?_⟩
  · rw [isUnit_iff_exists_inv]
    refine ⟨⟨aeval x (X i ^ e) / aeval x m, X i ^ e, m, e, hm, isHomogeneous_X_pow i e, hme, rfl⟩, ?_⟩
    apply Subtype.ext
    change aeval x m / aeval x (X i ^ e) * (aeval x (X i ^ e) / aeval x m) = 1
    field_simp
  · change aeval x m / aeval x (X i ^ e) * (aeval x g / aeval x m) ∈ idealMod pp I
    refine Submodule.subset_span ⟨g, X i ^ e, e, hg, pow_mem (X_mem_monos hi) e, hge,
      isHomogeneous_X_pow i e, ?_⟩
    field_simp

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨u, hu, hus⟩ : ∃ u : chartRing k x I, IsUnit (chartIncl h u) ∧ (u : Ω) * s ∈ idealMod pp I * L.sub I := by`. Use `Submodule.mul_induction_on (C := fun r => ∃ u : chartRing k x I, IsUnit (chartIncl h u) ∧ (u : Ω) * r ∈ idealMod pp I * L.sub I) hsK ?_ ?_` and prove the remaining obligations. Introduce `a ha l hl`. Take `⟨u₁, hu₁, h₁⟩` from `exists_isUnit_mul_mem_idealMod h ha`. Take `⟨u₂, hu₂, h₂⟩` from `(L.mem_iff I K h l).mp hl`.

Use `⟨u₁ * u₂, by rw [map_mul]; exact hu₁.mul hu₂, ?_⟩` and prove the remaining obligations. Establish `: ((u₁ * u₂ : chartRing k x I) : Ω) * (a * l) = ((u₁ : Ω) * a) * ((u₂ : Ω) • l)`. Simplify using `only [smul_eq_mul, MulMemClass.coe_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `Submodule.mul_mem_mul h₁ h₂`. Introduce and unpack `y₁ y₂ ⟨u₁, hu₁, h₁⟩ ⟨u₂, hu₂, h₂⟩`. Use `⟨u₁ * u₂, by rw [map_mul]; exact hu₁.mul hu₂, ?_⟩` and prove the remaining obligations. Establish `: ((u₁ * u₂ : chartRing k x I) : Ω) * (y₁ + y₂) = u₂ • ((u₁ : Ω) * y₁) + u₁ • ((u₂ : Ω) * y₂)`. Simplify using `only [chartRing_smul_def, MulMemClass.coe_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)`. Establish `hu' : (u : Ω) ∉ idealMod pp I`. Introduce `hmem`.

Establish `hK1 : (u : Ω) ∈ idealMod pp K` using `(idealSys x pp).mono I K h _ hmem`. Take `⟨v, hv⟩` from `hu`. Apply `one_not_mem_idealMod hW hle hK` to reduce the goal to its premises. Establish `hvu : ((↑v⁻¹ : chartRing k x K) : Ω) * (u : Ω) = 1`. Use `congrArg Subtype.val (Units.inv_mul v)` as an intermediate fact.

Rewrite `this` using `[hv]`. Conclude with `this`. Rewrite using `[← hvu, ← chartRing_smul_def]`. Conclude with `Submodule.smul_mem _ _ hK1`. Take `⟨L', hL'⟩` from `L.invertible I`.

Use `mem_of_mul_mem (L := 1) (L' := 1) (mul_one 1) hL' (idealMod_prime hW hle fun i hi => hK i (h hi)) (s := (u : Ω)) (Submodule.mem_one.mpr ⟨u, rfl⟩) (by rwa [mul_one]) hs (by rwa [one_mul])` and prove the remaining obligations.
-/
theorem mem_idealMod_mul_of_mem (L : LineBundle k x) (hW : pp.IsPrime) (hle : primeOf (S := k) x ≤ pp)
    {I K : Chart x} (h : I.1 ⊆ K.1) (hK : ∀ i ∈ K.1, (X i : Poly k N) ∉ pp) {s : Ω}
    (hs : s ∈ L.sub I) (hsK : s ∈ idealMod pp K * L.sub K) : s ∈ idealMod pp I * L.sub I := by
  obtain ⟨u, hu, hus⟩ : ∃ u : chartRing k x I, IsUnit (chartIncl h u) ∧
      (u : Ω) * s ∈ idealMod pp I * L.sub I := by
    refine Submodule.mul_induction_on (C := fun r => ∃ u : chartRing k x I, IsUnit (chartIncl h u) ∧
      (u : Ω) * r ∈ idealMod pp I * L.sub I) hsK ?_ ?_
    · intro a ha l hl
      obtain ⟨u₁, hu₁, h₁⟩ := exists_isUnit_mul_mem_idealMod h ha
      obtain ⟨u₂, hu₂, h₂⟩ := (L.mem_iff I K h l).mp hl
      refine ⟨u₁ * u₂, by rw [map_mul]; exact hu₁.mul hu₂, ?_⟩
      have : ((u₁ * u₂ : chartRing k x I) : Ω) * (a * l) = ((u₁ : Ω) * a) * ((u₂ : Ω) • l) := by
        simp only [smul_eq_mul, MulMemClass.coe_mul]; ring
      rw [this]
      exact Submodule.mul_mem_mul h₁ h₂
    · rintro y₁ y₂ ⟨u₁, hu₁, h₁⟩ ⟨u₂, hu₂, h₂⟩
      refine ⟨u₁ * u₂, by rw [map_mul]; exact hu₁.mul hu₂, ?_⟩
      have : ((u₁ * u₂ : chartRing k x I) : Ω) * (y₁ + y₂) =
          u₂ • ((u₁ : Ω) * y₁) + u₁ • ((u₂ : Ω) * y₂) := by
        simp only [chartRing_smul_def, MulMemClass.coe_mul]; ring
      rw [this]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
  have hu' : (u : Ω) ∉ idealMod pp I := by
    intro hmem
    have hK1 : (u : Ω) ∈ idealMod pp K := (idealSys x pp).mono I K h _ hmem
    obtain ⟨v, hv⟩ := hu
    apply one_not_mem_idealMod hW hle hK
    have hvu : ((↑v⁻¹ : chartRing k x K) : Ω) * (u : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul v)
      rw [hv] at this
      exact this
    rw [← hvu, ← chartRing_smul_def]
    exact Submodule.smul_mem _ _ hK1
  obtain ⟨L', hL'⟩ := L.invertible I
  refine mem_of_mul_mem (L := 1) (L' := 1) (mul_one 1) hL' (idealMod_prime hW hle fun i hi => hK i (h hi))
    (s := (u : Ω)) (Submodule.mem_one.mpr ⟨u, rfl⟩) (by rwa [mul_one]) hs (by rwa [one_mul])

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `one_not_mem_idealMod hW hle hI` to reduce the goal to its premises. Establish `hle' : G.sub I ≤ idealMod pp I * G.sub I`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Submodule.span_le]`. Introduce `t ht`. Conclude with `hcon t ht`. Take `⟨G', hG'⟩` from `hinv I`. Establish `h1 : (1 : Submodule (chartRing k x I) Ω) ≤ idealMod pp I`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `Submodule.one_le.mp h1`.
-/
theorem exists_sec_not_mem_of_generated (G : SubSystem k x Ω) (hG : G.Generated)
    (hinv : ∀ I, ∃ G' : Submodule (chartRing k x I) Ω, G.sub I * G' = 1) (hW : pp.IsPrime)
    (hle : primeOf (S := k) x ≤ pp) {I : Chart x} (hI : ∀ i ∈ I.1, (X i : Poly k N) ∉ pp) :
    ∃ t ∈ G.secs, t ∉ idealMod pp I * G.sub I := by
  by_contra hcon
  push Not at hcon
  apply one_not_mem_idealMod hW hle hI
  have hle' : G.sub I ≤ idealMod pp I * G.sub I := by
    calc G.sub I = Submodule.span _ (G.secs : Set Ω) := (hG I).symm
      _ ≤ _ := by
        rw [Submodule.span_le]
        intro t ht
        exact hcon t ht
  obtain ⟨G', hG'⟩ := hinv I
  have h1 : (1 : Submodule (chartRing k x I) Ω) ≤ idealMod pp I := by
    calc (1 : Submodule (chartRing k x I) Ω) = G.sub I * G' := hG'.symm
      _ ≤ idealMod pp I * G.sub I * G' := mul_le_mul' hle' le_rfl
      _ = idealMod pp I := by rw [mul_assoc, hG', mul_one]
  exact Submodule.one_le.mp h1

end Ideal

section CechMap

variable {n : ℕ} {U : Finset (Fin n)} {R : Type*} [CommRing R]
  {G G' : Cell U → Type*} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
  [∀ I, AddCommGroup (G' I)] [∀ I, Module R (G' I)]
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J} {ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G' I →ₗ[R] G' J}

def cechZeroCocycleMap (φ : ∀ I, G I →ₗ[R] G' I) (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m)) :
    LinearMap.ker (Cech.d G ρ 0) →ₗ[R] LinearMap.ker (Cech.d G' ρ' 0) :=
  (Cech.mapC φ 0).restrict fun s hs => by
    rw [LinearMap.mem_ker] at hs ⊢
    rw [← Cech.mapC_d φ hφ, hs, map_zero]

def cechH0Map (φ : ∀ I, G I →ₗ[R] G' I) (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m)) :
    Cech.H G ρ 0 →ₗ[R] Cech.H G' ρ' 0 :=
  Submodule.mapQ _ _ (cechZeroCocycleMap φ hφ)
    (by
      intro s hs
      change (s : Cech.Cochain G 0) ∈ (⊥ : Submodule R _) at hs
      rw [Submodule.mem_bot] at hs
      change (Cech.mapC φ 0 s : Cech.Cochain G' 0) ∈ (⊥ : Submodule R _)
      rw [hs, map_zero]; exact Submodule.zero_mem _)

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `z hz`. Take `⟨s, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`. Establish `hz' : cechZeroCocycleMap φ hφ s ∈ (Cech.bdry G' ρ' 0).comap (LinearMap.ker (Cech.d G' ρ' 0)).subtype` using `(Submodule.Quotient.mk_eq_zero _).mp hz`. Express the relevant statement in the definitionally equal form `_ = (0 : Cech.H G ρ 0)`.

Rewrite using `[show (0 : Cech.H G ρ 0) = Submodule.Quotient.mk 0 from rfl]`. Apply `congrArg` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(Cech.mapC φ 0 (s : Cech.Cochain G 0)) ∈ (⊥ : Submodule R (Cech.Cochain G' 0)) at hz'`. Express the relevant statement in the definitionally equal form `(s : Cech.Cochain G 0) = 0`.

Express the relevant statement in the definitionally equal form `(s : Cech.Cochain G 0) ∈ (⊥ : Submodule R (Cech.Cochain G 0))`. Rewrite `hz'` using `[Submodule.mem_bot]`. Use function extensionality and compare the values at `I`. Establish `h1` using `congrFun hz' I`. Express the relevant statement in the definitionally equal form `φ I.1 ((s : Cech.Cochain G 0) I) = 0 at h1`.

Conclude with `hinj I (h1.trans (map_zero _).symm)`.
-/
theorem cechH0Map_injective (φ : ∀ I, G I →ₗ[R] G' I) (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m))
    (hinj : ∀ I : Cech.Idx U 0, Function.Injective (φ I.1)) : Function.Injective (cechH0Map φ hφ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hz' : cechZeroCocycleMap φ hφ s ∈ (Cech.bdry G' ρ' 0).comap (LinearMap.ker (Cech.d G' ρ' 0)).subtype :=
    (Submodule.Quotient.mk_eq_zero _).mp hz
  change _ = (0 : Cech.H G ρ 0)
  rw [show (0 : Cech.H G ρ 0) = Submodule.Quotient.mk 0 from rfl]
  apply congrArg
  apply Subtype.ext
  change (Cech.mapC φ 0 (s : Cech.Cochain G 0)) ∈ (⊥ : Submodule R (Cech.Cochain G' 0)) at hz'
  change (s : Cech.Cochain G 0) = 0
  change (s : Cech.Cochain G 0) ∈ (⊥ : Submodule R (Cech.Cochain G 0))
  rw [Submodule.mem_bot] at hz'
  funext I
  have h1 := congrFun hz' I
  change φ I.1 ((s : Cech.Cochain G 0) I) = 0 at h1
  exact hinj I (h1.trans (map_zero _).symm)

end CechMap

section QuotMul

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

def quotMul (F₁ G₁ F₂ G₂ : SubSystem k x Ω) (s : Ω) (hF : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ F₂.sub I)
    (hG : ∀ I, ∀ y ∈ F₁.sub I, y ∈ G₁.sub I → s * y ∈ G₂.sub I) (I : Chart x) :
    (F₁.sub I ⧸ SubSystem.quotSub F₁ G₁ I) →ₗ[k] (F₂.sub I ⧸ SubSystem.quotSub F₂ G₂ I) :=
  (SubSystem.quotSub F₁ G₁ I).mapQ (SubSystem.quotSub F₂ G₂ I)
    { toFun := fun y => ⟨s * y, hF I y y.2⟩
      map_add' := fun a b => Subtype.ext (mul_add s a b)
      map_smul' := fun c a => Subtype.ext (mul_smul_comm c s (a : Ω)) }
    (fun y hy => hG I y y.2 hy)

/- English proof (translation)
Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ m`. Both sides reduce to the same expression.
-/
theorem quotMul_res (F₁ G₁ F₂ G₂ : SubSystem k x Ω) (s : Ω) (hF : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ F₂.sub I)
    (hG : ∀ I, ∀ y ∈ F₁.sub I, y ∈ G₁.sub I → s * y ∈ G₂.sub I) (I J : Chart x) (h : I.1 ⊆ J.1)
    (m : F₁.sub I ⧸ SubSystem.quotSub F₁ G₁ I) :
    quotMul F₁ G₁ F₂ G₂ s hF hG J (SubSystem.quotRes F₁ G₁ I J h m) =
      SubSystem.quotRes F₂ G₂ I J h (quotMul F₁ G₁ F₂ G₂ s hF hG I m) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rfl

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `z hz`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`. Establish `hz' : (⟨s * y, hF I y y.2⟩ : F₂.sub I) ∈ SubSystem.quotSub F₂ G₂ I` using `(Submodule.Quotient.mk_eq_zero _).mp hz`. Conclude with `(Submodule.Quotient.mk_eq_zero _).mpr (hinj y y.2 hz')`.
-/
theorem quotMul_injective (F₁ G₁ F₂ G₂ : SubSystem k x Ω) (s : Ω)
    (hF : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ F₂.sub I)
    (hG : ∀ I, ∀ y ∈ F₁.sub I, y ∈ G₁.sub I → s * y ∈ G₂.sub I) (I : Chart x)
    (hinj : ∀ y ∈ F₁.sub I, s * y ∈ G₂.sub I → y ∈ G₁.sub I) :
    Function.Injective (quotMul F₁ G₁ F₂ G₂ s hF hG I) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hz' : (⟨s * y, hF I y y.2⟩ : F₂.sub I) ∈ SubSystem.quotSub F₂ G₂ I :=
    (Submodule.Quotient.mk_eq_zero _).mp hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr (hinj y y.2 hz')

/- English proof (translation)
The claim follows from `LinearMap.finrank_le_finrank_of_injective (cechH0Map_injective (quotMul F₁ G₁ F₂ G₂ s hF hG) (quotMul_res F₁ G₁ F₂ G₂ s hF hG) fun I => quotMul_injective F₁ G₁ F₂ G₂ s hF hG I.1 (hinj I.1))`.
-/
theorem finrank_quotH_le (F₁ G₁ F₂ G₂ : SubSystem k x Ω) (s : Ω)
    (hF : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ F₂.sub I)
    (hG : ∀ I, ∀ y ∈ F₁.sub I, y ∈ G₁.sub I → s * y ∈ G₂.sub I)
    (hinj : ∀ I : Chart x, ∀ y ∈ F₁.sub I, s * y ∈ G₂.sub I → y ∈ G₁.sub I)
    [Module.Finite k (SubSystem.quotH F₂ G₂ 0)] :
    Module.finrank k (SubSystem.quotH F₁ G₁ 0) ≤ Module.finrank k (SubSystem.quotH F₂ G₂ 0) :=
  LinearMap.finrank_le_finrank_of_injective
    (cechH0Map_injective (quotMul F₁ G₁ F₂ G₂ s hF hG) (quotMul_res F₁ G₁ F₂ G₂ s hF hG)
      fun I => quotMul_injective F₁ G₁ F₂ G₂ s hF hG I.1 (hinj I.1))

end QuotMul

section Main

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

def ampleDataOfVeryAmple (H : LineBundle k x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hH : IsVeryAmpleBy H.toSubSystem h) : AmpleData k x H where
  m := 1
  m_pos := one_pos
  r := r
  h := h
  mem_secs j := by
    rw [show H.toSubSystem.pow 1 = H.toSubSystem from twistSys_zero_twist _]
    exact hH.mem_secs j
  generates I := by
    rw [show H.toSubSystem.pow 1 = H.toSubSystem from twistSys_zero_twist _]
    exact hH.generates I
  finite j hj := ⟨{1}, fun a ha => by
    have hb := hH.closed j hj ha
    rw [Finset.coe_singleton]
    exact Submodule.mem_span_singleton.mpr ⟨⟨a, hb⟩, by
      rw [Subalgebra.smul_def, smul_eq_mul, mul_one]⟩⟩
  affine j hj := hH.affine j hj

/- English proof (translation)
Take `⟨i, hi⟩` from `I.2.1`. Express the relevant statement in the definitionally equal form `twistMod k x 0 I = 1`. Rewrite using `[twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]`.
-/
theorem twistSys_sub_zero (I : Chart x) : (twistSys k x 0).sub I = 1 := by
  obtain ⟨i, hi⟩ := I.2.1
  change twistMod k x 0 I = 1
  rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨X j ^ m, 1, 0, m, one_mem _, isHomogeneous_X_pow j m, isHomogeneous_one _ _, by simp, by simp⟩`.
-/
theorem pow_mem_twistSys (j : Fin (N + 1)) (m : ℕ) (I : Chart x) :
    x j ^ m ∈ (twistSys k x (m : ℤ)).sub I :=
  Submodule.subset_span ⟨X j ^ m, 1, 0, m, one_mem _, isHomogeneous_X_pow j m, isHomogeneous_one _ _,
    by simp, by simp⟩

end Main

/- English proof (translation)
Introduce `k _ Ω _ _ N x Nb b pp e c hN hW`. Establish `hP` using `hW.isPrime`. Take `⟨r, hh, hhN⟩` from `hN`. Take `⟨c₀, hc₀⟩` from `hGA k Ω N x Nb (ampleDataOfVeryAmple Nb hhN) (twistBundle k x (-c))`. Set `GB : LineBundle k x` to `(twistBundle k x (-c)).tensorProd (Nb.powBundle c₀)`.

Establish `hGBs : GB.toSubSystem = (twistSys k x (-c)).twist (Nb.toSubSystem.pow c₀)`. Express the relevant statement in the definitionally equal form `(twistSys k x (-c)).twist (Nb.powBundle c₀).toSubSystem = _`. Rewrite using `[LineBundle.powBundle_toSubSystem]`. Establish `hGgen : GB.toSubSystem.Generated` using `by rw [hGBs]; exact hc₀ c₀ le_rfl`. Take `⟨i₀, hi₀⟩` from `hW.relevant`.

Establish `hxi₀ : x i₀ ≠ 0`. Introduce `h0`. Conclude with `hi₀ (hW.le ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i₀)).mpr (by`. Rewrite using `[aeval_X]`. Conclude with `h0)))`.

Set `I₀ : Chart x` to `singleChart hxi₀`. Establish `hI₀ : ∀ i ∈ I₀.1, (X i : Poly k N) ∉ pp` using `fun i hi => by`. Rewrite using `[Finset.mem_singleton.mp hi]`. Conclude with `hi₀`. Take `⟨t, ht, htI₀⟩` from `exists_sec_not_mem_of_generated GB.toSubSystem hGgen GB.invertible hP hW.le hI₀`.

Establish `htI : ∀ I, t ∈ GB.sub I` using `fun I => (Submodule.mem_iInf _).mp ht I`. Use `⟨c₀, fun n i => ?_⟩` and prove the remaining obligations. Take `⟨L2, hL2⟩` from `exists_lineBundle_twistMul Nb (n + c₀) 0`. Establish `hfin : Module.Finite k (SubSystem.quotH (twistMul Nb.toSubSystem (n + c₀) 0) ((twistMul Nb.toSubSystem (n + c₀) 0).twist (idealSys x pp)) 0)`. Rewrite using `[← hL2]`.

Conclude with `hFin k Ω N x L2 pp`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Take `⟨L1, hL1⟩` from `exists_lineBundle_twistMul Nb n (-((i : ℤ) * b))`. Set `F1B : LineBundle k x` to `L1.tensorProd (twistBundle k x c)`. Establish `hF1B : F1B.toSubSystem = (twistMul Nb.toSubSystem n (-((i : ℤ) * b))).twist (twistSys k x c)`.

Express the relevant statement in the definitionally equal form `L1.toSubSystem.twist (twistSys k x c) = _`. Rewrite using `[hL1]`. Set `LB : LineBundle k x` to `(twistBundle k x ((i : ℤ) * b)).tensorProd GB`. Establish `hcast : (((i * b : ℕ)) : ℤ) = (i : ℤ) * b` using `by push_cast; ring`. Establish `hLBsub : ∀ I, LB.sub I = GB.sub I * (twistSys k x ((i : ℤ) * b)).sub I` using `fun I => SubSystem.twist_sub_eq_mul_sub (twistSys k x ((i : ℤ) * b)) GB.toSubSystem I`.

Establish `hGBsub : ∀ I, GB.sub I = Nb.sub I ^ c₀ * (twistSys k x (-c)).sub I` using `fun I => by`. Rewrite using `[show GB.sub I = GB.toSubSystem.sub I from rfl, hGBs, SubSystem.twist_sub_eq_mul_sub, SubSystem.pow_sub]`. Set `s : Ω` to `x i₀ ^ (i * b) * t`. Establish `hsI : ∀ I, s ∈ LB.sub I` using `fun I => by`. Rewrite using `[hLBsub, mul_comm (GB.sub I)]`.

Use `pow_mem_twistSys (k := k) i₀ (i * b) I` as an intermediate fact. Rewrite `this` using `[hcast]`. Conclude with `Submodule.mul_mem_mul this (htI I)`. Establish `hsI₀ : s ∉ idealMod pp I₀ * LB.sub I₀`. Introduce `hs`.

Establish `hneg : x i₀ ^ (-((i : ℤ) * b)) ∈ (twistSys k x (-((i : ℤ) * b))).sub I₀`. Express the relevant statement in the definitionally equal form `_ ∈ twistMod k x _ I₀`. Rewrite using `[twistMod_eq_span _ I₀ (Finset.mem_singleton_self i₀)]`. Conclude with `Submodule.mem_span_singleton_self _`. Establish `h1` using `Submodule.mul_mem_mul hneg hs`.

Establish `hst : x i₀ ^ (-((i : ℤ) * b)) * s = t`. Express the relevant statement in the definitionally equal form `x i₀ ^ (-((i : ℤ) * b)) * (x i₀ ^ (i * b) * t) = t`. Rewrite using `[← mul_assoc, ← hcast, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hxi₀), one_mul]`. Rewrite `h1` using `[hst, hLBsub, show (twistSys k x (-((i : ℤ) * b))).sub I₀ * (idealMod pp I₀ * (GB.sub I₀ * (twistSys k x ((i : ℤ) * b)).sub I₀)) = idealMod pp I₀ * GB.sub I₀ * ((twistSys k x ((i : ℤ) * b)).sub I₀ * (twistSys k x (-((i : ℤ) * b))).sub I₀) by ring, twistSys_sub_mul, add_neg_cancel …`. Conclude with `htI₀ h1`.

Establish `hprod : ∀ I, LB.sub I * F1B.sub I = (twistMul Nb.toSubSystem (n + c₀) 0).sub I` using `fun I => by`. Rewrite using `[show F1B.sub I = F1B.toSubSystem.sub I from rfl, hF1B, SubSystem.twist_sub_eq_mul_sub, twistMul_sub, twistMul_sub, hLBsub, hGBsub, twistSys_sub_zero, one_mul]`. Rewrite using `[show Nb.sub I ^ c₀ * (twistSys k x (-c)).sub I * (twistSys k x ((i : ℤ) * b)).sub I * ((twistSys k x c).sub I * ((twistSys k x (-((i : ℤ) * b))).sub I * Nb.sub I ^ n)) = ((twistSys k x (-c)).sub I * (twistSys k x c).sub I) * ((twistSys k x ((i : ℤ) * b)).sub I * (twistSys k x (- …`. Use `finrank_quotH_le _ _ _ _ s (fun I y hy => ?_) (fun I y hy hyG => ?_) (fun I y hy hsy => ?_)` and prove the remaining obligations. Rewrite `*` using `[← hprod I, ← hF1B]`.

Conclude with `Submodule.mul_mem_mul (hsI I) hy`. Rewrite `hyG`, the goal using `[SubSystem.twist_sub_eq_mul_sub]`. Express the relevant statement in the definitionally equal form `s * y ∈ idealMod pp I * (twistMul Nb.toSubSystem (n + c₀) 0).sub I`. Rewrite using `[← hprod I, mul_left_comm]`. Rewrite `hyG` using `[← hF1B]`.

Conclude with `Submodule.mul_mem_mul (hsI I) hyG`. Rewrite `hsy`, the goal using `[SubSystem.twist_sub_eq_mul_sub]`. Express the relevant statement in the definitionally equal form `s * y ∈ idealMod pp I * (twistMul Nb.toSubSystem (n + c₀) 0).sub I at hsy`. Rewrite `hsy` using `[← hprod I]`. Rewrite `hy`, the goal using `[← hF1B]`.

Distinguish the cases in `hcase : ∀ j ∈ I.1, (X j : Poly k N) ∉ pp`. Take `⟨LB', hLB'⟩` from `LB.invertible I`. Take `⟨F1', hF1'⟩` from `F1B.invertible I`. Use `mem_of_mul_mem hLB' hF1' (idealMod_prime hP hW.le hcase) (hsI I) ?_ hy hsy` and prove the remaining obligations. Introduce `hsW`.

Set `K : Chart x` to `⟨I₀.1 ∪ I.1, I.2.1.mono Finset.subset_union_right, Finset.union_subset I₀.2.2 I.2.2⟩`. Establish `hK : ∀ j ∈ K.1, (X j : Poly k N) ∉ pp` using `fun j hj => by`. Break down `Finset.mem_union.mp hj with hj | hj` into its components or cases. Conclude with `hI₀ j hj`. Conclude with `hcase j hj`.

Establish `hsK : s ∈ idealMod pp K * LB.sub K`. Use `(LB.toSubSystem.twist (idealSys x pp)).mono I K Finset.subset_union_right s (by rw [SubSystem.twist_sub_eq_mul_sub]; exact hsW)` as an intermediate fact. Rewrite `this` using `[SubSystem.twist_sub_eq_mul_sub]`. Then use the resulting hypothesis. Conclude with `hsI₀ (mem_idealMod_mul_of_mem LB hP hW.le Finset.subset_union_left hK (hsI I₀) hsK)`. Use `push Not at hcase`.

Take `⟨j, hj, hjp⟩` from `hcase`. Rewrite using `[← one_mul y]`. Conclude with `Submodule.mul_mem_mul (one_mem_idealMod hj hjp) hy`.
-/
theorem proof (hGA : GeneratedAmple.Statement.{u, w}) (hFin : QuotSectionsFinite.Statement.{u, w}) :
    SectionCount.Drop.Term.Statement.{u, w} := by
  intro k _ Ω _ _ N x Nb b pp e c hN hW
  have hP := hW.isPrime
  obtain ⟨r, hh, hhN⟩ := hN
  obtain ⟨c₀, hc₀⟩ := hGA k Ω N x Nb (ampleDataOfVeryAmple Nb hhN) (twistBundle k x (-c))

  let GB : LineBundle k x := (twistBundle k x (-c)).tensorProd (Nb.powBundle c₀)
  have hGBs : GB.toSubSystem = (twistSys k x (-c)).twist (Nb.toSubSystem.pow c₀) := by
    change (twistSys k x (-c)).twist (Nb.powBundle c₀).toSubSystem = _
    rw [LineBundle.powBundle_toSubSystem]
  have hGgen : GB.toSubSystem.Generated := by rw [hGBs]; exact hc₀ c₀ le_rfl

  obtain ⟨i₀, hi₀⟩ := hW.relevant
  have hxi₀ : x i₀ ≠ 0 := by
    intro h0
    exact hi₀ (hW.le ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i₀)).mpr (by
      rw [aeval_X]; exact h0)))
  let I₀ : Chart x := singleChart hxi₀
  have hI₀ : ∀ i ∈ I₀.1, (X i : Poly k N) ∉ pp := fun i hi => by
    rw [Finset.mem_singleton.mp hi]; exact hi₀
  obtain ⟨t, ht, htI₀⟩ := exists_sec_not_mem_of_generated GB.toSubSystem hGgen GB.invertible hP hW.le hI₀
  have htI : ∀ I, t ∈ GB.sub I := fun I => (Submodule.mem_iInf _).mp ht I
  refine ⟨c₀, fun n i => ?_⟩

  obtain ⟨L2, hL2⟩ := exists_lineBundle_twistMul Nb (n + c₀) 0
  have hfin : Module.Finite k (SubSystem.quotH (twistMul Nb.toSubSystem (n + c₀) 0)
      ((twistMul Nb.toSubSystem (n + c₀) 0).twist (idealSys x pp)) 0) := by
    rw [← hL2]; exact hFin k Ω N x L2 pp
  refine ⟨hfin, ?_⟩

  obtain ⟨L1, hL1⟩ := exists_lineBundle_twistMul Nb n (-((i : ℤ) * b))
  let F1B : LineBundle k x := L1.tensorProd (twistBundle k x c)
  have hF1B : F1B.toSubSystem = (twistMul Nb.toSubSystem n (-((i : ℤ) * b))).twist (twistSys k x c) := by
    change L1.toSubSystem.twist (twistSys k x c) = _
    rw [hL1]

  let LB : LineBundle k x := (twistBundle k x ((i : ℤ) * b)).tensorProd GB
  have hcast : (((i * b : ℕ)) : ℤ) = (i : ℤ) * b := by push_cast; ring
  have hLBsub : ∀ I, LB.sub I = GB.sub I * (twistSys k x ((i : ℤ) * b)).sub I := fun I =>
    SubSystem.twist_sub_eq_mul_sub (twistSys k x ((i : ℤ) * b)) GB.toSubSystem I
  have hGBsub : ∀ I, GB.sub I = Nb.sub I ^ c₀ * (twistSys k x (-c)).sub I := fun I => by
    rw [show GB.sub I = GB.toSubSystem.sub I from rfl, hGBs, SubSystem.twist_sub_eq_mul_sub,
      SubSystem.pow_sub]
  let s : Ω := x i₀ ^ (i * b) * t
  have hsI : ∀ I, s ∈ LB.sub I := fun I => by
    rw [hLBsub, mul_comm (GB.sub I)]
    have := pow_mem_twistSys (k := k) i₀ (i * b) I
    rw [hcast] at this
    exact Submodule.mul_mem_mul this (htI I)

  have hsI₀ : s ∉ idealMod pp I₀ * LB.sub I₀ := by
    intro hs
    have hneg : x i₀ ^ (-((i : ℤ) * b)) ∈ (twistSys k x (-((i : ℤ) * b))).sub I₀ := by
      change _ ∈ twistMod k x _ I₀
      rw [twistMod_eq_span _ I₀ (Finset.mem_singleton_self i₀)]
      exact Submodule.mem_span_singleton_self _
    have h1 := Submodule.mul_mem_mul hneg hs
    have hst : x i₀ ^ (-((i : ℤ) * b)) * s = t := by
      change x i₀ ^ (-((i : ℤ) * b)) * (x i₀ ^ (i * b) * t) = t
      rw [← mul_assoc, ← hcast, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hxi₀), one_mul]
    rw [hst, hLBsub, show (twistSys k x (-((i : ℤ) * b))).sub I₀ * (idealMod pp I₀ * (GB.sub I₀ *
        (twistSys k x ((i : ℤ) * b)).sub I₀)) = idealMod pp I₀ * GB.sub I₀ *
        ((twistSys k x ((i : ℤ) * b)).sub I₀ * (twistSys k x (-((i : ℤ) * b))).sub I₀) by ring,
      twistSys_sub_mul, add_neg_cancel, twistSys_sub_zero, mul_one] at h1
    exact htI₀ h1

  have hprod : ∀ I, LB.sub I * F1B.sub I = (twistMul Nb.toSubSystem (n + c₀) 0).sub I := fun I => by
    rw [show F1B.sub I = F1B.toSubSystem.sub I from rfl, hF1B, SubSystem.twist_sub_eq_mul_sub,
      twistMul_sub, twistMul_sub, hLBsub, hGBsub, twistSys_sub_zero, one_mul]
    rw [show Nb.sub I ^ c₀ * (twistSys k x (-c)).sub I * (twistSys k x ((i : ℤ) * b)).sub I *
        ((twistSys k x c).sub I * ((twistSys k x (-((i : ℤ) * b))).sub I * Nb.sub I ^ n)) =
        ((twistSys k x (-c)).sub I * (twistSys k x c).sub I) *
        ((twistSys k x ((i : ℤ) * b)).sub I * (twistSys k x (-((i : ℤ) * b))).sub I) *
        (Nb.sub I ^ n * Nb.sub I ^ c₀) by ring,
      twistSys_sub_mul, twistSys_sub_mul, neg_add_cancel, add_neg_cancel, twistSys_sub_zero, ← pow_add,
      one_mul, one_mul]

  refine finrank_quotH_le _ _ _ _ s (fun I y hy => ?_) (fun I y hy hyG => ?_) (fun I y hy hsy => ?_)
  · rw [← hprod I, ← hF1B] at *
    exact Submodule.mul_mem_mul (hsI I) hy
  · rw [SubSystem.twist_sub_eq_mul_sub] at hyG ⊢
    change s * y ∈ idealMod pp I * (twistMul Nb.toSubSystem (n + c₀) 0).sub I
    rw [← hprod I, mul_left_comm]
    rw [← hF1B] at hyG
    exact Submodule.mul_mem_mul (hsI I) hyG
  · rw [SubSystem.twist_sub_eq_mul_sub] at hsy ⊢
    change s * y ∈ idealMod pp I * (twistMul Nb.toSubSystem (n + c₀) 0).sub I at hsy
    rw [← hprod I] at hsy
    rw [← hF1B] at hy ⊢
    by_cases hcase : ∀ j ∈ I.1, (X j : Poly k N) ∉ pp
    ·
      obtain ⟨LB', hLB'⟩ := LB.invertible I
      obtain ⟨F1', hF1'⟩ := F1B.invertible I
      refine mem_of_mul_mem hLB' hF1' (idealMod_prime hP hW.le hcase) (hsI I) ?_ hy hsy
      intro hsW
      let K : Chart x := ⟨I₀.1 ∪ I.1, I.2.1.mono Finset.subset_union_right,
        Finset.union_subset I₀.2.2 I.2.2⟩
      have hK : ∀ j ∈ K.1, (X j : Poly k N) ∉ pp := fun j hj => by
        rcases Finset.mem_union.mp hj with hj | hj
        · exact hI₀ j hj
        · exact hcase j hj
      have hsK : s ∈ idealMod pp K * LB.sub K := by
        have := (LB.toSubSystem.twist (idealSys x pp)).mono I K Finset.subset_union_right s
          (by rw [SubSystem.twist_sub_eq_mul_sub]; exact hsW)
        rwa [SubSystem.twist_sub_eq_mul_sub] at this
      exact hsI₀ (mem_idealMod_mul_of_mem LB hP hW.le Finset.subset_union_left hK (hsI I₀) hsK)
    ·
      push Not at hcase
      obtain ⟨j, hj, hjp⟩ := hcase
      rw [← one_mul y]
      exact Submodule.mul_mem_mul (one_mem_idealMod hj hjp) hy

end SectionCount.Drop.Term

end

end GroundTheory.Heights₂.Heights.Kleiman
