import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OpIsDVR
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.KTFiniteDimensional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValNorm

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField IsLocalRing

namespace NPA

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K : Type} [Field K] [NumberField K] (D N : ℕ)
  (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

/- English proof (translation)
Unfold `OpToKT`. Conclude with `IsLocalization.lift_comp _`.
-/
theorem opToKT_comp : (OpToKT D N la).comp (algebraMap (OT K D N) (Op D N la)) =
    (algebraMap (KTp K D N) (KTf K D N)).comp (OTtoKT K D N) := by
  unfold OpToKT
  exact IsLocalization.lift_comp _

/- English proof (translation)
Conclude with `RingHom.congr_fun (opToKT_comp D N la) a`.
-/
theorem opToKT_alg (a : OT K D N) : OpToKT D N la (algebraMap (OT K D N) (Op D N la) a) =
    algebraMap (KTp K D N) (KTf K D N) (OTtoKT K D N a) := by
  exact RingHom.congr_fun (opToKT_comp D N la) a

/- English proof (translation)
Unfold `OTtoKT`. Conclude with `MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K)`.
-/
theorem oTtoKT_injective : Function.Injective (OTtoKT K D N) := by
  unfold OTtoKT
  exact MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K)

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (laT D N la).primeCompl x`. Unfold `OpToKT at hx`. Rewrite `hx` using `[IsLocalization.lift_mk'_spec, mul_zero, RingHom.comp_apply]`.

Establish `h2 : OTtoKT K D N a = 0` using `(injective_iff_map_eq_zero _).mp (IsFractionRing.injective (KTp K D N) (KTf K D N)) _ hx`. Establish `h3 : a = 0` using `(injective_iff_map_eq_zero _).mp (oTtoKT_injective D N) _ h2`. Substitute `h3` using the available equality. Conclude with `IsLocalization.mk'_zero _`.
-/
theorem opToKT_injective : Function.Injective (OpToKT D N la) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (laT D N la).primeCompl x
  unfold OpToKT at hx
  rw [IsLocalization.lift_mk'_spec, mul_zero, RingHom.comp_apply] at hx
  have h2 : OTtoKT K D N a = 0 :=
    (injective_iff_map_eq_zero _).mp (IsFractionRing.injective (KTp K D N) (KTf K D N)) _ hx
  have h3 : a = 0 := (injective_iff_map_eq_zero _).mp (oTtoKT_injective D N) _ h2
  subst h3
  exact IsLocalization.mk'_zero _

/- English proof (translation)
Use `letI := (OpToKT D N la).toAlgebra`. Establish `hinj : Function.Injective (algebraMap (Op D N la) (KTf K D N))` using `opToKT_injective D N la`. Establish `hC : ∀ s : 𝓞 K, OTtoKT K D N (MvPolynomial.C s) = MvPolynomial.C (algebraMap (𝓞 K) K s)` using `fun s => MvPolynomial.map_C _ _`. Establish `hX : ∀ i, OTtoKT K D N (MvPolynomial.X i) = MvPolynomial.X i` using `fun i => MvPolynomial.map_X _ _`. Establish `hcl : ∀ p : KTp K D N, ∃ s : 𝓞 K, s ≠ 0 ∧ ∃ p' : OT K D N, OTtoKT K D N p' = MvPolynomial.C (algebraMap (𝓞 K) K s) * p`.

Introduce `p`. Proceed by induction on `p using MvPolynomial.induction_on`. Use `next a =>`. Take `⟨x, y, hy, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 K) a`. Establish `hy' : algebraMap (𝓞 K) K y ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy`.

Use `⟨y, nonZeroDivisors.ne_zero hy, MvPolynomial.C x, ?_⟩` and prove the remaining obligations. Rewrite using `[hC, ← MvPolynomial.C_mul]`. Use `congr 1`. Use `first`. Consider the case `(field_simp; done)`.

Consider the case `(rw [mul_div_assoc', mul_div_cancel_left₀ _ hy'])`. Consider the case `(field_simp; ring)`. Use `next p q hp hq =>`. Take `⟨s1, hs1, p1, hp1⟩` from `hp`. Take `⟨s2, hs2, q1, hq1⟩` from `hq`.

Use `⟨s1 * s2, mul_ne_zero hs1 hs2, MvPolynomial.C s2 * p1 + MvPolynomial.C s1 * q1, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, hp1, hq1, hC, hC, map_mul (algebraMap (𝓞 K) K), MvPolynomial.C_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `next p i hp =>`. Take `⟨s, hs, p1, hp1⟩` from `hp`.

Conclude with `⟨s, hs, p1 * MvPolynomial.X i, by rw [map_mul, hp1, hX, mul_assoc]⟩`. Establish `hCne : ∀ s : 𝓞 K, s ≠ 0 → algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.C (algebraMap (𝓞 K) K s)) ≠ 0`. Introduce `s hs`. Rewrite using `[ne_eq, IsFractionRing.to_map_eq_zero_iff, MvPolynomial.C_eq_zero]`. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hs`.

Establish `hOp : ∀ a : OT K D N, algebraMap (Op D N la) (KTf K D N) (algebraMap (OT K D N) (Op D N la) a) = algebraMap (KTp K D N) (KTf K D N) (OTtoKT K D N a)` using `opToKT_alg D N la`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩`. Conclude with `IsUnit.mk0 _ ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hy))`. Introduce `z`.

Take `⟨p, q, hq, rfl⟩` from `IsFractionRing.div_surjective (A := KTp K D N) z`. Take `⟨sp, hsp, p', hp'⟩` from `hcl p`. Take `⟨sq, hsq, q', hq'⟩` from `hcl q`. Establish `hq0 : algebraMap (KTp K D N) (KTf K D N) q ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq`. Establish `e1 : algebraMap (Op D N la) (KTf K D N) (algebraMap (OT K D N) (Op D N la) (p' * MvPolynomial.C sq)) = algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.C (algebraMap (𝓞 K) K sp)) * algebraMap (KTp K D N) (KTf K D N) p * algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.C (algebraM …`.

Rewrite using `[hOp, map_mul, hp', hC, map_mul, map_mul]`. Establish `e2 : algebraMap (Op D N la) (KTf K D N) (algebraMap (OT K D N) (Op D N la) (q' * MvPolynomial.C sp)) = algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.C (algebraMap (𝓞 K) K sq)) * algebraMap (KTp K D N) (KTf K D N) q * algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.C (algebraM …`. Rewrite using `[hOp, map_mul, hq', hC, map_mul, map_mul]`. Establish `hx2 : algebraMap (OT K D N) (Op D N la) (q' * MvPolynomial.C sp) ≠ 0` using `(map_ne_zero_iff _ hinj).mp (by`. Rewrite using `[e2]`.

Conclude with `mul_ne_zero (mul_ne_zero (hCne sq hsq) hq0) (hCne sp hsp))`. Use `⟨⟨algebraMap (OT K D N) (Op D N la) (p' * MvPolynomial.C sq), ⟨_, mem_nonZeroDivisors_of_ne_zero hx2⟩⟩, ?_⟩` and prove the remaining obligations. Use `show _ * algebraMap (Op D N la) (KTf K D N) (algebraMap (OT K D N) (Op D N la) (q' * MvPolynomial.C sp)) = _`. Rewrite using `[e1, e2]`. Establish `h1` using `hCne sq hsq`.

Establish `h2` using `hCne sp hsp`. Use `first`. Consider the case `(field_simp; done)`. Consider the case `(field_simp; ring)`. Consider the case `(rw [div_mul_eq_mul_div, div_eq_iff hq0]; ring)`.

Introduce `x y hxy`. Conclude with `⟨1, by rw [hinj hxy]⟩`.
-/
theorem op_isFractionRing :
    letI := (OpToKT D N la).toAlgebra
    IsFractionRing (Op D N la) (KTf K D N) := by
  letI := (OpToKT D N la).toAlgebra
  have hinj : Function.Injective (algebraMap (Op D N la) (KTf K D N)) := opToKT_injective D N la
  have hC : ∀ s : 𝓞 K, OTtoKT K D N (MvPolynomial.C s) = MvPolynomial.C (algebraMap (𝓞 K) K s) :=
    fun s => MvPolynomial.map_C _ _
  have hX : ∀ i, OTtoKT K D N (MvPolynomial.X i) = MvPolynomial.X i :=
    fun i => MvPolynomial.map_X _ _
  have hcl : ∀ p : KTp K D N, ∃ s : 𝓞 K, s ≠ 0 ∧ ∃ p' : OT K D N,
      OTtoKT K D N p' = MvPolynomial.C (algebraMap (𝓞 K) K s) * p := by
    intro p
    induction p using MvPolynomial.induction_on
    next a =>
      obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
      have hy' : algebraMap (𝓞 K) K y ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
      refine ⟨y, nonZeroDivisors.ne_zero hy, MvPolynomial.C x, ?_⟩
      rw [hC, ← MvPolynomial.C_mul]
      congr 1
      first
        | (field_simp; done)
        | (rw [mul_div_assoc', mul_div_cancel_left₀ _ hy'])
        | (field_simp; ring)
    next p q hp hq =>
      obtain ⟨s1, hs1, p1, hp1⟩ := hp
      obtain ⟨s2, hs2, q1, hq1⟩ := hq
      refine ⟨s1 * s2, mul_ne_zero hs1 hs2, MvPolynomial.C s2 * p1 + MvPolynomial.C s1 * q1, ?_⟩
      rw [map_add, map_mul, map_mul, hp1, hq1, hC, hC, map_mul (algebraMap (𝓞 K) K),
        MvPolynomial.C_mul]
      ring
    next p i hp =>
      obtain ⟨s, hs, p1, hp1⟩ := hp
      exact ⟨s, hs, p1 * MvPolynomial.X i, by rw [map_mul, hp1, hX, mul_assoc]⟩
  have hCne : ∀ s : 𝓞 K, s ≠ 0 → algebraMap (KTp K D N) (KTf K D N)
      (MvPolynomial.C (algebraMap (𝓞 K) K s)) ≠ 0 := by
    intro s hs
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff, MvPolynomial.C_eq_zero]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hs
  have hOp : ∀ a : OT K D N, algebraMap (Op D N la) (KTf K D N) (algebraMap (OT K D N) (Op D N la) a) =
      algebraMap (KTp K D N) (KTf K D N) (OTtoKT K D N a) := opToKT_alg D N la
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    exact IsUnit.mk0 _ ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hy))
  · intro z
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := KTp K D N) z
    obtain ⟨sp, hsp, p', hp'⟩ := hcl p
    obtain ⟨sq, hsq, q', hq'⟩ := hcl q
    have hq0 : algebraMap (KTp K D N) (KTf K D N) q ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    have e1 : algebraMap (Op D N la) (KTf K D N)
        (algebraMap (OT K D N) (Op D N la) (p' * MvPolynomial.C sq)) =
        algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.C (algebraMap (𝓞 K) K sp)) *
          algebraMap (KTp K D N) (KTf K D N) p *
          algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.C (algebraMap (𝓞 K) K sq)) := by
      rw [hOp, map_mul, hp', hC, map_mul, map_mul]
    have e2 : algebraMap (Op D N la) (KTf K D N)
        (algebraMap (OT K D N) (Op D N la) (q' * MvPolynomial.C sp)) =
        algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.C (algebraMap (𝓞 K) K sq)) *
          algebraMap (KTp K D N) (KTf K D N) q *
          algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.C (algebraMap (𝓞 K) K sp)) := by
      rw [hOp, map_mul, hq', hC, map_mul, map_mul]
    have hx2 : algebraMap (OT K D N) (Op D N la) (q' * MvPolynomial.C sp) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mp (by
        rw [e2]
        exact mul_ne_zero (mul_ne_zero (hCne sq hsq) hq0) (hCne sp hsp))
    refine ⟨⟨algebraMap (OT K D N) (Op D N la) (p' * MvPolynomial.C sq),
      ⟨_, mem_nonZeroDivisors_of_ne_zero hx2⟩⟩, ?_⟩
    show _ * algebraMap (Op D N la) (KTf K D N)
        (algebraMap (OT K D N) (Op D N la) (q' * MvPolynomial.C sp)) = _
    rw [e1, e2]
    have h1 := hCne sq hsq
    have h2 := hCne sp hsp
    first
      | (field_simp; done)
      | (field_simp; ring)
      | (rw [div_mul_eq_mul_div, div_eq_iff hq0]; ring)
  · intro x y hxy
    exact ⟨1, by rw [hinj hxy]⟩

/- English proof (translation)
Establish `hdvd : la.asIdeal ∣ Ideal.span {ϖ}` using `Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hϖ)`. Take `⟨J, hJ⟩` from `hdvd`. Establish `hJla : ¬ J ≤ la.asIdeal`. Introduce `hle`. Apply `hϖ2` to reduce the goal to its premises.

Establish `hsub : Ideal.span {ϖ} ≤ la.asIdeal ^ 2`. Rewrite using `[hJ, sq]`. Conclude with `Ideal.mul_mono_right hle`. Conclude with `hsub (Ideal.mem_span_singleton_self ϖ)`. Take `⟨s, hsJ, hsla⟩` from `Set.not_subset.mp hJla`.

Establish `key : ∀ a ∈ la.asIdeal, ∃ b, s * a = ϖ * b`. Introduce `a ha`. Establish `hmem : s * a ∈ Ideal.span {ϖ}`. Rewrite using `[hJ, mul_comm s a]`. Conclude with `Ideal.mul_mem_mul ha hsJ`.

Conclude with `Ideal.mem_span_singleton.mp hmem`. Establish `hsnot : MvPolynomial.C s ∉ laT D N la`. Unfold `laT`. Rewrite using `[MvPolynomial.mem_map_C_iff]`. Introduce `h`.

Apply `hsla` to reduce the goal to its premises. Simplify using `using h 0`. Establish `hsu : IsUnit (algebraMap (OT K D N) (Op D N la) (MvPolynomial.C s))` using `IsLocalization.map_units (Op D N la) (⟨MvPolynomial.C s, hsnot⟩ : (laT D N la).primeCompl)`. Establish `hsub : ∀ a ∈ la.asIdeal, algebraMap (OT K D N) (Op D N la) (MvPolynomial.C a) ∈ Ideal.span {algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ)}`. Introduce `a ha`.

Take `⟨b, hb⟩` from `key a ha`. Take `⟨u, hu⟩` from `hsu`. Establish `e : algebraMap (OT K D N) (Op D N la) (MvPolynomial.C s) * algebraMap (OT K D N) (Op D N la) (MvPolynomial.C a) = algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ) * algebraMap (OT K D N) (Op D N la) (MvPolynomial.C b)`. Simplify using `only [← map_mul, hb]`. Rewrite `e` using `[← hu]`.

Use `Ideal.mem_span_singleton.mpr ⟨algebraMap (OT K D N) (Op D N la) (MvPolynomial.C b) * ↑u⁻¹, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hm : IsLocalRing.maximalIdeal (Op D N la) = Ideal.span {algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ)}`. Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal]`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Establish `hle : laT D N la ≤ Ideal.comap (algebraMap (OT K D N) (Op D N la)) (Ideal.span {algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ)})` using `by show Ideal.map (MvPolynomial.C : 𝓞 K →+* OT K D N) la.asIdeal ≤ _`. Use `Ideal.map_le_iff_le_comap.mpr ?_` and prove the remaining obligations. Introduce `a ha`. Conclude with `hsub a ha`.

Conclude with `hle`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hϖ)`. Use `set x := algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ) with hxdef`. Establish `hx0 : x ≠ 0`.

Establish `hϖ0 : ϖ ≠ 0` using `fun h => hϖ2 (h ▸ Ideal.zero_mem _)`. Rewrite using `[hxdef]`. Use `(map_ne_zero_iff _ (IsLocalization.injective (Op D N la) (Ideal.primeCompl_le_nonZeroDivisors (laT D N la)))).mpr ?_` and prove the remaining obligations. Simplify using `using hϖ0`. Establish `hxm : x ∈ IsLocalRing.maximalIdeal (Op D N la)`.

Rewrite using `[hm]`. Conclude with `Ideal.mem_span_singleton_self x`. Establish `hxnu : ¬ IsUnit x` using `(IsLocalRing.mem_maximalIdeal x).mp hxm`. Use `⟨hxnu, ?_⟩` and prove the remaining obligations. Introduce `a b hab`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `ha : a ∈ IsLocalRing.maximalIdeal (Op D N la)` using `(IsLocalRing.mem_maximalIdeal a).mpr hcon.1`. Establish `hb : b ∈ IsLocalRing.maximalIdeal (Op D N la)` using `(IsLocalRing.mem_maximalIdeal b).mpr hcon.2`. Rewrite `ha`, `hb` using `[hm, Ideal.mem_span_singleton]`.

Take `⟨a', rfl⟩` from `ha`. Take `⟨b', rfl⟩` from `hb`. Apply `hxnu` to reduce the goal to its premises. Establish `h2 : x * (a' * (x * b')) = x * 1`. Rewrite using `[mul_one, ← mul_assoc]`.

Conclude with `hab.symm`. Establish `h3 : a' * (x * b') = 1` using `mul_left_cancel₀ hx0 h2`. Establish `h4 : x * (b' * a') = 1`. Rewrite using `[← h3]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `⟨⟨x, b' * a', h4, by rw [mul_comm]; exact h4⟩, rfl⟩`.
-/
theorem op_irreducible (ϖ : 𝓞 K) (hϖ : ϖ ∈ la.asIdeal) (hϖ2 : ϖ ∉ la.asIdeal ^ 2) :
    Irreducible (algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ)) := by
  classical
  have hdvd : la.asIdeal ∣ Ideal.span {ϖ} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hϖ)
  obtain ⟨J, hJ⟩ := hdvd
  have hJla : ¬ J ≤ la.asIdeal := by
    intro hle
    apply hϖ2
    have hsub : Ideal.span {ϖ} ≤ la.asIdeal ^ 2 := by
      rw [hJ, sq]
      exact Ideal.mul_mono_right hle
    exact hsub (Ideal.mem_span_singleton_self ϖ)
  obtain ⟨s, hsJ, hsla⟩ := Set.not_subset.mp hJla
  have key : ∀ a ∈ la.asIdeal, ∃ b, s * a = ϖ * b := by
    intro a ha
    have hmem : s * a ∈ Ideal.span {ϖ} := by
      rw [hJ, mul_comm s a]
      exact Ideal.mul_mem_mul ha hsJ
    exact Ideal.mem_span_singleton.mp hmem
  have hsnot : MvPolynomial.C s ∉ laT D N la := by
    unfold laT
    rw [MvPolynomial.mem_map_C_iff]
    intro h
    apply hsla
    simpa using h 0
  have hsu : IsUnit (algebraMap (OT K D N) (Op D N la) (MvPolynomial.C s)) :=
    IsLocalization.map_units (Op D N la) (⟨MvPolynomial.C s, hsnot⟩ : (laT D N la).primeCompl)
  have hsub : ∀ a ∈ la.asIdeal, algebraMap (OT K D N) (Op D N la) (MvPolynomial.C a) ∈
      Ideal.span {algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ)} := by
    intro a ha
    obtain ⟨b, hb⟩ := key a ha
    obtain ⟨u, hu⟩ := hsu
    have e : algebraMap (OT K D N) (Op D N la) (MvPolynomial.C s) *
        algebraMap (OT K D N) (Op D N la) (MvPolynomial.C a) =
        algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ) *
          algebraMap (OT K D N) (Op D N la) (MvPolynomial.C b) := by
      simp only [← map_mul, hb]
    rw [← hu] at e
    refine Ideal.mem_span_singleton.mpr ⟨algebraMap (OT K D N) (Op D N la) (MvPolynomial.C b) * ↑u⁻¹, ?_⟩
    calc algebraMap (OT K D N) (Op D N la) (MvPolynomial.C a)
        = ↑u⁻¹ * (↑u * algebraMap (OT K D N) (Op D N la) (MvPolynomial.C a)) := by simp
      _ = ↑u⁻¹ * (algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ) *
          algebraMap (OT K D N) (Op D N la) (MvPolynomial.C b)) := by rw [e]
      _ = _ := by ring
  have hm : IsLocalRing.maximalIdeal (Op D N la) =
      Ideal.span {algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ)} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      have hle : laT D N la ≤ Ideal.comap (algebraMap (OT K D N) (Op D N la))
          (Ideal.span {algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ)}) := by
        show Ideal.map (MvPolynomial.C : 𝓞 K →+* OT K D N) la.asIdeal ≤ _
        refine Ideal.map_le_iff_le_comap.mpr ?_
        intro a ha
        exact hsub a ha
      exact hle
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hϖ)
  set x := algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ) with hxdef
  have hx0 : x ≠ 0 := by
    have hϖ0 : ϖ ≠ 0 := fun h => hϖ2 (h ▸ Ideal.zero_mem _)
    rw [hxdef]
    refine (map_ne_zero_iff _ (IsLocalization.injective (Op D N la)
      (Ideal.primeCompl_le_nonZeroDivisors (laT D N la)))).mpr ?_
    simpa using hϖ0
  have hxm : x ∈ IsLocalRing.maximalIdeal (Op D N la) := by
    rw [hm]
    exact Ideal.mem_span_singleton_self x
  have hxnu : ¬ IsUnit x := (IsLocalRing.mem_maximalIdeal x).mp hxm
  refine ⟨hxnu, ?_⟩
  intro a b hab
  by_contra hcon
  push_neg at hcon
  have ha : a ∈ IsLocalRing.maximalIdeal (Op D N la) := (IsLocalRing.mem_maximalIdeal a).mpr hcon.1
  have hb : b ∈ IsLocalRing.maximalIdeal (Op D N la) := (IsLocalRing.mem_maximalIdeal b).mpr hcon.2
  rw [hm, Ideal.mem_span_singleton] at ha hb
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  apply hxnu
  have h2 : x * (a' * (x * b')) = x * 1 := by
    rw [mul_one, ← mul_assoc]
    exact hab.symm
  have h3 : a' * (x * b') = 1 := mul_left_cancel₀ hx0 h2
  have h4 : x * (b' * a') = 1 := by
    rw [← h3]
    ring
  exact ⟨⟨x, b' * a', h4, by rw [mul_comm]; exact h4⟩, rfl⟩

/- English proof (translation)
Rewrite using `[opToKT_alg, IsScalarTower.algebraMap_apply K (KTp K D N) (KTf K D N), MvPolynomial.algebraMap_eq]`. Use `congr 1`. Unfold `OTtoKT`. Rewrite using `[MvPolynomial.map_C]`.
-/
theorem opToKT_C (ϖ : 𝓞 K) :
    OpToKT D N la (algebraMap (OT K D N) (Op D N la) (MvPolynomial.C ϖ)) =
      algebraMap K (KTf K D N) (ϖ : K) := by
  rw [opToKT_alg, IsScalarTower.algebraMap_apply K (KTp K D N) (KTf K D N), MvPolynomial.algebraMap_eq]
  congr 1
  unfold OTtoKT
  rw [MvPolynomial.map_C]

end NPA

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

/- English proof (translation)
Unfold `Data.OpToS Data.KTtoS Data.OTtoS`. Rewrite using `[RingHom.comp_apply, NPA.opToKT_alg, IsFractionRing.lift_algebraMap]`. Both sides reduce to the same expression.
-/
theorem opToS_alg (h : d.S1) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c : ι)
    (x : OT K d.D d.N) :
    d.OpToS h la c (algebraMap (OT K d.D d.N) (Op d.D d.N la) x) = d.OTtoS c x := by
  unfold Data.OpToS Data.KTtoS Data.OTtoS
  rw [RingHom.comp_apply, NPA.opToKT_alg, IsFractionRing.lift_algebraMap]
  rfl

/- English proof (translation)
Use `letI iF : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra`. Use `letI iO : Algebra (Op d.D d.N la) (KTf K d.D d.N) := (OpToKT d.D d.N la).toAlgebra`. Use `letI iOL : Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := (d.OpToS h la c).toAlgebra`. Use `haveI : IsScalarTower (Op d.D d.N la) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Use `haveI : IsDiscreteValuationRing (Op d.D d.N la) := Op_isDVR d.D d.N la`.

Use `haveI : IsFractionRing (Op d.D d.N la) (KTf K d.D d.N) := NPA.op_isFractionRing d.D d.N la`. Use `haveI : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.omS_finite hd h c).1`. Use `haveI : CharZero (KTf K d.D d.N) := charZero_of_injective_algebraMap (algebraMap K (KTf K d.D d.N)).injective`. Use `haveI : Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := inferInstance`. Use `haveI : IsDedekindDomain (integralClosure (Op d.D d.N la) (OmS (Ω c) d.D d.N)) := integralClosure.isDedekindDomain (Op d.D d.N la) (KTf K d.D d.N) _`.

Use `haveI : IsFractionRing (integralClosure (Op d.D d.N la) (OmS (Ω c) d.D d.N)) (OmS (Ω c) d.D d.N) := integralClosure.isFractionRing_of_finite_extension (KTf K d.D d.N) _`. Take `⟨u, hu, hn⟩` from `ValPl.norm_eq_places (O := Op d.D d.N la) (F := KTf K d.D d.N) y hy (NPA.op_irreducible d.D d.N la ϖ hϖ hϖ2)`. Use `letI iT : Algebra (OT K d.D d.N) (OmS (Ω c) d.D d.N) := (d.OTtoS c).toAlgebra`. Use `haveI : IsScalarTower (OT K d.D d.N) (Op d.D d.N la) (OmS (Ω c) d.D d.N) := IsScalarTower.of_algebraMap_eq (fun x => (d.opToS_alg h la c x).symm)`. Establish `hpl : ValPl.PlacesOver (Op d.D d.N la) (OmS (Ω c) d.D d.N) = d.PlOver la c`.

Use extensionality with `w`. Simplify using `only [ValPl.PlacesOver, Data.PlOver, Set.mem_setOf_eq]`. Rewrite using `[← ValPl.placesOver_iff_loc (R := OT K d.D d.N) (laT d.D d.N la) w]`. Both sides reduce to the same expression. Use `⟨u, hu, ?_⟩` and prove the remaining obligations.

Rewrite using `[hn, hpl]`. Rewrite using `[show algebraMap (Op d.D d.N la) (KTf K d.D d.N) (algebraMap (OT K d.D d.N) (Op d.D d.N la) (MvPolynomial.C ϖ)) = algebraMap K (KTf K d.D d.N) (ϖ : K) from NPA.opToKT_C d.D d.N la ϖ]`. Both sides reduce to the same expression.
-/
theorem norm_at_la_A (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (ϖ : 𝓞 K) (hϖ : ϖ ∈ la.asIdeal) (hϖ2 : ϖ ∉ la.asIdeal ^ 2)
    (y : OmS (Ω c) d.D d.N) (hy : y ≠ 0) :
    ∃ u : Op d.D d.N la, IsUnit u ∧
      letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
      Algebra.norm (KTf K d.D d.N) y =
        (algebraMap K (KTf K d.D d.N) (ϖ : K)) ^
          (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
            (d.fze h c w : ℤ) * WithTop.untopD 0 (w y)) * OpToKT d.D d.N la u := by
  letI iF : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  letI iO : Algebra (Op d.D d.N la) (KTf K d.D d.N) := (OpToKT d.D d.N la).toAlgebra
  letI iOL : Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := (d.OpToS h la c).toAlgebra
  haveI : IsScalarTower (Op d.D d.N la) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsDiscreteValuationRing (Op d.D d.N la) := Op_isDVR d.D d.N la
  haveI : IsFractionRing (Op d.D d.N la) (KTf K d.D d.N) := NPA.op_isFractionRing d.D d.N la
  haveI : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.omS_finite hd h c).1
  haveI : CharZero (KTf K d.D d.N) :=
    charZero_of_injective_algebraMap (algebraMap K (KTf K d.D d.N)).injective
  haveI : Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := inferInstance
  haveI : IsDedekindDomain (integralClosure (Op d.D d.N la) (OmS (Ω c) d.D d.N)) :=
    integralClosure.isDedekindDomain (Op d.D d.N la) (KTf K d.D d.N) _
  haveI : IsFractionRing (integralClosure (Op d.D d.N la) (OmS (Ω c) d.D d.N)) (OmS (Ω c) d.D d.N) :=
    integralClosure.isFractionRing_of_finite_extension (KTf K d.D d.N) _
  obtain ⟨u, hu, hn⟩ := ValPl.norm_eq_places (O := Op d.D d.N la) (F := KTf K d.D d.N) y hy
    (NPA.op_irreducible d.D d.N la ϖ hϖ hϖ2)
  letI iT : Algebra (OT K d.D d.N) (OmS (Ω c) d.D d.N) := (d.OTtoS c).toAlgebra
  haveI : IsScalarTower (OT K d.D d.N) (Op d.D d.N la) (OmS (Ω c) d.D d.N) :=
    IsScalarTower.of_algebraMap_eq (fun x => (d.opToS_alg h la c x).symm)
  have hpl : ValPl.PlacesOver (Op d.D d.N la) (OmS (Ω c) d.D d.N) = d.PlOver la c := by
    ext w
    simp only [ValPl.PlacesOver, Data.PlOver, Set.mem_setOf_eq]
    rw [← ValPl.placesOver_iff_loc (R := OT K d.D d.N) (laT d.D d.N la) w]
    rfl
  refine ⟨u, hu, ?_⟩
  rw [hn, hpl]
  rw [show algebraMap (Op d.D d.N la) (KTf K d.D d.N)
      (algebraMap (OT K d.D d.N) (Op d.D d.N la) (MvPolynomial.C ϖ)) =
      algebraMap K (KTf K d.D d.N) (ϖ : K) from NPA.opToKT_C d.D d.N la ϖ]
  rfl

end Data

end ReciprocityTheory.ChartRestriction.G.T0
