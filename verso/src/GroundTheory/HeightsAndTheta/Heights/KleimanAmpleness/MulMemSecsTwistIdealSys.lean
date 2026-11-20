import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BaseChangeTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Kleiman

noncomputable section

section Kill

variable {R : Type*} [CommRing R] {Ω : Type*} [Field Ω] [Algebra R Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

/- English proof (translation)
Simplify using `only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at hy ⊢`. Introduce `I`. Rewrite using `[SubSystem.twist_sub_eq_mul_of_line]`. Use `Submodule.mul_mem_mul (Submodule.subset_span ⟨C a, 1, 0, ha, one_mem _, isHomogeneous_C _ _, isHomogeneous_one _ _, by simp⟩) (hy I)` and prove the remaining obligations.
-/
theorem mul_mem_secs_twist_idealSys (J : Ideal (Poly R N)) {a : R} (ha : C a ∈ J)
    (F : SubSystem R x Ω) {y : Ω} (hy : y ∈ F.secs) :
    algebraMap R Ω a * y ∈ (F.twist (idealSys x J)).secs := by
  simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at hy ⊢
  intro I
  rw [SubSystem.twist_sub_eq_mul_of_line]
  refine Submodule.mul_mem_mul (Submodule.subset_span ⟨C a, 1, 0, ha, one_mem _, isHomogeneous_C _ _,
    isHomogeneous_one _ _, by simp⟩) (hy I)

end Kill

section Local

variable {S : Type*} [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal] {O : Type*} [CommRing O] [Algebra S O]
  [IsLocalization.AtPrime O 𝔪] {Ω : Type*} [Field Ω] [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω]
  {N : ℕ} {x : Fin (N + 1) → Ω}

/- English proof (translation)
Take `⟨⟨t, ht⟩, hb⟩` from `IsLocalization.exist_integer_multiples 𝔪.primeCompl f.support (fun d => f.coeff d)`. Establish `hb' : ∀ d ∈ f.support, ∃ r : S, algebraMap S O r = t • f.coeff d` using `fun d hd => RingHom.mem_rangeS.mp (hb d hd)`. Use `choose! c hc using hb'`. Establish `hcoeff : ∀ d, (∑ d' ∈ f.support, monomial d' (c d') : Poly S N).coeff d = if d ∈ f.support then c d else 0`. Introduce `d`.

Rewrite using `[coeff_sum]`. Simplify using `only [coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`. Use `⟨t, ht, ∑ d' ∈ f.support, monomial d' (c d'), ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `d`.

Rewrite using `[coeff_map, coeff_C_mul, hcoeff]`. Use `split_ifs with hd`. Rewrite using `[hc d hd, Algebra.smul_def]`. Rewrite `hd` using `[mem_support_iff, not_not]`. Rewrite using `[hd, map_zero, mul_zero]`.

Introduce `d hd`. Rewrite `hd` using `[hcoeff]`. Use `split_ifs at hd with h`. Conclude with `mem_support_iff.mp h`. Conclude with `absurd rfl hd`.
-/
theorem exists_map_eq_C_mul (f : Poly O N) :
    ∃ t : S, t ∉ 𝔪 ∧ ∃ g : Poly S N, map (algebraMap S O) g = C (algebraMap S O t) * f ∧
      ∀ d, g.coeff d ≠ 0 → f.coeff d ≠ 0 := by
  classical
  obtain ⟨⟨t, ht⟩, hb⟩ := IsLocalization.exist_integer_multiples 𝔪.primeCompl f.support (fun d => f.coeff d)
  have hb' : ∀ d ∈ f.support, ∃ r : S, algebraMap S O r = t • f.coeff d :=
    fun d hd => RingHom.mem_rangeS.mp (hb d hd)
  choose! c hc using hb'
  have hcoeff : ∀ d, (∑ d' ∈ f.support, monomial d' (c d') : Poly S N).coeff d =
      if d ∈ f.support then c d else 0 := by
    intro d
    rw [coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
  refine ⟨t, ht, ∑ d' ∈ f.support, monomial d' (c d'), ?_, ?_⟩
  · ext d
    rw [coeff_map, coeff_C_mul, hcoeff]
    split_ifs with hd
    · rw [hc d hd, Algebra.smul_def]
    · rw [mem_support_iff, not_not] at hd
      rw [hd, map_zero, mul_zero]
  · intro d hd
    rw [hcoeff] at hd
    split_ifs at hd with h
    · exact mem_support_iff.mp h
    · exact absurd rfl hd

omit [IsLocalization.AtPrime O 𝔪] in

/- English proof (translation)
Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem a ha`. Take `⟨i, hi, rfl⟩` from `ha`. Conclude with `⟨X i, Submonoid.subset_closure ⟨i, hi, rfl⟩, map_X _ _⟩`. Consider the case `one => exact ⟨1, one_mem _, map_one _⟩`.

Consider the case `mul a b _ _ ha hb`. Take `⟨a₀, ha₀, rfl⟩` from `ha`. Take `⟨b₀, hb₀, rfl⟩` from `hb`. Conclude with `⟨a₀ * b₀, mul_mem ha₀ hb₀, map_mul _ _ _⟩`.
-/
theorem exists_monos_map {I : Finset (Fin (N + 1))} {s : Poly O N} (hs : s ∈ monos (S := O) I) :
    ∃ s₀ ∈ monos (S := S) I, map (algebraMap S O) s₀ = s := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    exact ⟨X i, Submonoid.subset_closure ⟨i, hi, rfl⟩, map_X _ _⟩
  | one => exact ⟨1, one_mem _, map_one _⟩
  | mul a b _ _ ha hb =>
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    exact ⟨a₀ * b₀, mul_mem ha₀ hb₀, map_mul _ _ _⟩

/- English proof (translation)
Take `⟨t, ht, g, hg, hgc⟩` from `exists_map_eq_C_mul 𝔪 f`. Take `⟨s₀, hs₀, rfl⟩` from `exists_monos_map (S := S) hs`. Take `⟨e₀, he₀⟩` from `monos_isHomogeneous hs₀`. Establish `hs0 : map (algebraMap S O) s₀ ≠ 0` using `fun h => eval_ne_zero_of_mem_monos I hs (by rw [h, map_zero])`. Establish `hee : e₀ = e` using `(he₀.map (algebraMap S O)).inj_right hse hs0`.

Substitute `hee` using the available equality. Use `⟨t, ht, g, s₀, ?_, hs₀, he₀, hg, ?_⟩` and prove the remaining obligations. Introduce `d hd`. Conclude with `hf (hgc d hd)`. Rewrite using `[← aeval_map_algebraMap (A := O) x g, hg, ← aeval_map_algebraMap (A := O) x s₀, map_mul, aeval_C, IsScalarTower.algebraMap_apply S O Ω, mul_div_assoc]`.
-/
theorem exists_lift_frac {I : Chart x} {f s : Poly O N} {e : ℕ} (hf : f.IsHomogeneous e)
    (hs : s ∈ monos I.1) (hse : s.IsHomogeneous e) :
    ∃ t : S, t ∉ 𝔪 ∧ ∃ g s₀ : Poly S N, g.IsHomogeneous e ∧ s₀ ∈ monos I.1 ∧ s₀.IsHomogeneous e ∧
      map (algebraMap S O) g = C (algebraMap S O t) * f ∧
      algebraMap S Ω t * (aeval x f / aeval x s) = aeval x g / aeval x s₀ := by
  obtain ⟨t, ht, g, hg, hgc⟩ := exists_map_eq_C_mul 𝔪 f
  obtain ⟨s₀, hs₀, rfl⟩ := exists_monos_map (S := S) hs
  obtain ⟨e₀, he₀⟩ := monos_isHomogeneous hs₀
  have hs0 : map (algebraMap S O) s₀ ≠ 0 := fun h =>
    eval_ne_zero_of_mem_monos I hs (by rw [h, map_zero])
  have hee : e₀ = e := (he₀.map (algebraMap S O)).inj_right hse hs0
  subst hee
  refine ⟨t, ht, g, s₀, ?_, hs₀, he₀, hg, ?_⟩
  · intro d hd
    exact hf (hgc d hd)
  · rw [← aeval_map_algebraMap (A := O) x g, hg, ← aeval_map_algebraMap (A := O) x s₀, map_mul, aeval_C,
      IsScalarTower.algebraMap_apply S O Ω, mul_div_assoc]

/- English proof (translation)
Take `⟨f, s, e, hs, hf, hse, rfl⟩` from `ha`. Take `⟨t, ht, g, s₀, hg, hs₀, hs₀e, -, hval⟩` from `exists_lift_frac 𝔪 hf hs hse`. Conclude with `⟨t, ht, hval ▸ ⟨g, s₀, e, hs₀, hg, hs₀e, rfl⟩⟩`.
-/
theorem exists_mul_mem_chartRing {I : Chart x} {a : Ω} (ha : a ∈ chartRing O x I) :
    ∃ t : S, t ∉ 𝔪 ∧ algebraMap S Ω t * a ∈ chartRing S x I := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  obtain ⟨t, ht, g, s₀, hg, hs₀, hs₀e, -, hval⟩ := exists_lift_frac 𝔪 hf hs hse
  exact ⟨t, ht, hval ▸ ⟨g, s₀, e, hs₀, hg, hs₀e, rfl⟩⟩

omit [IsLocalization.AtPrime O 𝔪] [IsScalarTower S O Ω] in

/- English proof (translation)
Introduce `h` and use `((Ideal.IsPrime.mem_or_mem inferInstance h).elim h₁ h₂)`.
-/
theorem mul_not_mem {t₁ t₂ : S} (h₁ : t₁ ∉ 𝔪) (h₂ : t₂ ∉ 𝔪) : t₁ * t₂ ∉ 𝔪 := fun h =>
  ((Ideal.IsPrime.mem_or_mem inferInstance h).elim h₁ h₂)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `z ∈ Submodule.span (chartRing O x I) (G.sub I : Set Ω) at hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, fun h => (Ideal.IsMaximal.ne_top inferInstance) ((Ideal.eq_top_iff_one _).mpr h), by rw [map_one, one_mul]; exact hy⟩`. Consider the case `zero => exact ⟨1, fun h => (Ideal.IsMaximal.ne_top inferInstance) ((Ideal.eq_top_iff_one _).mpr h), by rw [mul_zero]; exact zero_mem _⟩`. Consider the case `add a b _ _ ha hb`.

Take `⟨t₁, ht₁, h₁⟩` from `ha`. Take `⟨t₂, ht₂, h₂⟩` from `hb`. Use `⟨t₁ * t₂, mul_not_mem 𝔪 ht₁ ht₂, ?_⟩` and prove the remaining obligations. Establish `e : algebraMap S Ω (t₁ * t₂) * (a + b) = t₂ • (algebraMap S Ω t₁ * a) + t₁ • (algebraMap S Ω t₂ * b)`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `add_mem ((G.sub I).smul_of_tower_mem t₂ h₁) ((G.sub I).smul_of_tower_mem t₁ h₂)`. Consider the case `smul a z _ hz`. Take `⟨t, ht, hzt⟩` from `hz`.

Take `⟨t', ht', hb⟩` from `exists_mul_mem_chartRing 𝔪 a.2`. Use `⟨t' * t, mul_not_mem 𝔪 ht' ht, ?_⟩` and prove the remaining obligations. Establish `e : algebraMap S Ω (t' * t) * (a • z) = (⟨_, hb⟩ : chartRing S x I) • (algebraMap S Ω t * z)`. Rewrite using `[chartRing_smul_def, chartRing_smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `(G.sub I).smul_mem _ hzt`.
-/
theorem exists_mul_mem_sub {G : SubSystem S x Ω} {I : Chart x} {z : Ω} (hz : z ∈ (G.baseChange O).sub I) :
    ∃ t : S, t ∉ 𝔪 ∧ algebraMap S Ω t * z ∈ G.sub I := by
  change z ∈ Submodule.span (chartRing O x I) (G.sub I : Set Ω) at hz
  induction hz using Submodule.span_induction with
  | mem y hy => exact ⟨1, fun h => (Ideal.IsMaximal.ne_top inferInstance) ((Ideal.eq_top_iff_one _).mpr h),
      by rw [map_one, one_mul]; exact hy⟩
  | zero => exact ⟨1, fun h => (Ideal.IsMaximal.ne_top inferInstance) ((Ideal.eq_top_iff_one _).mpr h),
      by rw [mul_zero]; exact zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨t₁, ht₁, h₁⟩ := ha
    obtain ⟨t₂, ht₂, h₂⟩ := hb
    refine ⟨t₁ * t₂, mul_not_mem 𝔪 ht₁ ht₂, ?_⟩
    have e : algebraMap S Ω (t₁ * t₂) * (a + b) =
        t₂ • (algebraMap S Ω t₁ * a) + t₁ • (algebraMap S Ω t₂ * b) := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]; ring
    rw [e]
    exact add_mem ((G.sub I).smul_of_tower_mem t₂ h₁) ((G.sub I).smul_of_tower_mem t₁ h₂)
  | smul a z _ hz =>
    obtain ⟨t, ht, hzt⟩ := hz
    obtain ⟨t', ht', hb⟩ := exists_mul_mem_chartRing 𝔪 a.2
    refine ⟨t' * t, mul_not_mem 𝔪 ht' ht, ?_⟩
    have e : algebraMap S Ω (t' * t) * (a • z) =
        (⟨_, hb⟩ : chartRing S x I) • (algebraMap S Ω t * z) := by
      rw [chartRing_smul_def, chartRing_smul_def, map_mul]; ring
    rw [e]
    exact (G.sub I).smul_mem _ hzt

omit [Algebra S O] [IsScalarTower S O Ω] in

/- English proof (translation)
Simplify using `only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at hy ⊢`. Conclude with `fun I => Submodule.subset_span (hy I)`.
-/
theorem mem_secs_baseChange {G : SubSystem S x Ω} {y : Ω} (hy : y ∈ G.secs) :
    y ∈ (G.baseChange O).secs := by
  simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at hy ⊢
  exact fun I => Submodule.subset_span (hy I)

/- English proof (translation)
Simplify using `only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at hz ⊢`. Use `choose t ht hzt using fun I => exists_mul_mem_sub 𝔪 (hz I)`. Use `⟨∏ I, t I, fun h => ?_, fun I => ?_⟩` and prove the remaining obligations. Take `⟨I, -, hI⟩` from `(Ideal.IsPrime.prod_mem_iff (hp := inferInstance)).mp h`. Conclude with `ht I hI`.

Rewrite using `[← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ I), map_mul, mul_comm (algebraMap S Ω (t I)), mul_assoc, ← Algebra.smul_def]`. Conclude with `(G.sub I).smul_of_tower_mem _ (hzt I)`.
-/
theorem exists_mul_mem_secs {G : SubSystem S x Ω} {z : Ω} (hz : z ∈ (G.baseChange O).secs) :
    ∃ t : S, t ∉ 𝔪 ∧ algebraMap S Ω t * z ∈ G.secs := by
  classical
  simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at hz ⊢
  choose t ht hzt using fun I => exists_mul_mem_sub 𝔪 (hz I)
  refine ⟨∏ I, t I, fun h => ?_, fun I => ?_⟩
  · obtain ⟨I, -, hI⟩ := (Ideal.IsPrime.prod_mem_iff (hp := inferInstance)).mp h
    exact ht I hI
  · rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ I), map_mul, mul_comm (algebraMap S Ω (t I)),
      mul_assoc, ← Algebra.smul_def]
    exact (G.sub I).smul_of_tower_mem _ (hzt I)

/- English proof (translation)
Take `⟨v, hv⟩` from `IsLocalization.map_units O (⟨t, ht⟩ : 𝔪.primeCompl)`. Use `⟨(v⁻¹ : Oˣ), ?_⟩` and prove the remaining obligations. Rewrite using `[IsScalarTower.algebraMap_apply S O Ω, ← map_mul]`. Express the relevant statement in the definitionally equal form `algebraMap O Ω ((v⁻¹ : Oˣ) * algebraMap S O t) = 1`. Rewrite using `[← hv, Units.inv_mul, map_one]`.
-/
theorem exists_inv_algebraMap {t : S} (ht : t ∉ 𝔪) : ∃ u : O, algebraMap O Ω u * algebraMap S Ω t = 1 := by
  obtain ⟨v, hv⟩ := IsLocalization.map_units O (⟨t, ht⟩ : 𝔪.primeCompl)
  refine ⟨(v⁻¹ : Oˣ), ?_⟩
  rw [IsScalarTower.algebraMap_apply S O Ω, ← map_mul]
  change algebraMap O Ω ((v⁻¹ : Oˣ) * algebraMap S O t) = 1
  rw [← hv, Units.inv_mul, map_one]

include 𝔪 in

/- English proof (translation)
Use `SubSystem.ext_sub fun I => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `idealMod pp' I = Submodule.span (chartRing O x I) (idealMod (pp'.comap (map (algebraMap S O) : Poly S N →+* Poly O N)) I : Set Ω)`. Simplify using `only [idealMod]`. Rewrite using `[span_baseChange_span]`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩`. Take `⟨t, ht, g, s₀, hg, hs₀, hs₀e, hmap, hval⟩` from `exists_lift_frac 𝔪 hfe hs hse`. Take `⟨u, hu⟩` from `exists_inv_algebraMap 𝔪 (O := O) (Ω := Ω) ht`. Establish `hg' : g ∈ pp'.comap (map (algebraMap S O) : Poly S N →+* Poly O N)`.

Rewrite using `[Ideal.mem_comap]`. Express the relevant statement in the definitionally equal form `map (algebraMap S O) g ∈ pp'`. Rewrite using `[hmap]`. Conclude with `Ideal.mul_mem_left _ _ hf`. Establish `e' : aeval x f / aeval x s = (⟨algebraMap O Ω u, Subalgebra.algebraMap_mem _ u⟩ : chartRing O x I) • (aeval x g / aeval x s₀)`.

Rewrite using `[chartRing_smul_def, ← hval, ← mul_assoc, hu, one_mul]`. Rewrite using `[SetLike.mem_coe, e']`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, s₀, e, hg', hs₀, hg, hs₀e, rfl⟩)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨g, s, e, hg, hs, hge, hse, rfl⟩`.

Conclude with `Submodule.subset_span ⟨map (algebraMap S O) g, map (algebraMap S O) s, e, hg, map_mem_monos_baseChange hs, hge.map _, hse.map _, by`. Rewrite using `[aeval_map_algebraMap, aeval_map_algebraMap]⟩`.
-/
theorem idealSys_localize (pp' : Ideal (Poly O N)) :
    idealSys x pp' =
      (idealSys x (pp'.comap (map (algebraMap S O) : Poly S N →+* Poly O N))).baseChange O := by
  refine SubSystem.ext_sub fun I => ?_
  change idealMod pp' I = Submodule.span (chartRing O x I)
    (idealMod (pp'.comap (map (algebraMap S O) : Poly S N →+* Poly O N)) I : Set Ω)
  simp only [idealMod]
  rw [span_baseChange_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
    obtain ⟨t, ht, g, s₀, hg, hs₀, hs₀e, hmap, hval⟩ := exists_lift_frac 𝔪 hfe hs hse
    obtain ⟨u, hu⟩ := exists_inv_algebraMap 𝔪 (O := O) (Ω := Ω) ht
    have hg' : g ∈ pp'.comap (map (algebraMap S O) : Poly S N →+* Poly O N) := by
      rw [Ideal.mem_comap]
      change map (algebraMap S O) g ∈ pp'
      rw [hmap]
      exact Ideal.mul_mem_left _ _ hf
    have e' : aeval x f / aeval x s = (⟨algebraMap O Ω u, Subalgebra.algebraMap_mem _ u⟩ : chartRing O x I) •
        (aeval x g / aeval x s₀) := by
      rw [chartRing_smul_def, ← hval, ← mul_assoc, hu, one_mul]
    rw [SetLike.mem_coe, e']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, s₀, e, hg', hs₀, hg, hs₀e, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨g, s, e, hg, hs, hge, hse, rfl⟩
    exact Submodule.subset_span ⟨map (algebraMap S O) g, map (algebraMap S O) s, e, hg,
      map_mem_monos_baseChange hs, hge.map _, hse.map _, by
        rw [aeval_map_algebraMap, aeval_map_algebraMap]⟩

omit [IsScalarTower S O Ω] in

/- English proof (translation)
Establish `stable : ∀ (P : Submodule S Q) (o : O) (n : Q), n ∈ P → o • n ∈ P`. Introduce `P o n hn`. Take `⟨⟨a, ⟨t, ht⟩⟩, h⟩` from `IsLocalization.surj 𝔪.primeCompl o`. Take `⟨y, i, hi, hyi⟩` from `Ideal.IsMaximal.exists_inv (inferInstance : 𝔪.IsMaximal) ht`. Establish `h' : algebraMap S O y * algebraMap S O t + algebraMap S O i = 1`.

Rewrite using `[← map_mul, ← map_add, hyi, map_one]`. Establish `ho : o = algebraMap S O (y * a) + o * algebraMap S O i`. Simplify using `only at h`. Rewrite using `[map_mul]`. Take the linear combination `(algebraMap S O y) * h - o * h'`.

Rewrite using `[ho, add_smul, mul_smul, algebraMap_smul, algebraMap_smul, hkill i hi n, smul_zero, add_zero]`. Conclude with `P.smul_mem _ hn`. Set `e : Submodule O Q ≃o Submodule S Q` to `{ toFun := fun P => P.restrictScalars S invFun := fun P => { toAddSubmonoid := P.toAddSubmonoid, smul_mem' := fun o n hn => stable P o n hn } left_inv := fun _ => rfl right_inv := fun _ => rfl map_rel_iff' := Iff.rfl }`. Rewrite using `[Module.length_eq_height, Module.length_eq_height, ← Order.height_orderIso e ⊤, e.map_top]`.
-/
theorem length_eq_of_killed {Q : Type*} [AddCommGroup Q] [Module O Q] [Module S Q] [IsScalarTower S O Q]
    (hkill : ∀ m ∈ 𝔪, ∀ q : Q, m • q = 0) : Module.length S Q = Module.length O Q := by
  have stable : ∀ (P : Submodule S Q) (o : O) (n : Q), n ∈ P → o • n ∈ P := by
    intro P o n hn
    obtain ⟨⟨a, ⟨t, ht⟩⟩, h⟩ := IsLocalization.surj 𝔪.primeCompl o
    obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv (inferInstance : 𝔪.IsMaximal) ht
    have h' : algebraMap S O y * algebraMap S O t + algebraMap S O i = 1 := by
      rw [← map_mul, ← map_add, hyi, map_one]
    have ho : o = algebraMap S O (y * a) + o * algebraMap S O i := by
      simp only at h
      rw [map_mul]
      linear_combination (algebraMap S O y) * h - o * h'
    rw [ho, add_smul, mul_smul, algebraMap_smul, algebraMap_smul, hkill i hi n, smul_zero, add_zero]
    exact P.smul_mem _ hn
  let e : Submodule O Q ≃o Submodule S Q :=
    { toFun := fun P => P.restrictScalars S
      invFun := fun P => { toAddSubmonoid := P.toAddSubmonoid, smul_mem' := fun o n hn => stable P o n hn }
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  rw [Module.length_eq_height, Module.length_eq_height, ← Order.height_orderIso e ⊤, e.map_top]

end Local

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
