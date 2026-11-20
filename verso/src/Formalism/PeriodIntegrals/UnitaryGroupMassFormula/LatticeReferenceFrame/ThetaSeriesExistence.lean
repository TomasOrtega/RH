import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.ThetaA

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain

namespace PI.ScRefExists.TH

variable (I : Formalism.MainNotions.S.AutInst)

/- English proof (translation)
Establish `hg0 : (g : 𝓞 I.E) ≠ 0`. Introduce `h`. Establish `h2` using `congrArg (fun x : 𝓞 I.E => (x : I.E)) h`. Establish `h3 : (g : I.E) = 0` using `by simpa using h2`. Establish `h4 : g = 0` using `by exact_mod_cast h3`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hg0`.
-/
theorem spanG_ne (g : ℕ) (hg : 1 ≤ g) : Ideal.span {(g : 𝓞 I.E)} ≠ 0 := by
  have hg0 : (g : 𝓞 I.E) ≠ 0 := by
    intro h
    have h2 := congrArg (fun x : 𝓞 I.E => (x : I.E)) h
    have h3 : (g : I.E) = 0 := by simpa using h2
    have h4 : g = 0 := by exact_mod_cast h3
    omega
  rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
  exact hg0

def primesG (g : ℕ) (hg : 1 ≤ g) : Finset (HeightOneSpectrum (𝓞 I.E)) :=
  (Ideal.finite_factors (spanG_ne I g hg)).toFinset

/- English proof (translation)
Unfold `primesG`. Rewrite using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`.
-/
theorem mem_primesG (g : ℕ) (hg : 1 ≤ g) (P : HeightOneSpectrum (𝓞 I.E)) :
    P ∈ primesG I g hg ↔ (g : 𝓞 I.E) ∈ P.asIdeal := by
  unfold primesG
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]

/- English proof (translation)
Rewrite using `[Ideal.radical_eq_sInf]`. Use `le_sInf fun J hJ => ?_` and prove the remaining obligations. Take `⟨hJle, hJp⟩` from `hJ`. Establish `hgJ : (g : 𝓞 I.E) ∈ J` using `hJle (Ideal.mem_span_singleton_self _)`. Establish `hJ0 : J ≠ ⊥`.

Introduce `h`. Apply `spanG_ne I g hg` to reduce the goal to its premises. Rewrite using `[Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Rewrite `hgJ` using `[h]`. Conclude with `(Submodule.mem_bot _).mp hgJ`.

Set `Q : HeightOneSpectrum (𝓞 I.E)` to `⟨J, hJp, hJ0⟩`. Establish `hQ : Q ∈ primesG I g hg` using `(mem_primesG I g hg Q).mpr hgJ`. Conclude with `Ideal.prod_le_inf.trans (Finset.inf_le hQ)`.
-/
theorem prod_le_radical (g : ℕ) (hg : 1 ≤ g) :
    (∏ P ∈ primesG I g hg, P.asIdeal) ≤ (Ideal.span {(g : 𝓞 I.E)}).radical := by
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun J hJ => ?_
  obtain ⟨hJle, hJp⟩ := hJ
  have hgJ : (g : 𝓞 I.E) ∈ J := hJle (Ideal.mem_span_singleton_self _)
  have hJ0 : J ≠ ⊥ := by
    intro h
    apply spanG_ne I g hg
    rw [Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    rw [h] at hgJ
    exact (Submodule.mem_bot _).mp hgJ
  let Q : HeightOneSpectrum (𝓞 I.E) := ⟨J, hJp, hJ0⟩
  have hQ : Q ∈ primesG I g hg := (mem_primesG I g hg Q).mpr hgJ
  exact Ideal.prod_le_inf.trans (Finset.inf_le hQ)

/- English proof (translation)
Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.mp hz`. Use `⟨t, ?_⟩` and prove the remaining obligations. Rewrite using `[← ht]`. Use `first`. Consider the case `(push_cast; ring)`.

Consider the case `simp [mul_comm]`.
-/
private lemma sk_GE_of_mem_span_natCast (g : ℕ) (z : 𝓞 I.E) (hz : z ∈ Ideal.span {(g : 𝓞 I.E)}) :
    PI.ScRefExists.Sk.GE I g (z : I.E) := by
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hz
  refine ⟨t, ?_⟩
  rw [← ht]
  first
    | (push_cast; ring)
    | simp [mul_comm]

/- English proof (translation)
Introduce `I g hg hS`. Use `letI : LinearOrder (HeightOneSpectrum (𝓞 I.E)) := by first`. Consider the case `exact linearOrderOfSTO WellOrderingRel`. Consider the case `exact IsWellOrder.linearOrder WellOrderingRel`. Take `⟨N, hN⟩ : ∃ N : ℕ, (∏ P ∈ primesG I g hg, P.asIdeal) ^ N ≤ Ideal.span {(g : 𝓞 I.E)}` from `by first`.

Consider the case `exact Ideal.exists_pow_le_of_le_radical_of_fg (prod_le_radical I g hg) (IsNoetherian.noetherian _)`. Consider the case `exact Ideal.exists_pow_le_of_le_radical_of_fg (IsNoetherian.noetherian _) (prod_le_radical I g hg)`. Take `⟨θ, hθ⟩` from `IsDedekindDomain.exists_forall_sub_mem_ideal (s := primesG I g hg) (fun P : HeightOneSpectrum (𝓞 I.E) => P.asIdeal) (fun _ => N) (fun P _ => P.prime) (fun P _ Q _ h e => h (HeightOneSpectrum.ext e)) (fun P => if (P : HeightOneSpectrum (𝓞 I.E)) < cj I P then (1 : 𝓞 I.E) else 0)`. Establish `h1 : ∀ P ∈ primesG I g hg, P < cj I P → θ - 1 ∈ P.asIdeal ^ N`. Introduce `P hP h`.

Simplify `hθ P hP` using `[h]`. Establish `h0 : ∀ P ∈ primesG I g hg, ¬ P < cj I P → θ ∈ P.asIdeal ^ N`. Introduce `P hP h`. Simplify `hθ P hP` using `[h]`. Establish `hcjS : ∀ P ∈ primesG I g hg, cj I P ∈ primesG I g hg`.

Introduce `P hP`. Rewrite `hP`, the goal using `[mem_primesG]`. Rewrite using `[mem_cj, map_natCast]`. Conclude with `hP`. Establish `hsg : ∀ (P : HeightOneSpectrum (𝓞 I.E)) (z : 𝓞 I.E), z ∈ (cj I P).asIdeal ^ N → sg I z ∈ P.asIdeal ^ N`.

Introduce `P z hz`. Establish `h2` using `Ideal.mem_map_of_mem (sg I) hz`. Rewrite `h2` using `[Ideal.map_pow, show (cj I P).asIdeal = P.asIdeal.comap (sg I) from rfl, Ideal.map_comap_of_surjective _ (fun y => ⟨sg I y, sg_sg I y⟩)]`. Then use the resulting hypothesis. Establish `hloc : ∀ P ∈ primesG I g hg, θ * θ - θ ∈ P.asIdeal ^ N ∧ θ * sg I θ ∈ P.asIdeal ^ N ∧ 1 - θ - sg I θ ∈ P.asIdeal ^ N`. Introduce `P hP`.

Establish `hne : cj I P ≠ P` using `cj_ne I g hg hS P ((mem_primesG I g hg P).mp hP)`. Distinguish the cases in `hlt : P < cj I P`. Establish `ha` using `h1 P hP hlt`. Establish `hb : θ ∈ (cj I P).asIdeal ^ N` using `h0 (cj I P) (hcjS P hP) (by rw [cj_cj]; exact lt_asymm hlt)`. Establish `hb'` using `hsg P θ hb`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e : θ * θ - θ = (θ - 1) * θ` using `by ring`. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ _ ha`. Conclude with `Ideal.mul_mem_left _ _ hb'`.

Establish `e : 1 - θ - sg I θ = -(θ - 1) - sg I θ` using `by ring`. Rewrite using `[e]`. Conclude with `Ideal.sub_mem _ (Submodule.neg_mem _ ha) hb'`. Establish `ha` using `h0 P hP hlt`. Establish `hlt' : cj I P < cj I (cj I P)`.

Rewrite using `[cj_cj]`. Conclude with `lt_of_le_of_ne (not_lt.mp hlt) hne`. Establish `hb'` using `hsg P _ (h1 (cj I P) (hcjS P hP) hlt')`. Rewrite `hb'` using `[map_sub, map_one]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `e : θ * θ - θ = θ * (θ - 1)` using `by ring`. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ _ ha`. Conclude with `Ideal.mul_mem_right _ _ ha`. Establish `e : 1 - θ - sg I θ = -θ - (sg I θ - 1)` using `by ring`.

Rewrite using `[e]`. Conclude with `Ideal.sub_mem _ (Submodule.neg_mem _ ha) hb'`. Establish `key : (primesG I g hg).inf (fun P : HeightOneSpectrum (𝓞 I.E) => P.asIdeal ^ N) = (∏ P ∈ primesG I g hg, P.asIdeal) ^ N`. Rewrite using `[← Finset.prod_pow]`. Conclude with `IsDedekindDomain.inf_prime_pow_eq_prod _ _ _ (fun P _ => P.prime) (fun P _ Q _ h e => h (HeightOneSpectrum.ext e))`.

Establish `hmem : ∀ z : 𝓞 I.E, (∀ P ∈ primesG I g hg, z ∈ P.asIdeal ^ N) → z ∈ Ideal.span {(g : 𝓞 I.E)}`. Introduce `z hz`. Apply `hN` to reduce the goal to its premises. Rewrite using `[← key]`. Conclude with `(Ideal.span_singleton_le_iff_mem _).mp (Finset.le_inf fun P hP => (Ideal.span_singleton_le_iff_mem _).mpr (hz P hP))`.

Use `⟨θ, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e : ((θ * θ - θ : 𝓞 I.E) : I.E) = (θ : I.E) * θ - θ` using `by push_cast; ring`. Rewrite using `[← e]`. Conclude with `sk_GE_of_mem_span_natCast I g _ (hmem _ fun P hP => (hloc P hP).1)`. Establish `e : ((θ * sg I θ : 𝓞 I.E) : I.E) = (θ : I.E) * star (θ : I.E)`.

Rewrite using `[← sg_coe]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← e]`. Conclude with `sk_GE_of_mem_span_natCast I g _ (hmem _ fun P hP => (hloc P hP).2.1)`.

Establish `e : ((1 - θ - sg I θ : 𝓞 I.E) : I.E) = 1 - (θ : I.E) - star (θ : I.E)`. Rewrite using `[← sg_coe]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← e]`.

Conclude with `sk_GE_of_mem_span_natCast I g _ (hmem _ fun P hP => (hloc P hP).2.2)`.
-/
theorem theta_series_existence : PI.ScRefExists.Sk.ThetaEx := by
  intro I g hg hS
  classical
  letI : LinearOrder (HeightOneSpectrum (𝓞 I.E)) := by
    first
      | exact linearOrderOfSTO WellOrderingRel
      | exact IsWellOrder.linearOrder WellOrderingRel
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (∏ P ∈ primesG I g hg, P.asIdeal) ^ N ≤ Ideal.span {(g : 𝓞 I.E)} := by
    first
      | exact Ideal.exists_pow_le_of_le_radical_of_fg (prod_le_radical I g hg) (IsNoetherian.noetherian _)
      | exact Ideal.exists_pow_le_of_le_radical_of_fg (IsNoetherian.noetherian _) (prod_le_radical I g hg)
  obtain ⟨θ, hθ⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := primesG I g hg)
    (fun P : HeightOneSpectrum (𝓞 I.E) => P.asIdeal) (fun _ => N) (fun P _ => P.prime)
    (fun P _ Q _ h e => h (HeightOneSpectrum.ext e))
    (fun P => if (P : HeightOneSpectrum (𝓞 I.E)) < cj I P then (1 : 𝓞 I.E) else 0)
  have h1 : ∀ P ∈ primesG I g hg, P < cj I P → θ - 1 ∈ P.asIdeal ^ N := by
    intro P hP h
    simpa [h] using hθ P hP
  have h0 : ∀ P ∈ primesG I g hg, ¬ P < cj I P → θ ∈ P.asIdeal ^ N := by
    intro P hP h
    simpa [h] using hθ P hP
  have hcjS : ∀ P ∈ primesG I g hg, cj I P ∈ primesG I g hg := by
    intro P hP
    rw [mem_primesG] at hP ⊢
    rw [mem_cj, map_natCast]
    exact hP
  have hsg : ∀ (P : HeightOneSpectrum (𝓞 I.E)) (z : 𝓞 I.E), z ∈ (cj I P).asIdeal ^ N →
      sg I z ∈ P.asIdeal ^ N := by
    intro P z hz
    have h2 := Ideal.mem_map_of_mem (sg I) hz
    rwa [Ideal.map_pow, show (cj I P).asIdeal = P.asIdeal.comap (sg I) from rfl,
      Ideal.map_comap_of_surjective _ (fun y => ⟨sg I y, sg_sg I y⟩)] at h2
  have hloc : ∀ P ∈ primesG I g hg, θ * θ - θ ∈ P.asIdeal ^ N ∧ θ * sg I θ ∈ P.asIdeal ^ N ∧
      1 - θ - sg I θ ∈ P.asIdeal ^ N := by
    intro P hP
    have hne : cj I P ≠ P := cj_ne I g hg hS P ((mem_primesG I g hg P).mp hP)
    by_cases hlt : P < cj I P
    · have ha := h1 P hP hlt
      have hb : θ ∈ (cj I P).asIdeal ^ N :=
        h0 (cj I P) (hcjS P hP) (by rw [cj_cj]; exact lt_asymm hlt)
      have hb' := hsg P θ hb
      refine ⟨?_, ?_, ?_⟩
      · have e : θ * θ - θ = (θ - 1) * θ := by ring
        rw [e]
        exact Ideal.mul_mem_right _ _ ha
      · exact Ideal.mul_mem_left _ _ hb'
      · have e : 1 - θ - sg I θ = -(θ - 1) - sg I θ := by ring
        rw [e]
        exact Ideal.sub_mem _ (Submodule.neg_mem _ ha) hb'
    · have ha := h0 P hP hlt
      have hlt' : cj I P < cj I (cj I P) := by
        rw [cj_cj]
        exact lt_of_le_of_ne (not_lt.mp hlt) hne
      have hb' := hsg P _ (h1 (cj I P) (hcjS P hP) hlt')
      rw [map_sub, map_one] at hb'
      refine ⟨?_, ?_, ?_⟩
      · have e : θ * θ - θ = θ * (θ - 1) := by ring
        rw [e]
        exact Ideal.mul_mem_right _ _ ha
      · exact Ideal.mul_mem_right _ _ ha
      · have e : 1 - θ - sg I θ = -θ - (sg I θ - 1) := by ring
        rw [e]
        exact Ideal.sub_mem _ (Submodule.neg_mem _ ha) hb'
  have key : (primesG I g hg).inf (fun P : HeightOneSpectrum (𝓞 I.E) => P.asIdeal ^ N) =
      (∏ P ∈ primesG I g hg, P.asIdeal) ^ N := by
    rw [← Finset.prod_pow]
    exact IsDedekindDomain.inf_prime_pow_eq_prod _ _ _ (fun P _ => P.prime)
      (fun P _ Q _ h e => h (HeightOneSpectrum.ext e))
  have hmem : ∀ z : 𝓞 I.E, (∀ P ∈ primesG I g hg, z ∈ P.asIdeal ^ N) →
      z ∈ Ideal.span {(g : 𝓞 I.E)} := by
    intro z hz
    apply hN
    rw [← key]
    exact (Ideal.span_singleton_le_iff_mem _).mp
      (Finset.le_inf fun P hP => (Ideal.span_singleton_le_iff_mem _).mpr (hz P hP))
  refine ⟨θ, ?_, ?_, ?_⟩
  · have e : ((θ * θ - θ : 𝓞 I.E) : I.E) = (θ : I.E) * θ - θ := by push_cast; ring
    rw [← e]
    exact sk_GE_of_mem_span_natCast I g _ (hmem _ fun P hP => (hloc P hP).1)
  · have e : ((θ * sg I θ : 𝓞 I.E) : I.E) = (θ : I.E) * star (θ : I.E) := by
      rw [← sg_coe]; push_cast; ring
    rw [← e]
    exact sk_GE_of_mem_span_natCast I g _ (hmem _ fun P hP => (hloc P hP).2.1)
  · have e : ((1 - θ - sg I θ : 𝓞 I.E) : I.E) = 1 - (θ : I.E) - star (θ : I.E) := by
      rw [← sg_coe]; push_cast; ring
    rw [← e]
    exact sk_GE_of_mem_span_natCast I g _ (hmem _ fun P hP => (hloc P hP).2.2)

end PI.ScRefExists.TH
