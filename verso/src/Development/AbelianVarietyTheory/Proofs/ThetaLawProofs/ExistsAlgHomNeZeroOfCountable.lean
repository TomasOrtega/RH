import Mathlib

namespace GlobalTheory

/- English proof (translation)
Use `Fintype.ofFinite σ` as an intermediate fact. Establish `hd : Dense (⋂ p ∈ T, {c : σ → ℂ | MvPolynomial.eval c p ≠ 0})`. Use `dense_biInter_of_isOpen (fun p _ => ?_) hT (fun p hp => ?_)` and prove the remaining obligations. Conclude with `isOpen_ne_fun (MvPolynomial.continuous_eval p) continuous_const`. Introduce `c`.

Assume the negation of the conclusion as `hc`. Establish `hev : (fun c : σ → ℂ => MvPolynomial.eval c p) =ᶠ[nhds c] 0`. Establish `h1 : (closure {c : σ → ℂ | MvPolynomial.eval c p ≠ 0})ᶜ ∈ nhds c` using `isClosed_closure.isOpen_compl.mem_nhds hc`. Use `filter_upwards [h1] with x hx`. Assume the negation of the conclusion as `hx'`.

Conclude with `hx (subset_closure hx')`. Establish `hz` using `(AnalyticOnNhd.eval_mvPolynomial p).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ c) hev`. Establish `: p = 0` using `MvPolynomial.funext fun x => by`. Simplify using `using hz (Set.mem_univ x)`. Conclude with `h0 (this ▸ hp)`.

Take `⟨c, hc⟩` from `hd.nonempty`. Conclude with `⟨c, fun p hp => Set.mem_iInter₂.1 hc p hp⟩`.
-/
theorem exists_eval_ne_zero_of_countable {σ : Type} [Finite σ] (T : Set (MvPolynomial σ ℂ))
    (hT : T.Countable) (h0 : (0 : MvPolynomial σ ℂ) ∉ T) :
    ∃ c : σ → ℂ, ∀ p ∈ T, MvPolynomial.eval c p ≠ 0 := by
  classical
  have := Fintype.ofFinite σ
  have hd : Dense (⋂ p ∈ T, {c : σ → ℂ | MvPolynomial.eval c p ≠ 0}) := by
    refine dense_biInter_of_isOpen (fun p _ => ?_) hT (fun p hp => ?_)
    · exact isOpen_ne_fun (MvPolynomial.continuous_eval p) continuous_const
    · intro c
      by_contra hc
      have hev : (fun c : σ → ℂ => MvPolynomial.eval c p) =ᶠ[nhds c] 0 := by
        have h1 : (closure {c : σ → ℂ | MvPolynomial.eval c p ≠ 0})ᶜ ∈ nhds c :=
          isClosed_closure.isOpen_compl.mem_nhds hc
        filter_upwards [h1] with x hx
        by_contra hx'
        exact hx (subset_closure hx')
      have hz := (AnalyticOnNhd.eval_mvPolynomial p).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ c) hev
      have : p = 0 := MvPolynomial.funext fun x => by
        simpa using hz (Set.mem_univ x)
      exact h0 (this ▸ hp)
  obtain ⟨c, hc⟩ := hd.nonempty
  exact ⟨c, fun p hp => Set.mem_iInter₂.1 hc p hp⟩

/- English proof (translation)
Take `⟨d, g, hinj, hfin⟩` from `exists_finite_inj_algHom_of_fg ℂ E`. Use `letI : Algebra (MvPolynomial (Fin d) ℂ) E := g.toRingHom.toAlgebra`. Use `haveI : Module.Finite (MvPolynomial (Fin d) ℂ) E := hfin`. Establish `hn : ∀ r : E, r ≠ 0 → ∃ n : MvPolynomial (Fin d) ℂ, n ≠ 0 ∧ algebraMap (MvPolynomial (Fin d) ℂ) E n ∈ Ideal.span {r}`. Introduce `r hr`.

Use `Ideal.comap_ne_bot_of_integral_mem (R := MvPolynomial (Fin d) ℂ) (I := Ideal.span {r}) hr (Ideal.mem_span_singleton_self r) (Algebra.IsIntegral.isIntegral r)` as an intermediate fact. Take `⟨n, hn, hn0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot this`. Conclude with `⟨n, hn0, hn⟩`. Use `choose! n hn0 hnr using hn`. Establish `hne : ∀ r ∈ T, r ≠ 0` using `fun r hr h => h0 (h ▸ hr)`.

Take `⟨c, hc⟩` from `exists_eval_ne_zero_of_countable (n '' T) (hT.image n) (by`. Introduce and unpack `⟨r, hr, h⟩`. Conclude with `hn0 r (hne r hr) h)`. Establish `hsurj : Function.Surjective (MvPolynomial.eval c : MvPolynomial (Fin d) ℂ →+* ℂ)` using `fun z => ⟨MvPolynomial.C z, by simp⟩`. Use `haveI hmax : (RingHom.ker (MvPolynomial.eval c : MvPolynomial (Fin d) ℂ →+* ℂ)).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj`.

Take `⟨Q, hQ, hQp⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := E) (RingHom.ker (MvPolynomial.eval c : MvPolynomial (Fin d) ℂ →+* ℂ)) (by`. Establish `: RingHom.ker (algebraMap (MvPolynomial (Fin d) ℂ) E) = ⊥` using `(RingHom.injective_iff_ker_eq_bot _).1 hinj`. Rewrite using `[this]`. Conclude with `bot_le)`. Use `letI : Field (E ⧸ Q) := Ideal.Quotient.field Q`.

Use `haveI : Module.Finite ℂ (E ⧸ Q) := finite_of_finite_type_of_isJacobsonRing ℂ (E ⧸ Q)`. Establish `hbij : Function.Bijective (Algebra.ofId ℂ (E ⧸ Q))` using `IsAlgClosed.algebraMap_bijective_of_isIntegral`. Set `e : ℂ ≃ₐ[ℂ] (E ⧸ Q)` to `AlgEquiv.ofBijective _ hbij`. Use `⟨(e.symm : (E ⧸ Q) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ Q), fun r hr h => ?_⟩` and prove the remaining obligations. Establish `h1 : Ideal.Quotient.mk Q r = 0`.

Apply `e.symm.injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `h`. Establish `h2 : r ∈ Q` using `Ideal.Quotient.eq_zero_iff_mem.1 h1`. Establish `h3 : n r ∈ Q.comap (algebraMap (MvPolynomial (Fin d) ℂ) E)` using `(Ideal.span_singleton_le_iff_mem Q).2 h2 (hnr r (hne r hr))`.

Rewrite `h3` using `[hQp]`. Conclude with `hc (n r) ⟨r, hr, rfl⟩ h3`.
-/
theorem exists_algHom_ne_zero_of_countable (E : Type) [CommRing E] [IsDomain E] [Algebra ℂ E]
    [Algebra.FiniteType ℂ E] (T : Set E) (hT : T.Countable) (h0 : (0 : E) ∉ T) :
    ∃ s : E →ₐ[ℂ] ℂ, ∀ r ∈ T, s r ≠ 0 := by
  classical
  obtain ⟨d, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ E
  letI : Algebra (MvPolynomial (Fin d) ℂ) E := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin d) ℂ) E := hfin
  have hn : ∀ r : E, r ≠ 0 → ∃ n : MvPolynomial (Fin d) ℂ, n ≠ 0 ∧
      algebraMap (MvPolynomial (Fin d) ℂ) E n ∈ Ideal.span {r} := by
    intro r hr
    have := Ideal.comap_ne_bot_of_integral_mem (R := MvPolynomial (Fin d) ℂ)
      (I := Ideal.span {r}) hr (Ideal.mem_span_singleton_self r)
      (Algebra.IsIntegral.isIntegral r)
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot this
    exact ⟨n, hn0, hn⟩
  choose! n hn0 hnr using hn
  have hne : ∀ r ∈ T, r ≠ 0 := fun r hr h => h0 (h ▸ hr)
  obtain ⟨c, hc⟩ := exists_eval_ne_zero_of_countable (n '' T) (hT.image n) (by
    rintro ⟨r, hr, h⟩
    exact hn0 r (hne r hr) h)
  have hsurj : Function.Surjective (MvPolynomial.eval c : MvPolynomial (Fin d) ℂ →+* ℂ) :=
    fun z => ⟨MvPolynomial.C z, by simp⟩
  haveI hmax : (RingHom.ker (MvPolynomial.eval c : MvPolynomial (Fin d) ℂ →+* ℂ)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ hsurj
  obtain ⟨Q, hQ, hQp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := E)
    (RingHom.ker (MvPolynomial.eval c : MvPolynomial (Fin d) ℂ →+* ℂ)) (by
      have : RingHom.ker (algebraMap (MvPolynomial (Fin d) ℂ) E) = ⊥ :=
        (RingHom.injective_iff_ker_eq_bot _).1 hinj
      rw [this]
      exact bot_le)
  letI : Field (E ⧸ Q) := Ideal.Quotient.field Q
  haveI : Module.Finite ℂ (E ⧸ Q) := finite_of_finite_type_of_isJacobsonRing ℂ (E ⧸ Q)
  have hbij : Function.Bijective (Algebra.ofId ℂ (E ⧸ Q)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : ℂ ≃ₐ[ℂ] (E ⧸ Q) := AlgEquiv.ofBijective _ hbij
  refine ⟨(e.symm : (E ⧸ Q) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ Q), fun r hr h => ?_⟩
  have h1 : Ideal.Quotient.mk Q r = 0 := by
    apply e.symm.injective
    rw [map_zero]
    exact h
  have h2 : r ∈ Q := Ideal.Quotient.eq_zero_iff_mem.1 h1
  have h3 : n r ∈ Q.comap (algebraMap (MvPolynomial (Fin d) ℂ) E) :=
    (Ideal.span_singleton_le_iff_mem Q).2 h2 (hnr r (hne r hr))
  rw [hQp] at h3
  exact hc (n r) ⟨r, hr, rfl⟩ h3

end GlobalTheory
