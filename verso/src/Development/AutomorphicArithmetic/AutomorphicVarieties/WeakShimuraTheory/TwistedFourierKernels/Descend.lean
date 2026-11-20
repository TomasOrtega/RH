import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.PrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.H5 GlobalTheory.GalOfCusp

/- English proof (translation)
Introduce `hl` and use `hv ((h _).1 (by simpa using hl))`.
-/
private theorem not_lt_of_not_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ}
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A v) (hv : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    ¬ A.valuation (l : Ω) < 1 := fun hl => hv ((h _).1 (by simpa using hl))

/- English proof (translation)
Introduce `hmem`. Establish `hcard : Nat.card (𝓞 F ⧸ v.asIdeal) = p` using `hn`. Use `haveI : Nontrivial (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top`. Establish `h1 : addOrderOf (1 : 𝓞 F ⧸ v.asIdeal) ∣ p` using `hcard ▸ addOrderOf_dvd_natCard (1 : 𝓞 F ⧸ v.asIdeal)`. Establish `h2 : addOrderOf (1 : 𝓞 F ⧸ v.asIdeal) ∣ l`.

Rewrite using `[addOrderOf_dvd_iff_nsmul_eq_zero, nsmul_one]`. Establish `h0 : Ideal.Quotient.mk v.asIdeal (l : 𝓞 F) = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr hmem`. Simplify using `using h0`. Establish `hne1 : addOrderOf (1 : 𝓞 F ⧸ v.asIdeal) ≠ 1`. Introduce `h`.

Establish `h3 : addOrderOf (1 : 𝓞 F ⧸ v.asIdeal) ∣ 1` using `by rw [h]`. Rewrite `h3` using `[addOrderOf_dvd_iff_nsmul_eq_zero, one_nsmul]`. Conclude with `one_ne_zero h3`. Break down `(Nat.dvd_prime hp).mp h1 with h | h` into its components or cases. Conclude with `hne1 h`.

Rewrite `h2` using `[h]`. Conclude with `hne ((Nat.prime_dvd_prime_iff_eq hp hl).mp h2)`.
-/
private theorem not_mem_of_norm {F : Type} [Field F] [NumberField F] {l p : ℕ} (hl : l.Prime) (hp : p.Prime) (hne : p ≠ l)
    {v : HeightOneSpectrum (𝓞 F)} (hn : normV v = p) : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal := by
  intro hmem
  have hcard : Nat.card (𝓞 F ⧸ v.asIdeal) = p := hn
  haveI : Nontrivial (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
  have h1 : addOrderOf (1 : 𝓞 F ⧸ v.asIdeal) ∣ p := hcard ▸ addOrderOf_dvd_natCard (1 : 𝓞 F ⧸ v.asIdeal)
  have h2 : addOrderOf (1 : 𝓞 F ⧸ v.asIdeal) ∣ l := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero, nsmul_one]
    have h0 : Ideal.Quotient.mk v.asIdeal (l : 𝓞 F) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    simpa using h0
  have hne1 : addOrderOf (1 : 𝓞 F ⧸ v.asIdeal) ≠ 1 := by
    intro h
    have h3 : addOrderOf (1 : 𝓞 F ⧸ v.asIdeal) ∣ 1 := by rw [h]
    rw [addOrderOf_dvd_iff_nsmul_eq_zero, one_nsmul] at h3
    exact one_ne_zero h3
  rcases (Nat.dvd_prime hp).mp h1 with h | h
  · exact hne1 h
  · rw [h] at h2
    exact hne ((Nat.prime_dvd_prime_iff_eq hp hl).mp h2)

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D T c' h K`. Take `⟨hq, hconj, hkerH⟩` from `prFacts K.V`. Establish `hsurj : Function.Surjective K.V.pr` using `hq.surjective`. Establish `hker : K.V.pr.ker ≤ K.β.ker`. Use `le_trans (hkerH K.t.ker inferInstance ?_ ?_ K.t_unr) K.β_t` and prove the remaining obligations.

Conclude with `isClosed_singleton.preimage K.t_cont`. Introduce `g g' hg hmem`. Establish `h1` using `(K.conj g g' hg).2.2`. Rewrite `hmem`, the goal using `[MonoidHom.mem_ker]`. Rewrite `h1` using `[hmem, one_mul]`.

Conclude with `h1`. Set `β₀` to `K.V.pr.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨K.β, hker⟩`. Establish `hcomp : β₀.comp K.V.pr = K.β` using `MonoidHom.liftOfRightInverse_comp _ _ _ _`. Establish `hβ₀ : ∀ g, β₀ (K.V.pr g) = K.β g` using `fun g => DFunLike.congr_fun hcomp g`. Establish `hβt : ∀ g, K.t g = 1 → β₀ (K.V.pr g) = 1`.

Introduce `g hg`. Rewrite using `[hβ₀]`. Conclude with `K.β_t hg`. Establish `hl : l.Prime` using `Fact.out`. Use `⟨β₀, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩, hcomp⟩` and prove the remaining obligations.

Introduce `x`. Take `⟨g, rfl⟩` from `hsurj x`. Take `⟨g', hg', hc⟩` from `hconj g`. Rewrite using `[hc]`. Establish `e : β₀ (K.V.pr g') * β₀ (K.V.pr g) = 1`.

Rewrite using `[hβ₀, hβ₀, mul_comm]`. Conclude with `(K.conj g g' hg').2.1`. Conclude with `e`. Introduce `u x hx`. Take `⟨w, hw⟩` from `u`.

Take `⟨g, hg, rfl⟩` from `hx`. Conclude with `hβt g (K.t_unr _ (not_lt_of_not_mem (K.s.hA w) (K.s.St_l w hw)) hg)`. Introduce `x hx`. Take `⟨g, hg, rfl⟩` from `hx`. Conclude with `hβt g (K.t_unr _ (not_lt_of_not_mem (K.s.hA K.s.v0) (not_mem_of_norm hl K.s.p_prime K.s.p_ne K.s.norm_v0_eq_one)) hg)`.

Introduce `v g hg`. Conclude with `hβt _ (K.mu v g hg).2`. Introduce `N s`. Establish `hf : (fun g => Ideal.Quotient.mk (maximalIdeal c'.O ^ N) ((β₀ (K.V.pr g) : c'.O))) = (fun g => Ideal.Quotient.mk (maximalIdeal c'.O ^ N) ((K.β g : c'.O)))` using `funext fun g => by rw [hβ₀]`. Establish `ho : IsOpen (K.V.pr ⁻¹' ((fun x => Ideal.Quotient.mk (maximalIdeal c'.O ^ N) ((β₀ x : c'.O))) ⁻¹' s))` using `by show IsOpen ((fun g => Ideal.Quotient.mk (maximalIdeal c'.O ^ N) ((β₀ (K.V.pr g) : c'.O))) ⁻¹' s)`.

Rewrite using `[hf]`. Conclude with `K.β_cont N s`. Conclude with `hq.isOpen_preimage.mp ho`. Introduce `x`. Take `⟨g, rfl⟩` from `hsurj x`.

Establish `e : ((β₀ (K.V.pr g) : c'.O)) - 1 ∈ maximalIdeal c'.O`. Rewrite using `[hβ₀, ← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, K.β_red, sub_self]`. Conclude with `e`.
-/
theorem UpperTheory.V.Ws.H5.descend :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h), ∃ β₀ : K.V.frame.G₀ →* c'.Oˣ, TwCh K.V.frame β₀ ∧ β₀.comp K.V.pr = K.β := by
  intro Ω _ _ _ l _ c D T c' h K
  obtain ⟨hq, hconj, hkerH⟩ := prFacts K.V
  have hsurj : Function.Surjective K.V.pr := hq.surjective
  have hker : K.V.pr.ker ≤ K.β.ker := by
    refine le_trans (hkerH K.t.ker inferInstance ?_ ?_ K.t_unr) K.β_t
    · exact isClosed_singleton.preimage K.t_cont
    · intro g g' hg hmem
      have h1 := (K.conj g g' hg).2.2
      rw [MonoidHom.mem_ker] at hmem ⊢
      rw [hmem, one_mul] at h1
      exact h1
  let β₀ := K.V.pr.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨K.β, hker⟩
  have hcomp : β₀.comp K.V.pr = K.β := MonoidHom.liftOfRightInverse_comp _ _ _ _
  have hβ₀ : ∀ g, β₀ (K.V.pr g) = K.β g := fun g => DFunLike.congr_fun hcomp g
  have hβt : ∀ g, K.t g = 1 → β₀ (K.V.pr g) = 1 := by
    intro g hg
    rw [hβ₀]
    exact K.β_t hg
  have hl : l.Prime := Fact.out
  refine ⟨β₀, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩, hcomp⟩
  · intro x
    obtain ⟨g, rfl⟩ := hsurj x
    obtain ⟨g', hg', hc⟩ := hconj g
    rw [hc]
    have e : β₀ (K.V.pr g') * β₀ (K.V.pr g) = 1 := by
      rw [hβ₀, hβ₀, mul_comm]
      exact (K.conj g g' hg').2.1
    exact e
  · intro u x hx
    obtain ⟨w, hw⟩ := u
    obtain ⟨g, hg, rfl⟩ := hx
    exact hβt g (K.t_unr _ (not_lt_of_not_mem (K.s.hA w) (K.s.St_l w hw)) hg)
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := hx
    exact hβt g (K.t_unr _ (not_lt_of_not_mem (K.s.hA K.s.v0) (not_mem_of_norm hl K.s.p_prime K.s.p_ne K.s.norm_v0_eq_one)) hg)
  · intro v g hg
    exact hβt _ (K.mu v g hg).2
  · intro N s
    have hf : (fun g => Ideal.Quotient.mk (maximalIdeal c'.O ^ N) ((β₀ (K.V.pr g) : c'.O))) = (fun g => Ideal.Quotient.mk (maximalIdeal c'.O ^ N) ((K.β g : c'.O))) := funext fun g => by rw [hβ₀]
    have ho : IsOpen (K.V.pr ⁻¹' ((fun x => Ideal.Quotient.mk (maximalIdeal c'.O ^ N) ((β₀ x : c'.O))) ⁻¹' s)) := by
      show IsOpen ((fun g => Ideal.Quotient.mk (maximalIdeal c'.O ^ N) ((β₀ (K.V.pr g) : c'.O))) ⁻¹' s)
      rw [hf]
      exact K.β_cont N s
    exact hq.isOpen_preimage.mp ho
  · intro x
    obtain ⟨g, rfl⟩ := hsurj x
    have e : ((β₀ (K.V.pr g) : c'.O)) - 1 ∈ maximalIdeal c'.O := by
      rw [hβ₀, ← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, K.β_red, sub_self]
    exact e
