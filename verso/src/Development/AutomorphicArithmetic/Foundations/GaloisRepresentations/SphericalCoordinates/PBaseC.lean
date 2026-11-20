import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange

noncomputable section

open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open scoped Classical

namespace UpperTheory.Gal.W2

/- English proof (translation)
Introduce `h`. Take `⟨r, hr⟩` from `Complex.conj_eq_iff_real.1 h`. Establish `h0` using `D.ρc_root`. Rewrite `h0` using `[hr]`. Establish `h1 : (r : ℝ) ^ 2 - D.tr * r + D.nm = 0` using `by exact_mod_cast h0`.

Establish `h2 : ((D.tr : ℝ)) ^ 2 - 4 * D.nm < 0` using `by exact_mod_cast D.disc_neg`. Use polynomial arithmetic with `[sq_nonneg (2 * r - D.tr)]`.
-/
private theorem rho_ne_conj {p : ℕ} [Fact p.Prime] (D : Datum p) :
    (starRingEnd ℂ) D.ρc ≠ D.ρc := by
  intro h
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h
  have h0 := D.ρc_root
  rw [hr] at h0
  have h1 : (r : ℝ) ^ 2 - D.tr * r + D.nm = 0 := by exact_mod_cast h0
  have h2 : ((D.tr : ℝ)) ^ 2 - 4 * D.nm < 0 := by exact_mod_cast D.disc_neg
  nlinarith [sq_nonneg (2 * r - D.tr)]

/- English proof (translation)
Establish `hne : ComplexEmbedding.conjugate t₀ ≠ t₀`. Introduce `h`. Apply `rho_ne_conj D` to reduce the goal to its premises. Use `congrArg (fun τ : D.F →+* ℂ => τ (D.ω : D.F)) h` as an intermediate fact. Simplify `this` using `[ComplexEmbedding.conjugate_coe_eq, h₀]`.

Establish `hc : (ComplexEmbedding.conjugate t₀) (D.ω : D.F) ≠ D.ρc`. Simplify `rho_ne_conj D` using `[ComplexEmbedding.conjugate_coe_eq, h₀]`. Establish `key : ∀ τ : D.F →+* ℂ, (typeMult D.n t₀ (epsD D) τ : ℂ) * τ (c : D.F) = (if τ = t₀ then τ (c : D.F) else 0) + (if τ (D.ω : D.F) ≠ D.ρc then (D.n : ℂ) * τ (c : D.F) else 0) - (if τ = ComplexEmbedding.conjugate t₀ then τ (c : D.F) else 0)`. Introduce `τ`. Unfold `typeMult epsD`.

Distinguish the cases in `h1 : τ = t₀`. Substitute `h1` using the available equality. Simplify using `[hne.symm, h₀]`. Distinguish the cases in `h2 : τ = ComplexEmbedding.conjugate t₀`. Substitute `h2` using the available equality.

Establish `hc' : (starRingEnd ℂ) (t₀ (D.ω : D.F)) ≠ D.ρc`. Simplify `hc` using `[ComplexEmbedding.conjugate_coe_eq]`. Simplify using `[h1, hc', Nat.cast_sub hn]`. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `by_cases h3 : τ (D.ω : D.F) = D.ρc <;> simp [h1, h2, h3]`.

Rewrite using `[Finset.sum_congr rfl fun τ _ => key τ, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_filter]`. Simplify using `[ComplexEmbedding.conjugate_coe_eq]`.
-/
private theorem type_sum {p : ℕ} [Fact p.Prime] (D : Datum p) (t₀ : D.F →+* ℂ) (h₀ : t₀ (D.ω : D.F) = D.ρc)
    (hn : 1 ≤ D.n) (c : 𝓞 D.F) :
    ∑ τ : D.F →+* ℂ, (typeMult D.n t₀ (epsD D) τ : ℂ) * τ (c : D.F) =
      t₀ (c : D.F) + ∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ D.ρc), (D.n : ℂ) * τ (c : D.F) -
        (starRingEnd ℂ) (t₀ (c : D.F)) := by
  have hne : ComplexEmbedding.conjugate t₀ ≠ t₀ := by
    intro h
    apply rho_ne_conj D
    have := congrArg (fun τ : D.F →+* ℂ => τ (D.ω : D.F)) h
    simpa [ComplexEmbedding.conjugate_coe_eq, h₀] using this
  have hc : (ComplexEmbedding.conjugate t₀) (D.ω : D.F) ≠ D.ρc := by
    simpa [ComplexEmbedding.conjugate_coe_eq, h₀] using rho_ne_conj D
  have key : ∀ τ : D.F →+* ℂ, (typeMult D.n t₀ (epsD D) τ : ℂ) * τ (c : D.F) =
      (if τ = t₀ then τ (c : D.F) else 0) + (if τ (D.ω : D.F) ≠ D.ρc then (D.n : ℂ) * τ (c : D.F) else 0) -
        (if τ = ComplexEmbedding.conjugate t₀ then τ (c : D.F) else 0) := by
    intro τ
    unfold typeMult epsD
    by_cases h1 : τ = t₀
    · subst h1
      simp [hne.symm, h₀]
    · by_cases h2 : τ = ComplexEmbedding.conjugate t₀
      · subst h2
        have hc' : (starRingEnd ℂ) (t₀ (D.ω : D.F)) ≠ D.ρc := by
          simpa [ComplexEmbedding.conjugate_coe_eq] using hc
        simp [h1, hc', Nat.cast_sub hn]
        ring
      · by_cases h3 : τ (D.ω : D.F) = D.ρc <;> simp [h1, h2, h3]
  rw [Finset.sum_congr rfl fun τ _ => key τ, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_filter]
  simp [ComplexEmbedding.conjugate_coe_eq]

/- English proof (translation)
Introduce `p _ D ha hm t₀ ht ρ hs gb hst`. Establish `hsub : Subsingleton (Fin D.a)` using `by rw [ha]; infer_instance`. Set `i₀ : Fin D.a` to `⟨0, by omega⟩`. Set `b : Base D ℂ` to `{ unit := fun k hk => by`. Use `isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 fun h => ?_)` and prove the remaining obligations.

Substitute `h` using the available equality. Conclude with `(Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left p |>.1 hk)`. Use `ρ := gb.ρ`. Use `ρ_root := gb.ρ_root`. Use `t := gb.t`.

Use `t_ω := gb.t_ω`. Use `comax := fun i j hij => absurd (hsub.elim i j) hij`. Use `apart := fun i j hij => absurd (hsub.elim i j) hij }`. Use `⟨b, rfl, fun i => (RingHom.id_comp _).symm, ?_⟩` and prove the remaining obligations. Introduce `c`.

Establish `hti : b.t i₀ c = t₀ (c : D.F)`. Use `hst.2 i₀ c` as an intermediate fact. Rewrite `this` using `[ht i₀]`. Conclude with `this`. Establish `hb : b.ρ = D.ρc` using `hst.1`.

Establish `h₀ : t₀ (D.ω : D.F) = D.ρc` using `by rw [← ht i₀]; exact D.tau_ω i₀`. Rewrite using `[hs.tr c, type_sum D t₀ h₀ hs.pos c, hm, Fintype.sum_subsingleton _ i₀, Fintype.sum_subsingleton _ i₀]`. Simplify using `[hti, hb]`.
-/
theorem baseC_of : BaseC := by
  intro p _ D ha hm t₀ ht ρ hs gb hst
  have hsub : Subsingleton (Fin D.a) := by rw [ha]; infer_instance
  let i₀ : Fin D.a := ⟨0, by omega⟩
  let b : Base D ℂ :=
    { unit := fun k hk => by
        refine isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 fun h => ?_)
        subst h
        exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left p |>.1 hk)
      ρ := gb.ρ
      ρ_root := gb.ρ_root
      t := gb.t
      t_ω := gb.t_ω
      comax := fun i j hij => absurd (hsub.elim i j) hij
      apart := fun i j hij => absurd (hsub.elim i j) hij }
  refine ⟨b, rfl, fun i => (RingHom.id_comp _).symm, ?_⟩
  intro c
  have hti : b.t i₀ c = t₀ (c : D.F) := by
    have := hst.2 i₀ c
    rw [ht i₀] at this
    exact this
  have hb : b.ρ = D.ρc := hst.1
  have h₀ : t₀ (D.ω : D.F) = D.ρc := by rw [← ht i₀]; exact D.tau_ω i₀
  rw [hs.tr c, type_sum D t₀ h₀ hs.pos c, hm, Fintype.sum_subsingleton _ i₀, Fintype.sum_subsingleton _ i₀]
  simp [hti, hb]

end UpperTheory.Gal.W2
