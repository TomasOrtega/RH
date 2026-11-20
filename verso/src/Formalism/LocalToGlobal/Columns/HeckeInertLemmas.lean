import Formalism.LocalToGlobal.Columns.HeckeInert
import Formalism.LocalToGlobal.Columns.GSetLemmas
import Formalism.LocalToGlobal.Columns.UnipotentRightActionFunctionsW

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module Pointwise

section Fin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

/- English proof (translation)
Establish `hPk : P ^ s.sum ≠ ⊥` using `pow_ne_zero _ hP`. Take `⟨a, haP, ha⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hPk`. Establish `hI : Ideal.span {a} * P ^ s.sum ≠ ⊥`. Rewrite using `[Ne, Ideal.mul_eq_bot, not_or]`. Conclude with `⟨fun h => ha (Ideal.span_singleton_eq_bot.1 h), hPk⟩`.

Establish `hfin` using `finite_between ((Ideal.span {a} * P ^ s.sum) • d.1.N) d.1.N (finite_quot_smul d.1.N d.2.lat.fg _ hI)`. Use `Set.Finite.of_injOn (f := fun e : DecoSet E n ST SG => Ideal.span {a} • e.1.N) ?_ ?_ hfin` and prove the remaining obligations. Introduce `e he`. Take `⟨h1, h2⟩` from `he.1.smul_le`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_smul]`. Conclude with `Submodule.smul_mono le_rfl h1`. Conclude with `(Submodule.smul_mono ((Ideal.span_singleton_le_iff_mem _).2 haP) le_rfl).trans h2`. Introduce `e he e' he' h`. Establish `hN : e.1.N = e'.1.N`.

Simplify using `only [Submodule.ideal_span_singleton_smul] at h`. Establish `hinj : Function.Injective fun x : Sp E n => a • x` using `smul_right_injective (Sp E n) ha`. Establish `hsub : ∀ A B : Submodule (𝓞 E) (Sp E n), a • A = a • B → A ≤ B`. Introduce `A B hAB x hx`. Establish `: a • x ∈ a • B` using `hAB ▸ Submodule.smul_mem_pointwise_smul x a A hx`.

Take `⟨y, hy, hyx⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 this`. Rewrite using `[← hinj hyx]` and apply the resulting hypothesis. Conclude with `le_antisymm (hsub _ _ h) (hsub _ _ h.symm)`. Conclude with `Subtype.ext (Deco.ext hN (he.2.1.trans he'.2.1.symm) (he.2.2.trans he'.2.2.symm))`.
-/
theorem DecoSet.inertSet_finite {P : Ideal (𝓞 E)} (hP : P ≠ ⊥) (s : List ℕ) (d : DecoSet E n ST SG) :
    (d.inertSet P s).Finite := by
  have hPk : P ^ s.sum ≠ ⊥ := pow_ne_zero _ hP
  obtain ⟨a, haP, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPk
  have hI : Ideal.span {a} * P ^ s.sum ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    exact ⟨fun h => ha (Ideal.span_singleton_eq_bot.1 h), hPk⟩
  have hfin := finite_between ((Ideal.span {a} * P ^ s.sum) • d.1.N) d.1.N
    (finite_quot_smul d.1.N d.2.lat.fg _ hI)
  refine Set.Finite.of_injOn (f := fun e : DecoSet E n ST SG => Ideal.span {a} • e.1.N) ?_ ?_ hfin
  · intro e he
    obtain ⟨h1, h2⟩ := he.1.smul_le
    refine ⟨?_, ?_⟩
    · rw [mul_smul]
      exact Submodule.smul_mono le_rfl h1
    · exact (Submodule.smul_mono ((Ideal.span_singleton_le_iff_mem _).2 haP) le_rfl).trans h2
  · intro e he e' he' h
    have hN : e.1.N = e'.1.N := by
      simp only [Submodule.ideal_span_singleton_smul] at h
      have hinj : Function.Injective fun x : Sp E n => a • x := smul_right_injective (Sp E n) ha
      have hsub : ∀ A B : Submodule (𝓞 E) (Sp E n), a • A = a • B → A ≤ B := by
        intro A B hAB x hx
        have : a • x ∈ a • B := hAB ▸ Submodule.smul_mem_pointwise_smul x a A hx
        obtain ⟨y, hy, hyx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 this
        rwa [← hinj hyx]
      exact le_antisymm (hsub _ _ h) (hsub _ _ h.symm)
    exact Subtype.ext (Deco.ext hN (he.2.1.trans he'.2.1.symm) (he.2.2.trans he'.2.2.symm))

/- English proof (translation)
Unfold `DecoSet.inertNb`. Rewrite using `[dif_pos (DecoSet.inertSet_finite hP s d), Set.Finite.mem_toFinset]`.
-/
theorem DecoSet.mem_inertNb {P : Ideal (𝓞 E)} (hP : P ≠ ⊥) (s : List ℕ) (d e : DecoSet E n ST SG) :
    e ∈ d.inertNb P s ↔ e ∈ d.inertSet P s := by
  unfold DecoSet.inertNb
  rw [dif_pos (DecoSet.inertSet_finite hP s d), Set.Finite.mem_toFinset]

/- English proof (translation)
Use `symm`. Conclude with `Finset.sum_equiv (MulAction.toPerm g) (fun e => (DecoSet.smul_mem_inertNb_iff g).symm) (fun e _ => rfl)`.
-/
theorem DecoSet.sum_inertNb_smul {M : Type} [AddCommMonoid M] (P : Ideal (𝓞 E)) (s : List ℕ)
    (g : UF E n × GLG E n SG) (d : DecoSet E n ST SG) (ψ : DecoSet E n ST SG → M) :
    ∑ e ∈ (g • d).inertNb P s, ψ e = ∑ e ∈ d.inertNb P s, ψ (g • e) := by
  symm
  exact Finset.sum_equiv (MulAction.toPerm g) (fun e => (DecoSet.smul_mem_inertNb_iff g).symm) (fun e _ => rfl)

end Fin

section Op

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}

end Op

end Formalism.L2.Col
