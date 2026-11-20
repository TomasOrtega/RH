import Development.EtaleCohomology.EtaleSheaves.HensIdemCut

noncomputable section
open Polynomial

namespace LateralTheory.E.LFactorPf

def LEtaleLift : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (A' : Type) [CommRing A']
  [Algebra A A'] [Algebra.Etale A A'] (φ : A' →ₐ[A] A ⧸ I),
  ∃ ψ : A' →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp ψ = φ

/- English proof (translation)
Introduce `A _ I _ f g₀ h₀ hf hg hh hgh e`. Break down `subsingleton_or_nontrivial (A ⧸ I) with hs | hs` into its components or cases. Establish `hI : I = ⊤` using `Ideal.Quotient.subsingleton_iff.mp hs`. Establish `h1 : (1 : A) ∈ (⊥ : Ideal A).jacobson` using `HenselianRing.jac (I := I) (hI ▸ Submodule.mem_top)`. Establish `hu` using `Ideal.mem_jacobson_bot.mp h1 (-1)`.

Establish `hA : Subsingleton A`. Simplify using `at hu`. Conclude with `subsingleton_of_zero_eq_one (by simpa using hu)`. Use `⟨1, 1, monic_one, monic_one, Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩` and prove the remaining obligations. Establish `hn : f.natDegree = g₀.natDegree + h₀.natDegree`.

Rewrite using `[← hg.natDegree_mul hh, ← e, hf.natDegree_map]`. Set `p : MonicDegreeEq A f.natDegree` to `.mk f hf rfl`. Establish `e' : g₀ * h₀ = p.1.map (algebraMap A (A ⧸ I))` using `e.symm`. Set `φ` to `(UniversalCoprimeFactorizationRing.homEquiv (A ⧸ I) _ _ hn p).symm ⟨(.mk g₀ hg rfl, .mk h₀ hh rfl), e', hgh⟩`. Take `⟨ψ, hψ⟩` from `hE A I _ φ`.

Set `q` to `UniversalCoprimeFactorizationRing.homEquiv A _ _ hn p ψ`. Use `⟨q.1.1.1, q.1.2.1, q.1.1.monic, q.1.2.monic, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `q.2.1` as an intermediate fact. Simplify `this.symm` using `[p]`. Use `UniversalCoprimeFactorizationRing.homEquiv_comp_fst A _ _ hn p ψ (Ideal.Quotient.mkₐ A I)` as an intermediate fact.

Rewrite `this` using `[hψ, Equiv.apply_symm_apply]`. Conclude with `congr($(this).1).symm`. Use `UniversalCoprimeFactorizationRing.homEquiv_comp_snd A _ _ hn p ψ (Ideal.Quotient.mkₐ A I)` as an intermediate fact. Rewrite `this` using `[hψ, Equiv.apply_symm_apply]`. Conclude with `congr($(this).1).symm`.
-/
theorem LFactor_of (hE : LEtaleLift) : LateralTheory.E.HensIdemCut.LFactor := by
  intro A _ I _ f g₀ h₀ hf hg hh hgh e
  rcases subsingleton_or_nontrivial (A ⧸ I) with hs | hs
  · have hI : I = ⊤ := Ideal.Quotient.subsingleton_iff.mp hs
    have h1 : (1 : A) ∈ (⊥ : Ideal A).jacobson := HenselianRing.jac (I := I) (hI ▸ Submodule.mem_top)
    have hu := Ideal.mem_jacobson_bot.mp h1 (-1)
    have hA : Subsingleton A := by
      simp at hu
      exact subsingleton_of_zero_eq_one (by simpa using hu)
    refine ⟨1, 1, monic_one, monic_one, Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hn : f.natDegree = g₀.natDegree + h₀.natDegree := by
    rw [← hg.natDegree_mul hh, ← e, hf.natDegree_map]
  let p : MonicDegreeEq A f.natDegree := .mk f hf rfl
  have e' : g₀ * h₀ = p.1.map (algebraMap A (A ⧸ I)) := e.symm
  let φ := (UniversalCoprimeFactorizationRing.homEquiv (A ⧸ I) _ _ hn p).symm
    ⟨(.mk g₀ hg rfl, .mk h₀ hh rfl), e', hgh⟩
  obtain ⟨ψ, hψ⟩ := hE A I _ φ
  let q := UniversalCoprimeFactorizationRing.homEquiv A _ _ hn p ψ
  refine ⟨q.1.1.1, q.1.2.1, q.1.1.monic, q.1.2.monic, ?_, ?_, ?_⟩
  · have := q.2.1
    simpa [p] using this.symm
  · have := UniversalCoprimeFactorizationRing.homEquiv_comp_fst A _ _ hn p ψ (Ideal.Quotient.mkₐ A I)
    rw [hψ, Equiv.apply_symm_apply] at this
    exact congr($(this).1).symm
  · have := UniversalCoprimeFactorizationRing.homEquiv_comp_snd A _ _ hn p ψ (Ideal.Quotient.mkₐ A I)
    rw [hψ, Equiv.apply_symm_apply] at this
    exact congr($(this).1).symm

end LateralTheory.E.LFactorPf
