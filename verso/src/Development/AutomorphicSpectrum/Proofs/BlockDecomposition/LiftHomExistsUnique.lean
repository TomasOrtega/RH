import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.EtaleLift

/- English proof (translation)
Introduce `hEt h g u hIJ hg hu`. Take `⟨g0, ⟨hg0i, hg0j⟩, hg0u⟩` from `𝓛.univ (B ⧸ J) ((Ideal.Quotient.mk J).comp h) g (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hx)) (fun o x hx => hg o x hx)`. Establish `hcomm : g0.comp (MvPolynomial.eval₂Hom 𝓛.i 𝓛.t) = (Ideal.Quotient.mk J).comp (MvPolynomial.eval₂Hom h u)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`.

Simplify using `only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]`. Conclude with `RingHom.congr_fun hg0i c`. Introduce `k`. Simplify using `only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']`. Rewrite using `[hu k]`.

Conclude with `hg0j (T k) (𝓛.t k) (𝓛.hT k).symm`. Take `⟨F, ⟨hFψ, hFg⟩, hFu⟩` from `hEt _ _ (MvPolynomial.eval₂Hom 𝓛.i 𝓛.t) 𝓛.et (MvPolynomial.eval₂Hom h u) g0 hcomm`. Use `⟨F, ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `RingHom.ext fun c => by simpa using RingHom.congr_fun hFψ (MvPolynomial.C c)`. Conclude with `fun k => by simpa using RingHom.congr_fun hFψ (MvPolynomial.X k)`.

Introduce `r z hz`. Rewrite using `[← hg0j r z hz]`. Conclude with `RingHom.congr_fun hFg z`. Introduce and unpack `f' ⟨hf'i, hf't, hf'j⟩`. Apply `hFu` to reduce the goal to its premises.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`. Simplify using `only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]`. Conclude with `RingHom.congr_fun hf'i c`.

Introduce `k`. Simplify using `only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']`. Conclude with `hf't k`. Apply `hg0u` to reduce the goal to its premises. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[RingHom.comp_assoc, hf'i]`. Introduce `r z hz`. Conclude with `hf'j r z hz`.
-/
theorem lift_hom_existsUnique {O R Λ : Type} [CommRing O] [CommRing R] [CommRing Λ] (a : O →+* R) {d : ℕ}
    (T : Fin d → R) (I : Ideal Λ) (κ : O →+* Λ ⧸ I) (𝓛 : Lift a T Λ I κ) {B : Type} [CommRing B]
    (J : Ideal B) : EtLift J → ∀ (h : Λ →+* B) (g : R →+* B ⧸ J) (u : Fin d → B), I ≤ J.comap h →
    (∀ o x, Ideal.Quotient.mk I x = κ o → g (a o) = Ideal.Quotient.mk J (h x)) →
    (∀ k, Ideal.Quotient.mk J (u k) = g (T k)) →
    ∃! f : 𝓛.D →+* B, f.comp 𝓛.i = h ∧ (∀ k, f (𝓛.t k) = u k) ∧
      ∀ r z, Ideal.Quotient.mk _ z = 𝓛.j r → Ideal.Quotient.mk J (f z) = g r := by
  intro hEt h g u hIJ hg hu
  obtain ⟨g0, ⟨hg0i, hg0j⟩, hg0u⟩ := 𝓛.univ (B ⧸ J) ((Ideal.Quotient.mk J).comp h) g
    (fun x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hx)) (fun o x hx => hg o x hx)
  have hcomm : g0.comp (MvPolynomial.eval₂Hom 𝓛.i 𝓛.t) =
      (Ideal.Quotient.mk J).comp (MvPolynomial.eval₂Hom h u) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      exact RingHom.congr_fun hg0i c
    · intro k
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      rw [hu k]
      exact hg0j (T k) (𝓛.t k) (𝓛.hT k).symm
  obtain ⟨F, ⟨hFψ, hFg⟩, hFu⟩ :=
    hEt _ _ (MvPolynomial.eval₂Hom 𝓛.i 𝓛.t) 𝓛.et (MvPolynomial.eval₂Hom h u) g0 hcomm
  refine ⟨F, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact RingHom.ext fun c => by simpa using RingHom.congr_fun hFψ (MvPolynomial.C c)
  · exact fun k => by simpa using RingHom.congr_fun hFψ (MvPolynomial.X k)
  · intro r z hz
    rw [← hg0j r z hz]
    exact RingHom.congr_fun hFg z
  · rintro f' ⟨hf'i, hf't, hf'j⟩
    apply hFu
    refine ⟨?_, ?_⟩
    · apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
        exact RingHom.congr_fun hf'i c
      · intro k
        simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
        exact hf't k
    · apply hg0u
      refine ⟨?_, ?_⟩
      · rw [RingHom.comp_assoc, hf'i]
      · intro r z hz
        exact hf'j r z hz

end GlobalTheory.CompanionTheory.EtaleLift
