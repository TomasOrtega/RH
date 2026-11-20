import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Take `⟨s, hs⟩` from `hg.bij.2 a`. Use `(RingHom.mem_range).2 ⟨s, ?_⟩` and prove the remaining obligations. Use `show (X.presheaf.stalkSpecializes (specializes_refl (genPt ξ)) ≫ Scheme.stalkClosedPointTo ξ).hom s = a`. Rewrite using `[TopCat.Presheaf.stalkSpecializes_refl]`. Conclude with `hs`.
-/
theorem regAt_generic_eq_top {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hg : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩ := by
  obtain ⟨s, hs⟩ := hg.bij.2 a
  refine (RingHom.mem_range).2 ⟨s, ?_⟩
  show (X.presheaf.stalkSpecializes (specializes_refl (genPt ξ)) ≫ Scheme.stalkClosedPointTo ξ).hom s = a
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact hs

/- English proof (translation)
Set `p₀ : Cpt ξ` to `⟨genPt ξ, specializes_rfl⟩`. Establish `hreg : ∀ a : Ω, a ∈ regAt ξ p₀` using `fun a => regAt_generic_eq_top hT.gen a`. Take `⟨k, hk⟩` from `hT.cover p₀`. Unfold `Lat.IsVB Lat.IsVBOn at hV`. Take `⟨U, hU, b, hbV, hbF⟩` from `hV p₀ (Set.mem_univ _)`.

Take `⟨-, hLp⟩` from `hbF p₀ (Set.mem_univ _) hU`. Take `⟨-, hG2⟩` from `hG`. Establish `hw0 : ∀ i : Fin r, ∃ w : Module.Dual Ω E, ∀ l, w (c l) = if i = l then 1 else 0`. Introduce `i`. Take `⟨w, hwf⟩` from `LinearMap.exists_extend ((Module.Basis.span hc).coord i)`.

Use `⟨w, fun l => ?_⟩` and prove the remaining obligations. Establish `h1 : w (c l) = (Module.Basis.span hc).coord i (Module.Basis.span hc l)`. Rewrite using `[← hwf]`. Simplify using `[Module.Basis.span_apply]`. Rewrite using `[h1, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`.

Distinguish the cases in `h : i = l`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`. Use `choose w hw using hw0`.

Establish `hg0 : ∀ i, ∃ g : Fin n → Ω, (∀ j, g j ∈ regAt ξ p₀) ∧ ∀ e ∈ L p₀, w i e = ∑ j, g j * (φ j e / x k ^ m)` using `fun i => hG2 p₀ k hk (w i) (fun e _ => hreg _)`. Use `choose g hgr hg using hg0`. Establish `key : ∀ i, ∀ e ∈ V, w i e = ∑ j, g i j / x k ^ m * φ j e`. Introduce `i`. Take `⟨ψ, hψdef⟩ : ∃ ψ : E →ₗ[Ω] Ω, ψ = ∑ j, (g i j / x k ^ m) • φ j` from `⟨_, rfl⟩`.

Establish `hψ : ∀ e, ψ e = ∑ j, g i j / x k ^ m * φ j e`. Introduce `e`. Rewrite using `[hψdef]`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]`. Establish `heq : Set.EqOn (w i) ψ (Set.range b)`.

Introduce and unpack `_ ⟨t, rfl⟩`. Establish `hbt : b t ∈ L p₀`. Rewrite using `[hLp]`. Conclude with `Submodule.subset_span ⟨t, rfl⟩`. Rewrite using `[hg i (b t) hbt, hψ]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Introduce `e he`. Rewrite `he` using `[← hbV]`. Rewrite using `[LinearMap.eqOn_span' heq he, hψ]`.

Use `⟨Matrix.of fun i j => g i j / x k ^ m, ?_⟩` and prove the remaining obligations. Use extensionality with `i l`. Establish `hcl : c l ∈ V`. Rewrite using `[← hs]`. Conclude with `Submodule.subset_span ⟨l, rfl⟩`.

Simplify using `only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]`. Rewrite using `[← key i (c l) hcl, hw i l]`.
-/
theorem exists_leftInverse_flagForms (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (r : ℕ)
    (V : Submodule Ω E) (m n : ℕ) (φ : Fin n → Module.Dual Ω E) (c : Fin r → E)
    (hT : CoordTie ℤ ξ x) (hV : L.IsVB r V) (hG : IsTwistGen ξ x L m φ)
    (hc : LinearIndependent Ω c) (hs : Submodule.span Ω (Set.range c) = V) :
    ∃ B : Matrix (Fin r) (Fin n) Ω, B * Matrix.of (fun j l => φ j (c l)) = 1 := by
  let p₀ : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  have hreg : ∀ a : Ω, a ∈ regAt ξ p₀ := fun a => regAt_generic_eq_top hT.gen a
  obtain ⟨k, hk⟩ := hT.cover p₀
  unfold Lat.IsVB Lat.IsVBOn at hV
  obtain ⟨U, hU, b, hbV, hbF⟩ := hV p₀ (Set.mem_univ _)
  obtain ⟨-, hLp⟩ := hbF p₀ (Set.mem_univ _) hU
  obtain ⟨-, hG2⟩ := hG
  have hw0 : ∀ i : Fin r, ∃ w : Module.Dual Ω E, ∀ l, w (c l) = if i = l then 1 else 0 := by
    intro i
    obtain ⟨w, hwf⟩ := LinearMap.exists_extend ((Module.Basis.span hc).coord i)
    refine ⟨w, fun l => ?_⟩
    have h1 : w (c l) = (Module.Basis.span hc).coord i (Module.Basis.span hc l) := by
      rw [← hwf]
      simp [Module.Basis.span_apply]
    rw [h1, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : i = l
    · subst h
      simp
    · simp [h, Ne.symm h]
  choose w hw using hw0
  have hg0 : ∀ i, ∃ g : Fin n → Ω, (∀ j, g j ∈ regAt ξ p₀) ∧
      ∀ e ∈ L p₀, w i e = ∑ j, g j * (φ j e / x k ^ m) :=
    fun i => hG2 p₀ k hk (w i) (fun e _ => hreg _)
  choose g hgr hg using hg0
  have key : ∀ i, ∀ e ∈ V, w i e = ∑ j, g i j / x k ^ m * φ j e := by
    intro i
    obtain ⟨ψ, hψdef⟩ : ∃ ψ : E →ₗ[Ω] Ω, ψ = ∑ j, (g i j / x k ^ m) • φ j := ⟨_, rfl⟩
    have hψ : ∀ e, ψ e = ∑ j, g i j / x k ^ m * φ j e := by
      intro e
      rw [hψdef]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    have heq : Set.EqOn (w i) ψ (Set.range b) := by
      rintro _ ⟨t, rfl⟩
      have hbt : b t ∈ L p₀ := by
        rw [hLp]
        exact Submodule.subset_span ⟨t, rfl⟩
      rw [hg i (b t) hbt, hψ]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    intro e he
    rw [← hbV] at he
    rw [LinearMap.eqOn_span' heq he, hψ]
  refine ⟨Matrix.of fun i j => g i j / x k ^ m, ?_⟩
  ext i l
  have hcl : c l ∈ V := by
    rw [← hs]
    exact Submodule.subset_span ⟨l, rfl⟩
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [← key i (c l) hcl, hw i l]

end GlobalTheory.CompanionTheory.Ar.FlagBun
