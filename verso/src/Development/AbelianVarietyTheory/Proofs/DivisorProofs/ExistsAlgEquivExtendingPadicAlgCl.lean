import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CokLen
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
open scoped TensorProduct
open scoped Classical

namespace GlobalTheory.LKTrip

/- English proof (translation)
Use `⟨AlgEquiv.ofBijective (φ.liftNormal (PadicAlgCl p)) (Algebra.IsAlgebraic.algHom_bijective _), fun x => ?_⟩` and prove the remaining obligations. Conclude with `φ.liftNormal_commutes (PadicAlgCl p) x`.
-/
theorem exists_algEquiv_extending_padicAlgCl {p : ℕ} [Fact p.Prime]
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (φ : E →ₐ[ℚ_[p]] PadicAlgCl p) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ∀ x : E, σ x = φ x := by
  refine ⟨AlgEquiv.ofBijective (φ.liftNormal (PadicAlgCl p))
    (Algebra.IsAlgebraic.algHom_bijective _), fun x => ?_⟩
  exact φ.liftNormal_commutes (PadicAlgCl p) x

/- English proof (translation)
Use `letI : Algebra G.Kq (PadicAlgCl p) := ((algebraMap ℚ_[p] (PadicAlgCl p)).comp G.u).toAlgebra`. Use `haveI : FiniteDimensional G.Kq G.F := Module.Finite.of_restrictScalars_finite ℚ G.Kq G.F`. Set `f : (Σ w : Fin G.m, (G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p)) → (G.F →ₐ[G.Kq] PadicAlgCl p)` to `fun a => { (a.2 : G.Fw a.1 →+* PadicAlgCl p).comp (G.embW a.1) with commutes' := fun x => by`. Establish `h : G.embW a.1 (x : G.F) = algebraMap ℚ_[p] (G.Fw a.1) (G.u x)` using `Subtype.ext (G.emb_over a.1 x)`. Express the relevant statement in the definitionally equal form `a.2 (G.embW a.1 (x : G.F)) = algebraMap ℚ_[p] (PadicAlgCl p) (G.u x)`.

Rewrite using `[h, AlgHom.commutes] }`. Establish `hf : ∀ a x, f a x = a.2 (G.embW a.1 x)` using `fun _ _ => rfl`. Establish `hbij : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, φ⟩ ⟨w', ψ⟩ h`.

Establish `h' : ∀ x, φ (G.embW w x) = ψ (G.embW w' x)` using `fun x => by`. Rewrite using `[← hf ⟨w, φ⟩, h, hf]`. Take `⟨σ, hσ⟩` from `exists_algEquiv_extending_padicAlgCl _ φ`. Take `⟨τ, hτ⟩` from `exists_algEquiv_extending_padicAlgCl _ ψ`. Choose the witnesses or unpack the hypotheses as in `rfl : w = w' := by`.

Use `G.emb_inj w w' (σ.trans τ.symm) (RingHom.ext fun x => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `τ.symm (σ (G.emb w x)) = G.emb w' x`. Rewrite using `[AlgEquiv.symm_apply_eq]`. Conclude with `(hσ (G.embW w x)).trans ((h' x).trans (hτ (G.embW w' x)).symm)`. Choose the witnesses or unpack the hypotheses as in `rfl : φ = ψ := by`.

Use `IntermediateField.adjoin_algHom_ext ℚ_[p] ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `h' x`. Both sides reduce to the same expression. Introduce `τ`.

Take `⟨w, σ, h⟩` from `G.emb_all (τ : G.F →+* PadicAlgCl p) (fun x => τ.commutes x)`. Use `⟨⟨w, (σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p).comp (G.Fw w).val⟩, AlgHom.ext fun x => ?_⟩` and prove the remaining obligations. Conclude with `(DFunLike.congr_fun h x).symm`. Establish `hc` using `Fintype.card_of_bijective hbij`. Rewrite `hc` using `[Fintype.card_sigma, AlgHom.card]`.

Simplify `hc` using `only [AlgHom.card]`.
-/
theorem HTGroup.sum_finrank_Fw_eq_finrank_Kq {p : ℕ} [Fact p.Prime] (G : HTGroup p) :
    ∑ w : Fin G.m, Module.finrank ℚ_[p] (G.Fw w) = Module.finrank G.Kq G.F := by
  letI : Algebra G.Kq (PadicAlgCl p) := ((algebraMap ℚ_[p] (PadicAlgCl p)).comp G.u).toAlgebra
  haveI : FiniteDimensional G.Kq G.F := Module.Finite.of_restrictScalars_finite ℚ G.Kq G.F
  let f : (Σ w : Fin G.m, (G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p)) → (G.F →ₐ[G.Kq] PadicAlgCl p) := fun a =>
    { (a.2 : G.Fw a.1 →+* PadicAlgCl p).comp (G.embW a.1) with
      commutes' := fun x => by
        have h : G.embW a.1 (x : G.F) = algebraMap ℚ_[p] (G.Fw a.1) (G.u x) :=
          Subtype.ext (G.emb_over a.1 x)
        change a.2 (G.embW a.1 (x : G.F)) = algebraMap ℚ_[p] (PadicAlgCl p) (G.u x)
        rw [h, AlgHom.commutes] }
  have hf : ∀ a x, f a x = a.2 (G.embW a.1 x) := fun _ _ => rfl
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨w, φ⟩ ⟨w', ψ⟩ h
      have h' : ∀ x, φ (G.embW w x) = ψ (G.embW w' x) := fun x => by
        rw [← hf ⟨w, φ⟩, h, hf]
      obtain ⟨σ, hσ⟩ := exists_algEquiv_extending_padicAlgCl _ φ
      obtain ⟨τ, hτ⟩ := exists_algEquiv_extending_padicAlgCl _ ψ
      obtain rfl : w = w' := by
        refine G.emb_inj w w' (σ.trans τ.symm) (RingHom.ext fun x => ?_)
        change τ.symm (σ (G.emb w x)) = G.emb w' x
        rw [AlgEquiv.symm_apply_eq]
        exact (hσ (G.embW w x)).trans ((h' x).trans (hτ (G.embW w' x)).symm)
      obtain rfl : φ = ψ := by
        refine IntermediateField.adjoin_algHom_ext ℚ_[p] ?_
        rintro _ ⟨x, rfl⟩
        exact h' x
      rfl
    · intro τ
      obtain ⟨w, σ, h⟩ := G.emb_all (τ : G.F →+* PadicAlgCl p) (fun x => τ.commutes x)
      refine ⟨⟨w, (σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p).comp (G.Fw w).val⟩, AlgHom.ext fun x => ?_⟩
      exact (DFunLike.congr_fun h x).symm
  have hc := Fintype.card_of_bijective hbij
  rw [Fintype.card_sigma, AlgHom.card] at hc
  simpa only [AlgHom.card] using hc

/- English proof (translation)
Rewrite using `[G.sum_finrank_Fw_eq_finrank_Kq, ← G.hKq.1]`. Conclude with `Module.finrank_mul_finrank ℚ G.Kq G.F`.
-/
theorem HTGroup.two_mul_sum_finrank_Fw (p : ℕ) [Fact p.Prime] (G : HTGroup p) :
    2 * ∑ w : Fin G.m, Module.finrank ℚ_[p] (G.Fw w) = Module.finrank ℚ G.F := by
  rw [G.sum_finrank_Fw_eq_finrank_Kq, ← G.hKq.1]
  exact Module.finrank_mul_finrank ℚ G.Kq G.F

end GlobalTheory.LKTrip
