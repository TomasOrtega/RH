import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatakeGLOfHasSatakeParametersPrincipalSeries
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeVectorIffInverseDoubleCosets
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalReciprocityUnramifiedSpherical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.HeckeEigConj

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Both sides reduce to the same expression. Consider the case `tmul a b`. Simplify using `only [SplitPlace.proj, conjAL, GlobalTheory.HeckeFrob.conjSplit, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]`.

Both sides reduce to the same expression. Consider the case `add a b ha hb => rw [map_add, map_add, map_add, ha, hb]`. Both sides reduce to the same expression.
-/
theorem proj_conjSplit {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (z : AL L) :
    (GlobalTheory.HeckeFrob.conjSplit s).proj z = s.proj (conjAL L z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | tmul a b =>
    simp only [SplitPlace.proj, conjAL, GlobalTheory.HeckeFrob.conjSplit, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]; rfl

/- English proof (translation)
Use `Units.ext (Matrix.ext fun a b => ?_)` and prove the remaining obligations. Rewrite using `[GlobalTheory.LFun.ConjPlace.invT_val, ← map_inv]`. Establish `h` using `congrFun₂ (GlobalTheory.FinTypCount.inv_val x) b a`. Express the relevant statement in the definitionally equal form `i ((GlobalTheory.HeckeFrob.conjSplit s).proj _) = i (s.proj ((((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix _ _ _) b a))`. Rewrite using `[h, proj_conjSplit]`.

Both sides reduce to the same expression.
-/
theorem map_loc_conjSplit (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) {K' : Type}
    [Field K'] (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* K') (x : GAf L n) :
    Matrix.GeneralLinearGroup.map i.toRingHom ((GlobalTheory.HeckeFrob.conjSplit s).loc n x) =
      GlobalTheory.LFun.ConjPlace.invT i n (s.loc n x) := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [GlobalTheory.LFun.ConjPlace.invT_val, ← map_inv]
  have h := congrFun₂ (GlobalTheory.FinTypCount.inv_val x) b a
  change i ((GlobalTheory.HeckeFrob.conjSplit s).proj _) = i (s.proj ((((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix _ _ _) b a))
  rw [h, proj_conjSplit]
  rfl

/- English proof (translation)
Use extensionality with `g`. Rewrite using `[GlobalTheory.SplitFlip.mem_KO_iff, GlobalTheory.HeckeScalarSph.mem_GLint_iff]`. Establish `h : ∀ x : w.adicCompletion E, x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ Formalism.UG.Ov E w` using `fun x => (Valuation.mem_integer_iff _ _).trans (GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff w x)`. Simplify using `only [h]`.
-/
theorem KO_eq_KGL (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) = GlobalTheory.LFun.KGL w n := by
  ext g
  rw [GlobalTheory.SplitFlip.mem_KO_iff, GlobalTheory.HeckeScalarSph.mem_GLint_iff]
  have h : ∀ x : w.adicCompletion E, x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ Formalism.UG.Ov E w := fun x =>
    (Valuation.mem_integer_iff _ _).trans (GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff w x)
  simp only [h]

/- English proof (translation)
Establish `hmem : ∀ x ∈ D, ∀ y ∈ D, (x⁻¹ * y ∈ J ↔ x⁻¹ * y ∈ Umax L n)` using `fun x hx y hy => hJ _ (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hD x hx)) (hD y hy))`. Use function extensionality and compare the values at `g`. Rewrite using `[Finset.sum_apply, NG.heckeD, finsum_eq_sum_of_support_subset (s := R.image fun x : GAf L n => (x : GAf L n ⧸ J)), Finset.sum_image]`. Use `Finset.sum_congr rfl fun γ hγ => ?_` and prove the remaining obligations. Establish `hc : ∃ x ∈ D, (x : GAf L n ⧸ J) = γ` using `⟨γ, h1 γ hγ, rfl⟩`.

Rewrite using `[dif_pos hc]`. Establish `hu : γ⁻¹ * hc.choose ∈ Umax L n` using `(hmem γ (h1 γ hγ) _ hc.choose_spec.1).1 (QuotientGroup.eq.1 hc.choose_spec.2.symm)`. Use `congrFun (hf _ hu (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hD γ (h1 γ hγ))) (hD _ hc.choose_spec.1))) (g * γ)` as an intermediate fact. Use `Eq.trans ?_ this` and prove the remaining obligations. Use `show f _ = f _`.

Use `congr 1`. Use `group`. Introduce `γ hγ δ hδ e`. Conclude with `(h2 δ (h1 δ hδ)).unique ⟨hγ, (hmem γ (h1 γ hγ) δ (h1 δ hδ)).1 (QuotientGroup.eq.1 e)⟩ ⟨hδ, by rw [inv_mul_cancel]; exact one_mem _⟩`. Introduce `c hc`.

Distinguish the cases in `h : ∃ x ∈ D, (x : GAf L n ⧸ J) = c`. Take `⟨x, hx, rfl⟩` from `h`. Take `⟨γ, ⟨hγ, e⟩, -⟩` from `h2 x hx`. Conclude with `Finset.mem_coe.2 (Finset.mem_image.2 ⟨γ, hγ, QuotientGroup.eq.2 ((hmem γ (h1 γ hγ) x hx).2 e)⟩)`. Conclude with `absurd (dif_neg h) hc`.
-/
theorem heckeD_eq_sum_of_agree {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (GAf L n)) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))}
    (hJ : ∀ κ, TrivOutside {v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) {D : Set (GAf L n)} (hD : ∀ x ∈ D, TrivOutside {v} x)
    {R : Finset (GAf L n)} (h1 : ∀ γ ∈ R, γ ∈ D) (h2 : ∀ x ∈ D, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n)
    {f : GAf L n → W} (hf : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) :
    NG.heckeD J D f = ∑ γ ∈ R, NG.rt L n γ f := by
  classical
  have hmem : ∀ x ∈ D, ∀ y ∈ D, (x⁻¹ * y ∈ J ↔ x⁻¹ * y ∈ Umax L n) := fun x hx y hy =>
    hJ _ (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hD x hx)) (hD y hy))
  funext g
  rw [Finset.sum_apply, NG.heckeD, finsum_eq_sum_of_support_subset (s := R.image fun x : GAf L n => (x : GAf L n ⧸ J)),
    Finset.sum_image]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    have hc : ∃ x ∈ D, (x : GAf L n ⧸ J) = γ := ⟨γ, h1 γ hγ, rfl⟩
    rw [dif_pos hc]
    have hu : γ⁻¹ * hc.choose ∈ Umax L n :=
      (hmem γ (h1 γ hγ) _ hc.choose_spec.1).1 (QuotientGroup.eq.1 hc.choose_spec.2.symm)
    have := congrFun (hf _ hu (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hD γ (h1 γ hγ)))
      (hD _ hc.choose_spec.1))) (g * γ)
    refine Eq.trans ?_ this
    show f _ = f _
    congr 1
    group
  · intro γ hγ δ hδ e
    exact (h2 δ (h1 δ hδ)).unique ⟨hγ, (hmem γ (h1 γ hγ) δ (h1 δ hδ)).1 (QuotientGroup.eq.1 e)⟩
      ⟨hδ, by rw [inv_mul_cancel]; exact one_mem _⟩
  · intro c hc
    by_cases h : ∃ x ∈ D, (x : GAf L n ⧸ J) = c
    · obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨γ, ⟨hγ, e⟩, -⟩ := h2 x hx
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨γ, hγ, QuotientGroup.eq.2 ((hmem γ (h1 γ hγ) x hx).2 e)⟩)
    · exact absurd (dif_neg h) hc

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply, normV]`. Rewrite using `[normV, (GlobalTheory.HeckeFrob.conjSplit s).card_quot]`. Both sides reduce to the same expression.
-/
theorem norms_eq {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    Formalism.UG.qV L (GlobalTheory.HeckeFrob.conjSplit s).w = normV (GlobalTheory.HeckeFrob.conjSplit s).w ∧
      s.q = normV (GlobalTheory.HeckeFrob.conjSplit s).w := by
  refine ⟨?_, ?_⟩
  · rw [Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply, normV]
  · rw [normV, (GlobalTheory.HeckeFrob.conjSplit s).card_quot]
    rfl

end GlobalTheory.HeckeEigConj

end
