import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteModuloIntegral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZariskiAnalyticNormality
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

noncomputable section

def germCompRingHom {σ τ : Type} [Fintype σ] [Fintype τ] (x : σ → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) :
    Germ (𝓝 (L x)) ℂ →+* Germ (𝓝 x) ℂ where
  toFun s := s.compTendsto L (L.continuous.tendsto x)
  map_one' := rfl
  map_mul' s t := Germ.inductionOn₂ s t fun _ _ => rfl
  map_zero' := rfl
  map_add' s t := Germ.inductionOn₂ s t fun _ _ => rfl

def holGermsPullback {σ τ : Type} [Fintype σ] [Fintype τ] (x : σ → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) :
    holGerms (L x) →+* holGerms x :=
  ((germCompRingHom x L).comp (holGerms (L x)).subtype).codRestrict (holGerms x) fun s => by
    obtain ⟨b, hb, hbs⟩ := s.2
    refine ⟨b ∘ L, hb.comp (L.analyticAt x), ?_⟩
    show _ = germCompRingHom x L s.1
    rw [← hbs]
    rfl

/- English proof (translation)
Introduce `σ τ _ _ x k f L hf hfin g hg`. Take `⟨n, e, he, hrep⟩` from `hfin`. Use `set φ := holGermsPullback x L with hφdef`. Use `set I : Ideal (holGerms x) := Ideal.span (Set.range fun i => (⟨f i, f i, hf i, rfl⟩ : holGerms x)) with hIdef`. Set `_ : Algebra (holGerms (L x)) (holGerms x ⧸ I)` to `((Ideal.Quotient.mk I).comp φ).toAlgebra`.

Establish `hsmul : ∀ (s : holGerms (L x)) (q : holGerms x), s • Ideal.Quotient.mk I q = Ideal.Quotient.mk I (φ s * q)`. Introduce `s q`. Rewrite using `[Algebra.smul_def, RingHom.algebraMap_toAlgebra]`. Simplify using the standard rewrite rules. Establish `hfg : Module.Finite (holGerms (L x)) (holGerms x ⧸ I)`.

Use `⟨⟨Finset.univ.image fun m => Ideal.Quotient.mk I ⟨e m, e m, he m, rfl⟩, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce and unpack `q -`. Take `⟨⟨_, u, hu, rfl⟩, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Take `⟨b, h, hb, hh, hev⟩` from `hrep u hu`.

Establish `hq : Ideal.Quotient.mk I ⟨u, u, hu, rfl⟩ = ∑ m, (⟨b m, b m, hb m, rfl⟩ : holGerms (L x)) • Ideal.Quotient.mk I ⟨e m, e m, he m, rfl⟩`. Simplify using `only [hsmul, ← map_sum]`. Rewrite using `[Ideal.Quotient.eq]`. Establish `hmem : ∑ i, (⟨h i, h i, hh i, rfl⟩ : holGerms x) * ⟨f i, f i, hf i, rfl⟩ ∈ I` using `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)`. Use `hmem using 1` and compare the differences between its conclusion and the goal.

Apply `Subring.subtype_injective` to reduce the goal to its premises. Establish `e1 : (holGerms x).subtype ((⟨u, u, hu, rfl⟩ : holGerms x) - ∑ m, φ ⟨b m, b m, hb m, rfl⟩ * ⟨e m, e m, he m, rfl⟩) = Germ.coeRingHom (𝓝 x) (u - ∑ m, (b m ∘ L) * e m)`. Simplify using `only [map_sub, map_sum, map_mul]`. Both sides reduce to the same expression. Establish `e2 : (holGerms x).subtype (∑ i, (⟨h i, h i, hh i, rfl⟩ : holGerms x) * ⟨f i, f i, hf i, rfl⟩) = Germ.coeRingHom (𝓝 x) (∑ i, h i * f i)`.

Simplify using `only [map_sum, map_mul]`. Both sides reduce to the same expression. Rewrite using `[e1, e2]`. Use `Germ.coe_eq.2 ?_` and prove the remaining obligations. Use `filter_upwards [hev] with z hz`.

Simplify using `only [Pi.sub_apply, Finset.sum_apply, Pi.mul_apply, Function.comp_apply]`. Rewrite using `[hz]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hq]`. Conclude with `Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp))`.

Use `Algebra.IsIntegral.of_finite (holGerms (L x)) (holGerms x ⧸ I)` as an intermediate fact. Take `⟨p, hpm, hp⟩` from `Algebra.IsIntegral.isIntegral (R := holGerms (L x)) (Ideal.Quotient.mk I ⟨g, g, hg, rfl⟩)`. Rewrite `hp` using `[RingHom.algebraMap_toAlgebra, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem, hpm.as_sum]`. Simplify using `only [eval₂_add, eval₂_X_pow, eval₂_finsetSum, eval₂_mul, eval₂_C] at hp`. Take `⟨c, hc⟩` from `Ideal.mem_span_range_iff_exists_fun.1 hp`.

Use `choose a ha hae using fun j : ℕ => (p.coeff j).2`. Use `choose h hh hhe using fun i => (c i).2`. Use `⟨p.natDegree, fun j => a j, h, fun j => ha j, hh, ?_⟩` and prove the remaining obligations. Establish `hcI : ∀ i, (holGerms x).subtype (c i) = Germ.coeRingHom (𝓝 x) (h i)` using `fun i => (hhe i).symm`. Establish `hφI : ∀ j, (holGerms x).subtype (φ (p.coeff j)) = Germ.coeRingHom (𝓝 x) (a j ∘ L)`.

Introduce `j`. Use `show germCompRingHom x L (p.coeff j).1 = _`. Rewrite using `[← hae j]`. Both sides reduce to the same expression. Establish `hgerm : Germ.coeRingHom (𝓝 x) (∑ i, h i * f i) = Germ.coeRingHom (𝓝 x) (g ^ p.natDegree + ∑ j ∈ Finset.range p.natDegree, (a j ∘ L) * g ^ j)`.

Use `congrArg (holGerms x).subtype hc` as an intermediate fact. Simplify using `only [map_add, map_sum, map_mul, map_pow, hcI, hφI] at this ⊢`. Conclude with `this`. Use `filter_upwards [Germ.coe_eq.1 hgerm] with z hz`. Simplify using `only [Finset.sum_apply, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Function.comp_apply] at hz`.

Rewrite using `[Fin.sum_univ_eq_sum_range (fun j => a j (L z) * g z ^ j), hz]`.
-/
theorem FiniteModuloIntegral.proof : FiniteModuloIntegral.Statement := by
  classical
  intro σ τ _ _ x k f L hf hfin g hg
  obtain ⟨n, e, he, hrep⟩ := hfin
  set φ := holGermsPullback x L with hφdef
  set I : Ideal (holGerms x) :=
    Ideal.span (Set.range fun i => (⟨f i, f i, hf i, rfl⟩ : holGerms x)) with hIdef
  let _ : Algebra (holGerms (L x)) (holGerms x ⧸ I) := ((Ideal.Quotient.mk I).comp φ).toAlgebra
  have hsmul : ∀ (s : holGerms (L x)) (q : holGerms x),
      s • Ideal.Quotient.mk I q = Ideal.Quotient.mk I (φ s * q) := by
    intro s q
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    simp

  have hfg : Module.Finite (holGerms (L x)) (holGerms x ⧸ I) := by
    refine ⟨⟨Finset.univ.image fun m => Ideal.Quotient.mk I ⟨e m, e m, he m, rfl⟩, ?_⟩⟩
    rw [eq_top_iff]
    rintro q -
    obtain ⟨⟨_, u, hu, rfl⟩, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨b, h, hb, hh, hev⟩ := hrep u hu
    have hq : Ideal.Quotient.mk I ⟨u, u, hu, rfl⟩ = ∑ m, (⟨b m, b m, hb m, rfl⟩ : holGerms (L x)) •
        Ideal.Quotient.mk I ⟨e m, e m, he m, rfl⟩ := by
      simp only [hsmul, ← map_sum]
      rw [Ideal.Quotient.eq]
      have hmem : ∑ i, (⟨h i, h i, hh i, rfl⟩ : holGerms x) * ⟨f i, f i, hf i, rfl⟩ ∈ I :=
        Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
      convert hmem using 1
      apply Subring.subtype_injective
      have e1 : (holGerms x).subtype ((⟨u, u, hu, rfl⟩ : holGerms x) -
          ∑ m, φ ⟨b m, b m, hb m, rfl⟩ * ⟨e m, e m, he m, rfl⟩) =
          Germ.coeRingHom (𝓝 x) (u - ∑ m, (b m ∘ L) * e m) := by
        simp only [map_sub, map_sum, map_mul]
        rfl
      have e2 : (holGerms x).subtype (∑ i, (⟨h i, h i, hh i, rfl⟩ : holGerms x) * ⟨f i, f i, hf i, rfl⟩) =
          Germ.coeRingHom (𝓝 x) (∑ i, h i * f i) := by
        simp only [map_sum, map_mul]
        rfl
      rw [e1, e2]
      refine Germ.coe_eq.2 ?_
      filter_upwards [hev] with z hz
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.mul_apply, Function.comp_apply]
      rw [hz]
      ring
    rw [hq]
    exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have := Algebra.IsIntegral.of_finite (holGerms (L x)) (holGerms x ⧸ I)

  obtain ⟨p, hpm, hp⟩ :=
    Algebra.IsIntegral.isIntegral (R := holGerms (L x)) (Ideal.Quotient.mk I ⟨g, g, hg, rfl⟩)
  rw [RingHom.algebraMap_toAlgebra, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem,
    hpm.as_sum] at hp
  simp only [eval₂_add, eval₂_X_pow, eval₂_finsetSum, eval₂_mul, eval₂_C] at hp
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 hp
  choose a ha hae using fun j : ℕ => (p.coeff j).2
  choose h hh hhe using fun i => (c i).2
  refine ⟨p.natDegree, fun j => a j, h, fun j => ha j, hh, ?_⟩
  have hcI : ∀ i, (holGerms x).subtype (c i) = Germ.coeRingHom (𝓝 x) (h i) := fun i => (hhe i).symm
  have hφI : ∀ j, (holGerms x).subtype (φ (p.coeff j)) = Germ.coeRingHom (𝓝 x) (a j ∘ L) := by
    intro j
    show germCompRingHom x L (p.coeff j).1 = _
    rw [← hae j]
    rfl
  have hgerm : Germ.coeRingHom (𝓝 x) (∑ i, h i * f i) = Germ.coeRingHom (𝓝 x)
      (g ^ p.natDegree + ∑ j ∈ Finset.range p.natDegree, (a j ∘ L) * g ^ j) := by
    have := congrArg (holGerms x).subtype hc
    simp only [map_add, map_sum, map_mul, map_pow, hcI, hφI] at this ⊢
    exact this
  filter_upwards [Germ.coe_eq.1 hgerm] with z hz
  simp only [Finset.sum_apply, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Function.comp_apply] at hz
  rw [Fin.sum_univ_eq_sum_range (fun j => a j (L z) * g z ^ j), hz]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
