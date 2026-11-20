import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFibreRadical
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFibreTor
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFibreRadicalPrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

/- English proof (translation)
Use `le_antisymm (Ideal.map_inf_le φ) ?_` and prove the remaining obligations. Introduce and unpack `y ⟨hyI, hyJ⟩`. Take `⟨a, ha, rfl⟩` from `(Ideal.mem_map_iff_of_surjective φ hφ).1 hyI`. Take `⟨b, hb, hab⟩` from `(Ideal.mem_map_iff_of_surjective φ hφ).1 hyJ`. Establish `hmem : a - b ∈ (I ⊔ J) ⊓ RingHom.ker φ` using `⟨Ideal.sub_mem _ (Ideal.mem_sup_left ha) (Ideal.mem_sup_right hb), RingHom.mem_ker.2 (by rw [map_sub, hab, sub_self])⟩`.

Establish `h2 : a - b ∈ RingHom.ker φ * I ⊔ RingHom.ker φ * J`. Rewrite using `[← Ideal.mul_sup]`. Conclude with `h hmem`. Take `⟨u, hu, v, hv, huv⟩` from `Submodule.mem_sup.1 h2`. Establish `hu' : u ∈ RingHom.ker φ ⊓ I` using `Ideal.mul_le_inf hu`.

Establish `hv' : v ∈ RingHom.ker φ ⊓ J` using `Ideal.mul_le_inf hv`. Use `(Ideal.mem_map_iff_of_surjective φ hφ).2 ⟨a - u, ⟨Ideal.sub_mem _ ha hu'.2, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `e : a - u = b + v` using `by linear_combination -huv`. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ hb hv'.2`.

Rewrite using `[map_sub, RingHom.mem_ker.1 hu'.1, sub_zero]`.
-/
theorem map_inf_eq_of_sup_inf_ker_le {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R')
    (hφ : Function.Surjective φ) (I J : Ideal R)
    (h : (I ⊔ J) ⊓ RingHom.ker φ ≤ RingHom.ker φ * (I ⊔ J)) :
    (I ⊓ J).map φ = I.map φ ⊓ J.map φ := by
  refine le_antisymm (Ideal.map_inf_le φ) ?_
  rintro y ⟨hyI, hyJ⟩
  obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).1 hyI
  obtain ⟨b, hb, hab⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).1 hyJ
  have hmem : a - b ∈ (I ⊔ J) ⊓ RingHom.ker φ :=
    ⟨Ideal.sub_mem _ (Ideal.mem_sup_left ha) (Ideal.mem_sup_right hb),
      RingHom.mem_ker.2 (by rw [map_sub, hab, sub_self])⟩
  have h2 : a - b ∈ RingHom.ker φ * I ⊔ RingHom.ker φ * J := by
    rw [← Ideal.mul_sup]; exact h hmem
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h2
  have hu' : u ∈ RingHom.ker φ ⊓ I := Ideal.mul_le_inf hu
  have hv' : v ∈ RingHom.ker φ ⊓ J := Ideal.mul_le_inf hv
  refine (Ideal.mem_map_iff_of_surjective φ hφ).2 ⟨a - u, ⟨Ideal.sub_mem _ ha hu'.2, ?_⟩, ?_⟩
  · have e : a - u = b + v := by linear_combination -huv
    rw [e]
    exact Ideal.add_mem _ hb hv'.2
  · rw [map_sub, RingHom.mem_ker.1 hu'.1, sub_zero]

/- English proof (translation)
Introduce `σ _ ι _ K hK`. Establish `hsurj : ∀ t : σ → ℂ, Function.Surjective (MvPolynomial.map (eval t) : MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ)` using `fun t => MvPolynomial.map_surjective _ (fun c => ⟨C c, eval_C c⟩)`. Establish `key : ∀ s : Finset (Ideal (MvPolynomial ι (MvPolynomial σ ℂ))), (∀ p ∈ s, p.IsPrime) → ∃ F : MvPolynomial σ ℂ, F ≠ 0 ∧ ∀ t : σ → ℂ, eval t F ≠ 0 → ((s.inf id).map (MvPolynomial.map (eval t))).IsRadical`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty`. Introduce `_`. Use `⟨1, one_ne_zero, fun t _ => ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.inf_empty, Ideal.map_top]`. Conclude with `fun _ _ => Submodule.mem_top`.

Consider the case `insert p s hps ih`. Introduce `hs`. Take `⟨F₁, hF₁, h₁⟩` from `ih (fun q hq => hs q (Finset.mem_insert_of_mem hq))`. Take `⟨F₂, hF₂, h₂⟩` from `hP σ ι p (hs p (Finset.mem_insert_self p s))`. Take `⟨F₃, hF₃, h₃⟩` from `hT σ ι (p ⊔ s.inf id)`.

Use `⟨F₁ * F₂ * F₃, mul_ne_zero (mul_ne_zero hF₁ hF₂) hF₃, fun t ht => ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, ne_eq, mul_eq_zero, not_or] at ht`. Take `⟨⟨ht₁, ht₂⟩, ht₃⟩` from `ht`. Rewrite using `[Finset.inf_insert, id, map_inf_eq_of_sup_inf_ker_le _ (hsurj t) _ _ (h₃ t ht₃)]`. Conclude with `(h₂ t ht₂).inf (h₁ t ht₁)`.

Establish `hfin` using `Ideal.finite_minimalPrimes_of_isNoetherianRing _ K`. Take `⟨F, hF, hFt⟩` from `key hfin.toFinset (fun p hp => ((hfin.mem_toFinset).1 hp).1.1)`. Use `⟨F, hF, fun t ht => ?_⟩` and prove the remaining obligations. Establish `hK' : K = hfin.toFinset.inf id`. Rewrite using `[Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset, Ideal.sInf_minimalPrimes]`.

Conclude with `le_antisymm Ideal.le_radical hK`. Rewrite using `[hK']`. Conclude with `hFt t ht`.
-/
theorem GenericFibreRadical.proof (hT : GenericFibreTor.Statement)
    (hP : GenericFibreRadicalPrime.Statement) : GenericFibreRadical.Statement := by
  intro σ _ ι _ K hK
  have hsurj : ∀ t : σ → ℂ, Function.Surjective
      (MvPolynomial.map (eval t) : MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) :=
    fun t => MvPolynomial.map_surjective _ (fun c => ⟨C c, eval_C c⟩)
  classical
  have key : ∀ s : Finset (Ideal (MvPolynomial ι (MvPolynomial σ ℂ))), (∀ p ∈ s, p.IsPrime) →
      ∃ F : MvPolynomial σ ℂ, F ≠ 0 ∧ ∀ t : σ → ℂ, eval t F ≠ 0 →
        ((s.inf id).map (MvPolynomial.map (eval t))).IsRadical := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨1, one_ne_zero, fun t _ => ?_⟩
      rw [Finset.inf_empty, Ideal.map_top]
      exact fun _ _ => Submodule.mem_top
    | insert p s hps ih =>
      intro hs
      obtain ⟨F₁, hF₁, h₁⟩ := ih (fun q hq => hs q (Finset.mem_insert_of_mem hq))
      obtain ⟨F₂, hF₂, h₂⟩ := hP σ ι p (hs p (Finset.mem_insert_self p s))
      obtain ⟨F₃, hF₃, h₃⟩ := hT σ ι (p ⊔ s.inf id)
      refine ⟨F₁ * F₂ * F₃, mul_ne_zero (mul_ne_zero hF₁ hF₂) hF₃, fun t ht => ?_⟩
      simp only [map_mul, ne_eq, mul_eq_zero, not_or] at ht
      obtain ⟨⟨ht₁, ht₂⟩, ht₃⟩ := ht
      rw [Finset.inf_insert, id, map_inf_eq_of_sup_inf_ker_le _ (hsurj t) _ _ (h₃ t ht₃)]
      exact (h₂ t ht₂).inf (h₁ t ht₁)
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing _ K
  obtain ⟨F, hF, hFt⟩ := key hfin.toFinset (fun p hp => ((hfin.mem_toFinset).1 hp).1.1)
  refine ⟨F, hF, fun t ht => ?_⟩
  have hK' : K = hfin.toFinset.inf id := by
    rw [Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset, Ideal.sInf_minimalPrimes]
    exact le_antisymm Ideal.le_radical hK
  rw [hK']
  exact hFt t ht

end

end GroundTheory.Heights₂.Heights
