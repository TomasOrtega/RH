import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLAlgebraMap
open GlobalTheory.LogDerProj

set_option autoImplicit false

namespace GlobalTheory.LogDerProj

/- English proof (translation)
Introduce `k R S _ _ _ _ f _ φ hφ J n`. Use `letI : Algebra k R := φ.toAlgebra`. Use `haveI : Algebra.FiniteType k R := hφ`. Use `haveI : Algebra.FinitePresentation k R := Algebra.FinitePresentation.of_finiteType.mp inferInstance`. Use `haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R`.

Use `letI : Algebra k S := ((algebraMap R S).comp φ).toAlgebra`. Use `haveI : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `hn0 : ∀ c : k, n.1 (algebraMap R S (φ c)) = 0` using `fun c => n.2.1 c`. Establish `hnJ : ∀ y ∈ J.map (algebraMap R S), n.1 y ∈ J.map (algebraMap R S)` using `n.2.2`. Set `gl : R →ₗ[k] S` to `{ toFun := fun r => n.1 (algebraMap R S r) map_add' := fun a b => by simp map_smul' := fun c r => by`.

Rewrite using `[RingHom.id_apply, Algebra.smul_def, map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Use `show _ = algebraMap R S (φ c) * _`. Rewrite using `[show algebraMap k R c = φ c from rfl, hn0, mul_zero, add_zero] }`. Set `g : Derivation k R S` to `Derivation.mk' gl fun a b => by show n.1 (algebraMap R S (a * b)) = a • n.1 (algebraMap R S b) + b • n.1 (algebraMap R S a)`. Rewrite using `[map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, Algebra.smul_def, Algebra.smul_def]`.

Establish `hg : ∀ r, g r = n.1 (algebraMap R S r)` using `fun r => rfl`. Take `⟨h, s, hs⟩` from `Module.FinitePresentation.exists_lift_of_isLocalizedModule (Submonoid.powers f) (Algebra.linearMap R S) g.liftKaehlerDifferential`. Set `D' : Derivation k R R` to `h.compDer (KaehlerDifferential.D k R)`. Establish `hD' : ∀ r, algebraMap R S (D' r) = algebraMap R S s * n.1 (algebraMap R S r)`. Introduce `r`.

Use `congrArg (fun L : Ω[R⁄k] →ₗ[R] S => L (KaehlerDifferential.D k R r)) hs` as an intermediate fact. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply, LinearMap.smul_apply, Derivation.liftKaehlerDifferential_comp_D] at this`. Rewrite `this` using `[Submonoid.smul_def, Algebra.smul_def]`. Rewrite using `[← hg]`. Conclude with `this`.

Establish `hJfg : J.FG` using `IsNoetherian.noetherian J`. Take `⟨T, hT⟩` from `hJfg`. Establish `hex : ∀ t : T, ∃ m : Submonoid.powers f, (m : R) * D' t ∈ J`. Introduce `t`. Establish `ht : (t : R) ∈ J` using `hT ▸ Ideal.subset_span t.2`.

Establish `h1 : algebraMap R S (D' t) ∈ J.map (algebraMap R S)`. Rewrite using `[hD']`. Conclude with `Ideal.mul_mem_left _ _ (hnJ _ (Ideal.mem_map_of_mem _ ht))`. Take `⟨m, hm, hmJ⟩` from `(IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers f) S J _).1 h1`. Conclude with `⟨⟨m, hm⟩, hmJ⟩`.

Use `choose c hc using hex`. Set `m : Submonoid.powers f` to `∏ t, c t`. Establish `hmT : ∀ t ∈ T, (m : R) * D' t ∈ J`. Introduce `t ht`. Establish `hdvd : (c ⟨t, ht⟩ : R) ∣ (m : R)` using `by show (c ⟨t, ht⟩ : R) ∣ ((∏ t, c t : Submonoid.powers f) : R)`.

Rewrite using `[Submonoid.coe_finset_prod]`. Conclude with `Finset.dvd_prod_of_mem _ (Finset.mem_univ _)`. Take `⟨q, hq⟩` from `hdvd`. Rewrite using `[hq, mul_comm _ q, mul_assoc]`. Conclude with `Ideal.mul_mem_left _ _ (hc ⟨t, ht⟩)`.

Set `D : Derivation ℤ R R` to `(m : R) • D'.restrictScalars ℤ`. Establish `hDapp : ∀ r, D r = (m : R) * D' r` using `fun r => rfl`. Establish `hDmem : D ∈ logSub φ J`. Use `⟨fun a => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[hDapp, show φ a = algebraMap k R a from rfl, D'.map_algebraMap, mul_zero]`.

Rewrite `hy` using `[← hT]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => rw [hDapp]`. Conclude with `hmT x hx`. Consider the case `zero => rw [map_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul a x hx' hx`. Rewrite using `[smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]`.

Establish `hxJ : x ∈ J` using `by rw [← hT]; exact hx'`. Conclude with `add_mem (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ hxJ)`. Use `⟨(⟨D, hDmem⟩, m * s), ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `der_ext f _ _ fun r => ?_` and prove the remaining obligations.

Rewrite using `[res_apply, hDapp]`. Use `show ((m * s : Submonoid.powers f) : R) • n.1 (algebraMap R S r) = _`. Rewrite using `[Algebra.smul_def, Submonoid.coe_mul, map_mul, map_mul, hD', mul_assoc]`.
-/
theorem exists_pow_smul_eq_res : ∀ {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R)
    [IsLocalization.Away f S] (φ : k →+* R), φ.FiniteType → ∀ (J : Ideal R)
    (n : (logSub ((algebraMap R S).comp φ) (J.map (algebraMap R S))).restrictScalars R),
    ∃ x : logSub φ J × Submonoid.powers f, x.2 • n = res (S := S) f φ J x.1 := by
  intro k R S _ _ _ _ f _ φ hφ J n
  letI : Algebra k R := φ.toAlgebra
  haveI : Algebra.FiniteType k R := hφ
  haveI : Algebra.FinitePresentation k R := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  letI : Algebra k S := ((algebraMap R S).comp φ).toAlgebra
  haveI : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hn0 : ∀ c : k, n.1 (algebraMap R S (φ c)) = 0 := fun c => n.2.1 c
  have hnJ : ∀ y ∈ J.map (algebraMap R S), n.1 y ∈ J.map (algebraMap R S) := n.2.2
  let gl : R →ₗ[k] S :=
    { toFun := fun r => n.1 (algebraMap R S r)
      map_add' := fun a b => by simp
      map_smul' := fun c r => by
        rw [RingHom.id_apply, Algebra.smul_def, map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        show _ = algebraMap R S (φ c) * _
        rw [show algebraMap k R c = φ c from rfl, hn0, mul_zero, add_zero] }
  let g : Derivation k R S := Derivation.mk' gl fun a b => by
    show n.1 (algebraMap R S (a * b)) = a • n.1 (algebraMap R S b) + b • n.1 (algebraMap R S a)
    rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, Algebra.smul_def, Algebra.smul_def]
  have hg : ∀ r, g r = n.1 (algebraMap R S r) := fun r => rfl
  obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule (Submonoid.powers f)
    (Algebra.linearMap R S) g.liftKaehlerDifferential
  let D' : Derivation k R R := h.compDer (KaehlerDifferential.D k R)
  have hD' : ∀ r, algebraMap R S (D' r) = algebraMap R S s * n.1 (algebraMap R S r) := by
    intro r
    have := congrArg (fun L : Ω[R⁄k] →ₗ[R] S => L (KaehlerDifferential.D k R r)) hs
    simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply, LinearMap.smul_apply,
      Derivation.liftKaehlerDifferential_comp_D] at this
    rw [Submonoid.smul_def, Algebra.smul_def] at this
    rw [← hg]
    exact this
  have hJfg : J.FG := IsNoetherian.noetherian J
  obtain ⟨T, hT⟩ := hJfg
  have hex : ∀ t : T, ∃ m : Submonoid.powers f, (m : R) * D' t ∈ J := by
    intro t
    have ht : (t : R) ∈ J := hT ▸ Ideal.subset_span t.2
    have h1 : algebraMap R S (D' t) ∈ J.map (algebraMap R S) := by
      rw [hD']
      exact Ideal.mul_mem_left _ _ (hnJ _ (Ideal.mem_map_of_mem _ ht))
    obtain ⟨m, hm, hmJ⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers f) S J _).1 h1
    exact ⟨⟨m, hm⟩, hmJ⟩
  choose c hc using hex
  let m : Submonoid.powers f := ∏ t, c t
  have hmT : ∀ t ∈ T, (m : R) * D' t ∈ J := by
    intro t ht
    have hdvd : (c ⟨t, ht⟩ : R) ∣ (m : R) := by
      show (c ⟨t, ht⟩ : R) ∣ ((∏ t, c t : Submonoid.powers f) : R)
      rw [Submonoid.coe_finset_prod]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
    obtain ⟨q, hq⟩ := hdvd
    rw [hq, mul_comm _ q, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hc ⟨t, ht⟩)
  let D : Derivation ℤ R R := (m : R) • D'.restrictScalars ℤ
  have hDapp : ∀ r, D r = (m : R) * D' r := fun r => rfl
  have hDmem : D ∈ logSub φ J := by
    refine ⟨fun a => ?_, fun y hy => ?_⟩
    · rw [hDapp, show φ a = algebraMap k R a from rfl, D'.map_algebraMap, mul_zero]
    · rw [← hT] at hy
      induction hy using Submodule.span_induction with
      | mem x hx => rw [hDapp]; exact hmT x hx
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x hx' hx =>
        rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        have hxJ : x ∈ J := by rw [← hT]; exact hx'
        exact add_mem (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ hxJ)
  refine ⟨(⟨D, hDmem⟩, m * s), ?_⟩
  apply Subtype.ext
  refine der_ext f _ _ fun r => ?_
  rw [res_apply, hDapp]
  show ((m * s : Submonoid.powers f) : R) • n.1 (algebraMap R S r) = _
  rw [Algebra.smul_def, Submonoid.coe_mul, map_mul, map_mul, hD', mul_assoc]

end GlobalTheory.LogDerProj
