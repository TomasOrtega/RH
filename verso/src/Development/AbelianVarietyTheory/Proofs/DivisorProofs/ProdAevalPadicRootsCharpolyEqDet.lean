import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetAevalEqProdArootsCharpolyStatement

namespace GlobalTheory
open Polynomial

/- English proof (translation)
Rewrite using `[aeval_def]`. Use `congr 1`. Conclude with `RingHom.ext_int _ _`.
-/
theorem aeval_int_eq_eval₂ {A : Type} [Ring A] [inst : Algebra ℤ A] (x : A) (R : ℤ[X]) :
    @aeval ℤ A _ _ inst x R = eval₂ (Int.castRingHom A) x R := by
  rw [aeval_def]
  congr 1
  exact RingHom.ext_int _ _

/- English proof (translation)
Introduce `p _ S _ _ N _ _ _ _ ψ u P R d hψ hP hd`. Set `K` to `FractionRing S`. Establish `hg : Function.Injective ((algebraMap S K).comp ψ)` using `(IsFractionRing.injective S K).comp hψ`. Set `ψ' : ℚ_[p] →+* K` to `IsFractionRing.lift hg`. Establish `hψ' : ψ'.comp (algebraMap ℤ_[p] ℚ_[p]) = (algebraMap S K).comp ψ` using `IsLocalization.lift_comp _`.

Set `Ω` to `AlgebraicClosure K`. Use `letI : Algebra ℚ_[p] Ω := ((algebraMap K Ω).comp ψ').toAlgebra`. Establish `hΩ : algebraMap ℚ_[p] Ω = (algebraMap K Ω).comp ψ'` using `rfl`. Set `j : PadicAlgCl p →ₐ[ℚ_[p]] Ω` to `IsAlgClosed.lift`. Establish `hj : Function.Injective j` using `j.toRingHom.injective`.

Set `uK : Module.End K (TensorProduct S K N)` to `u.baseChange K`. Establish `key` using `GlobalTheory.T.det_aeval_eq_prod_aroots_charpoly' K Ω (TensorProduct S K N) uK (R.map (Int.castRingHom K))`. Establish `hF : ∀ {A : Type} [Ring A] [Algebra K A] (x : A), aeval x (R.map (Int.castRingHom K)) = aeval x R`. Introduce `A _ _ x`. Rewrite using `[← algebraMap_int_eq, aeval_map_algebraMap]`.

Simplify using `only [hF] at key`. Establish `hbc : aeval uK R = (aeval u R).baseChange K`. Use `aeval_algHom_apply (Module.End.baseChangeHom S K N).toRingHom.toIntAlgHom u R` as an intermediate fact. Conclude with `this`. Rewrite `key` using `[hbc, LinearMap.det_baseChange, hd]`.

Establish `hch : uK.charpoly.aroots Ω = (P.map (algebraMap ℤ_[p] ℚ_[p])).aroots Ω`. Rewrite using `[LinearMap.charpoly_baseChange, ← hP, aroots_def, aroots_def, map_map, map_map, map_map, hΩ]`. Simplify using `only [RingHom.comp_assoc, hψ']`. Rewrite `key` using `[hch]`. Apply `hj` to reduce the goal to its premises.

Use `set Q := P.map (algebraMap ℤ_[p] ℚ_[p])`. Establish `hroots : Q.aroots Ω = (Q.aroots (PadicAlgCl p)).map j`. Establish `h` using `(IsAlgClosed.splits (Q.map (algebraMap ℚ_[p] (PadicAlgCl p)))).roots_map (j : PadicAlgCl p →+* Ω)`. Rewrite `h` using `[map_map, AlgHom.comp_algebraMap]`. Rewrite using `[aroots_def, aroots_def, h]`.

Both sides reduce to the same expression. Rewrite `key` using `[hroots, Multiset.map_map]`. Rewrite using `[map_multiset_prod, Multiset.map_map, AlgHom.commutes]`. Simplify using `only [aeval_int_eq_eval₂] at key ⊢`. Establish `e1 : ∀ a : PadicAlgCl p, j (eval₂ (Int.castRingHom _) a R) = eval₂ (Int.castRingHom Ω) (j a) R`.

Introduce `a`. Express the relevant statement in the definitionally equal form `(j : PadicAlgCl p →+* Ω) (eval₂ (Int.castRingHom _) a R) = _`. Rewrite using `[Polynomial.hom_eval₂]`. Use `congr 1`. Conclude with `RingHom.ext_int _ _`.

Simplify using `only [Function.comp_def, e1] at key ⊢`. Use `key.symm.trans ?_` and prove the remaining obligations. Rewrite using `[hΩ, RingHom.comp_apply]`. Use `congr 1`. Conclude with `(RingHom.congr_fun hψ' d).symm`.
-/
theorem prod_aeval_aroots_padic_eq_det : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [IsDomain S] (N : Type) [AddCommGroup N] [Module S N] [Module.Free S N] [Module.Finite S N] (ψ : ℤ_[p] →+* S) (u : N →ₗ[S] N) (P : Polynomial ℤ_[p]) (R : Polynomial ℤ) (d : ℤ_[p]), Function.Injective ψ → P.map ψ = u.charpoly → LinearMap.det (Polynomial.aeval u R) = ψ d → (((P.map (algebraMap ℤ_[p] ℚ_[p])).aroots (PadicAlgCl p)).map (fun a => Polynomial.aeval a R)).prod = algebraMap ℚ_[p] (PadicAlgCl p) (d : ℚ_[p]) := by
  intro p _ S _ _ N _ _ _ _ ψ u P R d hψ hP hd
  let K := FractionRing S
  have hg : Function.Injective ((algebraMap S K).comp ψ) :=
    (IsFractionRing.injective S K).comp hψ
  let ψ' : ℚ_[p] →+* K := IsFractionRing.lift hg
  have hψ' : ψ'.comp (algebraMap ℤ_[p] ℚ_[p]) = (algebraMap S K).comp ψ :=
    IsLocalization.lift_comp _
  let Ω := AlgebraicClosure K
  letI : Algebra ℚ_[p] Ω := ((algebraMap K Ω).comp ψ').toAlgebra
  have hΩ : algebraMap ℚ_[p] Ω = (algebraMap K Ω).comp ψ' := rfl
  let j : PadicAlgCl p →ₐ[ℚ_[p]] Ω := IsAlgClosed.lift
  have hj : Function.Injective j := j.toRingHom.injective
  let uK : Module.End K (TensorProduct S K N) := u.baseChange K
  have key := GlobalTheory.T.det_aeval_eq_prod_aroots_charpoly' K Ω (TensorProduct S K N) uK (R.map (Int.castRingHom K))
  have hF : ∀ {A : Type} [Ring A] [Algebra K A] (x : A), aeval x (R.map (Int.castRingHom K)) = aeval x R := by
    intro A _ _ x
    rw [← algebraMap_int_eq, aeval_map_algebraMap]
  simp only [hF] at key
  have hbc : aeval uK R = (aeval u R).baseChange K := by
    have := aeval_algHom_apply (Module.End.baseChangeHom S K N).toRingHom.toIntAlgHom u R
    exact this
  rw [hbc, LinearMap.det_baseChange, hd] at key
  have hch : uK.charpoly.aroots Ω = (P.map (algebraMap ℤ_[p] ℚ_[p])).aroots Ω := by
    rw [LinearMap.charpoly_baseChange, ← hP, aroots_def, aroots_def, map_map, map_map, map_map, hΩ]
    simp only [RingHom.comp_assoc, hψ']
  rw [hch] at key
  apply hj
  set Q := P.map (algebraMap ℤ_[p] ℚ_[p])
  have hroots : Q.aroots Ω = (Q.aroots (PadicAlgCl p)).map j := by
    have h := (IsAlgClosed.splits (Q.map (algebraMap ℚ_[p] (PadicAlgCl p)))).roots_map (j : PadicAlgCl p →+* Ω)
    rw [map_map, AlgHom.comp_algebraMap] at h
    rw [aroots_def, aroots_def, h]
    rfl
  rw [hroots, Multiset.map_map] at key
  rw [map_multiset_prod, Multiset.map_map, AlgHom.commutes]
  simp only [aeval_int_eq_eval₂] at key ⊢
  have e1 : ∀ a : PadicAlgCl p, j (eval₂ (Int.castRingHom _) a R) = eval₂ (Int.castRingHom Ω) (j a) R := by
    intro a
    change (j : PadicAlgCl p →+* Ω) (eval₂ (Int.castRingHom _) a R) = _
    rw [Polynomial.hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _
  simp only [Function.comp_def, e1] at key ⊢
  refine key.symm.trans ?_
  rw [hΩ, RingHom.comp_apply]
  congr 1
  exact (RingHom.congr_fun hψ' d).symm

end GlobalTheory
