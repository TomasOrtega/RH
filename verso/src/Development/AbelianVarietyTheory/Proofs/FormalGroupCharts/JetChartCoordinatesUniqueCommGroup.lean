import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointAddSqZeroEqProdMulTangentStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open SqZero

/- English proof (translation)
Establish `hJ2 : J ^ 2 = ⊥`. Rewrite using `[← le_bot_iff, pow_two, ← hJ]`. Conclude with `Ideal.mul_mono_right hJ'`. Set `c : Fin d → J` to `fun j => ⟨_, hδ j⟩`. Establish `hc : ∀ j, (c j : A) * (c j : A) = 0` using `fun j => mul_eq_zero_of_sq hJ2 (c j).2 (c j).2`.

Establish `he : ∀ j, epsTo R (c j : A) (hc j) (TrivSqZeroExt.inr 1) = c j` using `fun j => epsTo_eps _ _`. Establish `key` using `GlobalTheory.T.jetPoint_add_sqZero_eq_prod_mul_tangent R G hG d v hv x hx₁ hx₂ hx₃ A aug J hJ hJ' m ψ ψ' hψ hψ' (fun j => epsTo R (c j : A) (hc j)) (fun j => by rw [he]; exact (c j).2) (fun j => by rw [he]; exact (add_sub_cancel _ _).symm)`. Rewrite `key` using `[← h]`. Establish `h1 : lieExp v (fun j => (c j : A)) hc = 1` using `mul_eq_right.1 key.symm`. Establish `h0 : c = 0`.

Apply `(expHom_bijective hv hJ2).1` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `congrArg Additive.ofMul (Subtype.ext h1)`. Use `jet_ext fun j => ?_` and prove the remaining obligations. Establish `: ψ' (zR m j) - ψ (zR m j) = 0` using `congrArg Subtype.val (congrFun h0 j)`.

Conclude with `(sub_eq_zero.1 this).symm`.
-/
theorem jetCoord_eq_of_sub_mem {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (hG : Smooth G.hom) {d : ℕ} {v : Fin d → (epsR R ⟶ G)}
    (hv : IsLieBasis v) {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G}
    (hx₁ : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m)
    (hx₂ : ∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1)
    (hx₃ : ∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j)
    {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (J : Ideal A)
    (hJ : J * RingHom.ker aug = ⊥) (hJ' : J ≤ RingHom.ker aug) {m : ℕ}
    (ψ ψ' : JetR R (Fin d) m →ₐ[R] A) (hψ : aug.comp ψ = jetAug R (Fin d) m)
    (hψ' : aug.comp ψ' = jetAug R (Fin d) m) (hδ : ∀ j, ψ' (zR m j) - ψ (zR m j) ∈ J)
    (h : spMap ψ ≫ x m = spMap ψ' ≫ x m) : ψ = ψ' := by
  have hJ2 : J ^ 2 = ⊥ := by
    rw [← le_bot_iff, pow_two, ← hJ]
    exact Ideal.mul_mono_right hJ'
  let c : Fin d → J := fun j => ⟨_, hδ j⟩
  have hc : ∀ j, (c j : A) * (c j : A) = 0 := fun j => mul_eq_zero_of_sq hJ2 (c j).2 (c j).2
  have he : ∀ j, epsTo R (c j : A) (hc j) (TrivSqZeroExt.inr 1) = c j := fun j => epsTo_eps _ _
  have key := GlobalTheory.T.jetPoint_add_sqZero_eq_prod_mul_tangent R G hG d v hv x hx₁ hx₂ hx₃ A aug J hJ hJ' m ψ ψ' hψ hψ'
    (fun j => epsTo R (c j : A) (hc j)) (fun j => by rw [he]; exact (c j).2)
    (fun j => by rw [he]; exact (add_sub_cancel _ _).symm)
  rw [← h] at key
  have h1 : lieExp v (fun j => (c j : A)) hc = 1 := mul_eq_right.1 key.symm
  have h0 : c = 0 := by
    apply (expHom_bijective hv hJ2).1
    rw [map_zero]
    exact congrArg Additive.ofMul (Subtype.ext h1)
  refine jet_ext fun j => ?_
  have : ψ' (zR m j) - ψ (zR m j) = 0 := congrArg Subtype.val (congrFun h0 j)
  exact (sub_eq_zero.1 this).symm

/- English proof (translation)
Use `set N := RingHom.ker aug with hNdef`. Establish `main : ∀ k j, ψ' (zR m j) - ψ (zR m j) ∈ N ^ (k + 1)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`.

Introduce `j`. Rewrite using `[zero_add, pow_one, hNdef, RingHom.mem_ker, map_sub, ← AlgHom.comp_apply, ← AlgHom.comp_apply, hψ, hψ', sub_self]`. Consider the case `succ k ih`. Set `q : A →ₐ[R] A ⧸ N ^ (k + 1 + 1)` to `Ideal.Quotient.mkₐ R _`. Establish `hq : Function.Surjective q` using `Ideal.Quotient.mkₐ_surjective R _`.

Set `aug' : (A ⧸ N ^ (k + 1 + 1)) →ₐ[R] R` to `Ideal.Quotient.liftₐ _ aug (fun a ha => Ideal.pow_le_self (by omega) ha)`. Establish `haug : aug'.comp q = aug` using `AlgHom.ext fun _ => rfl`. Establish `hker : RingHom.ker aug' = N.map q`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `a ha`.

Take `⟨b, rfl⟩` from `hq a`. Conclude with `Ideal.mem_map_of_mem _ ha`. Conclude with `Ideal.map_le_iff_le_comap.2 fun a ha => ha`. Establish `e` using `jetCoord_eq_of_sub_mem hG hv hx₁ hx₂ hx₃ aug' ((N ^ (k + 1)).map q) (by rw [hker, ← Ideal.map_mul, ← pow_succ]; exact Ideal.map_quotient_self _) (by rw [hker]; exact Ideal.map_mono (Ideal.pow_le_self (by omega))) (q.comp ψ) (q.comp ψ') (by rw [← AlgHom.comp_assoc, haug, hψ]) (by …`. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, ← map_sub]`.

Conclude with `Ideal.mem_map_of_mem _ (ih j))`. Use the proof step `(by rw [← spMap_comp, ← spMap_comp, Category.assoc, Category.assoc, h])`. Introduce `j`. Conclude with `Ideal.Quotient.eq.1 (AlgHom.congr_fun e (zR m j)).symm`. Use `jet_ext fun j => ?_` and prove the remaining obligations.

Use `main m j` as an intermediate fact. Rewrite `this` using `[hN, Ideal.mem_bot]`. Conclude with `(sub_eq_zero.1 this).symm`.
-/
theorem jetCoord_unique (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] (hG : Smooth G.hom) (d : ℕ) (v : Fin d → (epsR R ⟶ G)) (hv : IsLieBasis v)
    (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G)
    (hx₁ : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m)
    (hx₂ : ∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1)
    (hx₃ : ∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j)
    (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ)
    (hN : (RingHom.ker aug) ^ (m + 1) = ⊥) (ψ ψ' : JetR R (Fin d) m →ₐ[R] A)
    (hψ : aug.comp ψ = jetAug R (Fin d) m) (hψ' : aug.comp ψ' = jetAug R (Fin d) m)
    (h : spMap ψ ≫ x m = spMap ψ' ≫ x m) : ψ = ψ' := by
  set N := RingHom.ker aug with hNdef
  have main : ∀ k j, ψ' (zR m j) - ψ (zR m j) ∈ N ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro j
      rw [zero_add, pow_one, hNdef, RingHom.mem_ker, map_sub, ← AlgHom.comp_apply,
        ← AlgHom.comp_apply, hψ, hψ', sub_self]
    | succ k ih =>
      let q : A →ₐ[R] A ⧸ N ^ (k + 1 + 1) := Ideal.Quotient.mkₐ R _
      have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective R _
      let aug' : (A ⧸ N ^ (k + 1 + 1)) →ₐ[R] R := Ideal.Quotient.liftₐ _ aug
        (fun a ha => Ideal.pow_le_self (by omega) ha)
      have haug : aug'.comp q = aug := AlgHom.ext fun _ => rfl
      have hker : RingHom.ker aug' = N.map q := by
        apply le_antisymm
        · intro a ha
          obtain ⟨b, rfl⟩ := hq a
          exact Ideal.mem_map_of_mem _ ha
        · exact Ideal.map_le_iff_le_comap.2 fun a ha => ha
      have e := jetCoord_eq_of_sub_mem hG hv hx₁ hx₂ hx₃ aug' ((N ^ (k + 1)).map q)
        (by rw [hker, ← Ideal.map_mul, ← pow_succ]; exact Ideal.map_quotient_self _)
        (by rw [hker]; exact Ideal.map_mono (Ideal.pow_le_self (by omega)))
        (q.comp ψ) (q.comp ψ') (by rw [← AlgHom.comp_assoc, haug, hψ])
        (by rw [← AlgHom.comp_assoc, haug, hψ'])
        (fun j => by
          rw [AlgHom.comp_apply, AlgHom.comp_apply, ← map_sub]
          exact Ideal.mem_map_of_mem _ (ih j))
        (by rw [← spMap_comp, ← spMap_comp, Category.assoc, Category.assoc, h])
      intro j
      exact Ideal.Quotient.eq.1 (AlgHom.congr_fun e (zR m j)).symm
  refine jet_ext fun j => ?_
  have := main m j
  rw [hN, Ideal.mem_bot] at this
  exact (sub_eq_zero.1 this).symm

end GlobalTheory
