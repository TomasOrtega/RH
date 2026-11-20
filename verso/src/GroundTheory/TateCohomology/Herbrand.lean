import Mathlib
import GroundTheory.TateCohomology.HerbrandTate
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

universe u

open CategoryTheory Rep.FiniteCyclicGroup

section CommGroup

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G] (A : Rep.{u} R G) {σ : G}
  (hσ : ∀ x, x ∈ Subgroup.zpowers σ)

include hσ in

/- English proof (translation)
Use extensionality with `x`. Simplify `Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ σ hσ x` using `[Rep.sub_hom, Rep.applyAsHom, sub_eq_zero]`.
-/
theorem invariants_eq_ker_normHomCompSub_g :
    A.ρ.invariants = LinearMap.ker (normHomCompSub A σ).g.hom := by
  ext x
  simpa [Rep.sub_hom, Rep.applyAsHom, sub_eq_zero] using
    Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ σ hσ x

include hσ in
/- English proof (translation)
Use extensionality with `⟨y, hy⟩`. Rewrite using `[Submodule.mem_map, LinearMap.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨z, hz⟩, ⟨m, hm⟩, he⟩`. Use `⟨m, Subtype.ext ?_⟩` and prove the remaining obligations.

Establish `he'` using `congrArg Subtype.val he`. Express the relevant statement in the definitionally equal form `(z : A) = y at he'`. Express the relevant statement in the definitionally equal form `A.ρ.norm m = y`. Rewrite using `[← he']`. Conclude with `hm`.

Introduce and unpack `⟨m, hm⟩`. Establish `hm'` using `congrArg Subtype.val hm`. Express the relevant statement in the definitionally equal form `A.ρ.norm m = y at hm'`. Use `⟨⟨A.ρ.norm m, fun g => Representation.self_norm_apply A.ρ g m⟩, ⟨m, rfl⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Conclude with `hm'`.
-/
theorem normRangeInvariants_map :
    (normRangeInvariants A).map
        (LinearEquiv.ofEq _ _ (invariants_eq_ker_normHomCompSub_g A hσ) :
          A.ρ.invariants →ₗ[R] LinearMap.ker (normHomCompSub A σ).g.hom) =
      LinearMap.range (normHomCompSub A σ).moduleCatToCycles := by
  ext ⟨y, hy⟩
  rw [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨⟨z, hz⟩, ⟨m, hm⟩, he⟩
    refine ⟨m, Subtype.ext ?_⟩
    have he' := congrArg Subtype.val he
    change (z : A) = y at he'
    change A.ρ.norm m = y
    rw [← he']
    exact hm
  · rintro ⟨m, hm⟩
    have hm' := congrArg Subtype.val hm
    change A.ρ.norm m = y at hm'
    refine ⟨⟨A.ρ.norm m, fun g => Representation.self_norm_apply A.ρ g m⟩, ⟨m, rfl⟩, Subtype.ext ?_⟩
    exact hm'

noncomputable def tateCohomologyZeroIsoHomology :
    tateCohomology A 0 ≅ (normHomCompSub A σ).homology :=
  (tateCohomologyZeroIso R G).app A ≪≫
    (Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (invariants_eq_ker_normHomCompSub_g A hσ))
      (normRangeInvariants_map A hσ)).toModuleIso ≪≫
    (normHomCompSub A σ).moduleCatHomologyIso.symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ker_norm_eq_ker_subCompNormHom_g :
    LinearMap.ker A.ρ.norm = LinearMap.ker (subCompNormHom A σ).g.hom :=
  rfl

include hσ in
/- English proof (translation)
Establish `hc` using `Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ σ hσ`. Use extensionality with `⟨y, hy⟩`. Rewrite using `[Submodule.mem_map, LinearMap.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨z, hz⟩, hzm, he⟩`.

Establish `he'` using `congrArg Subtype.val he`. Express the relevant statement in the definitionally equal form `(z : A) = y at he'`. Rewrite `hzm` using `[mem_augmentationKerNorm_iff, hc]`. Take `⟨m, hm⟩` from `hzm`. Use `⟨m, Subtype.ext ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `A.ρ σ m - m = y`. Rewrite using `[← he']`. Conclude with `hm`. Introduce and unpack `⟨m, hm⟩`. Establish `hm'` using `congrArg Subtype.val hm`.

Express the relevant statement in the definitionally equal form `A.ρ σ m - m = y at hm'`. Use `⟨⟨y, hy⟩, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[mem_augmentationKerNorm_iff, hc]`. Conclude with `⟨m, hm'⟩`.
-/
theorem augmentationKerNorm_map :
    (augmentationKerNorm A).map
        (LinearEquiv.ofEq _ _ (ker_norm_eq_ker_subCompNormHom_g A (σ := σ)) :
          LinearMap.ker A.ρ.norm →ₗ[R] LinearMap.ker (subCompNormHom A σ).g.hom) =
      LinearMap.range (subCompNormHom A σ).moduleCatToCycles := by
  have hc := Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ σ hσ
  ext ⟨y, hy⟩
  rw [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨⟨z, hz⟩, hzm, he⟩
    have he' := congrArg Subtype.val he
    change (z : A) = y at he'
    rw [mem_augmentationKerNorm_iff, hc] at hzm
    obtain ⟨m, hm⟩ := hzm
    refine ⟨m, Subtype.ext ?_⟩
    change A.ρ σ m - m = y
    rw [← he']
    exact hm
  · rintro ⟨m, hm⟩
    have hm' := congrArg Subtype.val hm
    change A.ρ σ m - m = y at hm'
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    rw [mem_augmentationKerNorm_iff, hc]
    exact ⟨m, hm'⟩

noncomputable def tateCohomologyNegOneIsoHomology :
    tateCohomology A (-1) ≅ (subCompNormHom A σ).homology :=
  (tateCohomologyNegOneIso R G).app A ≪≫
    (Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (ker_norm_eq_ker_subCompNormHom_g A))
      (augmentationKerNorm_map A hσ)).toModuleIso ≪≫
    (subCompNormHom A σ).moduleCatHomologyIso.symm

/- English proof (translation)
Rewrite `h` using `[Int.negSucc_eq, even_neg, ← Nat.cast_succ, Int.even_coe_nat, Nat.even_add_one]`. Conclude with `Nat.not_even_iff_odd.1 h`.
-/
theorem odd_of_even_negSucc {i : ℕ} (h : Even (Int.negSucc i)) : Odd i := by
  rw [Int.negSucc_eq, even_neg, ← Nat.cast_succ, Int.even_coe_nat, Nat.even_add_one] at h
  exact Nat.not_even_iff_odd.1 h

/- English proof (translation)
Rewrite `h` using `[Int.negSucc_eq, odd_neg, ← Nat.cast_succ, Int.odd_coe_nat, Nat.odd_add_one]`. Conclude with `Nat.not_odd_iff_even.1 h`.
-/
theorem even_of_odd_negSucc {i : ℕ} (h : Odd (Int.negSucc i)) : Even i := by
  rw [Int.negSucc_eq, odd_neg, ← Nat.cast_succ, Int.odd_coe_nat, Nat.odd_add_one] at h
  exact Nat.not_odd_iff_even.1 h

variable [DecidableEq G]

noncomputable def tateCohomologyIsoEven :
    ∀ n : ℤ, Even n → (tateCohomology A n ≅ (normHomCompSub A σ).homology)
  | .ofNat 0, _ => tateCohomologyZeroIsoHomology A hσ
  | .ofNat (i + 1), hn =>
      (TateCohomology.isoGroupCohomology (i + 1)).app A ≪≫
        groupCohomologyIsoEven A σ hσ (i + 1) ((Int.even_coe_nat (i + 1)).1 hn)
  | .negSucc i, hn =>
      haveI : NeZero i := ⟨fun h => by
        have := odd_of_even_negSucc hn
        rw [h] at this
        exact Nat.not_odd_zero this⟩
      (TateCohomology.isoGroupHomology (Int.negSucc i) i (Int.negSucc_eq i)).app A ≪≫
        groupHomologyIsoOdd A σ hσ i (odd_of_even_negSucc hn)

noncomputable def tateCohomologyIsoOdd :
    ∀ n : ℤ, Odd n → (tateCohomology A n ≅ (subCompNormHom A σ).homology)
  | .ofNat 0, hn => absurd hn (by decide)
  | .ofNat (i + 1), hn =>
      (TateCohomology.isoGroupCohomology (i + 1)).app A ≪≫
        groupCohomologyIsoOdd A σ hσ (i + 1) ((Int.odd_coe_nat (i + 1)).1 hn)
  | .negSucc 0, _ => tateCohomologyNegOneIsoHomology A hσ
  | .negSucc (i + 1), hn =>
      (TateCohomology.isoGroupHomology (Int.negSucc (i + 1)) (i + 1)
          (Int.negSucc_eq (i + 1))).app A ≪≫
        groupHomologyIsoEven A σ hσ (i + 1) (even_of_odd_negSucc hn)

noncomputable def tateCohomologyPeriodicIsoOfComm (n : ℤ) :
    tateCohomology A (n + 2) ≅ tateCohomology A n :=
  if h : Even n then
    tateCohomologyIsoEven A hσ (n + 2) (h.add even_two) ≪≫ (tateCohomologyIsoEven A hσ n h).symm
  else
    tateCohomologyIsoOdd A hσ (n + 2) ((Int.not_even_iff_odd.1 h).add_even even_two) ≪≫
      (tateCohomologyIsoOdd A hσ n (Int.not_even_iff_odd.1 h)).symm

end CommGroup

noncomputable def tateCohomologyPeriodicIso {R G : Type u} [CommRing R] [Group G] [Fintype G]
    (A : Rep.{u} R G) {σ : G} (hσ : ∀ x, x ∈ Subgroup.zpowers σ) (n : ℤ) :
    tateCohomology A (n + 2) ≅ tateCohomology A n := by
  classical
  letI : CommGroup G :=
    { (inferInstance : Group G) with
      mul_comm := fun a b => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hσ a)
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hσ b)
        exact zpow_mul_comm σ i j }
  exact tateCohomologyPeriodicIsoOfComm A hσ n

end GroundTheory.GroupCoh
