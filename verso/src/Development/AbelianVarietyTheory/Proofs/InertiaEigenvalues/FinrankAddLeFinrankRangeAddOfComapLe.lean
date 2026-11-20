import Mathlib

open TensorProduct Module

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ E A M _ _ _ _ _ _ π ν Z R U _ _ hZ hRU hU hmap`. Use `set Q := LinearMap.range π with hQ`. Use `set Z' : Submodule k Q := Z.comap Q.subtype`. Use `set R' : Submodule k U := R.comap U.subtype`. Establish `hZ' : finrank k Z' = finrank k Z` using `(Submodule.comapSubtypeEquivOfLe hZ).finrank_eq`.

Establish `hR' : finrank k R' = finrank k R` using `(Submodule.comapSubtypeEquivOfLe hRU).finrank_eq`. Use `set K : Submodule k E := U.comap ν`. Set `g : K →ₗ[k] Q ⧸ Z'` to `Z'.mkQ ∘ₗ π.rangeRestrict ∘ₗ K.subtype`. Set `f : K →ₗ[k] U ⧸ R'` to `R'.mkQ ∘ₗ ((ν ∘ₗ K.subtype).codRestrict U (fun x => x.2))`. Establish `hf : Function.Surjective f`.

Introduce `y`. Take `⟨u, rfl⟩` from `R'.mkQ_surjective y`. Take `⟨e, he⟩` from `hU u.2`. Establish `heU : ν e ∈ U` using `he ▸ u.2`. Use `⟨⟨e, heU⟩, ?_⟩` and prove the remaining obligations.

Establish `hu : ((ν ∘ₗ K.subtype).codRestrict U (fun x => x.2)) ⟨e, heU⟩ = u` using `Subtype.ext he`. Conclude with `congrArg R'.mkQ hu`. Establish `hker : LinearMap.ker g ≤ LinearMap.ker f`. Introduce `x hx`. Establish `h0 : Submodule.Quotient.mk (p` using `Z') (π.rangeRestrict (x : E)) = 0 := LinearMap.mem_ker.mp hx`.

Establish `hx' : π (x : E) ∈ Z` using `(Submodule.Quotient.mk_eq_zero (p := Z')).mp h0`. Establish `hy : ν (x : E) ∈ R` using `hmap _ hx'`. Rewrite using `[LinearMap.mem_ker]`. Conclude with `(Submodule.Quotient.mk_eq_zero (p := R') (x := ((ν ∘ₗ K.subtype).codRestrict U (fun x => x.2)) x)).mpr hy`. Set `gq` to `(LinearMap.ker g).liftQ g le_rfl`.

Set `fq` to `(LinearMap.ker g).liftQ f hker`. Establish `hgq : Function.Injective gq`. Rewrite using `[← LinearMap.ker_eq_bot]`. Conclude with `Submodule.ker_liftQ_eq_bot _ _ _ le_rfl`. Establish `hfq : Function.Surjective fq`.

Introduce `y`. Take `⟨x, rfl⟩` from `hf y`. Conclude with `⟨Submodule.Quotient.mk x, rfl⟩`. Establish `: Module.Finite k (K ⧸ LinearMap.ker g)` using `Module.Finite.of_injective gq hgq`. Establish `key : finrank k (U ⧸ R') ≤ finrank k (Q ⧸ Z')` using `(LinearMap.finrank_le_finrank_of_surjective hfq).trans (LinearMap.finrank_le_finrank_of_injective hgq)`.

Establish `h1` using `Submodule.finrank_quotient_add_finrank R'`. Establish `h2` using `Submodule.finrank_quotient_add_finrank Z'`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_add_le_finrank_range_add_of_comap_le : ∀ (k : Type) [Field k] (E A M : Type) [AddCommGroup E] [Module k E] [AddCommGroup A] [Module k A] [AddCommGroup M] [Module k M] (π : E →ₗ[k] A) (ν : E →ₗ[k] M) (Z : Submodule k A) (R U : Submodule k M) [FiniteDimensional k ↥(LinearMap.range π)] [FiniteDimensional k ↥U], Z ≤ LinearMap.range π → R ≤ U → U ≤ LinearMap.range ν → (∀ e, π e ∈ Z → ν e ∈ R) → finrank k ↥Z + finrank k ↥U ≤ finrank k ↥(LinearMap.range π) + finrank k ↥R := by
  intro k _ E A M _ _ _ _ _ _ π ν Z R U _ _ hZ hRU hU hmap
  set Q := LinearMap.range π with hQ
  set Z' : Submodule k Q := Z.comap Q.subtype
  set R' : Submodule k U := R.comap U.subtype
  have hZ' : finrank k Z' = finrank k Z := (Submodule.comapSubtypeEquivOfLe hZ).finrank_eq
  have hR' : finrank k R' = finrank k R := (Submodule.comapSubtypeEquivOfLe hRU).finrank_eq
  set K : Submodule k E := U.comap ν
  let g : K →ₗ[k] Q ⧸ Z' := Z'.mkQ ∘ₗ π.rangeRestrict ∘ₗ K.subtype
  let f : K →ₗ[k] U ⧸ R' := R'.mkQ ∘ₗ ((ν ∘ₗ K.subtype).codRestrict U (fun x => x.2))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨u, rfl⟩ := R'.mkQ_surjective y
    obtain ⟨e, he⟩ := hU u.2
    have heU : ν e ∈ U := he ▸ u.2
    refine ⟨⟨e, heU⟩, ?_⟩
    have hu : ((ν ∘ₗ K.subtype).codRestrict U (fun x => x.2)) ⟨e, heU⟩ = u := Subtype.ext he
    exact congrArg R'.mkQ hu
  have hker : LinearMap.ker g ≤ LinearMap.ker f := by
    intro x hx
    have h0 : Submodule.Quotient.mk (p := Z') (π.rangeRestrict (x : E)) = 0 := LinearMap.mem_ker.mp hx
    have hx' : π (x : E) ∈ Z := (Submodule.Quotient.mk_eq_zero (p := Z')).mp h0
    have hy : ν (x : E) ∈ R := hmap _ hx'
    rw [LinearMap.mem_ker]
    exact (Submodule.Quotient.mk_eq_zero (p := R')
      (x := ((ν ∘ₗ K.subtype).codRestrict U (fun x => x.2)) x)).mpr hy
  let gq := (LinearMap.ker g).liftQ g le_rfl
  let fq := (LinearMap.ker g).liftQ f hker
  have hgq : Function.Injective gq := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  have hfq : Function.Surjective fq := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have : Module.Finite k (K ⧸ LinearMap.ker g) := Module.Finite.of_injective gq hgq
  have key : finrank k (U ⧸ R') ≤ finrank k (Q ⧸ Z') :=
    (LinearMap.finrank_le_finrank_of_surjective hfq).trans
      (LinearMap.finrank_le_finrank_of_injective hgq)
  have h1 := Submodule.finrank_quotient_add_finrank R'
  have h2 := Submodule.finrank_quotient_add_finrank Z'
  omega

end GlobalTheory
