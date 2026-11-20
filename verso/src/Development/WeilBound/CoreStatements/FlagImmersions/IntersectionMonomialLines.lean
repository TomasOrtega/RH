import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

namespace Ii

/- English proof (translation)
Establish `hc : ∀ j, Fintype.card {a // f a = j} = Fintype.card {a // g a = j}`. Introduce `j`. Use `congrArg (Multiset.count j) h` as an intermediate fact. Simplify using `only [Multiset.count_map] at this`. Rewrite using `[Fintype.card_subtype, Fintype.card_subtype]`.

Apply the tactic sequence `convert this using 1 <;> simp [Finset.card_def, Finset.filter_val, eq_comm]`. Set `e : ∀ j, {a // f a = j} ≃ {a // g a = j}` to `fun j => Fintype.equivOfCardEq (hc j)`. Set `σ : Equiv.Perm α` to `((Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaCongrRight e)).trans (Equiv.sigmaFiberEquiv g)`. Use `⟨σ, fun a => ?_⟩` and prove the remaining obligations. Conclude with `(e (f a) ⟨a, rfl⟩).2`.
-/
theorem exists_perm_of_map_eq {α J : Type} [Fintype α] (f g : α → J)
    (h : Finset.univ.val.map f = Finset.univ.val.map g) : ∃ σ : Equiv.Perm α, ∀ a, g (σ a) = f a := by
  classical
  have hc : ∀ j, Fintype.card {a // f a = j} = Fintype.card {a // g a = j} := by
    intro j
    have := congrArg (Multiset.count j) h
    simp only [Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    convert this using 1 <;> simp [Finset.card_def, Finset.filter_val, eq_comm]
  let e : ∀ j, {a // f a = j} ≃ {a // g a = j} := fun j => Fintype.equivOfCardEq (hc j)
  let σ : Equiv.Perm α :=
    ((Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaCongrRight e)).trans (Equiv.sigmaFiberEquiv g)
  refine ⟨σ, fun a => ?_⟩
  exact (e (f a) ⟨a, rfl⟩).2

/- English proof (translation)
Rewrite using `[Finsupp.toMultiset_sum]`. Simplify using `only [Finsupp.toMultiset_single, one_smul]`. Rewrite using `[← Multiset.sum_map_singleton (Finset.univ.val.map w), Multiset.map_map]`. Both sides reduce to the same expression.
-/
theorem toMultiset_sum_single {d : ℕ} {J : Type} (w : Fin d → J) :
    Finsupp.toMultiset (∑ k, Finsupp.single (w k) 1 : J →₀ ℕ) = Finset.univ.val.map w := by
  rw [Finsupp.toMultiset_sum]
  simp only [Finsupp.toMultiset_single, one_smul]
  rw [← Multiset.sum_map_singleton (Finset.univ.val.map w), Multiset.map_map]
  rfl

end Ii

open Ii in
/- English proof (translation)
Introduce `II hII K _ ι _ P d J ℓ w hP hℓ`. Use `set m : J →₀ ℕ := ∑ k, Finsupp.single (w k) 1 with hm`. Establish `hdeg : m.degree = d`. Simplify using `[hm, map_sum, Finsupp.degree_single]`. Use `set L : List J := (Finsupp.toMultiset m).toList with hL`.

Establish `hML : (L : Multiset J) = Finset.univ.val.map w`. Rewrite using `[hL, Multiset.coe_toList, hm, toMultiset_sum_single]`. Establish `hlen : L.length = d`. Use `congrArg Multiset.card hML` as an intermediate fact. Simplify using `using this`.

Set `f : Fin d → J` to `fun k => L.get (Fin.cast hlen.symm k)`. Establish `hf : List.ofFn f = L` using `List.ext_get (by simp [hlen]) (fun i h1 h2 => by simp [f])`. Establish `hmap : Finset.univ.val.map f = Finset.univ.val.map w`. Rewrite using `[Fin.univ_val_map, hf, hML]`. Take `⟨σ, hσ⟩` from `exists_perm_of_map_eq f w hmap`.

Establish `hmono : monoLines ℓ m d = (fun k => ℓ (w k)) ∘ σ`. Use function extensionality and compare the values at `k`. Establish `hk : (k : ℕ) < L.length`. Rewrite using `[hlen]`. Conclude with `k.2`.

Simplify using `only [monoLines, Function.comp_apply, hσ k]`. Rewrite using `[dif_pos hk]`. Both sides reduce to the same expression. Use `⟨hdeg, σ, hmono, ?_⟩` and prove the remaining obligations. Rewrite using `[hmono]`.

Conclude with `(hII K ι).1 P d (fun k => ℓ (w k)) σ hP (fun j => hℓ _)`.
-/
theorem intersection_monomial_lines : ∀ II : IntersectionSystem, IsIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (J : Type) (ℓ : J → HermLine ι) (w : Fin d → J), IsArithVar P d → (∀ j, IsSmoothHerm (ℓ j)) → (∑ k, Finsupp.single (w k) 1 : J →₀ ℕ).degree = d ∧ ∃ σ : Equiv.Perm (Fin d), monoLines ℓ (∑ k, Finsupp.single (w k) 1) d = (fun k => ℓ (w k)) ∘ σ ∧ II K ι P d (monoLines ℓ (∑ k, Finsupp.single (w k) 1) d) = II K ι P d (fun k => ℓ (w k)) := by
  intro II hII K _ ι _ P d J ℓ w hP hℓ
  set m : J →₀ ℕ := ∑ k, Finsupp.single (w k) 1 with hm
  have hdeg : m.degree = d := by
    simp [hm, map_sum, Finsupp.degree_single]
  set L : List J := (Finsupp.toMultiset m).toList with hL
  have hML : (L : Multiset J) = Finset.univ.val.map w := by
    rw [hL, Multiset.coe_toList, hm, toMultiset_sum_single]
  have hlen : L.length = d := by
    have := congrArg Multiset.card hML
    simpa using this
  let f : Fin d → J := fun k => L.get (Fin.cast hlen.symm k)
  have hf : List.ofFn f = L :=
    List.ext_get (by simp [hlen]) (fun i h1 h2 => by simp [f])
  have hmap : Finset.univ.val.map f = Finset.univ.val.map w := by
    rw [Fin.univ_val_map, hf, hML]
  obtain ⟨σ, hσ⟩ := exists_perm_of_map_eq f w hmap
  have hmono : monoLines ℓ m d = (fun k => ℓ (w k)) ∘ σ := by
    funext k
    have hk : (k : ℕ) < L.length := by
      rw [hlen]
      exact k.2
    simp only [monoLines, Function.comp_apply, hσ k]
    rw [dif_pos hk]
    rfl
  refine ⟨hdeg, σ, hmono, ?_⟩
  rw [hmono]
  exact (hII K ι).1 P d (fun k => ℓ (w k)) σ hP (fun j => hℓ _)

end RootFieldNumerics
