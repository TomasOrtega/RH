import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.KroneckerProductDet
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ProdFactorialSupportSubSingle

open Matrix MvPolynomial
open scoped Kronecker

noncomputable section

namespace Formalism.L2.Geo.Def
namespace KroneckerDeterminant

variable {R T : Type} [CommRing R] [Fintype T] [DecidableEq T] {I : T → Type} [∀ τ, Fintype (I τ)]
  [∀ τ, DecidableEq (I τ)] (A : ∀ τ, Matrix (I τ) (I τ) R)

def Ms (s : Finset T) : Matrix (∀ τ, I τ) (∀ τ, I τ) R :=
  Matrix.of fun i j => if (∀ τ, τ ∉ s → i τ = j τ) then ∏ τ ∈ s, A τ (i τ) (j τ) else 0

def Ba (a : T) : Matrix (∀ τ, I τ) (∀ τ, I τ) R :=
  Matrix.of fun i j => if (∀ τ, τ ≠ a → i τ = j τ) then A a (i a) (j a) else 0

end KroneckerDeterminant

namespace TensorFockForm

open Formalism.REAL

variable {T σ : Type} [Fintype T] [DecidableEq T]

def emb (g : T → σ →₀ ℕ) : T × σ →₀ ℕ := ∑ τ, Finsupp.mapDomain (Prod.mk τ) (g τ)

/- English proof (translation)
Introduce `_ _ h` and use `(Prod.mk.inj h).2`.
-/
lemma prodMk_inj (τ : T) : Function.Injective (Prod.mk τ : σ → T × σ) := fun _ _ h => (Prod.mk.inj h).2

/- English proof (translation)
Unfold `emb`. Rewrite using `[Finsupp.finsetSum_apply, Finset.sum_eq_single τ]`. Conclude with `Finsupp.mapDomain_apply (prodMk_inj τ) _ _`. Introduce `τ' _ hτ'`. Apply `Finsupp.mapDomain_of_notMem_range` to reduce the goal to its premises.

Introduce and unpack `⟨k', hk'⟩`. Conclude with `hτ' (Prod.mk.inj hk').1`. Introduce `h`. Conclude with `absurd (Finset.mem_univ τ) h`.
-/
lemma emb_apply (g : T → σ →₀ ℕ) (τ : T) (k : σ) : emb g (τ, k) = g τ k := by
  unfold emb
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single τ]
  · exact Finsupp.mapDomain_apply (prodMk_inj τ) _ _
  · intro τ' _ hτ'
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨k', hk'⟩
    exact hτ' (Prod.mk.inj hk').1
  · intro h; exact absurd (Finset.mem_univ τ) h

/- English proof (translation)
Introduce `g h hgh`. Use function extensionality and compare the values at `τ`. Use extensionality with `k`. Rewrite using `[← emb_apply g τ k, ← emb_apply h τ k, hgh]`.
-/
lemma emb_inj : Function.Injective (emb : (T → σ →₀ ℕ) → T × σ →₀ ℕ) := by
  intro g h hgh
  funext τ
  ext k
  rw [← emb_apply g τ k, ← emb_apply h τ k, hgh]

/- English proof (translation)
The claim follows from `Finset.prod_subset h (fun k _ hk => by simp [Finsupp.notMem_support_iff.mp hk])`.
-/
lemma fact_subset {α : Type} (u : α →₀ ℕ) (S : Finset α) (h : u.support ⊆ S) :
    ∏ k ∈ u.support, (u k).factorial = ∏ k ∈ S, (u k).factorial :=
  Finset.prod_subset h (fun k _ hk => by simp [Finsupp.notMem_support_iff.mp hk])

/- English proof (translation)
Use `set U : Finset σ := Finset.univ.biUnion fun τ => (g τ).support with hU`. Establish `hsub : (emb g).support ⊆ (Finset.univ : Finset T) ×ˢ U`. Introduce and unpack `⟨τ, k⟩ hx`. Rewrite `hx` using `[Finsupp.mem_support_iff, emb_apply]`. Simplify using `only [Finset.mem_product, Finset.mem_univ, true_and, hU, Finset.mem_biUnion]`.

Conclude with `⟨τ, Finsupp.mem_support_iff.mpr hx⟩`. Rewrite using `[fact_subset _ _ hsub, Finset.prod_product]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Simplify using `only [emb_apply]`. Use `(fact_subset (g τ) U ?_).symm` and prove the remaining obligations.

Introduce `k hk`. Simplify using `only [hU, Finset.mem_biUnion, Finset.mem_univ, true_and]`. Conclude with `⟨τ, hk⟩`.
-/
lemma fact_emb (g : T → σ →₀ ℕ) :
    ∏ x ∈ (emb g).support, (emb g x).factorial = ∏ τ, ∏ k ∈ (g τ).support, (g τ k).factorial := by
  classical
  set U : Finset σ := Finset.univ.biUnion fun τ => (g τ).support with hU
  have hsub : (emb g).support ⊆ (Finset.univ : Finset T) ×ˢ U := by
    rintro ⟨τ, k⟩ hx
    rw [Finsupp.mem_support_iff, emb_apply] at hx
    simp only [Finset.mem_product, Finset.mem_univ, true_and, hU, Finset.mem_biUnion]
    exact ⟨τ, Finsupp.mem_support_iff.mpr hx⟩
  rw [fact_subset _ _ hsub, Finset.prod_product]
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [emb_apply]
  refine (fact_subset (g τ) U ?_).symm
  intro k hk
  simp only [hU, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨τ, hk⟩

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Use `conv_lhs => rw [as_sum (p τ)]`. Rewrite using `[map_sum]`. Simplify using `only [rename_monomial]`.

Use `_ = ∑ g ∈ Fintype.piFinset (fun τ => (p τ).support), ∏ τ, monomial (Finsupp.mapDomain (Prod.mk τ) (g τ)) (coeff (g τ) (p τ)) := Finset.prod_univ_sum _ _`. Use `_ = _ := Finset.sum_congr rfl fun g _ => (monomial_sum_prod _ _ _).symm`.
-/
lemma prod_rename_eq (p : T → MvPolynomial σ ℂ) :
    ∏ τ, rename (Prod.mk τ) (p τ) =
      ∑ g ∈ Fintype.piFinset (fun τ => (p τ).support), monomial (emb g) (∏ τ, coeff (g τ) (p τ)) := by
  calc ∏ τ, rename (Prod.mk τ) (p τ)
      = ∏ τ, ∑ v ∈ (p τ).support, monomial (Finsupp.mapDomain (Prod.mk τ) v) (coeff v (p τ)) := by
        refine Finset.prod_congr rfl fun τ _ => ?_
        conv_lhs => rw [as_sum (p τ)]
        rw [map_sum]
        simp only [rename_monomial]
    _ = ∑ g ∈ Fintype.piFinset (fun τ => (p τ).support),
          ∏ τ, monomial (Finsupp.mapDomain (Prod.mk τ) (g τ)) (coeff (g τ) (p τ)) :=
        Finset.prod_univ_sum _ _
    _ = _ := Finset.sum_congr rfl fun g _ => (monomial_sum_prod _ _ _).symm

open Classical in
/- English proof (translation)
Rewrite using `[fischerInner_monomial_left, coeff_monomial]`. Distinguish the cases in `h : u = v`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg (Ne.symm h), if_neg h]`.

Simplify using the standard rewrite rules.
-/
lemma fock_mono (u v : σ →₀ ℕ) (a b : ℂ) :
    fockF (monomial u a) (monomial v b) =
      if u = v then a * star b * ((∏ k ∈ u.support, (u k).factorial : ℕ) : ℂ) else 0 := by
  rw [fischerInner_monomial_left, coeff_monomial]
  by_cases h : u = v
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]; simp

end TensorFockForm

open TensorFockForm Formalism.REAL in
/- English proof (translation)
Introduce `T σ _ _ p q`. Rewrite using `[prod_rename_eq p, prod_rename_eq q, fischerInner_sum_left]`. Repeatedly rewrite using `[fischerInner_sum_right, fock_mono]`. Establish `hR : ∀ τ, fockF (p τ) (q τ) = ∑ m ∈ (p τ).support, ∑ n ∈ (q τ).support, (if m = n then coeff m (p τ) * star (coeff n (q τ)) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) else 0)`. Introduce `τ`.

Use `conv_lhs => rw [as_sum (p τ), as_sum (q τ)]`. Rewrite using `[fischerInner_sum_left]`. Repeatedly rewrite using `[fischerInner_sum_right, fock_mono]`. Repeatedly rewrite using `[hR]`. Rewrite using `[Finset.prod_univ_sum]`.

Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_univ_sum]`. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Distinguish the cases in `hgh : g = h`. Substitute `hgh` using the available equality.

Simplify using `only [if_true]`. Rewrite using `[fact_emb]`. Use `push_cast`. Rewrite using `[star_prod, Finset.prod_mul_distrib, Finset.prod_mul_distrib]`. Rewrite using `[if_neg (fun e => hgh (emb_inj e))]`.

Take `⟨τ, hτ⟩` from `Function.ne_iff.mp hgh`. Conclude with `(Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ)).symm`.
-/
theorem TensorFock_holds : TensorFockProduct := by
  intro T σ _ _ p q
  classical
  rw [prod_rename_eq p, prod_rename_eq q, fischerInner_sum_left]
  simp_rw [fischerInner_sum_right, fock_mono]
  have hR : ∀ τ, fockF (p τ) (q τ) = ∑ m ∈ (p τ).support, ∑ n ∈ (q τ).support,
      (if m = n then coeff m (p τ) * star (coeff n (q τ)) *
        ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) else 0) := by
    intro τ
    conv_lhs => rw [as_sum (p τ), as_sum (q τ)]
    rw [fischerInner_sum_left]
    simp_rw [fischerInner_sum_right, fock_mono]
  simp_rw [hR]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  by_cases hgh : g = h
  · subst hgh
    simp only [if_true]
    rw [fact_emb]
    push_cast
    rw [star_prod, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  · rw [if_neg (fun e => hgh (emb_inj e))]
    obtain ⟨τ, hτ⟩ := Function.ne_iff.mp hgh
    exact (Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ)).symm

end Formalism.L2.Geo.Def
