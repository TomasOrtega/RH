import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ ha, ih]`.
-/
private theorem zpow_sum_eq_prod_zpow {ι : Type*} {a : ℂ} (ha : a ≠ 0) (s : Finset ι) (e : ι → ℤ) :
    a ^ (∑ u ∈ s, e u) = ∏ u ∈ s, a ^ e u := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ ha, ih]

/- English proof (translation)
Introduce `hXi E _ _ _ n W j x ζ hζ k`. Take `⟨γ, t, h1, h2, h3, h4⟩` from `hζ.onRat k`. Use `⟨γ, h1, fun v => ?_⟩` and prove the remaining obligations. Establish `hs : xi0 W j γ v = _` using `hXi E n W j γ.1.1 γ.1.2 t h2 v`. Rewrite using `[hs]`.

Use `congr 1`. Rewrite using `[h4]`. Establish `e : ∀ u : InfinitePlace E, u.embedding (t : E) ^ (-∑ i, (W u).w i) = ∏ φ : E →+* ℂ, (if φ x = -u.embedding x then φ (k : E) else 1) ^ (-∑ i, (W u).w i)`. Introduce `u`. Rewrite using `[h3 u.embedding, Finset.prod_filter, Finset.prod_zpow]`.

Rewrite using `[Finset.prod_congr rfl fun u _ => e u, Finset.prod_comm, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun φ _ => ?_` and prove the remaining obligations. Establish `ha : φ (k : E) ≠ 0` using `(map_ne_zero φ).2 k.ne_zero`. Unfold `mOf`. Rewrite using `[zpow_sub₀ ha, div_eq_mul_inv, zpow_sum_eq_prod_zpow ha, ← Finset.prod_inv_distrib]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun u _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : φ x = -u.embedding x`. Establish `h' : u.embedding x = -φ x` using `by rw [h, neg_neg]`. Rewrite using `[if_pos h, if_pos h', _root_.zpow_neg]`.

Establish `h' : ¬ u.embedding x = -φ x` using `fun h'' => h (by rw [h'', neg_neg])`. Rewrite using `[if_neg h, if_neg h']`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Gal.CertificateRingHomMap.pXiZeta_of :
    UpperTheory.Gal.CertificateRingHomMap.XiScalar → UpperTheory.Gal.CertificateRingHomMap.XiZeta := by
  intro hXi E _ _ _ n W j x ζ hζ k
  obtain ⟨γ, t, h1, h2, h3, h4⟩ := hζ.onRat k
  refine ⟨γ, h1, fun v => ?_⟩
  have hs : xi0 W j γ v = _ := hXi E n W j γ.1.1 γ.1.2 t h2 v
  rw [hs]
  congr 1
  rw [h4]
  have e : ∀ u : InfinitePlace E, u.embedding (t : E) ^ (-∑ i, (W u).w i) =
      ∏ φ : E →+* ℂ, (if φ x = -u.embedding x then φ (k : E) else 1) ^ (-∑ i, (W u).w i) := by
    intro u
    rw [h3 u.embedding, Finset.prod_filter, Finset.prod_zpow]
  rw [Finset.prod_congr rfl fun u _ => e u, Finset.prod_comm, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun φ _ => ?_
  have ha : φ (k : E) ≠ 0 := (map_ne_zero φ).2 k.ne_zero
  unfold mOf
  rw [zpow_sub₀ ha, div_eq_mul_inv, zpow_sum_eq_prod_zpow ha, ← Finset.prod_inv_distrib]
  congr 1
  refine Finset.prod_congr rfl fun u _ => ?_
  by_cases h : φ x = -u.embedding x
  · have h' : u.embedding x = -φ x := by rw [h, neg_neg]
    rw [if_pos h, if_pos h', _root_.zpow_neg]
  · have h' : ¬ u.embedding x = -φ x := fun h'' => h (by rw [h'', neg_neg])
    rw [if_neg h, if_neg h']
    simp
