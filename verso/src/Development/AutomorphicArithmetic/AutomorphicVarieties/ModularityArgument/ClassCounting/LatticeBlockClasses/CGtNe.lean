import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.MemPowEqv

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

/- English proof (translation)
Introduce `hS L F _ _ _ _ _ J _ q _ ζ χ η 𝔡 h`. Establish `hsum : ∀ x : ZMod q, ∑ i : {j // χ j = x}, η i.1 = 0`. Introduce `x`. Establish `h1 : η.mapDomain χ x = 0` using `by rw [h]; rfl`. Rewrite `h1` using `[Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp), Finsupp.finset_sum_apply]`.

Rewrite using `[← h1, ← Finset.sum_subtype (Finset.univ.filter fun j => χ j = x) (by simp) (fun j => η j), Finset.sum_filter]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.single_apply]`. Establish `hex : ∀ x : ZMod q, ∃ g : ({j // χ j = x} → F) ≃ₗ[F] ({j // χ j = x} → F), LinearEquiv.det g = 1 ∧ ∀ w, InLat 0 w ↔ InLat (fun i : {j // χ j = x} => η i.1 • 𝔡) (g w)`. Introduce `x`.

Use `hS F {j // χ j = x} 0 (fun i => η i.1 • 𝔡) 1 (Or.inr rfl) fun P => ?_` and prove the remaining obligations. Simplify using `only [Pi.zero_apply, Finsupp.coe_zero, sub_zero, Finsupp.smul_apply, smul_eq_mul]`. Rewrite using `[← Finset.sum_mul, hsum, zero_mul]`. Simplify using `[ordP]`. Use `choose g' hdet hlat using hex`.

Take `⟨⟨g, hg⟩, hall⟩` from `cBlock L F J (ZMod q) (fun _ => 1) χ g'`. Use `⟨g, (hall g hg).2.2 _ (fun j => η j • 𝔡) (fun j P => ?_) hlat, fun _ => 1, χ, g', hg, fun j => ?_, hdet⟩` and prove the remaining obligations. Rewrite using `[(cAct L F).2.2.1]`. Use `congr 1`.
-/
theorem UpperTheory.V.ZK.Cl.cGtNe :
    UpperTheory.V.ZK.Cl.CGtNe := by
  intro hS L F _ _ _ _ _ J _ q _ ζ χ η 𝔡 h
  classical
  have hsum : ∀ x : ZMod q, ∑ i : {j // χ j = x}, η i.1 = 0 := by
    intro x
    have h1 : η.mapDomain χ x = 0 := by rw [h]; rfl
    rw [Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp), Finsupp.finset_sum_apply] at h1
    rw [← h1, ← Finset.sum_subtype (Finset.univ.filter fun j => χ j = x) (by simp) (fun j => η j), Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finsupp.single_apply]
  have hex : ∀ x : ZMod q, ∃ g : ({j // χ j = x} → F) ≃ₗ[F] ({j // χ j = x} → F), LinearEquiv.det g = 1 ∧
      ∀ w, InLat 0 w ↔ InLat (fun i : {j // χ j = x} => η i.1 • 𝔡) (g w) := by
    intro x
    refine hS F {j // χ j = x} 0 (fun i => η i.1 • 𝔡) 1 (Or.inr rfl) fun P => ?_
    simp only [Pi.zero_apply, Finsupp.coe_zero, sub_zero, Finsupp.smul_apply, smul_eq_mul]
    rw [← Finset.sum_mul, hsum, zero_mul]
    simp [ordP]
  choose g' hdet hlat using hex
  obtain ⟨⟨g, hg⟩, hall⟩ := cBlock L F J (ZMod q) (fun _ => 1) χ g'
  refine ⟨g, (hall g hg).2.2 _ (fun j => η j • 𝔡) (fun j P => ?_) hlat, fun _ => 1, χ, g', hg, fun j => ?_, hdet⟩
  · rw [(cAct L F).2.2.1]
  · congr 1
