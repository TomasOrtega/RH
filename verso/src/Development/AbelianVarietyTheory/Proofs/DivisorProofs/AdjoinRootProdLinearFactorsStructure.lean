import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

noncomputable section
namespace GlobalTheory.RingFacts

variable {O : Type} [CommRing O] {S : Type} [Fintype S] [DecidableEq S]

/- English proof (translation)
The claim follows from `monic_prod_of_monic _ _ fun s _ => monic_X_sub_C (a s)`.
-/
theorem monic_Q (a : S → O) : (∏ s, (X - Polynomial.C (a s)) : O[X]).Monic :=
  monic_prod_of_monic _ _ fun s _ => monic_X_sub_C (a s)

/- English proof (translation)
Simplify using `[lin, AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]`.
-/
theorem lin_eq (a : S → O) (s : S) :
    lin a s = AdjoinRoot.mk (∏ s, (X - Polynomial.C (a s)) : O[X]) (X - Polynomial.C (a s)) := by
  simp [lin, AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]

/- English proof (translation)
Rewrite using `[cofac, map_prod]`. Conclude with `Finset.prod_congr rfl fun s _ => lin_eq a s`.
-/
theorem cofac_eq (a : S → O) (τ : S) :
    cofac a τ = AdjoinRoot.mk (∏ s, (X - Polynomial.C (a s)) : O[X])
      (∏ s ∈ Finset.univ.erase τ, (X - Polynomial.C (a s))) := by
  rw [cofac, map_prod]
  exact Finset.prod_congr rfl fun s _ => lin_eq a s

/- English proof (translation)
Simplify using `[ev]`.
-/
theorem ev_mk (a : S → O) (τ : S) (f : O[X]) :
    ev a τ (AdjoinRoot.mk _ f) = f.eval (a τ) := by
  simp [ev]

/- English proof (translation)
Take `⟨f, rfl⟩` from `AdjoinRoot.mk_surjective r`. Rewrite `hr` using `[ev_mk]`. Take `⟨h, hh⟩` from `(Polynomial.dvd_iff_isRoot).2 hr`. Conclude with `⟨AdjoinRoot.mk _ h, by rw [hh, map_mul, lin_eq]⟩`.
-/
theorem exists_lin_mul_of_ev_eq_zero (a : S → O) (τ : S) (r : RS a) (hr : ev a τ r = 0) :
    ∃ r', r = lin a τ * r' := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective r
  rw [ev_mk] at hr
  obtain ⟨h, hh⟩ := (Polynomial.dvd_iff_isRoot).2 hr
  exact ⟨AdjoinRoot.mk _ h, by rw [hh, map_mul, lin_eq]⟩

/- English proof (translation)
Take `⟨g, hg⟩` from `exists_lin_mul_of_ev_eq_zero a τ (r - algebraMap O (RS a) (ev a τ r)) (by rw [map_sub, AlgHom.commutes]; simp)`. Conclude with `⟨g, by rw [← hg]; ring⟩`.
-/
theorem eq_algebraMap_add_lin_mul (a : S → O) (τ : S) (r : RS a) :
    ∃ g, r = algebraMap O (RS a) (ev a τ r) + lin a τ * g := by
  obtain ⟨g, hg⟩ := exists_lin_mul_of_ev_eq_zero a τ (r - algebraMap O (RS a) (ev a τ r))
    (by rw [map_sub, AlgHom.commutes]; simp)
  exact ⟨g, by rw [← hg]; ring⟩

/- English proof (translation)
Rewrite using `[cofac, Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Finset.prod_congr rfl (fun s _ => lin_eq a s), ← map_prod]`. Conclude with `AdjoinRoot.mk_self`.
-/
theorem lin_mul_cofac (a : S → O) (τ : S) : lin a τ * cofac a τ = 0 := by
  rw [cofac, Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Finset.prod_congr rfl
    (fun s _ => lin_eq a s), ← map_prod]
  exact AdjoinRoot.mk_self

/- English proof (translation)
Rewrite using `[cofac, map_prod]`. Conclude with `Finset.prod_congr rfl fun s _ => ev_lin a τ s`.
-/
theorem ev_cofac (a : S → O) (τ : S) :
    ev a τ (cofac a τ) = ∏ s ∈ Finset.univ.erase τ, (a τ - a s) := by
  rw [cofac, map_prod]
  exact Finset.prod_congr rfl fun s _ => ev_lin a τ s

/- English proof (translation)
Take `⟨f, rfl⟩` from `AdjoinRoot.mk_surjective r`. Rewrite `hr` using `[lin_eq, ← map_mul, AdjoinRoot.mk_eq_zero]`. Take `⟨g, hg⟩` from `hr`. Rewrite `hg` using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), mul_assoc]`. Establish `hf : f = (∏ s ∈ Finset.univ.erase τ, (X - Polynomial.C (a s))) * g` using `mul_left_cancel₀ (X_sub_C_ne_zero (a τ)) hg`.

Take `⟨h, hh⟩` from `eq_algebraMap_add_lin_mul a τ (AdjoinRoot.mk _ g)`. Use `⟨ev a τ (AdjoinRoot.mk _ g), ?_⟩` and prove the remaining obligations. Establish `hc` using `lin_mul_cofac a τ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hh]`.

Use `_ = algebraMap O (RS a) (ev a τ (AdjoinRoot.mk _ g)) * cofac a τ + (lin a τ * cofac a τ) * h := by ring`. Use `_ = _ := by rw [hc]; simp`.
-/
theorem eq_smul_cofac_of_lin_mul_eq_zero [IsDomain O] (a : S → O) (τ : S) (r : RS a)
    (hr : lin a τ * r = 0) : ∃ c : O, r = algebraMap O (RS a) c * cofac a τ := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective r
  rw [lin_eq, ← map_mul, AdjoinRoot.mk_eq_zero] at hr
  obtain ⟨g, hg⟩ := hr
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), mul_assoc] at hg
  have hf : f = (∏ s ∈ Finset.univ.erase τ, (X - Polynomial.C (a s))) * g :=
    mul_left_cancel₀ (X_sub_C_ne_zero (a τ)) hg
  obtain ⟨h, hh⟩ := eq_algebraMap_add_lin_mul a τ (AdjoinRoot.mk _ g)
  refine ⟨ev a τ (AdjoinRoot.mk _ g), ?_⟩
  have hc := lin_mul_cofac a τ
  calc AdjoinRoot.mk _ f = cofac a τ * AdjoinRoot.mk _ g := by rw [hf, map_mul, cofac_eq]
    _ = cofac a τ * (algebraMap O (RS a) (ev a τ (AdjoinRoot.mk _ g)) + lin a τ * h) := by
        rw [← hh]
    _ = algebraMap O (RS a) (ev a τ (AdjoinRoot.mk _ g)) * cofac a τ
        + (lin a τ * cofac a τ) * h := by ring
    _ = _ := by rw [hc]; simp

/- English proof (translation)
Introduce `O _ _ S _ _ a τ`. Set `pb` to `AdjoinRoot.powerBasis' (monic_Q a)`. Conclude with `⟨Module.Free.of_basis pb.basis, pb.finite, lin_mul_cofac a τ, ev_cofac a τ, exists_lin_mul_of_ev_eq_zero a τ, eq_algebraMap_add_lin_mul a τ (cofac a τ), eq_smul_cofac_of_lin_mul_eq_zero a τ⟩`.
-/
theorem ring_facts : ∀ (O : Type) [CommRing O] [IsDomain O] (S : Type) [Fintype S] [DecidableEq S]
    (a : S → O) (τ : S), Module.Free O (RS a) ∧ Module.Finite O (RS a) ∧
    lin a τ * cofac a τ = 0 ∧ ev a τ (cofac a τ) = ∏ s ∈ Finset.univ.erase τ, (a τ - a s) ∧
    (∀ r : RS a, ev a τ r = 0 → ∃ r', r = lin a τ * r') ∧
    (∃ g : RS a, cofac a τ = algebraMap O (RS a) (ev a τ (cofac a τ)) + lin a τ * g) ∧
    (∀ r : RS a, lin a τ * r = 0 → ∃ c : O, r = algebraMap O (RS a) c * cofac a τ) := by
  intro O _ _ S _ _ a τ
  let pb := AdjoinRoot.powerBasis' (monic_Q a)
  exact ⟨Module.Free.of_basis pb.basis, pb.finite, lin_mul_cofac a τ, ev_cofac a τ,
    exists_lin_mul_of_ev_eq_zero a τ, eq_algebraMap_add_lin_mul a τ (cofac a τ),
    eq_smul_cofac_of_lin_mul_eq_zero a τ⟩

end GlobalTheory.RingFacts
