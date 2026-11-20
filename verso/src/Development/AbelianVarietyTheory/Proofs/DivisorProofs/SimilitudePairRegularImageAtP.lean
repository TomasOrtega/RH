import Mathlib
import GroundTheory.Brauer.TensorSimple
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount Polynomial
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Use `letI : Algebra G.F (G.Fw w) := (G.embW w).toAlgebra`. Establish `hg : ∀ a, G.rho w (algebraMap G.F G.C a) = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) (G.Fw w)) a` using `fun a => by rw [G.rho_F, Matrix.algebraMap_eq_diagonal]; rfl`. Set `g : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) (G.Fw w)` to `{ G.rho w with commutes' := hg }`. Set `L : G.Fw w ⊗[G.F] G.C →ₐ[G.Fw w] Matrix (Fin G.n) (Fin G.n) (G.Fw w)` to `Algebra.TensorProduct.lift (Algebra.ofId (G.Fw w) _) g (fun r _ => Algebra.commute_algebraMap_left r _)`. Use `haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩`.

Establish `hinj : Function.Injective L` using `(IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right (not_subsingleton _)`. Establish `hL : ∀ x : G.C, L ((1 : G.Fw w) ⊗ₜ x) = G.rho w x` using `fun x => by show (Algebra.TensorProduct.lift _ g _) ((1 : G.Fw w) ⊗ₜ x) = _ erw [Algebra.TensorProduct.lift_tmul]`. Rewrite using `[map_one, one_mul]`. Both sides reduce to the same expression. Use `set γ : G.C := (P.γ : G.C) with hγ`.

Establish `hdeg : (minpoly G.F γ).natDegree = G.n` using `P.reg.1`. Establish `hli : LinearIndependent G.F (fun i : Fin G.n => γ ^ (i : ℕ))`. Use `linearIndependent_pow (K := G.F) γ` as an intermediate fact. Rewrite `this` using `[hdeg]`. Conclude with `this`.

Establish `hT : LinearIndependent (G.Fw w) (fun i : Fin G.n => (1 : G.Fw w) ⊗ₜ[G.F] (γ ^ (i : ℕ)))` using `Module.Flat.linearIndependent_one_tmul hli`. Establish `hM : LinearIndependent (G.Fw w) (fun i : Fin G.n => (G.rho w γ) ^ (i : ℕ))`. Use `hT.map' L.toLinearMap (LinearMap.ker_eq_bot.2 hinj)` as an intermediate fact. Establish `e : (fun i : Fin G.n => (G.rho w γ) ^ (i : ℕ)) = L.toLinearMap ∘ (fun i : Fin G.n => (1 : G.Fw w) ⊗ₜ[G.F] (γ ^ (i : ℕ)))`. Use function extensionality and compare the values at `i`.

Simplify using `only [Function.comp_apply, AlgHom.toLinearMap_apply]`. Rewrite using `[hL, map_pow]`. Rewrite using `[e]`. Conclude with `this`. Establish `hint : IsIntegral (G.Fw w) (G.rho w γ)` using `Algebra.IsIntegral.isIntegral _`.

Use `set q := minpoly (G.Fw w) (G.rho w γ) with hq`. Establish `hqm : q.Monic` using `minpoly.monic hint`. Establish `hqdeg : G.n ≤ q.natDegree`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Establish `h0 : aeval (G.rho w γ) q = 0` using `minpoly.aeval _ _`. Rewrite `h0` using `[Polynomial.aeval_eq_sum_range' hlt, Finset.sum_range]`. Establish `h1` using `Fintype.linearIndependent_iff.1 hM (fun i => q.coeff i) h0 ⟨q.natDegree, hlt⟩`. Establish `h2 : q.coeff q.natDegree = 1` using `hqm.coeff_natDegree`. Rewrite `h1` using `[h2]`.

Conclude with `one_ne_zero h1`. Establish `hpol : aeval (G.rho w γ) (P.pol.map (G.embW w)) = 0`. Establish `h : aeval (g γ) (minpoly G.F γ) = 0` using `by rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]`. Express the relevant statement in the definitionally equal form `aeval (G.rho w γ) ((minpoly G.F γ).map (algebraMap G.F (G.Fw w))) = 0`. Rewrite using `[Polynomial.aeval_map_algebraMap]`.

Conclude with `h`. Establish `hFint : IsIntegral G.F γ` using `Algebra.IsIntegral.isIntegral _`. Establish `hm1 : (P.pol.map (G.embW w)).Monic` using `(minpoly.monic hFint).map _`. Establish `hn1 : (P.pol.map (G.embW w)).natDegree = G.n`. Rewrite using `[Polynomial.natDegree_map]`.

Conclude with `hdeg`. Establish `e1` using `Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm hm1 (minpoly.dvd _ _ hpol) (by rw [hn1]; exact hqdeg)`. Establish `e2` using `Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm (Matrix.charpoly_monic _) (Matrix.minpoly_dvd_charpoly _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hqdeg)`. Rewrite using `[e2, e1]`.
-/
theorem charpoly_rho_eq_map_pol (G : HTGroup p) (P : Pair G) (w : Fin G.m) :
    (G.rho w (P.γ : G.C)).charpoly = P.pol.map (G.embW w) := by
  letI : Algebra G.F (G.Fw w) := (G.embW w).toAlgebra
  have hg : ∀ a, G.rho w (algebraMap G.F G.C a) = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) (G.Fw w)) a :=
    fun a => by rw [G.rho_F, Matrix.algebraMap_eq_diagonal]; rfl
  let g : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) (G.Fw w) := { G.rho w with commutes' := hg }
  let L : G.Fw w ⊗[G.F] G.C →ₐ[G.Fw w] Matrix (Fin G.n) (Fin G.n) (G.Fw w) :=
    Algebra.TensorProduct.lift (Algebra.ofId (G.Fw w) _) g (fun r _ => Algebra.commute_algebraMap_left r _)
  haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
  have hinj : Function.Injective L :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right (not_subsingleton _)
  have hL : ∀ x : G.C, L ((1 : G.Fw w) ⊗ₜ x) = G.rho w x := fun x => by
    show (Algebra.TensorProduct.lift _ g _) ((1 : G.Fw w) ⊗ₜ x) = _
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
    rfl
  set γ : G.C := (P.γ : G.C) with hγ
  have hdeg : (minpoly G.F γ).natDegree = G.n := P.reg.1
  have hli : LinearIndependent G.F (fun i : Fin G.n => γ ^ (i : ℕ)) := by
    have := linearIndependent_pow (K := G.F) γ
    rw [hdeg] at this
    exact this
  have hT : LinearIndependent (G.Fw w) (fun i : Fin G.n => (1 : G.Fw w) ⊗ₜ[G.F] (γ ^ (i : ℕ))) :=
    Module.Flat.linearIndependent_one_tmul hli
  have hM : LinearIndependent (G.Fw w) (fun i : Fin G.n => (G.rho w γ) ^ (i : ℕ)) := by
    have := hT.map' L.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
    have e : (fun i : Fin G.n => (G.rho w γ) ^ (i : ℕ)) =
        L.toLinearMap ∘ (fun i : Fin G.n => (1 : G.Fw w) ⊗ₜ[G.F] (γ ^ (i : ℕ))) := by
      funext i
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply]
      rw [hL, map_pow]
    rw [e]
    exact this
  have hint : IsIntegral (G.Fw w) (G.rho w γ) := Algebra.IsIntegral.isIntegral _
  set q := minpoly (G.Fw w) (G.rho w γ) with hq
  have hqm : q.Monic := minpoly.monic hint
  have hqdeg : G.n ≤ q.natDegree := by
    by_contra hlt
    push_neg at hlt
    have h0 : aeval (G.rho w γ) q = 0 := minpoly.aeval _ _
    rw [Polynomial.aeval_eq_sum_range' hlt, Finset.sum_range] at h0
    have h1 := Fintype.linearIndependent_iff.1 hM (fun i => q.coeff i) h0 ⟨q.natDegree, hlt⟩
    have h2 : q.coeff q.natDegree = 1 := hqm.coeff_natDegree
    rw [h2] at h1
    exact one_ne_zero h1
  have hpol : aeval (G.rho w γ) (P.pol.map (G.embW w)) = 0 := by
    have h : aeval (g γ) (minpoly G.F γ) = 0 := by rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    change aeval (G.rho w γ) ((minpoly G.F γ).map (algebraMap G.F (G.Fw w))) = 0
    rw [Polynomial.aeval_map_algebraMap]
    exact h
  have hFint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hm1 : (P.pol.map (G.embW w)).Monic := (minpoly.monic hFint).map _
  have hn1 : (P.pol.map (G.embW w)).natDegree = G.n := by
    rw [Polynomial.natDegree_map]; exact hdeg
  have e1 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm hm1 (minpoly.dvd _ _ hpol)
    (by rw [hn1]; exact hqdeg)
  have e2 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm (Matrix.charpoly_monic _)
    (Matrix.minpoly_dvd_charpoly _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hqdeg)
  rw [e2, e1]

/- English proof (translation)
Introduce `p _ G P`. Establish `h1 : ∀ w, (P.atP.2 w).val.charpoly = P.pol.map (G.embW w)` using `fun w => charpoly_rho_eq_map_pol G P w`. Use `⟨h1, fun w => ?_, fun y => ?_⟩` and prove the remaining obligations. Use `show (P.atP.2 w).val.charpoly.Separable`. Rewrite using `[h1]`.

Conclude with `P.reg.2.map`. Rewrite using `[Subgroup.mem_centralizer_singleton_iff] show locC G y.1 * locC G (P.γ, P.c) = locC G (P.γ, P.c) * locC G y.1`. Rewrite using `[← map_mul, ← map_mul]`. Use `congr 1`. Conclude with `Prod.ext y.2.1 (mul_comm _ _)`.
-/
theorem atP_regular : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G),
    (∀ w, (P.atP.2 w).val.charpoly = P.pol.map (G.embW w)) ∧ regular₂ G P.atP ∧
      ∀ y : P.cent, locC G y.1 ∈ Subgroup.centralizer {P.atP} := by
  intro p _ G P
  have h1 : ∀ w, (P.atP.2 w).val.charpoly = P.pol.map (G.embW w) := fun w => charpoly_rho_eq_map_pol G P w
  refine ⟨h1, fun w => ?_, fun y => ?_⟩
  · show (P.atP.2 w).val.charpoly.Separable
    rw [h1]
    exact P.reg.2.map
  · rw [Subgroup.mem_centralizer_singleton_iff]
    show locC G y.1 * locC G (P.γ, P.c) = locC G (P.γ, P.c) * locC G y.1
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext y.2.1 (mul_comm _ _)

end GlobalTheory.LKMid
