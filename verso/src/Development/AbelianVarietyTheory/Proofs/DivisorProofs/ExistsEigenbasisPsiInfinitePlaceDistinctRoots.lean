import Mathlib
import GroundTheory.Brauer.TensorSimple
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixDiagonalizableOfCharpolyEqProdDistinct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardRootsMapPol

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount Polynomial
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Use `letI : Algebra G.F ℂ := v.embedding.toAlgebra`. Establish `hg : ∀ a, G.psi v (algebraMap G.F G.C a) = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) ℂ) a` using `fun a => by rw [G.psi_F, Matrix.algebraMap_eq_diagonal]; rfl`. Set `g : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ` to `{ G.psi v with commutes' := hg }`. Set `L : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ` to `Algebra.TensorProduct.lift (Algebra.ofId ℂ _) g (fun r _ => Algebra.commute_algebraMap_left r _)`. Use `haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩`.

Establish `hinj : Function.Injective L` using `(IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right (not_subsingleton _)`. Establish `hL : ∀ x : G.C, L ((1 : ℂ) ⊗ₜ x) = G.psi v x` using `fun x => by show (Algebra.TensorProduct.lift _ g _) ((1 : ℂ) ⊗ₜ x) = _ erw [Algebra.TensorProduct.lift_tmul]`. Rewrite using `[map_one, one_mul]`. Both sides reduce to the same expression. Use `set γ : G.C := (P.γ : G.C) with hγ`.

Establish `hdeg : (minpoly G.F γ).natDegree = G.n` using `P.reg.1`. Establish `hli : LinearIndependent G.F (fun i : Fin G.n => γ ^ (i : ℕ))`. Use `linearIndependent_pow (K := G.F) γ` as an intermediate fact. Rewrite `this` using `[hdeg]`. Conclude with `this`.

Establish `hT : LinearIndependent ℂ (fun i : Fin G.n => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ)))` using `Module.Flat.linearIndependent_one_tmul hli`. Establish `hM : LinearIndependent ℂ (fun i : Fin G.n => (G.psi v γ) ^ (i : ℕ))`. Use `hT.map' L.toLinearMap (LinearMap.ker_eq_bot.2 hinj)` as an intermediate fact. Establish `e : (fun i : Fin G.n => (G.psi v γ) ^ (i : ℕ)) = L.toLinearMap ∘ (fun i : Fin G.n => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ)))`. Use function extensionality and compare the values at `i`.

Simplify using `only [Function.comp_apply, AlgHom.toLinearMap_apply]`. Rewrite using `[hL, map_pow]`. Rewrite using `[e]`. Conclude with `this`. Establish `hint : IsIntegral ℂ (G.psi v γ)` using `Algebra.IsIntegral.isIntegral _`.

Use `set q := minpoly ℂ (G.psi v γ) with hq`. Establish `hqm : q.Monic` using `minpoly.monic hint`. Establish `hqdeg : G.n ≤ q.natDegree`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Establish `h0 : aeval (G.psi v γ) q = 0` using `minpoly.aeval _ _`. Rewrite `h0` using `[Polynomial.aeval_eq_sum_range' hlt, Finset.sum_range]`. Establish `h1` using `Fintype.linearIndependent_iff.1 hM (fun i => q.coeff i) h0 ⟨q.natDegree, hlt⟩`. Establish `h2 : q.coeff q.natDegree = 1` using `hqm.coeff_natDegree`. Rewrite `h1` using `[h2]`.

Conclude with `one_ne_zero h1`. Establish `hpol : aeval (G.psi v γ) (P.pol.map v.embedding) = 0`. Establish `h : aeval (g γ) (minpoly G.F γ) = 0` using `by rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]`. Express the relevant statement in the definitionally equal form `aeval (G.psi v γ) ((minpoly G.F γ).map (algebraMap G.F ℂ)) = 0`. Rewrite using `[Polynomial.aeval_map_algebraMap]`.

Conclude with `h`. Establish `hFint : IsIntegral G.F γ` using `Algebra.IsIntegral.isIntegral _`. Establish `hm1 : (P.pol.map v.embedding).Monic` using `(minpoly.monic hFint).map _`. Establish `hn1 : (P.pol.map v.embedding).natDegree = G.n`. Rewrite using `[Polynomial.natDegree_map]`.

Conclude with `hdeg`. Establish `e1` using `Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm hm1 (minpoly.dvd _ _ hpol) (by rw [hn1]; exact hqdeg)`. Establish `e2` using `Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm (Matrix.charpoly_monic _) (Matrix.minpoly_dvd_charpoly _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hqdeg)`. Rewrite using `[e2, e1]`.
-/
theorem charpoly_psi_eq_map_pol (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F) :
    (G.psi v (P.γ : G.C)).charpoly = P.pol.map v.embedding := by
  letI : Algebra G.F ℂ := v.embedding.toAlgebra
  have hg : ∀ a, G.psi v (algebraMap G.F G.C a) = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) ℂ) a :=
    fun a => by rw [G.psi_F, Matrix.algebraMap_eq_diagonal]; rfl
  let g : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ := { G.psi v with commutes' := hg }
  let L : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) g (fun r _ => Algebra.commute_algebraMap_left r _)
  haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
  have hinj : Function.Injective L :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right (not_subsingleton _)
  have hL : ∀ x : G.C, L ((1 : ℂ) ⊗ₜ x) = G.psi v x := fun x => by
    show (Algebra.TensorProduct.lift _ g _) ((1 : ℂ) ⊗ₜ x) = _
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
    rfl
  set γ : G.C := (P.γ : G.C) with hγ
  have hdeg : (minpoly G.F γ).natDegree = G.n := P.reg.1
  have hli : LinearIndependent G.F (fun i : Fin G.n => γ ^ (i : ℕ)) := by
    have := linearIndependent_pow (K := G.F) γ
    rw [hdeg] at this
    exact this
  have hT : LinearIndependent ℂ (fun i : Fin G.n => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ))) :=
    Module.Flat.linearIndependent_one_tmul hli
  have hM : LinearIndependent ℂ (fun i : Fin G.n => (G.psi v γ) ^ (i : ℕ)) := by
    have := hT.map' L.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
    have e : (fun i : Fin G.n => (G.psi v γ) ^ (i : ℕ)) =
        L.toLinearMap ∘ (fun i : Fin G.n => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ))) := by
      funext i
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply]
      rw [hL, map_pow]
    rw [e]
    exact this
  have hint : IsIntegral ℂ (G.psi v γ) := Algebra.IsIntegral.isIntegral _
  set q := minpoly ℂ (G.psi v γ) with hq
  have hqm : q.Monic := minpoly.monic hint
  have hqdeg : G.n ≤ q.natDegree := by
    by_contra hlt
    push_neg at hlt
    have h0 : aeval (G.psi v γ) q = 0 := minpoly.aeval _ _
    rw [Polynomial.aeval_eq_sum_range' hlt, Finset.sum_range] at h0
    have h1 := Fintype.linearIndependent_iff.1 hM (fun i => q.coeff i) h0 ⟨q.natDegree, hlt⟩
    have h2 : q.coeff q.natDegree = 1 := hqm.coeff_natDegree
    rw [h2] at h1
    exact one_ne_zero h1
  have hpol : aeval (G.psi v γ) (P.pol.map v.embedding) = 0 := by
    have h : aeval (g γ) (minpoly G.F γ) = 0 := by rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    change aeval (G.psi v γ) ((minpoly G.F γ).map (algebraMap G.F ℂ)) = 0
    rw [Polynomial.aeval_map_algebraMap]
    exact h
  have hFint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hm1 : (P.pol.map v.embedding).Monic := (minpoly.monic hFint).map _
  have hn1 : (P.pol.map v.embedding).natDegree = G.n := by
    rw [Polynomial.natDegree_map]; exact hdeg
  have e1 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm hm1 (minpoly.dvd _ _ hpol)
    (by rw [hn1]; exact hqdeg)
  have e2 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm (Matrix.charpoly_monic _)
    (Matrix.minpoly_dvd_charpoly _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hqdeg)
  rw [e2, e1]

/- English proof (translation)
Introduce `p _ G P v`. Use `set Q := P.pol.map v.embedding with hQ`. Take `⟨hcard, hmon⟩` from `GlobalTheory.LKMid.Pair.card_roots_map_pol p G P v.embedding`. Establish `hsep : Q.Separable` using `P.reg.2.map`. Establish `hnd : Q.roots.Nodup` using `Polynomial.nodup_roots hsep`.

Establish `hQm : Q.Monic` using `hmon.map _`. Establish `hne : P.pol ≠ 0` using `hmon.ne_zero`. Set `e : Fin G.n ≃ {x // x ∈ Q.roots.toFinset}` to `(Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hcard)).symm`. Set `lam : Fin G.n → ℂ` to `fun i => (e i : ℂ)`. Establish `hlam : Function.Injective lam` using `fun i j h => e.injective (Subtype.ext h)`.

Establish `hprod : Q = ∏ k, (X - C (lam k))`. Establish `h1 : Q = (Q.roots.map (fun a => X - C a)).prod` using `(Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQm (IsAlgClosed.card_roots_eq_natDegree)).symm`. Rewrite using `[h1]`. Establish `h2 : (Q.roots.map (fun a => X - C a)).prod = ∏ a ∈ Q.roots.toFinset, (X - C a)`. Rewrite using `[Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd]`.

Rewrite using `[h2, ← Finset.prod_coe_sort]`. Conclude with `(Fintype.prod_equiv e _ _ (fun _ => rfl)).symm`. Establish `hcp : (G.psi v (P.γ : G.C)).charpoly = ∏ k, (X - C (lam k))`. Rewrite using `[charpoly_psi_eq_map_pol, ← hQ, ← hprod]`. Take `⟨Z, hZ⟩` from `GlobalTheory.matrix_diagonalizable_of_charpoly_eq_prod_distinct ℂ G.n _ lam hlam hcp`.

Use `⟨Z, lam, hlam, fun z => ?_, hZ⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.mem_roots_map_of_injective v.embedding.injective hne, ← hQ, ← Multiset.mem_toFinset]`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Conclude with `⟨e.symm ⟨z, hz⟩, by simp [lam]⟩`.

Introduce and unpack `⟨i, rfl⟩`. Conclude with `(e i).2`.
-/
theorem psi_eigenbasis : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F),
    ∃ (Z : GL (Fin G.n) ℂ) (lam : Fin G.n → ℂ), Function.Injective lam ∧
      (∀ z : ℂ, P.pol.eval₂ v.embedding z = 0 ↔ ∃ i, lam i = z) ∧
      G.psi v (P.γ : G.C) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal lam := by
  intro p _ G P v
  set Q := P.pol.map v.embedding with hQ
  obtain ⟨hcard, hmon⟩ := GlobalTheory.LKMid.Pair.card_roots_map_pol p G P v.embedding
  have hsep : Q.Separable := P.reg.2.map
  have hnd : Q.roots.Nodup := Polynomial.nodup_roots hsep
  have hQm : Q.Monic := hmon.map _
  have hne : P.pol ≠ 0 := hmon.ne_zero
  let e : Fin G.n ≃ {x // x ∈ Q.roots.toFinset} :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hcard)).symm
  let lam : Fin G.n → ℂ := fun i => (e i : ℂ)
  have hlam : Function.Injective lam := fun i j h => e.injective (Subtype.ext h)
  have hprod : Q = ∏ k, (X - C (lam k)) := by
    have h1 : Q = (Q.roots.map (fun a => X - C a)).prod :=
      (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQm
        (IsAlgClosed.card_roots_eq_natDegree)).symm
    rw [h1]
    have h2 : (Q.roots.map (fun a => X - C a)).prod = ∏ a ∈ Q.roots.toFinset, (X - C a) := by
      rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd]
    rw [h2, ← Finset.prod_coe_sort]
    exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
  have hcp : (G.psi v (P.γ : G.C)).charpoly = ∏ k, (X - C (lam k)) := by
    rw [charpoly_psi_eq_map_pol, ← hQ, ← hprod]
  obtain ⟨Z, hZ⟩ := GlobalTheory.matrix_diagonalizable_of_charpoly_eq_prod_distinct ℂ G.n _ lam hlam hcp
  refine ⟨Z, lam, hlam, fun z => ?_, hZ⟩
  rw [← Polynomial.mem_roots_map_of_injective v.embedding.injective hne, ← hQ, ← Multiset.mem_toFinset]
  constructor
  · intro hz
    exact ⟨e.symm ⟨z, hz⟩, by simp [lam]⟩
  · rintro ⟨i, rfl⟩
    exact (e i).2

end GlobalTheory.LKMid
