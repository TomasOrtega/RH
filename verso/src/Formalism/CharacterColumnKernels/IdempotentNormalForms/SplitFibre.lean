import Formalism.CharacterColumnKernels.StatOntoLattice

open Polynomial

noncomputable section

namespace Formalism.NG

universe u

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `T _ P hP hdeg`. Establish `hP1 : P = 1` using `hP.natDegree_eq_zero.mp hdeg`. Use `⟨T, inferInstance, Algebra.id T, Fin.elim0, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Break down `subsingleton_or_nontrivial T with h | h` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[Module.finrank_self]`. Both sides reduce to the same expression. Simplify using `[hP1]`.

Rewrite using `[eq_top_iff]`. Introduce `t _`. Conclude with `Subalgebra.algebraMap_mem _ t`. Introduce `B _ _ a _`. Conclude with `⟨Algebra.ofId T B, fun i => i.elim0⟩`.

Consider the case `succ n ih`. Introduce `T _ P hP hdeg`. Establish `hnt : Nontrivial T`. Break down `subsingleton_or_nontrivial T with h | h` into its components or cases. It suffices to derive a contradiction.

Establish `h0 : P = 0` using `Subsingleton.elim _ _`. Rewrite `hdeg` using `[h0, natDegree_zero]`. Use linear arithmetic over natural numbers and integers. Conclude with `h`. Set `r : AdjoinRoot P` to `AdjoinRoot.root P`.

Set `pb` to `AdjoinRoot.powerBasis' hP`. Establish `hfree1 : Module.Free T (AdjoinRoot P)` using `Module.Free.of_basis pb.basis`. Establish `hfin1 : Module.Finite T (AdjoinRoot P)` using `Module.Finite.of_basis pb.basis`. Establish `hrank1 : Module.finrank T (AdjoinRoot P) = n + 1`. Rewrite using `[Module.finrank_eq_card_basis pb.basis, Fintype.card_fin]`.

Simplify using `[pb, hdeg]`. Establish `hroot : (P.map (algebraMap T (AdjoinRoot P))).IsRoot r`. Rewrite using `[AdjoinRoot.algebraMap_eq]`. Conclude with `AdjoinRoot.isRoot_root P`. Take `⟨Q, hQ⟩ : ∃ Q, Q = P.map (algebraMap T (AdjoinRoot P)) /ₘ (X - C r)` from `⟨_, rfl⟩`.

Establish `hfac1 : (X - C r) * Q = P.map (algebraMap T (AdjoinRoot P))`. Rewrite using `[hQ]`. Conclude with `mul_divByMonic_eq_iff_isRoot.mpr hroot`. Establish `hPm : (P.map (algebraMap T (AdjoinRoot P))).Monic` using `hP.map _`. Establish `hQm : Q.Monic` using `(monic_X_sub_C r).of_mul_monic_left (hfac1 ▸ hPm)`.

Establish `: Nontrivial (AdjoinRoot P)` using `Module.nontrivial_of_finrank_pos (by rw [hrank1]; omega)`. Establish `hQdeg : Q.natDegree = n`. Establish `h1` using `(monic_X_sub_C r).natDegree_mul hQm`. Rewrite `h1` using `[hfac1, hP.natDegree_map, hdeg, natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers.

Take `⟨T₂, i₂, a₂, rr₂, hfree2, hfin2, hrank2, hfac2, hadj2, huniv2⟩` from `ih (AdjoinRoot P) Q hQm hQdeg`. Set `_ : Algebra T T₂` to `((algebraMap (AdjoinRoot P) T₂).comp (algebraMap T (AdjoinRoot P))).toAlgebra`. Establish `: IsScalarTower T (AdjoinRoot P) T₂` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Set `rr : Fin (n + 1) → T₂` to `Fin.cons (algebraMap (AdjoinRoot P) T₂ r) rr₂`. Use `⟨T₂, i₂, inferInstance, rr, Module.Free.trans (R := T) (S := AdjoinRoot P) (M := T₂), Module.Finite.trans (AdjoinRoot P) T₂, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Module.finrank_mul_finrank T (AdjoinRoot P) T₂, hrank1, hrank2, Nat.factorial_succ]`. Establish `hmap : P.map (algebraMap T T₂) = (P.map (algebraMap T (AdjoinRoot P))).map (algebraMap (AdjoinRoot P) T₂)`. Rewrite using `[Polynomial.map_map, ← IsScalarTower.algebraMap_eq]`. Rewrite using `[hmap, ← hfac1, Polynomial.map_mul, hfac2, Fin.prod_univ_succ]`. Simplify using `[rr]`.

Establish `hsub : ∀ t : AdjoinRoot P, algebraMap (AdjoinRoot P) T₂ t ∈ Algebra.adjoin T (Set.range rr)`. Introduce `t`. Establish `ht : t ∈ Algebra.adjoin T ({r} : Set (AdjoinRoot P))`. Rewrite using `[AdjoinRoot.adjoinRoot_eq_top]`. Discharge the goal by the elementary cases of `trivial`.

Establish `hm : (IsScalarTower.toAlgHom T (AdjoinRoot P) T₂) t ∈ (Algebra.adjoin T ({r} : Set (AdjoinRoot P))).map (IsScalarTower.toAlgHom T (AdjoinRoot P) T₂)` using `Subalgebra.mem_map.mpr ⟨t, ht, rfl⟩`. Rewrite `hm` using `[AlgHom.map_adjoin, Set.image_singleton]`. Conclude with `Algebra.adjoin_mono (by rintro _ rfl; exact ⟨0, rfl⟩) hm`. Rewrite using `[eq_top_iff]`. Introduce and unpack `z -`.

Establish `hz : z ∈ Algebra.adjoin (AdjoinRoot P) (Set.range rr₂)`. Rewrite using `[hadj2]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem y hy`.

Take `⟨i, rfl⟩` from `hy`. Conclude with `Algebra.subset_adjoin ⟨i.succ, by simp [rr]⟩`. Consider the case `algebraMap t => exact hsub t`. Consider the case `add y w _ _ hy hw => exact add_mem hy hw`. Consider the case `mul y w _ _ hy hw => exact mul_mem hy hw`.

Introduce `B _ _ a ha`. Establish `hroot0 : P.eval₂ (Algebra.ofId T B : T →+* B) (a 0) = 0` using `by show P.eval₂ (algebraMap T B) (a 0) = 0`. Rewrite using `[← Polynomial.eval_map, ha, Polynomial.eval_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ 0) (by simp)`. Set `ψ : AdjoinRoot P →ₐ[T] B` to `AdjoinRoot.liftAlgHom P (Algebra.ofId T B) (a 0) hroot0`.

Set `_ : Algebra (AdjoinRoot P) B` to `ψ.toRingHom.toAlgebra`. Establish `: IsScalarTower T (AdjoinRoot P) B` using `IsScalarTower.of_algebraMap_eq fun t => (ψ.commutes t).symm`. Establish `hψr : algebraMap (AdjoinRoot P) B r = a 0` using `AdjoinRoot.liftAlgHom_root _ _ _ _`. Establish `hQB : Q.map (algebraMap (AdjoinRoot P) B) = ∏ i : Fin n, (X - C (a i.succ))`. Establish `h1 : P.map (algebraMap T B) = (X - C (a 0)) * Q.map (algebraMap (AdjoinRoot P) B)`.

Rewrite using `[IsScalarTower.algebraMap_eq T (AdjoinRoot P) B, ← Polynomial.map_map, ← hfac1, Polynomial.map_mul]`. Simplify using `[hψr]`. Rewrite `h1` using `[ha, Fin.prod_univ_succ]`. Establish `h3` using `sub_eq_zero.mpr h1`. Rewrite `h3` using `[← mul_sub, (monic_X_sub_C (a 0)).mul_right_eq_zero_iff, sub_eq_zero]`.

Conclude with `h3.symm`. Take `⟨φ₂, hφ₂⟩` from `huniv2 B (fun i => a i.succ) hQB`. Use `⟨φ₂.restrictScalars T, fun i => ?_⟩` and prove the remaining obligations. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `only [rr, Fin.cons_zero, AlgHom.restrictScalars_apply]`.

Rewrite using `[AlgHom.commutes, hψr]`. Simplify using `only [rr, Fin.cons_succ, AlgHom.restrictScalars_apply]`. Conclude with `hφ₂ j`.
-/
private theorem exists_universal_splitting_algebra (n : ℕ) : ∀ (T : Type u) [CommRing T] (P : T[X]), P.Monic → P.natDegree = n →
    ∃ (T' : Type u) (_ : CommRing T') (_ : Algebra T T') (rr : Fin n → T'),
      Module.Free T T' ∧ Module.Finite T T' ∧ Module.finrank T T' = n.factorial ∧
      P.map (algebraMap T T') = ∏ i, (X - C (rr i)) ∧
      Algebra.adjoin T (Set.range rr) = ⊤ ∧
      ∀ (B : Type*) [CommRing B] [Algebra T B] (a : Fin n → B),
        P.map (algebraMap T B) = ∏ i, (X - C (a i)) →
        ∃ φ : T' →ₐ[T] B, ∀ i, φ (rr i) = a i := by
  induction n with
  | zero =>
    intro T _ P hP hdeg
    have hP1 : P = 1 := hP.natDegree_eq_zero.mp hdeg
    refine ⟨T, inferInstance, Algebra.id T, Fin.elim0, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
    · rcases subsingleton_or_nontrivial T with h | h
      · simp
      · rw [Module.finrank_self]
        rfl
    · simp [hP1]
    · rw [eq_top_iff]
      intro t _
      exact Subalgebra.algebraMap_mem _ t
    · intro B _ _ a _
      exact ⟨Algebra.ofId T B, fun i => i.elim0⟩
  | succ n ih =>
    intro T _ P hP hdeg
    have hnt : Nontrivial T := by
      rcases subsingleton_or_nontrivial T with h | h
      · exfalso
        have h0 : P = 0 := Subsingleton.elim _ _
        rw [h0, natDegree_zero] at hdeg
        omega
      · exact h
    let r : AdjoinRoot P := AdjoinRoot.root P
    let pb := AdjoinRoot.powerBasis' hP
    have hfree1 : Module.Free T (AdjoinRoot P) := Module.Free.of_basis pb.basis
    have hfin1 : Module.Finite T (AdjoinRoot P) := Module.Finite.of_basis pb.basis
    have hrank1 : Module.finrank T (AdjoinRoot P) = n + 1 := by
      rw [Module.finrank_eq_card_basis pb.basis, Fintype.card_fin]
      simp [pb, hdeg]
    have hroot : (P.map (algebraMap T (AdjoinRoot P))).IsRoot r := by
      rw [AdjoinRoot.algebraMap_eq]
      exact AdjoinRoot.isRoot_root P
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = P.map (algebraMap T (AdjoinRoot P)) /ₘ (X - C r) := ⟨_, rfl⟩
    have hfac1 : (X - C r) * Q = P.map (algebraMap T (AdjoinRoot P)) := by
      rw [hQ]
      exact mul_divByMonic_eq_iff_isRoot.mpr hroot
    have hPm : (P.map (algebraMap T (AdjoinRoot P))).Monic := hP.map _
    have hQm : Q.Monic := (monic_X_sub_C r).of_mul_monic_left (hfac1 ▸ hPm)
    have : Nontrivial (AdjoinRoot P) := Module.nontrivial_of_finrank_pos (by rw [hrank1]; omega)
    have hQdeg : Q.natDegree = n := by
      have h1 := (monic_X_sub_C r).natDegree_mul hQm
      rw [hfac1, hP.natDegree_map, hdeg, natDegree_X_sub_C] at h1
      omega
    obtain ⟨T₂, i₂, a₂, rr₂, hfree2, hfin2, hrank2, hfac2, hadj2, huniv2⟩ := ih (AdjoinRoot P) Q hQm hQdeg
    let _ : Algebra T T₂ := ((algebraMap (AdjoinRoot P) T₂).comp (algebraMap T (AdjoinRoot P))).toAlgebra
    have : IsScalarTower T (AdjoinRoot P) T₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let rr : Fin (n + 1) → T₂ := Fin.cons (algebraMap (AdjoinRoot P) T₂ r) rr₂
    refine ⟨T₂, i₂, inferInstance, rr, Module.Free.trans (R := T) (S := AdjoinRoot P) (M := T₂),
      Module.Finite.trans (AdjoinRoot P) T₂,
      ?_, ?_, ?_, ?_⟩
    · rw [← Module.finrank_mul_finrank T (AdjoinRoot P) T₂, hrank1, hrank2, Nat.factorial_succ]
    · have hmap : P.map (algebraMap T T₂) =
          (P.map (algebraMap T (AdjoinRoot P))).map (algebraMap (AdjoinRoot P) T₂) := by
        rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
      rw [hmap, ← hfac1, Polynomial.map_mul, hfac2, Fin.prod_univ_succ]
      simp [rr]
    · have hsub : ∀ t : AdjoinRoot P,
          algebraMap (AdjoinRoot P) T₂ t ∈ Algebra.adjoin T (Set.range rr) := by
        intro t
        have ht : t ∈ Algebra.adjoin T ({r} : Set (AdjoinRoot P)) := by
          rw [AdjoinRoot.adjoinRoot_eq_top]
          trivial
        have hm : (IsScalarTower.toAlgHom T (AdjoinRoot P) T₂) t ∈
            (Algebra.adjoin T ({r} : Set (AdjoinRoot P))).map
              (IsScalarTower.toAlgHom T (AdjoinRoot P) T₂) := Subalgebra.mem_map.mpr ⟨t, ht, rfl⟩
        rw [AlgHom.map_adjoin, Set.image_singleton] at hm
        exact Algebra.adjoin_mono (by rintro _ rfl; exact ⟨0, rfl⟩) hm
      rw [eq_top_iff]
      rintro z -
      have hz : z ∈ Algebra.adjoin (AdjoinRoot P) (Set.range rr₂) := by
        rw [hadj2]
        trivial
      induction hz using Algebra.adjoin_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact Algebra.subset_adjoin ⟨i.succ, by simp [rr]⟩
      | algebraMap t => exact hsub t
      | add y w _ _ hy hw => exact add_mem hy hw
      | mul y w _ _ hy hw => exact mul_mem hy hw
    · intro B _ _ a ha
      have hroot0 : P.eval₂ (Algebra.ofId T B : T →+* B) (a 0) = 0 := by
        show P.eval₂ (algebraMap T B) (a 0) = 0
        rw [← Polynomial.eval_map, ha, Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ 0) (by simp)
      let ψ : AdjoinRoot P →ₐ[T] B := AdjoinRoot.liftAlgHom P (Algebra.ofId T B) (a 0) hroot0
      let _ : Algebra (AdjoinRoot P) B := ψ.toRingHom.toAlgebra
      have : IsScalarTower T (AdjoinRoot P) B :=
        IsScalarTower.of_algebraMap_eq fun t => (ψ.commutes t).symm
      have hψr : algebraMap (AdjoinRoot P) B r = a 0 := AdjoinRoot.liftAlgHom_root _ _ _ _
      have hQB : Q.map (algebraMap (AdjoinRoot P) B) = ∏ i : Fin n, (X - C (a i.succ)) := by
        have h1 : P.map (algebraMap T B) = (X - C (a 0)) * Q.map (algebraMap (AdjoinRoot P) B) := by
          rw [IsScalarTower.algebraMap_eq T (AdjoinRoot P) B, ← Polynomial.map_map, ← hfac1,
            Polynomial.map_mul]
          simp [hψr]
        rw [ha, Fin.prod_univ_succ] at h1
        have h3 := sub_eq_zero.mpr h1
        rw [← mul_sub, (monic_X_sub_C (a 0)).mul_right_eq_zero_iff, sub_eq_zero] at h3
        exact h3.symm
      obtain ⟨φ₂, hφ₂⟩ := huniv2 B (fun i => a i.succ) hQB
      refine ⟨φ₂.restrictScalars T, fun i => ?_⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [rr, Fin.cons_zero, AlgHom.restrictScalars_apply]
        rw [AlgHom.commutes, hψr]
      · simp only [rr, Fin.cons_succ, AlgHom.restrictScalars_apply]
        exact hφ₂ j

/- English proof (translation)
Introduce `T _ P hP hdeg`. Take `⟨T', i', a', rr, h1, h2, h3, h4, h5, h6⟩` from `exists_universal_splitting_algebra n T P hP hdeg`. Conclude with `⟨T', i', a', rr, h1, h2, h3, h4, h5, fun B _ _ a ha => h6 B a ha⟩`.
-/
theorem splitAux (n : ℕ) : ∀ (T : Type u) [CommRing T] (P : T[X]), P.Monic → P.natDegree = n →
    ∃ (T' : Type u) (_ : CommRing T') (_ : Algebra T T') (rr : Fin n → T'),
      Module.Free T T' ∧ Module.Finite T T' ∧ Module.finrank T T' = n.factorial ∧
      P.map (algebraMap T T') = ∏ i, (X - C (rr i)) ∧
      Algebra.adjoin T (Set.range rr) = ⊤ ∧
      ∀ (B : Type u) [CommRing B] [Algebra T B] (a : Fin n → B),
        P.map (algebraMap T B) = ∏ i, (X - C (a i)) →
        ∃ φ : T' →ₐ[T] B, ∀ i, φ (rr i) = a i := by
  intro T _ P hP hdeg
  obtain ⟨T', i', a', rr, h1, h2, h3, h4, h5, h6⟩ := exists_universal_splitting_algebra n T P hP hdeg
  exact ⟨T', i', a', rr, h1, h2, h3, h4, h5, fun B _ _ a ha => h6 B a ha⟩

/- English proof (translation)
Unfold `StatSplitAlg`. Introduce `T _ P hP`. Take `⟨T', i', a', rr, h1, h2, h3, h4, h5, h6⟩` from `splitAux P.natDegree T P hP rfl`. Use `⟨T', i', a', rr, h1, h2, h3, h4, h5, fun B _ _ a ha => ?_⟩` and prove the remaining obligations. Take `⟨φ, hφ⟩` from `h6 B a ha`.

Use `⟨φ, hφ, fun ψ hψ => ?_⟩` and prove the remaining obligations. Use `AlgHom.ext_of_adjoin_eq_top h5 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[hψ i, hφ i]`.
-/
theorem splitAlg : StatSplitAlg := by
  unfold StatSplitAlg
  intro T _ P hP
  obtain ⟨T', i', a', rr, h1, h2, h3, h4, h5, h6⟩ := splitAux P.natDegree T P hP rfl
  refine ⟨T', i', a', rr, h1, h2, h3, h4, h5, fun B _ _ a ha => ?_⟩
  obtain ⟨φ, hφ⟩ := h6 B a ha
  refine ⟨φ, hφ, fun ψ hψ => ?_⟩
  refine AlgHom.ext_of_adjoin_eq_top h5 ?_
  rintro _ ⟨i, rfl⟩
  rw [hψ i, hφ i]

open TensorProduct in
/- English proof (translation)
Unfold `StatSplitFibre`. Introduce `T T' K _ _ _ _ P hP rr hrr hadj b x a ha hPa c hc`. Set `_ : Algebra T K` to `x.toAlgebra`. Take `⟨U, iU, aU, u, hUfree, hUfin, hUrank, hUfac, hUadj, hUuniv⟩` from `exists_universal_splitting_algebra P.natDegree T P hP rfl`. Establish `hfacσ : ∀ σ : Equiv.Perm (Fin P.natDegree), P.map (algebraMap T (T' × K)) = ∏ i, (X - C ((rr i, a (σ i)) : T' × K))`.

Introduce `σ`. Establish `hext : ∀ p q : (T' × K)[X], p.map (RingHom.fst T' K) = q.map (RingHom.fst T' K) → p.map (RingHom.snd T' K) = q.map (RingHom.snd T' K) → p = q`. Introduce `p q h1 h2`. Use extensionality with `k`. Simplify using `using congrArg (fun f => Polynomial.coeff f k) h1`.

Simplify using `using congrArg (fun f => Polynomial.coeff f k) h2`. Apply `hext` to reduce the goal to its premises. Rewrite using `[Polynomial.map_map, Polynomial.map_prod]`. Establish `: (RingHom.fst T' K).comp (algebraMap T (T' × K)) = algebraMap T T'` using `by ext; rfl`. Rewrite using `[this, hrr]`.

Simplify using the standard rewrite rules. Rewrite using `[Polynomial.map_map, Polynomial.map_prod]`. Establish `: (RingHom.snd T' K).comp (algebraMap T (T' × K)) = x` using `by ext; rfl`. Rewrite using `[this, hPa]`. Simplify using `only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]`.

Conclude with `(Equiv.prod_comp σ (fun i => X - C (a i))).symm`. Set `Φ : Equiv.Perm (Fin P.natDegree) → (U →ₐ[T] T' × K)` to `fun σ => (hUuniv (T' × K) (fun i => (rr i, a (σ i))) (hfacσ σ)).choose`. Establish `hΦ : ∀ σ i, Φ σ (u i) = (rr i, a (σ i))` using `fun σ => (hUuniv (T' × K) (fun i => (rr i, a (σ i))) (hfacσ σ)).choose_spec`. Set `ψ : U →ₐ[T] T'` to `(AlgHom.fst T T' K).comp (Φ 1)`. Establish `hψ : ∀ i, ψ (u i) = rr i` using `fun i => by simp [ψ, hΦ]`.

Establish `hψσ : ∀ σ, (AlgHom.fst T T' K).comp (Φ σ) = ψ`. Introduce `σ`. Use `AlgHom.ext_of_adjoin_eq_top hUadj ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Simplify using `[ψ, hΦ]`.

Establish `hsurj : Function.Surjective ψ`. Establish `hle : Algebra.adjoin T (Set.range rr) ≤ ψ.range`. Rewrite using `[Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨u i, hψ i⟩`.

Rewrite `hle` using `[hadj]`. Introduce `y`. Take `⟨z, hz⟩` from `hle Algebra.mem_top`. Conclude with `⟨z, hz⟩`. Establish `: Nontrivial T` using `x.domain_nontrivial`.

Establish `hfinT' : Module.Finite T T'` using `Module.Finite.of_basis b`. Establish `: Module.Free T T'` using `Module.Free.of_basis b`. Establish `hbij : Function.Bijective ψ` using `OrzechProperty.bijective_of_surjective_of_finrank_le ψ.toLinearMap hsurj (by rw [hUrank, Module.finrank_eq_card_basis b, Fintype.card_fin])`. Set `ψe : U ≃ₐ[T] T'` to `AlgEquiv.ofBijective ψ hbij`. Establish `hψe : ∀ i, ψe.symm (rr i) = u i`.

Introduce `i`. Rewrite using `[AlgEquiv.symm_apply_eq]`. Conclude with `(hψ i).symm`. Set `χ : Equiv.Perm (Fin P.natDegree) → (U →ₐ[T] K)` to `fun σ => (AlgHom.snd T T' K).comp (Φ σ)`. Establish `hχ : ∀ σ i, χ σ (u i) = a (σ i)` using `fun σ i => by simp [χ, hΦ]`.

Set `φ : Equiv.Perm (Fin P.natDegree) → (T' →+* K)` to `fun σ => ((χ σ).comp ψe.symm.toAlgHom).toRingHom`. Establish `hφr : ∀ σ i, φ σ (rr i) = a (σ i)`. Introduce `σ i`. Express the relevant statement in the definitionally equal form `χ σ (ψe.symm (rr i)) = _`. Rewrite using `[hψe, hχ]`.

Establish `hcomp : ∀ σ, (φ σ).comp (algebraMap T T') = x`. Introduce `σ`. Use extensionality with `t`. Express the relevant statement in the definitionally equal form `χ σ (ψe.symm (algebraMap T T' t)) = x t`. Rewrite using `[AlgEquiv.commutes, AlgHom.commutes]`.

Both sides reduce to the same expression. Establish `hφinj : Function.Injective fun σ => ((φ σ : T' →+* K) : T' →* K)`. Introduce `σ τ h`. Use extensionality with `i`. Establish `h1 : φ σ (rr i) = φ τ (rr i)` using `DFunLike.congr_fun h (rr i)`.

Rewrite `h1` using `[hφr, hφr]`. Conclude with `congrArg Fin.val (ha h1)`. Establish `hF : LinearIndependent K (fun σ => (φ σ : T' → K))` using `(linearIndependent_monoidHom T' K).comp _ hφinj`. Establish `hexp : ∀ σ t, φ σ t = ∑ k, x (b.repr t k) * φ σ (b k)`. Introduce `σ t`.

Use `conv_lhs => rw [← b.sum_repr t]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul]`. Use `congr 1`.

Conclude with `RingHom.congr_fun (hcomp σ) _`. Establish `hcard : Fintype.card (Equiv.Perm (Fin P.natDegree)) = Fintype.card (Fin P.natDegree.factorial)`. Rewrite using `[Fintype.card_perm, Fintype.card_fin, Fintype.card_fin]`. Set `e₀ : Equiv.Perm (Fin P.natDegree) ≃ Fin P.natDegree.factorial` to `Fintype.equivOfCardEq hcard`. Set `M : Matrix (Fin P.natDegree.factorial) (Fin P.natDegree.factorial) K` to `fun p k => φ (e₀.symm p) (b k)`.

Establish `hdetM : M.det ≠ 0`. Introduce `hdet`. Establish `hdetT : M.transpose.det = 0` using `by rw [Matrix.det_transpose]; exact hdet`. Take `⟨d, hd0, hd⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdetT`. Establish `hk : ∀ k, ∑ σ, d (e₀ σ) * φ σ (b k) = 0`.

Introduce `k`. Establish `h1 : ∑ p, φ (e₀.symm p) (b k) * d p = 0` using `congrFun hd k`. Rewrite using `[← h1]`. Conclude with `Fintype.sum_equiv e₀ _ _ fun σ => by simp [mul_comm]`. Establish `hsum : ∑ σ ∈ Finset.univ, d (e₀ σ) • (fun σ => (φ σ : T' → K)) σ = 0`.

Use function extensionality and compare the values at `t`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[hexp σ t]`.

Use `_ = ∑ k, x (b.repr t k) * ∑ σ, d (e₀ σ) * φ σ (b k) := by`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Use `_ = 0 := by simp [hk]`. Establish `h0` using `linearIndependent_iff'.mp hF Finset.univ (fun σ => d (e₀ σ)) hsum`. Apply `hd0` to reduce the goal to its premises. Use function extensionality and compare the values at `p`. Use `h0 (e₀.symm p) (Finset.mem_univ _)` as an intermediate fact.

Simplify using `using this`. Assume the negation of the conclusion as `hc0`. Apply `hdetM` to reduce the goal to its premises. Use `Matrix.exists_mulVec_eq_zero_iff.mp ⟨c, hc0, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`.

Simplify using `only [Matrix.mulVec, dotProduct, Pi.zero_apply, M]`. Use `hc (φ (e₀.symm p)) (hcomp _)` as an intermediate fact. Simplify `this` using `[mul_comm]`.
-/
theorem splitFibre : StatSplitFibre := by
  unfold StatSplitFibre
  intro T T' K _ _ _ _ P hP rr hrr hadj b x a ha hPa c hc
  classical
  let _ : Algebra T K := x.toAlgebra
  obtain ⟨U, iU, aU, u, hUfree, hUfin, hUrank, hUfac, hUadj, hUuniv⟩ :=
    exists_universal_splitting_algebra P.natDegree T P hP rfl
  have hfacσ : ∀ σ : Equiv.Perm (Fin P.natDegree),
      P.map (algebraMap T (T' × K)) = ∏ i, (X - C ((rr i, a (σ i)) : T' × K)) := by
    intro σ
    have hext : ∀ p q : (T' × K)[X], p.map (RingHom.fst T' K) = q.map (RingHom.fst T' K) →
        p.map (RingHom.snd T' K) = q.map (RingHom.snd T' K) → p = q := by
      intro p q h1 h2
      ext k
      · simpa using congrArg (fun f => Polynomial.coeff f k) h1
      · simpa using congrArg (fun f => Polynomial.coeff f k) h2
    apply hext
    · rw [Polynomial.map_map, Polynomial.map_prod]
      have : (RingHom.fst T' K).comp (algebraMap T (T' × K)) = algebraMap T T' := by ext; rfl
      rw [this, hrr]
      simp
    · rw [Polynomial.map_map, Polynomial.map_prod]
      have : (RingHom.snd T' K).comp (algebraMap T (T' × K)) = x := by ext; rfl
      rw [this, hPa]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      exact (Equiv.prod_comp σ (fun i => X - C (a i))).symm
  let Φ : Equiv.Perm (Fin P.natDegree) → (U →ₐ[T] T' × K) := fun σ =>
    (hUuniv (T' × K) (fun i => (rr i, a (σ i))) (hfacσ σ)).choose
  have hΦ : ∀ σ i, Φ σ (u i) = (rr i, a (σ i)) := fun σ =>
    (hUuniv (T' × K) (fun i => (rr i, a (σ i))) (hfacσ σ)).choose_spec
  let ψ : U →ₐ[T] T' := (AlgHom.fst T T' K).comp (Φ 1)
  have hψ : ∀ i, ψ (u i) = rr i := fun i => by simp [ψ, hΦ]
  have hψσ : ∀ σ, (AlgHom.fst T T' K).comp (Φ σ) = ψ := by
    intro σ
    refine AlgHom.ext_of_adjoin_eq_top hUadj ?_
    rintro _ ⟨i, rfl⟩
    simp [ψ, hΦ]
  have hsurj : Function.Surjective ψ := by
    have hle : Algebra.adjoin T (Set.range rr) ≤ ψ.range := by
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact ⟨u i, hψ i⟩
    rw [hadj] at hle
    intro y
    obtain ⟨z, hz⟩ := hle Algebra.mem_top
    exact ⟨z, hz⟩
  have : Nontrivial T := x.domain_nontrivial
  have hfinT' : Module.Finite T T' := Module.Finite.of_basis b
  have : Module.Free T T' := Module.Free.of_basis b
  have hbij : Function.Bijective ψ :=
    OrzechProperty.bijective_of_surjective_of_finrank_le ψ.toLinearMap hsurj
      (by rw [hUrank, Module.finrank_eq_card_basis b, Fintype.card_fin])
  let ψe : U ≃ₐ[T] T' := AlgEquiv.ofBijective ψ hbij
  have hψe : ∀ i, ψe.symm (rr i) = u i := by
    intro i
    rw [AlgEquiv.symm_apply_eq]
    exact (hψ i).symm
  let χ : Equiv.Perm (Fin P.natDegree) → (U →ₐ[T] K) := fun σ => (AlgHom.snd T T' K).comp (Φ σ)
  have hχ : ∀ σ i, χ σ (u i) = a (σ i) := fun σ i => by simp [χ, hΦ]
  let φ : Equiv.Perm (Fin P.natDegree) → (T' →+* K) :=
    fun σ => ((χ σ).comp ψe.symm.toAlgHom).toRingHom
  have hφr : ∀ σ i, φ σ (rr i) = a (σ i) := by
    intro σ i
    change χ σ (ψe.symm (rr i)) = _
    rw [hψe, hχ]
  have hcomp : ∀ σ, (φ σ).comp (algebraMap T T') = x := by
    intro σ
    ext t
    change χ σ (ψe.symm (algebraMap T T' t)) = x t
    rw [AlgEquiv.commutes, AlgHom.commutes]
    rfl
  have hφinj : Function.Injective fun σ => ((φ σ : T' →+* K) : T' →* K) := by
    intro σ τ h
    ext i
    have h1 : φ σ (rr i) = φ τ (rr i) := DFunLike.congr_fun h (rr i)
    rw [hφr, hφr] at h1
    exact congrArg Fin.val (ha h1)
  have hF : LinearIndependent K (fun σ => (φ σ : T' → K)) :=
    (linearIndependent_monoidHom T' K).comp _ hφinj
  have hexp : ∀ σ t, φ σ t = ∑ k, x (b.repr t k) * φ σ (b k) := by
    intro σ t
    conv_lhs => rw [← b.sum_repr t]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul]
    congr 1
    exact RingHom.congr_fun (hcomp σ) _
  have hcard : Fintype.card (Equiv.Perm (Fin P.natDegree)) =
      Fintype.card (Fin P.natDegree.factorial) := by
    rw [Fintype.card_perm, Fintype.card_fin, Fintype.card_fin]
  let e₀ : Equiv.Perm (Fin P.natDegree) ≃ Fin P.natDegree.factorial := Fintype.equivOfCardEq hcard
  let M : Matrix (Fin P.natDegree.factorial) (Fin P.natDegree.factorial) K :=
    fun p k => φ (e₀.symm p) (b k)
  have hdetM : M.det ≠ 0 := by
    intro hdet
    have hdetT : M.transpose.det = 0 := by rw [Matrix.det_transpose]; exact hdet
    obtain ⟨d, hd0, hd⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetT
    have hk : ∀ k, ∑ σ, d (e₀ σ) * φ σ (b k) = 0 := by
      intro k
      have h1 : ∑ p, φ (e₀.symm p) (b k) * d p = 0 := congrFun hd k
      rw [← h1]
      exact Fintype.sum_equiv e₀ _ _ fun σ => by simp [mul_comm]
    have hsum : ∑ σ ∈ Finset.univ, d (e₀ σ) • (fun σ => (φ σ : T' → K)) σ = 0 := by
      funext t
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      calc ∑ σ, d (e₀ σ) * φ σ t = ∑ σ, d (e₀ σ) * ∑ k, x (b.repr t k) * φ σ (b k) := by
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [hexp σ t]
        _ = ∑ k, x (b.repr t k) * ∑ σ, d (e₀ σ) * φ σ (b k) := by
            simp only [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun σ _ => ?_
            ring
        _ = 0 := by simp [hk]
    have h0 := linearIndependent_iff'.mp hF Finset.univ (fun σ => d (e₀ σ)) hsum
    apply hd0
    funext p
    have := h0 (e₀.symm p) (Finset.mem_univ _)
    simpa using this
  by_contra hc0
  apply hdetM
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨c, hc0, ?_⟩
  funext p
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, M]
  have := hc (φ (e₀.symm p)) (hcomp _)
  simpa [mul_comm] using this

end Formalism.NG
