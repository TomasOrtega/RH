import Mathlib
open NumberField

namespace PositivityTheory.Xgn.FreeNakayamaDescent
open TensorProduct Module

/- English proof (translation)
Use `haveI : Module.Free S (S ⊗[A] M) := Module.Free.of_basis b`. Use `haveI : Module.Flat A M := Module.Flat.of_flat_tensorProduct A M S`. Establish `hrk : ∀ p : PrimeSpectrum A, rankAtStalk M p = r`. Introduce `p`. Take `⟨q, rfl⟩` from `PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := S) p`.

Use `haveI : Nontrivial S := q.nontrivial`. Rewrite using `[← rankAtStalk_baseChange, rankAtStalk_eq_finrank_of_free]`. Simplify using `[finrank_eq_card_basis b]`. Apply `nonempty_basis_of_flat_of_finrank_eq A M r` to reduce the goal to its premises. Introduce `P`.

Use `haveI := P.2`. Use `letI := Ideal.Quotient.field P.1`. Establish `h` using `rankAtStalk_baseChange (R := A) (M := M) (S := A ⧸ P.1) ⟨⊥, Ideal.isPrime_bot⟩`. Rewrite `h` using `[hrk, rankAtStalk_eq_finrank_of_free]`. Simplify using `using h`.
-/
theorem descent (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [Module.FaithfullyFlat A S]
    [Finite (MaximalSpectrum A)] [AddCommGroup M] [Module A M] [Module.Finite A M] (r : ℕ)
    (b : Basis (Fin r) S (S ⊗[A] M)) : Nonempty (Basis (Fin r) A M) := by
  haveI : Module.Free S (S ⊗[A] M) := Module.Free.of_basis b
  haveI : Module.Flat A M := Module.Flat.of_flat_tensorProduct A M S
  have hrk : ∀ p : PrimeSpectrum A, rankAtStalk M p = r := by
    intro p
    obtain ⟨q, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := S) p
    haveI : Nontrivial S := q.nontrivial
    rw [← rankAtStalk_baseChange, rankAtStalk_eq_finrank_of_free]
    simp [finrank_eq_card_basis b]
  apply nonempty_basis_of_flat_of_finrank_eq A M r
  intro P
  haveI := P.2
  letI := Ideal.Quotient.field P.1
  have h := rankAtStalk_baseChange (R := A) (M := M) (S := A ⧸ P.1) ⟨⊥, Ideal.isPrime_bot⟩
  rw [hrk, rankAtStalk_eq_finrank_of_free] at h
  simpa using h

/- English proof (translation)
Use `⟨Basis.mk (v := y) ?_ ?_⟩` and prove the remaining obligations. Rewrite `hli`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `g hg j`. Use `hli (fun q => c.repr (g q.1) q.2) (by` as an intermediate fact. Rewrite using `[Fintype.sum_prod_type, ← hg]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `conv_rhs => rw [← c.sum_repr (g j), Finset.sum_smul]`. Simplify using `only [smul_assoc])`. Apply `c.repr.injective` to reduce the goal to its premises. Use extensionality with `i`.

Simplify using `using this (j, i)`. Introduce `t _`. Establish `ht : t ∈ Submodule.span k (Set.range fun q : Fin r × ι => c q.2 • y q.1)`. Rewrite using `[hsp]`. Discharge the goal by the elementary cases of `trivial`.

Establish `hle : Submodule.span k (Set.range fun q : Fin r × ι => c q.2 • y q.1) ≤ (Submodule.span S (Set.range y)).restrictScalars k`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨q, rfl⟩`. Conclude with `Submodule.smul_mem (Submodule.span S (Set.range y)) (c q.2) (Submodule.subset_span (Set.mem_range_self q.1))`. Conclude with `hle ht`.
-/
theorem basis_of_tower (k S T ι : Type) [Field k] [CommRing S] [Algebra k S] [AddCommGroup T]
    [Module k T] [Module S T] [IsScalarTower k S T] [Fintype ι] (c : Basis ι k S) (r : ℕ)
    (y : Fin r → T) (hli : LinearIndependent k (fun q : Fin r × ι => c q.2 • y q.1))
    (hsp : Submodule.span k (Set.range fun q : Fin r × ι => c q.2 • y q.1) = ⊤) :
    Nonempty (Basis (Fin r) S T) := by
  refine ⟨Basis.mk (v := y) ?_ ?_⟩
  · rw [Fintype.linearIndependent_iff] at hli ⊢
    intro g hg j
    have := hli (fun q => c.repr (g q.1) q.2) (by
      rw [Fintype.sum_prod_type, ← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      conv_rhs => rw [← c.sum_repr (g j), Finset.sum_smul]
      simp only [smul_assoc])
    apply c.repr.injective
    ext i
    simpa using this (j, i)
  · intro t _
    have ht : t ∈ Submodule.span k (Set.range fun q : Fin r × ι => c q.2 • y q.1) := by
      rw [hsp]; trivial
    have hle : Submodule.span k (Set.range fun q : Fin r × ι => c q.2 • y q.1) ≤
        (Submodule.span S (Set.range y)).restrictScalars k := by
      rw [Submodule.span_le]
      rintro _ ⟨q, rfl⟩
      exact Submodule.smul_mem (Submodule.span S (Set.range y)) (c q.2)
        (Submodule.subset_span (Set.mem_range_self q.1))
    exact hle ht

/- English proof (translation)
Use `haveI : Module.Finite F A := Module.Finite.of_basis b`. Use `haveI : IsArtinianRing A := IsArtinianRing.of_finite F A`. Use `haveI : Module.Finite A M := Module.Finite.of_restrictScalars_finite F A M`. Establish `ibc : IsBaseChange k (IsScalarTower.toAlgHom F A S).toLinearMap` using `Algebra.IsPushout.out`. Set `c : Basis ι k S` to `ibc.basis b`.

Establish `hc : ∀ i, c i = algebraMap A S (b i)` using `fun i => ibc.basis_apply b i`. Set `g : S ⊗[A] M ≃ₗ[k] N` to `(Algebra.IsPushout.cancelBaseChange F k A S M).trans e`. Establish `hg : ∀ i (n : N), g.symm (act i n) = c i • g.symm n`. Introduce `i n`. Take `⟨t, rfl⟩` from `e.surjective n`.

Proceed by induction on `t with`. Consider the case `zero => simp`. Consider the case `add u v hu hv => simp only [map_add, hu, hv, smul_add]`. Consider the case `tmul s m`. Establish `h1 : (s ⊗ₜ[F] m : k ⊗[F] M) = s • (1 ⊗ₜ[F] m)` using `by simp [smul_tmul']`.

Rewrite using `[h1, map_smul, map_smul, hact, map_smul, map_smul, smul_comm, hc]`. Use `congr 1`. Simplify using `[g, smul_tmul', ← smul_tmul, Algebra.smul_def]`. Take `⟨bS⟩` from `basis_of_tower k S (S ⊗[A] M) ι c r (fun j => g.symm (x j)) (by`. Use `hli.map' g.symm.toLinearMap g.symm.ker` as an intermediate fact.

Establish `h2 : (fun q : Fin r × ι => c q.2 • g.symm (x q.1)) = g.symm.toLinearMap ∘ (fun q : Fin r × ι => act q.2 (x q.1))`. Use function extensionality and compare the values at `q`. Simplify using `[hg]`. Rewrite using `[h2]`. Conclude with `this)`.

Use the proof step `(by`. Establish `: (fun q : Fin r × ι => c q.2 • g.symm (x q.1)) = g.symm.toLinearMap ∘ (fun q : Fin r × ι => act q.2 (x q.1))`. Use function extensionality and compare the values at `q`. Simplify using `[hg]`. Rewrite using `[this, Set.range_comp, ← Submodule.map_span, hsp, Submodule.map_top]`.

Conclude with `g.symm.range)`. Take `⟨bA⟩` from `descent A S M r bS`. Use `⟨bA, ?_⟩` and prove the remaining obligations. Establish `: (fun q : Fin r × ι => b q.2 • bA q.1) = b.smulTower' bA`. Use function extensionality and compare the values at `q`.

Conclude with `(Basis.smulTower'_apply b bA q).symm`. Rewrite using `[this]`. Conclude with `⟨Basis.linearIndependent _, Basis.span_eq _⟩`.
-/
theorem abstract_descent (F k A S M N ι : Type) [Field F] [Field k] [CommRing A] [CommRing S]
    [Algebra F k] [Algebra F A] [Algebra F S] [Algebra k S] [Algebra A S]
    [IsScalarTower F k S] [IsScalarTower F A S] [Algebra.IsPushout F k A S]
    [Module.FaithfullyFlat A S]
    [AddCommGroup M] [Module F M] [Module A M] [IsScalarTower F A M] [Module.Finite F M]
    [AddCommGroup N] [Module k N] [Fintype ι] (b : Basis ι F A)
    (e : k ⊗[F] M ≃ₗ[k] N) (act : ι → N →ₗ[k] N)
    (hact : ∀ i m, act i (e (1 ⊗ₜ m)) = e (1 ⊗ₜ (b i • m))) (r : ℕ) (x : Fin r → N)
    (hli : LinearIndependent k (fun q : Fin r × ι => act q.2 (x q.1)))
    (hsp : Submodule.span k (Set.range fun q : Fin r × ι => act q.2 (x q.1)) = ⊤) :
    ∃ x0 : Fin r → M, LinearIndependent F (fun q : Fin r × ι => b q.2 • x0 q.1) ∧
      Submodule.span F (Set.range fun q : Fin r × ι => b q.2 • x0 q.1) = ⊤ := by
  haveI : Module.Finite F A := Module.Finite.of_basis b
  haveI : IsArtinianRing A := IsArtinianRing.of_finite F A
  haveI : Module.Finite A M := Module.Finite.of_restrictScalars_finite F A M
  have ibc : IsBaseChange k (IsScalarTower.toAlgHom F A S).toLinearMap := Algebra.IsPushout.out
  let c : Basis ι k S := ibc.basis b
  have hc : ∀ i, c i = algebraMap A S (b i) := fun i => ibc.basis_apply b i
  let g : S ⊗[A] M ≃ₗ[k] N := (Algebra.IsPushout.cancelBaseChange F k A S M).trans e
  have hg : ∀ i (n : N), g.symm (act i n) = c i • g.symm n := by
    intro i n
    obtain ⟨t, rfl⟩ := e.surjective n
    induction t with
    | zero => simp
    | add u v hu hv => simp only [map_add, hu, hv, smul_add]
    | tmul s m =>
      have h1 : (s ⊗ₜ[F] m : k ⊗[F] M) = s • (1 ⊗ₜ[F] m) := by simp [smul_tmul']
      rw [h1, map_smul, map_smul, hact, map_smul, map_smul, smul_comm, hc]
      congr 1
      simp [g, smul_tmul', ← smul_tmul, Algebra.smul_def]
  obtain ⟨bS⟩ := basis_of_tower k S (S ⊗[A] M) ι c r (fun j => g.symm (x j))
    (by
      have := hli.map' g.symm.toLinearMap g.symm.ker
      have h2 : (fun q : Fin r × ι => c q.2 • g.symm (x q.1)) =
          g.symm.toLinearMap ∘ (fun q : Fin r × ι => act q.2 (x q.1)) := by
        funext q
        simp [hg]
      rw [h2]
      exact this)
    (by
      have : (fun q : Fin r × ι => c q.2 • g.symm (x q.1)) =
          g.symm.toLinearMap ∘ (fun q : Fin r × ι => act q.2 (x q.1)) := by
        funext q
        simp [hg]
      rw [this, Set.range_comp, ← Submodule.map_span, hsp, Submodule.map_top]
      exact g.symm.range)
  obtain ⟨bA⟩ := descent A S M r bS
  refine ⟨bA, ?_⟩
  have : (fun q : Fin r × ι => b q.2 • bA q.1) = b.smulTower' bA := by
    funext q
    exact (Basis.smulTower'_apply b bA q).symm
  rw [this]
  exact ⟨Basis.linearIndependent _, Basis.span_eq _⟩

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/- English proof (translation)
Use `letI : Module A (n → F) := Module.compHom (n → F) φ.toRingHom`. Establish `hs : ∀ (a : A) (m : n → F), a • m = (φ a).mulVec m` using `fun _ _ => rfl`. Use `haveI : IsScalarTower F A (n → F) := ⟨fun c a m => by`. Rewrite using `[hs, hs, map_smul, Matrix.smul_mulVec]⟩`. Use `haveI : Algebra.IsPushout F k A (A ⊗[F] k) := Algebra.IsPushout.symm inferInstance`.

Conclude with `abstract_descent F k A (A ⊗[F] k) (n → F) (n → k) ι b (TensorProduct.piScalarRight F k k n) (fun i => ((φ (b i)).map (algebraMap F k)).mulVecLin) (by`. Introduce `i m`. Use function extensionality and compare the values at `a`. Simplify using `[hs, Matrix.mulVec, dotProduct, Algebra.smul_def]) r x hli hsp`.
-/
theorem matrix_descent (F k A n ι : Type) [Field F] [Field k] [CommRing A]
    [Algebra F k] [Algebra F A] [Fintype n] [DecidableEq n] [Fintype ι] (b : Basis ι F A)
    (φ : A →ₐ[F] Matrix n n F) (r : ℕ) (x : Fin r → n → k)
    (hli : LinearIndependent k
      (fun q : Fin r × ι => ((φ (b q.2)).map (algebraMap F k)).mulVec (x q.1)))
    (hsp : Submodule.span k (Set.range fun q : Fin r × ι =>
      ((φ (b q.2)).map (algebraMap F k)).mulVec (x q.1)) = ⊤) :
    ∃ x0 : Fin r → n → F, LinearIndependent F (fun q : Fin r × ι => (φ (b q.2)).mulVec (x0 q.1)) ∧
      Submodule.span F (Set.range fun q : Fin r × ι => (φ (b q.2)).mulVec (x0 q.1)) = ⊤ := by
  letI : Module A (n → F) := Module.compHom (n → F) φ.toRingHom
  have hs : ∀ (a : A) (m : n → F), a • m = (φ a).mulVec m := fun _ _ => rfl
  haveI : IsScalarTower F A (n → F) := ⟨fun c a m => by
    rw [hs, hs, map_smul, Matrix.smul_mulVec]⟩
  haveI : Algebra.IsPushout F k A (A ⊗[F] k) := Algebra.IsPushout.symm inferInstance
  exact abstract_descent F k A (A ⊗[F] k) (n → F) (n → k) ι b
    (TensorProduct.piScalarRight F k k n)
    (fun i => ((φ (b i)).map (algebraMap F k)).mulVecLin)
    (by
      intro i m
      funext a
      simp [hs, Matrix.mulVec, dotProduct, Algebra.smul_def]) r x hli hsp

/- English proof (translation)
Set `φ : F ⊗[ℤ] O →ₐ[F] Matrix n n F` to `Algebra.TensorProduct.lift (Algebra.ofId F _) ρ.toIntAlgHom (fun c y => Algebra.commute_algebraMap_left c _)`. Set `b` to `Algebra.TensorProduct.basis F β`. Establish `hb : ∀ i, φ (b i) = ρ (β i)`. Introduce `i`. Simplify using `only [φ, b, Algebra.TensorProduct.basis_apply]`.

Use `(Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[map_one, one_mul]`. Both sides reduce to the same expression. Use `matrix_descent F k _ n _ b φ r x (by simpa only [hb] using hli) (by simpa only [hb] using hsp)` as an intermediate fact. Simplify `this` using `only [hb]`.
-/
theorem int_descent (F k O n ι : Type) [Field F] [Field k] [CommRing O]
    [Algebra F k] [Fintype n] [DecidableEq n] [Fintype ι] (β : Basis ι ℤ O)
    (ρ : O →+* Matrix n n F) (r : ℕ) (x : Fin r → n → k)
    (hli : LinearIndependent k
      (fun q : Fin r × ι => ((ρ (β q.2)).map (algebraMap F k)).mulVec (x q.1)))
    (hsp : Submodule.span k (Set.range fun q : Fin r × ι =>
      ((ρ (β q.2)).map (algebraMap F k)).mulVec (x q.1)) = ⊤) :
    ∃ x0 : Fin r → n → F, LinearIndependent F (fun q : Fin r × ι => (ρ (β q.2)).mulVec (x0 q.1)) ∧
      Submodule.span F (Set.range fun q : Fin r × ι => (ρ (β q.2)).mulVec (x0 q.1)) = ⊤ := by
  let φ : F ⊗[ℤ] O →ₐ[F] Matrix n n F :=
    Algebra.TensorProduct.lift (Algebra.ofId F _) ρ.toIntAlgHom
      (fun c y => Algebra.commute_algebraMap_left c _)
  let b := Algebra.TensorProduct.basis F β
  have hb : ∀ i, φ (b i) = ρ (β i) := by
    intro i
    simp only [φ, b, Algebra.TensorProduct.basis_apply]
    refine (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_
    rw [map_one, one_mul]
    rfl
  have := matrix_descent F k _ n _ b φ r x
    (by simpa only [hb] using hli) (by simpa only [hb] using hsp)
  simpa only [hb] using this

/- English proof (translation)
Set `b0` to `Basis.mk hli hsp.ge`. Set `σ : n ≃ κ` to `(Pi.basisFun (IsLocalRing.ResidueField R) n).indexEquiv b0`. Establish `h0` using `((Pi.basisFun (IsLocalRing.ResidueField R) n).reindex σ).is_basis_iff_det.1 ⟨hli, hsp⟩`. Rewrite using `[((Pi.basisFun R n).reindex σ).is_basis_iff_det]`. Rewrite `h0`, the goal using `[Basis.det_apply]`.

Rewrite using `[← isUnit_map_iff (IsLocalRing.residue R), RingHom.map_det]`. Use `h0 using 2` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using `[Basis.toMatrix_apply]`.
-/
theorem lift_basis (R n κ : Type) [CommRing R] [IsLocalRing R] [Fintype n] [DecidableEq n]
    [Fintype κ] (v : κ → n → R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun q => fun a => IsLocalRing.residue R (v q a)))
    (hsp : Submodule.span (IsLocalRing.ResidueField R)
      (Set.range fun q => fun a => IsLocalRing.residue R (v q a)) = ⊤) :
    LinearIndependent R v ∧ Submodule.span R (Set.range v) = ⊤ := by
  classical
  let b0 := Basis.mk hli hsp.ge
  let σ : n ≃ κ := (Pi.basisFun (IsLocalRing.ResidueField R) n).indexEquiv b0
  have h0 := ((Pi.basisFun (IsLocalRing.ResidueField R) n).reindex σ).is_basis_iff_det.1 ⟨hli, hsp⟩
  rw [((Pi.basisFun R n).reindex σ).is_basis_iff_det]
  rw [Basis.det_apply] at h0 ⊢
  rw [← isUnit_map_iff (IsLocalRing.residue R), RingHom.map_det]
  convert h0 using 2
  ext i j
  simp [Basis.toMatrix_apply]

end PositivityTheory.Xgn.FreeNakayamaDescent

/- English proof (translation)
Introduce `E _ _ R k _ _ _ f _ n _ _ r ρ ⟨x, hli, hsp⟩`. Use `letI : Algebra (IsLocalRing.ResidueField R) k := (IsLocalRing.ResidueField.lift f).toAlgebra`. Set `ρ0 : 𝓞 E →+* Matrix n n (IsLocalRing.ResidueField R)` to `(IsLocalRing.residue R).mapMatrix.comp ρ`. Establish `hb : ∀ a, ρ0 a = (ρ a).map (IsLocalRing.residue R)` using `fun _ => rfl`. Establish `hb' : ∀ a, (ρ0 a).map (algebraMap (IsLocalRing.ResidueField R) k) = (ρ a).map f`.

Introduce `i`. Rewrite using `[hb, Matrix.map_map]`. Both sides reduce to the same expression. Take `⟨x0, h1, h2⟩` from `PositivityTheory.Xgn.FreeNakayamaDescent.int_descent (IsLocalRing.ResidueField R) k _ n _ (RingOfIntegers.basis E) ρ0 r x (by simpa only [hb'] using hli) (by simpa only [hb'] using hsp)`. Use `choose y hy using fun j a => IsLocalRing.residue_surjective (R := R) (x0 j a)`.

Use `⟨y, ?_⟩` and prove the remaining obligations. Establish `key : (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => fun a => IsLocalRing.residue R ((ρ (RingOfIntegers.basis E q.2)).mulVec (y q.1) a)) = fun q => (ρ0 (RingOfIntegers.basis E q.2)).mulVec (x0 q.1)`. Use function extensionality and compare the values at `q a`. Rewrite using `[hb, RingHom.map_mulVec]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Conclude with `hy _ _`. Apply `PositivityTheory.Xgn.FreeNakayamaDescent.lift_basis` to reduce the goal to its premises. Rewrite using `[key]`. Conclude with `h1`.

Rewrite using `[key]`. Conclude with `h2`.
-/
theorem PositivityTheory.Xgn.free_module_nakayama_descent : ∀ (E : Type) [Field E] [NumberField E] (R k : Type) [CommRing R] [IsLocalRing R] [Field k] (f : R →+* k) [IsLocalHom f] (n : Type) [Fintype n] [DecidableEq n] (r : ℕ) (ρ : 𝓞 E →+* Matrix n n R), (∃ x : Fin r → n → k, LinearIndependent k (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ((ρ (RingOfIntegers.basis E q.2)).map f).mulVec (x q.1)) ∧ Submodule.span k (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ((ρ (RingOfIntegers.basis E q.2)).map f).mulVec (x q.1)) = ⊤) → ∃ x : Fin r → n → R, LinearIndependent R (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => (ρ (RingOfIntegers.basis E q.2)).mulVec (x q.1)) ∧ Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => (ρ (RingOfIntegers.basis E q.2)).mulVec (x q.1)) = ⊤ := by
  intro E _ _ R k _ _ _ f _ n _ _ r ρ ⟨x, hli, hsp⟩
  letI : Algebra (IsLocalRing.ResidueField R) k := (IsLocalRing.ResidueField.lift f).toAlgebra
  let ρ0 : 𝓞 E →+* Matrix n n (IsLocalRing.ResidueField R) :=
    (IsLocalRing.residue R).mapMatrix.comp ρ
  have hb : ∀ a, ρ0 a = (ρ a).map (IsLocalRing.residue R) := fun _ => rfl
  have hb' : ∀ a, (ρ0 a).map (algebraMap (IsLocalRing.ResidueField R) k) = (ρ a).map f := by
    intro i
    rw [hb, Matrix.map_map]
    rfl
  obtain ⟨x0, h1, h2⟩ := PositivityTheory.Xgn.FreeNakayamaDescent.int_descent
    (IsLocalRing.ResidueField R) k _ n _ (RingOfIntegers.basis E) ρ0 r x
    (by simpa only [hb'] using hli) (by simpa only [hb'] using hsp)
  choose y hy using fun j a => IsLocalRing.residue_surjective (R := R) (x0 j a)
  refine ⟨y, ?_⟩
  have key : (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => fun a =>
      IsLocalRing.residue R ((ρ (RingOfIntegers.basis E q.2)).mulVec (y q.1) a)) =
      fun q => (ρ0 (RingOfIntegers.basis E q.2)).mulVec (x0 q.1) := by
    funext q a
    rw [hb, RingHom.map_mulVec]
    congr 1
    funext a
    exact hy _ _
  apply PositivityTheory.Xgn.FreeNakayamaDescent.lift_basis
  · rw [key]; exact h1
  · rw [key]; exact h2
