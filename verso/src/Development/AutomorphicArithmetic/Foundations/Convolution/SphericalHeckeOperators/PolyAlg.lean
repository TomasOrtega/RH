import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.H

/- English proof (translation)
Establish `h : (evalAt z).comp (polyEmb n) = MvPolynomial.aeval (fun j : Fin n => (z j : ℂ))`. Use `MvPolynomial.algHom_ext fun i => ?_` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply, polyEmb_X, evalAt_single, MvPolynomial.aeval_X, one_mul, monomialChar_apply, Finset.prod_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`.

Simplify using `[Pi.single_eq_of_ne hj]`. Simplify using the standard rewrite rules. Conclude with `AlgHom.congr_fun h Q`.
-/
private theorem evalAt_polynomialEmbed {n : ℕ} (z : Fin n → ℂˣ) (Q : MvPolynomial (Fin n) ℂ) :
    evalAt z (polyEmb n Q) = MvPolynomial.aeval (fun j : Fin n => (z j : ℂ)) Q := by
  have h : (evalAt z).comp (polyEmb n) = MvPolynomial.aeval (fun j : Fin n => (z j : ℂ)) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, polyEmb_X, evalAt_single, MvPolynomial.aeval_X, one_mul,
      monomialChar_apply, Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  exact AlgHom.congr_fun h Q

/- English proof (translation)
Establish `h : (bc l).comp (polyEmb n) = (polyEmb n).comp (MvPolynomial.expand l)`. Use `MvPolynomial.algHom_ext fun i => ?_` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.expand_X, map_pow, polyEmb_X, AddMonoidAlgebra.single_pow, one_pow]`. Simplify using `[bc, AddMonoidAlgebra.mapDomainAlgHom, AddMonoidAlgebra.mapDomain_single]`. Conclude with `AlgHom.congr_fun h Q`.
-/
private theorem baseChange_polynomialEmbed {n : ℕ} (l : ℕ) (Q : MvPolynomial (Fin n) ℂ) :
    bc l (polyEmb n Q) = polyEmb n (MvPolynomial.expand l Q) := by
  have h : (bc l).comp (polyEmb n) = (polyEmb n).comp (MvPolynomial.expand l) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.expand_X, map_pow, polyEmb_X,
      AddMonoidAlgebra.single_pow, one_pow]
    simp [bc, AddMonoidAlgebra.mapDomainAlgHom, AddMonoidAlgebra.mapDomain_single]
  exact AlgHom.congr_fun h Q

/- English proof (translation)
Establish `h` using `(MvPolynomial.esymmAlgEquiv (Fin n) ℂ (Fintype.card_fin n)).apply_symm_apply ⟨MvPolynomial.expand l (MvPolynomial.esymm (Fin n) ℂ (i + 1)), fun w => by`. Rewrite using `[MvPolynomial.rename_expand, MvPolynomial.esymm_isSymmetric]⟩`. Establish `h2` using `congrArg Subtype.val h`. Rewrite using `[← MvPolynomial.esymmAlgHom_apply]`. Conclude with `h2`.
-/
private theorem aeval_elemSymm_power {n : ℕ} (l : ℕ) (i : Fin n) :
    MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) (powE l i) =
      MvPolynomial.expand l (MvPolynomial.esymm (Fin n) ℂ (i + 1)) := by
  have h := (MvPolynomial.esymmAlgEquiv (Fin n) ℂ (Fintype.card_fin n)).apply_symm_apply
    ⟨MvPolynomial.expand l (MvPolynomial.esymm (Fin n) ℂ (i + 1)), fun w => by
      rw [MvPolynomial.rename_expand, MvPolynomial.esymm_isSymmetric]⟩
  have h2 := congrArg Subtype.val h
  rw [← MvPolynomial.esymmAlgHom_apply]
  exact h2

/- English proof (translation)
Establish `h : (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1))).comp (MvPolynomial.aeval (powE l)) = (MvPolynomial.expand l).comp (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)))`. Use `MvPolynomial.algHom_ext fun i => ?_` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X, aeval_elemSymm_power]`. Conclude with `AlgHom.congr_fun h γ`.
-/
private theorem aeval_aeval_elemSymm_power {n : ℕ} (l : ℕ) (γ : MvPolynomial (Fin n) ℂ) :
    MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1))
        (MvPolynomial.aeval (powE l) γ) =
      MvPolynomial.expand l
        (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) γ) := by
  have h : (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1))).comp
        (MvPolynomial.aeval (powE l)) =
      (MvPolynomial.expand l).comp
        (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1))) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
      aeval_elemSymm_power]
  exact AlgHom.congr_fun h γ

/- English proof (translation)
Introduce `σ`. Establish `h` using `(MvPolynomial.esymmAlgHom (Fin n) ℂ n γ).2`. Rewrite `h` using `[MvPolynomial.esymmAlgHom_apply, MvPolynomial.mem_symmetricSubalgebra]`. Rewrite using `[← polyEmb_rename, h σ]`.
-/
private theorem polynomialEmbed_symmetric_mem {n : ℕ} (γ : MvPolynomial (Fin n) ℂ) :
    polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) γ) ∈
      symmetricLaurent n := by
  intro σ
  have h := (MvPolynomial.esymmAlgHom (Fin n) ℂ n γ).2
  rw [MvPolynomial.esymmAlgHom_apply, MvPolynomial.mem_symmetricSubalgebra] at h
  rw [← polyEmb_rename, h σ]

/- English proof (translation)
Introduce `n`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `g hg ⟨Q, rfl⟩`. Establish `hQ : Q ∈ MvPolynomial.symmetricSubalgebra (Fin n) ℂ`. Rewrite using `[MvPolynomial.mem_symmetricSubalgebra]`.

Introduce `σ`. Apply `polyEmb_injective` to reduce the goal to its premises. Rewrite using `[polyEmb_rename]`. Conclude with `hg σ`. Take `⟨γ, hγ⟩` from `MvPolynomial.esymmAlgHom_surjective ℂ (σ := Fin n) (n := n) (Fintype.card_fin n).le ⟨Q, hQ⟩`.

Use `⟨γ, ?_⟩` and prove the remaining obligations. Rewrite using `[← MvPolynomial.esymmAlgHom_apply, hγ]`. Both sides reduce to the same expression. Introduce `γ z`. Rewrite using `[evalAt_polynomialEmbed]`.

Establish `h : (MvPolynomial.aeval (fun j : Fin n => (z j : ℂ))).comp (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1))) = MvPolynomial.aeval (fun i : Fin n => (Finset.univ.val.map fun j => (z j : ℂ)).esymm (i + 1))`. Use `MvPolynomial.algHom_ext fun i => ?_` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X, MvPolynomial.aeval_esymm_eq_multiset_esymm]`. Establish `h2` using `AlgHom.congr_fun h γ`. Rewrite `h2` using `[AlgHom.comp_apply]`.

Rewrite using `[h2, MvPolynomial.aeval_eq_eval]`. Introduce `l γ`. Rewrite using `[baseChange_polynomialEmbed, aeval_aeval_elemSymm_power]`. Introduce `D classical`. Set `f : (Fin n → Fin (D + 1)) → LaurentRing n` to `fun c => polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (c i : ℕ)) (1 : ℂ)))`.

Use `⟨Finset.univ.image f, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Take `⟨c, -, rfl⟩` from `Finset.mem_image.1 hy`. Conclude with `polynomialEmbed_symmetric_mem _`. Introduce `p hp`.

Rewrite using `[p.as_sum, map_sum, map_sum]`. Use `Submodule.sum_mem _ fun s hs => ?_` and prove the remaining obligations. Establish `hle : ∀ i, s i < D + 1` using `fun i => by`. Establish `h1 : s.degree ≤ p.totalDegree` using `MvPolynomial.le_totalDegree hs`. Establish `h2 : s i ≤ s.degree`.

Rewrite using `[Finsupp.degree_eq_sum]`. Conclude with `Finset.single_le_sum (f := fun j => s j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)`. Use linear arithmetic over natural numbers and integers. Establish `hm : MvPolynomial.monomial s (MvPolynomial.coeff s p) = MvPolynomial.coeff s p • MvPolynomial.monomial s (1 : ℂ)`. Rewrite using `[MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`.

Rewrite using `[hm, map_smul, map_smul]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Use `Finset.mem_coe.2 (Finset.mem_image.2 ⟨fun i => ⟨s i, hle i⟩, Finset.mem_univ _, ?_⟩)` and prove the remaining obligations. Establish `hs' : (Finsupp.equivFunOnFinite.symm fun i => s i) = s`. Use extensionality with `i`.

Both sides reduce to the same expression. Simplify using `only [f, hs']`.
-/
theorem UpperTheory.ConvolutionTheory.H.polyAlg :
    ∀ n : ℕ,
      (∀ g ∈ symmetricLaurent n, g ∈ (polyEmb n).range → ∃ γ : MvPolynomial (Fin n) ℂ, polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) γ) = g) ∧
      (∀ (γ : MvPolynomial (Fin n) ℂ) (z : Fin n → ℂˣ), evalAt z (polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) γ)) =
        MvPolynomial.eval (fun i : Fin n => (Finset.univ.val.map fun j => (z j : ℂ)).esymm (i + 1)) γ) ∧
      (∀ (l : ℕ) (γ : MvPolynomial (Fin n) ℂ), bc l (polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) γ)) = polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) (MvPolynomial.aeval (powE l) γ))) ∧
      ∀ D : ℕ, ∃ P : Finset (LaurentRing n), (∀ y ∈ P, y ∈ symmetricLaurent n) ∧
        ∀ p : MvPolynomial (Fin n) ℂ, p.totalDegree ≤ D → polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) p) ∈ Submodule.span ℂ (P : Set (LaurentRing n)) := by
  intro n
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro g hg ⟨Q, rfl⟩
    have hQ : Q ∈ MvPolynomial.symmetricSubalgebra (Fin n) ℂ := by
      rw [MvPolynomial.mem_symmetricSubalgebra]
      intro σ
      apply polyEmb_injective
      rw [polyEmb_rename]
      exact hg σ
    obtain ⟨γ, hγ⟩ := MvPolynomial.esymmAlgHom_surjective ℂ (σ := Fin n) (n := n)
      (Fintype.card_fin n).le ⟨Q, hQ⟩
    refine ⟨γ, ?_⟩
    rw [← MvPolynomial.esymmAlgHom_apply, hγ]
    rfl
  · intro γ z
    rw [evalAt_polynomialEmbed]
    have h : (MvPolynomial.aeval (fun j : Fin n => (z j : ℂ))).comp
          (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1))) =
        MvPolynomial.aeval (fun i : Fin n => (Finset.univ.val.map fun j => (z j : ℂ)).esymm (i + 1)) := by
      refine MvPolynomial.algHom_ext fun i => ?_
      rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
        MvPolynomial.aeval_esymm_eq_multiset_esymm]
    have h2 := AlgHom.congr_fun h γ
    rw [AlgHom.comp_apply] at h2
    rw [h2, MvPolynomial.aeval_eq_eval]
  · intro l γ
    rw [baseChange_polynomialEmbed, aeval_aeval_elemSymm_power]
  · intro D
    classical
    let f : (Fin n → Fin (D + 1)) → LaurentRing n := fun c =>
      polyEmb n (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1))
        (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i => (c i : ℕ)) (1 : ℂ)))
    refine ⟨Finset.univ.image f, ?_, ?_⟩
    · intro y hy
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hy
      exact polynomialEmbed_symmetric_mem _
    · intro p hp
      rw [p.as_sum, map_sum, map_sum]
      refine Submodule.sum_mem _ fun s hs => ?_
      have hle : ∀ i, s i < D + 1 := fun i => by
        have h1 : s.degree ≤ p.totalDegree := MvPolynomial.le_totalDegree hs
        have h2 : s i ≤ s.degree := by
          rw [Finsupp.degree_eq_sum]
          exact Finset.single_le_sum (f := fun j => s j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      have hm : MvPolynomial.monomial s (MvPolynomial.coeff s p) =
          MvPolynomial.coeff s p • MvPolynomial.monomial s (1 : ℂ) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [hm, map_smul, map_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨fun i => ⟨s i, hle i⟩, Finset.mem_univ _, ?_⟩)
      have hs' : (Finsupp.equivFunOnFinite.symm fun i => s i) = s := by
        ext i
        rfl
      simp only [f, hs']
