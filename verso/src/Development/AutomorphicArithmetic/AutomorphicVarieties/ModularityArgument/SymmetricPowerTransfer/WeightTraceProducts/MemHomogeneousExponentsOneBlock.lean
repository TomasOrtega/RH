import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.CoeffScale
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.FinMH

noncomputable section

open MvPolynomial

namespace UpperTheory.V.Z.Sym.Wt

/- English proof (translation)
Establish `mem : ∀ c : S → ℂ, (∑ m : S, monomial (m : σ →₀ ℕ) (c m)) ∈ V`. Introduce `c`. Rewrite using `[hV]`. Introduce `m hm`. Take `⟨i, -, hi⟩` from `Finset.mem_biUnion.1 (MvPolynomial.support_sum hm)`.

Establish `h` using `MvPolynomial.support_monomial_subset hi`. Rewrite `h` using `[Finset.mem_singleton]`. Rewrite using `[h]`. Conclude with `i.2`. Set `e : V ≃ₗ[ℂ] (S → ℂ)` to `{ toFun := fun P m => coeff (m : σ →₀ ℕ) P.1 map_add' := fun P Q => by`.

Use extensionality with `m`. Simplify using the standard rewrite rules. Use the proof step `map_smul' := fun a P => by`. Use extensionality with `m`. Simplify using the standard rewrite rules.

Use `invFun := fun c => ⟨∑ m : S, monomial (m : σ →₀ ℕ) (c m), mem c⟩`. Use `left_inv := fun P => by`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only`. Use `conv_rhs => rw [P.1.as_sum]`.

Rewrite using `[Finset.sum_coe_sort S (fun m => monomial m (coeff m P.1))]`. Use `symm`. Use `Finset.sum_subset (fun m hm => (hV P.1).1 P.2 m hm) ?_` and prove the remaining obligations. Introduce `m _ hm`. Rewrite using `[MvPolynomial.notMem_support_iff.1 hm, map_zero]`.

Use `right_inv := fun c => by`. Use extensionality with `m`. Simplify using `[coeff_sum, coeff_monomial] }`. Set `b` to `Module.Basis.ofEquivFun e`. Rewrite using `[LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace, ← Finset.sum_coe_sort S]`.

Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.diag_apply, LinearMap.toMatrix_apply, Module.Basis.ofEquivFun_repr_apply]`. Use `show coeff (m : σ →₀ ℕ) (F (b m)).1 = _`. Rewrite using `[hF]`. Establish `hb : (b m).1 = monomial (m : σ →₀ ℕ) 1`.

Rewrite using `[Module.Basis.coe_ofEquivFun]`. Use `show ∑ i : S, monomial (i : σ →₀ ℕ) (Pi.single m 1 i) = _`. Rewrite using `[Finset.sum_eq_single m]`. Simplify using the standard rewrite rules. Introduce `i _ hi`.

Simplify using `[Pi.single_eq_of_ne hi]`. Simplify using the standard rewrite rules. Rewrite using `[hb]`.
-/
theorem trace_eq_sum_coeff {σ : Type} (V : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ V]
    (S : Finset (σ →₀ ℕ)) (hV : ∀ P, P ∈ V ↔ ∀ m ∈ P.support, m ∈ S)
    (f : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) (F : Module.End ℂ V) (hF : ∀ P, (F P).1 = f P.1) :
    LinearMap.trace ℂ V F = ∑ m ∈ S, coeff m (f (monomial m 1)) := by
  classical
  have mem : ∀ c : S → ℂ, (∑ m : S, monomial (m : σ →₀ ℕ) (c m)) ∈ V := by
    intro c
    rw [hV]
    intro m hm
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hm)
    have h := MvPolynomial.support_monomial_subset hi
    rw [Finset.mem_singleton] at h
    rw [h]
    exact i.2
  let e : V ≃ₗ[ℂ] (S → ℂ) :=
    { toFun := fun P m => coeff (m : σ →₀ ℕ) P.1
      map_add' := fun P Q => by
        ext m
        simp
      map_smul' := fun a P => by
        ext m
        simp
      invFun := fun c => ⟨∑ m : S, monomial (m : σ →₀ ℕ) (c m), mem c⟩
      left_inv := fun P => by
        apply Subtype.ext
        dsimp only
        conv_rhs => rw [P.1.as_sum]
        rw [Finset.sum_coe_sort S (fun m => monomial m (coeff m P.1))]
        symm
        refine Finset.sum_subset (fun m hm => (hV P.1).1 P.2 m hm) ?_
        intro m _ hm
        rw [MvPolynomial.notMem_support_iff.1 hm, map_zero]
      right_inv := fun c => by
        ext m
        simp [coeff_sum, coeff_monomial] }
  let b := Module.Basis.ofEquivFun e
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Module.Basis.ofEquivFun_repr_apply]
  show coeff (m : σ →₀ ℕ) (F (b m)).1 = _
  rw [hF]
  have hb : (b m).1 = monomial (m : σ →₀ ℕ) 1 := by
    rw [Module.Basis.coe_ofEquivFun]
    show ∑ i : S, monomial (i : σ →₀ ℕ) (Pi.single m 1 i) = _
    rw [Finset.sum_eq_single m]
    · simp
    · intro i _ hi
      simp [Pi.single_eq_of_ne hi]
    · simp
  rw [hb]

variable {K : Type} [Fintype K] {d : ℕ}

def glue (μ : K → (Unit × Fin d →₀ ℕ)) : K × Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => μ p.1 ((), p.2)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem glue_apply (μ : K → (Unit × Fin d →₀ ℕ)) (k : K) (i : Fin d) : glue μ (k, i) = μ k ((), i) := rfl

/- English proof (translation)
Introduce `μ ν h`. Use function extensionality and compare the values at `k`. Use extensionality with `⟨⟨⟩, i⟩`. Establish `h'` using `congrArg (fun m => m (k, i)) h`. Simplify `h'` using `[glue_apply]`.
-/
theorem glue_injective : Function.Injective (glue : (K → (Unit × Fin d →₀ ℕ)) → _) := by
  intro μ ν h
  funext k
  ext ⟨⟨⟩, i⟩
  have h' := congrArg (fun m => m (k, i)) h
  simpa [glue_apply] using h'

def inB (k : K) (p : Unit × Fin d) : K × Fin d := (k, p.2)

/- English proof (translation)
Use extensionality with `⟨k, i⟩`. Rewrite using `[glue_apply, Finsupp.finset_sum_apply, Finset.sum_eq_single k]`. Establish `hinj : Function.Injective (inB (d` using `d) k) := by`. Introduce and unpack `⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h`. Simplify using `only [inB, Prod.mk.injEq] at h`.

Rewrite using `[h.2]`. Conclude with `(Finsupp.mapDomain_apply hinj (ν k) ((), i)).symm`. Introduce `k' _ hk`. Apply `Finsupp.mapDomain_notin_range` to reduce the goal to its premises. Introduce and unpack `⟨p, hp⟩`.

Simplify using `only [inB, Prod.mk.injEq] at hp`. Conclude with `hk hp.1`. Introduce `h`. Conclude with `absurd (Finset.mem_univ k) h`.
-/
private theorem glue_eq_sum_mapDomain_inB (ν : K → (Unit × Fin d →₀ ℕ)) :
    glue ν = ∑ k, (ν k).mapDomain (inB k) := by
  ext ⟨k, i⟩
  rw [glue_apply, Finsupp.finset_sum_apply, Finset.sum_eq_single k]
  · have hinj : Function.Injective (inB (d := d) k) := by
      rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
      simp only [inB, Prod.mk.injEq] at h
      rw [h.2]
    exact (Finsupp.mapDomain_apply hinj (ν k) ((), i)).symm
  · intro k' _ hk
    apply Finsupp.mapDomain_notin_range
    rintro ⟨p, hp⟩
    simp only [inB, Prod.mk.injEq] at hp
    exact hk hp.1
  · intro h
    exact absurd (Finset.mem_univ k) h

/- English proof (translation)
Repeatedly rewrite using `[rename_monomial]`. Rewrite using `[← monomial_sum_prod, glue_eq_sum_mapDomain_inB]`.
-/
theorem prod_rename_monomial (ν : K → (Unit × Fin d →₀ ℕ)) (c : K → ℂ) :
    ∏ k, rename (inB k) (monomial (ν k) (c k)) = monomial (glue ν) (∏ k, c k) := by
  simp_rw [rename_monomial]
  rw [← monomial_sum_prod, glue_eq_sum_mapDomain_inB]

/- English proof (translation)
Establish `hP : ∀ k, rename (inB k) (P k) = ∑ m ∈ (P k).support, rename (inB k) (monomial m (coeff m (P k)))`. Introduce `k`. Use `conv_lhs => rw [(P k).as_sum]`. Rewrite using `[map_sum]`. Repeatedly rewrite using `[hP]`.

Rewrite using `[Finset.prod_univ_sum]`. Repeatedly rewrite using `[prod_rename_monomial]`. Rewrite using `[coeff_sum]`. Repeatedly rewrite using `[coeff_monomial, glue_injective.eq_iff]`. Rewrite using `[Finset.sum_ite_eq']`.

Use `split_ifs with h`. Both sides reduce to the same expression. Rewrite `h` using `[Fintype.mem_piFinset] at h push_neg`. Take `⟨k, hk⟩` from `h`. Use `symm`.

Apply `Finset.prod_eq_zero (Finset.mem_univ k)` to reduce the goal to its premises. Conclude with `MvPolynomial.notMem_support_iff.1 hk`.
-/
theorem coeff_glue_prod (μ : K → (Unit × Fin d →₀ ℕ)) (P : K → MvPolynomial (Unit × Fin d) ℂ) :
    coeff (glue μ) (∏ k, rename (inB k) (P k)) = ∏ k, coeff (μ k) (P k) := by
  classical
  have hP : ∀ k, rename (inB k) (P k) =
      ∑ m ∈ (P k).support, rename (inB k) (monomial m (coeff m (P k))) := by
    intro k
    conv_lhs => rw [(P k).as_sum]
    rw [map_sum]
  simp_rw [hP]
  rw [Finset.prod_univ_sum]
  simp_rw [prod_rename_monomial]
  rw [coeff_sum]
  simp_rw [coeff_monomial, glue_injective.eq_iff]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Fintype.mem_piFinset] at h
    push_neg at h
    obtain ⟨k, hk⟩ := h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    exact MvPolynomial.notMem_support_iff.1 hk

omit [Fintype K] in
/- English proof (translation)
Establish `h : (sbs g).comp (rename (inB k)) = (rename (inB k)).comp (sbs fun _ : Unit => g k)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨⟨⟩, i⟩`. Simplify using `[sbs, inB, map_sum]`. Conclude with `congrArg (fun φ => φ P) h`.
-/
theorem sbs_rename (g : K → GL (Fin d) ℂ) (k : K) (P : MvPolynomial (Unit × Fin d) ℂ) :
    sbs g (rename (inB k) P) = rename (inB k) (sbs (fun _ : Unit => g k) P) := by
  have h : (sbs g).comp (rename (inB k)) =
      (rename (inB k)).comp (sbs fun _ : Unit => g k) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨⟨⟩, i⟩
    simp [sbs, inB, map_sum]
  exact congrArg (fun φ => φ P) h

/- English proof (translation)
Establish `h : monomial (glue ν) (1 : ℂ) = ∏ k, rename (inB k) (monomial (ν k) 1)`. Rewrite using `[prod_rename_monomial]`. Simplify using the standard rewrite rules. Rewrite using `[h, map_prod]`. Repeatedly rewrite using `[sbs_rename]`.

Conclude with `coeff_glue_prod _ _`.
-/
theorem coeff_sbs_glue (g : K → GL (Fin d) ℂ) (μ ν : K → (Unit × Fin d →₀ ℕ)) :
    coeff (glue μ) (sbs g (monomial (glue ν) 1)) =
      ∏ k, coeff (μ k) (sbs (fun _ : Unit => g k) (monomial (ν k) 1)) := by
  have h : monomial (glue ν) (1 : ℂ) = ∏ k, rename (inB k) (monomial (ν k) 1) := by
    rw [prod_rename_monomial]
    simp
  rw [h, map_prod]
  simp_rw [sbs_rename]
  exact coeff_glue_prod _ _

def deg1 (d n : ℕ) : Finset (Unit × Fin d →₀ ℕ) := Finset.finsuppAntidiag Finset.univ n

/- English proof (translation)
Simplify using `[deg1, Finset.mem_finsuppAntidiag, Fintype.sum_prod_type]`.
-/
theorem mem_homogeneousExponentsOneBlock {n : ℕ} {m : Unit × Fin d →₀ ℕ} : m ∈ deg1 d n ↔ ∑ i, m ((), i) = n := by
  simp [deg1, Finset.mem_finsuppAntidiag, Fintype.sum_prod_type]

/- English proof (translation)
Use `haveI := finMH Unit d (fun _ : Unit => n)`. Use `trace_eq_sum_coeff _ _ (fun P => ?_) f F hF` and prove the remaining obligations. Use `(memMH Unit d (fun _ => n) P).trans ?_` and prove the remaining obligations. Simplify using `only [mem_homogeneousExponentsOneBlock]`. Prove the components needed by the constructor for the conclusion.

Introduce `h m hm`. Conclude with `h m hm ()`. Introduce and unpack `h m hm ⟨⟩`. Conclude with `h m hm`.
-/
theorem trace_one_block (n : ℕ) (f : MvPolynomial (Unit × Fin d) ℂ →ₗ[ℂ] MvPolynomial (Unit × Fin d) ℂ)
    (F : Module.End ℂ (MH d fun _ : Unit => n)) (hF : ∀ P, (F P).1 = f P.1) :
    LinearMap.trace ℂ _ F = ∑ m ∈ deg1 d n, coeff m (f (monomial m 1)) := by
  haveI := finMH Unit d (fun _ : Unit => n)
  refine trace_eq_sum_coeff _ _ (fun P => ?_) f F hF
  refine (memMH Unit d (fun _ => n) P).trans ?_
  simp only [mem_homogeneousExponentsOneBlock]
  constructor
  · intro h m hm
    exact h m hm ()
  · rintro h m hm ⟨⟩
    exact h m hm

/- English proof (translation)
The claim follows from `trace_one_block n (sbs fun _ : Unit => g).toLinearMap _ fun _ => rfl`.
-/
theorem symPowTrace_eq_sum_coeff (n : ℕ) (g : GL (Fin d) ℂ) :
    tr1 d n g = ∑ m ∈ deg1 d n, coeff m (sbs (fun _ : Unit => g) (monomial m 1)) :=
  trace_one_block n (sbs fun _ : Unit => g).toLinearMap _ fun _ => rfl

/- English proof (translation)
Use `haveI := finMH K d n`. Establish `hV : ∀ P, P ∈ MH d n ↔ ∀ m ∈ P.support, m ∈ (Fintype.piFinset fun k => deg1 d (n k)).image glue`. Introduce `P`. Use `(memMH K d n P).trans ?_` and prove the remaining obligations. Use `forall₂_congr fun m _ => ?_` and prove the remaining obligations.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `Finset.mem_image.2 ⟨fun k => Finsupp.equivFunOnFinite.symm fun p => m (k, p.2), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.mem_piFinset]`. Introduce `k`.

Rewrite using `[mem_homogeneousExponentsOneBlock]`. Simplify using `using h k`. Use extensionality with `⟨k, i⟩`. Simplify using `[glue_apply]`. Introduce `hm k`.

Take `⟨μ, hμ, rfl⟩` from `Finset.mem_image.1 hm`. Rewrite `hμ` using `[Fintype.mem_piFinset]`. Simplify using `only [glue_apply]`. Conclude with `mem_homogeneousExponentsOneBlock.1 (hμ k)`. Rewrite using `[trace_eq_sum_coeff (MH d n) _ hV f F hF, Finset.sum_image (fun x _ y _ h => glue_injective h)]`.
-/
theorem trace_blocks [DecidableEq K] (n : K → ℕ)
    (f : MvPolynomial (K × Fin d) ℂ →ₗ[ℂ] MvPolynomial (K × Fin d) ℂ)
    (F : Module.End ℂ (MH d n)) (hF : ∀ P, (F P).1 = f P.1) :
    LinearMap.trace ℂ _ F = ∑ μ ∈ Fintype.piFinset (fun k => deg1 d (n k)),
      coeff (glue μ) (f (monomial (glue μ) 1)) := by
  classical
  haveI := finMH K d n
  have hV : ∀ P, P ∈ MH d n ↔ ∀ m ∈ P.support,
      m ∈ (Fintype.piFinset fun k => deg1 d (n k)).image glue := by
    intro P
    refine (memMH K d n P).trans ?_
    refine forall₂_congr fun m _ => ?_
    constructor
    · intro h
      refine Finset.mem_image.2 ⟨fun k => Finsupp.equivFunOnFinite.symm fun p => m (k, p.2), ?_, ?_⟩
      · rw [Fintype.mem_piFinset]
        intro k
        rw [mem_homogeneousExponentsOneBlock]
        simpa using h k
      · ext ⟨k, i⟩
        simp [glue_apply]
    · intro hm k
      obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.1 hm
      rw [Fintype.mem_piFinset] at hμ
      simp only [glue_apply]
      exact mem_homogeneousExponentsOneBlock.1 (hμ k)
  rw [trace_eq_sum_coeff (MH d n) _ hV f F hF,
    Finset.sum_image (fun x _ y _ h => glue_injective h)]

end UpperTheory.V.Z.Sym.Wt

end
