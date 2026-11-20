import Mathlib

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open MvPolynomial

variable {K : Type*} [Field K] {S₁ S₂ : Type*}

/- English proof (translation)
Establish `h` using `AlgHom.congr_fun (sumAlgEquiv_comp_rename_inl K S₁ S₂) a`. Simplify `h` using `[MvPolynomial.algebraMap_eq]`.
-/
theorem sumAlgEquiv_rename_inl (a : MvPolynomial S₁ K) :
    sumAlgEquiv K S₁ S₂ (rename Sum.inl a) = map (C : K →+* MvPolynomial S₂ K) a := by
  have h := AlgHom.congr_fun (sumAlgEquiv_comp_rename_inl K S₁ S₂) a
  simpa [MvPolynomial.algebraMap_eq] using h

/- English proof (translation)
Establish `h` using `AlgHom.congr_fun (sumAlgEquiv_comp_rename_inr K S₁ S₂) b`. Simplify `h` using `[MvPolynomial.algebraMap_eq]`.
-/
theorem sumAlgEquiv_rename_inr_eq_C' (b : MvPolynomial S₂ K) :
    sumAlgEquiv K S₁ S₂ (rename Sum.inr b) = C b := by
  have h := AlgHom.congr_fun (sumAlgEquiv_comp_rename_inr K S₁ S₂) b
  simpa [MvPolynomial.algebraMap_eq] using h

def mvPolynomialCoeffInFirstVariables (m : S₁ →₀ ℕ) : MvPolynomial (S₁ ⊕ S₂) K →ₗ[K] MvPolynomial S₂ K :=
  (lcoeff (MvPolynomial S₂ K) m).restrictScalars K ∘ₗ (sumAlgEquiv K S₁ S₂).toLinearMap

/- English proof (translation)
Simplify using `only [mvPolynomialCoeffInFirstVariables, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, LinearMap.restrictScalars_apply, lcoeff_apply, map_mul, sumAlgEquiv_rename_inl, sumAlgEquiv_rename_inr_eq_C']`. Rewrite using `[mul_comm, coeff_C_mul, coeff_map, smul_eq_C_mul, mul_comm]`.
-/
theorem leftCoeff_rename_mul (m : S₁ →₀ ℕ) (a : MvPolynomial S₁ K) (b : MvPolynomial S₂ K) :
    mvPolynomialCoeffInFirstVariables m (rename Sum.inl a * rename Sum.inr b) = coeff m a • b := by
  simp only [mvPolynomialCoeffInFirstVariables, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, LinearMap.restrictScalars_apply,
    lcoeff_apply, map_mul, sumAlgEquiv_rename_inl, sumAlgEquiv_rename_inr_eq_C']
  rw [mul_comm, coeff_C_mul, coeff_map, smul_eq_C_mul, mul_comm]

/- English proof (translation)
Establish `h` using `(hw.tmul_of_isDomain hv).comp Prod.swap Prod.swap_injective`. Set `e : TensorProduct K (MvPolynomial S₂ K) (MvPolynomial S₁ K) ≃ₗ[K] MvPolynomial (S₁ ⊕ S₂) K` to `((algebraTensorAlgEquiv K (MvPolynomial S₂ K) (σ := S₁)).restrictScalars K).toLinearEquiv.trans (sumAlgEquiv K S₁ S₂).symm.toLinearEquiv`. Establish `he : ∀ p : κ₁ × κ₂, e (TensorProduct.tmul K (w p.2) (v p.1)) = rename Sum.inl (v p.1) * rename Sum.inr (w p.2)`. Introduce `p`. Apply `(sumAlgEquiv K S₁ S₂).injective` to reduce the goal to its premises.

Simplify using `[e, algebraTensorAlgEquiv_tmul, sumAlgEquiv_rename_inl, sumAlgEquiv_rename_inr_eq_C', smul_eq_C_mul, MvPolynomial.algebraMap_eq, mul_comm]`. Establish `h2` using `h.map' e.toLinearMap e.ker`. Simplify `h2` using `only [Function.comp_def, Prod.fst_swap, Prod.snd_swap, LinearEquiv.coe_coe, he]`.
-/
theorem linearIndependent_rename_mul {κ₁ κ₂ : Type*} (v : κ₁ → MvPolynomial S₁ K) (w : κ₂ → MvPolynomial S₂ K)
    (hv : LinearIndependent K v) (hw : LinearIndependent K w) :
    LinearIndependent K fun p : κ₁ × κ₂ => rename Sum.inl (v p.1) * rename Sum.inr (w p.2) := by
  have h := (hw.tmul_of_isDomain hv).comp Prod.swap Prod.swap_injective
  let e : TensorProduct K (MvPolynomial S₂ K) (MvPolynomial S₁ K) ≃ₗ[K] MvPolynomial (S₁ ⊕ S₂) K :=
    ((algebraTensorAlgEquiv K (MvPolynomial S₂ K) (σ := S₁)).restrictScalars K).toLinearEquiv.trans
      (sumAlgEquiv K S₁ S₂).symm.toLinearEquiv
  have he : ∀ p : κ₁ × κ₂, e (TensorProduct.tmul K (w p.2) (v p.1)) =
      rename Sum.inl (v p.1) * rename Sum.inr (w p.2) := by
    intro p
    apply (sumAlgEquiv K S₁ S₂).injective
    simp [e, algebraTensorAlgEquiv_tmul, sumAlgEquiv_rename_inl, sumAlgEquiv_rename_inr_eq_C', smul_eq_C_mul, MvPolynomial.algebraMap_eq,
      mul_comm]
  have h2 := h.map' e.toLinearMap e.ker
  simpa only [Function.comp_def, Prod.fst_swap, Prod.snd_swap, LinearEquiv.coe_coe, he] using h2

def sumComplementToProduct {ι σ : Type} (i : ι) : σ ⊕ ({j // j ≠ i} × σ) → ι × σ :=
  Sum.elim (fun x => (i, x)) (fun p => (p.1.1, p.2))

/- English proof (translation)
Introduce `x y h`. Apply the tactic sequence `rcases x with x | ⟨⟨j, hj⟩, x⟩ <;> rcases y with y | ⟨⟨j', hj'⟩, y⟩ <;>`. Simplify using `only [sumComplementToProduct, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at h`. Apply the tactic sequence `all_goals first`. Consider the case `exact absurd h.1.symm hj'`.

Consider the case `exact absurd h.1 hj`. Consider the case `simp_all`.
-/
theorem splitIndex_injective {ι σ : Type} (i : ι) : Function.Injective (sumComplementToProduct (σ := σ) i) := by
  intro x y h
  rcases x with x | ⟨⟨j, hj⟩, x⟩ <;> rcases y with y | ⟨⟨j', hj'⟩, y⟩ <;>
    simp only [sumComplementToProduct, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at h
  all_goals first
    | exact absurd h.1.symm hj'
    | exact absurd h.1 hj
    | simp_all

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `ι _ _ hι σ κ b hb`. Use `haveI : IsEmpty ι := Fintype.card_eq_zero_iff.1 hι`. Use `haveI : Unique (∀ τ, κ τ) := Pi.uniqueOfIsEmpty κ`.

Rewrite using `[linearIndependent_unique_iff]`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `ι _ _ hι σ κ b hb`. Take `⟨τ₀⟩ : Nonempty ι` from `Fintype.card_pos_iff.1 (by omega)`.

Establish `hcard : Fintype.card {τ // τ ≠ τ₀} = n`. Rewrite using `[Fintype.card_subtype_compl, Fintype.card_subtype_eq, hι]`. Use linear arithmetic over natural numbers and integers. Establish `hW` using `ih {τ // τ ≠ τ₀} hcard (fun τ => κ τ.1) (fun τ => b τ.1) (fun τ => hb τ.1)`. Establish `hP` using `linearIndependent_rename_mul (b τ₀) _ (hb τ₀) hW`.

Establish `hR` using `hP.map' (rename (sumComplementToProduct (σ := σ) τ₀)).toLinearMap (LinearMap.ker_eq_bot.2 (rename_injective _ (splitIndex_injective τ₀)))`. Establish `h2` using `hR.comp (Equiv.piSplitAt τ₀ κ) (Equiv.piSplitAt τ₀ κ).injective`. Establish `key : ∀ g : (∀ τ, κ τ), ∏ τ, rename (Prod.mk τ) (b τ (g τ)) = rename (sumComplementToProduct (σ` using `σ) τ₀) (rename Sum.inl (b τ₀ (g τ₀)) * rename Sum.inr (∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (g τ.1)))) := by`. Introduce `g`. Simplify using `only [map_mul, map_prod, rename_rename]`.

Rewrite using `[Fintype.prod_eq_mul_prod_subtype_ne _ τ₀]`. Both sides reduce to the same expression. Establish `hfun : (fun g : (∀ τ, κ τ) => ∏ τ, rename (Prod.mk τ) (b τ (g τ))) = ((rename (sumComplementToProduct (σ` using `σ) τ₀)).toLinearMap ∘ (fun p : κ τ₀ × (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => rename Sum.inl (b τ₀ p.1) * rename Sum.inr (∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (p.2 τ))))) ∘ (Equiv.piSplitAt τ₀ κ) := by`. Use function extensionality and compare the values at `g`. Rewrite using `[key g]`.

Both sides reduce to the same expression. Rewrite using `[hfun]`. Conclude with `h2`.
-/
theorem linearIndependent_prod_rename_of_card (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ {σ : Type} (κ : ι → Type) (b : ∀ τ, κ τ → MvPolynomial σ K), (∀ τ, LinearIndependent K (b τ)) →
    LinearIndependent K (fun g : (∀ τ, κ τ) => ∏ τ, rename (Prod.mk τ) (b τ (g τ))) := by
  induction n with
  | zero =>
    intro ι _ _ hι σ κ b hb
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.1 hι
    haveI : Unique (∀ τ, κ τ) := Pi.uniqueOfIsEmpty κ
    rw [linearIndependent_unique_iff]
    simp
  | succ n ih =>
    intro ι _ _ hι σ κ b hb
    obtain ⟨τ₀⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    have hcard : Fintype.card {τ // τ ≠ τ₀} = n := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hι]; omega
    have hW := ih {τ // τ ≠ τ₀} hcard (fun τ => κ τ.1) (fun τ => b τ.1) (fun τ => hb τ.1)
    have hP := linearIndependent_rename_mul (b τ₀) _ (hb τ₀) hW
    have hR := hP.map' (rename (sumComplementToProduct (σ := σ) τ₀)).toLinearMap
      (LinearMap.ker_eq_bot.2 (rename_injective _ (splitIndex_injective τ₀)))
    have h2 := hR.comp (Equiv.piSplitAt τ₀ κ) (Equiv.piSplitAt τ₀ κ).injective
    have key : ∀ g : (∀ τ, κ τ), ∏ τ, rename (Prod.mk τ) (b τ (g τ)) =
        rename (sumComplementToProduct (σ := σ) τ₀) (rename Sum.inl (b τ₀ (g τ₀)) *
          rename Sum.inr (∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (g τ.1)))) := by
      intro g
      simp only [map_mul, map_prod, rename_rename]
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ τ₀]
      rfl
    have hfun : (fun g : (∀ τ, κ τ) => ∏ τ, rename (Prod.mk τ) (b τ (g τ))) =
        ((rename (sumComplementToProduct (σ := σ) τ₀)).toLinearMap ∘ (fun p : κ τ₀ × (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) =>
          rename Sum.inl (b τ₀ p.1) * rename Sum.inr (∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (p.2 τ))))) ∘
          (Equiv.piSplitAt τ₀ κ) := by
      funext g
      rw [key g]
      rfl
    rw [hfun]
    exact h2

/- English proof (translation)
Conclude with `linearIndependent_prod_rename_of_card _ ι rfl κ b hb`.
-/
theorem linearIndependent_prod_rename_of_forall {ι σ : Type} [Fintype ι] [DecidableEq ι] (κ : ι → Type) (b : ∀ τ, κ τ → MvPolynomial σ K)
    (hb : ∀ τ, LinearIndependent K (b τ)) :
    LinearIndependent K (fun g : (∀ τ, κ τ) => ∏ τ, rename (Prod.mk τ) (b τ (g τ))) := by
  exact linearIndependent_prod_rename_of_card _ ι rfl κ b hb

section Len

/- English proof (translation)
Establish `h : (B.comap A.subtype).map (Submodule.equivMapOfInjective f hf A : A →ₗ[O] A.map f) = (B.map f).comap (A.map f).subtype`. Use extensionality with `⟨y, hy⟩`. Simplify using `only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨x, hxA⟩, hxB, hx⟩`.

Use `⟨x, hxB, ?_⟩` and prove the remaining obligations. Establish `hx'` using `congrArg Subtype.val hx`. Conclude with `hx'`. Introduce and unpack `⟨x, hxB, rfl⟩`. Take `⟨x', hx'A, hx'⟩` from `Submodule.mem_map.1 hy`.

Establish `hxx : x' = x` using `hf hx'`. Substitute `hxx` using the available equality. Conclude with `⟨⟨x', hx'A⟩, hxB, Subtype.ext rfl⟩`. Conclude with `(Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf A) h).length_eq.symm`.
-/
theorem length_quot_map_of_injective {O M M' : Type*} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (f : M →ₗ[O] M') (hf : Function.Injective f) (A B : Submodule O M) :
    Module.length O (A.map f ⧸ (B.map f).comap (A.map f).subtype) = Module.length O (A ⧸ B.comap A.subtype) := by
  have h : (B.comap A.subtype).map (Submodule.equivMapOfInjective f hf A : A →ₗ[O] A.map f) =
      (B.map f).comap (A.map f).subtype := by
    ext ⟨y, hy⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨⟨x, hxA⟩, hxB, hx⟩
      refine ⟨x, hxB, ?_⟩
      have hx' := congrArg Subtype.val hx
      exact hx'
    · rintro ⟨x, hxB, rfl⟩
      obtain ⟨x', hx'A, hx'⟩ := Submodule.mem_map.1 hy
      have hxx : x' = x := hf hx'
      subst hxx
      exact ⟨⟨x', hx'A⟩, hxB, Subtype.ext rfl⟩
  exact (Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf A) h).length_eq.symm

/- English proof (translation)
Use `set P := Submodule.pi Set.univ fun _ : G => A with hP`. Use `set B' := B.comap A.subtype with hB'`. Set `pr : G → P →ₗ[O] A` to `fun g => LinearMap.codRestrict A ((LinearMap.proj g).comp P.subtype) (fun x => x.2 g (Set.mem_univ g))`. Set `φ : P →ₗ[O] (G → A ⧸ B')` to `LinearMap.pi fun g => B'.mkQ.comp (pr g)`. Establish `hsurj : Function.Surjective φ`.

Introduce `y`. Use `choose x hx using fun g => Submodule.Quotient.mk_surjective B' (y g)`. Use `⟨⟨fun g => (x g : M), fun g _ => (x g).2⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Simplify using `only [φ, pr, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply]`.

Rewrite using `[← hx g]`. Both sides reduce to the same expression. Establish `hker : LinearMap.ker φ = (Submodule.pi Set.univ fun _ : G => B).comap P.subtype`. Use extensionality with `x`. Simplify using `only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_pi, Set.mem_univ, true_implies]`.

Prove the components needed by the constructor for the conclusion. Introduce `h g`. Establish `hg` using `congrFun h g`. Simplify using `only [φ, pr, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply, Submodule.Quotient.mk_eq_zero, hB', Submodule.mem_comap] at hg`. Conclude with `hg`.

Introduce `h`. Use function extensionality and compare the values at `g`. Simplify using `only [φ, pr, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply, Submodule.Quotient.mk_eq_zero, hB', Submodule.mem_comap]`. Conclude with `h g`. Establish `e` using `(Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective φ hsurj)`.

Rewrite using `[e.length_eq, Module.length_pi, ENat.card_eq_coe_fintype_card, nsmul_eq_mul]`.
-/
theorem length_quot_pi_const {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M] (G : Type*) [Fintype G] [DecidableEq G]
    (A B : Submodule O M) :
    Module.length O ((Submodule.pi Set.univ fun _ : G => A) ⧸
        (Submodule.pi Set.univ fun _ : G => B).comap (Submodule.pi Set.univ fun _ : G => A).subtype) =
      Fintype.card G • Module.length O (A ⧸ B.comap A.subtype) := by
  set P := Submodule.pi Set.univ fun _ : G => A with hP
  set B' := B.comap A.subtype with hB'
  let pr : G → P →ₗ[O] A := fun g =>
    LinearMap.codRestrict A ((LinearMap.proj g).comp P.subtype) (fun x => x.2 g (Set.mem_univ g))
  let φ : P →ₗ[O] (G → A ⧸ B') := LinearMap.pi fun g => B'.mkQ.comp (pr g)
  have hsurj : Function.Surjective φ := by
    intro y
    choose x hx using fun g => Submodule.Quotient.mk_surjective B' (y g)
    refine ⟨⟨fun g => (x g : M), fun g _ => (x g).2⟩, ?_⟩
    funext g
    simp only [φ, pr, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [← hx g]
    rfl
  have hker : LinearMap.ker φ = (Submodule.pi Set.univ fun _ : G => B).comap P.subtype := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_pi,
      Set.mem_univ, true_implies]
    constructor
    · intro h g
      have hg := congrFun h g
      simp only [φ, pr, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply,
        Submodule.Quotient.mk_eq_zero, hB', Submodule.mem_comap] at hg
      exact hg
    · intro h
      funext g
      simp only [φ, pr, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply,
        Submodule.Quotient.mk_eq_zero, hB', Submodule.mem_comap]
      exact h g
  have e := (Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective φ hsurj)
  rw [e.length_eq, Module.length_pi, ENat.card_eq_coe_fintype_card, nsmul_eq_mul]

end Len

section Psi

variable {K : Type*} [Field K]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Use extensionality with `m`. Establish `h'` using `congrArg (mvPolynomialCoeffInFirstVariables (K := K) (S₁ := S₁) (S₂ := S₂) m) h`. Simplify using `only [map_sum, leftCoeff_rename_mul, map_zero] at h'`. Simplify using `using (Fintype.linearIndependent_iff.1 hw) (fun j => coeff m (a j)) h' j`.
-/
theorem eq_zero_of_sum_rename_mul {S₁ S₂ κ : Type*} [Fintype κ] (w : κ → MvPolynomial S₂ K) (hw : LinearIndependent K w)
    (a : κ → MvPolynomial S₁ K) (h : ∑ j, rename Sum.inl (a j) * rename Sum.inr (w j) = 0) : a = 0 := by
  funext j
  ext m
  have h' := congrArg (mvPolynomialCoeffInFirstVariables (K := K) (S₁ := S₁) (S₂ := S₂) m) h
  simp only [map_sum, leftCoeff_rename_mul, map_zero] at h'
  simpa using (Fintype.linearIndependent_iff.1 hw) (fun j => coeff m (a j)) h' j

def mvPolynomialProductExtension {ι σ : Type} [Fintype ι] [DecidableEq ι] (τ₀ : ι) (κ : ι → Type) [∀ τ, Fintype (κ τ)]
    (b : ∀ τ, κ τ → MvPolynomial σ K) :
    ((∀ τ : {τ // τ ≠ τ₀}, κ τ.1) → MvPolynomial σ K) →ₗ[K] MvPolynomial (ι × σ) K where
  toFun h := ∑ g, rename (Prod.mk τ₀) (h g) * ∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ.1) (b τ.1 (g τ))
  map_add' h h' := by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' c h := by simp only [Pi.smul_apply, map_smul, smul_mul_assoc, Finset.smul_sum, RingHom.id_apply]

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `h hh`. Establish `hW : LinearIndependent K (fun g : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => ∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (g τ)))` using `linearIndependent_prod_rename_of_forall (fun τ : {τ // τ ≠ τ₀} => κ τ.1) (fun τ => b τ.1) (fun τ => hb τ.1 τ.2)`. Establish `key : mvPolynomialProductExtension τ₀ κ b h = rename (sumComplementToProduct (σ` using `σ) τ₀) (∑ g, rename Sum.inl (h g) * rename Sum.inr (∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (g τ)))) := by`. Simplify using `only [mvPolynomialProductExtension, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_mul, map_prod, rename_rename]`.

Both sides reduce to the same expression. Rewrite `hh` using `[key]`. Establish `hh' : ∑ g, rename Sum.inl (h g) * rename Sum.inr (∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (g τ))) = 0` using `rename_injective _ (splitIndex_injective τ₀) (by rw [hh, map_zero])`. Conclude with `eq_zero_of_sum_rename_mul _ hW h hh'`.
-/
theorem factorMap_injective {ι σ : Type} [Fintype ι] [DecidableEq ι] (τ₀ : ι) (κ : ι → Type) [∀ τ, Fintype (κ τ)]
    (b : ∀ τ, κ τ → MvPolynomial σ K) (hb : ∀ τ, τ ≠ τ₀ → LinearIndependent K (b τ)) :
    Function.Injective (mvPolynomialProductExtension τ₀ κ b) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro h hh
  have hW : LinearIndependent K (fun g : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) =>
      ∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (g τ))) :=
    linearIndependent_prod_rename_of_forall (fun τ : {τ // τ ≠ τ₀} => κ τ.1) (fun τ => b τ.1) (fun τ => hb τ.1 τ.2)
  have key : mvPolynomialProductExtension τ₀ κ b h = rename (sumComplementToProduct (σ := σ) τ₀) (∑ g, rename Sum.inl (h g) *
      rename Sum.inr (∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (g τ)))) := by
    simp only [mvPolynomialProductExtension, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_mul, map_prod, rename_rename]
    rfl
  rw [key] at hh
  have hh' : ∑ g, rename Sum.inl (h g) *
      rename Sum.inr (∏ τ : {τ // τ ≠ τ₀}, rename (Prod.mk τ) (b τ.1 (g τ))) = 0 :=
    rename_injective _ (splitIndex_injective τ₀) (by rw [hh, map_zero])
  exact eq_zero_of_sum_rename_mul _ hW h hh'

/- English proof (translation)
Rewrite using `[length_quot_map_of_injective _ (show Function.Injective ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O) from factorMap_injective τ₀ κ b hb), length_quot_pi_const, Fintype.card_pi]`.
-/
theorem length_quot_map_positionMap {ι σ : Type} [Fintype ι] [DecidableEq ι] (τ₀ : ι) (κ : ι → Type) [∀ τ, Fintype (κ τ)]
    [∀ τ, DecidableEq (κ τ)] (b : ∀ τ, κ τ → MvPolynomial σ K) (hb : ∀ τ, τ ≠ τ₀ → LinearIndependent K (b τ))
    (O : Subring K) (A₀ B₀ : Submodule O (MvPolynomial σ K)) :
    Module.length O (((Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => A₀).map
          ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O)) ⧸
        ((Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => B₀).map ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O)).comap
          ((Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => A₀).map
            ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O)).subtype) =
      (∏ τ : {τ // τ ≠ τ₀}, Fintype.card (κ τ.1)) • Module.length O (A₀ ⧸ B₀.comap A₀.subtype) := by
  rw [length_quot_map_of_injective _ (show Function.Injective ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O) from
    factorMap_injective τ₀ κ b hb), length_quot_pi_const, Fintype.card_pi]

end Psi

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
