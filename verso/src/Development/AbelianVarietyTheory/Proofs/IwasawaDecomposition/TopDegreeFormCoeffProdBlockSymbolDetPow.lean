import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockSymApply

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace GlobalTheory.BlockTop

section General

variable {α : Type} [Fintype α] [DecidableEq α]

def graph (w : Equiv.Perm α) : α × α →₀ ℕ := ∑ a, Finsupp.single (a, w a) 1

def tc (P : MvPolynomial (α × α) ℂ) : ℂ :=
  ∑ w : Equiv.Perm α, ((Equiv.Perm.sign w : ℤ) : ℂ) * coeff (graph w) P

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem topCoeff_eq_tc {n : ℕ} (P : MvPolynomial (Fin n × Fin n) ℂ) : GlobalTheory.GoodMetric.topCoeff P = tc P := rfl

/- English proof (translation)
Simplify using `only [tc, coeff_sum, Finset.mul_sum]`. Conclude with `Finset.sum_comm`.
-/
theorem tc_sum {κ : Type} (s : Finset κ) (f : κ → MvPolynomial (α × α) ℂ) :
    tc (∑ i ∈ s, f i) = ∑ i ∈ s, tc (f i) := by
  simp only [tc, coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

/- English proof (translation)
Simplify using `only [tc, coeff_monomial, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem tc_monomial (u : α × α →₀ ℕ) (c : ℂ) : tc (monomial u c) = c * tc (monomial u 1) := by
  simp only [tc, coeff_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs <;> ring

/- English proof (translation)
Rewrite using `[graph, Finsupp.finset_sum_apply, Finset.sum_eq_single a (fun c _ hc => by simp [Finsupp.single_apply, hc]) (by simp)]`. Simplify using `[Finsupp.single_apply]`.
-/
theorem graph_apply (w : Equiv.Perm α) (a b : α) : graph w (a, b) = if w a = b then 1 else 0 := by
  rw [graph, Finsupp.finset_sum_apply, Finset.sum_eq_single a (fun c _ hc => by simp [Finsupp.single_apply, hc]) (by simp)]
  simp [Finsupp.single_apply]

/- English proof (translation)
Unfold `tc`. Rewrite using `[← (Equiv.permCongr e).sum_comp]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Establish `hg : graph (e.permCongr v) = Finsupp.mapDomain (Prod.map e e) (graph v)`. Unfold `graph`.

Rewrite using `[Finsupp.mapDomain_finset_sum]`. Simplify using `only [Finsupp.mapDomain_single]`. Rewrite using `[← e.sum_comp]`. Simplify using `[Equiv.permCongr_apply]`. Establish `hinj : Function.Injective (Prod.map e e)` using `fun x y h => by`.

Simplify using `only [Prod.map, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h`. Conclude with `Prod.ext h.1 h.2`. Rewrite using `[hg, coeff_rename_mapDomain _ hinj, Equiv.Perm.sign_permCongr]`.
-/
theorem tc_rename_equiv {β : Type} [Fintype β] [DecidableEq β] (e : α ≃ β) (P : MvPolynomial (α × α) ℂ) :
    tc (rename (Prod.map e e) P) = tc P := by
  unfold tc
  rw [← (Equiv.permCongr e).sum_comp]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hg : graph (e.permCongr v) = Finsupp.mapDomain (Prod.map e e) (graph v) := by
    unfold graph
    rw [Finsupp.mapDomain_finset_sum]
    simp only [Finsupp.mapDomain_single]
    rw [← e.sum_comp]
    simp [Equiv.permCongr_apply]
  have hinj : Function.Injective (Prod.map e e) := fun x y h => by
    simp only [Prod.map, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    exact Prod.ext h.1 h.2
  rw [hg, coeff_rename_mapDomain _ hinj, Equiv.Perm.sign_permCongr]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.prod_insert ha, ih, monomial_mul, Finset.sum_insert ha, Finset.prod_insert ha]`.
-/
theorem prod_monomial' {κ : Type} (s : Finset κ) (f : κ → α × α →₀ ℕ) (c : κ → ℂ) :
    ∏ i ∈ s, (monomial (f i) (c i) : MvPolynomial (α × α) ℂ) = monomial (∑ i ∈ s, f i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, ih, monomial_mul, Finset.sum_insert ha, Finset.prod_insert ha]

end General

section Blocks

variable {ι γ : Type} [Fintype ι] [DecidableEq ι] [Fintype γ] [DecidableEq γ]

def emb (τ : ι) (v : γ × γ) : (ι × γ) × (ι × γ) := ((τ, v.1), (τ, v.2))

/- English proof (translation)
Introduce and unpack `⟨a, b⟩ ⟨c, d⟩ h`. Simplify using `only [emb, Prod.mk.injEq, true_and] at h`. Simplify using `[h]`.
-/
theorem emb_injective (τ : ι) : Function.Injective (emb (γ := γ) τ) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [emb, Prod.mk.injEq, true_and] at h
  simp [h]

def glue (D : ι → (γ × γ →₀ ℕ)) : (ι × γ) × (ι × γ) →₀ ℕ := ∑ τ, (D τ).mapDomain (emb τ)

/- English proof (translation)
Unfold `glue`. Rewrite using `[Finsupp.finset_sum_apply, Finset.sum_eq_single τ]`. Conclude with `Finsupp.mapDomain_apply (emb_injective τ) _ _`. Introduce `τ' _ hτ'`. Apply `Finsupp.mapDomain_notin_range` to reduce the goal to its premises.

Introduce and unpack `⟨u, hu⟩`. Simplify using `only [emb, Prod.mk.injEq] at hu`. Conclude with `hτ' hu.1.1`. Simplify using the standard rewrite rules.
-/
theorem glue_emb (D : ι → (γ × γ →₀ ℕ)) (τ : ι) (v : γ × γ) : glue D (emb τ v) = D τ v := by
  unfold glue
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single τ]
  · exact Finsupp.mapDomain_apply (emb_injective τ) _ _
  · intro τ' _ hτ'
    apply Finsupp.mapDomain_notin_range
    rintro ⟨u, hu⟩
    simp only [emb, Prod.mk.injEq] at hu
    exact hτ' hu.1.1
  · simp

/- English proof (translation)
Unfold `glue`. Rewrite using `[Finsupp.finset_sum_apply]`. Use `Finset.sum_eq_zero fun τ _ => Finsupp.mapDomain_notin_range _ _ ?_` and prove the remaining obligations. Introduce and unpack `⟨u, hu⟩`. Simplify using `only [emb, Prod.mk.injEq] at hu`.

Conclude with `h (by rw [← hu.1, ← hu.2])`.
-/
theorem glue_off (D : ι → (γ × γ →₀ ℕ)) (a b : ι × γ) (h : a.1 ≠ b.1) : glue D (a, b) = 0 := by
  unfold glue
  rw [Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun τ _ => Finsupp.mapDomain_notin_range _ _ ?_
  rintro ⟨u, hu⟩
  simp only [emb, Prod.mk.injEq] at hu
  exact h (by rw [← hu.1, ← hu.2])

/- English proof (translation)
Introduce `D D' h`. Use function extensionality and compare the values at `τ`. Use extensionality with `v`. Rewrite using `[← glue_emb, h, glue_emb]`.
-/
theorem glue_injective : Function.Injective (glue (ι := ι) (γ := γ)) := by
  intro D D' h
  funext τ
  ext v
  rw [← glue_emb, h, glue_emb]

/- English proof (translation)
Unfold `glue graph`. Simplify using `only [Finsupp.mapDomain_finset_sum, Finsupp.mapDomain_single]`. Rewrite using `[Fintype.sum_prod_type]`. Both sides reduce to the same expression.
-/
theorem graph_prodCongrRight (σ : ι → Equiv.Perm γ) :
    graph (Equiv.prodCongrRight σ) = glue fun τ => graph (σ τ) := by
  unfold glue graph
  simp only [Finsupp.mapDomain_finset_sum, Finsupp.mapDomain_single]
  rw [Fintype.sum_prod_type]
  rfl

/- English proof (translation)
Establish `hw' : ∀ b, (w.symm b).1 = b.1` using `fun b => by`. Use `hw (w.symm b)` as an intermediate fact. Rewrite `this` using `[Equiv.apply_symm_apply]`. Conclude with `this.symm`. Establish `li : ∀ τ x, (w.symm (τ, (w (τ, x)).2)).2 = x` using `fun τ x => by`.

Establish `e1 : (τ, (w (τ, x)).2) = w (τ, x)` using `Prod.ext (hw (τ, x)).symm rfl`. Rewrite using `[e1, Equiv.symm_apply_apply]`. Establish `ri : ∀ τ x, (w (τ, (w.symm (τ, x)).2)).2 = x` using `fun τ x => by`. Establish `e1 : (τ, (w.symm (τ, x)).2) = w.symm (τ, x)` using `Prod.ext (hw' (τ, x)).symm rfl`. Rewrite using `[e1, Equiv.apply_symm_apply]`.

Use `⟨fun τ => Equiv.mk (fun x => (w (τ, x)).2) (fun x => (w.symm (τ, x)).2) (li τ) (ri τ), ?_⟩` and prove the remaining obligations. Use extensionality with `⟨τ, x⟩`. Simplify using `[hw]`. Simplify using the standard rewrite rules.
-/
theorem exists_prodCongrRight (w : Equiv.Perm (ι × γ)) (hw : ∀ a, (w a).1 = a.1) :
    ∃ σ : ι → Equiv.Perm γ, Equiv.prodCongrRight σ = w := by
  have hw' : ∀ b, (w.symm b).1 = b.1 := fun b => by
    have := hw (w.symm b)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have li : ∀ τ x, (w.symm (τ, (w (τ, x)).2)).2 = x := fun τ x => by
    have e1 : (τ, (w (τ, x)).2) = w (τ, x) := Prod.ext (hw (τ, x)).symm rfl
    rw [e1, Equiv.symm_apply_apply]
  have ri : ∀ τ x, (w (τ, (w.symm (τ, x)).2)).2 = x := fun τ x => by
    have e1 : (τ, (w.symm (τ, x)).2) = w.symm (τ, x) := Prod.ext (hw' (τ, x)).symm rfl
    rw [e1, Equiv.apply_symm_apply]
  refine ⟨fun τ => Equiv.mk (fun x => (w (τ, x)).2) (fun x => (w.symm (τ, x)).2) (li τ) (ri τ), ?_⟩
  ext ⟨τ, x⟩
  · simp [hw]
  · simp

/- English proof (translation)
Introduce `σ σ' h`. Use function extensionality and compare the values at `τ`. Use extensionality with `x`. Use `congrArg (fun w : Equiv.Perm (ι × γ) => (w (τ, x)).2) h` as an intermediate fact. Simplify using `using this`.
-/
theorem prodCongrRight_injective :
    Function.Injective (fun σ : ι → Equiv.Perm γ => (Equiv.prodCongrRight σ : Equiv.Perm (ι × γ))) := by
  intro σ σ' h
  funext τ
  ext x
  have := congrArg (fun w : Equiv.Perm (ι × γ) => (w (τ, x)).2) h
  simpa using this

/- English proof (translation)
Simplify using `only [tc, coeff_monomial]`. Rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ]`. Use `set F : Equiv.Perm (ι × γ) → ℂ := fun w => ((Equiv.Perm.sign w : ℤ) : ℂ) * if glue D = graph w then 1 else 0 with hF`. Establish `h1 : ∑ w, F w = ∑ w ∈ Finset.univ.image (fun σ : ι → Equiv.Perm γ => Equiv.prodCongrRight σ), F w`. Use `(Finset.sum_subset (Finset.subset_univ _) fun w _ hw => ?_).symm` and prove the remaining obligations.

Simplify using `only [hF]`. Rewrite using `[if_neg, mul_zero]`. Introduce `hg`. Apply `hw` to reduce the goal to its premises. Establish `hb : ∀ a, (w a).1 = a.1`.

Introduce `a`. Assume the negation of the conclusion as `hne`. Establish `e1` using `glue_off D a (w a) (Ne.symm hne)`. Rewrite `e1` using `[hg, graph_apply, if_pos rfl]`. Conclude with `one_ne_zero e1`.

Take `⟨σ, hσ⟩` from `exists_prodCongrRight w hb`. Conclude with `Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, hσ⟩`. Rewrite using `[h1, Finset.sum_image fun x _ y _ h => prodCongrRight_injective h]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Simplify using `only [hF, graph_prodCongrRight, glue_injective.eq_iff, Equiv.Perm.sign_prodCongrRight]`.

Rewrite using `[Finset.prod_mul_distrib]`. Use `push_cast`. Use `congr 1`. Distinguish the cases in `hD : D = fun τ => graph (σ τ)`. Rewrite using `[if_pos hD]`.

Use `symm`. Conclude with `Finset.prod_eq_one fun τ _ => if_pos (congrFun hD τ)`. Rewrite using `[if_neg hD]`. Choose the witnesses or unpack the hypotheses as in `⟨τ, hτ⟩ : ∃ τ, D τ ≠ graph (σ τ) := by`. Assume the negation of the conclusion as `hall`.

Use `push_neg at hall`. Conclude with `hD (funext hall)`. Use `symm`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ)`.
-/
theorem tc_monomial_glue (D : ι → (γ × γ →₀ ℕ)) :
    tc (monomial (glue D) (1 : ℂ)) = ∏ τ, tc (monomial (D τ) (1 : ℂ)) := by
  simp only [tc, coeff_monomial]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  set F : Equiv.Perm (ι × γ) → ℂ := fun w => ((Equiv.Perm.sign w : ℤ) : ℂ) * if glue D = graph w then 1 else 0 with hF
  have h1 : ∑ w, F w = ∑ w ∈ Finset.univ.image (fun σ : ι → Equiv.Perm γ => Equiv.prodCongrRight σ), F w := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun w _ hw => ?_).symm
    simp only [hF]
    rw [if_neg, mul_zero]
    intro hg
    apply hw
    have hb : ∀ a, (w a).1 = a.1 := by
      intro a
      by_contra hne
      have e1 := glue_off D a (w a) (Ne.symm hne)
      rw [hg, graph_apply, if_pos rfl] at e1
      exact one_ne_zero e1
    obtain ⟨σ, hσ⟩ := exists_prodCongrRight w hb
    exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, hσ⟩
  rw [h1, Finset.sum_image fun x _ y _ h => prodCongrRight_injective h]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [hF, graph_prodCongrRight, glue_injective.eq_iff, Equiv.Perm.sign_prodCongrRight]
  rw [Finset.prod_mul_distrib]
  push_cast
  congr 1
  by_cases hD : D = fun τ => graph (σ τ)
  · rw [if_pos hD]
    symm
    exact Finset.prod_eq_one fun τ _ => if_pos (congrFun hD τ)
  · rw [if_neg hD]
    obtain ⟨τ, hτ⟩ : ∃ τ, D τ ≠ graph (σ τ) := by
      by_contra hall
      push_neg at hall
      exact hD (funext hall)
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ)

/- English proof (translation)
Establish `hL : ∏ τ, rename (emb τ) (f τ) = ∑ x ∈ Fintype.piFinset fun τ => (f τ).support, monomial (glue x) (∏ τ, coeff (x τ) (f τ))`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Use `conv_lhs => rw [(f τ).as_sum]`. Rewrite using `[map_sum]`.

Simplify using `only [rename_monomial]`. Use `_ = _ := by`. Rewrite using `[Finset.prod_univ_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[prod_monomial']`.

Both sides reduce to the same expression. Establish `hR : ∀ τ, tc (f τ) = ∑ d ∈ (f τ).support, coeff d (f τ) * tc (monomial d (1 : ℂ))`. Introduce `τ`. Use `conv_lhs => rw [(f τ).as_sum]`. Rewrite using `[tc_sum]`.

Conclude with `Finset.sum_congr rfl fun d _ => tc_monomial _ _`. Rewrite using `[hL, tc_sum]`. Repeatedly rewrite using `[hR]`. Rewrite using `[Finset.prod_univ_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[tc_monomial, tc_monomial_glue, Finset.prod_mul_distrib]`.
-/
theorem tc_prod_rename (f : ι → MvPolynomial (γ × γ) ℂ) :
    tc (∏ τ, rename (emb τ) (f τ)) = ∏ τ, tc (f τ) := by
  have hL : ∏ τ, rename (emb τ) (f τ) = ∑ x ∈ Fintype.piFinset fun τ => (f τ).support,
      monomial (glue x) (∏ τ, coeff (x τ) (f τ)) := by
    calc ∏ τ, rename (emb τ) (f τ)
        = ∏ τ, ∑ d ∈ (f τ).support, monomial (d.mapDomain (emb τ)) (coeff d (f τ)) := by
          refine Finset.prod_congr rfl fun τ _ => ?_
          conv_lhs => rw [(f τ).as_sum]
          rw [map_sum]
          simp only [rename_monomial]
      _ = _ := by
          rw [Finset.prod_univ_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [prod_monomial']
          rfl
  have hR : ∀ τ, tc (f τ) = ∑ d ∈ (f τ).support, coeff d (f τ) * tc (monomial d (1 : ℂ)) := by
    intro τ
    conv_lhs => rw [(f τ).as_sum]
    rw [tc_sum]
    exact Finset.sum_congr rfl fun d _ => tc_monomial _ _
  rw [hL, tc_sum]
  simp_rw [hR]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [tc_monomial, tc_monomial_glue, Finset.prod_mul_distrib]

end Blocks

end GlobalTheory.BlockTop

namespace GlobalTheory.BlockTop

def symMat (p q : ℕ) : Matrix (Fin p) (Fin p) (MvPolynomial ((Fin p × Fin q) × (Fin p × Fin q)) ℂ) :=
  Matrix.of fun i j => ∑ b : Fin q, X ((i, b), (j, b))

/- English proof (translation)
The claim follows from `(AlgHom.map_det (rename g) _).symm`.
-/
theorem det_map_rename {σ' : Type} (p q : ℕ) (g : (Fin p × Fin q) × (Fin p × Fin q) → σ') :
    ((symMat p q).map (rename (R := ℂ) g)).det = rename g (symMat p q).det :=
  (AlgHom.map_det (rename g) _).symm

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[GlobalTheory.DomainDens.blockSym, symMat, map_sum, rename_X, emb]`.
-/
theorem blockSym_eq {ι : Type} [Fintype ι] {p q n : ℕ} (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι) :
    GlobalTheory.DomainDens.blockSym h τ = (symMat p q).map
      (rename (Prod.map (Fintype.equivFinOfCardEq h) (Fintype.equivFinOfCardEq h) ∘ emb τ)) := by
  ext i j
  simp [GlobalTheory.DomainDens.blockSym, symMat, map_sum, rename_X, emb]

end GlobalTheory.BlockTop

open GlobalTheory.BlockTop in

/- English proof (translation)
Introduce `ι _ p q n h h1`. Use `set e := Fintype.equivFinOfCardEq h`. Use `set e1 := Fintype.equivFinOfCardEq h1`. Establish `hL : ∏ τ, (GlobalTheory.DomainDens.blockSym h τ).det ^ q = rename (Prod.map e e) (∏ τ, rename (emb τ) ((symMat p q).det ^ q))`. Rewrite using `[map_prod]`.

Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[blockSym_eq, det_map_rename, rename_rename, map_pow]`. Use `set e' : Fin p × Fin q ≃ Fin (p * q) := (Equiv.punitProd (Fin p × Fin q)).symm.trans e1`. Establish `hR : (GlobalTheory.DomainDens.blockSym h1 ()).det ^ q = rename (Prod.map e' e') ((symMat p q).det ^ q)`. Rewrite using `[blockSym_eq, det_map_rename, map_pow]`.

Both sides reduce to the same expression. Rewrite using `[hL, hR, topCoeff_eq_tc, topCoeff_eq_tc, tc_rename_equiv, tc_rename_equiv, tc_prod_rename, Finset.prod_const, Finset.card_univ]`.
-/
theorem GlobalTheory.DomainDens.topCoeff_prod_blockSym_det_pow : ∀ (ι : Type) [Fintype ι] (p q n : ℕ)
    (h : Fintype.card (ι × Fin p × Fin q) = n) (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q),
    GlobalTheory.GoodMetric.topCoeff (∏ τ, (GlobalTheory.DomainDens.blockSym h τ).det ^ q) =
      GlobalTheory.GoodMetric.topCoeff ((GlobalTheory.DomainDens.blockSym h1 ()).det ^ q) ^ Fintype.card ι := by
  intro ι _ p q n h h1
  classical
  set e := Fintype.equivFinOfCardEq h
  set e1 := Fintype.equivFinOfCardEq h1
  have hL : ∏ τ, (GlobalTheory.DomainDens.blockSym h τ).det ^ q =
      rename (Prod.map e e) (∏ τ, rename (emb τ) ((symMat p q).det ^ q)) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [blockSym_eq, det_map_rename, rename_rename, map_pow]
  set e' : Fin p × Fin q ≃ Fin (p * q) := (Equiv.punitProd (Fin p × Fin q)).symm.trans e1
  have hR : (GlobalTheory.DomainDens.blockSym h1 ()).det ^ q = rename (Prod.map e' e') ((symMat p q).det ^ q) := by
    rw [blockSym_eq, det_map_rename, map_pow]
    rfl
  rw [hL, hR, topCoeff_eq_tc, topCoeff_eq_tc, tc_rename_equiv, tc_rename_equiv, tc_prod_rename,
    Finset.prod_const, Finset.card_univ]
