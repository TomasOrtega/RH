import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatDecompositionTwoBlocksStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatDecompositionUniqueStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalVanishingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusReciprocityInnerProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarishChandraCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntertwinerInnerProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerProductCuspidalIsoStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MackeyInnerProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PermutationMatrixPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SamePartitionStatementStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Transp

open CategoryTheory
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

section Matrices

variable {ι : Type} [Fintype ι] [DecidableEq ι] {s s' : ℕ}

/- English proof (translation)
Unfold `pm`. Conclude with `map_mul _ _ _`.
-/
theorem pm_mul (σ τ : Equiv.Perm ι) : pm K (σ * τ) = pm K σ * pm K τ := by
  unfold pm; exact map_mul _ _ _

/- English proof (translation)
Unfold `pm`. Conclude with `(map_inv _ _).symm`.
-/
theorem pm_inv (σ : Equiv.Perm ι) : (pm K σ)⁻¹ = pm K σ⁻¹ := by
  unfold pm; exact (map_inv _ _).symm

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using (one_mem (parab K b)).1`. Consider the case `succ k ih`. Rewrite using `[pow_succ, Units.val_mul]`. Conclude with `isBlockUT_mul b ih h`.
-/
theorem isBlockUT_pow (b : ι → Fin s) {g : GL ι K} (h : IsBlockUT K b (g : Matrix ι ι K)) (k : ℕ) :
    IsBlockUT K b ((g ^ k : GL ι K) : Matrix ι ι K) := by
  induction k with
  | zero => simpa using (one_mem (parab K b)).1
  | succ k ih =>
    rw [pow_succ, Units.val_mul]
    exact isBlockUT_mul b ih h

/- English proof (translation)
Use `⟨h, ?_⟩` and prove the remaining obligations. Establish `hk : 0 < orderOf g` using `orderOf_pos g`. Establish `e : g⁻¹ = g ^ (orderOf g - 1)`. Apply `inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[← pow_succ', Nat.sub_add_cancel hk, pow_orderOf_eq_one]`.

Rewrite using `[e]`. Conclude with `isBlockUT_pow b h _`.
-/
theorem mem_parab_of_isBlockUT (b : ι → Fin s) {g : GL ι K} (h : IsBlockUT K b (g : Matrix ι ι K)) :
    g ∈ parab K b := by
  refine ⟨h, ?_⟩
  have hk : 0 < orderOf g := orderOf_pos g
  have e : g⁻¹ = g ^ (orderOf g - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hk, pow_orderOf_eq_one]
  rw [e]
  exact isBlockUT_pow b h _

/- English proof (translation)
Apply `mem_parab_of_isBlockUT` to reduce the goal to its premises. Introduce `i j hij`. Rewrite using `[(GlobalTheory.T.permutation_matrix_properties K ι τ).1 i j, if_neg]`. Introduce and unpack `rfl`. Rewrite `hij` using `[h]`.

Conclude with `lt_irrefl _ hij`.
-/
theorem pm_mem_parab (b : ι → Fin s) (τ : Equiv.Perm ι) (h : ∀ i, b (τ i) = b i) :
    pm K τ ∈ parab K b := by
  apply mem_parab_of_isBlockUT
  intro i j hij
  rw [(GlobalTheory.T.permutation_matrix_properties K ι τ).1 i j, if_neg]
  rintro rfl
  rw [h] at hij
  exact lt_irrefl _ hij

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `⟨i, hi⟩ ⟨j, hj⟩`. Simplify using `only [blkGL, dif_pos hu.1]`. Express the relevant statement in the definitionally equal form `(u : Matrix ι ι K) i j = _`. Rewrite using `[hu.2 i j (hi.trans hj.symm)]`.

Simplify using `[Matrix.one_apply, Subtype.ext_iff]`.
-/
theorem blkGL_unip (β : ι → Fin s) (c : Fin s) {u : GL ι K} (hu : u ∈ unip K β) :
    blkGL β c u = 1 := by
  apply Units.ext
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [blkGL, dif_pos hu.1]
  change (u : Matrix ι ι K) i j = _
  rw [hu.2 i j (hi.trans hj.symm)]
  simp [Matrix.one_apply, Subtype.ext_iff]

/- English proof (translation)
Use `Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Establish `h1 : blkGL β c u⁻¹ = 1`. Use `GlobalTheory.CompanionTheory.TyFin.CuspVan.blkGL_mul β c hu.1 (inv_mem hu.1)` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, blkGL_unip β c hu, one_mul, blkGL_unip β c (GlobalTheory.CompanionTheory.TyFin.CuspVan.one_mem_unip β), eq_comm]`. Then use the resulting hypothesis. Rewrite using `[GlobalTheory.CompanionTheory.TyFin.CuspVan.blkGL_mul β c (inv_mem hu.1) hh, h1, one_mul]`.
-/
theorem hcFun_inv_mul (β : ι → Fin s) (ψ : ∀ c : Fin s, GL {i // β i = c} K → ℂ) {u h : GL ι K}
    (hu : u ∈ unip K β) (hh : h ∈ parab K β) : hcFun β ψ (u⁻¹ * h) = hcFun β ψ h := by
  refine Finset.prod_congr rfl fun c _ => ?_
  have h1 : blkGL β c u⁻¹ = 1 := by
    have := GlobalTheory.CompanionTheory.TyFin.CuspVan.blkGL_mul β c hu.1 (inv_mem hu.1)
    rwa [mul_inv_cancel, blkGL_unip β c hu, one_mul,
      blkGL_unip β c (GlobalTheory.CompanionTheory.TyFin.CuspVan.one_mem_unip β), eq_comm] at this
  rw [GlobalTheory.CompanionTheory.TyFin.CuspVan.blkGL_mul β c (inv_mem hu.1) hh, h1, one_mul]

open Classical in

/- English proof (translation)
Use `GlobalTheory.T.cuspidal_vanishing K ι s s' b β lam hl hs (parab K b ⊓ parab K β) (fun h => hcFun β ψ h⁻¹) inf_le_left ?_` and prove the remaining obligations. Introduce `u hu hoff`. Establish `hub : IsBlockUT K b (u : Matrix ι ι K)` using `fun i j hij => hoff i j (ne_of_gt hij)`. Use `⟨⟨mem_parab_of_isBlockUT b hub, hu.1⟩, fun h hh => ?_⟩` and prove the remaining obligations. Simplify using `only [mul_inv_rev]`.

Conclude with `hcFun_inv_mul β ψ hu (inv_mem hh.2)`.
-/
theorem sum_inter_eq_zero (b : ι → Fin s) (β : ι → Fin s')
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (hl : ∀ c, IsCuspidal K (lam c))
    (ψ : ∀ c : Fin s', GL {i // β i = c} K → ℂ) (hs : ∃ i j, b i = b j ∧ β i ≠ β j) :
    (∑ h, if h ∈ parab K b ⊓ parab K β then
      hcFun β ψ h⁻¹ * hcFun b (fun c => (lam c).character) h else 0) = 0 := by
  refine GlobalTheory.T.cuspidal_vanishing K ι s s' b β lam hl hs (parab K b ⊓ parab K β)
    (fun h => hcFun β ψ h⁻¹) inf_le_left ?_
  intro u hu hoff
  have hub : IsBlockUT K b (u : Matrix ι ι K) := fun i j hij => hoff i j (ne_of_gt hij)
  refine ⟨⟨mem_parab_of_isBlockUT b hub, hu.1⟩, fun h hh => ?_⟩
  simp only [mul_inv_rev]
  exact hcFun_inv_mul β ψ hu (inv_mem hh.2)

/- English proof (translation)
Unfold `ip`. Use `mul_eq_zero_of_right _ ?_` and prove the remaining obligations. Distinguish the cases in `hA : ∃ i j, b i = b j ∧ β i ≠ β j`. Use `Eq.trans ?_ (sum_inter_eq_zero b β lam hl (fun c => (nu c).character) hA)` and prove the remaining obligations. Use `Fintype.sum_equiv (Equiv.inv _) _ _ fun g => ?_` and prove the remaining obligations.

Simplify using `only [Equiv.inv_apply, inv_inv, SetLike.mem_coe]`. Distinguish the cases in `hg : g ∈ parab K b ⊓ parab K β`. Rewrite using `[if_pos hg, if_pos (inv_mem hg), mul_comm]`. Rewrite using `[if_neg hg, if_neg (fun h => hg (by simpa using inv_mem h))]`. Establish `hB : ∃ i j, β i = β j ∧ b i ≠ b j`.

Assume the negation of the conclusion as `hB`. Use `push_neg at hA hB`. Conclude with `hs fun i j => ⟨hA i j, hB i j⟩`. Use `sum_inter_eq_zero β b nu hn (fun c => (lam c).character) hB` as an intermediate fact. Rewrite `this` using `[inf_comm]`.

Simplify `this` using `only [SetLike.mem_coe]`.
-/
theorem ip_inter_eq_zero (b : ι → Fin s) (β : ι → Fin s')
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (hl : ∀ c, IsCuspidal K (lam c))
    (nu : ∀ c : Fin s', FDRep ℂ (GL {i // β i = c} K)) (hn : ∀ c, IsCuspidal K (nu c))
    (hs : ¬ ∀ i j, b i = b j ↔ β i = β j) :
    ip ((parab K b ⊓ parab K β : Subgroup (GL ι K)) : Set (GL ι K))
      (hcFun b fun c => (lam c).character) (hcFun β fun c => (nu c).character) = 0 := by
  classical
  unfold ip
  refine mul_eq_zero_of_right _ ?_
  by_cases hA : ∃ i j, b i = b j ∧ β i ≠ β j
  · refine Eq.trans ?_ (sum_inter_eq_zero b β lam hl (fun c => (nu c).character) hA)
    refine Fintype.sum_equiv (Equiv.inv _) _ _ fun g => ?_
    simp only [Equiv.inv_apply, inv_inv, SetLike.mem_coe]
    by_cases hg : g ∈ parab K b ⊓ parab K β
    · rw [if_pos hg, if_pos (inv_mem hg), mul_comm]
    · rw [if_neg hg, if_neg (fun h => hg (by simpa using inv_mem h))]
  · have hB : ∃ i j, β i = β j ∧ b i ≠ b j := by
      by_contra hB
      push_neg at hA hB
      exact hs fun i j => ⟨hA i j, hB i j⟩
    have := sum_inter_eq_zero β b nu hn (fun c => (lam c).character) hB
    rw [inf_comm] at this
    simpa only [SetLike.mem_coe] using this

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem glEquiv_glEquiv {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] (f : α ≃ β) (e : β ≃ γ) (x : GL α K) :
    glEquiv K e (glEquiv K f x) = glEquiv K (f.trans e) x := by
  apply Units.ext
  ext i j
  rfl

open Classical in

/- English proof (translation)
Substitute `hβ` using the available equality. Rewrite using `[GlobalTheory.T.same_partition_statement K ι s s' b π]`. Establish `key : ∀ c, ip Set.univ (lam c).character (fun x => (mu (π c)).character (glEquiv K (e (π c)) (glEquiv K (Equiv.subtypeEquivRight (p` using `fun i => b i = c) (q := fun i => (π ∘ b) i = π c) fun _ => π.injective.eq_iff.symm) x))) = if CuspIso K (lam c) (mu (π c)) then 1 else 0 := by`. Introduce `c`. Simplify using `only [glEquiv_glEquiv]`.

Conclude with `(GlobalTheory.T.inner_product_cuspidal_iso K _ _ (lam c) (mu (π c)) _ (hl c) (hm (π c))).1`. Rewrite using `[Finset.prod_congr rfl fun c _ => key c, Finset.prod_boole]`. Simplify using the standard rewrite rules.
-/
theorem ip_same (b : ι → Fin s) (π : Fin s ≃ Fin s') (β : ι → Fin s') (hβ : β = π ∘ b) (b' : ι → Fin s')
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (mu : ∀ c : Fin s', FDRep ℂ (GL {i // b' i = c} K))
    (e : ∀ c : Fin s', {i // β i = c} ≃ {j // b' j = c})
    (hl : ∀ c, Simple (lam c)) (hm : ∀ c, Simple (mu c)) :
    ip ((parab K b ⊓ parab K β : Subgroup (GL ι K)) : Set (GL ι K))
      (hcFun b fun c => (lam c).character)
      (hcFun β fun c x => (mu c).character (glEquiv K (e c) x)) =
      if ∀ c, CuspIso K (lam c) (mu (π c)) then 1 else 0 := by
  subst hβ
  rw [GlobalTheory.T.same_partition_statement K ι s s' b π]
  have key : ∀ c, ip Set.univ (lam c).character (fun x => (mu (π c)).character
      (glEquiv K (e (π c)) (glEquiv K (Equiv.subtypeEquivRight (p := fun i => b i = c)
        (q := fun i => (π ∘ b) i = π c) fun _ => π.injective.eq_iff.symm) x))) =
      if CuspIso K (lam c) (mu (π c)) then 1 else 0 := by
    intro c
    simp only [glEquiv_glEquiv]
    exact (GlobalTheory.T.inner_product_cuspidal_iso K _ _ (lam c) (mu (π c)) _ (hl c) (hm (π c))).1
  rw [Finset.prod_congr rfl fun c _ => key c, Finset.prod_boole]
  simp

/- English proof (translation)
Set `f : Fin s → Fin s'` to `fun c => β (Function.surjInv hb c)`. Establish `hf : ∀ i, f (b i) = β i` using `fun i => (h _ _).1 (Function.surjInv_eq hb (b i))`. Establish `hinj : Function.Injective f`. Introduce `c d hcd`. Use `(h _ _).2 hcd` as an intermediate fact.

Rewrite `this` using `[Function.surjInv_eq hb, Function.surjInv_eq hb]`. Then use the resulting hypothesis. Establish `hsurj : Function.Surjective f` using `fun y => by`. Take `⟨i, rfl⟩` from `hβ y`. Conclude with `⟨b i, hf i⟩`. Use `⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, funext fun i => ?_⟩` and prove the remaining obligations.

Conclude with `(hf i).symm`.
-/
theorem exists_equiv_of_fibres (b : ι → Fin s) (β : ι → Fin s') (hb : Function.Surjective b)
    (hβ : Function.Surjective β) (h : ∀ i j, b i = b j ↔ β i = β j) :
    ∃ π : Fin s ≃ Fin s', β = π ∘ b := by
  let f : Fin s → Fin s' := fun c => β (Function.surjInv hb c)
  have hf : ∀ i, f (b i) = β i := fun i =>
    (h _ _).1 (Function.surjInv_eq hb (b i))
  have hinj : Function.Injective f := by
    intro c d hcd
    have := (h _ _).2 hcd
    rwa [Function.surjInv_eq hb, Function.surjInv_eq hb] at this
  have hsurj : Function.Surjective f := fun y => by
    obtain ⟨i, rfl⟩ := hβ y
    exact ⟨b i, hf i⟩
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, funext fun i => ?_⟩
  exact (hf i).symm

end Matrices

section Terms

variable {n s s' : ℕ} (b : Fin n → Fin s) (b' : Fin n → Fin s')
  (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
  (mu : ∀ c : Fin s', FDRep ℂ (GL {i // b' i = c} K))

open Classical in

/- English proof (translation)
Take `⟨-, h2, h3, h4⟩` from `GlobalTheory.T.permutation_matrix_properties K (Fin n) σ`. Establish `hf : (fun x => hcFun b' (fun c => (mu c).character) (pm K σ * x * (pm K σ)⁻¹)) = hcFun (b' ∘ σ) (fun c x => (mu c).character (glEquiv K (σ.subtypeEquiv (p` using `fun i => (b' ∘ σ) i = c) (q := fun j => b' j = c) fun _ => Iff.rfl) x)) := by`. Use function extensionality and compare the values at `x`. Rewrite using `[h2, h4 s' b']`. Rewrite using `[hf, h3 s' b']`.

Conclude with `ip_same b π (b' ∘ σ) h b' lam mu _ hl hm`.
-/
theorem term_same (σ : Equiv.Perm (Fin n)) (π : Fin s ≃ Fin s') (h : b' ∘ σ = π ∘ b)
    (hl : ∀ c, Simple (lam c)) (hm : ∀ c, Simple (mu c)) :
    ip ((parab K b ⊓ cj (pm K σ) (parab K b') : Subgroup (GL (Fin n) K)) : Set (GL (Fin n) K))
      (hcFun b fun c => (lam c).character)
      (fun x => hcFun b' (fun c => (mu c).character) (pm K σ * x * (pm K σ)⁻¹)) =
      if ∀ c, CuspIso K (lam c) (mu (π c)) then 1 else 0 := by
  obtain ⟨-, h2, h3, h4⟩ := GlobalTheory.T.permutation_matrix_properties K (Fin n) σ
  have hf : (fun x => hcFun b' (fun c => (mu c).character) (pm K σ * x * (pm K σ)⁻¹)) =
      hcFun (b' ∘ σ) (fun c x => (mu c).character (glEquiv K
        (σ.subtypeEquiv (p := fun i => (b' ∘ σ) i = c) (q := fun j => b' j = c) fun _ => Iff.rfl) x)) := by
    funext x
    rw [h2, h4 s' b']
  rw [hf, h3 s' b']
  exact ip_same b π (b' ∘ σ) h b' lam mu _ hl hm

/- English proof (translation)
Take `⟨-, h2, h3, h4⟩` from `GlobalTheory.T.permutation_matrix_properties K (Fin n) σ`. Set `e : ∀ c : Fin s', {i // (b' ∘ σ) i = c} ≃ {j // b' j = c}` to `fun c => σ.subtypeEquiv (p := fun i => (b' ∘ σ) i = c) (q := fun j => b' j = c) fun _ => Iff.rfl`. Establish `hf : (fun x => hcFun b' (fun c => (mu c).character) (pm K σ * x * (pm K σ)⁻¹)) = hcFun (b' ∘ σ) (fun c => (transp (e c).symm (mu c)).character)`. Use function extensionality and compare the values at `x`. Rewrite using `[h2, h4 s' b']`.

Use `congr 1`. Rewrite using `[hf, h3 s' b']`. Conclude with `ip_inter_eq_zero b (b' ∘ σ) lam hl _ (fun c => PI.GreenLabelSurjWork.transp_cusp _ _ (hm c)) h`.
-/
theorem term_split (σ : Equiv.Perm (Fin n)) (hl : ∀ c, IsCuspidal K (lam c))
    (hm : ∀ c, IsCuspidal K (mu c)) (h : ¬ ∀ i j, b i = b j ↔ b' (σ i) = b' (σ j)) :
    ip ((parab K b ⊓ cj (pm K σ) (parab K b') : Subgroup (GL (Fin n) K)) : Set (GL (Fin n) K))
      (hcFun b fun c => (lam c).character)
      (fun x => hcFun b' (fun c => (mu c).character) (pm K σ * x * (pm K σ)⁻¹)) = 0 := by
  obtain ⟨-, h2, h3, h4⟩ := GlobalTheory.T.permutation_matrix_properties K (Fin n) σ
  let e : ∀ c : Fin s', {i // (b' ∘ σ) i = c} ≃ {j // b' j = c} := fun c =>
    σ.subtypeEquiv (p := fun i => (b' ∘ σ) i = c) (q := fun j => b' j = c) fun _ => Iff.rfl
  have hf : (fun x => hcFun b' (fun c => (mu c).character) (pm K σ * x * (pm K σ)⁻¹)) =
      hcFun (b' ∘ σ) (fun c => (transp (e c).symm (mu c)).character) := by
    funext x
    rw [h2, h4 s' b']
    congr 1
  rw [hf, h3 s' b']
  exact ip_inter_eq_zero b (b' ∘ σ) lam hl _
    (fun c => PI.GreenLabelSurjWork.transp_cusp _ _ (hm c)) h

/- English proof (translation)
Set `f : ∀ c : Fin s, {i // b i = c} ≃ {j // π.symm (b' j) = c}` to `fun c => (h c).choose.trans (Equiv.subtypeEquivRight fun j => (π.symm_apply_eq).symm)`. Use `⟨Equiv.ofFiberEquiv f, funext fun i => ?_⟩` and prove the remaining obligations. Use `Equiv.ofFiberEquiv_map f i` as an intermediate fact. Simplify using `only [Function.comp_apply]`. Rewrite using `[← this, Equiv.apply_symm_apply]`.
-/
theorem exists_perm_of_cuspIso (π : Fin s ≃ Fin s') (h : ∀ c, CuspIso K (lam c) (mu (π c))) :
    ∃ σ : Equiv.Perm (Fin n), b' ∘ σ = π ∘ b := by
  let f : ∀ c : Fin s, {i // b i = c} ≃ {j // π.symm (b' j) = c} := fun c =>
    (h c).choose.trans (Equiv.subtypeEquivRight fun j => (π.symm_apply_eq).symm)
  refine ⟨Equiv.ofFiberEquiv f, funext fun i => ?_⟩
  have := Equiv.ofFiberEquiv_map f i
  simp only [Function.comp_apply]
  rw [← this, Equiv.apply_symm_apply]

end Terms

end GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal

open GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal in

/- English proof (translation)
Introduce `K _ _ _ n s s' b b' lam mu hb hb' hl hm`. Set `R : Type` to `{π : Fin s ≃ Fin s' // ∃ σ : Equiv.Perm (Fin n), b' ∘ σ = π ∘ b}`. Set `sig : R → Equiv.Perm (Fin n)` to `fun r => r.2.choose`. Establish `hsig : ∀ r : R, b' ∘ sig r = r.1 ∘ b` using `fun r => r.2.choose_spec`. Take `⟨hA, hAc⟩` from `GlobalTheory.T.harish_chandra_character K (Fin n) s b lam`.

Take `⟨hB, hBc⟩` from `GlobalTheory.T.harish_chandra_character K (Fin n) s' b' mu`. Establish `hcl : ∀ x g : GL (Fin n) K, (hcRep K b' mu).character (x * g * x⁻¹) = (hcRep K b' mu).character g`. Introduce `x g`. Simplify using `only [Representation.character, map_mul]`. Rewrite using `[LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]`.

Establish `hdist : ∀ r r' : R, (∃ β ∈ parab K b', ∃ α ∈ parab K b, pm K (sig r') = β * pm K (sig r) * α) → r = r'`. Introduce and unpack `r r' ⟨β, hβ, α, hα, he⟩`. Establish `hu` using `GlobalTheory.T.bruhat_decomposition_unique K (Fin n) s s' b b' (sig r) (sig r') ⟨β, hβ, α, hα, he⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Equiv.ext` to reduce the goal to its premises.

Introduce `c`. Take `⟨i0, hi0⟩` from `hb c`. Establish `hne : Nonempty {i // b i = c ∧ b' (sig r i) = r.1 c}` using `⟨⟨i0, hi0, by rw [← hi0]; exact congrFun (hsig r) i0⟩⟩`. Establish `pos` using `Fintype.card_pos_iff.2 hne`. Rewrite `pos` using `[hu c (r.1 c)]`.

Take `⟨⟨i, hi, hi'⟩⟩` from `Fintype.card_pos_iff.1 pos`. Establish `h1` using `congrFun (hsig r') i`. Simplify using `only [Function.comp_apply] at h1`. Rewrite `h1` using `[hi', hi]`. Conclude with `h1`.

Establish `hcover : ∀ x : GL (Fin n) K, (∃ r : R, ∃ β ∈ parab K b', ∃ α ∈ parab K b, x = β * pm K (sig r) * α) ∨ ∃ y, (∃ β ∈ parab K b', ∃ α ∈ parab K b, x = β * y * α) ∧ ip ((parab K b ⊓ cj y (parab K b') : Subgroup (GL (Fin n) K)) : Set (GL (Fin n) K)) (hcFun b fun c => (lam c).character) …`. Introduce `x`. Take `⟨σ, β, hβ, α, hα, rfl⟩` from `(GlobalTheory.T.bruhat_decomposition_two_blocks K n).1 s s' b b' x`. Distinguish the cases in `hf : ∀ i j, b i = b j ↔ b' (σ i) = b' (σ j)`. Use `left`.

Take `⟨π, hπ⟩` from `exists_equiv_of_fibres b (b' ∘ σ) hb (hb'.comp σ.surjective) hf`. Set `r : R` to `⟨π, σ, hπ⟩`. Use `⟨r, β * pm K (σ * (sig r)⁻¹), mul_mem hβ (pm_mem_parab b' _ fun i => ?_), α, hα, ?_⟩` and prove the remaining obligations. Establish `h1` using `congrFun hπ ((sig r)⁻¹ i)`. Establish `h2` using `congrFun (hsig r) ((sig r)⁻¹ i)`.

Establish `h3 : sig r ((sig r)⁻¹ i) = i` using `by simp`. Simplify using `only [Function.comp_apply] at h1 h2`. Rewrite `h2` using `[h3]`. Rewrite using `[Equiv.Perm.mul_apply, h1]`. Conclude with `h2.symm`.

Rewrite using `[pm_mul, ← pm_inv] group`. Use `right`. Conclude with `⟨pm K σ, ⟨β, hβ, α, hα, rfl⟩, term_split b b' lam mu σ (fun c => (hl c).2) (fun c => (hm c).2) hf⟩`. Apply `Nat.cast_injective (R := ℂ)` to reduce the goal to its premises. Rewrite using `[GlobalTheory.T.intertwiner_inner_product (GL (Fin n) K) _ _ (hcRep K b lam) (hcRep K b' mu), hA, (GlobalTheory.T.frobenius_reciprocity_inner_product (GL (Fin n) K) (parab K b) _ _ hcl).1, hB, GlobalTheory.T.mackey_inner_product (GL (Fin n) K) (parab K b) (parab K b') _ _ hAc hBc …`.

Establish `hterm : ∀ r : R, ip ((parab K b ⊓ cj (pm K (sig r)) (parab K b') : Subgroup (GL (Fin n) K)) : Set (GL (Fin n) K)) (hcFun b fun c => (lam c).character) (fun x => hcFun b' (fun c => (mu c).character) (pm K (sig r) * x * (pm K (sig r))⁻¹)) = if ∀ c, CuspIso K (lam c) (mu (r.1 c)) th …` using `fun r => term_same b b' lam mu (sig r) r.1 (hsig r) (fun c => (hl c).1) (fun c => (hm c).1)`. Rewrite using `[Finset.sum_congr rfl fun r _ => hterm r, Finset.sum_boole]`. Use `congr 1`. Rewrite using `[← Fintype.card_subtype, ← Nat.card_eq_fintype_card]`. Conclude with `Nat.card_congr ⟨fun r => ⟨r.1.1, r.2⟩, fun p => ⟨⟨p.1, exists_perm_of_cuspIso b b' lam mu p.1 p.2⟩, p.2⟩, fun _ => rfl, fun _ => rfl⟩`.
-/
theorem GlobalTheory.CompanionTheory.TyFin.mackeyAll : ReciprocityTheory.Ty.Fin.St.MackeyAll := by
  intro K _ _ _ n s s' b b' lam mu hb hb' hl hm
  classical
  let R : Type := {π : Fin s ≃ Fin s' // ∃ σ : Equiv.Perm (Fin n), b' ∘ σ = π ∘ b}
  let sig : R → Equiv.Perm (Fin n) := fun r => r.2.choose
  have hsig : ∀ r : R, b' ∘ sig r = r.1 ∘ b := fun r => r.2.choose_spec
  obtain ⟨hA, hAc⟩ := GlobalTheory.T.harish_chandra_character K (Fin n) s b lam
  obtain ⟨hB, hBc⟩ := GlobalTheory.T.harish_chandra_character K (Fin n) s' b' mu
  have hcl : ∀ x g : GL (Fin n) K, (hcRep K b' mu).character (x * g * x⁻¹) =
      (hcRep K b' mu).character g := by
    intro x g
    simp only [Representation.character, map_mul]
    rw [LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hdist : ∀ r r' : R, (∃ β ∈ parab K b', ∃ α ∈ parab K b,
      pm K (sig r') = β * pm K (sig r) * α) → r = r' := by
    rintro r r' ⟨β, hβ, α, hα, he⟩
    have hu := GlobalTheory.T.bruhat_decomposition_unique K (Fin n) s s' b b' (sig r) (sig r') ⟨β, hβ, α, hα, he⟩
    apply Subtype.ext
    apply Equiv.ext
    intro c
    obtain ⟨i0, hi0⟩ := hb c
    have hne : Nonempty {i // b i = c ∧ b' (sig r i) = r.1 c} :=
      ⟨⟨i0, hi0, by rw [← hi0]; exact congrFun (hsig r) i0⟩⟩
    have pos := Fintype.card_pos_iff.2 hne
    rw [hu c (r.1 c)] at pos
    obtain ⟨⟨i, hi, hi'⟩⟩ := Fintype.card_pos_iff.1 pos
    have h1 := congrFun (hsig r') i
    simp only [Function.comp_apply] at h1
    rw [hi', hi] at h1
    exact h1
  have hcover : ∀ x : GL (Fin n) K, (∃ r : R, ∃ β ∈ parab K b', ∃ α ∈ parab K b,
        x = β * pm K (sig r) * α) ∨
      ∃ y, (∃ β ∈ parab K b', ∃ α ∈ parab K b, x = β * y * α) ∧
        ip ((parab K b ⊓ cj y (parab K b') : Subgroup (GL (Fin n) K)) : Set (GL (Fin n) K))
          (hcFun b fun c => (lam c).character)
          (fun h => hcFun b' (fun c => (mu c).character) (y * h * y⁻¹)) = 0 := by
    intro x
    obtain ⟨σ, β, hβ, α, hα, rfl⟩ := (GlobalTheory.T.bruhat_decomposition_two_blocks K n).1 s s' b b' x
    by_cases hf : ∀ i j, b i = b j ↔ b' (σ i) = b' (σ j)
    · left
      obtain ⟨π, hπ⟩ := exists_equiv_of_fibres b (b' ∘ σ) hb (hb'.comp σ.surjective) hf
      let r : R := ⟨π, σ, hπ⟩
      refine ⟨r, β * pm K (σ * (sig r)⁻¹), mul_mem hβ (pm_mem_parab b' _ fun i => ?_), α, hα, ?_⟩
      · have h1 := congrFun hπ ((sig r)⁻¹ i)
        have h2 := congrFun (hsig r) ((sig r)⁻¹ i)
        have h3 : sig r ((sig r)⁻¹ i) = i := by simp
        simp only [Function.comp_apply] at h1 h2
        rw [h3] at h2
        rw [Equiv.Perm.mul_apply, h1]
        exact h2.symm
      · rw [pm_mul, ← pm_inv]
        group
    · right
      exact ⟨pm K σ, ⟨β, hβ, α, hα, rfl⟩, term_split b b' lam mu σ (fun c => (hl c).2)
        (fun c => (hm c).2) hf⟩
  apply Nat.cast_injective (R := ℂ)
  rw [GlobalTheory.T.intertwiner_inner_product (GL (Fin n) K) _ _ (hcRep K b lam) (hcRep K b' mu), hA,
    (GlobalTheory.T.frobenius_reciprocity_inner_product (GL (Fin n) K) (parab K b) _ _ hcl).1, hB,
    GlobalTheory.T.mackey_inner_product (GL (Fin n) K) (parab K b) (parab K b') _ _ hAc hBc R
      (fun r => pm K (sig r)) hdist hcover]
  have hterm : ∀ r : R, ip ((parab K b ⊓ cj (pm K (sig r)) (parab K b') :
      Subgroup (GL (Fin n) K)) : Set (GL (Fin n) K))
      (hcFun b fun c => (lam c).character)
      (fun x => hcFun b' (fun c => (mu c).character) (pm K (sig r) * x * (pm K (sig r))⁻¹)) =
      if ∀ c, CuspIso K (lam c) (mu (r.1 c)) then 1 else 0 := fun r =>
    term_same b b' lam mu (sig r) r.1 (hsig r) (fun c => (hl c).1) (fun c => (hm c).1)
  rw [Finset.sum_congr rfl fun r _ => hterm r, Finset.sum_boole]
  congr 1
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr ⟨fun r => ⟨r.1.1, r.2⟩,
    fun p => ⟨⟨p.1, exists_perm_of_cuspIso b b' lam mu p.1 p.2⟩, p.2⟩, fun _ => rfl, fun _ => rfl⟩
