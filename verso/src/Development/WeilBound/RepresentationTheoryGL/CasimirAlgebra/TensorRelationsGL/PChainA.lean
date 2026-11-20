import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace ChainP

section gen
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `[Module.End.intCast_apply]`.
-/
theorem intCast_comp (f : V →ₗ[ℂ] W) (z : ℤ) :
    f ∘ₗ ((z : Module.End ℂ V)) = ((z : Module.End ℂ W)) ∘ₗ f := by
  refine LinearMap.ext fun v => ?_
  simp [Module.End.intCast_apply]

/- English proof (translation)
Proceed by induction on `t with`. Consider the case `zero => refine LinearMap.ext fun v => ?_`. Simplify using the standard rewrite rules. Consider the case `succ t ih`. Rewrite using `[List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, h 0, LinearMap.comp_assoc, ih (fun k => A k.succ) (fun k => B k.succ) (fun k => h _), LinearMap.comp_assoc]`.
-/
theorem ofFn_comp (f : V →ₗ[ℂ] W) {t : ℕ} (A : Fin t → Module.End ℂ V) (B : Fin t → Module.End ℂ W)
    (h : ∀ k, f ∘ₗ A k = B k ∘ₗ f) : f ∘ₗ (List.ofFn A).prod = (List.ofFn B).prod ∘ₗ f := by
  induction t with
  | zero => refine LinearMap.ext fun v => ?_; simp
  | succ t ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_eq_comp,
      Module.End.mul_eq_comp, ← LinearMap.comp_assoc, h 0, LinearMap.comp_assoc,
      ih (fun k => A k.succ) (fun k => B k.succ) (fun k => h _), LinearMap.comp_assoc]

/- English proof (translation)
Unfold `qdet qminor`. Establish `key : ∀ σ : Equiv.Perm (Fin n), f ∘ₗ (((Equiv.Perm.sign σ : ℤ) : Module.End ℂ V) * (List.ofFn fun k : Fin n => Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod) = (((Equiv.Perm.sign σ : ℤ) : Module.End ℂ W) * (List.ofFn fun k : Fin n => Tm F (u - (k : ℂ)) (id (σ k)) (id k)).prod) ∘ₗ f` using `fun σ => by`. Rewrite using `[Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, intCast_comp,`. Use the proof step `LinearMap.comp_assoc, ofFn_comp f _ _ (fun k => ?_), LinearMap.comp_assoc]`. Simplify using `only [Tm]`.

Rewrite using `[LinearMap.comp_add, LinearMap.add_comp, h]`. Use `congr 1`. Use `split_ifs`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]`. Conclude with `Finset.sum_congr rfl fun σ _ => LinearMap.congr_fun (key σ) v`.
-/
theorem qdet_comp {n : ℕ} (f : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b, f ∘ₗ E a b = F a b ∘ₗ f) (u : ℂ) :
    f ∘ₗ qdet E u = qdet F u ∘ₗ f := by
  unfold qdet qminor
  have key : ∀ σ : Equiv.Perm (Fin n), f ∘ₗ (((Equiv.Perm.sign σ : ℤ) : Module.End ℂ V) *
      (List.ofFn fun k : Fin n => Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod) =
      (((Equiv.Perm.sign σ : ℤ) : Module.End ℂ W) *
      (List.ofFn fun k : Fin n => Tm F (u - (k : ℂ)) (id (σ k)) (id k)).prod) ∘ₗ f := fun σ => by
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, intCast_comp,
    LinearMap.comp_assoc, ofFn_comp f _ _ (fun k => ?_), LinearMap.comp_assoc]
    simp only [Tm]
    rw [LinearMap.comp_add, LinearMap.add_comp, h]
    congr 1
    split_ifs
    · refine LinearMap.ext fun v => ?_; simp
    · simp
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun σ _ => LinearMap.congr_fun (key σ) v

/- English proof (translation)
Establish `key : ∀ r : ℂ, f ∘ₗ (A - algebraMap ℂ _ r) = (B - algebraMap ℂ _ r) ∘ₗ f`. Introduce `r`. Use extensionality with `v`. Establish `hv` using `LinearMap.congr_fun h v`. Simplify using `only [LinearMap.comp_apply] at hv`.

Simplify using `[hv]`. Proceed by induction on `L with`. Consider the case `nil`. Use extensionality with `v`. Simplify using the standard rewrite rules.

Consider the case `cons r L ih`. Rewrite using `[List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, key r, LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc]`.
-/
theorem listSub_comp (f : V →ₗ[ℂ] W) (A : Module.End ℂ V) (B : Module.End ℂ W) (h : f ∘ₗ A = B ∘ₗ f)
    (L : List ℂ) :
    f ∘ₗ (L.map fun r => A - algebraMap ℂ _ r).prod = (L.map fun r => B - algebraMap ℂ _ r).prod ∘ₗ f := by
  have key : ∀ r : ℂ, f ∘ₗ (A - algebraMap ℂ _ r) = (B - algebraMap ℂ _ r) ∘ₗ f := by
    intro r
    ext v
    have hv := LinearMap.congr_fun h v
    simp only [LinearMap.comp_apply] at hv
    simp [hv]
  induction L with
  | nil =>
    ext v
    simp
  | cons r L ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
      Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, key r,
      LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc]

/- English proof (translation)
Apply `Commute.list_prod_left` to reduce the goal to its premises. Introduce `x hx`. Take `⟨r, -, rfl⟩` from `List.mem_map.1 hx`. Conclude with `h.sub_left (Algebra.commutes r T)`.
-/
theorem listSub_commute (A T : Module.End ℂ V) (h : Commute A T) (L : List ℂ) :
    Commute (L.map fun r => A - algebraMap ℂ _ r).prod T := by
  apply Commute.list_prod_left
  intro x hx
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 hx
  exact h.sub_left (Algebra.commutes r T)

/- English proof (translation)
Rewrite using `[List.pairwise_map]`. Conclude with `List.pairwise_of_forall fun r s => ((Commute.refl A).sub_left (Algebra.commutes r A)).sub_right (Algebra.commutes s _).symm`.
-/
theorem listSub_pairwise (A : Module.End ℂ V) (L : List ℂ) :
    (L.map fun r => A - algebraMap ℂ _ r).Pairwise Commute := by
  rw [List.pairwise_map]
  exact List.pairwise_of_forall fun r s =>
    ((Commute.refl A).sub_left (Algebra.commutes r A)).sub_right (Algebra.commutes s _).symm

/- English proof (translation)
Establish `hm : l c ∈ List.ofFn l` using `by simp`. Establish `h1 : ((List.ofFn l).map fun r => A - algebraMap ℂ (Module.End ℂ V) r).prod = 0`. Rewrite using `[List.map_ofFn]`. Conclude with `h0`. Rewrite `h1` using `[((List.perm_cons_erase hm).map _).prod_eq' (listSub_pairwise A _), List.map_cons, List.prod_cons]`.

Rewrite using `[(listSub_commute A _ ((Commute.refl A).sub_right (Algebra.commutes _ A).symm) _).eq]`. Conclude with `h1`.
-/
theorem listSub_kill (A : Module.End ℂ V) {n : ℕ} (l : Fin n → ℂ) (c : Fin n)
    (h0 : (List.ofFn fun k => A - algebraMap ℂ _ (l k)).prod = 0) :
    (((List.ofFn l).erase (l c)).map fun r => A - algebraMap ℂ _ r).prod * (A - algebraMap ℂ _ (l c)) = 0 := by
  have hm : l c ∈ List.ofFn l := by simp
  have h1 : ((List.ofFn l).map fun r => A - algebraMap ℂ (Module.End ℂ V) r).prod = 0 := by
    rw [List.map_ofFn]
    exact h0
  rw [((List.perm_cons_erase hm).map _).prod_eq' (listSub_pairwise A _), List.map_cons,
    List.prod_cons] at h1
  rw [(listSub_commute A _ ((Commute.refl A).sub_right (Algebra.commutes _ A).symm) _).eq]
  exact h1

/- English proof (translation)
Introduce `g hg`. Establish `hle : Algebra.adjoin ℂ s ≤ Subalgebra.centralizer ℂ {T}` using `Algebra.adjoin_le fun x hx => by`. Rewrite using `[SetLike.mem_coe, Subalgebra.mem_centralizer_iff]`. Introduce `y hy`. Rewrite using `[Set.mem_singleton_iff.1 hy]`.

Conclude with `(hs x hx).symm.eq`. Establish `h2` using `hle hg`. Rewrite `h2` using `[Subalgebra.mem_centralizer_iff]`. Conclude with `(h2 T (Set.mem_singleton T)).symm`.
-/
theorem adjoin_commute {A : Type} [Ring A] [Algebra ℂ A] (s : Set A) (T : A) (hs : ∀ x ∈ s, Commute x T) :
    ∀ g ∈ Algebra.adjoin ℂ s, Commute g T := by
  intro g hg
  have hle : Algebra.adjoin ℂ s ≤ Subalgebra.centralizer ℂ {T} :=
    Algebra.adjoin_le fun x hx => by
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact (hs x hx).symm.eq
  have h2 := hle hg
  rw [Subalgebra.mem_centralizer_iff] at h2
  exact (h2 T (Set.mem_singleton T)).symm

end gen

end ChainP

end PositivityTheory.Rg.Cz

end
