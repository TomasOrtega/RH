import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Finset Equiv

noncomputable section

namespace GlobalTheory.CompanionTheory.CapelliBlocks

open Formalism.REAL CompanionTheory.D.DSIC

/- English proof (translation)
Take `rfl : m = n` from `Fin.equiv_iff_eq.mp ⟨τ⟩`. Establish `hr` using `qSkewRow A m m E id (τ : Fin m → Fin m) τ u`. Establish `hc` using `qSkewCol A m m E hE id id τ u`. Simplify using `only [Function.id_comp] at hr hc`. Rewrite using `[hr, hc, ← mul_assoc, ← Int.cast_mul, qdet]`.

Establish `: ((Perm.sign τ : ℤˣ) : ℤ) * (Perm.sign τ : ℤˣ) = 1`. Rewrite using `[← Units.val_mul, Int.units_mul_self, Units.val_one]`. Rewrite using `[this, Int.cast_one, one_mul]`.
-/
theorem qminor_equiv {A : Type} [Ring A] [Algebra ℂ A] {m n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (τ : Fin m ≃ Fin n) (u : ℂ) : qminor E τ τ u = qdet E u := by
  obtain rfl : m = n := Fin.equiv_iff_eq.mp ⟨τ⟩
  have hr := qSkewRow A m m E id (τ : Fin m → Fin m) τ u
  have hc := qSkewCol A m m E hE id id τ u
  simp only [Function.id_comp] at hr hc
  rw [hr, hc, ← mul_assoc, ← Int.cast_mul, qdet]
  have : ((Perm.sign τ : ℤˣ) : ℤ) * (Perm.sign τ : ℤˣ) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  rw [this, Int.cast_one, one_mul]

/- English proof (translation)
Rewrite using `[qminor, ← (finSumFinEquiv (m := q) (n := p)).permCongr.sum_comp]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Perm.sign_permCongr, List.ofFn_add, List.prod_append]`. Use `congr 4`. Use function extensionality and compare the values at `k`.

Establish `: (Fin.castLE (Nat.le_add_right q p) k) = Fin.castAdd p k` using `rfl`. Simplify using `[this]`. Use function extensionality and compare the values at `k`. Simplify using `[sub_sub]`.
-/
theorem qminor_sum {A : Type} [Ring A] [Algebra ℂ A] {n q p : ℕ} (E : Fin n → Fin n → A)
    (r : Fin q ⊕ Fin p → Fin n) (u : ℂ) :
    qminor E (r ∘ finSumFinEquiv.symm) (r ∘ finSumFinEquiv.symm) u =
      ∑ σ : Perm (Fin q ⊕ Fin p), ((Perm.sign σ : ℤ) : A) *
        ((List.ofFn fun k : Fin q => Tm E (u - (k : ℂ)) (r (σ (Sum.inl k))) (r (Sum.inl k))).prod *
         (List.ofFn fun k : Fin p => Tm E (u - (q : ℂ) - (k : ℂ)) (r (σ (Sum.inr k))) (r (Sum.inr k))).prod) := by
  rw [qminor, ← (finSumFinEquiv (m := q) (n := p)).permCongr.sum_comp]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Perm.sign_permCongr, List.ofFn_add, List.prod_append]
  congr 4
  · funext k
    have : (Fin.castLE (Nat.le_add_right q p) k) = Fin.castAdd p k := rfl
    simp [this]
  · funext k
    simp [sub_sub]

/- English proof (translation)
The claim follows from `| [], _, h, _ => by simp at h | T :: l, h1, h2, v => by rw [List.prod_cons, Module.End.mul_apply] obtain ⟨S, hS, hS'⟩ := h2 rcases List.mem_cons.mp hS with rfl | hS · exact hS' _ · exact h1 T List.mem_cons_self _ (prod_mem P l (fun T hT => h1 T (List.mem_cons_of_mem _ hT)) ⟨S, hS …`.
-/
theorem prod_mem {V : Type} [AddCommGroup V] [Module ℂ V] (P : Submodule ℂ V) :
    ∀ l : List (Module.End ℂ V), (∀ T ∈ l, ∀ v ∈ P, T v ∈ P) → (∃ T ∈ l, ∀ v, T v ∈ P) → ∀ v, l.prod v ∈ P
  | [], _, h, _ => by simp at h
  | T :: l, h1, h2, v => by
    rw [List.prod_cons, Module.End.mul_apply]
    obtain ⟨S, hS, hS'⟩ := h2
    rcases List.mem_cons.mp hS with rfl | hS
    · exact hS' _
    · exact h1 T List.mem_cons_self _
        (prod_mem P l (fun T hT => h1 T (List.mem_cons_of_mem _ hT)) ⟨S, hS, hS'⟩ v)

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def pplus (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) : Submodule ℂ V where
  carrier := {v | ∃ w : NC ε → V, v = ∑ i : NC ε, E i.1.1 i.1.2 (w i)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨w, rfl⟩ ⟨w', rfl⟩
    exact ⟨w + w', by simp [Finset.sum_add_distrib]⟩
  smul_mem' := by
    rintro c _ ⟨w, rfl⟩
    exact ⟨c • w, by simp [Finset.smul_sum]⟩

/- English proof (translation)
Use `⟨Pi.single (⟨(a, b), ha, hb⟩ : NC ε) v, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single (⟨(a, b), ha, hb⟩ : NC ε)]`. Simplify using the standard rewrite rules. Introduce `i _ hi`. Simplify using `[Pi.single_eq_of_ne hi]`.

Simplify using the standard rewrite rules.
-/
theorem mem_pplus (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) {a b : Fin n}
    (ha : ε a = true) (hb : ε b = false) (v : V) : E a b v ∈ pplus ε E := by
  classical
  refine ⟨Pi.single (⟨(a, b), ha, hb⟩ : NC ε) v, ?_⟩
  rw [Finset.sum_eq_single (⟨(a, b), ha, hb⟩ : NC ε)]
  · simp
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · simp

/- English proof (translation)
Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨⟨a, b⟩, ha, hb⟩` from `i`. Simplify using `only at ha hb ⊢`.

Generalize the expression as in `w _ = x`. Establish `h` using `LinearMap.congr_fun (hE c d a b) x`. Establish `hda : d ≠ a` using `by rintro rfl; simp [ha] at hd`. Rewrite `h` using `[if_neg hda, zero_sub, LinearMap.sub_apply, sub_eq_iff_eq_add, LinearMap.neg_apply, Module.End.mul_apply, Module.End.mul_apply]`. Rewrite using `[h]`.

Use `Submodule.add_mem _ (Submodule.neg_mem _ ?_) (mem_pplus ε E ha hb _)` and prove the remaining obligations. Use `split_ifs`. Conclude with `mem_pplus ε E ha hd _`. Simplify using the standard rewrite rules.
-/
theorem stab_pplus (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) {c d : Fin n}
    (hc : ε c = false) (hd : ε d = false) : ∀ v ∈ pplus ε E, E c d v ∈ pplus ε E := by
  rintro _ ⟨w, rfl⟩
  rw [map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨⟨a, b⟩, ha, hb⟩ := i
  dsimp only at ha hb ⊢
  generalize w _ = x
  have h := LinearMap.congr_fun (hE c d a b) x
  have hda : d ≠ a := by rintro rfl; simp [ha] at hd
  rw [if_neg hda, zero_sub, LinearMap.sub_apply, sub_eq_iff_eq_add, LinearMap.neg_apply,
    Module.End.mul_apply, Module.End.mul_apply] at h
  rw [h]
  refine Submodule.add_mem _ (Submodule.neg_mem _ ?_) (mem_pplus ε E ha hb _)
  split_ifs
  · exact mem_pplus ε E ha hd _
  · simp

/- English proof (translation)
Establish `hab : a ≠ b` using `by rintro rfl; simp [ha] at hb`. Rewrite using `[Tm, if_neg hab, zero_add]`. Conclude with `mem_pplus ε E ha hb v`.
-/
theorem Tm_mem (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) {a b : Fin n}
    (ha : ε a = true) (hb : ε b = false) (u : ℂ) (v : V) : Tm E u a b v ∈ pplus ε E := by
  have hab : a ≠ b := by rintro rfl; simp [ha] at hb
  rw [Tm, if_neg hab, zero_add]
  exact mem_pplus ε E ha hb v

/- English proof (translation)
Introduce `v hv`. Consider the cases of `ha : ε a`. Rewrite using `[Tm, LinearMap.add_apply]`. Use `Submodule.add_mem _ ?_ (stab_pplus ε E hE ha hb v hv)` and prove the remaining obligations. Use `split_ifs`.

Rewrite using `[Module.algebraMap_end_apply]`. Conclude with `Submodule.smul_mem _ _ hv`. Simplify using the standard rewrite rules. Conclude with `Tm_mem ε E ha hb u v`.
-/
theorem Tm_stab (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (a : Fin n) {b : Fin n}
    (hb : ε b = false) (u : ℂ) : ∀ v ∈ pplus ε E, Tm E u a b v ∈ pplus ε E := by
  intro v hv
  cases ha : ε a
  · rw [Tm, LinearMap.add_apply]
    refine Submodule.add_mem _ ?_ (stab_pplus ε E hE ha hb v hv)
    split_ifs
    · rw [Module.algebraMap_end_apply]
      exact Submodule.smul_mem _ _ hv
    · simp
  · exact Tm_mem ε E ha hb u v

/- English proof (translation)
Rewrite using `[qminor_sum]`. Use `set f : Perm (Fin q ⊕ Fin p) → Module.End ℂ V := fun σ => ((Perm.sign σ : ℤ) : Module.End ℂ V) * ((List.ofFn fun k : Fin q => Tm E (u - (k : ℂ)) (r (σ (Sum.inl k))) (r (Sum.inl k))).prod * (List.ofFn fun k : Fin p => Tm E (u - (q : ℂ) - (k : ℂ)) (r (σ (Sum.inr k))) (r (Sum.inr k) …`. Use `set s : Finset (Perm (Fin q ⊕ Fin p)) := univ.image fun σ : Perm (Fin q) × Perm (Fin p) => Perm.sumCongrHom _ _ σ with hs`. Establish `h1 : qminor E (r ∘ Sum.inl) (r ∘ Sum.inl) u * qminor E (r ∘ Sum.inr) (r ∘ Sum.inr) (u - (q : ℂ)) = ∑ σ ∈ s, f σ`. Rewrite using `[hs, Finset.sum_image (fun x _ y _ h => Perm.sumCongrHom_injective h), qminor, qminor, Finset.sum_mul_sum, Fintype.sum_prod_type]`.

Use `Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Simplify using `only [hf, Perm.sumCongrHom_apply, Perm.sign_sumCongr, Units.val_mul, Int.cast_mul, Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr, Function.comp_apply, mul_assoc]`. Use `congr 1`. Rewrite using `[← mul_assoc, ← (Int.cast_commute _ _).eq, mul_assoc]`. Rewrite using `[h1, ← Finset.sum_add_sum_compl s, LinearMap.add_apply, add_sub_cancel_left, LinearMap.sum_apply]`.

Use `Submodule.sum_mem _ fun σ hσ => ?_` and prove the remaining obligations. Establish `h2 : ∃ k j, σ (Sum.inl k) = Sum.inr j`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `Finset.mem_compl.mp hσ` to reduce the goal to its premises.

Establish `: σ ∈ (Perm.sumCongrHom (Fin q) (Fin p)).range`. Apply `Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl` to reduce the goal to its premises. Introduce and unpack `_ ⟨k, rfl⟩`. Consider the cases of `h : σ (Sum.inl k) with`. Consider the case `inl j => exact ⟨j, rfl⟩`.

Consider the case `inr j => exact absurd h (hcon k j)`. Take `⟨τ, hτ⟩` from `this`. Conclude with `Finset.mem_image.mpr ⟨τ, Finset.mem_univ _, hτ⟩`. Take `⟨k, j, hkj⟩` from `h2`. Simplify using `only [hf, Module.End.mul_apply, Module.End.intCast_apply]`.

Use `Submodule.smul_of_tower_mem _ _ (prod_mem _ _ ?_ ?_ _)` and prove the remaining obligations. Introduce `T hT`. Take `⟨i, rfl⟩` from `List.mem_ofFn.mp hT`. Conclude with `Tm_stab ε E hE _ (hl i) _`. Use `⟨_, List.mem_ofFn.mpr ⟨k, rfl⟩, fun v => Tm_mem ε E ?_ (hl k) _ v⟩` and prove the remaining obligations.

Rewrite using `[hkj]`. Conclude with `hr j`.
-/
theorem block_mem (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) {q p : ℕ}
    (r : Fin q ⊕ Fin p → Fin n) (hl : ∀ k, ε (r (Sum.inl k)) = false) (hr : ∀ k, ε (r (Sum.inr k)) = true)
    (u : ℂ) (v : V) :
    qminor E (r ∘ finSumFinEquiv.symm) (r ∘ finSumFinEquiv.symm) u v -
      (qminor E (r ∘ Sum.inl) (r ∘ Sum.inl) u * qminor E (r ∘ Sum.inr) (r ∘ Sum.inr) (u - (q : ℂ))) v ∈
        pplus ε E := by
  classical
  rw [qminor_sum]
  set f : Perm (Fin q ⊕ Fin p) → Module.End ℂ V := fun σ => ((Perm.sign σ : ℤ) : Module.End ℂ V) *
        ((List.ofFn fun k : Fin q => Tm E (u - (k : ℂ)) (r (σ (Sum.inl k))) (r (Sum.inl k))).prod *
         (List.ofFn fun k : Fin p => Tm E (u - (q : ℂ) - (k : ℂ)) (r (σ (Sum.inr k))) (r (Sum.inr k))).prod)
    with hf
  set s : Finset (Perm (Fin q ⊕ Fin p)) :=
    univ.image fun σ : Perm (Fin q) × Perm (Fin p) => Perm.sumCongrHom _ _ σ with hs
  have h1 : qminor E (r ∘ Sum.inl) (r ∘ Sum.inl) u * qminor E (r ∘ Sum.inr) (r ∘ Sum.inr) (u - (q : ℂ)) =
      ∑ σ ∈ s, f σ := by
    rw [hs, Finset.sum_image (fun x _ y _ h => Perm.sumCongrHom_injective h), qminor, qminor,
      Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    simp only [hf, Perm.sumCongrHom_apply, Perm.sign_sumCongr, Units.val_mul, Int.cast_mul,
      Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr, Function.comp_apply, mul_assoc]
    congr 1
    rw [← mul_assoc, ← (Int.cast_commute _ _).eq, mul_assoc]
  rw [h1, ← Finset.sum_add_sum_compl s, LinearMap.add_apply, add_sub_cancel_left, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun σ hσ => ?_
  have h2 : ∃ k j, σ (Sum.inl k) = Sum.inr j := by
    by_contra hcon
    push Not at hcon
    apply Finset.mem_compl.mp hσ
    have : σ ∈ (Perm.sumCongrHom (Fin q) (Fin p)).range := by
      apply Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
      rintro _ ⟨k, rfl⟩
      cases h : σ (Sum.inl k) with
      | inl j => exact ⟨j, rfl⟩
      | inr j => exact absurd h (hcon k j)
    obtain ⟨τ, hτ⟩ := this
    exact Finset.mem_image.mpr ⟨τ, Finset.mem_univ _, hτ⟩
  obtain ⟨k, j, hkj⟩ := h2
  simp only [hf, Module.End.mul_apply, Module.End.intCast_apply]
  refine Submodule.smul_of_tower_mem _ _ (prod_mem _ _ ?_ ?_ _)
  · intro T hT
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hT
    exact Tm_stab ε E hE _ (hl i) _
  · refine ⟨_, List.mem_ofFn.mpr ⟨k, rfl⟩, fun v => Tm_mem ε E ?_ (hl k) _ v⟩
    rw [hkj]
    exact hr j

/- English proof (translation)
Use `Finset.orderEmbOfFin_mem (univ.filter fun a => ε a = s) rfl k` as an intermediate fact. Conclude with `(Finset.mem_filter.mp this).2`.
-/
theorem blk_val (ε : Fin n → Bool) (s : Bool) (k : Fin (nb ε s)) : ε (blk ε s k) = s := by
  have := Finset.orderEmbOfFin_mem (univ.filter fun a => ε a = s) rfl k
  exact (Finset.mem_filter.mp this).2

/- English proof (translation)
Establish `hinj : ∀ s, Function.Injective (blk ε s)` using `fun s => ((univ.filter fun a => ε a = s).orderEmbOfFin rfl).injective`. Establish `hsur : ∀ a, ∃ k, blk ε (ε a) k = a` using `fun a => by`. Establish `: a ∈ Set.range ((univ.filter fun b => ε b = ε a).orderEmbOfFin rfl)`. Rewrite using `[Finset.range_orderEmbOfFin]`. Simplify using the standard rewrite rules.

Conclude with `this`. Prove the components needed by the constructor for the conclusion. Use `Function.Injective.sumElim (hinj false) (hinj true) fun a b h => ?_` and prove the remaining obligations. Establish `h1` using `blk_val ε false a`. Rewrite `h1` using `[h, blk_val ε true b]`.

Conclude with `absurd h1 (by simp)`. Introduce `a`. Establish `h` using `hsur a`. Consider the cases of `ha : ε a`. Rewrite `h` using `[ha]`.

Take `⟨k, hk⟩` from `h`. Conclude with `⟨Sum.inl k, hk⟩`. Rewrite `h` using `[ha]`. Take `⟨k, hk⟩` from `h`. Conclude with `⟨Sum.inr k, hk⟩`.
-/
theorem blk_bijective (ε : Fin n → Bool) : Function.Bijective (Sum.elim (blk ε false) (blk ε true)) := by
  have hinj : ∀ s, Function.Injective (blk ε s) := fun s =>
    ((univ.filter fun a => ε a = s).orderEmbOfFin rfl).injective
  have hsur : ∀ a, ∃ k, blk ε (ε a) k = a := fun a => by
    have : a ∈ Set.range ((univ.filter fun b => ε b = ε a).orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      simp
    exact this
  constructor
  · refine Function.Injective.sumElim (hinj false) (hinj true) fun a b h => ?_
    have h1 := blk_val ε false a
    rw [h, blk_val ε true b] at h1
    exact absurd h1 (by simp)
  · intro a
    have h := hsur a
    cases ha : ε a
    · rw [ha] at h
      obtain ⟨k, hk⟩ := h
      exact ⟨Sum.inl k, hk⟩
    · rw [ha] at h
      obtain ⟨k, hk⟩ := h
      exact ⟨Sum.inr k, hk⟩

/- English proof (translation)
Introduce `n ε V _ _ E hE u v`. Establish `h` using `block_mem ε E hE (Sum.elim (blk ε false) (blk ε true)) (blk_val ε false) (blk_val ε true) u v`. Establish `h2` using `qminor_equiv E hE (finSumFinEquiv.symm.trans (Equiv.ofBijective _ (blk_bijective ε))) u`. Rewrite using `[← h2]`. Conclude with `h`.
-/
theorem co0 : CompanionTheory.D.DSIC.CapelliDeterminantBlockProduct := by
  intro n ε V _ _ E hE u v
  have h := block_mem ε E hE (Sum.elim (blk ε false) (blk ε true)) (blk_val ε false) (blk_val ε true) u v
  have h2 := qminor_equiv E hE (finSumFinEquiv.symm.trans (Equiv.ofBijective _ (blk_bijective ε))) u
  rw [← h2]
  exact h

end GlobalTheory.CompanionTheory.CapelliBlocks
