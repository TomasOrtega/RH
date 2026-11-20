import Mathlib

namespace BaseChangeColon.BC

open MvPolynomial

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `g hg`. Rewrite `hg` using `[Submodule.mem_colon_singleton, smul_eq_mul]`. Take `⟨n, c, t, ht⟩` from `Submodule.mem_span_set'.1 hg`. Use `choose j hj hj' using fun i => (t i).2`.

Establish `hrel : ∑ o : Option (Fin n), (o.elim x fun i => -j i) • (o.elim g c : R') = 0`. Rewrite using `[Fintype.sum_option]`. Simplify using `only [Option.elim, Algebra.smul_def, map_neg, neg_mul, Finset.sum_neg_distrib]`. Rewrite using `[mul_comm, ← ht, add_neg_eq_zero]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hj', smul_eq_mul, mul_comm]`. Take `⟨k, a, y, h1, h2⟩` from `Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := R') (f := fun o : Option (Fin n) => o.elim x fun i => -j i) (x := fun o => o.elim g c) hrel`. Establish `hg' : g = ∑ l, a none l • y l` using `h1 none`. Rewrite using `[hg']`. Use `Ideal.sum_mem _ fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[Algebra.smul_def]`. Use `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)` and prove the remaining obligations. Rewrite using `[Submodule.mem_colon_singleton, smul_eq_mul]`. Establish `h3` using `h2 l`. Rewrite `h3` using `[Fintype.sum_option]`.

Simplify using `only [Option.elim, neg_mul, Finset.sum_neg_distrib, add_neg_eq_zero] at h3`. Rewrite using `[mul_comm, h3]`. Conclude with `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hj i)`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `y hy`.

Rewrite `hy` using `[Submodule.mem_colon_singleton, smul_eq_mul]`. Rewrite using `[Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul, ← map_mul]`. Conclude with `Ideal.mem_map_of_mem _ hy`.
-/
theorem flat_colon {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R']
    (I : Ideal R) (x : R) :
    (I.map (algebraMap R R')).colon {algebraMap R R' x} = (I.colon {x}).map (algebraMap R R') := by
  apply le_antisymm
  · intro g hg
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hg
    obtain ⟨n, c, t, ht⟩ := Submodule.mem_span_set'.1 hg
    choose j hj hj' using fun i => (t i).2
    have hrel : ∑ o : Option (Fin n), (o.elim x fun i => -j i) • (o.elim g c : R') = 0 := by
      rw [Fintype.sum_option]
      simp only [Option.elim, Algebra.smul_def, map_neg, neg_mul, Finset.sum_neg_distrib]
      rw [mul_comm, ← ht, add_neg_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hj', smul_eq_mul, mul_comm]
    obtain ⟨k, a, y, h1, h2⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := R')
      (f := fun o : Option (Fin n) => o.elim x fun i => -j i) (x := fun o => o.elim g c) hrel
    have hg' : g = ∑ l, a none l • y l := h1 none
    rw [hg']
    refine Ideal.sum_mem _ fun l _ => ?_
    rw [Algebra.smul_def]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [Submodule.mem_colon_singleton, smul_eq_mul]
    have h3 := h2 l
    rw [Fintype.sum_option] at h3
    simp only [Option.elim, neg_mul, Finset.sum_neg_distrib, add_neg_eq_zero] at h3
    rw [mul_comm, h3]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hj i)
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hy
    rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul, ← map_mul]
    exact Ideal.mem_map_of_mem _ hy

attribute [local instance] MvPolynomial.algebraMvPolynomial

/- English proof (translation)
Establish `hb` using `(inferInstance : Algebra.IsPushout O (MvPolynomial σ O) O' (MvPolynomial σ O')).out`. Use `haveI : Module.Flat (MvPolynomial σ O) (MvPolynomial σ O') := Module.Flat.isBaseChange O (MvPolynomial σ O) O' (MvPolynomial σ O') hb`. Conclude with `flat_colon (R' := MvPolynomial σ O') I x`.
-/
theorem map_colon {O O' σ : Type} [CommRing O] [CommRing O'] [Algebra O O'] [Module.Flat O O']
    (I : Ideal (MvPolynomial σ O)) (x : MvPolynomial σ O) :
    (I.map (MvPolynomial.map (algebraMap O O'))).colon {MvPolynomial.map (algebraMap O O') x} =
      (I.colon {x}).map (MvPolynomial.map (algebraMap O O')) := by
  have hb := (inferInstance :
    Algebra.IsPushout O (MvPolynomial σ O) O' (MvPolynomial σ O')).out
  haveI : Module.Flat (MvPolynomial σ O) (MvPolynomial σ O') :=
    Module.Flat.isBaseChange O (MvPolynomial σ O) O' (MvPolynomial σ O') hb
  exact flat_colon (R' := MvPolynomial σ O') I x

/- English proof (translation)
Use `set J' := J.map (MvPolynomial.map (algebraMap O O')) with hJ'`. Use `set m : Ideal O := Ideal.span {ϖ} with hmdef`. Use `letI : Field (O ⧸ m) := Ideal.Quotient.field m`. Establish `hle : m ≤ J.comap (algebraMap O (MvPolynomial σ O))`. Rewrite using `[hmdef, Ideal.span_le, Set.singleton_subset_iff]`.

Conclude with `hJ`. Use `letI : Algebra (O ⧸ m) (MvPolynomial σ O ⧸ J) := Ideal.Quotient.algebraQuotientOfLEComap hle`. Use `haveI : IsScalarTower O (O ⧸ m) (MvPolynomial σ O ⧸ J) := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Take `⟨ι, ⟨b⟩⟩ : ∃ ι : Type, Nonempty (Module.Basis ι (O ⧸ m) (MvPolynomial σ O ⧸ J))` from `⟨_, ⟨Module.Basis.ofVectorSpace _ _⟩⟩`. Establish `hb` using `(inferInstance : Algebra.IsPushout O O' (MvPolynomial σ O) (MvPolynomial σ O')).out`.

Use `set m' : Ideal O' := Ideal.span {algebraMap O O' ϖ} with hm'`. Establish `hle' : m ≤ m'.comap (Algebra.ofId O O')`. Rewrite using `[hmdef, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `Ideal.mem_span_singleton_self _`. Set `ι0 : (O ⧸ m) →ₐ[O] (O' ⧸ m')` to `Ideal.quotientMapₐ m' (Algebra.ofId O O') hle'`.

Set `lam : ι → (MvPolynomial σ O →ₗ[O] (O' ⧸ m'))` to `fun i => ι0.toLinearMap ∘ₗ ((b.coord i).restrictScalars O) ∘ₗ (Ideal.Quotient.mkₐ O J).toLinearMap`. Establish `hlam : ∀ i s, lam i s = ι0 (b.coord i (Ideal.Quotient.mk J s))` using `fun _ _ => rfl`. Set `Λ : ι → (MvPolynomial σ O' →ₗ[O'] (O' ⧸ m'))` to `fun i => hb.lift (lam i)`. Establish `hΛ : ∀ i s, Λ i (MvPolynomial.map (algebraMap O O') s) = lam i s` using `fun i s => hb.lift_eq (lam i) s`. Establish `hkill : ∀ i, ∀ w ∈ J', Λ i w = 0`.

Introduce `i w hw`. It suffices to establish `h : ∀ h, Λ i (h * w) = 0 by simpa using h 1`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨s, hs, rfl⟩` from `hx`.

Introduce `h`. Proceed by induction on `h using hb.inductionOn with`. Consider the case `zero => simp`. Consider the case `tmul t`. Express the relevant statement in the definitionally equal form `Λ i (MvPolynomial.map (algebraMap O O') t * _) = 0`.

Rewrite using `[← map_mul, hΛ, hlam, Ideal.Quotient.eq_zero_iff_mem.2 (J.mul_mem_left t hs)]`. Simplify using the standard rewrite rules. Consider the case `smul a t ht => rw [smul_mul_assoc, map_smul, ht, smul_zero]`. Consider the case `add a t ha ht => rw [add_mul, map_add, ha, ht, add_zero]`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => intro h`. Rewrite using `[mul_add, map_add, hx, hy, add_zero]`. Consider the case `smul a x _ hx => intro h`. Rewrite using `[smul_eq_mul, ← mul_assoc, hx]`. Use `choose B hB using fun i => Ideal.Quotient.mk_surjective (I := J) (b i)`.

Set `U : Submodule O' (MvPolynomial σ O')` to `Submodule.span O' (Set.range fun i => MvPolynomial.map (algebraMap O O') (B i)) ⊔ J'.restrictScalars O'`. Establish `hJU : ∀ s ∈ J, MvPolynomial.map (algebraMap O O') s ∈ U` using `fun s hs => Submodule.mem_sup_right (Ideal.mem_map_of_mem _ hs)`. Establish `hU1 : ∀ x ∈ Submodule.span (O ⧸ m) (Set.range b), ∀ s, Ideal.Quotient.mk J s = x → MvPolynomial.map (algebraMap O O') s ∈ U`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Introduce `s hs`. Establish `h1` using `hJU _ (Ideal.Quotient.eq.1 (hs.trans (hB i).symm))`. Establish `h2 : MvPolynomial.map (algebraMap O O') (B i) ∈ U` using `Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)`.

Simplify using `using U.add_mem h1 h2`. Consider the case `zero => exact fun s hs => hJU s (Ideal.Quotient.eq_zero_iff_mem.1 hs)`. Consider the case `add x y _ _ hx hy`. Introduce `s hs`. Take `⟨s1, rfl⟩` from `Ideal.Quotient.mk_surjective x`.

Establish `h1` using `hx s1 rfl`. Establish `h2` using `hy (s - s1) (by rw [map_sub, hs, add_sub_cancel_left])`. Simplify using `using U.add_mem h1 h2`. Consider the case `smul c x _ hx`. Introduce `s hs`.

Take `⟨s1, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨o, rfl⟩` from `Ideal.Quotient.mk_surjective c`. Establish `h1` using `U.smul_mem (algebraMap O O' o) (hx s1 rfl)`. Establish `h3 : Ideal.Quotient.mk J s = Ideal.Quotient.mk J (C o * s1)`. Rewrite using `[hs, Algebra.smul_def, map_mul]`.

Both sides reduce to the same expression. Establish `h2` using `hJU _ (Ideal.Quotient.eq.1 h3)`. Rewrite `h1` using `[smul_eq_C_mul]`. Simplify using `using U.add_mem h1 h2`. Establish `hU : ∀ w, w ∈ U`.

Introduce `w`. Proceed by induction on `w using hb.inductionOn with`. Consider the case `zero => exact U.zero_mem`. Consider the case `tmul t => exact hU1 _ (by rw [b.span_eq]; trivial) t rfl`. Consider the case `smul a t ht => exact U.smul_mem a ht`.

Consider the case `add a t ha ht => exact U.add_mem ha ht`. Take `⟨v, hv, w, hw, rfl⟩` from `Submodule.mem_sup.1 (hU g)`. Take `⟨c, rfl⟩` from `Finsupp.mem_span_range_iff_exists_finsupp.1 hv`. Use `Ideal.add_mem _ (Ideal.mem_sup_right ?_) (Ideal.mem_sup_left hw)` and prove the remaining obligations. Use `Ideal.sum_mem _ fun i hi => ?_` and prove the remaining obligations.

Establish `h1` using `hkill i _ hg`. Rewrite `h1` using `[← C_pow, ← smul_eq_C_mul, map_smul, map_add, hkill i w hw, add_zero, Finsupp.sum, map_sum, Finset.sum_eq_single i]`. Rewrite `h1` using `[map_smul, hΛ, hlam, hB]`. Establish `h2 : Ideal.Quotient.mk m' (ϖ' ^ k * c i) = 0`. Rewrite using `[← h1]`.

Simplify using `[Algebra.smul_def]`. Rewrite `h2` using `[Ideal.Quotient.eq_zero_iff_mem, hm', Ideal.mem_span_singleton', he]`. Take `⟨z, hz⟩` from `h2`. Take `⟨r, rfl⟩` from `Nat.exists_eq_add_of_lt hk`. Establish `h3 : c i = ϖ' * (z * u * ϖ' ^ r)`.

Apply `mul_left_cancel₀ (pow_ne_zero k h0)` to reduce the goal to its premises. Rewrite using `[← hz]`. Expand and normalize the polynomial expressions, which then agree. Express the relevant statement in the definitionally equal form `c i • _ ∈ _`. Rewrite using `[h3, smul_eq_C_mul, C_mul, mul_assoc]`.

Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Introduce `l _ hl`. Rewrite using `[map_smul, hΛ, hlam, hB]`. Simplify using `[hl]`. Conclude with `fun h => absurd hi h`.
-/
theorem ram_colon {O O' σ : Type} [CommRing O] [CommRing O'] [IsDomain O'] [Algebra O O'] (ϖ : O)
    (hm : (Ideal.span {ϖ}).IsMaximal) (ϖ' : O') (h0 : ϖ' ≠ 0) (u : O'ˣ) (e k : ℕ)
    (he : algebraMap O O' ϖ = u * ϖ' ^ e) (hk : k < e) (J : Ideal (MvPolynomial σ O))
    (hJ : C ϖ ∈ J) (g : MvPolynomial σ O')
    (hg : C ϖ' ^ k * g ∈ J.map (MvPolynomial.map (algebraMap O O'))) :
    g ∈ J.map (MvPolynomial.map (algebraMap O O')) ⊔ Ideal.span {C ϖ'} := by
  classical
  set J' := J.map (MvPolynomial.map (algebraMap O O')) with hJ'
  set m : Ideal O := Ideal.span {ϖ} with hmdef
  letI : Field (O ⧸ m) := Ideal.Quotient.field m
  have hle : m ≤ J.comap (algebraMap O (MvPolynomial σ O)) := by
    rw [hmdef, Ideal.span_le, Set.singleton_subset_iff]
    exact hJ
  letI : Algebra (O ⧸ m) (MvPolynomial σ O ⧸ J) := Ideal.Quotient.algebraQuotientOfLEComap hle
  haveI : IsScalarTower O (O ⧸ m) (MvPolynomial σ O ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨ι, ⟨b⟩⟩ : ∃ ι : Type, Nonempty (Module.Basis ι (O ⧸ m) (MvPolynomial σ O ⧸ J)) :=
    ⟨_, ⟨Module.Basis.ofVectorSpace _ _⟩⟩
  have hb := (inferInstance :
    Algebra.IsPushout O O' (MvPolynomial σ O) (MvPolynomial σ O')).out
  set m' : Ideal O' := Ideal.span {algebraMap O O' ϖ} with hm'
  have hle' : m ≤ m'.comap (Algebra.ofId O O') := by
    rw [hmdef, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_span_singleton_self _
  let ι0 : (O ⧸ m) →ₐ[O] (O' ⧸ m') := Ideal.quotientMapₐ m' (Algebra.ofId O O') hle'
  let lam : ι → (MvPolynomial σ O →ₗ[O] (O' ⧸ m')) := fun i =>
    ι0.toLinearMap ∘ₗ ((b.coord i).restrictScalars O) ∘ₗ (Ideal.Quotient.mkₐ O J).toLinearMap
  have hlam : ∀ i s, lam i s = ι0 (b.coord i (Ideal.Quotient.mk J s)) := fun _ _ => rfl
  let Λ : ι → (MvPolynomial σ O' →ₗ[O'] (O' ⧸ m')) := fun i => hb.lift (lam i)
  have hΛ : ∀ i s, Λ i (MvPolynomial.map (algebraMap O O') s) = lam i s := fun i s =>
    hb.lift_eq (lam i) s
  have hkill : ∀ i, ∀ w ∈ J', Λ i w = 0 := by
    intro i w hw
    suffices h : ∀ h, Λ i (h * w) = 0 by simpa using h 1
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, hs, rfl⟩ := hx
      intro h
      induction h using hb.inductionOn with
      | zero => simp
      | tmul t =>
        change Λ i (MvPolynomial.map (algebraMap O O') t * _) = 0
        rw [← map_mul, hΛ, hlam, Ideal.Quotient.eq_zero_iff_mem.2 (J.mul_mem_left t hs)]
        simp
      | smul a t ht => rw [smul_mul_assoc, map_smul, ht, smul_zero]
      | add a t ha ht => rw [add_mul, map_add, ha, ht, add_zero]
    | zero => simp
    | add x y _ _ hx hy => intro h; rw [mul_add, map_add, hx, hy, add_zero]
    | smul a x _ hx => intro h; rw [smul_eq_mul, ← mul_assoc, hx]
  choose B hB using fun i => Ideal.Quotient.mk_surjective (I := J) (b i)
  let U : Submodule O' (MvPolynomial σ O') :=
    Submodule.span O' (Set.range fun i => MvPolynomial.map (algebraMap O O') (B i)) ⊔
      J'.restrictScalars O'
  have hJU : ∀ s ∈ J, MvPolynomial.map (algebraMap O O') s ∈ U := fun s hs =>
    Submodule.mem_sup_right (Ideal.mem_map_of_mem _ hs)
  have hU1 : ∀ x ∈ Submodule.span (O ⧸ m) (Set.range b), ∀ s, Ideal.Quotient.mk J s = x →
      MvPolynomial.map (algebraMap O O') s ∈ U := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro s hs
      have h1 := hJU _ (Ideal.Quotient.eq.1 (hs.trans (hB i).symm))
      have h2 : MvPolynomial.map (algebraMap O O') (B i) ∈ U :=
        Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
      simpa using U.add_mem h1 h2
    | zero => exact fun s hs => hJU s (Ideal.Quotient.eq_zero_iff_mem.1 hs)
    | add x y _ _ hx hy =>
      intro s hs
      obtain ⟨s1, rfl⟩ := Ideal.Quotient.mk_surjective x
      have h1 := hx s1 rfl
      have h2 := hy (s - s1) (by rw [map_sub, hs, add_sub_cancel_left])
      simpa using U.add_mem h1 h2
    | smul c x _ hx =>
      intro s hs
      obtain ⟨s1, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective c
      have h1 := U.smul_mem (algebraMap O O' o) (hx s1 rfl)
      have h3 : Ideal.Quotient.mk J s = Ideal.Quotient.mk J (C o * s1) := by
        rw [hs, Algebra.smul_def, map_mul]
        rfl
      have h2 := hJU _ (Ideal.Quotient.eq.1 h3)
      rw [smul_eq_C_mul] at h1
      simpa using U.add_mem h1 h2
  have hU : ∀ w, w ∈ U := by
    intro w
    induction w using hb.inductionOn with
    | zero => exact U.zero_mem
    | tmul t => exact hU1 _ (by rw [b.span_eq]; trivial) t rfl
    | smul a t ht => exact U.smul_mem a ht
    | add a t ha ht => exact U.add_mem ha ht
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.1 (hU g)
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hv
  refine Ideal.add_mem _ (Ideal.mem_sup_right ?_) (Ideal.mem_sup_left hw)
  refine Ideal.sum_mem _ fun i hi => ?_
  have h1 := hkill i _ hg
  rw [← C_pow, ← smul_eq_C_mul, map_smul, map_add, hkill i w hw, add_zero, Finsupp.sum, map_sum,
    Finset.sum_eq_single i] at h1
  · rw [map_smul, hΛ, hlam, hB] at h1
    have h2 : Ideal.Quotient.mk m' (ϖ' ^ k * c i) = 0 := by
      rw [← h1]
      simp [Algebra.smul_def]
    rw [Ideal.Quotient.eq_zero_iff_mem, hm', Ideal.mem_span_singleton', he] at h2
    obtain ⟨z, hz⟩ := h2
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_lt hk
    have h3 : c i = ϖ' * (z * u * ϖ' ^ r) := by
      apply mul_left_cancel₀ (pow_ne_zero k h0)
      rw [← hz]; ring
    change c i • _ ∈ _
    rw [h3, smul_eq_C_mul, C_mul, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · intro l _ hl
    rw [map_smul, hΛ, hlam, hB]
    simp [hl]
  · exact fun h => absurd hi h

end BaseChangeColon.BC
