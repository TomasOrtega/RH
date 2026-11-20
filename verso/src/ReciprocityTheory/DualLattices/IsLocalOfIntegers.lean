import ReciprocityTheory.DualLattices.CotangentSurjective

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

/- English proof (translation)
Establish `e : (fun k => c₀ * A k i₀ - ∑ i ∈ Finset.univ.erase i₀, β i * A k i) = fun k => ∑ i, (if i = i₀ then c₀ else -β i) • A k i`. Use function extensionality and compare the values at `k`. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), if_pos rfl, smul_eq_mul, sub_eq_add_neg, ← Finset.sum_neg_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations.

Rewrite using `[if_neg (Finset.ne_of_mem_erase hi), smul_eq_mul, neg_mul]`. Rewrite using `[e, Matrix.det_updateCol_sum, if_pos rfl, smul_eq_mul]`.
-/
lemma det_col_comb {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (i₀ : Fin n)
    (c₀ : R) (β : Fin n → R) :
    (A.updateCol i₀
      (fun k => c₀ * A k i₀ - ∑ i ∈ Finset.univ.erase i₀, β i * A k i)).det = c₀ * A.det := by
  have e : (fun k => c₀ * A k i₀ - ∑ i ∈ Finset.univ.erase i₀, β i * A k i) =
      fun k => ∑ i, (if i = i₀ then c₀ else -β i) • A k i := by
    funext k
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), if_pos rfl, smul_eq_mul, sub_eq_add_neg,
      ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_neg (Finset.ne_of_mem_erase hi), smul_eq_mul, neg_mul]
  rw [e, Matrix.det_updateCol_sum, if_pos rfl, smul_eq_mul]

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro c n q _ T _`. Simplify using the standard rewrite rules. Consider the case `succ m ih`.

Introduce `c n q hq T hT`. Set `tl : ((j : Fin (m + 1)) → R ⧸ Ideal.span {c j}) →ₗ[R] ((j : Fin m) → R ⧸ Ideal.span {c j.succ})` to `LinearMap.pi fun j => LinearMap.proj j.succ`. Establish `htl_surj : Function.Surjective tl` using `fun y => ⟨Fin.cons (0 : R ⧸ Ideal.span {c 0}) y, funext fun j => rfl⟩`. Establish `hprod : ∏ j, c j = c 0 * ∏ j : Fin m, c j.succ` using `Fin.prod_univ_succ c`. Establish `hfst : ∀ (r : Fin n → R) (a : Fin n → R), (∀ i, Ideal.Quotient.mk (Ideal.span {c 0}) (a i) = q i 0) → (∑ i, r i • q i) 0 = Ideal.Quotient.mk (Ideal.span {c 0}) (∑ i, r i * a i)`.

Introduce `r a ha`. Rewrite using `[Finset.sum_apply, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, ← ha i, map_mul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]`. Distinguish the cases in `hc0 : IsUnit (c 0)`.

Establish `hgen : Submodule.span R (Set.range (tl ∘ q)) = ⊤`. Rewrite using `[Set.range_comp, ← Submodule.map_span, hq, Submodule.map_top, LinearMap.range_eq_top.2 htl_surj]`. Establish `h` using `ih (fun j => c j.succ) n (tl ∘ q) hgen T (fun k => by`. Use `congrArg tl (hT k)` as an intermediate fact. Rewrite `this` using `[map_sum, map_zero]`.

Simplify `this)` using `only [map_smul, Function.comp_apply]`. Rewrite using `[hprod, Ideal.span_singleton_mul_left_unit hc0]`. Conclude with `h`. Use `choose a ha using fun i => Ideal.Quotient.mk_surjective (q i 0)`. Take `⟨g, hg⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 (hq ▸ Submodule.mem_top : (Pi.single (0 : Fin (m + 1)) (1 : R ⧸ Ideal.span {c 0}) : (j : Fin (m + 1)) → R ⧸ Ideal.span {c j}) ∈ Submodule.span R (Set.range q))`.

Establish `hc0m : c 0 ∈ IsLocalRing.maximalIdeal R` using `(IsLocalRing.mem_maximalIdeal _).2 hc0`. Establish `hspan_le : Ideal.span {c 0} ≤ IsLocalRing.maximalIdeal R` using `(Ideal.span_singleton_le_iff_mem _).2 hc0m`. Establish `h1 : ∑ i, g i * a i - 1 ∈ Ideal.span {c 0}`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hfst g a ha, hg]`. Simplify using the standard rewrite rules.

Establish `hu : IsUnit (∑ i, g i * a i)`. Assume the negation of the conclusion as `hx`. Establish `hx' : ∑ i, g i * a i ∈ IsLocalRing.maximalIdeal R` using `(IsLocalRing.mem_maximalIdeal _).2 hx`. Use `Ideal.sub_mem _ hx' (hspan_le h1)` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`.

Conclude with `(IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)`. Choose the witnesses or unpack the hypotheses as in `⟨i₀, hi₀⟩ : ∃ i₀, IsUnit (a i₀) := by`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Apply `(IsLocalRing.mem_maximalIdeal _).1 _ hu` to reduce the goal to its premises.

Conclude with `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hne i))`. Use `set ai : R := ↑hi₀.unit⁻¹ with hai`. Establish `haai : a i₀ * ai = 1` using `by rw [hai]; exact hi₀.mul_val_inv`. Set `β : Fin n → R` to `fun i => a i * ai`. Establish `hβ0 : β i₀ = 1` using `haai`.

Set `q'' : Fin n → ((j : Fin (m + 1)) → R ⧸ Ideal.span {c j})` to `fun i => if i = i₀ then c 0 • q i₀ else q i - β i • q i₀`. Establish `hcomb : ∀ (r : Fin n → R) (w : R), c 0 * w = ∑ i, r i * β i → ∑ i, (if i = i₀ then w else r i) • q'' i = ∑ i, r i • q i`. Introduce `r w hw`. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]`. Establish `hrest : ∑ i ∈ Finset.univ.erase i₀, (if i = i₀ then w else r i) • q'' i = ∑ i ∈ Finset.univ.erase i₀, r i • q i - (∑ i ∈ Finset.univ.erase i₀, r i * β i) • q i₀`.

Rewrite using `[Finset.sum_smul, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hne : i ≠ i₀` using `Finset.ne_of_mem_erase hi`. Simplify using `only [q'', if_neg hne, smul_sub, smul_smul]`. Establish `hw' : c 0 * w = r i₀ + ∑ i ∈ Finset.univ.erase i₀, r i * β i`.

Rewrite using `[hw, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), hβ0, mul_one]`. Rewrite using `[hrest]`. Simplify using `only [q'', if_pos rfl, smul_smul, ↓reduceIte]`. Rewrite using `[mul_comm w, hw', add_smul]`. Normalize the expressions using the abelian group laws.

Establish `hk0 : ∀ k, ∑ i, T k i * a i ∈ Ideal.span {c 0}` using `fun k => by`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← hfst (T k) a ha, hT k]`. Both sides reduce to the same expression. Use `choose t' ht' using fun k => Ideal.mem_span_singleton'.1 (hk0 k)`. Set `t : Fin n → R` to `fun k => t' k * ai`.

Establish `ht : ∀ k, c 0 * t k = ∑ i, T k i * β i` using `fun k => by`. Simplify using `only [t, β, ← mul_assoc, ← Finset.sum_mul, ← ht' k]`. Expand and normalize the polynomial expressions, which then agree. Set `T'' : Matrix (Fin n) (Fin n) R` to `Matrix.of fun k i => if i = i₀ then t k else T k i`. Establish `hrel : ∀ k, ∑ i, T'' k i • (tl ∘ q'') i = 0` using `fun k => by`.

Use `hcomb (T k) (t k) (ht k)` as an intermediate fact. Rewrite `this` using `[hT k]`. Establish `h2` using `congrArg tl this`. Rewrite `h2` using `[map_sum, map_zero]`. Simplify `h2` using `only [T'', Matrix.of_apply, map_smul, Function.comp_apply]`.

Establish `hgen : Submodule.span R (Set.range (tl ∘ q'')) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `y _`. Take `⟨x, rfl⟩` from `htl_surj y`. Set `x0 : (j : Fin (m + 1)) → R ⧸ Ideal.span {c j}` to `Fin.cons 0 (tl x)`.

Take `⟨r, hr⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 (hq ▸ Submodule.mem_top : x0 ∈ Submodule.span R (Set.range q))`. Establish `hr0 : ∑ i, r i * a i ∈ Ideal.span {c 0}`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← hfst r a ha, hr]`. Both sides reduce to the same expression. Take `⟨w', hw'⟩` from `Ideal.mem_span_singleton'.1 hr0`.

Establish `hw : c 0 * (w' * ai) = ∑ i, r i * β i`. Simplify using `only [β, ← mul_assoc, ← Finset.sum_mul, ← hw']`. Expand and normalize the polynomial expressions, which then agree. Establish `hx` using `hcomb r (w' * ai) hw`. Rewrite `hx` using `[hr]`.

Establish `htx : tl x = tl x0` using `funext fun j => rfl`. Rewrite using `[htx, ← hx, map_sum]`. Conclude with `Submodule.sum_mem _ fun i _ => by`. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Establish `hdet''` using `ih (fun j => c j.succ) n (tl ∘ q'') hgen T'' hrel`. Establish `hTeq : T = T''.updateCol i₀ (fun k => c 0 * T'' k i₀ - ∑ i ∈ Finset.univ.erase i₀, β i * T'' k i)`. Use extensionality with `k i`. Distinguish the cases in `hi : i = i₀`. Substitute `hi` using the available equality.

Rewrite using `[updateCol_self]`. Simplify using `only [T'', Matrix.of_apply, ↓reduceIte]`. Rewrite using `[ht k, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hβ0, mul_one]`. Establish `: ∑ x ∈ Finset.univ.erase i, β x * (if x = i then t k else T k x) = ∑ x ∈ Finset.univ.erase i, T k x * β x` using `Finset.sum_congr rfl fun x hx => by`. Rewrite using `[if_neg (Finset.ne_of_mem_erase hx), mul_comm]`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[updateCol_ne hi]`. Simplify using `only [T'', Matrix.of_apply, if_neg hi]`. Rewrite using `[hTeq, det_col_comb]`.

Take `⟨z, hz⟩` from `Ideal.mem_span_singleton'.1 hdet''`. Rewrite using `[hprod, ← hz]`. Conclude with `Ideal.mem_span_singleton'.2 ⟨z, by ring⟩`.
-/
theorem det_mem_span_prod {R : Type*} [CommRing R] [IsLocalRing R] :
    ∀ (m : ℕ) (c : Fin m → R) (n : ℕ) (q : Fin n → ((j : Fin m) → R ⧸ Ideal.span {c j})),
      Submodule.span R (Set.range q) = ⊤ →
      ∀ T : Matrix (Fin n) (Fin n) R, (∀ k, ∑ i, T k i • q i = 0) →
      T.det ∈ Ideal.span {∏ j, c j} := by
  intro m
  induction m with
  | zero => intro c n q _ T _; simp
  | succ m ih =>
    intro c n q hq T hT
    let tl : ((j : Fin (m + 1)) → R ⧸ Ideal.span {c j}) →ₗ[R]
        ((j : Fin m) → R ⧸ Ideal.span {c j.succ}) :=
      LinearMap.pi fun j => LinearMap.proj j.succ
    have htl_surj : Function.Surjective tl := fun y =>
      ⟨Fin.cons (0 : R ⧸ Ideal.span {c 0}) y, funext fun j => rfl⟩
    have hprod : ∏ j, c j = c 0 * ∏ j : Fin m, c j.succ := Fin.prod_univ_succ c

    have hfst : ∀ (r : Fin n → R) (a : Fin n → R),
        (∀ i, Ideal.Quotient.mk (Ideal.span {c 0}) (a i) = q i 0) →
        (∑ i, r i • q i) 0 = Ideal.Quotient.mk (Ideal.span {c 0}) (∑ i, r i * a i) := by
      intro r a ha
      rw [Finset.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, ← ha i, map_mul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
    by_cases hc0 : IsUnit (c 0)
    · have hgen : Submodule.span R (Set.range (tl ∘ q)) = ⊤ := by
        rw [Set.range_comp, ← Submodule.map_span, hq, Submodule.map_top,
          LinearMap.range_eq_top.2 htl_surj]
      have h := ih (fun j => c j.succ) n (tl ∘ q) hgen T (fun k => by
        have := congrArg tl (hT k)
        rw [map_sum, map_zero] at this
        simpa only [map_smul, Function.comp_apply] using this)
      rw [hprod, Ideal.span_singleton_mul_left_unit hc0]
      exact h
    · choose a ha using fun i => Ideal.Quotient.mk_surjective (q i 0)
      obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun R).1
        (hq ▸ Submodule.mem_top : (Pi.single (0 : Fin (m + 1)) (1 : R ⧸ Ideal.span {c 0}) :
          (j : Fin (m + 1)) → R ⧸ Ideal.span {c j}) ∈ Submodule.span R (Set.range q))
      have hc0m : c 0 ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hc0
      have hspan_le : Ideal.span {c 0} ≤ IsLocalRing.maximalIdeal R :=
        (Ideal.span_singleton_le_iff_mem _).2 hc0m
      have h1 : ∑ i, g i * a i - 1 ∈ Ideal.span {c 0} := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hfst g a ha, hg]
        simp
      have hu : IsUnit (∑ i, g i * a i) := by
        by_contra hx
        have hx' : ∑ i, g i * a i ∈ IsLocalRing.maximalIdeal R :=
          (IsLocalRing.mem_maximalIdeal _).2 hx
        have := Ideal.sub_mem _ hx' (hspan_le h1)
        rw [sub_sub_cancel] at this
        exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)
      obtain ⟨i₀, hi₀⟩ : ∃ i₀, IsUnit (a i₀) := by
        by_contra hne
        push Not at hne
        apply (IsLocalRing.mem_maximalIdeal _).1 _ hu
        exact Ideal.sum_mem _ fun i _ =>
          Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hne i))
      set ai : R := ↑hi₀.unit⁻¹ with hai
      have haai : a i₀ * ai = 1 := by rw [hai]; exact hi₀.mul_val_inv
      let β : Fin n → R := fun i => a i * ai
      have hβ0 : β i₀ = 1 := haai
      let q'' : Fin n → ((j : Fin (m + 1)) → R ⧸ Ideal.span {c j}) := fun i =>
        if i = i₀ then c 0 • q i₀ else q i - β i • q i₀

      have hcomb : ∀ (r : Fin n → R) (w : R), c 0 * w = ∑ i, r i * β i →
          ∑ i, (if i = i₀ then w else r i) • q'' i = ∑ i, r i • q i := by
        intro r w hw
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
        have hrest : ∑ i ∈ Finset.univ.erase i₀, (if i = i₀ then w else r i) • q'' i =
            ∑ i ∈ Finset.univ.erase i₀, r i • q i -
              (∑ i ∈ Finset.univ.erase i₀, r i * β i) • q i₀ := by
          rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i hi => ?_
          have hne : i ≠ i₀ := Finset.ne_of_mem_erase hi
          simp only [q'', if_neg hne, smul_sub, smul_smul]
        have hw' : c 0 * w = r i₀ + ∑ i ∈ Finset.univ.erase i₀, r i * β i := by
          rw [hw, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), hβ0, mul_one]
        rw [hrest]
        simp only [q'', if_pos rfl, smul_smul, ↓reduceIte]
        rw [mul_comm w, hw', add_smul]
        abel

      have hk0 : ∀ k, ∑ i, T k i * a i ∈ Ideal.span {c 0} := fun k => by
        rw [← Ideal.Quotient.eq_zero_iff_mem, ← hfst (T k) a ha, hT k]; rfl
      choose t' ht' using fun k => Ideal.mem_span_singleton'.1 (hk0 k)
      let t : Fin n → R := fun k => t' k * ai
      have ht : ∀ k, c 0 * t k = ∑ i, T k i * β i := fun k => by
        simp only [t, β, ← mul_assoc, ← Finset.sum_mul, ← ht' k]
        ring
      let T'' : Matrix (Fin n) (Fin n) R := Matrix.of fun k i => if i = i₀ then t k else T k i
      have hrel : ∀ k, ∑ i, T'' k i • (tl ∘ q'') i = 0 := fun k => by
        have := hcomb (T k) (t k) (ht k)
        rw [hT k] at this
        have h2 := congrArg tl this
        rw [map_sum, map_zero] at h2
        simpa only [T'', Matrix.of_apply, map_smul, Function.comp_apply] using h2
      have hgen : Submodule.span R (Set.range (tl ∘ q'')) = ⊤ := by
        rw [eq_top_iff]
        intro y _
        obtain ⟨x, rfl⟩ := htl_surj y
        let x0 : (j : Fin (m + 1)) → R ⧸ Ideal.span {c j} := Fin.cons 0 (tl x)
        obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).1
          (hq ▸ Submodule.mem_top : x0 ∈ Submodule.span R (Set.range q))
        have hr0 : ∑ i, r i * a i ∈ Ideal.span {c 0} := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, ← hfst r a ha, hr]; rfl
        obtain ⟨w', hw'⟩ := Ideal.mem_span_singleton'.1 hr0
        have hw : c 0 * (w' * ai) = ∑ i, r i * β i := by
          simp only [β, ← mul_assoc, ← Finset.sum_mul, ← hw']
          ring
        have hx := hcomb r (w' * ai) hw
        rw [hr] at hx
        have htx : tl x = tl x0 := funext fun j => rfl
        rw [htx, ← hx, map_sum]
        exact Submodule.sum_mem _ fun i _ => by
          rw [map_smul]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      have hdet'' := ih (fun j => c j.succ) n (tl ∘ q'') hgen T'' hrel
      have hTeq : T = T''.updateCol i₀
          (fun k => c 0 * T'' k i₀ - ∑ i ∈ Finset.univ.erase i₀, β i * T'' k i) := by
        ext k i
        by_cases hi : i = i₀
        · subst hi
          rw [updateCol_self]
          simp only [T'', Matrix.of_apply, ↓reduceIte]
          rw [ht k, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hβ0, mul_one]
          have : ∑ x ∈ Finset.univ.erase i, β x * (if x = i then t k else T k x) =
              ∑ x ∈ Finset.univ.erase i, T k x * β x :=
            Finset.sum_congr rfl fun x hx => by
              rw [if_neg (Finset.ne_of_mem_erase hx), mul_comm]
          rw [this]; ring
        · rw [updateCol_ne hi]
          simp only [T'', Matrix.of_apply, if_neg hi]
      rw [hTeq, det_col_comb]
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hdet''
      rw [hprod, ← hz]
      exact Ideal.mem_span_singleton'.2 ⟨z, by ring⟩

/- English proof (translation)
Establish `hne : Nontrivial R` using `⟨⟨0, 1, fun h => by`. Use `congrArg (fun x => v (algebraMap R C x)) h` as an intermediate fact. Simplify using `at this⟩⟩`. Use `@IsLocalRing.of_nonunits_add R _ hne ?_` and prove the remaining obligations. Introduce `a b ha hb`.

Rewrite `ha`, `hb`, the goal using `[mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one]`. Establish `ha' : v (algebraMap R C a) < 1` using `lt_of_le_of_ne (hv.map_le_one a) ha`. Establish `hb' : v (algebraMap R C b) < 1` using `lt_of_le_of_ne (hv.map_le_one b) hb`. Rewrite using `[map_add]`. Conclude with `ne_of_lt (lt_of_le_of_lt (v.map_add _ _) (max_lt ha' hb'))`.
-/
lemma isLocal_of_integers {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) : IsLocalRing R := by
  have hne : Nontrivial R := ⟨⟨0, 1, fun h => by
    have := congrArg (fun x => v (algebraMap R C x)) h
    simp at this⟩⟩
  refine @IsLocalRing.of_nonunits_add R _ hne ?_
  intro a b ha hb
  rw [mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one] at ha hb ⊢
  have ha' : v (algebraMap R C a) < 1 := lt_of_le_of_ne (hv.map_le_one a) ha
  have hb' : v (algebraMap R C b) < 1 := lt_of_le_of_ne (hv.map_le_one b) hb
  rw [map_add]
  exact ne_of_lt (lt_of_le_of_lt (v.map_add _ _) (max_lt ha' hb'))

/- English proof (translation)
Use `haveI := isLocal_of_integers hv`. Take `⟨m, c, ⟨e⟩, hxc⟩` from `hx`. Use `choose a ha using hrel`. Take `⟨q, hqdef⟩ : ∃ q : Fin n → ((j : Fin m) → R ⧸ Ideal.span {c j}), q = fun i => e (y i)` from `⟨_, rfl⟩`. Establish `hq : Submodule.span R (Set.range q) = ⊤`.

Establish `h1 : Set.range q = (e : M →ₗ[R] _) '' Set.range y`. Use extensionality with `z`. Simplify using `[hqdef]`. Rewrite using `[h1, Submodule.span_image, hy, Submodule.map_top, LinearEquiv.range]`. Take `⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin n) R, T = fun i j => (if j = i then δ i else 0) - (if j < i then a i j else 0)` from `⟨_, rfl⟩`.

Establish `hrelT : ∀ k, ∑ i, T k i • q i = 0`. Introduce `k`. Establish `h` using `congrArg e (ha k)`. Simplify using `only [map_smul, map_sum, ite_smul, zero_smul] at h`. Simplify using `only [hT, hqdef, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Rewrite using `[h, sub_eq_zero]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`. Establish `hdet` using `det_mem_span_prod m c n q hq T hrelT`. Establish `hdetT : T.det = ∏ i, δ i`.

Rewrite using `[Matrix.det_of_lowerTriangular]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[hT]`. Introduce `i j hij`. Establish `h' : i < j` using `OrderDual.toDual_lt_toDual.mp hij`.

Simplify using `[hT, h'.ne', not_lt.mpr h'.le]`. Take `⟨r, hr⟩` from `Ideal.mem_span_singleton'.mp hdet`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hdetT, ← hr]`. Simplify using `[map_prod]`.

Use `_ ≤ 1 * ∏ j, v (algebraMap R C (c j)) := by gcongr`. Conclude with `hv.map_le_one r`. Use `_ = x := by rw [one_mul, hxc]`.
-/
theorem prod_le_of_gen {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) {M : Type} [AddCommGroup M] [Module R M] {x : NNReal}
    (hx : HasLen v R M x) {n : ℕ} (y : Fin n → M)
    (hy : Submodule.span R (Set.range y) = ⊤) (δ : Fin n → R)
    (hrel : ∀ i, ∃ a : Fin n → R, δ i • y i = ∑ j, (if j < i then a j else 0) • y j) :
    ∏ i, v (algebraMap R C (δ i)) ≤ x := by
  haveI := isLocal_of_integers hv
  obtain ⟨m, c, ⟨e⟩, hxc⟩ := hx
  choose a ha using hrel
  obtain ⟨q, hqdef⟩ : ∃ q : Fin n → ((j : Fin m) → R ⧸ Ideal.span {c j}), q = fun i => e (y i) :=
    ⟨_, rfl⟩
  have hq : Submodule.span R (Set.range q) = ⊤ := by
    have h1 : Set.range q = (e : M →ₗ[R] _) '' Set.range y := by
      ext z
      simp [hqdef]
    rw [h1, Submodule.span_image, hy, Submodule.map_top, LinearEquiv.range]
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin n) R,
      T = fun i j => (if j = i then δ i else 0) - (if j < i then a i j else 0) := ⟨_, rfl⟩
  have hrelT : ∀ k, ∑ i, T k i • q i = 0 := by
    intro k
    have h := congrArg e (ha k)
    simp only [map_smul, map_sum, ite_smul, zero_smul] at h
    simp only [hT, hqdef, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [h, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hdet := det_mem_span_prod m c n q hq T hrelT
  have hdetT : T.det = ∏ i, δ i := by
    rw [Matrix.det_of_lowerTriangular]
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp [hT]
    · intro i j hij
      have h' : i < j := OrderDual.toDual_lt_toDual.mp hij
      simp [hT, h'.ne', not_lt.mpr h'.le]
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hdet
  calc ∏ i, v (algebraMap R C (δ i)) = v (algebraMap R C (∏ i, δ i)) := by simp [map_prod]
    _ = v (algebraMap R C r) * ∏ j, v (algebraMap R C (c j)) := by
        rw [← hdetT, ← hr]
        simp [map_prod]
    _ ≤ 1 * ∏ j, v (algebraMap R C (c j)) := by
        gcongr
        exact hv.map_le_one r
    _ = x := by rw [one_mul, hxc]

end ReciprocityTheory.PGsh.Up
