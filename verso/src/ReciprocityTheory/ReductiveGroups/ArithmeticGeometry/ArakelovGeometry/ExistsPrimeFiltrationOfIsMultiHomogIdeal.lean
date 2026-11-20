import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.DoubleBlock

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable abbrev lexDecEq (n : ℕ) : DecidableEq (Lex (Fin n → ℕ)) := LinearOrder.toDecidableEq

attribute [local instance 2000] lexDecEq

section Lex

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : ℕ}

def lexW (e : K ≃ Fin n) : (Σ k, ι k) → Lex (Fin n → ℕ) :=
  fun p => toLex (Pi.single (e p.1) 1)

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • lexW (ι := ι) e i) (fun i => zero_nsmul _)]`. Use `show (∑ p, m p • (Pi.single (e p.1) 1 : Fin n → ℕ)) = fun j => ∑ i, m ⟨e.symm j, i⟩`. Use function extensionality and compare the values at `j`. Rewrite using `[Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single (e.symm j)]`. Simplify using `[Pi.single_apply]`.

Introduce `k _ hk`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Establish `hjk : j ≠ e k` using `fun h => hk (by rw [h, Equiv.symm_apply_apply])`. Simplify using `[Pi.single_apply, hjk]`. Simplify using the standard rewrite rules.
-/
theorem weight_lexW (e : K ≃ Fin n) (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (lexW (ι := ι) e) m = toLex (fun j => ∑ i, m ⟨e.symm j, i⟩) := by
  rw [Finsupp.weight_apply,
    Finsupp.sum_fintype m (fun i c => c • lexW (ι := ι) e i) (fun i => zero_nsmul _)]
  show (∑ p, m p • (Pi.single (e p.1) 1 : Fin n → ℕ)) = fun j => ∑ i, m ⟨e.symm j, i⟩
  funext j
  rw [Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single (e.symm j)]
  · simp [Pi.single_apply]
  · intro k _ hk
    refine Finset.sum_eq_zero fun i _ => ?_
    have hjk : j ≠ e k := fun h => hk (by rw [h, Equiv.symm_apply_apply])
    simp [Pi.single_apply, hjk]
  · simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h d hd`. Rewrite using `[weight_lexW]`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Conclude with `h d (MvPolynomial.mem_support_iff.mpr hd) (e.symm j)`. Introduce `h d hd k`. Establish `h1` using `h (MvPolynomial.mem_support_iff.mp hd)`. Rewrite `h1` using `[weight_lexW]`. Take `⟨j, rfl⟩` from `e.symm.surjective k`.

Conclude with `congrFun (toLex.injective h1) j`.
-/
theorem isMultiHomog_iff_lex (e : K ≃ Fin n) (f : MRing ι) (a : K → ℕ) :
    IsMultiHomog f a ↔ IsWeightedHomogeneous (lexW e) f (toLex (a ∘ e.symm)) := by
  constructor
  · intro h d hd
    rw [weight_lexW]
    congr 1
    funext j
    exact h d (MvPolynomial.mem_support_iff.mpr hd) (e.symm j)
  · intro h d hd k
    have h1 := h (MvPolynomial.mem_support_iff.mp hd)
    rw [weight_lexW] at h1
    obtain ⟨j, rfl⟩ := e.symm.surjective k
    exact congrFun (toLex.injective h1) j

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/- English proof (translation)
Rewrite `h` using `[mem_weightedHomogeneousSubmodule]`. Rewrite using `[isMultiHomog_iff_lex e]`. Establish `hm : (fun k => ofLex m (e k)) ∘ e.symm = ofLex m`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules.

Rewrite using `[hm, toLex_ofLex]`. Conclude with `h`.
-/
theorem isMultiHomog_of_mem_lex (e : K ≃ Fin n) {f : MRing ι} {m : Lex (Fin n → ℕ)}
    (h : f ∈ weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e) m) :
    IsMultiHomog f (fun k => ofLex m (e k)) := by
  rw [mem_weightedHomogeneousSubmodule] at h
  rw [isMultiHomog_iff_lex e]
  have hm : (fun k => ofLex m (e k)) ∘ e.symm = ofLex m := by
    funext j
    simp
  rw [hm, toLex_ofLex]
  exact h

/- English proof (translation)
Rewrite using `[mem_weightedHomogeneousSubmodule]`. Conclude with `(isMultiHomog_iff_lex e f a).1 h`.
-/
theorem mem_lex_of_isMultiHomog (e : K ≃ Fin n) {f : MRing ι} {a : K → ℕ} (h : IsMultiHomog f a) :
    f ∈ weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e) (toLex (a ∘ e.symm)) := by
  rw [mem_weightedHomogeneousSubmodule]
  exact (isMultiHomog_iff_lex e f a).1 h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨S, hS⟩` from `(Ideal.IsHomogeneous.iff_exists _ J).1 h`. Use `⟨Subtype.val '' S, ?_, hS⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, -, rfl⟩`.

Take `⟨i, hi⟩` from `x.2`. Conclude with `⟨_, isMultiHomog_of_mem_lex e hi⟩`. Introduce and unpack `⟨S, hS, rfl⟩`. Apply `Ideal.homogeneous_span` to reduce the goal to its premises. Introduce `x hx`.

Take `⟨a, ha⟩` from `hS x hx`. Conclude with `⟨_, mem_lex_of_isMultiHomog e ha⟩`.
-/
theorem isHomogeneous_lex_iff (e : K ≃ Fin n) (J : Ideal (MRing ι)) :
    J.IsHomogeneous (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e)) ↔ IsMultiHomogIdeal J := by
  constructor
  · intro h
    obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists _ J).1 h
    refine ⟨Subtype.val '' S, ?_, hS⟩
    rintro _ ⟨x, -, rfl⟩
    obtain ⟨i, hi⟩ := x.2
    exact ⟨_, isMultiHomog_of_mem_lex e hi⟩
  · rintro ⟨S, hS, rfl⟩
    apply Ideal.homogeneous_span
    intro x hx
    obtain ⟨a, ha⟩ := hS x hx
    exact ⟨_, mem_lex_of_isMultiHomog e ha⟩

end Lex

section Filtration

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Introduce `m hm k`. Establish `hm0 : m = 0`. Rewrite `hm` using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_one]`. Assume the negation of the conclusion as `h`. Conclude with `hm (if_neg (Ne.symm h))`.

Simplify using `[hm0]`.
-/
theorem isMultiHomog_one : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  have hm0 : m = 0 := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
    by_contra h
    exact hm (if_neg (Ne.symm h))
  simp [hm0]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/- English proof (translation)
Set `e` to `Fintype.equivFin K`. Establish `hJh : J.IsHomogeneous (weightedHomogeneousSubmodule ℤ (lexW (ι` using `ι) e)) := (isHomogeneous_lex_iff e J).2 hJ`. Establish `hcolh : ∀ (f : MRing ι) (d : Lex (Fin (Fintype.card K) → ℕ)), f ∈ weightedHomogeneousSubmodule ℤ (lexW (ι` using `ι) e) d → (J.colon {f}).IsHomogeneous (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e)) := by`. Introduce `f d hf i g hg`. Rewrite `hg`, the goal using `[Submodule.mem_colon_singleton, smul_eq_mul]`.

Rewrite using `[← DirectSum.coe_decompose_mul_add_of_right_mem _ hf]`. Conclude with `hJh (i + d) hg`. Set `S : Set (Ideal (MRing ι))` to `{P | ∃ (f : MRing ι) (c : K → ℕ), IsMultiHomog f c ∧ f ∉ J ∧ P = J.colon {f}}`. Establish `hne : S.Nonempty`. Use `⟨J.colon {1}, ?_⟩` and prove the remaining obligations.

Simplify using `only [S, Set.mem_setOf_eq]`. Conclude with `⟨1, 0, isMultiHomog_one, fun h => hJt ((Ideal.eq_top_iff_one J).2 h), rfl⟩`. Take `⟨P, hP, hmax⟩` from `set_has_maximal_iff_noetherian.2 (inferInstance : IsNoetherian (MRing ι) (MRing ι)) S hne`. Take `⟨f, c, hf, hfJ, rfl⟩` from `hP`. Establish `hfm` using `mem_lex_of_isMultiHomog e hf`.

Establish `hPh` using `hcolh f _ hfm`. Use `⟨f, c, hf, hfJ, ?_, (isHomogeneous_lex_iff e _).1 hPh⟩` and prove the remaining obligations. Apply `Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem hPh` to reduce the goal to its premises. Introduce `h`. Apply `hfJ` to reduce the goal to its premises.

Establish `h1 : (1 : MRing ι) ∈ J.colon {f}` using `by rw [h]; exact Submodule.mem_top`. Rewrite `h1` using `[Submodule.mem_colon_singleton, one_smul]`. Then use the resulting hypothesis. Introduce and unpack `x y ⟨i, hx⟩ ⟨j, hy⟩ hxy`. Distinguish the cases in `hxP : x ∈ J.colon {f}`. Conclude with `Or.inl hxP`.

Use `right`. Establish `hxf` using `SetLike.GradedMul.mul_mem hx hfm`. Establish `hxfJ : x * f ∉ J` using `by rwa [Submodule.mem_colon_singleton, smul_eq_mul] at hxP`. Establish `hmem : J.colon {x * f} ∈ S`. Simplify using `only [S, Set.mem_setOf_eq]`.

Conclude with `⟨x * f, _, isMultiHomog_of_mem_lex e hxf, hxfJ, rfl⟩`. Establish `hle : J.colon {f} ≤ J.colon {x * f}`. Introduce `g hg`. Rewrite `hg`, the goal using `[Submodule.mem_colon_singleton, smul_eq_mul]`. Rewrite using `[← mul_assoc, mul_comm g x, mul_assoc]`.

Conclude with `J.mul_mem_left x hg`. Establish `heq : J.colon {f} = J.colon {x * f}`. Assume the negation of the conclusion as `hne'`. Conclude with `hmax _ hmem (lt_of_le_of_ne hle hne')`. Rewrite using `[heq, Submodule.mem_colon_singleton, smul_eq_mul]`.

Rewrite `hxy` using `[Submodule.mem_colon_singleton, smul_eq_mul]`. Rewrite using `[← mul_assoc, mul_comm y x]`. Conclude with `hxy`.
-/
theorem exists_colon_prime (J : Ideal (MRing ι)) (hJ : IsMultiHomogIdeal J) (hJt : J ≠ ⊤) :
    ∃ (f : MRing ι) (c : K → ℕ), IsMultiHomog f c ∧ f ∉ J ∧
      (J.colon {f}).IsPrime ∧ IsMultiHomogIdeal (J.colon {f}) := by
  let e := Fintype.equivFin K
  have hJh : J.IsHomogeneous (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e)) :=
    (isHomogeneous_lex_iff e J).2 hJ

  have hcolh : ∀ (f : MRing ι) (d : Lex (Fin (Fintype.card K) → ℕ)),
      f ∈ weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e) d →
      (J.colon {f}).IsHomogeneous (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e)) := by
    intro f d hf i g hg
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hg ⊢
    rw [← DirectSum.coe_decompose_mul_add_of_right_mem _ hf]
    exact hJh (i + d) hg

  let S : Set (Ideal (MRing ι)) := {P | ∃ (f : MRing ι) (c : K → ℕ), IsMultiHomog f c ∧ f ∉ J ∧ P = J.colon {f}}
  have hne : S.Nonempty := by
    refine ⟨J.colon {1}, ?_⟩
    simp only [S, Set.mem_setOf_eq]
    exact ⟨1, 0, isMultiHomog_one, fun h => hJt ((Ideal.eq_top_iff_one J).2 h), rfl⟩
  obtain ⟨P, hP, hmax⟩ :=
    set_has_maximal_iff_noetherian.2 (inferInstance : IsNoetherian (MRing ι) (MRing ι)) S hne
  obtain ⟨f, c, hf, hfJ, rfl⟩ := hP
  have hfm := mem_lex_of_isMultiHomog e hf
  have hPh := hcolh f _ hfm
  refine ⟨f, c, hf, hfJ, ?_, (isHomogeneous_lex_iff e _).1 hPh⟩
  apply Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem hPh
  · intro h
    apply hfJ
    have h1 : (1 : MRing ι) ∈ J.colon {f} := by rw [h]; exact Submodule.mem_top
    rwa [Submodule.mem_colon_singleton, one_smul] at h1
  · rintro x y ⟨i, hx⟩ ⟨j, hy⟩ hxy
    by_cases hxP : x ∈ J.colon {f}
    · exact Or.inl hxP
    right
    have hxf := SetLike.GradedMul.mul_mem hx hfm
    have hxfJ : x * f ∉ J := by rwa [Submodule.mem_colon_singleton, smul_eq_mul] at hxP
    have hmem : J.colon {x * f} ∈ S := by
      simp only [S, Set.mem_setOf_eq]
      exact ⟨x * f, _, isMultiHomog_of_mem_lex e hxf, hxfJ, rfl⟩
    have hle : J.colon {f} ≤ J.colon {x * f} := by
      intro g hg
      rw [Submodule.mem_colon_singleton, smul_eq_mul] at hg ⊢
      rw [← mul_assoc, mul_comm g x, mul_assoc]
      exact J.mul_mem_left x hg
    have heq : J.colon {f} = J.colon {x * f} := by
      by_contra hne'
      exact hmax _ hmem (lt_of_le_of_ne hle hne')
    rw [heq, Submodule.mem_colon_singleton, smul_eq_mul]
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hxy
    rw [← mul_assoc, mul_comm y x]
    exact hxy

/- English proof (translation)
Take `⟨S, hS, rfl⟩` from `hJ`. Use `⟨S ∪ {f}, ?_, (Ideal.span_union _ _).symm⟩` and prove the remaining obligations. Introduce and unpack `g (hg | hg)`. Conclude with `hS g hg`. Rewrite using `[Set.mem_singleton_iff.mp hg]`.

Conclude with `⟨c, hf⟩`.
-/
theorem isMultiHomogIdeal_sup_span {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) {f : MRing ι}
    {c : K → ℕ} (hf : IsMultiHomog f c) : IsMultiHomogIdeal (J ⊔ Ideal.span {f}) := by
  obtain ⟨S, hS, rfl⟩ := hJ
  refine ⟨S ∪ {f}, ?_, (Ideal.span_union _ _).symm⟩
  rintro g (hg | hg)
  · exact hS g hg
  · rw [Set.mem_singleton_iff.mp hg]
    exact ⟨c, hf⟩

/- English proof (translation)
Proceed by induction on `J using WellFoundedGT.induction`. Name the introduced variables `J ih`. Distinguish the cases in `hJt : J = ⊤`. Conclude with `⟨0, fun _ => J, Fin.elim0, Fin.elim0, Fin.elim0, rfl, hJt, fun j => Fin.elim0 j⟩`. Take `⟨f, c, hf, hfJ, hprime, hqh⟩` from `exists_colon_prime J hJ hJt`.

Establish `hlt : J < J ⊔ Ideal.span {f}` using `lt_of_le_of_ne le_sup_left fun h => hfJ (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))`. Take `⟨N, F, g, cc, q, hF0, hFl, hstep⟩` from `ih _ hlt (isMultiHomogIdeal_sup_span hJ hf)`. Use `⟨N + 1, Fin.cons J F, Fin.cons f g, Fin.cons c cc, Fin.cons (J.colon {f}) q, rfl, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Fin.succ_last, Fin.cons_succ]`. Conclude with `hFl`.

Introduce `j`. Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations. Use `⟨by simpa using hf, ?_, by simpa using hprime, by simpa using hqh, fun g' => ?_⟩` and prove the remaining obligations. Simplify using `[hF0]`. Simplify using `[Submodule.mem_colon_singleton, smul_eq_mul]`.

Simplify using `only [← Fin.succ_castSucc, Fin.cons_succ]`. Conclude with `hstep j`.
-/
theorem exists_primeFiltration_of_isMultiHomogIdeal (J : Ideal (MRing ι)) (hJ : IsMultiHomogIdeal J) :
    ∃ (N : ℕ) (F : Fin (N + 1) → Ideal (MRing ι)) (f : Fin N → MRing ι) (c : Fin N → K → ℕ)
      (q : Fin N → Ideal (MRing ι)),
      F 0 = J ∧ F (Fin.last N) = ⊤ ∧ ∀ j : Fin N,
        IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
        (q j).IsPrime ∧ IsMultiHomogIdeal (q j) ∧
        ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc := by
  induction J using WellFoundedGT.induction
  rename_i J ih
  by_cases hJt : J = ⊤
  · exact ⟨0, fun _ => J, Fin.elim0, Fin.elim0, Fin.elim0, rfl, hJt, fun j => Fin.elim0 j⟩
  obtain ⟨f, c, hf, hfJ, hprime, hqh⟩ := exists_colon_prime J hJ hJt
  have hlt : J < J ⊔ Ideal.span {f} := lt_of_le_of_ne le_sup_left fun h =>
    hfJ (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  obtain ⟨N, F, g, cc, q, hF0, hFl, hstep⟩ := ih _ hlt (isMultiHomogIdeal_sup_span hJ hf)
  refine ⟨N + 1, Fin.cons J F, Fin.cons f g, Fin.cons c cc, Fin.cons (J.colon {f}) q, rfl, ?_, ?_⟩
  · rw [← Fin.succ_last, Fin.cons_succ]
    exact hFl
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · refine ⟨by simpa using hf, ?_, by simpa using hprime, by simpa using hqh, fun g' => ?_⟩
      · simp [hF0]
      · simp [Submodule.mem_colon_singleton, smul_eq_mul]
    · simp only [← Fin.succ_castSucc, Fin.cons_succ]
      exact hstep j

end Filtration

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
