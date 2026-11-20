import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentKaehlerDOfAlgebraicIndependentStatement

namespace GlobalTheory.BertiniC

open KaehlerDifferential in

/- English proof (translation)
Establish `r4 : algebraMap A κ (f p₀) ≠ 0`. Introduce `h`. Rewrite `r4s` using `[h, mul_zero, zero_sub, neg_eq_zero]`. Conclude with `one_ne_zero r4s`. Establish `hlin` using `GlobalTheory.T.linearIndependent_kaehlerD_of_algebraicIndependent k κ t ht`.

Use `set m : Fin n → KaehlerDifferential k κ := fun l => KaehlerDifferential.map k k A κ (ω l) with hm`. Establish `hdψ : ∀ a : A, D k κ (algebraMap A κ a) = ∑ l, algebraMap A κ (δ l a) • m l`. Introduce `a`. Rewrite using `[← KaehlerDifferential.map_D k k A κ, hω a, map_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.map_smul, algebraMap_smul]`. Establish `e1 : ∀ i ∈ J, ∑ p, algebraMap A κ (f p) • D k κ (t (i, p)) = - ∑ p, t (i, p) • D k κ (algebraMap A κ (f p))`. Introduce `i hi`. Establish `h` using `congrArg (D k κ) (r1 i hi)`. Rewrite `h` using `[map_sum, map_zero]`.

Simplify using `only [Derivation.leibniz, Finset.sum_add_distrib] at h`. Rewrite using `[eq_neg_iff_add_eq_zero, add_comm]`. Conclude with `h`. Establish `e2 : ∑ i ∈ J, c i • ∑ p, t (i, p) • D k κ (algebraMap A κ (f p)) = 0`. Establish `: ∑ i ∈ J, c i • ∑ p, t (i, p) • D k κ (algebraMap A κ (f p)) = ∑ l, (∑ i ∈ J, c i * ∑ p, t (i, p) * algebraMap A κ (δ l (f p))) • m l`.

Simplify using `only [hdψ, Finset.smul_sum, Finset.sum_smul, Finset.mul_sum, smul_smul, mul_assoc]`. Use `conv_rhs => rw [Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_comm`. Rewrite using `[this]`. Simplify using `[r2]`.

Establish `key : ∑ x ∈ J ×ˢ (Finset.univ : Finset ι), (c x.1 * algebraMap A κ (f x.2)) • D k κ (t x) = 0`. Rewrite using `[Finset.sum_product]`. Simplify using `only [mul_smul, ← Finset.smul_sum]`. Rewrite using `[Finset.sum_congr rfl (fun i hi => by rw [e1 i hi]), ]`. Simplify using `only [smul_neg, Finset.sum_neg_distrib, e2, neg_zero]`.

Use `linearIndependent_iff'.1 hlin _ _ key (i₀, p₀) (by simp [hi₀])` as an intermediate fact. Rewrite `this` using `[sub_eq_zero.1 r3, one_mul]`. Conclude with `r4 this`.
-/
theorem false_of_dependent_derivatives {k A κ : Type} [Field k] [CharZero k] [CommRing A] [Algebra k A]
    [Field κ] [Algebra k κ] [Algebra A κ] [IsScalarTower k A κ] [Algebra.EssFiniteType k κ]
    (n : ℕ) (δ : Fin n → Derivation k A A) (ω : Fin n → KaehlerDifferential k A)
    (hω : ∀ a : A, KaehlerDifferential.D k A a = ∑ l, δ l a • ω l)
    {ι : Type} [Fintype ι] (f : ι → A) (M : ℕ) (J : Finset (Fin M)) (i₀ : Fin M) (p₀ : ι)
    (hi₀ : i₀ ∈ J) (t : Fin M × ι → κ) (ht : AlgebraicIndependent k t) (c : Fin M → κ)
    (r1 : ∀ i ∈ J, ∑ p, t (i, p) * algebraMap A κ (f p) = 0)
    (r2 : ∀ l, ∑ i ∈ J, c i * ∑ p, t (i, p) * algebraMap A κ (δ l (f p)) = 0)
    (r3 : c i₀ - 1 = 0) (s : κ) (r4s : s * algebraMap A κ (f p₀) - 1 = 0) : False := by
  have r4 : algebraMap A κ (f p₀) ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_sub, neg_eq_zero] at r4s
    exact one_ne_zero r4s
  have hlin := GlobalTheory.T.linearIndependent_kaehlerD_of_algebraicIndependent k κ t ht
  set m : Fin n → KaehlerDifferential k κ := fun l => KaehlerDifferential.map k k A κ (ω l) with hm
  have hdψ : ∀ a : A, D k κ (algebraMap A κ a) = ∑ l, algebraMap A κ (δ l a) • m l := by
    intro a
    rw [← KaehlerDifferential.map_D k k A κ, hω a, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [LinearMap.map_smul, algebraMap_smul]
  have e1 : ∀ i ∈ J, ∑ p, algebraMap A κ (f p) • D k κ (t (i, p)) =
      - ∑ p, t (i, p) • D k κ (algebraMap A κ (f p)) := by
    intro i hi
    have h := congrArg (D k κ) (r1 i hi)
    rw [map_sum, map_zero] at h
    simp only [Derivation.leibniz, Finset.sum_add_distrib] at h
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h
  have e2 : ∑ i ∈ J, c i • ∑ p, t (i, p) • D k κ (algebraMap A κ (f p)) = 0 := by
    have : ∑ i ∈ J, c i • ∑ p, t (i, p) • D k κ (algebraMap A κ (f p)) =
        ∑ l, (∑ i ∈ J, c i * ∑ p, t (i, p) * algebraMap A κ (δ l (f p))) • m l := by
      simp only [hdψ, Finset.smul_sum, Finset.sum_smul, Finset.mul_sum, smul_smul, mul_assoc]
      conv_rhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    rw [this]
    simp [r2]
  have key : ∑ x ∈ J ×ˢ (Finset.univ : Finset ι), (c x.1 * algebraMap A κ (f x.2)) • D k κ (t x) = 0 := by
    rw [Finset.sum_product]
    simp only [mul_smul, ← Finset.smul_sum]
    rw [Finset.sum_congr rfl (fun i hi => by rw [e1 i hi]), ]
    simp only [smul_neg, Finset.sum_neg_distrib, e2, neg_zero]
  have := linearIndependent_iff'.1 hlin _ _ key (i₀, p₀) (by simp [hi₀])
  rw [sub_eq_zero.1 r3, one_mul] at this
  exact r4 this

section Construction

variable {k A : Type} [Field k] [CommRing A] [Algebra k A] {n : ℕ}
  (δ : Fin n → Derivation k A A) {ι : Type} [Fintype ι] (f : ι → A) {M : ℕ}
  (J : Finset (Fin M)) (i₀ : Fin M) (p₀ : ι)

abbrev Var (M : ℕ) (ι : Type) := (Fin M × ι) ⊕ (Fin M ⊕ Unit)

open MvPolynomial in

noncomputable def relIdeal : Ideal (MvPolynomial (Var M ι) A) :=
  Ideal.span {x | (∃ i ∈ J, x = ∑ p, X (Sum.inl (i, p)) * C (f p)) ∨
    (∃ l, x = ∑ i ∈ J, X (Sum.inr (Sum.inl i)) * ∑ p, X (Sum.inl (i, p)) * C (δ l (f p))) ∨
    x = X (Sum.inr (Sum.inl i₀)) - 1 ∨ x = X (Sum.inr (Sum.inr ())) * C (f p₀) - 1}

end Construction

open MvPolynomial in

/- English proof (translation)
Introduce `k A _ _ _ _ _ n δ ω hω ι _ f M J i₀ p₀ hi₀`. Use `set I := relIdeal δ f J i₀ p₀ with hIdef`. Set `T` to `MvPolynomial (Var M ι) A ⧸ I`. Set `gm : MvPolynomial (Fin M × ι) k →ₐ[k] T` to `aeval (fun x => Ideal.Quotient.mk I (X (Sum.inl x)))`. Establish `g1mem : ∀ i ∈ J, (∑ p, X (Sum.inl (i, p)) * C (f p) : MvPolynomial (Var M ι) A) ∈ I` using `fun i hi => Ideal.subset_span (Or.inl ⟨i, hi, rfl⟩)`.

Establish `g2mem : ∀ l, (∑ i ∈ J, X (Sum.inr (Sum.inl i)) * ∑ p, X (Sum.inl (i, p)) * C (δ l (f p)) : MvPolynomial (Var M ι) A) ∈ I` using `fun l => Ideal.subset_span (Or.inr (Or.inl ⟨l, rfl⟩))`. Establish `g3mem : (X (Sum.inr (Sum.inl i₀)) - 1 : MvPolynomial (Var M ι) A) ∈ I` using `Ideal.subset_span (Or.inr (Or.inr (Or.inl rfl)))`. Establish `g4mem : (X (Sum.inr (Sum.inr ())) * C (f p₀) - 1 : MvPolynomial (Var M ι) A) ∈ I` using `Ideal.subset_span (Or.inr (Or.inr (Or.inr rfl)))`. Establish `hni : ¬ Function.Injective gm`. Introduce `hinj`.

Set `S : Submonoid T` to `(nonZeroDivisors (MvPolynomial (Fin M × ι) k)).map gm`. Establish `hS : ∀ Q : MvPolynomial (Fin M × ι) k, Q ≠ 0 → gm Q ∈ S` using `fun Q hQ => Submonoid.mem_map_of_mem _ (mem_nonZeroDivisors_of_ne_zero hQ)`. Establish `hdisj : Disjoint ((⊥ : Ideal T) : Set T) S`. Rewrite using `[Set.disjoint_left]`. Introduce and unpack `x hx ⟨Q, hQ, rfl⟩`.

Establish `h0 : gm Q = 0` using `(Submodule.mem_bot _).1 hx`. Establish `: Q = 0` using `hinj (by rw [h0, map_zero])`. Conclude with `nonZeroDivisors.ne_zero hQ this`. Take `⟨𝔮, h𝔮, -, hd⟩` from `Ideal.exists_le_prime_disjoint ⊥ S hdisj`. Use `haveI := h𝔮`.

Set `D` to `T ⧸ 𝔮`. Set `κ` to `FractionRing D`. Set `π : MvPolynomial (Var M ι) A →+* κ` to `(algebraMap D κ).comp ((Ideal.Quotient.mk 𝔮).comp (Ideal.Quotient.mk I))`. Establish `hπC : ∀ a : A, π (C a) = algebraMap A κ a`. Introduce `a`.

Use `show algebraMap D κ (Ideal.Quotient.mk 𝔮 (Ideal.Quotient.mk I (C a))) = _`. Rewrite using `[IsScalarTower.algebraMap_apply A D κ]`. Both sides reduce to the same expression. Establish `hπI : ∀ x ∈ I, π x = 0`. Introduce `x hx`.

Use `show algebraMap D κ (Ideal.Quotient.mk 𝔮 (Ideal.Quotient.mk I x)) = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero, map_zero]`. Establish `ht : AlgebraicIndependent k (fun x : Fin M × ι => π (X (Sum.inl x)))`. Rewrite using `[algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]`. Introduce `Q hQ`.

Assume the negation of the conclusion as `hQ0`. Establish `heq : (aeval (fun x : Fin M × ι => π (X (Sum.inl x))) : MvPolynomial (Fin M × ι) k →ₐ[k] κ) = (IsScalarTower.toAlgHom k D κ).comp ((Ideal.Quotient.mkₐ k 𝔮).comp gm)`. Use extensionality with `x`. Simplify using `[π, gm]`. Rewrite `hQ` using `[heq]`.

Establish `h1 : Ideal.Quotient.mk 𝔮 (gm Q) = 0` using `(IsFractionRing.injective D κ) (hQ.trans (map_zero _).symm)`. Rewrite `h1` using `[Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Set.disjoint_left.1 hd h1 (hS Q hQ0)`. Apply `false_of_dependent_derivatives n δ ω hω f M J i₀ p₀ hi₀ _ ht (fun i => π (X (Sum.inr (Sum.inl i))))` to reduce the goal to its premises. Introduce `i hi`.

Use `hπI _ (g1mem i hi)` as an intermediate fact. Simplify `this` using `only [map_sum, map_mul, hπC]`. Introduce `l`. Use `hπI _ (g2mem l)` as an intermediate fact. Simplify `this` using `only [map_sum, map_mul, hπC]`.

Establish `h3 : π (X (Sum.inr (Sum.inl i₀)) - 1) = 0` using `hπI _ g3mem`. Rewrite `h3` using `[RingHom.map_sub, RingHom.map_one]`. Conclude with `h3`. Establish `h4` using `hπI _ g4mem`. Rewrite `h4` using `[RingHom.map_sub, RingHom.map_mul, hπC, RingHom.map_one]`.

Conclude with `h4`. Choose the witnesses or unpack the hypotheses as in `⟨Q, hQ0, hQ⟩ : ∃ Q, Q ≠ 0 ∧ gm Q = 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hni ((injective_iff_map_eq_zero gm).2 fun Q hQ => by_contra fun h => hcon Q h hQ)`.

Use `⟨Q, hQ0, ?_⟩` and prove the remaining obligations. Introduce `u hu K _ _ φ c hφ hc hrel hδ`. Set `e : MvPolynomial (Var M ι) A →+* K` to `eval₂Hom φ.toRingHom (Sum.elim (fun x => algebraMap k K (u x)) (Sum.elim c (fun _ => (φ (f p₀))⁻¹)))`. Establish `hI : I ≤ RingHom.ker e`. Rewrite using `[hIdef, relIdeal, Ideal.span_le]`.

Apply the tactic sequence `rintro x (⟨i, hi, rfl⟩ | ⟨l, rfl⟩ | rfl | rfl) <;> simp only [SetLike.mem_coe, RingHom.mem_ker]`. Use `hrel i hi` as an intermediate fact. Simplify `this` using `[e, map_sum, Algebra.smul_def]`. Use `hδ l` as an intermediate fact. Simplify `this` using `[e, map_sum, Algebra.smul_def]`.

Simplify using `[e, hc]`. Simplify using `[e, inv_mul_cancel₀ hφ]`. Set `e' : T →+* K` to `Ideal.Quotient.lift I e (fun a ha => hI ha)`. Establish `hcomp : e'.comp gm.toRingHom = (algebraMap k K).comp (eval u)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `a show e' (gm (C a)) = algebraMap k K (eval u (C a))`. Rewrite using `[MvPolynomial.aeval_C]`. Use `show e (algebraMap k (MvPolynomial (Var M ι) A) a) = _`. Rewrite using `[MvPolynomial.algebraMap_apply, eval₂Hom_C, eval_C]`. Conclude with `φ.commutes a`.

Introduce `x show e' (gm (X x)) = algebraMap k K (eval u (X x))`. Rewrite using `[MvPolynomial.aeval_X, eval_X]`. Use `show e (X (Sum.inl x)) = _`. Rewrite using `[eval₂Hom_X']`. Both sides reduce to the same expression.

Use `RingHom.congr_fun hcomp Q` as an intermediate fact. Simplify using `only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this`. Rewrite `this` using `[hQ, map_zero]`. Conclude with `hu ((algebraMap k K).injective (this.symm.trans (map_zero _).symm))`.
-/
theorem no_dependence_of_general : ∀ (k A : Type) [Field k] [CharZero k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (n : ℕ) (δ : Fin n → Derivation k A A) (ω : Fin n → KaehlerDifferential k A), (∀ a : A, KaehlerDifferential.D k A a = ∑ l, δ l a • ω l) → ∀ {ι : Type} [Fintype ι] (f : ι → A) (M : ℕ) (J : Finset (Fin M)) (i₀ : Fin M) (p₀ : ι), i₀ ∈ J → ∃ Q : MvPolynomial (Fin M × ι) k, Q ≠ 0 ∧ ∀ u : Fin M × ι → k, MvPolynomial.eval u Q ≠ 0 → ∀ (K : Type) [Field K] [Algebra k K] (φ : A →ₐ[k] K) (c : Fin M → K), φ (f p₀) ≠ 0 → c i₀ = 1 → (∀ i ∈ J, φ (∑ p, u (i, p) • f p) = 0) → ¬ ∀ l, ∑ i ∈ J, c i * φ (δ l (∑ p, u (i, p) • f p)) = 0 := by
  intro k A _ _ _ _ _ n δ ω hω ι _ f M J i₀ p₀ hi₀
  classical
  set I := relIdeal δ f J i₀ p₀ with hIdef
  let T := MvPolynomial (Var M ι) A ⧸ I
  let gm : MvPolynomial (Fin M × ι) k →ₐ[k] T :=
    aeval (fun x => Ideal.Quotient.mk I (X (Sum.inl x)))
  have g1mem : ∀ i ∈ J, (∑ p, X (Sum.inl (i, p)) * C (f p) : MvPolynomial (Var M ι) A) ∈ I :=
    fun i hi => Ideal.subset_span (Or.inl ⟨i, hi, rfl⟩)
  have g2mem : ∀ l, (∑ i ∈ J, X (Sum.inr (Sum.inl i)) * ∑ p, X (Sum.inl (i, p)) * C (δ l (f p)) :
      MvPolynomial (Var M ι) A) ∈ I :=
    fun l => Ideal.subset_span (Or.inr (Or.inl ⟨l, rfl⟩))
  have g3mem : (X (Sum.inr (Sum.inl i₀)) - 1 : MvPolynomial (Var M ι) A) ∈ I :=
    Ideal.subset_span (Or.inr (Or.inr (Or.inl rfl)))
  have g4mem : (X (Sum.inr (Sum.inr ())) * C (f p₀) - 1 : MvPolynomial (Var M ι) A) ∈ I :=
    Ideal.subset_span (Or.inr (Or.inr (Or.inr rfl)))
  have hni : ¬ Function.Injective gm := by
    intro hinj
    let S : Submonoid T := (nonZeroDivisors (MvPolynomial (Fin M × ι) k)).map gm
    have hS : ∀ Q : MvPolynomial (Fin M × ι) k, Q ≠ 0 → gm Q ∈ S := fun Q hQ =>
      Submonoid.mem_map_of_mem _ (mem_nonZeroDivisors_of_ne_zero hQ)
    have hdisj : Disjoint ((⊥ : Ideal T) : Set T) S := by
      rw [Set.disjoint_left]
      rintro x hx ⟨Q, hQ, rfl⟩
      have h0 : gm Q = 0 := (Submodule.mem_bot _).1 hx
      have : Q = 0 := hinj (by rw [h0, map_zero])
      exact nonZeroDivisors.ne_zero hQ this
    obtain ⟨𝔮, h𝔮, -, hd⟩ := Ideal.exists_le_prime_disjoint ⊥ S hdisj
    haveI := h𝔮
    let D := T ⧸ 𝔮
    let κ := FractionRing D
    let π : MvPolynomial (Var M ι) A →+* κ :=
      (algebraMap D κ).comp ((Ideal.Quotient.mk 𝔮).comp (Ideal.Quotient.mk I))
    have hπC : ∀ a : A, π (C a) = algebraMap A κ a := by
      intro a
      show algebraMap D κ (Ideal.Quotient.mk 𝔮 (Ideal.Quotient.mk I (C a))) = _
      rw [IsScalarTower.algebraMap_apply A D κ]
      rfl
    have hπI : ∀ x ∈ I, π x = 0 := by
      intro x hx
      show algebraMap D κ (Ideal.Quotient.mk 𝔮 (Ideal.Quotient.mk I x)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero, map_zero]
    have ht : AlgebraicIndependent k (fun x : Fin M × ι => π (X (Sum.inl x))) := by
      rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
      intro Q hQ
      by_contra hQ0
      have heq : (aeval (fun x : Fin M × ι => π (X (Sum.inl x))) :
          MvPolynomial (Fin M × ι) k →ₐ[k] κ) =
          (IsScalarTower.toAlgHom k D κ).comp ((Ideal.Quotient.mkₐ k 𝔮).comp gm) := by
        ext x
        simp [π, gm]
      rw [heq] at hQ
      have h1 : Ideal.Quotient.mk 𝔮 (gm Q) = 0 :=
        (IsFractionRing.injective D κ) (hQ.trans (map_zero _).symm)
      rw [Ideal.Quotient.eq_zero_iff_mem] at h1
      exact Set.disjoint_left.1 hd h1 (hS Q hQ0)
    apply false_of_dependent_derivatives n δ ω hω f M J i₀ p₀ hi₀ _ ht (fun i => π (X (Sum.inr (Sum.inl i))))
    · intro i hi
      have := hπI _ (g1mem i hi)
      simpa only [map_sum, map_mul, hπC] using this
    · intro l
      have := hπI _ (g2mem l)
      simpa only [map_sum, map_mul, hπC] using this
    · have h3 : π (X (Sum.inr (Sum.inl i₀)) - 1) = 0 := hπI _ g3mem
      rw [RingHom.map_sub, RingHom.map_one] at h3
      exact h3
    · have h4 := hπI _ g4mem
      rw [RingHom.map_sub, RingHom.map_mul, hπC, RingHom.map_one] at h4
      exact h4
  obtain ⟨Q, hQ0, hQ⟩ : ∃ Q, Q ≠ 0 ∧ gm Q = 0 := by
    by_contra hcon
    push_neg at hcon
    exact hni ((injective_iff_map_eq_zero gm).2 fun Q hQ => by_contra fun h => hcon Q h hQ)
  refine ⟨Q, hQ0, ?_⟩
  intro u hu K _ _ φ c hφ hc hrel hδ
  let e : MvPolynomial (Var M ι) A →+* K := eval₂Hom φ.toRingHom
    (Sum.elim (fun x => algebraMap k K (u x)) (Sum.elim c (fun _ => (φ (f p₀))⁻¹)))
  have hI : I ≤ RingHom.ker e := by
    rw [hIdef, relIdeal, Ideal.span_le]
    rintro x (⟨i, hi, rfl⟩ | ⟨l, rfl⟩ | rfl | rfl) <;> simp only [SetLike.mem_coe, RingHom.mem_ker]
    · have := hrel i hi
      simpa [e, map_sum, Algebra.smul_def] using this
    · have := hδ l
      simpa [e, map_sum, Algebra.smul_def] using this
    · simp [e, hc]
    · simp [e, inv_mul_cancel₀ hφ]
  let e' : T →+* K := Ideal.Quotient.lift I e (fun a ha => hI ha)
  have hcomp : e'.comp gm.toRingHom = (algebraMap k K).comp (eval u) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      show e' (gm (C a)) = algebraMap k K (eval u (C a))
      rw [MvPolynomial.aeval_C]
      show e (algebraMap k (MvPolynomial (Var M ι) A) a) = _
      rw [MvPolynomial.algebraMap_apply, eval₂Hom_C, eval_C]
      exact φ.commutes a
    · intro x
      show e' (gm (X x)) = algebraMap k K (eval u (X x))
      rw [MvPolynomial.aeval_X, eval_X]
      show e (X (Sum.inl x)) = _
      rw [eval₂Hom_X']
      rfl
  have := RingHom.congr_fun hcomp Q
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [hQ, map_zero] at this
  exact hu ((algebraMap k K).injective (this.symm.trans (map_zero _).symm))

end GlobalTheory.BertiniC
