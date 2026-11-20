import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryLocalPointEqMapRational

noncomputable section

open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2

namespace GlobalTheory.CompanionTheory.EllLoc

/- English proof (translation)
Rewrite using `[Polynomial.map_mul, Polynomial.map_C, h, Polynomial.coeff_map]`.
-/
theorem map_csr_left {K L : Type} [Field K] [Field L] (φ : K →+* L) (c : K →+* K) (c' : L →+* L)
    (h : ∀ x, φ (c x) = c' (φ x)) (P : K[X]) :
    (C (c (P.coeff 0)) * P).map φ = C (c' ((P.map φ).coeff 0)) * P.map φ := by
  rw [Polynomial.map_mul, Polynomial.map_C, h, Polynomial.coeff_map]

/- English proof (translation)
Establish `hcomp : φ.comp c = c'.comp φ` using `RingHom.ext h`. Establish `hd : (P.map c).natDegree = ((P.map φ).map c').natDegree`. Rewrite using `[Polynomial.natDegree_map, Polynomial.natDegree_map, Polynomial.natDegree_map]`. Rewrite using `[Polynomial.reverse, Polynomial.reverse, ← hd, ← Polynomial.reflect_map, Polynomial.map_map, hcomp, ← Polynomial.map_map]`.
-/
theorem map_csr_right {K L : Type} [Field K] [Field L] (φ : K →+* L) (c : K →+* K) (c' : L →+* L)
    (h : ∀ x, φ (c x) = c' (φ x)) (P : K[X]) :
    ((P.map c).reverse).map φ = ((P.map φ).map c').reverse := by
  have hcomp : φ.comp c = c'.comp φ := RingHom.ext h
  have hd : (P.map c).natDegree = ((P.map φ).map c').natDegree := by
    rw [Polynomial.natDegree_map, Polynomial.natDegree_map, Polynomial.natDegree_map]
  rw [Polynomial.reverse, Polynomial.reverse, ← hd, ← Polynomial.reflect_map, Polynomial.map_map, hcomp,
    ← Polynomial.map_map]

/- English proof (translation)
Establish `hmul : starRingEnd ℂ a * a = 1`. Rewrite using `[mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]`. Simplify using the standard rewrite rules. Rewrite using `[Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.reverse, Polynomial.natDegree_X_sub_C, Polynomial.reflect_sub, Polynomial.reflect_C]`. Establish `hX : reflect 1 (X : ℂ[X]) = 1`.

Simplify `Polynomial.reflect_monomial (R := ℂ) 1 1` using `[revAt]`. Rewrite using `[hX]`. Simplify using `only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, map_neg, C_neg, pow_one]`. Establish `: (C (starRingEnd ℂ a) * C a : ℂ[X]) = 1` using `by rw [← C_mul, hmul, C_1]`. Take the linear combination `this`.
-/
theorem csr_linear (a : ℂ) (ha : ‖a‖ = 1) :
    C (starRingEnd ℂ ((X - C a : ℂ[X]).coeff 0)) * (X - C a) = ((X - C a : ℂ[X]).map (starRingEnd ℂ)).reverse := by
  have hmul : starRingEnd ℂ a * a = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]; simp
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.reverse, Polynomial.natDegree_X_sub_C,
    Polynomial.reflect_sub, Polynomial.reflect_C]
  have hX : reflect 1 (X : ℂ[X]) = 1 := by
    simpa [revAt] using Polynomial.reflect_monomial (R := ℂ) 1 1
  rw [hX]
  simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, map_neg, C_neg, pow_one]
  have : (C (starRingEnd ℂ a) * C a : ℂ[X]) = 1 := by rw [← C_mul, hmul, C_1]
  linear_combination this

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp [Polynomial.reverse]`. Consider the case `cons a s ih`. Establish `h1` using `csr_linear a (hs a (Multiset.mem_cons_self a s))`. Establish `h2` using `ih fun z hz => hs z (Multiset.mem_cons_of_mem hz)`.

Rewrite using `[Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul, Polynomial.reverse_mul_of_domain, ← h1, ← h2, Polynomial.mul_coeff_zero, map_mul, C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem csr_prod (s : Multiset ℂ) (hs : ∀ z ∈ s, ‖z‖ = 1) :
    C (starRingEnd ℂ ((s.map fun a => (X - C a : ℂ[X])).prod.coeff 0)) * (s.map fun a => (X - C a : ℂ[X])).prod =
      ((s.map fun a => (X - C a : ℂ[X])).prod.map (starRingEnd ℂ)).reverse := by
  induction s using Multiset.induction_on with
  | empty => simp [Polynomial.reverse]
  | cons a s ih =>
    have h1 := csr_linear a (hs a (Multiset.mem_cons_self a s))
    have h2 := ih fun z hz => hs z (Multiset.mem_cons_of_mem hz)
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul, Polynomial.reverse_mul_of_domain, ← h1, ← h2,
      Polynomial.mul_coeff_zero, map_mul, C_mul]
    ring

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Use `set σ : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom with hσ`. Establish `hτ : ∀ x, τ (σ x) = starRingEnd ℂ (τ x)` using `fun x => IsCMField.complexEmbedding_complexConj E τ x`. Establish `hQ : (P.map τ).Monic` using `hP.1.map τ`. Establish `hroots : (P.map τ) = ((P.map τ).roots.map fun a => (X - C a : ℂ[X])).prod` using `(IsAlgClosed.splits (P.map τ)).eq_prod_roots_of_monic hQ`.

Establish `key` using `csr_prod (P.map τ).roots (hP.2.2.2 τ)`. Rewrite `key` using `[← hroots]`. Apply `Polynomial.map_injective τ τ.injective` to reduce the goal to its premises. Establish `e1` using `map_csr_left τ σ (starRingEnd ℂ) hτ P`. Establish `e2` using `map_csr_right τ σ (starRingEnd ℂ) hτ P`.

Rewrite using `[e2, ← key, ← e1]`. Both sides reduce to the same expression.
-/
theorem csr_global {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {P : E[X]} (hP : P ∈ Ell E n) :
    C (IsCMField.complexConj E (P.coeff 0)) * P = (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).reverse := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  set σ : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom with hσ
  have hτ : ∀ x, τ (σ x) = starRingEnd ℂ (τ x) := fun x => IsCMField.complexEmbedding_complexConj E τ x
  have hQ : (P.map τ).Monic := hP.1.map τ
  have hroots : (P.map τ) = ((P.map τ).roots.map fun a => (X - C a : ℂ[X])).prod :=
    (IsAlgClosed.splits (P.map τ)).eq_prod_roots_of_monic hQ
  have key := csr_prod (P.map τ).roots (hP.2.2.2 τ)
  rw [← hroots] at key
  apply Polynomial.map_injective τ τ.injective
  have e1 := map_csr_left τ σ (starRingEnd ℂ) hτ P
  have e2 := map_csr_right τ σ (starRingEnd ℂ) hτ P
  rw [e2, ← key, ← e1]
  rfl

/- English proof (translation)
Distinguish the cases in `hs : IsSplitAt w`. Conclude with `Or.inl hs`. Use `right`. Establish `hc : ∀ x, algebraMap E (w.adicCompletion E) ((IsCMField.complexConj E).toRingEquiv.toRingHom x) = cj w (algebraMap E (w.adicCompletion E) x)` using `fun x => (GlobalTheory.BCT.LocVal.cj_algebraMap w hs x).symm`. Establish `e1` using `map_csr_left (algebraMap E (w.adicCompletion E)) _ (cj w) hc P`.

Establish `e2` using `map_csr_right (algebraMap E (w.adicCompletion E)) _ (cj w) hc P`. Rewrite using `[atPl, ← e1, ← e2, ← csr_global hP]`. Both sides reduce to the same expression.
-/
theorem csr_at {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {P : E[X]} (hP : P ∈ Ell E n) (w : Pl E) :
    IsCsr w (atPl w P) := by
  by_cases hs : IsSplitAt w
  · exact Or.inl hs
  right
  have hc : ∀ x, algebraMap E (w.adicCompletion E) ((IsCMField.complexConj E).toRingEquiv.toRingHom x) =
      cj w (algebraMap E (w.adicCompletion E) x) := fun x => (GlobalTheory.BCT.LocVal.cj_algebraMap w hs x).symm
  have e1 := map_csr_left (algebraMap E (w.adicCompletion E)) _ (cj w) hc P
  have e2 := map_csr_right (algebraMap E (w.adicCompletion E)) _ (cj w) hc P
  rw [atPl, ← e1, ← e2, ← csr_global hP]
  rfl

/- English proof (translation)
Introduce `E _ _ _ a b p₁ p₂ h₁ h₂ hc w`. Establish `hm₁ : (atPl w p₁).Monic` using `h₁.1.map _`. Establish `hm₂ : (atPl w p₂).Monic` using `h₂.1.map _`. Use `⟨hm₁, hm₂, ?_, ?_, ?_, csr_at h₁ w, csr_at h₂ w⟩` and prove the remaining obligations. Rewrite using `[atPl, Polynomial.natDegree_map]`.

Conclude with `h₁.2.1`. Rewrite using `[atPl, Polynomial.natDegree_map]`. Conclude with `h₂.2.1`. Establish `hs : (p₁ * p₂).Separable` using `h₁.2.2.1.mul h₂.2.2.1 hc`. Use `hs.map (f := algebraMap E (w.adicCompletion E))` as an intermediate fact.

Rewrite `this` using `[Polynomial.map_mul]`. Then use the resulting hypothesis.
-/
theorem ellLocal : EllLocal := by
  intro E _ _ _ a b p₁ p₂ h₁ h₂ hc w
  have hm₁ : (atPl w p₁).Monic := h₁.1.map _
  have hm₂ : (atPl w p₂).Monic := h₂.1.map _
  refine ⟨hm₁, hm₂, ?_, ?_, ?_, csr_at h₁ w, csr_at h₂ w⟩
  · rw [atPl, Polynomial.natDegree_map]; exact h₁.2.1
  · rw [atPl, Polynomial.natDegree_map]; exact h₂.2.1
  · have hs : (p₁ * p₂).Separable := h₁.2.2.1.mul h₂.2.2.1 hc
    have := hs.map (f := algebraMap E (w.adicCompletion E))
    rwa [Polynomial.map_mul] at this

end GlobalTheory.CompanionTheory.EllLoc

end
