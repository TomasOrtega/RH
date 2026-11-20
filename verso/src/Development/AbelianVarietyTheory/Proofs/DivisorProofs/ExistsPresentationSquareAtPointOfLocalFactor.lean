import Mathlib
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `k A _ _ _ ε e he hidem ⟨s, φ, g', hφ, hker⟩ r a ha`. Use `choose y hy using fun i : Fin s => Ideal.Quotient.mk_surjective (I := Ideal.span {1 - e}) (φ (MvPolynomial.X i))`. Use `choose h hh using fun j : Fin r => hφ (Ideal.Quotient.mk (Ideal.span {1 - e}) (a j))`. Use `set Ψ : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A := MvPolynomial.aeval (Sum.elim y a) with hΨ`. Establish `hΨsurj : Function.Surjective Ψ`.

Introduce `x`. Take `⟨p, hp⟩` from `ha x`. Use `⟨MvPolynomial.rename Sum.inr p, ?_⟩` and prove the remaining obligations. Rewrite using `[hΨ, MvPolynomial.aeval_rename, Sum.elim_comp_inr]`. Conclude with `hp`.

Take `⟨u, hu⟩` from `hΨsurj e`. Use `set κ : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] MvPolynomial (Fin s) k := MvPolynomial.aeval (Sum.elim MvPolynomial.X h) with hκdef`. Establish `hκ : (Ideal.Quotient.mkₐ k (Ideal.span {1 - e})).comp Ψ = φ.comp κ`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`.

Break down `i with i | j` into its components or cases. Simplify using `[hΨ, hκdef, hy]`. Simplify using `[hΨ, hκdef, hh]`. Establish `hκF : ∀ F, Ideal.Quotient.mk (Ideal.span {1 - e}) (Ψ F) = φ (κ F)`. Introduce `F`.

Use `congrArg (fun f => f F) hκ` as an intermediate fact. Simplify using `using this`. Set `G : Fin s ⊕ Fin r → MvPolynomial (Fin s ⊕ Fin r) k` to `Sum.elim (fun i => MvPolynomial.rename Sum.inl (g' i)) (fun j => MvPolynomial.X (Sum.inr j) - MvPolynomial.rename Sum.inl (h j))`. Establish `hκr : ∀ p, κ (MvPolynomial.rename Sum.inl p) = p`. Introduce `p`.

Rewrite using `[hκdef, MvPolynomial.aeval_rename, Sum.elim_comp_inl, MvPolynomial.aeval_X_left_apply]`. Establish `hκX : ∀ j, κ (MvPolynomial.X (Sum.inr j)) = h j`. Introduce `j`. Rewrite using `[hκdef, MvPolynomial.aeval_X, Sum.elim_inr]`. Establish `hg'ker : ∀ i, φ (g' i) = 0`.

Introduce `i`. Establish `: g' i ∈ RingHom.ker φ` using `hker ▸ Ideal.subset_span ⟨i, rfl⟩`. Simplify using `using this`. Establish `hΨG : ∀ i, Ideal.Quotient.mk (Ideal.span {1 - e}) (Ψ (G i)) = 0`. Introduce `i`.

Rewrite using `[hκF]`. Break down `i with i | j` into its components or cases. Simplify using `only [G, Sum.elim_inl, hκr, hg'ker]`. Simplify using `only [G, Sum.elim_inr, map_sub, hκr, hκX, sub_self, map_zero]`. Establish `hΨuG : ∀ i, Ψ (u * G i) = 0`.

Introduce `i`. Establish `hm : Ψ (G i) ∈ Ideal.span {1 - e}` using `Ideal.Quotient.eq_zero_iff_mem.mp (hΨG i)`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp hm`. Rewrite using `[map_mul, hu, ← hc]`. Establish `h0 : e * (1 - e) = 0` using `by rw [mul_sub, mul_one, hidem.eq, sub_self]`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨s, y, fun i => u * G i, hΨuG, ?_⟩` and prove the remaining obligations. Rewrite using `[← hΨ]`. Introduce `F hF`. Rewrite `hF` using `[RingHom.mem_ker]`.

Establish `hFG : F ∈ Ideal.span (Set.range G)`. Establish `hq : (Ideal.Quotient.mkₐ k (Ideal.span (Set.range G))).comp ((MvPolynomial.rename Sum.inl).comp κ) = Ideal.Quotient.mkₐ k (Ideal.span (Set.range G))`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Break down `i with i | j` into its components or cases.

Simplify using `only [AlgHom.comp_apply, hκdef, MvPolynomial.aeval_X, Sum.elim_inl, MvPolynomial.rename_X]`. Simplify using `only [AlgHom.comp_apply, hκX, Ideal.Quotient.mkₐ_eq_mk]`. Rewrite using `[Ideal.Quotient.eq]`. Rewrite using `[← neg_sub, neg_mem_iff]`. Conclude with `Ideal.subset_span ⟨Sum.inr j, rfl⟩`.

Establish `h1 : F - MvPolynomial.rename Sum.inl (κ F) ∈ Ideal.span (Set.range G)`. Use `congrArg (fun f => f F) hq` as an intermediate fact. Simplify using `only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this`. Rewrite using `[← neg_sub, neg_mem_iff]`. Conclude with `Ideal.Quotient.eq.mp this`.

Establish `hmem : κ F ∈ Ideal.span (Set.range g')`. Rewrite using `[← hker, RingHom.mem_ker, ← hκF, hF, map_zero]`. Establish `h2 : MvPolynomial.rename Sum.inl (κ F) ∈ Ideal.span (Set.range G)`. Use `Ideal.mem_map_of_mem (MvPolynomial.rename (R := k) (Sum.inl : Fin s → Fin s ⊕ Fin r)) hmem` as an intermediate fact. Rewrite `this` using `[Ideal.map_span]`.

Use `Ideal.span_mono ?_ this` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, rfl⟩`. Conclude with `⟨Sum.inl i, rfl⟩`. Use `Ideal.add_mem _ h1 h2` as an intermediate fact. Simplify using `using this`.

Establish `hsplit : F = u * F + (1 - u) * F` using `by ring`. Rewrite using `[hsplit]`. Use `Submodule.add_mem_sup ?_ ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `(Ideal.mem_span_range_iff_exists_fun).mp hFG`. Use `(Ideal.mem_span_range_iff_exists_fun).mpr ⟨c, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hc, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Apply `Ideal.mul_mem_mul` to reduce the goal to its premises. Rewrite using `[RingHom.mem_ker]`.

Simplify using `[hu, he]`. Conclude with `hF`.
-/
theorem sqloc_present : ∀ (k A : Type) [CommRing k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k) (e : A), ε e = 1 → IsIdempotentElem e → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] (A ⧸ Ideal.span {1 - e})) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → ∀ (r : ℕ) (a : Fin r → A), Function.Surjective (MvPolynomial.aeval a : MvPolynomial (Fin r) k →ₐ[k] A) → ∃ (s : ℕ) (y : Fin s → A) (g : Fin s ⊕ Fin r → MvPolynomial (Fin s ⊕ Fin r) k), (∀ i, MvPolynomial.aeval (Sum.elim y a) (g i) = 0) ∧ RingHom.ker (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A) ≤ Ideal.span (Set.range g) ⊔ RingHom.ker (ε.comp (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A)) * RingHom.ker (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A) := by
  intro k A _ _ _ ε e he hidem ⟨s, φ, g', hφ, hker⟩ r a ha
  classical
  choose y hy using fun i : Fin s => Ideal.Quotient.mk_surjective (I := Ideal.span {1 - e}) (φ (MvPolynomial.X i))
  choose h hh using fun j : Fin r => hφ (Ideal.Quotient.mk (Ideal.span {1 - e}) (a j))
  set Ψ : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A := MvPolynomial.aeval (Sum.elim y a) with hΨ
  have hΨsurj : Function.Surjective Ψ := by
    intro x
    obtain ⟨p, hp⟩ := ha x
    refine ⟨MvPolynomial.rename Sum.inr p, ?_⟩
    rw [hΨ, MvPolynomial.aeval_rename, Sum.elim_comp_inr]
    exact hp
  obtain ⟨u, hu⟩ := hΨsurj e
  set κ : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] MvPolynomial (Fin s) k :=
    MvPolynomial.aeval (Sum.elim MvPolynomial.X h) with hκdef
  have hκ : (Ideal.Quotient.mkₐ k (Ideal.span {1 - e})).comp Ψ = φ.comp κ := by
    apply MvPolynomial.algHom_ext
    intro i
    rcases i with i | j
    · simp [hΨ, hκdef, hy]
    · simp [hΨ, hκdef, hh]
  have hκF : ∀ F, Ideal.Quotient.mk (Ideal.span {1 - e}) (Ψ F) = φ (κ F) := by
    intro F
    have := congrArg (fun f => f F) hκ
    simpa using this
  let G : Fin s ⊕ Fin r → MvPolynomial (Fin s ⊕ Fin r) k :=
    Sum.elim (fun i => MvPolynomial.rename Sum.inl (g' i))
      (fun j => MvPolynomial.X (Sum.inr j) - MvPolynomial.rename Sum.inl (h j))
  have hκr : ∀ p, κ (MvPolynomial.rename Sum.inl p) = p := by
    intro p
    rw [hκdef, MvPolynomial.aeval_rename, Sum.elim_comp_inl, MvPolynomial.aeval_X_left_apply]
  have hκX : ∀ j, κ (MvPolynomial.X (Sum.inr j)) = h j := by
    intro j
    rw [hκdef, MvPolynomial.aeval_X, Sum.elim_inr]
  have hg'ker : ∀ i, φ (g' i) = 0 := by
    intro i
    have : g' i ∈ RingHom.ker φ := hker ▸ Ideal.subset_span ⟨i, rfl⟩
    simpa using this
  have hΨG : ∀ i, Ideal.Quotient.mk (Ideal.span {1 - e}) (Ψ (G i)) = 0 := by
    intro i
    rw [hκF]
    rcases i with i | j
    · simp only [G, Sum.elim_inl, hκr, hg'ker]
    · simp only [G, Sum.elim_inr, map_sub, hκr, hκX, sub_self, map_zero]
  have hΨuG : ∀ i, Ψ (u * G i) = 0 := by
    intro i
    have hm : Ψ (G i) ∈ Ideal.span {1 - e} := Ideal.Quotient.eq_zero_iff_mem.mp (hΨG i)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hm
    rw [map_mul, hu, ← hc]
    have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hidem.eq, sub_self]
    calc e * (c * (1 - e)) = c * (e * (1 - e)) := by ring
      _ = 0 := by rw [h0, mul_zero]
  refine ⟨s, y, fun i => u * G i, hΨuG, ?_⟩
  rw [← hΨ]
  intro F hF
  rw [RingHom.mem_ker] at hF

  have hFG : F ∈ Ideal.span (Set.range G) := by
    have hq : (Ideal.Quotient.mkₐ k (Ideal.span (Set.range G))).comp
        ((MvPolynomial.rename Sum.inl).comp κ) = Ideal.Quotient.mkₐ k (Ideal.span (Set.range G)) := by
      apply MvPolynomial.algHom_ext
      intro i
      rcases i with i | j
      · simp only [AlgHom.comp_apply, hκdef, MvPolynomial.aeval_X, Sum.elim_inl,
          MvPolynomial.rename_X]
      · simp only [AlgHom.comp_apply, hκX, Ideal.Quotient.mkₐ_eq_mk]
        rw [Ideal.Quotient.eq]
        rw [← neg_sub, neg_mem_iff]
        exact Ideal.subset_span ⟨Sum.inr j, rfl⟩
    have h1 : F - MvPolynomial.rename Sum.inl (κ F) ∈ Ideal.span (Set.range G) := by
      have := congrArg (fun f => f F) hq
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
      rw [← neg_sub, neg_mem_iff]
      exact Ideal.Quotient.eq.mp this
    have hmem : κ F ∈ Ideal.span (Set.range g') := by
      rw [← hker, RingHom.mem_ker, ← hκF, hF, map_zero]
    have h2 : MvPolynomial.rename Sum.inl (κ F) ∈ Ideal.span (Set.range G) := by
      have := Ideal.mem_map_of_mem (MvPolynomial.rename (R := k) (Sum.inl : Fin s → Fin s ⊕ Fin r)) hmem
      rw [Ideal.map_span] at this
      refine Ideal.span_mono ?_ this
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨Sum.inl i, rfl⟩
    have := Ideal.add_mem _ h1 h2
    simpa using this
  have hsplit : F = u * F + (1 - u) * F := by ring
  rw [hsplit]
  refine Submodule.add_mem_sup ?_ ?_
  · obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hFG
    refine (Ideal.mem_span_range_iff_exists_fun).mpr ⟨c, ?_⟩
    rw [← hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · apply Ideal.mul_mem_mul
    · rw [RingHom.mem_ker]
      simp [hu, he]
    · exact hF

end GlobalTheory
