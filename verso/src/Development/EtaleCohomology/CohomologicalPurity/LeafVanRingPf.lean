import Development.EtaleCohomology.CohomologicalPurity.LeafClCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Cl

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p r hp hr`. Establish `: p + r - MvPolynomial.C (MvPolynomial.constantCoeff (p + r)) = (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) + (r - MvPolynomial.C (MvPolynomial.constantCoeff r))`. Simplify using `only [map_add]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `add_mem hp hr`. Consider the case `mul_X p n _`. Simplify using `only [map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero, sub_zero]`.

Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨n, rfl⟩)`.
-/
theorem sub_C_mem_X {σ R : Type} [CommRing R] (f : MvPolynomial σ R) :
    f - MvPolynomial.C (MvPolynomial.constantCoeff f) ∈ Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ R)) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr =>
    have : p + r - MvPolynomial.C (MvPolynomial.constantCoeff (p + r)) =
      (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) + (r - MvPolynomial.C (MvPolynomial.constantCoeff r)) := by
      simp only [map_add]; ring
    rw [this]; exact add_mem hp hr
  | mul_X p n _ =>
    simp only [map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero, sub_zero]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨n, rfl⟩)

/- English proof (translation)
Use `⟨hψ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `f hf`. Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective f`. Rewrite `hf` using `[Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem, hJ]`.

Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (MvPolynomial.constantCoeff f)`. Establish `h1 : ψ (f - MvPolynomial.C (MvPolynomial.constantCoeff f)) ∈ I.map φ`. Rewrite using `[← hJ]`. Conclude with `Ideal.mem_map_of_mem _ (sub_C_mem_X f)`. Establish `h2 : φ a ∈ I.map φ`.

Use `sub_mem (add_mem (hc a) (sub_mem hf h1)) (0 : I.map φ).2` as an intermediate fact. Rewrite `this` using `[map_sub, ← ha]`. Simplify using `using this`. Establish `h3 : Ideal.Quotient.mk I a = 0`. Apply `hφ.2.1` to reduce the goal to its premises.

Rewrite using `[Ideal.quotientMap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `h2`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`. Use `sub_C_mem_X f` as an intermediate fact. Rewrite `this` using `[← ha, h3, map_zero, sub_zero]`. Then use the resulting hypothesis.

Introduce `b`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Take `⟨a', ha'⟩` from `hφ.2.2 (Ideal.Quotient.mk _ b)`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a'`. Use `⟨Ideal.Quotient.mk _ (MvPolynomial.C (Ideal.Quotient.mk I a)), ?_⟩` and prove the remaining obligations.

Rewrite `ha'`, the goal using `[Ideal.quotientMap_mk]`. Rewrite `ha'`, the goal using `[Ideal.Quotient.eq]`. Rewrite using `[hJ]`. Use `sub_mem ha' (hc a)` as an intermediate fact. Simplify using `using this`.
-/
theorem chart_nbhd {d : ℕ} {A B : Type} [CommRing A] [CommRing B] (I : Ideal A) (φ : A →+* B)
    (ψ : MvPolynomial (Fin d) (A ⧸ I) →+* B) (hφ : Nbhd φ I) (hψ : ψ.Etale)
    (hJ : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (A ⧸ I)))).map ψ = I.map φ)
    (hc : ∀ a : A, φ a - ψ (MvPolynomial.C (Ideal.Quotient.mk I a)) ∈ I.map φ) :
    Nbhd ψ (Ideal.span (Set.range MvPolynomial.X)) := by
  refine ⟨hψ, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro f hf
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem, hJ] at hf
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (MvPolynomial.constantCoeff f)
    have h1 : ψ (f - MvPolynomial.C (MvPolynomial.constantCoeff f)) ∈ I.map φ := by
      rw [← hJ]; exact Ideal.mem_map_of_mem _ (sub_C_mem_X f)
    have h2 : φ a ∈ I.map φ := by
      have := sub_mem (add_mem (hc a) (sub_mem hf h1)) (0 : I.map φ).2
      rw [map_sub, ← ha] at this
      simpa using this
    have h3 : Ideal.Quotient.mk I a = 0 := by
      apply hφ.2.1
      rw [Ideal.quotientMap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact h2
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have := sub_C_mem_X f
    rwa [← ha, h3, map_zero, sub_zero] at this
  · intro b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨a', ha'⟩ := hφ.2.2 (Ideal.Quotient.mk _ b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
    refine ⟨Ideal.Quotient.mk _ (MvPolynomial.C (Ideal.Quotient.mk I a)), ?_⟩
    rw [Ideal.quotientMap_mk] at ha' ⊢
    rw [Ideal.Quotient.eq] at ha' ⊢
    rw [hJ]
    have := sub_mem ha' (hc a)
    simpa using this

/- English proof (translation)
Introduce `hH d q _ A _ I hC hq n i hn`. Establish `hA1 : A1` using `hH.1`. Establish `hA9 : A9` using `hH.2.2.2.2.2.2.1`. Take `⟨B, _, φ, ψ, hφ, hψ, hI, hc⟩` from `hC`. Establish `hJ : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (A ⧸ I)))).map ψ = I.map φ`.

Rewrite using `[Ideal.map_span, hI, ← Set.range_comp]`. Both sides reduce to the same expression. Establish `hN` using `chart_nbhd I φ ψ hφ hψ hJ hc`. Establish `e1` using `hNb hA1 q φ I (I.map φ) hφ rfl (off_map φ I).le n i`. Establish `e2` using `hNb hA1 q ψ _ _ hN rfl (off_map ψ _).le n i`.

Take `⟨th, hth⟩` from `hTh hH d`. Establish `hqR : IsUnit (q : A ⧸ I)` using `by simpa using hq.map (Ideal.Quotient.mk I)`. Take `⟨m, rfl⟩ : ∃ m, n = m + 2 * d` from `⟨n - 2 * d, by ring⟩`. Take `⟨j, rfl⟩ : ∃ j, i = j + d` from `⟨i - d, by ring⟩`. Establish `hm : m < 0` using `by omega`.

Establish `hsub : Subsingleton (Ht q (sp (A ⧸ I)) m j)` using `(hA9 (ZMod q) (tw q j)).1 _ m hm`. Establish `h3` using `((hth q).2.2.1 (A ⧸ I) _ rfl hqR m j).2`. Establish `hR : Subsingleton (Hs q (opn (off (MvPolynomial (Fin d) (A ⧸ I)) (Ideal.span (Set.range MvPolynomial.X)))) (m + 2 * d) (j + d))` using `by constructor; intro x y`. Take `⟨a, rfl⟩` from `h3 x`. Take `⟨b, rfl⟩` from `h3 y`.

Rewrite using `[Subsingleton.elim a b]`. Establish `hB : ∀ x y : Hs q (opn (off B ((Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (A ⧸ I)))).map ψ))) (m + 2 * d) (j + d), x = y`. Introduce `x y`. Take `⟨a, rfl⟩` from `e2.2 x`. Take `⟨b, rfl⟩` from `e2.2 y`.

Rewrite using `[Subsingleton.elim a b]`. Rewrite `hB` using `[hJ]`. Conclude with `⟨fun x y => e1.1 (hB _ _)⟩`.
-/
theorem LeafVanRing_of (hNb : LeafNb) (hTh : LeafThom) : LeafVanRing := by
  intro hH d q _ A _ I hC hq n i hn
  have hA1 : A1 := hH.1
  have hA9 : A9 := hH.2.2.2.2.2.2.1
  obtain ⟨B, _, φ, ψ, hφ, hψ, hI, hc⟩ := hC
  have hJ : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (A ⧸ I)))).map ψ = I.map φ := by
    rw [Ideal.map_span, hI, ← Set.range_comp]; rfl
  have hN := chart_nbhd I φ ψ hφ hψ hJ hc
  have e1 := hNb hA1 q φ I (I.map φ) hφ rfl (off_map φ I).le n i
  have e2 := hNb hA1 q ψ _ _ hN rfl (off_map ψ _).le n i
  obtain ⟨th, hth⟩ := hTh hH d
  have hqR : IsUnit (q : A ⧸ I) := by simpa using hq.map (Ideal.Quotient.mk I)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 * d := ⟨n - 2 * d, by ring⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + d := ⟨i - d, by ring⟩
  have hm : m < 0 := by omega
  have hsub : Subsingleton (Ht q (sp (A ⧸ I)) m j) := (hA9 (ZMod q) (tw q j)).1 _ m hm
  have h3 := ((hth q).2.2.1 (A ⧸ I) _ rfl hqR m j).2
  have hR : Subsingleton (Hs q (opn (off (MvPolynomial (Fin d) (A ⧸ I))
      (Ideal.span (Set.range MvPolynomial.X)))) (m + 2 * d) (j + d)) := by
    constructor; intro x y
    obtain ⟨a, rfl⟩ := h3 x; obtain ⟨b, rfl⟩ := h3 y; rw [Subsingleton.elim a b]
  have hB : ∀ x y : Hs q (opn (off B ((Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (A ⧸ I)))).map ψ))) (m + 2 * d) (j + d), x = y := by
    intro x y
    obtain ⟨a, rfl⟩ := e2.2 x; obtain ⟨b, rfl⟩ := e2.2 y; rw [Subsingleton.elim a b]
  rw [hJ] at hB
  exact ⟨fun x y => e1.1 (hB _ _)⟩

end LateralTheory.CohomologicalPurity.Cl
