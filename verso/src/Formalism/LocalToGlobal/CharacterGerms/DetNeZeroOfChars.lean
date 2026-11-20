import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrPl

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl

section Chars

variable {F A L : Type} [CommRing F] [CommRing A] [Algebra F A] [Field L] {ι' ι : Type} [Fintype ι'] [Fintype ι]

/- English proof (translation)
Establish `key : ∀ x : A, ∑ j, c j * χ j x = 0`. Introduce `x`. Take `⟨r, hr⟩` from `hb x`. Establish `hx : ∀ j, χ j x = ∑ i, φ (r i) * χ j (b i)`. Introduce `j`.

Establish `h1 : χ j (e * x) = χ j x` using `by rw [map_mul, he, one_mul]`. Rewrite using `[← h1, hr, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, hφ]`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hx j, Finset.mul_sum]`. Use `_ = ∑ i, φ (r i) * ∑ j, c j * χ j (b i) := by`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ = 0 := by simp [hc]`. Establish `hli : LinearIndependent L (fun j => ((χ j).toMonoidHom : A → L))`.

Establish `h` using `(linearIndependent_monoidHom A L).comp (fun j => (χ j).toMonoidHom) (by`. Introduce `j k hjk`. Apply `hχ` to reduce the goal to its premises. Use extensionality with `x`. Conclude with `DFunLike.congr_fun hjk x)`.

Conclude with `h`. Use function extensionality and compare the values at `j`. Establish `h2` using `Fintype.linearIndependent_iff.mp hli c (by`. Use function extensionality and compare the values at `x`. Rewrite using `[Finset.sum_apply]`.

Conclude with `key x)`. Conclude with `h2 j`.
-/
theorem char_indep (χ : ι' → A →+* L) (hχ : Function.Injective χ) (φ : F →+* L)
    (hφ : ∀ j r, χ j (algebraMap F A r) = φ r) (e : A) (he : ∀ j, χ j e = 1) (b : ι → A)
    (hb : ∀ x : A, ∃ r : ι → F, e * x = ∑ i, r i • b i) (c : ι' → L) (hc : ∀ i, ∑ j, c j * χ j (b i) = 0) :
    c = 0 := by
  have key : ∀ x : A, ∑ j, c j * χ j x = 0 := by
    intro x
    obtain ⟨r, hr⟩ := hb x
    have hx : ∀ j, χ j x = ∑ i, φ (r i) * χ j (b i) := by
      intro j
      have h1 : χ j (e * x) = χ j x := by rw [map_mul, he, one_mul]
      rw [← h1, hr, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, hφ]
    calc ∑ j, c j * χ j x = ∑ j, ∑ i, c j * (φ (r i) * χ j (b i)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hx j, Finset.mul_sum]
      _ = ∑ i, φ (r i) * ∑ j, c j * χ j (b i) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = 0 := by simp [hc]
  have hli : LinearIndependent L (fun j => ((χ j).toMonoidHom : A → L)) := by
    have h := (linearIndependent_monoidHom A L).comp (fun j => (χ j).toMonoidHom) (by
      intro j k hjk
      apply hχ
      ext x
      exact DFunLike.congr_fun hjk x)
    exact h
  funext j
  have h2 := Fintype.linearIndependent_iff.mp hli c (by
    funext x
    rw [Finset.sum_apply]
    exact key x)
  exact h2 j

/- English proof (translation)
Establish `hli : LinearIndependent L (fun j : ι' => fun i : ι => χ j (b i))`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `h0` using `char_indep χ hχ φ hφ e he b hb g (fun i => by`. Establish `h3` using `congrFun hg i`.

Rewrite `h3` using `[Finset.sum_apply]`. Conclude with `h3)`. Introduce `j`. Simplify using `[h0]`. Simplify using `using hli.fintype_card_le_finrank`.
-/
theorem card_le_of_chars (χ : ι' → A →+* L) (hχ : Function.Injective χ) (φ : F →+* L)
    (hφ : ∀ j r, χ j (algebraMap F A r) = φ r) (e : A) (he : ∀ j, χ j e = 1) (b : ι → A)
    (hb : ∀ x : A, ∃ r : ι → F, e * x = ∑ i, r i • b i) : Fintype.card ι' ≤ Fintype.card ι := by
  have hli : LinearIndependent L (fun j : ι' => fun i : ι => χ j (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 := char_indep χ hχ φ hφ e he b hb g (fun i => by
      have h3 := congrFun hg i
      rw [Finset.sum_apply] at h3
      exact h3)
    intro j
    simp [h0]
  simpa using hli.fintype_card_le_finrank

/- English proof (translation)
Introduce `hdet`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Apply `hv0` to reduce the goal to its premises. Apply `char_indep χ hχ φ hφ e he b hb v` to reduce the goal to its premises. Introduce `i`.

Establish `h` using `congrFun hv i`. Combine the equalities or inequalities in the displayed calculation. Consider the case `exact h`. Consider the case `simpa [Matrix.mulVec, dotProduct] using h`.
-/
theorem det_ne_zero_of_chars [DecidableEq ι] (χ : ι → A →+* L) (hχ : Function.Injective χ) (φ : F →+* L)
    (hφ : ∀ j r, χ j (algebraMap F A r) = φ r) (e : A) (he : ∀ j, χ j e = 1) (b : ι → A)
    (hb : ∀ x : A, ∃ r : ι → F, e * x = ∑ i, r i • b i) : (Matrix.of fun i j => χ j (b i)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  apply char_indep χ hχ φ hφ e he b hb v
  intro i
  have h := congrFun hv i
  calc ∑ j, v j * χ j (b i) = ∑ j, χ j (b i) * v j :=
        Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = 0 := by
        first
        | exact h
        | simpa [Matrix.mulVec, dotProduct] using h

end Chars

section Label

/- English proof (translation)
Assemble the required witnesses or components as `⟨(ZMod.finEquiv d).symm.toEquiv, fun a => by first | simp | (show (ZMod.finEquiv d).symm (a + 1) = (ZMod.finEquiv d).symm a + 1 rw [map_add, map_one])⟩`.
-/
theorem exists_jj (d : ℕ) [NeZero d] : ∃ jj : ZMod d ≃ Fin d, ∀ a, jj (a + 1) = jj a + 1 := ⟨(ZMod.finEquiv d).symm.toEquiv, fun a => by
  first
  | simp
  | (show (ZMod.finEquiv d).symm (a + 1) = (ZMod.finEquiv d).symm a + 1
     rw [map_add, map_one])⟩

/- English proof (translation)
Substitute `n` using the available equality. Take `⟨jj, hjj⟩` from `exists_jj d`. Set `e : ZMod d ≃ Emb` to `Equiv.ofBijective (fun a => (⟨em a, hmem a⟩ : Emb)) ⟨fun a a' h => hinj (congrArg Subtype.val h), fun τ => by`. Take `⟨a, ha⟩` from `hsurj τ τ.2`. Conclude with `⟨a, Subtype.ext ha.symm⟩⟩`.

Use `⟨inferInstance, jj.symm.trans e, jj, hjj, fun a => ?_⟩` and prove the remaining obligations. Use `show ((e (jj.symm (jj a)) : Emb) : X) = em a`. Rewrite using `[Equiv.symm_apply_apply]`. Both sides reduce to the same expression.
-/
theorem assemble {X : Type} {d : ℕ} [NeZero d] (n : ℕ) (hn : n = d) (Emb : Set X) (em : ZMod d → X)
    (hinj : Function.Injective em) (hmem : ∀ a, em a ∈ Emb) (hsurj : ∀ τ ∈ Emb, ∃ a, τ = em a) :
    ∃ (_ : NeZero n) (t : Fin n ≃ Emb) (jj : ZMod d ≃ Fin n),
      (∀ a, jj (a + 1) = jj a + 1) ∧ ∀ a, ((t (jj a) : Emb) : X) = em a := by
  subst n
  obtain ⟨jj, hjj⟩ := exists_jj d
  let e : ZMod d ≃ Emb := Equiv.ofBijective (fun a => (⟨em a, hmem a⟩ : Emb))
    ⟨fun a a' h => hinj (congrArg Subtype.val h), fun τ => by
      obtain ⟨a, ha⟩ := hsurj τ τ.2
      exact ⟨a, Subtype.ext ha.symm⟩⟩
  refine ⟨inferInstance, jj.symm.trans e, jj, hjj, fun a => ?_⟩
  show ((e (jj.symm (jj a)) : Emb) : X) = em a
  rw [Equiv.symm_apply_apply]
  rfl

end Label

end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
