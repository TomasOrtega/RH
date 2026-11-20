import Mathlib

namespace GlobalTheory

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨f, hf0, hfk⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, f v ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hf0 (LinearMap.ext h)`. Establish `hFi : ∀ (i : ℕ) (a : L) (w : V), (⇑F)^[i] (a • w) = (⇑s)^[i] a • (⇑F)^[i] w`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro a w`.

Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `a w`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hF]`. Establish `htr : ∀ w : V, F (∑ i ∈ Finset.range r, (⇑F)^[i] w) = ∑ i ∈ Finset.range r, (⇑F)^[i] w`.

Introduce `w`. Rewrite using `[map_sum]`. Establish `h1` using `Finset.sum_range_succ' (fun i => (⇑F)^[i] w) r`. Establish `h2` using `Finset.sum_range_succ (fun i => (⇑F)^[i] w) r`. Simplify using `only [Function.iterate_succ_apply'] at h1`.

Rewrite `h2` using `[hFr w]`. Rewrite `h1` using `[show (⇑F)^[0] w = w from rfl]`. Conclude with `add_right_cancel (h1.symm.trans h2)`. Set `χ : Fin r → (L →* L)` to `fun i => (((s : L →+* L) ^ (i : ℕ) : L →+* L) : L →* L)`. Establish `hχ : ∀ (i : Fin r) (a : L), χ i a = (⇑s)^[i] a`.

Introduce `i a`. Simplify using `[χ, RingHom.coe_pow]`. Establish `hinj : Function.Injective χ`. Introduce `i j hij`. Establish `key : ∀ (i j : Fin r), (i : ℕ) < j → χ i = χ j → False`.

Introduce `i j hlt he`. Take `⟨x, hx⟩` from `hsi ((j : ℕ) - i) (Nat.sub_pos_of_lt hlt) (by omega)`. Apply `hx` to reduce the goal to its premises. Establish `h3` using `congrArg (fun g : L →* L => g x) he`. Simplify using `only [hχ] at h3`.

Establish `hj : (j : ℕ) = (i : ℕ) + ((j : ℕ) - i)` using `by omega`. Rewrite `h3` using `[hj, Function.iterate_add_apply]`. Conclude with `((s.injective.iterate _) h3).symm`. Break down `lt_trichotomy (i : ℕ) j with h | h | h` into its components or cases. Conclude with `(key i j h hij).elim`.

Conclude with `Fin.ext h`. Conclude with `(key j i h hij.symm).elim`. Establish `hli` using `(linearIndependent_monoidHom L L).comp χ hinj`. Establish `hsum : ∑ i : Fin r, f ((⇑F)^[i] v) • (((fun g : L →* L => (g : L → L)) ∘ χ) i) = 0`. Use function extensionality and compare the values at `a`.

Establish `hfix : (∑ i ∈ Finset.range r, (⇑F)^[i] (a • v)) ∈ Submodule.span L {v | F v = v}` using `Submodule.subset_span (htr (a • v))`. Establish `h0` using `hfk hfix`. Rewrite `h0` using `[LinearMap.mem_ker, map_sum]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, hχ, Pi.zero_apply]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => f ((⇑F)^[i] v) * (⇑s)^[i] a)]`.

Rewrite using `[← h0]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hFi, map_smul, smul_eq_mul, mul_comm]`. Conclude with `hv ((Fintype.linearIndependent_iff.1 hli) (fun i => f ((⇑F)^[(i : ℕ)] v)) hsum ⟨0, hr⟩)`.
-/
theorem semilinear_fixed_span (L : Type) [Field L] (s : L ≃+* L) (r : ℕ) (hr : 0 < r)
    (hsr : ∀ x, (⇑s)^[r] x = x) (hsi : ∀ i, 0 < i → i < r → ∃ x, (⇑s)^[i] x ≠ x)
    (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (F : V →+ V)
    (hF : ∀ (a : L) (v : V), F (a • v) = s a • F v) (hFr : ∀ v, (⇑F)^[r] v = v) :
    Submodule.span L {v | F v = v} = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (LinearMap.ext h)

  have hFi : ∀ (i : ℕ) (a : L) (w : V), (⇑F)^[i] (a • w) = (⇑s)^[i] a • (⇑F)^[i] w := by
    intro i
    induction i with
    | zero => intro a w; simp
    | succ n ih =>
      intro a w
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih, hF]

  have htr : ∀ w : V, F (∑ i ∈ Finset.range r, (⇑F)^[i] w) = ∑ i ∈ Finset.range r, (⇑F)^[i] w := by
    intro w
    rw [map_sum]
    have h1 := Finset.sum_range_succ' (fun i => (⇑F)^[i] w) r
    have h2 := Finset.sum_range_succ (fun i => (⇑F)^[i] w) r
    simp only [Function.iterate_succ_apply'] at h1
    rw [hFr w] at h2
    rw [show (⇑F)^[0] w = w from rfl] at h1
    exact add_right_cancel (h1.symm.trans h2)

  let χ : Fin r → (L →* L) := fun i => (((s : L →+* L) ^ (i : ℕ) : L →+* L) : L →* L)
  have hχ : ∀ (i : Fin r) (a : L), χ i a = (⇑s)^[i] a := by
    intro i a
    simp [χ, RingHom.coe_pow]
  have hinj : Function.Injective χ := by
    intro i j hij
    have key : ∀ (i j : Fin r), (i : ℕ) < j → χ i = χ j → False := by
      intro i j hlt he
      obtain ⟨x, hx⟩ := hsi ((j : ℕ) - i) (Nat.sub_pos_of_lt hlt) (by omega)
      apply hx
      have h3 := congrArg (fun g : L →* L => g x) he
      simp only [hχ] at h3
      have hj : (j : ℕ) = (i : ℕ) + ((j : ℕ) - i) := by omega
      rw [hj, Function.iterate_add_apply] at h3
      exact ((s.injective.iterate _) h3).symm
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · exact (key i j h hij).elim
    · exact Fin.ext h
    · exact (key j i h hij.symm).elim
  have hli := (linearIndependent_monoidHom L L).comp χ hinj
  have hsum : ∑ i : Fin r, f ((⇑F)^[i] v) • (((fun g : L →* L => (g : L → L)) ∘ χ) i) = 0 := by
    funext a
    have hfix : (∑ i ∈ Finset.range r, (⇑F)^[i] (a • v)) ∈ Submodule.span L {v | F v = v} :=
      Submodule.subset_span (htr (a • v))
    have h0 := hfk hfix
    rw [LinearMap.mem_ker, map_sum] at h0
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, hχ,
      Pi.zero_apply]
    rw [Fin.sum_univ_eq_sum_range (fun i => f ((⇑F)^[i] v) * (⇑s)^[i] a)]
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hFi, map_smul, smul_eq_mul, mul_comm]
  exact hv ((Fintype.linearIndependent_iff.1 hli) (fun i => f ((⇑F)^[(i : ℕ)] v)) hsum ⟨0, hr⟩)

end GlobalTheory
