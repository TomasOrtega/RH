import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def dmap (W : Ideal (MRing ι)) (i : ∀ k, ι k) (a : K → ℕ) : mPiece W a → MRing ι ⧸ dehomI W i :=
  fun x => Ideal.Quotient.factor (le_sup_left : W ≤ dehomI W i) x.1

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Proceed by induction. Treat this case separately.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Separate the alternatives or extract the components of the hypothesis. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. A detailed English derivation is pending.
-/
theorem dmap_injective {W : Ideal (MRing ι)} (hWp : W.IsPrime) (hWm : IsMultiHomogIdeal W)
    {i : ∀ k, ι k} (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ W) (a : K → ℕ) :
    Function.Injective (dmap W i a) := by
  classical
  have homog_of_mem : ∀ {b : K → ℕ} {f : MRing ι}, f ∈ mHom ι b → IsMultiHomog f b := by
    intro b f hf
    unfold mHom at hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact hx
    | zero =>
      intro m hm
      simp at hm
    | add x y _ _ hx hy =>
      intro m hm k
      rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
      · exact hx m h k
      · exact hy m h k
    | smul n x _ hx =>
      intro m hm k
      exact hx m (MvPolynomial.support_smul hm) k
  rintro ⟨_, s, hs, rfl⟩ ⟨_, t, ht, rfl⟩ hxy
  have hd : Ideal.Quotient.mk (dehomI W i) s = Ideal.Quotient.mk (dehomI W i) t := hxy
  have hsub : s - t ∈ dehomI W i := Ideal.Quotient.eq.1 hd
  have hW := mem_of_mem_dehomI hWp hWm hi (homog_of_mem (Submodule.sub_mem _ hs ht)) hsub
  apply Subtype.ext
  exact Ideal.Quotient.eq.2 hW

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Proceed by induction. Treat this case separately.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Separate the alternatives or extract the components of the hypothesis. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem dmap_mono (W : Ideal (MRing ι)) (i : ∀ k, ι k) {a a' : K → ℕ} (h : ∀ k, a k ≤ a' k)
    (x : mPiece W a) : ∃ x' : mPiece W a', dmap W i a' x' = dmap W i a x := by
  classical
  have homog_of_mem : ∀ {b : K → ℕ} {f : MRing ι}, f ∈ mHom ι b → IsMultiHomog f b := by
    intro b f hf
    unfold mHom at hf
    induction hf using Submodule.span_induction with
    | mem x hx => exact hx
    | zero =>
      intro m hm
      simp at hm
    | add x y _ _ hx hy =>
      intro m hm k
      rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
      · exact hx m h k
      · exact hy m h k
    | smul n x _ hx =>
      intro m hm k
      exact hx m (MvPolynomial.support_smul hm) k
  obtain ⟨_, s, hs, rfl⟩ := x
  have hprod : s * xpow i (fun k => a' k - a k) ∈ mHom ι a' := by
    apply Submodule.subset_span
    have := isMultiHomog_mul (homog_of_mem hs) (isMultiHomog_xpow i (fun k => a' k - a k))
    have hsum : a + (fun k => a' k - a k) = a' := by
      funext k
      simp only [Pi.add_apply]
      have := h k
      omega
    rw [hsum] at this
    exact this
  refine ⟨⟨_, Submodule.mem_map_of_mem hprod⟩, ?_⟩
  show Ideal.Quotient.mk (dehomI W i) (s * xpow i (fun k => a' k - a k)) = Ideal.Quotient.mk (dehomI W i) s
  rw [map_mul, mk_xpow, mul_one]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isMultiHomog_monomial (m : (Σ k, ι k) →₀ ℕ) (c : ℤ) :
    IsMultiHomog (monomial m c : MRing ι) (fun k => ∑ i, m ⟨k, i⟩) := by
  classical
  intro m' hm' k
  rw [MvPolynomial.support_monomial] at hm'
  split_ifs at hm' with hc
  · simp at hm'
  · rw [Finset.mem_singleton] at hm'
    rw [hm']

/- English proof (translation)
Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem dmap_cover (W : Ideal (MRing ι)) (i : ∀ k, ι k) (y : MRing ι ⧸ dehomI W i) :
    ∃ (a : K → ℕ) (x : mPiece W a), dmap W i a x = y := by
  classical
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  let deg : ((Σ k, ι k) →₀ ℕ) → K → ℕ := fun m k => ∑ j, m ⟨k, j⟩
  let a : K → ℕ := fun k => f.support.sup (fun m => deg m k)
  have hle : ∀ m ∈ f.support, ∀ k, deg m k ≤ a k := fun m hm k =>
    Finset.le_sup (f := fun m => deg m k) hm
  have hterm : ∀ m ∈ f.support,
      monomial m (f.coeff m) * xpow i (fun k => a k - deg m k) ∈ mHom ι a := by
    intro m hm
    apply Submodule.subset_span
    have := isMultiHomog_mul (isMultiHomog_monomial m (f.coeff m))
      (isMultiHomog_xpow i (fun k => a k - deg m k))
    have hsum : (fun k => ∑ j, m ⟨k, j⟩) + (fun k => a k - deg m k) = a := by
      funext k
      simp only [Pi.add_apply]
      have := hle m hm k
      simp only [deg] at this ⊢
      omega
    rw [hsum] at this
    exact this
  have hF : (∑ m ∈ f.support, monomial m (f.coeff m) * xpow i (fun k => a k - deg m k)) ∈ mHom ι a :=
    Submodule.sum_mem _ hterm
  refine ⟨a, ⟨_, Submodule.mem_map_of_mem hF⟩, ?_⟩
  show Ideal.Quotient.mk (dehomI W i)
      (∑ m ∈ f.support, monomial m (f.coeff m) * xpow i (fun k => a k - deg m k)) =
    Ideal.Quotient.mk (dehomI W i) f
  simp only [map_sum, map_mul, mk_xpow, mul_one]
  conv_rhs => rw [f.as_sum]
  rw [map_sum]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Establish an intermediate fact. Treat this case separately. Treat this case separately. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem card_dehom {W : Ideal (MRing ι)} (hWp : W.IsPrime) (hWm : IsMultiHomogIdeal W)
    {i : ∀ k, ι k} (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ W) {a₁ c0 : ℕ}
    (hconst : ∀ a : K → ℕ, (∀ k, a₁ ≤ a k) → Nat.card (mPiece W a) = c0)
    (hfin : ∀ a : K → ℕ, Finite (mPiece W a)) {a : K → ℕ} (ha : ∀ k, a₁ ≤ a k) :
    Nat.card (MRing ι ⧸ dehomI W i) = c0 := by
  classical
  have hinj := fun b => dmap_injective hWp hWm hi b
  have hsurj : Function.Surjective (dmap W i a) := by
    intro y
    obtain ⟨b, x, hx⟩ := dmap_cover W i y
    let a' : K → ℕ := fun k => max (a k) (b k)
    have ha' : ∀ k, a₁ ≤ a' k := fun k => le_trans (ha k) (le_max_left _ _)
    obtain ⟨x', hx'⟩ := dmap_mono W i (fun k => le_max_right (a k) (b k)) x
    haveI := hfin a
    haveI := hfin a'
    have hsub : Set.range (dmap W i a) ⊆ Set.range (dmap W i a') := by
      rintro _ ⟨z, rfl⟩
      obtain ⟨z', hz'⟩ := dmap_mono W i (fun k => le_max_left (a k) (b k)) z
      exact ⟨z', hz'⟩
    have hcard : (Set.range (dmap W i a')).ncard ≤ (Set.range (dmap W i a)).ncard := by
      show Nat.card (Set.range (dmap W i a')) ≤ Nat.card (Set.range (dmap W i a))
      first
        | rw [Set.Nat.card_range_of_injective (hinj a), Set.Nat.card_range_of_injective (hinj a'),
            hconst a ha, hconst a' ha']
        | rw [Nat.card_range_of_injective (hinj a), Nat.card_range_of_injective (hinj a'),
            hconst a ha, hconst a' ha']
    have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.finite_range _)
    have hy : y ∈ Set.range (dmap W i a') := ⟨x', hx'.trans hx⟩
    rw [← heq] at hy
    exact hy
  rw [← hconst a ha]
  exact (Nat.card_eq_of_bijective _ ⟨hinj a, hsurj⟩).symm

/- English proof (translation)
Equip the data with the indicated structure. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem natCard_eq_pow_length {A : Type*} [AddCommGroup A] [Finite A] {p : ℕ} (hp : p.Prime)
    (h : ∀ x : A, p • x = 0) : Nat.card A = p ^ (Module.length ℤ A).toNat := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Module (ZMod p) A := AddCommGroup.zmodModule h
  have hlen : Module.length ℤ A = Module.length (ZMod p) A :=
    Module.length_eq_of_surjective (fun x => ⟨(x.val : ℤ), by simp⟩)
  have hfin : Module.length (ZMod p) A = (Module.finrank (ZMod p) A : ℕ∞) :=
    @Module.length_eq_finrank (ZMod p) A _ _ _ Module.Finite.of_finite
  have hcard : Nat.card A = Nat.card (ZMod p) ^ Module.finrank (ZMod p) A :=
    @Module.natCard_eq_pow_finrank (ZMod p) A _ _ _ Module.Finite.of_finite
  rw [hlen, hfin, ENat.toNat_coe, hcard, Nat.card_zmod]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
