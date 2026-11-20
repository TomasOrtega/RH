import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def dmap (W : Ideal (MRing ι)) (i : ∀ k, ι k) (a : K → ℕ) : mPiece W a → MRing ι ⧸ dehomI W i :=
  fun x => Ideal.Quotient.factor (le_sup_left : W ≤ dehomI W i) x.1

/- English proof (translation)
Establish `homog_of_mem : ∀ {b : K → ℕ} {f : MRing ι}, f ∈ mHom ι b → IsMultiHomog f b`. Introduce `b f hf`. Unfold `mHom at hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx => exact hx`.

Consider the case `zero`. Introduce `m hm`. Simplify using `at hm`. Consider the case `add x y _ _ hx hy`. Introduce `m hm k`.

Break down `Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h` into its components or cases. Conclude with `hx m h k`. Conclude with `hy m h k`. Consider the case `smul n x _ hx`. Introduce `m hm k`.

Conclude with `hx m (MvPolynomial.support_smul hm) k`. Introduce and unpack `⟨_, s, hs, rfl⟩ ⟨_, t, ht, rfl⟩ hxy`. Establish `hd : Ideal.Quotient.mk (dehomI W i) s = Ideal.Quotient.mk (dehomI W i) t` using `hxy`. Establish `hsub : s - t ∈ dehomI W i` using `Ideal.Quotient.eq.1 hd`. Establish `hW` using `mem_of_mem_dehomI hWp hWm hi (homog_of_mem (Submodule.sub_mem _ hs ht)) hsub`.

Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `Ideal.Quotient.eq.2 hW`.
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
Establish `homog_of_mem : ∀ {b : K → ℕ} {f : MRing ι}, f ∈ mHom ι b → IsMultiHomog f b`. Introduce `b f hf`. Unfold `mHom at hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx => exact hx`.

Consider the case `zero`. Introduce `m hm`. Simplify using `at hm`. Consider the case `add x y _ _ hx hy`. Introduce `m hm k`.

Break down `Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h` into its components or cases. Conclude with `hx m h k`. Conclude with `hy m h k`. Consider the case `smul n x _ hx`. Introduce `m hm k`.

Conclude with `hx m (MvPolynomial.support_smul hm) k`. Take `⟨_, s, hs, rfl⟩` from `x`. Establish `hprod : s * xpow i (fun k => a' k - a k) ∈ mHom ι a'`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `isMultiHomog_mul (homog_of_mem hs) (isMultiHomog_xpow i (fun k => a' k - a k))` as an intermediate fact.

Establish `hsum : a + (fun k => a' k - a k) = a'`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.add_apply]`. Use `h k` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite `this` using `[hsum]`. Conclude with `this`. Use `⟨⟨_, Submodule.mem_map_of_mem hprod⟩, ?_⟩` and prove the remaining obligations. Use `show Ideal.Quotient.mk (dehomI W i) (s * xpow i (fun k => a' k - a k)) = Ideal.Quotient.mk (dehomI W i) s`. Rewrite using `[map_mul, mk_xpow, mul_one]`.
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
Introduce `m' hm' k`. Rewrite `hm'` using `[MvPolynomial.support_monomial]`. Use `split_ifs at hm' with hc`. Simplify using `at hm'`. Rewrite `hm'` using `[Finset.mem_singleton]`.

Rewrite using `[hm']`.
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
Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Set `deg : ((Σ k, ι k) →₀ ℕ) → K → ℕ` to `fun m k => ∑ j, m ⟨k, j⟩`. Set `a : K → ℕ` to `fun k => f.support.sup (fun m => deg m k)`. Establish `hle : ∀ m ∈ f.support, ∀ k, deg m k ≤ a k` using `fun m hm k => Finset.le_sup (f := fun m => deg m k) hm`. Establish `hterm : ∀ m ∈ f.support, monomial m (f.coeff m) * xpow i (fun k => a k - deg m k) ∈ mHom ι a`.

Introduce `m hm`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `isMultiHomog_mul (isMultiHomog_monomial m (f.coeff m)) (isMultiHomog_xpow i (fun k => a k - deg m k))` as an intermediate fact. Establish `hsum : (fun k => ∑ j, m ⟨k, j⟩) + (fun k => a k - deg m k) = a`. Use function extensionality and compare the values at `k`.

Simplify using `only [Pi.add_apply]`. Use `hle m hm k` as an intermediate fact. Simplify using `only [deg] at this ⊢`. Use linear arithmetic over natural numbers and integers. Rewrite `this` using `[hsum]`.

Conclude with `this`. Establish `hF : (∑ m ∈ f.support, monomial m (f.coeff m) * xpow i (fun k => a k - deg m k)) ∈ mHom ι a` using `Submodule.sum_mem _ hterm`. Use `⟨a, ⟨_, Submodule.mem_map_of_mem hF⟩, ?_⟩` and prove the remaining obligations. Use `show Ideal.Quotient.mk (dehomI W i) (∑ m ∈ f.support, monomial m (f.coeff m) * xpow i (fun k => a k - deg m k)) = Ideal.Quotient.mk (dehomI W i) f`. Simplify using `only [map_sum, map_mul, mk_xpow, mul_one]`.

Use `conv_rhs => rw [f.as_sum]`. Rewrite using `[map_sum]`.
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
Establish `hinj` using `fun b => dmap_injective hWp hWm hi b`. Establish `hsurj : Function.Surjective (dmap W i a)`. Introduce `y`. Take `⟨b, x, hx⟩` from `dmap_cover W i y`. Set `a' : K → ℕ` to `fun k => max (a k) (b k)`.

Establish `ha' : ∀ k, a₁ ≤ a' k` using `fun k => le_trans (ha k) (le_max_left _ _)`. Take `⟨x', hx'⟩` from `dmap_mono W i (fun k => le_max_right (a k) (b k)) x`. Use `haveI := hfin a`. Use `haveI := hfin a'`. Establish `hsub : Set.range (dmap W i a) ⊆ Set.range (dmap W i a')`.

Introduce and unpack `_ ⟨z, rfl⟩`. Take `⟨z', hz'⟩` from `dmap_mono W i (fun k => le_max_left (a k) (b k)) z`. Conclude with `⟨z', hz'⟩`. Establish `hcard : (Set.range (dmap W i a')).ncard ≤ (Set.range (dmap W i a)).ncard` using `by show Nat.card (Set.range (dmap W i a')) ≤ Nat.card (Set.range (dmap W i a)) first`. Consider the case `rw [Set.Nat.card_range_of_injective (hinj a), Set.Nat.card_range_of_injective (hinj a'), hconst a ha, hconst a' ha']`.

Consider the case `rw [Nat.card_range_of_injective (hinj a), Nat.card_range_of_injective (hinj a'), hconst a ha, hconst a' ha']`. Establish `heq` using `Set.eq_of_subset_of_ncard_le hsub hcard (Set.finite_range _)`. Establish `hy : y ∈ Set.range (dmap W i a')` using `⟨x', hx'.trans hx⟩`. Rewrite `hy` using `[← heq]`. Conclude with `hy`.

Rewrite using `[← hconst a ha]`. Conclude with `(Nat.card_eq_of_bijective _ ⟨hinj a, hsurj⟩).symm`.
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
Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `letI : Module (ZMod p) A := AddCommGroup.zmodModule h`. Establish `hlen : Module.length ℤ A = Module.length (ZMod p) A` using `Module.length_eq_of_surjective (fun x => ⟨(x.val : ℤ), by simp⟩)`. Establish `hfin : Module.length (ZMod p) A = (Module.finrank (ZMod p) A : ℕ∞)` using `@Module.length_eq_finrank (ZMod p) A _ _ _ Module.Finite.of_finite`. Establish `hcard : Nat.card A = Nat.card (ZMod p) ^ Module.finrank (ZMod p) A` using `@Module.natCard_eq_pow_finrank (ZMod p) A _ _ _ Module.Finite.of_finite`.

Rewrite using `[hlen, hfin, ENat.toNat_coe, hcard, Nat.card_zmod]`.
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
