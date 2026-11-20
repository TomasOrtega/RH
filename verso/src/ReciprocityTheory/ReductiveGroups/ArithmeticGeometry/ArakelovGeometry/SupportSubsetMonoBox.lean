import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsHomogeneousGrL

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Use `revert m`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem s hs`. Introduce `m hm`. Rewrite using `[← hs m hm p.1]`.

Conclude with `Finset.single_le_sum (f := fun i => m ⟨p.1, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.2)`. Consider the case `zero`. Introduce `m hm`. Simplify using `at hm`. Consider the case `add x y _ _ hx hy`.

Introduce `m hm`. Break down `Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h` into its components or cases. Conclude with `hx h`. Conclude with `hy h`. Consider the case `smul c x _ hx`.

Introduce `m hm`. Conclude with `hx (MvPolynomial.support_smul hm)`.
-/
theorem le_of_mem_support_mHom {a : K → ℕ} {f : MRing ι} (hf : f ∈ mHom ι a) {m : (Σ k, ι k) →₀ ℕ}
    (hm : m ∈ f.support) (p : Σ k, ι k) : m p ≤ a p.1 := by
  classical
  revert m
  induction hf using Submodule.span_induction with
  | mem s hs =>
    intro m hm
    rw [← hs m hm p.1]
    exact Finset.single_le_sum (f := fun i => m ⟨p.1, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.2)
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
    · exact hx h
    · exact hy h
  | smul c x _ hx =>
    intro m hm
    exact hx (MvPolynomial.support_smul hm)

/- English proof (translation)
Establish `hfin : (Set.pi Set.univ fun p : (Σ k, ι k) => Set.Iic (a p.1)).Finite` using `Set.Finite.pi fun p => Set.finite_Iic _`. Use `(hfin.preimage (Finsupp.equivFunOnFinite.injective.injOn)).subset ?_` and prove the remaining obligations. Introduce `m hm p _`. Conclude with `hm p`.
-/
theorem finite_monoBox (a : K → ℕ) :
    {m : (Σ k, ι k) →₀ ℕ | ∀ p, m p ≤ a p.1}.Finite := by
  have hfin : (Set.pi Set.univ fun p : (Σ k, ι k) => Set.Iic (a p.1)).Finite :=
    Set.Finite.pi fun p => Set.finite_Iic _
  refine (hfin.preimage (Finsupp.equivFunOnFinite.injective.injOn)).subset ?_
  intro m hm p _
  exact hm p

def monoBox (a : K → ℕ) : Finset ((Σ k, ι k) →₀ ℕ) := (finite_monoBox (ι := ι) a).toFinset

/- English proof (translation)
Introduce `m hm`. Simplify using `only [monoBox, Set.Finite.mem_toFinset, Set.mem_setOf_eq]`. Conclude with `fun p => le_of_mem_support_mHom hf hm p`.
-/
theorem support_subset_monoBox {a : K → ℕ} {f : MRing ι} (hf : f ∈ mHom ι a) :
    f.support ⊆ monoBox a := by
  intro m hm
  simp only [monoBox, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  exact fun p => le_of_mem_support_mHom hf hm p

/- English proof (translation)
Take `⟨q, rfl⟩ : ∃ q, p = q + 1` from `⟨p - 1, by omega⟩`. Set `g : (monoBox (ι` to `ι) a → Fin (q + 1)) → MRing ι ⧸ J := fun c => Ideal.Quotient.mk J (∑ m : monoBox (ι := ι) a, MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) (((c m : ℕ) : ℤ)))`. Establish `hsub : (mPiece J a : Set (MRing ι ⧸ J)) ⊆ Set.range g`. Introduce `x hx`. Take `⟨f, hf, rfl⟩` from `Submodule.mem_map.mp hx`.

Establish `hq : (0 : ℤ) < ((q + 1 : ℕ) : ℤ)` using `by omega`. Use `⟨fun m => ⟨((MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f) % ((q + 1 : ℕ) : ℤ)).toNat, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h0` using `Int.emod_nonneg (MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f) hq.ne'`. Establish `h1` using `Int.emod_lt_of_pos (MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f) hq`. Use linear arithmetic over natural numbers and integers.

Use `show Ideal.Quotient.mk J (∑ m : monoBox (ι := ι) a, MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) ((((MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f) % ((q + 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ)) = Ideal.Quotient.mk J f`. Rewrite using `[Ideal.Quotient.eq]`. Establish `hf' : f = ∑ m : monoBox (ι` using `ι) a, MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) (MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f) := by`. Rewrite using `[Finset.sum_coe_sort (monoBox a) (fun m => MvPolynomial.monomial m (MvPolynomial.coeff m f))]`. Use `conv_lhs => rw [MvPolynomial.as_sum f]`.

Use `Finset.sum_subset (support_subset_monoBox hf) (fun m _ hm => ?_)` and prove the remaining obligations. Simplify using `only [MvPolynomial.mem_support_iff, ne_eq, not_not] at hm`. Simplify using `[hm]`. Establish `hP : ((q + 1 : ℕ) : MRing ι) ∈ J` using `hpJ`. Establish `hdiff : ∀ m : monoBox (ι` using `ι) a, MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) ((((MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f) % ((q + 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ) - MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) (MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f) ∈ J := by`.

Introduce `m`. Establish `h0` using `Int.emod_nonneg (MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f) hq.ne'`. Rewrite using `[Int.toNat_of_nonneg h0, ← map_sub, Int.emod_def]`. Establish `e : MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f - ((q + 1 : ℕ) : ℤ) * (MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f / ((q + 1 : ℕ) : ℤ)) - MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f = ((q + 1 : ℕ) : ℤ) * (-(MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f / ((q + 1 : ℕ) : ℤ)))`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, ← MvPolynomial.C_mul_monomial, map_natCast]`. Conclude with `J.mul_mem_right _ hP`. Establish `e2 : (∑ m : monoBox (ι` using `ι) a, MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) ((((MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f) % ((q + 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ)) - f = ∑ m : monoBox (ι := ι) a, (MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) ((((MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f) % ((q + 1 : ℕ) : ℤ) …`. Rewrite using `[Finset.sum_sub_distrib, ← hf']`. Rewrite using `[e2]`.

Conclude with `Ideal.sum_mem _ fun m _ => hdiff m`. Conclude with `((Set.finite_range g).subset hsub).to_subtype`.
-/
theorem finite_mPiece (J : Ideal (MRing ι)) (a : K → ℕ) {p : ℕ} (hp : 0 < p)
    (hpJ : (p : MRing ι) ∈ J) : Finite (mPiece J a) := by
  classical
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  let g : (monoBox (ι := ι) a → Fin (q + 1)) → MRing ι ⧸ J := fun c =>
    Ideal.Quotient.mk J (∑ m : monoBox (ι := ι) a,
      MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) (((c m : ℕ) : ℤ)))
  have hsub : (mPiece J a : Set (MRing ι ⧸ J)) ⊆ Set.range g := by
    intro x hx
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
    have hq : (0 : ℤ) < ((q + 1 : ℕ) : ℤ) := by omega
    refine ⟨fun m => ⟨((MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f) % ((q + 1 : ℕ) : ℤ)).toNat, ?_⟩, ?_⟩
    · have h0 := Int.emod_nonneg (MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f) hq.ne'
      have h1 := Int.emod_lt_of_pos (MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f) hq
      omega
    · show Ideal.Quotient.mk J (∑ m : monoBox (ι := ι) a, MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ)
          ((((MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f) % ((q + 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ)) =
        Ideal.Quotient.mk J f
      rw [Ideal.Quotient.eq]
      have hf' : f = ∑ m : monoBox (ι := ι) a,
          MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) (MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f) := by
        rw [Finset.sum_coe_sort (monoBox a) (fun m => MvPolynomial.monomial m (MvPolynomial.coeff m f))]
        conv_lhs => rw [MvPolynomial.as_sum f]
        refine Finset.sum_subset (support_subset_monoBox hf) (fun m _ hm => ?_)
        simp only [MvPolynomial.mem_support_iff, ne_eq, not_not] at hm
        simp [hm]
      have hP : ((q + 1 : ℕ) : MRing ι) ∈ J := hpJ
      have hdiff : ∀ m : monoBox (ι := ι) a, MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ)
          ((((MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f) % ((q + 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ) -
          MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) (MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f) ∈ J := by
        intro m
        have h0 := Int.emod_nonneg (MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f) hq.ne'
        rw [Int.toNat_of_nonneg h0, ← map_sub, Int.emod_def]
        have e : MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f - ((q + 1 : ℕ) : ℤ) *
            (MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f / ((q + 1 : ℕ) : ℤ)) -
            MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f =
            ((q + 1 : ℕ) : ℤ) * (-(MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f / ((q + 1 : ℕ) : ℤ))) := by
          ring
        rw [e, ← MvPolynomial.C_mul_monomial, map_natCast]
        exact J.mul_mem_right _ hP
      have e2 : (∑ m : monoBox (ι := ι) a, MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ)
          ((((MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f) % ((q + 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ)) - f =
          ∑ m : monoBox (ι := ι) a, (MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ)
          ((((MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f) % ((q + 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ) -
          MvPolynomial.monomial (m : (Σ k, ι k) →₀ ℕ) (MvPolynomial.coeff (m : (Σ k, ι k) →₀ ℕ) f)) := by
        rw [Finset.sum_sub_distrib, ← hf']
      rw [e2]
      exact Ideal.sum_mem _ fun m _ => hdiff m
  exact ((Set.finite_range g).subset hsub).to_subtype

/- English proof (translation)
Use `haveI := finite_mPiece J a hp hpJ`. Conclude with `Nat.card_pos`.
-/
theorem card_mPiece_pos (J : Ideal (MRing ι)) (a : K → ℕ) {p : ℕ} (hp : 0 < p)
    (hpJ : (p : MRing ι) ∈ J) : 0 < Nat.card (mPiece J a) := by
  haveI := finite_mPiece J a hp hpJ
  exact Nat.card_pos

/- English proof (translation)
Establish `hmem : ∀ f ∈ mHom ι a, f ∈ q`. Introduce `f hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem s hs`. Rewrite using `[MvPolynomial.as_sum s]`.

Use `Ideal.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Establish `hsum` using `hs m hm k`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, 0 < m ⟨k, i⟩ := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Establish `h0 : ∑ i, m ⟨k, i⟩ = 0` using `Finset.sum_eq_zero fun i _ => by have := hc i; omega`. Use linear arithmetic over natural numbers and integers. Establish `e : MvPolynomial.monomial m (MvPolynomial.coeff m s) = MvPolynomial.X ⟨k, i⟩ * MvPolynomial.monomial (m - Finsupp.single ⟨k, i⟩ 1) (MvPolynomial.coeff m s)`. Rewrite using `[MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hi)]`. Rewrite using `[e]`.

Conclude with `q.mul_mem_right _ (hk i)`. Consider the case `zero => exact q.zero_mem`. Consider the case `add x y _ _ hx hy => exact q.add_mem hx hy`. Consider the case `smul c x _ hx => exact Submodule.smul_of_tower_mem q c hx`. Establish `hzero : ∀ x : mPiece q a, x = 0`.

Introduce and unpack `⟨x, hx⟩`. Take `⟨f, hf, rfl⟩` from `Submodule.mem_map.mp hx`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show Ideal.Quotient.mk q f = 0`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr (hmem f hf)`.

Use `haveI : Unique (mPiece q a) := ⟨⟨0⟩, hzero⟩`. Conclude with `Nat.card_unique`.
-/
theorem card_mPiece_irrel {q : Ideal (MRing ι)} {k : K} (hk : ∀ i, (X ⟨k, i⟩ : MRing ι) ∈ q)
    {a : K → ℕ} (ha : 0 < a k) : Nat.card (mPiece q a) = 1 := by
  classical
  have hmem : ∀ f ∈ mHom ι a, f ∈ q := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem s hs =>
      rw [MvPolynomial.as_sum s]
      refine Ideal.sum_mem _ fun m hm => ?_
      have hsum := hs m hm k
      obtain ⟨i, hi⟩ : ∃ i, 0 < m ⟨k, i⟩ := by
        by_contra hc
        push_neg at hc
        have h0 : ∑ i, m ⟨k, i⟩ = 0 := Finset.sum_eq_zero fun i _ => by have := hc i; omega
        omega
      have e : MvPolynomial.monomial m (MvPolynomial.coeff m s) =
          MvPolynomial.X ⟨k, i⟩ * MvPolynomial.monomial (m - Finsupp.single ⟨k, i⟩ 1) (MvPolynomial.coeff m s) := by
        rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
          add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hi)]
      rw [e]
      exact q.mul_mem_right _ (hk i)
    | zero => exact q.zero_mem
    | add x y _ _ hx hy => exact q.add_mem hx hy
    | smul c x _ hx => exact Submodule.smul_of_tower_mem q c hx
  have hzero : ∀ x : mPiece q a, x = 0 := by
    rintro ⟨x, hx⟩
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
    apply Subtype.ext
    show Ideal.Quotient.mk q f = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmem f hf)
  haveI : Unique (mPiece q a) := ⟨⟨0⟩, hzero⟩
  exact Nat.card_unique

/- English proof (translation)
Establish `hmap : ∀ x ∈ mPiece J a, Ideal.Quotient.factor h x ∈ mPiece J' a`. Introduce `x hx`. Take `⟨g, hg, rfl⟩` from `Submodule.mem_map.mp hx`. Use `Submodule.mem_map.mpr ⟨g, hg, ?_⟩` and prove the remaining obligations. Use `show Ideal.Quotient.mk J' g = Ideal.Quotient.factor h (Ideal.Quotient.mk J g)`.

Rewrite using `[Ideal.Quotient.factor_mk]`. Use `Nat.card_le_card_of_surjective (fun x => ⟨Ideal.Quotient.factor h x, hmap x x.2⟩) ?_` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩`. Take `⟨g, hg, rfl⟩` from `Submodule.mem_map.mp hy`. Use `⟨⟨Ideal.Quotient.mk J g, Submodule.mem_map.mpr ⟨g, hg, rfl⟩⟩, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show Ideal.Quotient.factor h (Ideal.Quotient.mk J g) = Ideal.Quotient.mk J' g`. Rewrite using `[Ideal.Quotient.factor_mk]`.
-/
theorem card_mPiece_mono {J J' : Ideal (MRing ι)} (h : J ≤ J') (a : K → ℕ) [Finite (mPiece J a)] :
    Nat.card (mPiece J' a) ≤ Nat.card (mPiece J a) := by
  have hmap : ∀ x ∈ mPiece J a, Ideal.Quotient.factor h x ∈ mPiece J' a := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hx
    refine Submodule.mem_map.mpr ⟨g, hg, ?_⟩
    show Ideal.Quotient.mk J' g = Ideal.Quotient.factor h (Ideal.Quotient.mk J g)
    rw [Ideal.Quotient.factor_mk]
  refine Nat.card_le_card_of_surjective (fun x => ⟨Ideal.Quotient.factor h x, hmap x x.2⟩) ?_
  rintro ⟨y, hy⟩
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hy
  refine ⟨⟨Ideal.Quotient.mk J g, Submodule.mem_map.mpr ⟨g, hg, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  show Ideal.Quotient.factor h (Ideal.Quotient.mk J g) = Ideal.Quotient.mk J' g
  rw [Ideal.Quotient.factor_mk]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
