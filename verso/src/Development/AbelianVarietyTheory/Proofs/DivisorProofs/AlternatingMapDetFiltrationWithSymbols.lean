import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.FiltDet

/- English proof (translation)
Establish `h` using `AlternatingMap.eq_smul_basis_det (Pi.basisFun E (Fin d)) (ω.compLinearMap (Fintype.linearCombination E z))`. Establish `e1 : (fun i => Fintype.linearCombination E z (Pi.basisFun E (Fin d) i)) = z`. Use function extensionality and compare the values at `i`. Simplify using `[Fintype.linearCombination_apply_single]`. Establish `h2 : ω (fun j => Fintype.linearCombination E z (N j)) = (ω.compLinearMap (Fintype.linearCombination E z)) N` using `rfl`.

Rewrite using `[h2, h, AlternatingMap.smul_apply, Pi.basisFun_det, AlternatingMap.compLinearMap_apply, e1, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression.
-/
theorem alt_linComb {E A' : Type} [Field E] [AddCommGroup A'] [Module E A'] {d : ℕ}
    (ω : A' [⋀^Fin d]→ₗ[E] E) (z : Fin d → A') (N : Fin d → Fin d → E) :
    ω (fun j => Fintype.linearCombination E z (N j)) = (Matrix.of N).det * ω z := by
  classical
  have h := AlternatingMap.eq_smul_basis_det (Pi.basisFun E (Fin d))
    (ω.compLinearMap (Fintype.linearCombination E z))
  have e1 : (fun i => Fintype.linearCombination E z (Pi.basisFun E (Fin d) i)) = z := by
    funext i; simp [Fintype.linearCombination_apply_single]
  have h2 : ω (fun j => Fintype.linearCombination E z (N j)) =
      (ω.compLinearMap (Fintype.linearCombination E z)) N := rfl
  rw [h2, h, AlternatingMap.smul_apply, Pi.basisFun_det,
    AlternatingMap.compLinearMap_apply, e1, smul_eq_mul, mul_comm]
  rfl

/- English proof (translation)
Introduce `E A' _ _ _ r d I _ _ U sym hdec hsym ix J v hv hJ _ hcard z hz hzs hzv ω`. Establish `step : ∀ (a : Fin r) (x : A') (hx : x ∈ U a), x - ∑ i, sym a ⟨x, hx⟩ i • z (ix ⟨a, i⟩) ∈ U (a + 1)`. Introduce `a x hx`. Establish `hzs' : ∀ i, sym a ⟨z (ix ⟨a, i⟩), hz ⟨a, i⟩⟩ = Pi.single i 1` using `fun i => hzs ⟨a, i⟩`. Establish `hmem : ∑ i, sym a ⟨x, hx⟩ i • z (ix ⟨a, i⟩) ∈ U a` using `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hz ⟨a, i⟩)`.

Establish `hy : x - ∑ i, sym a ⟨x, hx⟩ i • z (ix ⟨a, i⟩) ∈ U a` using `Submodule.sub_mem _ hx hmem`. Use `(hsym a ⟨_, hy⟩).1 ?_` and prove the remaining obligations. Establish `: (⟨_, hy⟩ : U a) = ⟨x, hx⟩ - ∑ i, sym a ⟨x, hx⟩ i • ⟨z (ix ⟨a, i⟩), hz ⟨a, i⟩⟩` using `by ext; simp`. Rewrite using `[this, map_sub, map_sum]`. Simplify using `only [map_smul, hzs']`.

Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Choose the witnesses or unpack the hypotheses as in `⟨β, hβix, hβout⟩ : ∃ β : Fin d → ℕ, (∀ q, β (ix q) = q.1) ∧ (∀ k, k ∉ Set.range ix → β k = r) := by`. Use `⟨fun k => if h : k ∈ Set.range ix then ((Classical.choose h).1 : ℕ) else r, ?_, ?_⟩` and prove the remaining obligations. Introduce `q`.

Establish `h : ix q ∈ Set.range ix` using `⟨q, rfl⟩`. Simplify using `only [dif_pos h]`. Rewrite using `[ix.injective (Classical.choose_spec h)]`. Introduce `k hk`. Simplify using `only [dif_neg hk]`.

Establish `hβle : ∀ k, β k ≤ r`. Introduce `k`. Distinguish the cases in `hk : k ∈ Set.range ix`. Take `⟨q, rfl⟩` from `hk`. Rewrite using `[hβix]`.

Conclude with `q.1.isLt.le`. Rewrite using `[hβout k hk]`. Establish `conv : ∀ (S : Set (Fin d)) (x : A'), x ∈ Submodule.span E (z '' S) → ∃ c : Fin d → E, (∀ k ∉ S, c k = 0) ∧ Fintype.linearCombination E z c = x`. Introduce `S x hx`. Take `⟨l, hl, rfl⟩` from `(Finsupp.mem_span_image_iff_linearCombination E).1 hx`.

Use `⟨l, fun k hk => (Finsupp.mem_supported' E l).1 hl k hk, ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum_fintype]`. Introduce `i`. Simplify using the standard rewrite rules. Distinguish the cases in `hli : LinearIndependent E (fun k : J => v k)`.

Use `swap`. Establish `h1 : ¬ LinearIndependent E v` using `fun h => hli (h.comp _ Subtype.val_injective)`. Establish `h2 : ¬ LinearIndependent E z`. Introduce `h`. Apply `hli` to reduce the goal to its premises.

Establish `: (fun k : J => v k) = z ∘ Subtype.val`. Use function extensionality and compare the values at `k`. Conclude with `(hzv k.1 (hJ k.1 k.2).1).symm`. Rewrite using `[this]`. Conclude with `h.comp _ Subtype.val_injective`.

Rewrite using `[ω.map_linearDependent v h1, ω.map_linearDependent z h2, mul_zero]`. Establish `hspan : U r ≤ Submodule.span E (Set.range fun k : J => v k)`. Establish `hle : Submodule.span E (Set.range fun k : J => v k) ≤ U r`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`.

Conclude with `(hJ k.1 k.2).2`. Use `(Submodule.eq_of_le_of_finrank_le hle ?_).ge` and prove the remaining obligations. Rewrite using `[finrank_span_eq_card hli, Fintype.card_coe]`. Conclude with `hcard`. Establish `hdown : ∀ n a, a + n = r → U a ≤ Submodule.span E (z '' {k | a ≤ β k})`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `a ha`. Take `rfl : a = r` from `by omega`.

Use `hspan.trans (Submodule.span_mono ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Use `⟨k.1, ?_, hzv k.1 (hJ k.1 k.2).1⟩` and prove the remaining obligations. Simplify using `[hβout k.1 (hJ k.1 k.2).1]`. Consider the case `succ n ih`.

Introduce `a ha x hx`. Establish `har : a < r` using `by omega`. Establish `key` using `step ⟨a, har⟩ x hx`. Establish `hy` using `ih (a + 1) (by omega) key`. Establish `hmono : Submodule.span E (z '' {k | a + 1 ≤ β k}) ≤ Submodule.span E (z '' {k | a ≤ β k})` using `Submodule.span_mono (Set.image_mono fun k hk => by`.

Simplify using `only [Set.mem_setOf_eq] at hk ⊢`. Use the proof step `omega)`. Establish `hsum : ∑ i, sym ⟨a, har⟩ ⟨x, hx⟩ i • z (ix ⟨⟨a, har⟩, i⟩) ∈ Submodule.span E (z '' {k | a ≤ β k})`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ix ⟨⟨a, har⟩, i⟩, ?_, rfl⟩)` and prove the remaining obligations. Simplify using `[hβix]`.

Use `Submodule.add_mem _ (hmono hy) hsum` as an intermediate fact. Simplify using `using this`. Establish `hcol : ∀ q : (Σ a, I a), ∃ col : Fin d → E, Fintype.linearCombination E z col = v (ix q) ∧ (∀ k, β k < q.1 → col k = 0) ∧ ∀ i, col (ix ⟨q.1, i⟩) = sym q.1 ⟨v (ix q), hv q⟩ i`. Introduce and unpack `⟨a, i'⟩`. Establish `key` using `step a (v (ix ⟨a, i'⟩)) (hv ⟨a, i'⟩)`.

Establish `hy` using `hdown (r - (a + 1)) (a + 1) (by omega) key`. Take `⟨c, hc0, hcL⟩` from `conv _ _ hy`. Use `⟨c + ∑ i, sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i • Pi.single (ix ⟨a, i⟩) 1, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_sum, hcL]`. Simplify using `only [map_smul, Fintype.linearCombination_apply_single, one_smul]`.

Normalize the expressions using the abelian group laws. Introduce `k hk`. Establish `hk' : β k < a` using `hk`. Establish `h1 : c k = 0` using `hc0 k (by simp only [Set.mem_setOf_eq, not_le]; omega)`. Simplify using `only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, h1, zero_add]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Establish `hne : k ≠ ix ⟨a, i⟩`. Introduce and unpack `rfl`. Rewrite `hk'` using `[hβix]`. Conclude with `lt_irrefl _ hk'`.

Simplify using `[Pi.single_apply, hne]`. Introduce `i`. Establish `h1 : c (ix ⟨a, i⟩) = 0` using `hc0 _ (by simp [hβix])`. Simplify using `[h1, Finset.sum_apply, Pi.single_apply, Sigma.mk.inj_iff]`. Use `choose col hcolL hcol0 hcoldiag using hcol`.

Choose the witnesses or unpack the hypotheses as in `⟨N, hNix, hNout⟩ : ∃ N : Matrix (Fin d) (Fin d) E, (∀ q, N (ix q) = col q) ∧ (∀ k, k ∉ Set.range ix → N k = Pi.single k 1) := by`. Use `⟨Matrix.of fun k => if h : k ∈ Set.range ix then col (Classical.choose (Set.mem_range.1 h)) else Pi.single k 1, ?_, ?_⟩` and prove the remaining obligations. Introduce `q`. Establish `h : ix q ∈ Set.range ix` using `⟨q, rfl⟩`. Use function extensionality and compare the values at `j`.

Simplify using `only [Matrix.of_apply, dif_pos h]`. Rewrite using `[ix.injective (Classical.choose_spec (Set.mem_range.1 h))]`. Introduce `k hk`. Use function extensionality and compare the values at `j`. Simplify using `only [Matrix.of_apply, dif_neg hk]`.

Establish `hNL : ∀ j, Fintype.linearCombination E z (N j) = v j`. Introduce `j`. Distinguish the cases in `hj : j ∈ Set.range ix`. Take `⟨q, rfl⟩` from `hj`. Rewrite using `[hNix]`.

Conclude with `hcolL q`. Rewrite using `[hNout j hj, Fintype.linearCombination_apply_single, one_smul]`. Conclude with `hzv j hj`. Establish `hBT : N.BlockTriangular β`. Introduce `i j hij`.

Distinguish the cases in `hi : i ∈ Set.range ix`. Take `⟨q, rfl⟩` from `hi; rw [hNix]; exact hcol0 q j (by rw [hβix] at hij; exact hij)`. Rewrite using `[hNout i hi, Pi.single_apply, if_neg]`. Introduce and unpack `rfl`. Conclude with `lt_irrefl _ hij`.

Establish `hdet : N.det = ∏ a : Fin r, (Matrix.of fun i i' : I a => sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i).det`. Rewrite using `[hBT.det]`. Establish `himg : Finset.image β Finset.univ ⊆ Finset.range (r + 1)`. Introduce `b hb`. Take `⟨k, _, rfl⟩` from `Finset.mem_image.1 hb`.

Simplify using `only [Finset.mem_range]`. Use `hβle k` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.prod_subset himg ?_]`. Rewrite using `[Finset.prod_range_succ]`.

Establish `hlast : (N.toSquareBlock β r).det = 1`. Establish `: N.toSquareBlock β r = 1`. Use extensionality with `⟨i, hi⟩ ⟨j, hj⟩`. Establish `hi' : i ∉ Set.range ix`. Introduce and unpack `⟨q, rfl⟩`.

Rewrite `hi` using `[hβix]`. Use `q.1.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[Matrix.toSquareBlock_def, Matrix.of_apply, hNout i hi', Pi.single_apply, Matrix.one_apply]`. Simplify using `only [Subtype.mk.injEq, eq_comm]`.

Rewrite using `[this, Matrix.det_one]`. Rewrite using `[hlast, mul_one, ← Fin.prod_univ_eq_prod_range (fun x => (N.toSquareBlock β x).det) r]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `hinj : Function.Injective (fun i : I a => (⟨ix ⟨a, i⟩, hβix _⟩ : {k // β k = (a : ℕ)}))`. Introduce `i i' h`.

Simplify using `only [Subtype.mk.injEq, ix.apply_eq_iff_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h`. Conclude with `h`. Establish `hsurj : Function.Surjective (fun i : I a => (⟨ix ⟨a, i⟩, hβix _⟩ : {k // β k = (a : ℕ)}))`. Introduce and unpack `⟨k, hk⟩`. Distinguish the cases in `hkr : k ∈ Set.range ix`.

Take `⟨⟨b, i⟩, rfl⟩` from `hkr`. Rewrite `hk` using `[hβix]`. Establish `hab : b = a` using `Fin.ext hk`. Substitute `hab` using the available equality. Conclude with `⟨i, rfl⟩`.

Rewrite `hk` using `[hβout k hkr]`. Use `a.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Set `e` to `Equiv.ofBijective _ ⟨hinj, hsurj⟩`. Use `show (N.toSquareBlock β a).det = _`.

Rewrite using `[← Matrix.det_submatrix_equiv_self e, ← Matrix.det_transpose]`. Use `congr 1`. Use extensionality with `i i'`. Use `show N (ix ⟨a, i'⟩) (ix ⟨a, i⟩) = _`. Rewrite using `[hNix]`.

Conclude with `hcoldiag ⟨a, i'⟩ i`. Introduce `b _ hb haveI : IsEmpty {i // β i = b} := ⟨fun ⟨i, hi⟩ => hb (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩)⟩`. Conclude with `Matrix.det_isEmpty`. Establish `hv' : v = fun j => Fintype.linearCombination E z (N j)` using `funext fun j => (hNL j).symm`. Rewrite using `[show ω v = ω (fun j => Fintype.linearCombination E z (N j)) from congrArg _ hv',`.

Use the proof step `]`. Use `(alt_linComb ω z N).trans ?_` and prove the remaining obligations. Rewrite using `[← hdet]`. Both sides reduce to the same expression.
-/
theorem det_filtration_symbols : ∀ (E A' : Type) [Field E] [AddCommGroup A'] [Module E A'] (r d : ℕ) (I : Fin r → Type) [∀ a, Fintype (I a)] [∀ a, DecidableEq (I a)] (U : ℕ → Submodule E A') (sym : ∀ a : Fin r, U a →ₗ[E] (I a → E)), (∀ a < r, U (a + 1) ≤ U a) → (∀ (a : Fin r) (x : U a), sym a x = 0 ↔ x.1 ∈ U (a + 1)) → ∀ (ix : (Σ a, I a) ↪ Fin d) (J : Finset (Fin d)) (v : Fin d → A') (hv : ∀ q, v (ix q) ∈ U q.1), (∀ k ∈ J, k ∉ Set.range ix ∧ v k ∈ U r) → ∀ [FiniteDimensional E (U r)], Module.finrank E (U r) ≤ J.card → ∀ (z : Fin d → A') (hz : ∀ q, z (ix q) ∈ U q.1), (∀ q, sym q.1 ⟨z (ix q), hz q⟩ = Pi.single q.2 1) → (∀ k, k ∉ Set.range ix → z k = v k) → ∀ ω : A' [⋀^Fin d]→ₗ[E] E, ω v = (∏ a, (Matrix.of fun i i' : I a => sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i).det) * ω z := by
  intro E A' _ _ _ r d I _ _ U sym hdec hsym ix J v hv hJ _ hcard z hz hzs hzv ω
  classical

  have step : ∀ (a : Fin r) (x : A') (hx : x ∈ U a),
      x - ∑ i, sym a ⟨x, hx⟩ i • z (ix ⟨a, i⟩) ∈ U (a + 1) := by
    intro a x hx
    have hzs' : ∀ i, sym a ⟨z (ix ⟨a, i⟩), hz ⟨a, i⟩⟩ = Pi.single i 1 := fun i => hzs ⟨a, i⟩
    have hmem : ∑ i, sym a ⟨x, hx⟩ i • z (ix ⟨a, i⟩) ∈ U a :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hz ⟨a, i⟩)
    have hy : x - ∑ i, sym a ⟨x, hx⟩ i • z (ix ⟨a, i⟩) ∈ U a := Submodule.sub_mem _ hx hmem
    refine (hsym a ⟨_, hy⟩).1 ?_
    have : (⟨_, hy⟩ : U a) = ⟨x, hx⟩ - ∑ i, sym a ⟨x, hx⟩ i • ⟨z (ix ⟨a, i⟩), hz ⟨a, i⟩⟩ := by
      ext; simp
    rw [this, map_sub, map_sum]
    simp only [map_smul, hzs']
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  obtain ⟨β, hβix, hβout⟩ : ∃ β : Fin d → ℕ, (∀ q, β (ix q) = q.1) ∧
      (∀ k, k ∉ Set.range ix → β k = r) := by
    refine ⟨fun k => if h : k ∈ Set.range ix then ((Classical.choose h).1 : ℕ) else r, ?_, ?_⟩
    · intro q
      have h : ix q ∈ Set.range ix := ⟨q, rfl⟩
      simp only [dif_pos h]
      rw [ix.injective (Classical.choose_spec h)]
    · intro k hk; simp only [dif_neg hk]
  have hβle : ∀ k, β k ≤ r := by
    intro k
    by_cases hk : k ∈ Set.range ix
    · obtain ⟨q, rfl⟩ := hk; rw [hβix]; exact q.1.isLt.le
    · rw [hβout k hk]
  have conv : ∀ (S : Set (Fin d)) (x : A'), x ∈ Submodule.span E (z '' S) →
      ∃ c : Fin d → E, (∀ k ∉ S, c k = 0) ∧ Fintype.linearCombination E z c = x := by
    intro S x hx
    obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination E).1 hx
    refine ⟨l, fun k hk => (Finsupp.mem_supported' E l).1 hl k hk, ?_⟩
    rw [Fintype.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; simp
  by_cases hli : LinearIndependent E (fun k : J => v k)
  swap
  · have h1 : ¬ LinearIndependent E v := fun h => hli (h.comp _ Subtype.val_injective)
    have h2 : ¬ LinearIndependent E z := by
      intro h; apply hli
      have : (fun k : J => v k) = z ∘ Subtype.val := by
        funext k; exact (hzv k.1 (hJ k.1 k.2).1).symm
      rw [this]; exact h.comp _ Subtype.val_injective
    rw [ω.map_linearDependent v h1, ω.map_linearDependent z h2, mul_zero]
  have hspan : U r ≤ Submodule.span E (Set.range fun k : J => v k) := by
    have hle : Submodule.span E (Set.range fun k : J => v k) ≤ U r := by
      rw [Submodule.span_le]; rintro _ ⟨k, rfl⟩; exact (hJ k.1 k.2).2
    refine (Submodule.eq_of_le_of_finrank_le hle ?_).ge
    rw [finrank_span_eq_card hli, Fintype.card_coe]; exact hcard
  have hdown : ∀ n a, a + n = r → U a ≤ Submodule.span E (z '' {k | a ≤ β k}) := by
    intro n
    induction n with
    | zero =>
      intro a ha
      obtain rfl : a = r := by omega
      refine hspan.trans (Submodule.span_mono ?_)
      rintro _ ⟨k, rfl⟩
      refine ⟨k.1, ?_, hzv k.1 (hJ k.1 k.2).1⟩
      simp [hβout k.1 (hJ k.1 k.2).1]
    | succ n ih =>
      intro a ha x hx
      have har : a < r := by omega
      have key := step ⟨a, har⟩ x hx
      have hy := ih (a + 1) (by omega) key
      have hmono : Submodule.span E (z '' {k | a + 1 ≤ β k}) ≤
          Submodule.span E (z '' {k | a ≤ β k}) :=
        Submodule.span_mono (Set.image_mono fun k hk => by
          simp only [Set.mem_setOf_eq] at hk ⊢; omega)
      have hsum : ∑ i, sym ⟨a, har⟩ ⟨x, hx⟩ i • z (ix ⟨⟨a, har⟩, i⟩) ∈
          Submodule.span E (z '' {k | a ≤ β k}) := by
        refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
          (Submodule.subset_span ⟨ix ⟨⟨a, har⟩, i⟩, ?_, rfl⟩)
        simp [hβix]
      have := Submodule.add_mem _ (hmono hy) hsum
      simpa using this
  have hcol : ∀ q : (Σ a, I a), ∃ col : Fin d → E, Fintype.linearCombination E z col = v (ix q) ∧
      (∀ k, β k < q.1 → col k = 0) ∧
      ∀ i, col (ix ⟨q.1, i⟩) = sym q.1 ⟨v (ix q), hv q⟩ i := by
    rintro ⟨a, i'⟩
    have key := step a (v (ix ⟨a, i'⟩)) (hv ⟨a, i'⟩)
    have hy := hdown (r - (a + 1)) (a + 1) (by omega) key
    obtain ⟨c, hc0, hcL⟩ := conv _ _ hy
    refine ⟨c + ∑ i, sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i • Pi.single (ix ⟨a, i⟩) 1, ?_, ?_, ?_⟩
    · rw [map_add, map_sum, hcL]
      simp only [map_smul, Fintype.linearCombination_apply_single, one_smul]
      abel
    · intro k hk
      have hk' : β k < a := hk
      have h1 : c k = 0 := hc0 k (by simp only [Set.mem_setOf_eq, not_le]; omega)
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, h1, zero_add]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hne : k ≠ ix ⟨a, i⟩ := by
        rintro rfl; rw [hβix] at hk'; exact lt_irrefl _ hk'
      simp [Pi.single_apply, hne]
    · intro i
      have h1 : c (ix ⟨a, i⟩) = 0 := hc0 _ (by simp [hβix])
      simp [h1, Finset.sum_apply, Pi.single_apply, Sigma.mk.inj_iff]
  choose col hcolL hcol0 hcoldiag using hcol
  obtain ⟨N, hNix, hNout⟩ : ∃ N : Matrix (Fin d) (Fin d) E, (∀ q, N (ix q) = col q) ∧
      (∀ k, k ∉ Set.range ix → N k = Pi.single k 1) := by
    refine ⟨Matrix.of fun k => if h : k ∈ Set.range ix then col (Classical.choose (Set.mem_range.1 h))
      else Pi.single k 1, ?_, ?_⟩
    · intro q
      have h : ix q ∈ Set.range ix := ⟨q, rfl⟩
      funext j
      simp only [Matrix.of_apply, dif_pos h]
      rw [ix.injective (Classical.choose_spec (Set.mem_range.1 h))]
    · intro k hk; funext j; simp only [Matrix.of_apply, dif_neg hk]
  have hNL : ∀ j, Fintype.linearCombination E z (N j) = v j := by
    intro j
    by_cases hj : j ∈ Set.range ix
    · obtain ⟨q, rfl⟩ := hj; rw [hNix]; exact hcolL q
    · rw [hNout j hj, Fintype.linearCombination_apply_single, one_smul]; exact hzv j hj
  have hBT : N.BlockTriangular β := by
    intro i j hij
    by_cases hi : i ∈ Set.range ix
    · obtain ⟨q, rfl⟩ := hi; rw [hNix]; exact hcol0 q j (by rw [hβix] at hij; exact hij)
    · rw [hNout i hi, Pi.single_apply, if_neg]; rintro rfl; exact lt_irrefl _ hij
  have hdet : N.det = ∏ a : Fin r,
      (Matrix.of fun i i' : I a => sym a ⟨v (ix ⟨a, i'⟩), hv ⟨a, i'⟩⟩ i).det := by
    rw [hBT.det]
    have himg : Finset.image β Finset.univ ⊆ Finset.range (r + 1) := by
      intro b hb
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hb
      simp only [Finset.mem_range]; have := hβle k; omega
    rw [Finset.prod_subset himg ?_]
    · rw [Finset.prod_range_succ]
      have hlast : (N.toSquareBlock β r).det = 1 := by
        have : N.toSquareBlock β r = 1 := by
          ext ⟨i, hi⟩ ⟨j, hj⟩
          have hi' : i ∉ Set.range ix := by
            rintro ⟨q, rfl⟩; rw [hβix] at hi; have := q.1.isLt; omega
          rw [Matrix.toSquareBlock_def, Matrix.of_apply, hNout i hi', Pi.single_apply,
            Matrix.one_apply]
          simp only [Subtype.mk.injEq, eq_comm]
        rw [this, Matrix.det_one]
      rw [hlast, mul_one, ← Fin.prod_univ_eq_prod_range (fun x => (N.toSquareBlock β x).det) r]
      refine Finset.prod_congr rfl fun a _ => ?_
      have hinj : Function.Injective
          (fun i : I a => (⟨ix ⟨a, i⟩, hβix _⟩ : {k // β k = (a : ℕ)})) := by
        intro i i' h
        simp only [Subtype.mk.injEq, ix.apply_eq_iff_eq, Sigma.mk.inj_iff, heq_eq_eq,
          true_and] at h
        exact h
      have hsurj : Function.Surjective
          (fun i : I a => (⟨ix ⟨a, i⟩, hβix _⟩ : {k // β k = (a : ℕ)})) := by
        rintro ⟨k, hk⟩
        by_cases hkr : k ∈ Set.range ix
        · obtain ⟨⟨b, i⟩, rfl⟩ := hkr
          rw [hβix] at hk
          have hab : b = a := Fin.ext hk
          subst hab
          exact ⟨i, rfl⟩
        · rw [hβout k hkr] at hk; have := a.isLt; omega
      let e := Equiv.ofBijective _ ⟨hinj, hsurj⟩
      show (N.toSquareBlock β a).det = _
      rw [← Matrix.det_submatrix_equiv_self e, ← Matrix.det_transpose]
      congr 1
      ext i i'
      show N (ix ⟨a, i'⟩) (ix ⟨a, i⟩) = _
      rw [hNix]
      exact hcoldiag ⟨a, i'⟩ i
    · intro b _ hb
      haveI : IsEmpty {i // β i = b} :=
        ⟨fun ⟨i, hi⟩ => hb (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩)⟩
      exact Matrix.det_isEmpty
  have hv' : v = fun j => Fintype.linearCombination E z (N j) := funext fun j => (hNL j).symm
  rw [show ω v = ω (fun j => Fintype.linearCombination E z (N j)) from congrArg _ hv',
]
  refine (alt_linComb ω z N).trans ?_
  rw [← hdet]
  rfl

end GlobalTheory.FiltDet
