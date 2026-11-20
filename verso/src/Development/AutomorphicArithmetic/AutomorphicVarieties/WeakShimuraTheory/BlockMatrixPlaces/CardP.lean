import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

/- English proof (translation)
Introduce `A _ _ _ _ T _ _ _ _ P hsat hP n`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible A`. Establish `hm : maximalIdeal A = Ideal.span {ϖ}` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ`. Establish `hϖ0 : ϖ ≠ 0` using `hϖ.ne_zero`. Establish `hL : ∀ (k : ℕ) (z : T), z ∈ lev A T k ↔ ∃ t, ϖ ^ k • t = z`.

Introduce `k z`. Use `show z ∈ maximalIdeal A ^ k • (⊤ : Submodule A T) ↔ _`. Rewrite using `[hm, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Simplify using the standard rewrite rules. Establish `hfin : ∀ k, Finite (T ⧸ lev A T k)`.

Introduce `k`. Establish `h1 : (maximalIdeal A).FG` using `IsNoetherian.noetherian _`. Use `haveI : Finite (A ⧸ maximalIdeal A) := (inferInstance : Finite (ResidueField A))`. Use `haveI := Ideal.finite_quotient_pow h1 k`. Use `haveI : Finite (T ⧸ (⊤ : Submodule A T)) := inferInstance`.

Conclude with `Submodule.finite_quotient_smul _ (Module.finite_def.mp inferInstance)`. Take `⟨y, hyP, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hP`. Establish `hx : ∃ x ∈ P, x ∉ lev A T 1`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Establish `hall : ∀ k : ℕ, ∀ z ∈ P, z ∈ lev A T k`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `z _`.

Conclude with `(hL 0 z).mpr ⟨z, by simp⟩`. Consider the case `succ k ih`. Introduce `z hz`. Take `⟨t, rfl⟩` from `(hL 1 z).mp (hcon z hz)`. Establish `htP : t ∈ P` using `hsat _ _ (pow_ne_zero 1 hϖ0) hz`.

Take `⟨s, rfl⟩` from `(hL k t).mp (ih t htP)`. Conclude with `(hL (k + 1) _).mpr ⟨s, by rw [smul_smul, ← pow_add, add_comm 1 k]⟩`. Establish `hmem : y ∈ (⨅ i : ℕ, maximalIdeal A ^ i • (⊤ : Submodule A T))` using `Submodule.mem_iInf _ |>.mpr (fun i => hall i y hyP)`. Rewrite `hmem` using `[Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal A).ne_top]`. Conclude with `hy0 ((Submodule.mem_bot A).mp hmem)`.

Take `⟨x, hxP, hx1⟩` from `hx`. Use `⟨hfin n, ?_⟩` and prove the remaining obligations. Use `haveI := hfin n`. Establish `key : ∀ i j : ℕ, i < j → j < n → ϖ ^ i • x - ϖ ^ j • x ∉ lev A T n`. Introduce `i j hij hjn hmem`.

Take `⟨s, hs⟩` from `(hL n _).mp hmem`. Establish `e1 : ϖ ^ i • (ϖ ^ (n - i) • s) = ϖ ^ i • (x - ϖ ^ (j - i) • x)`. Rewrite using `[smul_smul, ← pow_add, Nat.add_sub_cancel' (by omega), hs, smul_sub, smul_smul, ← pow_add, Nat.add_sub_cancel' hij.le]`. Establish `e2 : ϖ ^ (n - i) • s = x - ϖ ^ (j - i) • x` using `smul_right_injective T (pow_ne_zero i hϖ0) e1`. Apply `hx1` to reduce the goal to its premises.

Rewrite using `[hL 1]`. Use `⟨ϖ ^ (n - i - 1) • s + ϖ ^ (j - i - 1) • x, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add, Nat.add_sub_cancel' (by omega : 1 ≤ n - i), Nat.add_sub_cancel' (by omega : 1 ≤ j - i), e2, sub_add_cancel]`. Set `f : Fin n → P.map (lev A T n).mkQ` to `fun i => ⟨(lev A T n).mkQ (ϖ ^ (i : ℕ) • x), Submodule.mem_map_of_mem (P.smul_mem _ hxP)⟩`. Establish `hf : Function.Injective f`.

Introduce `i j hij`. Establish `h' : (lev A T n).mkQ (ϖ ^ (i : ℕ) • x) = (lev A T n).mkQ (ϖ ^ (j : ℕ) • x)` using `congrArg Subtype.val hij`. Rewrite `h'` using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Break down `lt_trichotomy (i : ℕ) j with h | h | h` into its components or cases. Conclude with `absurd h' (key _ _ h j.2)`.

Conclude with `Fin.ext h`. Establish `h''` using `(lev A T n).neg_mem h'`. Rewrite `h''` using `[neg_sub]`. Conclude with `absurd h'' (key _ _ h i.2)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.Ws.Bl.cardP :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Finite (ResidueField A)] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (P : Submodule A T), (∀ (a : A) (x : T), a ≠ 0 → a • x ∈ P → x ∈ P) → P ≠ ⊥ →
          ∀ n, Finite (T ⧸ lev A T n) ∧ n ≤ Nat.card (P.map (lev A T n).mkQ) := by
  intro A _ _ _ _ T _ _ _ _ P hsat hP n
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hm : maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hL : ∀ (k : ℕ) (z : T), z ∈ lev A T k ↔ ∃ t, ϖ ^ k • t = z := by
    intro k z
    show z ∈ maximalIdeal A ^ k • (⊤ : Submodule A T) ↔ _
    rw [hm, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    simp
  have hfin : ∀ k, Finite (T ⧸ lev A T k) := by
    intro k
    have h1 : (maximalIdeal A).FG := IsNoetherian.noetherian _
    haveI : Finite (A ⧸ maximalIdeal A) := (inferInstance : Finite (ResidueField A))
    haveI := Ideal.finite_quotient_pow h1 k
    haveI : Finite (T ⧸ (⊤ : Submodule A T)) := inferInstance
    exact Submodule.finite_quotient_smul _ (Module.finite_def.mp inferInstance)
  obtain ⟨y, hyP, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  have hx : ∃ x ∈ P, x ∉ lev A T 1 := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ k : ℕ, ∀ z ∈ P, z ∈ lev A T k := by
      intro k
      induction k with
      | zero =>
        intro z _
        exact (hL 0 z).mpr ⟨z, by simp⟩
      | succ k ih =>
        intro z hz
        obtain ⟨t, rfl⟩ := (hL 1 z).mp (hcon z hz)
        have htP : t ∈ P := hsat _ _ (pow_ne_zero 1 hϖ0) hz
        obtain ⟨s, rfl⟩ := (hL k t).mp (ih t htP)
        exact (hL (k + 1) _).mpr ⟨s, by rw [smul_smul, ← pow_add, add_comm 1 k]⟩
    have hmem : y ∈ (⨅ i : ℕ, maximalIdeal A ^ i • (⊤ : Submodule A T)) :=
      Submodule.mem_iInf _ |>.mpr (fun i => hall i y hyP)
    rw [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _
      (IsLocalRing.maximalIdeal.isMaximal A).ne_top] at hmem
    exact hy0 ((Submodule.mem_bot A).mp hmem)
  obtain ⟨x, hxP, hx1⟩ := hx
  refine ⟨hfin n, ?_⟩
  haveI := hfin n
  have key : ∀ i j : ℕ, i < j → j < n → ϖ ^ i • x - ϖ ^ j • x ∉ lev A T n := by
    intro i j hij hjn hmem
    obtain ⟨s, hs⟩ := (hL n _).mp hmem
    have e1 : ϖ ^ i • (ϖ ^ (n - i) • s) = ϖ ^ i • (x - ϖ ^ (j - i) • x) := by
      rw [smul_smul, ← pow_add, Nat.add_sub_cancel' (by omega), hs, smul_sub, smul_smul,
        ← pow_add, Nat.add_sub_cancel' hij.le]
    have e2 : ϖ ^ (n - i) • s = x - ϖ ^ (j - i) • x :=
      smul_right_injective T (pow_ne_zero i hϖ0) e1
    apply hx1
    rw [hL 1]
    refine ⟨ϖ ^ (n - i - 1) • s + ϖ ^ (j - i - 1) • x, ?_⟩
    rw [smul_add, smul_smul, smul_smul, ← pow_add, ← pow_add,
      Nat.add_sub_cancel' (by omega : 1 ≤ n - i), Nat.add_sub_cancel' (by omega : 1 ≤ j - i),
      e2, sub_add_cancel]
  let f : Fin n → P.map (lev A T n).mkQ := fun i =>
    ⟨(lev A T n).mkQ (ϖ ^ (i : ℕ) • x), Submodule.mem_map_of_mem (P.smul_mem _ hxP)⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h' : (lev A T n).mkQ (ϖ ^ (i : ℕ) • x) = (lev A T n).mkQ (ϖ ^ (j : ℕ) • x) :=
      congrArg Subtype.val hij
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h'
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · exact absurd h' (key _ _ h j.2)
    · exact Fin.ext h
    · have h'' := (lev A T n).neg_mem h'
      rw [neg_sub] at h''
      exact absurd h'' (key _ _ h i.2)
  calc n = Nat.card (Fin n) := by simp
    _ ≤ _ := Nat.card_le_card_of_injective f hf
