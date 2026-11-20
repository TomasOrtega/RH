import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.DerCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

section Cofinal

variable {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]

/- English proof (translation)
Establish `: Ring.KrullDimLE 0 (B ⧸ maximalIdeal B ^ j)`. Use `Ring.krullDimLE_zero_iff.2 fun P hP => ?_` and prove the remaining obligations. Establish `hc : (P.comap (Ideal.Quotient.mk (maximalIdeal B ^ j))).IsPrime` using `Ideal.comap_isPrime _ _`. Establish `hle : maximalIdeal B ≤ P.comap (Ideal.Quotient.mk (maximalIdeal B ^ j))` using `fun x hx => by`. Use `hc.mem_of_pow_mem j ?_` and prove the remaining obligations.

Establish `: Ideal.Quotient.mk (maximalIdeal B ^ j) (x ^ j) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hx j)`. Use `show Ideal.Quotient.mk _ (x ^ j) ∈ P`. Rewrite using `[this]`. Conclude with `zero_mem _`. Establish `he : P.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) = maximalIdeal B` using `((maximalIdeal.isMaximal B).eq_of_le hc.ne_top hle).symm`.

Use `⟨⟨hP.ne_top, fun J hJ => ?_⟩⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hc' : J.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) ≠ ⊤` using `fun h => hne (by rw [Ideal.eq_top_iff_one]; simpa using (Ideal.eq_top_iff_one _).1 h)`. Establish `h1 : J.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) = P.comap (Ideal.Quotient.mk (maximalIdeal B ^ j))` using `le_antisymm ((le_maximalIdeal hc').trans he.ge) (Ideal.comap_mono hJ.le)`. Conclude with `hJ.ne' (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective h1)`.

Conclude with `IsNoetherianRing.isArtinianRing_of_krullDimLE_zero`.
-/
private theorem artinian_quot (j : ℕ) : IsArtinianRing (B ⧸ maximalIdeal B ^ j) := by
  have : Ring.KrullDimLE 0 (B ⧸ maximalIdeal B ^ j) := by
    refine Ring.krullDimLE_zero_iff.2 fun P hP => ?_
    have hc : (P.comap (Ideal.Quotient.mk (maximalIdeal B ^ j))).IsPrime := Ideal.comap_isPrime _ _
    have hle : maximalIdeal B ≤ P.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) := fun x hx => by
      refine hc.mem_of_pow_mem j ?_
      have : Ideal.Quotient.mk (maximalIdeal B ^ j) (x ^ j) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hx j)
      show Ideal.Quotient.mk _ (x ^ j) ∈ P
      rw [this]
      exact zero_mem _
    have he : P.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) = maximalIdeal B :=
      ((maximalIdeal.isMaximal B).eq_of_le hc.ne_top hle).symm
    refine ⟨⟨hP.ne_top, fun J hJ => ?_⟩⟩
    by_contra hne
    have hc' : J.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) ≠ ⊤ := fun h =>
      hne (by rw [Ideal.eq_top_iff_one]; simpa using (Ideal.eq_top_iff_one _).1 h)
    have h1 : J.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) = P.comap (Ideal.Quotient.mk (maximalIdeal B ^ j)) :=
      le_antisymm ((le_maximalIdeal hc').trans he.ge) (Ideal.comap_mono hJ.le)
    exact hJ.ne' (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective h1)
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

/- English proof (translation)
Use `haveI := artinian_quot (B := B) j`. Set `f : ℕ →o (Ideal (B ⧸ maximalIdeal B ^ j))ᵒᵈ` to `⟨fun N => OrderDual.toDual ((I N).map (Ideal.Quotient.mk _)), fun a b h => Ideal.map_mono (hI h)⟩`. Take `⟨e, he⟩` from `IsArtinian.monotone_stabilizes f`. Use `⟨e, fun N hN a ha => ?_⟩` and prove the remaining obligations. Establish `h1 : Ideal.Quotient.mk (maximalIdeal B ^ j) a ∈ (I N).map (Ideal.Quotient.mk _)`.

Establish `h2 : (I e).map (Ideal.Quotient.mk (maximalIdeal B ^ j)) = (I N).map (Ideal.Quotient.mk _)` using `he N hN`. Rewrite using `[← h2]`. Conclude with `Ideal.mem_map_of_mem _ ha`. Take `⟨b, hb, h3⟩` from `(Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 h1`. Conclude with `⟨b, hb, Ideal.Quotient.eq.1 h3.symm⟩`.
-/
private theorem stab (I : ℕ → Ideal B) (hI : Antitone I) (j : ℕ) :
    ∃ e, ∀ N, e ≤ N → ∀ a ∈ I e, ∃ b ∈ I N, a - b ∈ maximalIdeal B ^ j := by
  haveI := artinian_quot (B := B) j
  let f : ℕ →o (Ideal (B ⧸ maximalIdeal B ^ j))ᵒᵈ :=
    ⟨fun N => OrderDual.toDual ((I N).map (Ideal.Quotient.mk _)), fun a b h => Ideal.map_mono (hI h)⟩
  obtain ⟨e, he⟩ := IsArtinian.monotone_stabilizes f
  refine ⟨e, fun N hN a ha => ?_⟩
  have h1 : Ideal.Quotient.mk (maximalIdeal B ^ j) a ∈ (I N).map (Ideal.Quotient.mk _) := by
    have h2 : (I e).map (Ideal.Quotient.mk (maximalIdeal B ^ j)) = (I N).map (Ideal.Quotient.mk _) := he N hN
    rw [← h2]
    exact Ideal.mem_map_of_mem _ ha
  obtain ⟨b, hb, h3⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 h1
  exact ⟨b, hb, Ideal.Quotient.eq.1 h3.symm⟩

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Use `choose e he using fun j => stab I hI (k + j)`. Set `E : ℕ → ℕ` to `fun j => (Finset.range (j + 1)).sup e + j`. Establish `hE : Monotone E` using `monotone_nat_of_le_succ fun j => Nat.add_le_add (Finset.sup_mono (Finset.range_mono (Nat.le_succ _))) (Nat.le_succ _)`.

Establish `hEe : ∀ j, e j ≤ E j` using `fun j => le_trans (Finset.le_sup (f := e) (Finset.self_mem_range_succ j)) (Nat.le_add_right _ _)`. Establish `hEj : ∀ j, j ≤ E j` using `fun j => Nat.le_add_left _ _`. Set `P : ℕ → B → Prop` to `fun j x => x ∈ I (E j) ∧ x ∉ maximalIdeal B ^ k`. Establish `step : ∀ j x, P j x → ∃ y, P (j + 1) y ∧ x - y ∈ maximalIdeal B ^ (k + j)`. Introduce and unpack `j x ⟨h1, h2⟩`.

Take `⟨y, hy, hd⟩` from `he j (E (j + 1)) ((hEe j).trans (hE (Nat.le_succ j))) x (hI (hEe j) h1)`. Use `⟨y, ⟨hy, fun h => h2 ?_⟩, hd⟩` and prove the remaining obligations. Use `add_mem (Ideal.pow_le_pow_right (Nat.le_add_right k j) hd) h` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Take `⟨x₀, h1, h2⟩` from `SetLike.not_le_iff_exists.1 (hcon (E 0))`.

Set `a : ∀ j, {x // P j x}` to `fun j => Nat.rec ⟨x₀, h1, h2⟩ (fun j x => ⟨(step j x.1 x.2).choose, (step j x.1 x.2).choose_spec.1⟩) j`. Establish `ha : ∀ j, (a j).1 - (a (j + 1)).1 ∈ maximalIdeal B ^ (k + j)` using `fun j => (step j (a j).1 (a j).2).choose_spec.2`. Establish `hchain : ∀ m n, m ≤ n → (a m).1 - (a n).1 ∈ maximalIdeal B ^ (k + m)`. Introduce `m n hmn`. Proceed by induction on `n, hmn using Nat.le_induction with`.

Consider the case `base => simp`. Consider the case `succ n hmn ih`. Use `add_mem ih (Ideal.pow_le_pow_right (Nat.add_le_add_left hmn k) (ha n))` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis. Establish `hsm : ∀ j : ℕ, (maximalIdeal B ^ j • ⊤ : Ideal B) = maximalIdeal B ^ j` using `fun j => by simp`.

Take `⟨L, hL⟩` from `IsPrecomplete.prec (I := maximalIdeal B) (M := B) inferInstance (f := fun j => (a j).1) (fun {m n} hmn => by`. Rewrite using `[SModEq.sub_mem, hsm]`. Conclude with `Ideal.pow_le_pow_right (Nat.le_add_left _ _) (hchain m n hmn))`. Establish `hL' : ∀ j, (a j).1 - L ∈ maximalIdeal B ^ j` using `fun j => by`. Use `SModEq.sub_mem.1 (hL j)` as an intermediate fact.

Simplify using `using this`. Establish `hmem : ∀ N, L ∈ I N`. Introduce `N`. Distinguish the cases in `hNt : I N = ⊤`. Simplify using `[hNt]`.

Establish `hb : ⨅ i, maximalIdeal B ^ i • (⊤ : Submodule B (B ⧸ I N)) = ⊥` using `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal B).ne_top`. Establish `: Ideal.Quotient.mk (I N) L ∈ (⊥ : Submodule B (B ⧸ I N))`. Rewrite using `[← hb]`. Use `(Submodule.mem_iInf _).2 fun j => ?_` and prove the remaining obligations. Establish `h3 : (a (max j N)).1 ∈ I N` using `hI ((le_max_right j N).trans (hEj _)) (a (max j N)).2.1`.

Establish `h4` using `Ideal.pow_le_pow_right (le_max_left j N) (hL' (max j N))`. Establish `h5 : Ideal.Quotient.mk (I N) L = ((a (max j N)).1 - L) • (-1 : B ⧸ I N)`. Rewrite using `[Algebra.smul_def]`. Establish `: Ideal.Quotient.mk (I N) (a (max j N)).1 = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 h3`. Simplify using `[Ideal.Quotient.algebraMap_eq, this]`.

Rewrite using `[h5]`. Conclude with `Submodule.smul_mem_smul h4 trivial`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 this`. Establish `hz : L = 0`. Establish `: L ∈ ⨅ N, I N` using `(Submodule.mem_iInf _).2 hmem`.

Rewrite `this` using `[h0]`. Then use the resulting hypothesis. Use `hL' k` as an intermediate fact. Rewrite `this` using `[hz, sub_zero]`. Establish `h6` using `(a k).2.2`. Conclude with `h6 this`.
-/
private theorem cofinal [IsAdicComplete (maximalIdeal B) B] (I : ℕ → Ideal B) (hI : Antitone I)
    (h0 : ⨅ N, I N = ⊥) (k : ℕ) : ∃ N, I N ≤ maximalIdeal B ^ k := by
  by_contra hcon
  push_neg at hcon
  choose e he using fun j => stab I hI (k + j)

  let E : ℕ → ℕ := fun j => (Finset.range (j + 1)).sup e + j
  have hE : Monotone E := monotone_nat_of_le_succ fun j =>
    Nat.add_le_add (Finset.sup_mono (Finset.range_mono (Nat.le_succ _))) (Nat.le_succ _)
  have hEe : ∀ j, e j ≤ E j := fun j =>
    le_trans (Finset.le_sup (f := e) (Finset.self_mem_range_succ j)) (Nat.le_add_right _ _)
  have hEj : ∀ j, j ≤ E j := fun j => Nat.le_add_left _ _
  let P : ℕ → B → Prop := fun j x => x ∈ I (E j) ∧ x ∉ maximalIdeal B ^ k
  have step : ∀ j x, P j x → ∃ y, P (j + 1) y ∧ x - y ∈ maximalIdeal B ^ (k + j) := by
    rintro j x ⟨h1, h2⟩
    obtain ⟨y, hy, hd⟩ := he j (E (j + 1)) ((hEe j).trans (hE (Nat.le_succ j))) x (hI (hEe j) h1)
    refine ⟨y, ⟨hy, fun h => h2 ?_⟩, hd⟩
    have := add_mem (Ideal.pow_le_pow_right (Nat.le_add_right k j) hd) h
    rwa [sub_add_cancel] at this
  obtain ⟨x₀, h1, h2⟩ := SetLike.not_le_iff_exists.1 (hcon (E 0))
  let a : ∀ j, {x // P j x} := fun j => Nat.rec ⟨x₀, h1, h2⟩
    (fun j x => ⟨(step j x.1 x.2).choose, (step j x.1 x.2).choose_spec.1⟩) j
  have ha : ∀ j, (a j).1 - (a (j + 1)).1 ∈ maximalIdeal B ^ (k + j) := fun j =>
    (step j (a j).1 (a j).2).choose_spec.2
  have hchain : ∀ m n, m ≤ n → (a m).1 - (a n).1 ∈ maximalIdeal B ^ (k + m) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := add_mem ih (Ideal.pow_le_pow_right (Nat.add_le_add_left hmn k) (ha n))
      rwa [sub_add_sub_cancel] at this
  have hsm : ∀ j : ℕ, (maximalIdeal B ^ j • ⊤ : Ideal B) = maximalIdeal B ^ j := fun j => by simp
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := maximalIdeal B) (M := B) inferInstance
    (f := fun j => (a j).1) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hsm]
      exact Ideal.pow_le_pow_right (Nat.le_add_left _ _) (hchain m n hmn))
  have hL' : ∀ j, (a j).1 - L ∈ maximalIdeal B ^ j := fun j => by
    have := SModEq.sub_mem.1 (hL j)
    simpa using this
  have hmem : ∀ N, L ∈ I N := by
    intro N
    by_cases hNt : I N = ⊤
    · simp [hNt]
    have hb : ⨅ i, maximalIdeal B ^ i • (⊤ : Submodule B (B ⧸ I N)) = ⊥ :=
      Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal B).ne_top
    have : Ideal.Quotient.mk (I N) L ∈ (⊥ : Submodule B (B ⧸ I N)) := by
      rw [← hb]
      refine (Submodule.mem_iInf _).2 fun j => ?_
      have h3 : (a (max j N)).1 ∈ I N := hI ((le_max_right j N).trans (hEj _)) (a (max j N)).2.1
      have h4 := Ideal.pow_le_pow_right (le_max_left j N) (hL' (max j N))
      have h5 : Ideal.Quotient.mk (I N) L = ((a (max j N)).1 - L) • (-1 : B ⧸ I N) := by
        rw [Algebra.smul_def]
        have : Ideal.Quotient.mk (I N) (a (max j N)).1 = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h3
        simp [Ideal.Quotient.algebraMap_eq, this]
      rw [h5]
      exact Submodule.smul_mem_smul h4 trivial
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  have hz : L = 0 := by
    have : L ∈ ⨅ N, I N := (Submodule.mem_iInf _).2 hmem
    rwa [h0] at this
  have := hL' k
  rw [hz, sub_zero] at this
  have h6 := (a k).2.2
  exact h6 this

end Cofinal

section Der

variable {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing K] [Algebra O K]

/- English proof (translation)
Establish `h1 : D 1 = 0`. Use `hD 1 1` as an intermediate fact. Simplify using `only [mul_one, map_one, one_mul] at this`. Take the linear combination `(-1 : K) * this`. Proceed by induction on `hx using Algebra.adjoin_induction with`.

Consider the case `mem x hx => exact h x hx`. Consider the case `algebraMap a`. Use `⟨A.algebraMap_mem a, ?_⟩` and prove the remaining obligations. Establish `: (⟨algebraMap O R a, A.algebraMap_mem a⟩ : A) = a • (1 : A)`. Use `ext`.

Simplify using `[Algebra.smul_def]`. Rewrite using `[this, map_smul, h1, smul_zero]`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`.

Use `⟨add_mem a b, ?_⟩` and prove the remaining obligations. Establish `: (⟨x + y, add_mem a b⟩ : A) = ⟨x, a⟩ + ⟨y, b⟩` using `rfl`. Rewrite using `[this, map_add, ha, hb, add_zero]`. Consider the case `mul x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`.

Take `⟨b, hb⟩` from `hy`. Use `⟨mul_mem a b, ?_⟩` and prove the remaining obligations. Establish `: (⟨x * y, mul_mem a b⟩ : A) = ⟨x, a⟩ * ⟨y, b⟩` using `rfl`. Rewrite using `[this, hD, ha, hb, mul_zero, mul_zero, add_zero]`.
-/
private theorem kill (A : Subalgebra O R) (ξ : A →ₐ[O] K) (D : A →ₗ[O] K)
    (hD : ∀ f g, D (f * g) = ξ f * D g + ξ g * D f) (s : Set R)
    (h : ∀ x ∈ s, ∃ hx : x ∈ A, D ⟨x, hx⟩ = 0) {x : R} (hx : x ∈ Algebra.adjoin O s) :
    ∃ h : x ∈ A, D ⟨x, h⟩ = 0 := by
  have h1 : D 1 = 0 := by
    have := hD 1 1
    simp only [mul_one, map_one, one_mul] at this
    linear_combination (-1 : K) * this
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap a =>
    refine ⟨A.algebraMap_mem a, ?_⟩
    have : (⟨algebraMap O R a, A.algebraMap_mem a⟩ : A) = a • (1 : A) := by
      ext
      simp [Algebra.smul_def]
    rw [this, map_smul, h1, smul_zero]
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨add_mem a b, ?_⟩
    have : (⟨x + y, add_mem a b⟩ : A) = ⟨x, a⟩ + ⟨y, b⟩ := rfl
    rw [this, map_add, ha, hb, add_zero]
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨mul_mem a b, ?_⟩
    have : (⟨x * y, mul_mem a b⟩ : A) = ⟨x, a⟩ * ⟨y, b⟩ := rfl
    rw [this, hD, ha, hb, mul_zero, mul_zero, add_zero]

end Der

section Close

variable {O R K : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
  [NormedField K] [Algebra O K]

/- English proof (translation)
Set `I : ℕ → Ideal B` to `fun N => (maximalIdeal R ^ N).comap (B.val : B →+* R)`. Establish `hI : Antitone I` using `fun a b h => Ideal.comap_mono (Ideal.pow_le_pow_right h)`. Establish `h0 : ⨅ N, I N = ⊥`. Use `eq_bot_iff.2 fun x hx => ?_` and prove the remaining obligations. Establish `h1 : (x : R) ∈ ⨅ N : ℕ, maximalIdeal R ^ N` using `(Submodule.mem_iInf _).2 fun N => (Submodule.mem_iInf _).1 hx N`.

Rewrite `h1` using `[Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top, Ideal.mem_bot]`. Conclude with `Subtype.ext h1`. Use extensionality with `x`. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖E x‖ / 2` using `half_pos (norm_pos_iff.2 hne)`.

Take `⟨k, hk⟩` from `hc _ hpos`. Take `⟨N, hN⟩` from `cofinal I hI h0 k`. Take `⟨t, ht, hd'⟩` from `hd x N`. Establish `h2` using `hk (x - t) (hN hd')`. Rewrite `h2` using `[map_sub, hT t ht, sub_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem close_zero (B : Subalgebra O R) [hB : IsCO O B]
    (hm : maximalIdeal B = (maximalIdeal R).comap (B.val : B →+* R)) (E : B →ₗ[O] K)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a ∈ maximalIdeal B ^ k, ‖E a‖ ≤ ε) (T : Set B) (hT : ∀ t ∈ T, E t = 0)
    (hd : ∀ x : B, ∀ N : ℕ, ∃ t ∈ T, ((x - t : B) : R) ∈ maximalIdeal R ^ N) : E = 0 := by
  let I : ℕ → Ideal B := fun N => (maximalIdeal R ^ N).comap (B.val : B →+* R)
  have hI : Antitone I := fun a b h => Ideal.comap_mono (Ideal.pow_le_pow_right h)
  have h0 : ⨅ N, I N = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have h1 : (x : R) ∈ ⨅ N : ℕ, maximalIdeal R ^ N := (Submodule.mem_iInf _).2 fun N =>
      (Submodule.mem_iInf _).1 hx N
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top, Ideal.mem_bot] at h1
    exact Subtype.ext h1
  ext x
  by_contra hne
  have hpos : 0 < ‖E x‖ / 2 := half_pos (norm_pos_iff.2 hne)
  obtain ⟨k, hk⟩ := hc _ hpos
  obtain ⟨N, hN⟩ := cofinal I hI h0 k
  obtain ⟨t, ht, hd'⟩ := hd x N
  have h2 := hk (x - t) (hN hd')
  rw [map_sub, hT t ht, sub_zero] at h2
  linarith

end Close

/- English proof (translation)
Introduce `l _ c _ F C₀ n hF hn S ξ D hD hr hψ`. Take `⟨hco, hm⟩` from `Fr.co_B hF hn S`. Use `haveI := hco`. Establish `hD' : ∀ f g, D (f * g) = ξ f * D g + ξ g * D f` using `hD`. Establish `hs : ∀ x ∈ ({x | ∃ g i j, x = S.ρ.r g i j} ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)} : Set S.R), ∃ hx : x ∈ S.A, D ⟨x, hx⟩ = 0`.

Introduce and unpack `x (⟨g, i, j, rfl⟩ | ⟨v, i, g, rfl⟩)`. Conclude with `⟨S.r_mem g i j, hr g i j⟩`. Conclude with `⟨S.B_le_A (S.ψ_mem v i g), hψ v i g⟩`. Establish `hadj : Algebra.adjoin c.O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}) ≤ Algebra.adjoin c.O ({x | ∃ g i j, x = S.ρ.r g i j} ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)})`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations.

Introduce and unpack `x (⟨L, -, rfl⟩ | hx)`. Use `Subalgebra.list_prod_mem _ fun y hy => ?_` and prove the remaining obligations. Take `⟨s, -, rfl⟩` from `List.mem_map.1 hy`. Conclude with `Algebra.subset_adjoin (Or.inl ⟨_, _, _, rfl⟩)`. Conclude with `Algebra.subset_adjoin (Or.inr hx)`.

Establish `hB : D ∘ₗ S.inc.toLinearMap = 0`. Use `close_zero S.B (hm.trans rfl) _ (fun ε hε => ?_) {t | (t : S.R) ∈ Algebra.adjoin c.O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)})} (fun t ht => ?_) (fun x N => ?_)` and prove the remaining obligations. Establish `hDB : D ∘ₗ S.inc.toLinearMap ∈ PtDer (ξ.comp S.inc) (Qbar l)` using `fun f g => by`. Simplify using `using hD (S.inc f) (S.inc g)`. Take `⟨k, hk⟩` from `derCont l c S.B (ξ.comp S.inc) _ hDB ε hε`.

Conclude with `⟨k, fun a ha => (hk a ha).1⟩`. Take `⟨_, h⟩` from `kill S.A ξ D hD' _ hs (hadj ht)`. Conclude with `h`. Take `⟨y, hy, h⟩` from `x.2 N`. Conclude with `⟨⟨y, Fr.le_adicClosure _ hy⟩, hy, h⟩`.

Use extensionality with `⟨x, hx⟩`. Take `⟨_, h⟩` from `kill S.A ξ D hD' ((S.B : Set S.R) ∪ {x | ∃ g i j, x = S.ρ.r g i j}) (by`. Introduce and unpack `x (hx | ⟨g, i, j, rfl⟩)`. Conclude with `⟨S.B_le_A hx, LinearMap.congr_fun hB ⟨x, hx⟩⟩`. Conclude with `⟨S.r_mem g i j, hr g i j⟩) hx`.

Conclude with `h`.
-/
theorem UpperTheory.V.J.derExt :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ ξ : S.A →ₐ[c.O] Qbar l, ∀ D ∈ PtDer ξ (Qbar l), (∀ g i j, D (S.u.r g i j) = 0) → (∀ v i g, D (S.u.ψ v i g : S.A) = 0) → D = 0 := by
  intro l _ c _ F C₀ n hF hn S ξ D hD hr hψ
  obtain ⟨hco, hm⟩ := Fr.co_B hF hn S
  haveI := hco
  have hD' : ∀ f g, D (f * g) = ξ f * D g + ξ g * D f := hD

  have hs : ∀ x ∈ ({x | ∃ g i j, x = S.ρ.r g i j} ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)} : Set S.R),
      ∃ hx : x ∈ S.A, D ⟨x, hx⟩ = 0 := by
    rintro x (⟨g, i, j, rfl⟩ | ⟨v, i, g, rfl⟩)
    · exact ⟨S.r_mem g i j, hr g i j⟩
    · exact ⟨S.B_le_A (S.ψ_mem v i g), hψ v i g⟩
  have hadj : Algebra.adjoin c.O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}) ≤
      Algebra.adjoin c.O ({x | ∃ g i j, x = S.ρ.r g i j} ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}) := by
    refine Algebra.adjoin_le ?_
    rintro x (⟨L, -, rfl⟩ | hx)
    · refine Subalgebra.list_prod_mem _ fun y hy => ?_
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hy
      exact Algebra.subset_adjoin (Or.inl ⟨_, _, _, rfl⟩)
    · exact Algebra.subset_adjoin (Or.inr hx)

  have hB : D ∘ₗ S.inc.toLinearMap = 0 := by
    refine close_zero S.B (hm.trans rfl) _ (fun ε hε => ?_)
      {t | (t : S.R) ∈ Algebra.adjoin c.O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)})} (fun t ht => ?_)
      (fun x N => ?_)
    · have hDB : D ∘ₗ S.inc.toLinearMap ∈ PtDer (ξ.comp S.inc) (Qbar l) := fun f g => by
        simpa using hD (S.inc f) (S.inc g)
      obtain ⟨k, hk⟩ := derCont l c S.B (ξ.comp S.inc) _ hDB ε hε
      exact ⟨k, fun a ha => (hk a ha).1⟩
    · obtain ⟨_, h⟩ := kill S.A ξ D hD' _ hs (hadj ht)
      exact h
    · obtain ⟨y, hy, h⟩ := x.2 N
      exact ⟨⟨y, Fr.le_adicClosure _ hy⟩, hy, h⟩

  ext ⟨x, hx⟩
  obtain ⟨_, h⟩ := kill S.A ξ D hD' ((S.B : Set S.R) ∪ {x | ∃ g i j, x = S.ρ.r g i j}) (by
    rintro x (hx | ⟨g, i, j, rfl⟩)
    · exact ⟨S.B_le_A hx, LinearMap.congr_fun hB ⟨x, hx⟩⟩
    · exact ⟨S.r_mem g i j, hr g i j⟩) hx
  exact h
