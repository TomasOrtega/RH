import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne

open IsLocalRing Polynomial Matrix UpperTheory.V

/- English proof (translation)
Introduce `ι Q _ T d hT hu`. Use `choose f hf hf' using hu`. Establish `hfib : ∀ q, T q = {i | f i = q}`. Introduce `q`. Use extensionality with `i`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `(hf' i q h).symm`. Introduce `h`. Rewrite `h` using `[Set.mem_setOf_eq]`.

Rewrite using `[← h]`. Conclude with `hf i`. Break down `Nat.eq_zero_or_pos d with rfl | hd` into its components or cases. Establish `: IsEmpty ι` using `⟨fun i => by`. Establish `h` using `hT (f i)`.

Rewrite `h` using `[Set.ncard_eq_zero (Set.toFinite _)]`. Establish `hi : i ∈ T (f i)` using `hf i`. Rewrite `hi` using `[h]`. Simplify using `at hi⟩`. Rewrite using `[Nat.card_of_isEmpty (α := ι)]`.

Conclude with `dvd_zero _`. Establish `hne : ∀ q, (T q).Nonempty` using `fun q => Set.nonempty_of_ncard_ne_zero (by rw [hT q]; omega) choose g hg using hne`. Establish `ginj : Function.Injective g`. Introduce `q q' h`. Combine the equalities or inequalities in the displayed calculation.

Use `haveI : Finite Q := Finite.of_injective g ginj`. Use `letI : Fintype Q := Fintype.ofFinite Q`. Establish `hc : ∀ q, Nat.card {x // f x = q} = d` using `fun q => by`. Rewrite using `[← hT q, hfib q, ← Nat.card_coe_set_eq]`. Both sides reduce to the same expression.

Establish `key : Nat.card ι = Nat.card Q * d`. Rewrite using `[← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]`. Simplify using `only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]`. Rewrite using `[key]`. Conclude with `dvd_mul_right _ _`.
-/
theorem UpperTheory.V.Ws.card_dvd_of_partition_equal_size :
    ∀ (ι Q : Type) [Finite ι] (T : Q → Set ι) (d : ℕ), (∀ q, (T q).ncard = d) → (∀ i, ∃! q, i ∈ T q) →
      Nat.card Q ∣ Nat.card ι := by
  intro ι Q _ T d hT hu
  classical
  choose f hf hf' using hu
  have hfib : ∀ q, T q = {i | f i = q} := by
    intro q
    ext i
    constructor
    · intro h
      exact (hf' i q h).symm
    · intro h
      rw [Set.mem_setOf_eq] at h
      rw [← h]
      exact hf i
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : IsEmpty ι := ⟨fun i => by
      have h := hT (f i)
      rw [Set.ncard_eq_zero (Set.toFinite _)] at h
      have hi : i ∈ T (f i) := hf i
      rw [h] at hi
      simp at hi⟩
    rw [Nat.card_of_isEmpty (α := ι)]
    exact dvd_zero _
  · have hne : ∀ q, (T q).Nonempty := fun q =>
      Set.nonempty_of_ncard_ne_zero (by rw [hT q]; omega)
    choose g hg using hne
    have ginj : Function.Injective g := by
      intro q q' h
      calc q = f (g q) := hf' _ _ (hg q)
        _ = f (g q') := by rw [h]
        _ = q' := (hf' _ _ (hg q')).symm
    haveI : Finite Q := Finite.of_injective g ginj
    letI : Fintype Q := Fintype.ofFinite Q
    have hc : ∀ q, Nat.card {x // f x = q} = d := fun q => by
      rw [← hT q, hfib q, ← Nat.card_coe_set_eq]
      rfl
    have key : Nat.card ι = Nat.card Q * d := by
      rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
      simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
    rw [key]
    exact dvd_mul_right _ _
