import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormLineSectionPow

namespace ReciprocityTheory.ChartRestriction.G.T0

noncomputable def upMk {D N : ℕ} (ab : (Fin (D + 2) →₀ ℕ) × (Option (Fin (D + 2) × Fin (N + 1)) →₀ ℕ)) :
    UXVar D N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim (fun p => ab.2 (some p)) (fun i => ab.1 i))

noncomputable def upMono (D N n n' : ℕ) : Finset (UXVar D N →₀ ℕ) :=
  ((Finset.univ : Finset (Fin (D + 2))).finsuppAntidiag n ×ˢ
    (Finset.univ : Finset (Option (Fin (D + 2) × Fin (N + 1)))).finsuppAntidiag n').image upMk

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem upMk_apply_inl {D N : ℕ} (ab : (Fin (D + 2) →₀ ℕ) × (Option (Fin (D + 2) × Fin (N + 1)) →₀ ℕ))
    (p : Fin (D + 2) × Fin (N + 1)) : upMk ab (Sum.inl p) = ab.2 (some p) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem upMk_apply_inr {D N : ℕ} (ab : (Fin (D + 2) →₀ ℕ) × (Option (Fin (D + 2) × Fin (N + 1)) →₀ ℕ))
    (i : Fin (D + 2)) : upMk ab (Sum.inr i) = ab.1 i := rfl

/- English proof (translation)
Unfold `upMono`. Rewrite using `[Finset.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨a, b⟩, hab, rfl⟩`. Rewrite `hab` using `[Finset.mem_product, Finset.mem_finsuppAntidiag, Finset.mem_finsuppAntidiag]`.

Take `⟨⟨ha, -⟩, ⟨hb, -⟩⟩` from `hab`. Apply the tactic sequence `try dsimp only at ha hb`. Rewrite `hb` using `[Fintype.sum_option]`. Prove the components needed by the constructor for the conclusion. Unfold `xDeg`.

Simplify `ha` using `only [upMk_apply_inr]`. Unfold `uDeg`. Simplify using `only [upMk_apply_inl]`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨hx, hu⟩`.

Use `⟨(Finsupp.equivFunOnFinite.symm (fun i => s (Sum.inr i)), Finsupp.equivFunOnFinite.symm (fun o => Option.elim o (n' - uDeg s) (fun p => s (Sum.inl p)))), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_product, Finset.mem_finsuppAntidiag, Finset.mem_finsuppAntidiag]`. Use `⟨⟨?_, Finset.subset_univ _⟩, ⟨?_, Finset.subset_univ _⟩⟩` and prove the remaining obligations. Simplify `hx` using `[xDeg]`. Rewrite using `[Fintype.sum_option]`.

Simplify using `only [Finsupp.coe_equivFunOnFinite_symm, Option.elim]`. Unfold `uDeg at hu ⊢`. Use linear arithmetic over natural numbers and integers. Use extensionality with `x`. Apply the tactic sequence `cases x <;> simp [upMk]`.
-/
theorem mem_upMono {D N n n' : ℕ} {s : UXVar D N →₀ ℕ} :
    s ∈ upMono D N n n' ↔ xDeg s = n ∧ uDeg s ≤ n' := by
  classical
  unfold upMono
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    rw [Finset.mem_product, Finset.mem_finsuppAntidiag, Finset.mem_finsuppAntidiag] at hab
    obtain ⟨⟨ha, -⟩, ⟨hb, -⟩⟩ := hab
    try dsimp only at ha hb
    rw [Fintype.sum_option] at hb
    constructor
    · unfold xDeg
      simpa only [upMk_apply_inr] using ha
    · unfold uDeg
      simp only [upMk_apply_inl]
      omega
  · rintro ⟨hx, hu⟩
    refine ⟨(Finsupp.equivFunOnFinite.symm (fun i => s (Sum.inr i)),
      Finsupp.equivFunOnFinite.symm (fun o => Option.elim o (n' - uDeg s) (fun p => s (Sum.inl p)))), ?_, ?_⟩
    · rw [Finset.mem_product, Finset.mem_finsuppAntidiag, Finset.mem_finsuppAntidiag]
      refine ⟨⟨?_, Finset.subset_univ _⟩, ⟨?_, Finset.subset_univ _⟩⟩
      · simpa [xDeg] using hx
      · rw [Fintype.sum_option]
        simp only [Finsupp.coe_equivFunOnFinite_symm, Option.elim]
        unfold uDeg at hu ⊢
        omega
    · ext x
      cases x <;> simp [upMk]

/- English proof (translation)
Unfold `upMono cardUX`. Rewrite using `[Finset.card_image_of_injOn, Finset.card_product, Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]`. Use `congr 1`. Rewrite using `[show D + 2 + n - 1 = n + (D + 1) by omega, Nat.choose_symm_add, Nat.add_assoc]`. Rewrite using `[show (D + 2) * (N + 1) + 1 + n' - 1 = n' + (D + 2) * (N + 1) by omega, Nat.choose_symm_add]`.

Introduce and unpack `⟨a, b⟩ hab ⟨a', b'⟩ hab' h`. Simplify using `only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_finsuppAntidiag] at hab hab'`. Establish `h1 : ∀ i, a i = a' i` using `fun i => by`. Use `congrArg (fun s => s (Sum.inr i)) h` as an intermediate fact. Simplify `this` using `[upMk]`.

Establish `h2 : ∀ p, b (some p) = b' (some p)` using `fun p => by`. Use `congrArg (fun s => s (Sum.inl p)) h` as an intermediate fact. Simplify `this` using `[upMk]`. Establish `hb` using `hab.2.1`. Establish `hb'` using `hab'.2.1`.

Rewrite `hb`, `hb'` using `[Fintype.sum_option]`. Establish `hs : ∑ p, b (some p) = ∑ p, b' (some p)` using `Finset.sum_congr rfl fun p _ => h2 p`. Establish `h3 : b none = b' none` using `by omega`. Use `Prod.ext (Finsupp.ext h1) (Finsupp.ext fun o => ?_)` and prove the remaining obligations. Consider the cases of `o`.

Conclude with `h3`. Conclude with `h2 _`.
-/
theorem card_upMono (D N n n' : ℕ) : (upMono D N n n').card = cardUX D N n n' := by
  classical
  unfold upMono cardUX
  rw [Finset.card_image_of_injOn, Finset.card_product, Finset.card_finsuppAntidiag_nat_eq_choose,
    Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Finset.card_univ, Fintype.card_fin,
    Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  · congr 1
    · rw [show D + 2 + n - 1 = n + (D + 1) by omega, Nat.choose_symm_add, Nat.add_assoc]
    · rw [show (D + 2) * (N + 1) + 1 + n' - 1 = n' + (D + 2) * (N + 1) by omega, Nat.choose_symm_add]
  · rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_finsuppAntidiag] at hab hab'
    have h1 : ∀ i, a i = a' i := fun i => by
      have := congrArg (fun s => s (Sum.inr i)) h
      simpa [upMk] using this
    have h2 : ∀ p, b (some p) = b' (some p) := fun p => by
      have := congrArg (fun s => s (Sum.inl p)) h
      simpa [upMk] using this
    have hb := hab.2.1
    have hb' := hab'.2.1
    rw [Fintype.sum_option] at hb hb'
    have hs : ∑ p, b (some p) = ∑ p, b' (some p) := Finset.sum_congr rfl fun p _ => h2 p
    have h3 : b none = b' none := by omega
    refine Prod.ext (Finsupp.ext h1) (Finsupp.ext fun o => ?_)
    cases o
    · exact h3
    · exact h2 _

end ReciprocityTheory.ChartRestriction.G.T0
