import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIInfEigenspaceEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWIffGoodFormsOrthSum
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BadPlacesGoodCoefficients
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypeCharacterConjugateInverse

noncomputable section

open Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters

namespace GlobalTheory.GoodIdemFlip

section Local

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] {r : ℕ}

def invParam (s : SSParam p K r) : SSParam p K r := ⟨s.1, fun c => (s.2 c)⁻¹⟩

/- English proof (translation)
Use extensionality with `x`. Both sides reduce to the same expression.
-/
theorem cycChar_invParam (s : SSParam p K r) (c : Cyc (invParam s).1) : cycChar (invParam s) c = (cycChar s c)⁻¹ := by
  ext x; rfl

/- English proof (translation)
Establish `h : rootChar (invParam s) x = (cycChar s x.1)⁻¹ ^ (p ^ x.2.val)`. Rewrite using `[← cycChar_invParam s x.1]`. Both sides reduce to the same expression. Rewrite using `[h, inv_pow]`. Both sides reduce to the same expression.
-/
theorem rootChar_invParam (s : SSParam p K r) (x : Σ c : Cyc (invParam s).1, Fin (cycLen (invParam s).1 c)) :
    rootChar (invParam s) x = (rootChar s x)⁻¹ := by
  have h : rootChar (invParam s) x = (cycChar s x.1)⁻¹ ^ (p ^ x.2.val) := by
    rw [← cycChar_invParam s x.1]; rfl
  rw [h, inv_pow]
  rfl

/- English proof (translation)
Establish `: a⁻¹ / b⁻¹ = (a / b)⁻¹` using `by rw [inv_div_inv, inv_div]`. Simplify using `only [CongrMod, this, inv_pow, inv_eq_one]`.
-/
theorem congrMod_inv {A : Type} [CommGroup A] (l : ℕ) (a b : A) : CongrMod l a⁻¹ b⁻¹ ↔ CongrMod l a b := by
  have : a⁻¹ / b⁻¹ = (a / b)⁻¹ := by rw [inv_div_inv, inv_div]
  simp only [CongrMod, this, inv_pow, inv_eq_one]

/- English proof (translation)
Rewrite using `[← congrMod_inv, inv_inv]`.
-/
theorem congrMod_inv_left {A : Type} [CommGroup A] (l : ℕ) (a b : A) : CongrMod l a⁻¹ b ↔ CongrMod l a b⁻¹ := by
  rw [← congrMod_inv, inv_inv]

/- English proof (translation)
Use extensionality with `x`. Both sides reduce to the same expression.
-/
theorem inv_comp_baseNorm (χ : (ZMod p)ˣ →* Kˣ) (D : ℕ) :
    χ⁻¹.comp (baseNorm p D) = (χ.comp (baseNorm p D))⁻¹ := by
  ext x; rfl

/- English proof (translation)
Take `⟨h1, h2, ⟨h3, h3'⟩, h4, v5, h5⟩` from `hs`. Use `⟨fun v => ?_, fun l hl hl' v => ?_, ⟨fun l hl hl' v => ?_, fun v => ?_⟩, ?_, v5, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rcases h v with e | e <;> rw [e]`. Conclude with `h1 v`. Introduce `x y hxy`.

Rewrite `hxy` using `[rootChar_invParam, rootChar_invParam]`. Conclude with `h1 v (inv_injective hxy)`. Apply the tactic sequence `rcases h v with e | e <;> rw [e]`. Conclude with `h2 l hl hl' v`. Introduce `x y hxy`.

Rewrite using `[rootChar_invParam, rootChar_invParam, congrMod_inv]`. Conclude with `h2 l hl hl' v x y hxy`. Apply the tactic sequence `rcases h v with e | e <;> rw [e]`. Conclude with `h3 l hl hl' v`. Introduce `j c`.

Use `h3 l hl hl' v j c` as an intermediate fact. Rewrite `this` using `[inv_comp_baseNorm]`. Rewrite using `[cycChar_invParam, inv_comp_baseNorm, congrMod_inv, congrMod_inv_left]`. Conclude with `this.symm`. Apply the tactic sequence `rcases h v with e | e <;> rw [e]`.

Conclude with `h3' v`. Introduce `j x`. Use `h3' v j x` as an intermediate fact. Rewrite `this` using `[inv_comp_baseNorm]`. Rewrite using `[rootChar_invParam, inv_comp_baseNorm, Ne, Ne, inv_inj, inv_eq_iff_eq_inv]`.

Conclude with `this.symm`. Introduce and unpack `⟨a, ha, ha', hA⟩`. Use `h4 ⟨a, ha, ha', fun v => ?_⟩` and prove the remaining obligations. Use `hA v` as an intermediate fact. Apply the tactic sequence `rcases h v with e | e <;> rw [e] at this <;> exact this`.

Apply the tactic sequence `rcases h v5 with e | e <;> rw [e] <;> exact h5`.
-/
theorem goodAt_flip {ι J : Type} (χ : J → ((ZMod p)ˣ →* Kˣ)) (s s' : ι → SSParam p K r)
    (h : ∀ v, s' v = s v ∨ s' v = invParam (s v)) (hs : GoodAt χ s) : GoodAt χ s' := by
  obtain ⟨h1, h2, ⟨h3, h3'⟩, h4, v5, h5⟩ := hs
  refine ⟨fun v => ?_, fun l hl hl' v => ?_, ⟨fun l hl hl' v => ?_, fun v => ?_⟩, ?_, v5, ?_⟩
  · rcases h v with e | e <;> rw [e]
    · exact h1 v
    · intro x y hxy
      rw [rootChar_invParam, rootChar_invParam] at hxy
      exact h1 v (inv_injective hxy)
  · rcases h v with e | e <;> rw [e]
    · exact h2 l hl hl' v
    · intro x y hxy
      rw [rootChar_invParam, rootChar_invParam, congrMod_inv]
      exact h2 l hl hl' v x y hxy
  · rcases h v with e | e <;> rw [e]
    · exact h3 l hl hl' v
    · intro j c
      have := h3 l hl hl' v j c
      rw [inv_comp_baseNorm] at this
      rw [cycChar_invParam, inv_comp_baseNorm, congrMod_inv, congrMod_inv_left]
      exact this.symm
  · rcases h v with e | e <;> rw [e]
    · exact h3' v
    · intro j x
      have := h3' v j x
      rw [inv_comp_baseNorm] at this
      rw [rootChar_invParam, inv_comp_baseNorm, Ne, Ne, inv_inj, inv_eq_iff_eq_inv]
      exact this.symm
  · rintro ⟨a, ha, ha', hA⟩
    refine h4 ⟨a, ha, ha', fun v => ?_⟩
    have := hA v
    rcases h v with e | e <;> rw [e] at this <;> exact this
  · rcases h v5 with e | e <;> rw [e] <;> exact h5

/- English proof (translation)
Take `⟨c, rfl⟩` from `isConj_iff.1 h`. Conclude with `isConj_iff.2 ⟨c, by group⟩`.
-/
theorem isConj_inv_inv {G : Type} [Group G] {a b : G} (h : IsConj a b) : IsConj a⁻¹ b⁻¹ := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact isConj_iff.2 ⟨c, by group⟩

end Local

section Global

variable {R : Ranks} {H : Host R} {K : Type} [Field K]

open Classical in

def flipAt (S : Set (Sq H)) (x : LevelGroup H) : LevelGroup H := fun v => if v ∈ S then (x v)⁻¹ else x v

open Classical in

def flipParam (S : Set (Sq H)) (s : ∀ v : Sq H, SSParam (H.g v.1) K R.r) : ∀ v : Sq H, SSParam (H.g v.1) K R.r :=
  fun v => if v ∈ S then invParam (s v) else s v

/- English proof (translation)
Use function extensionality and compare the values at `v`. Apply the tactic sequence `by_cases hv : v ∈ S <;> simp [flipAt, hv]`.
-/
theorem flipAt_flipAt (S : Set (Sq H)) (x : LevelGroup H) : flipAt S (flipAt S x) = x := by
  funext v
  by_cases hv : v ∈ S <;> simp [flipAt, hv]

/- English proof (translation)
Use function extensionality and compare the values at `v`. Apply the tactic sequence `by_cases hv : v ∈ S <;> simp [flipAt, hv]`.
-/
theorem flipAt_one (S : Set (Sq H)) : flipAt S 1 = 1 := by
  funext v
  by_cases hv : v ∈ S <;> simp [flipAt, hv]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ S`. Simplify using `only [flipParam, flipAt, if_pos hv]`. Conclude with `(GlobalTheory.TypeCharacterConjugateInverse.typeChar_conj_inv _ K _ (s v)).2 (x v)`.

Simplify using `only [flipParam, flipAt, if_neg hv]`.
-/
theorem tupleChar_flipParam (S : Set (Sq H)) (s : ∀ v : Sq H, SSParam (H.g v.1) K R.r) :
    tupleChar (flipParam S s) = tupleChar s ∘ flipAt S := by
  funext x
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : v ∈ S
  · simp only [flipParam, flipAt, if_pos hv]
    exact (GlobalTheory.TypeCharacterConjugateInverse.typeChar_conj_inv _ K _ (s v)).2 (x v)
  · simp only [flipParam, flipAt, if_neg hv]

/- English proof (translation)
The claim follows from `Finset.prod_congr rfl fun v _ => (GlobalTheory.TypeCharacterConjugateInverse.typeChar_conj_inv _ K _ (s v)).1 _ _ (h v)`.
-/
theorem tupleChar_congr (s : ∀ v : Sq H, SSParam (H.g v.1) K R.r) {x y : LevelGroup H}
    (h : ∀ v, IsConj (x v) (y v)) : tupleChar s x = tupleChar s y :=
  Finset.prod_congr rfl fun v _ => (GlobalTheory.TypeCharacterConjugateInverse.typeChar_conj_inv _ K _ (s v)).1 _ _ (h v)

/- English proof (translation)
Take `⟨s, hs, rfl⟩` from `hτ`. Use `⟨flipParam S s, fun i => goodAt_flip _ _ _ (fun w => ?_) (hs i), tupleChar_flipParam S s⟩` and prove the remaining obligations. Distinguish the cases in `hv : (⟨i, w⟩ : Sq H) ∈ S`. Conclude with `Or.inr (if_pos hv)`. Conclude with `Or.inl (if_neg hv)`.
-/
theorem comp_flipAt_mem (om : ∀ i : Fin 2, (ZMod (H.g i))ˣ →* Kˣ) (S : Set (Sq H)) {τ : LevelGroup H → K}
    (hτ : τ ∈ goodTypes om) : τ ∘ flipAt S ∈ goodTypes om := by
  obtain ⟨s, hs, rfl⟩ := hτ
  refine ⟨flipParam S s, fun i => goodAt_flip _ _ _ (fun w => ?_) (hs i), tupleChar_flipParam S s⟩
  by_cases hv : (⟨i, w⟩ : Sq H) ∈ S
  · exact Or.inr (if_pos hv)
  · exact Or.inl (if_neg hv)

end Global

/- English proof (translation)
Simplify using `only [goodIdem, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, GlobalTheory.SumWCompare.coeff_centralIdem]`. Establish `inv : ∀ τ : LevelGroup H → ℂ, (τ ∘ flipAt S) ∘ flipAt S = τ` using `fun τ => by`. Use function extensionality and compare the values at `z`. Simplify using `[flipAt_flipAt]`. Use `Finset.sum_nbij' (fun τ => τ ∘ flipAt S) (fun τ => τ ∘ flipAt S) ?_ ?_ (fun τ _ => inv τ) (fun τ _ => inv τ) ?_` and prove the remaining obligations.

Introduce `τ hτ`. Conclude with `(Set.Finite.mem_toFinset _).2 (comp_flipAt_mem om S ((Set.Finite.mem_toFinset _).1 hτ))`. Introduce `τ hτ`. Conclude with `(Set.Finite.mem_toFinset _).2 (comp_flipAt_mem om S ((Set.Finite.mem_toFinset _).1 hτ))`. Introduce `τ hτ`.

Take `⟨s, -, rfl⟩` from `(Set.Finite.mem_toFinset _).1 hτ`. Establish `key : tupleChar s y⁻¹ = tupleChar s (flipAt S x⁻¹)`. Use `tupleChar_congr s fun v => ?_` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ S`. Simplify using `only [flipAt, if_pos hv, Pi.inv_apply]`.

Conclude with `isConj_inv_inv (h1 v hv).symm`. Simplify using `only [flipAt, if_neg hv, Pi.inv_apply]`. Conclude with `isConj_inv_inv (h2 v hv).symm`. Rewrite using `[Function.comp_apply, Function.comp_apply, flipAt_one, key]`.
-/
theorem coeff_goodIdem_flip (R : Ranks) (H : Host R) (om : ∀ i : Fin 2, (ZMod (H.g i))ˣ →* ℂˣ) (S : Set (Sq H))
    (x y : LevelGroup H) (h1 : ∀ v ∈ S, IsConj (x v)⁻¹ (y v)) (h2 : ∀ v ∉ S, IsConj (x v) (y v)) :
    (goodIdem om).coeff y = (goodIdem om).coeff x := by
  simp only [goodIdem, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, GlobalTheory.SumWCompare.coeff_centralIdem]
  have inv : ∀ τ : LevelGroup H → ℂ, (τ ∘ flipAt S) ∘ flipAt S = τ := fun τ => by
    funext z; simp [flipAt_flipAt]
  refine Finset.sum_nbij' (fun τ => τ ∘ flipAt S) (fun τ => τ ∘ flipAt S) ?_ ?_ (fun τ _ => inv τ) (fun τ _ => inv τ) ?_
  · intro τ hτ
    exact (Set.Finite.mem_toFinset _).2 (comp_flipAt_mem om S ((Set.Finite.mem_toFinset _).1 hτ))
  · intro τ hτ
    exact (Set.Finite.mem_toFinset _).2 (comp_flipAt_mem om S ((Set.Finite.mem_toFinset _).1 hτ))
  · intro τ hτ
    obtain ⟨s, -, rfl⟩ := (Set.Finite.mem_toFinset _).1 hτ
    have key : tupleChar s y⁻¹ = tupleChar s (flipAt S x⁻¹) := by
      refine tupleChar_congr s fun v => ?_
      by_cases hv : v ∈ S
      · simp only [flipAt, if_pos hv, Pi.inv_apply]
        exact isConj_inv_inv (h1 v hv).symm
      · simp only [flipAt, if_neg hv, Pi.inv_apply]
        exact isConj_inv_inv (h2 v hv).symm
    rw [Function.comp_apply, Function.comp_apply, flipAt_one, key]

end GlobalTheory.GoodIdemFlip
