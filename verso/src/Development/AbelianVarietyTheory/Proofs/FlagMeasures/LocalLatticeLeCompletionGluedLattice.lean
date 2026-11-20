import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemSpanSingleIff
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Glue

/- English proof (translation)
Introduce `p v hv`. Establish `hsingle : ∀ i : Fin n, ((N : E) • (Pi.single i 1 : Fin n → E)) ∈ Γ`. Introduce `i`. Rewrite using `[hΓ]`. Introduce `q`.

Establish `h1 : A.bc q ((N : E) • (Pi.single i 1 : Fin n → E)) = (N : (A.loc q).Ep) • (Pi.single i 1 : Fin n → (A.loc q).Ep)`. Use function extensionality and compare the values at `j`. Simplify using `only [Places.bc, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`. Rewrite using `[h1]`. Apply `hN` to reduce the goal to its premises. Introduce `j`.

Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[Subring.one_mem]`. Simplify using `[Pi.single_apply, h, Subring.zero_mem]`. Establish `hint : ∀ w : Fin n → (A.loc p).Ep, (∀ i, w i ∈ (A.L p).O) → (N : (A.loc p).Ep) • w ∈ A.lat p Γ`.

Introduce `w hw`. Establish `hw' : (N : (A.loc p).Ep) • w = ∑ i, (⟨w i, hw i⟩ : (A.L p).O) • A.bc p ((N : E) • (Pi.single i 1 : Fin n → E))`. Use function extensionality and compare the values at `j`. Simplify using `[Places.bc, Subring.smul_def, Pi.single_apply, Finset.sum_apply, mul_comm]`. Simplify using `[apply_ite (A.loc p).ιE, mul_ite, Finset.sum_ite_eq, mul_comm]`.

Rewrite using `[hw']`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hsingle i, rfl⟩)`. Establish `hfin : ∀ i, {q | (Pi.single p (v i) : ∀ q, (A.loc q).Ep) q ∉ (A.L q).O}.Finite`. Introduce `i`. Apply `(Set.finite_singleton p).subset` to reduce the goal to its premises.

Introduce `q hq`. Assume the negation of the conclusion as `h`. Apply `hq` to reduce the goal to its premises. Rewrite using `[Pi.single_eq_of_ne h]`. Conclude with `(A.L q).O.zero_mem`.

Use `choose x hx using fun i => happ _ (hfin i)`. Use `choose o ho hxo using hx`. Establish `hbc : ∀ q, A.bc q (fun i => x i) = (fun i => (Pi.single p (v i) : ∀ q, (A.loc q).Ep) q) + (N : (A.loc q).Ep) • (fun i => o i q)`. Introduce `q`. Use function extensionality and compare the values at `i`.

Establish `h2` using `hxo i q`. Simplify using `only [Places.bc, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hX : (fun i => x i) ∈ Γ`.

Rewrite using `[hΓ]`. Introduce `q`. Rewrite using `[hbc q]`. Use `(Λ q).add_mem ?_ (hN q _ fun i => ho i q)` and prove the remaining obligations. Distinguish the cases in `hq : q = p`.

Substitute `hq` using the available equality. Simplify using `using hv`. Establish `h3 : (fun i => (Pi.single p (v i) : ∀ q, (A.loc q).Ep) q) = 0`. Use function extensionality and compare the values at `i`. Simplify using `[Pi.single_eq_of_ne hq]`.

Rewrite using `[h3]`. Conclude with `(Λ q).zero_mem`. Establish `hv' : v = A.bc p (fun i => x i) - (N : (A.loc p).Ep) • (fun i => o i p)`. Rewrite using `[hbc p]`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Rewrite using `[hv']`. Conclude with `Submodule.sub_mem _ (Submodule.subset_span ⟨_, hX, rfl⟩) (hint _ fun i => ho i p)`.
-/
theorem local_le_lat_of_approx {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) (n : ℕ) (Λ : ∀ p, Submodule (A.L p).O (Fin n → (A.loc p).Ep))
    (Γ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ)
    (hΓ : ∀ x, x ∈ Γ ↔ ∀ p, A.bc p x ∈ Λ p)
    (hN : ∀ p (v : Fin n → (A.loc p).Ep), (∀ i, v i ∈ (A.L p).O) → (N : (A.loc p).Ep) • v ∈ Λ p)
    (happ : ∀ y : ∀ p, (A.loc p).Ep, {p | y p ∉ (A.L p).O}.Finite →
      ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O, (A.loc p).ιE x - y p = (N : (A.loc p).Ep) * o) :
    ∀ p, Λ p ≤ A.lat p Γ := by
  intro p v hv
  have hsingle : ∀ i : Fin n, ((N : E) • (Pi.single i 1 : Fin n → E)) ∈ Γ := by
    intro i
    rw [hΓ]
    intro q
    have h1 : A.bc q ((N : E) • (Pi.single i 1 : Fin n → E)) =
        (N : (A.loc q).Ep) • (Pi.single i 1 : Fin n → (A.loc q).Ep) := by
      funext j
      simp only [Places.bc, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]
      by_cases h : j = i
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [h1]
    apply hN
    intro j
    by_cases h : j = i
    · subst h; simp [Subring.one_mem]
    · simp [Pi.single_apply, h, Subring.zero_mem]
  have hint : ∀ w : Fin n → (A.loc p).Ep, (∀ i, w i ∈ (A.L p).O) →
      (N : (A.loc p).Ep) • w ∈ A.lat p Γ := by
    intro w hw
    have hw' : (N : (A.loc p).Ep) • w =
        ∑ i, (⟨w i, hw i⟩ : (A.L p).O) • A.bc p ((N : E) • (Pi.single i 1 : Fin n → E)) := by
      funext j
      simp [Places.bc, Subring.smul_def, Pi.single_apply, Finset.sum_apply, mul_comm]
      simp [apply_ite (A.loc p).ιE, mul_ite, Finset.sum_ite_eq, mul_comm]
    rw [hw']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hsingle i, rfl⟩)
  have hfin : ∀ i, {q | (Pi.single p (v i) : ∀ q, (A.loc q).Ep) q ∉ (A.L q).O}.Finite := by
    intro i
    apply (Set.finite_singleton p).subset
    intro q hq
    by_contra h
    apply hq
    rw [Pi.single_eq_of_ne h]
    exact (A.L q).O.zero_mem
  choose x hx using fun i => happ _ (hfin i)
  choose o ho hxo using hx
  have hbc : ∀ q, A.bc q (fun i => x i) =
      (fun i => (Pi.single p (v i) : ∀ q, (A.loc q).Ep) q) + (N : (A.loc q).Ep) • (fun i => o i q) := by
    intro q
    funext i
    have h2 := hxo i q
    simp only [Places.bc, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← h2]
    ring
  have hX : (fun i => x i) ∈ Γ := by
    rw [hΓ]
    intro q
    rw [hbc q]
    refine (Λ q).add_mem ?_ (hN q _ fun i => ho i q)
    by_cases hq : q = p
    · subst hq
      simpa using hv
    · have h3 : (fun i => (Pi.single p (v i) : ∀ q, (A.loc q).Ep) q) = 0 := by
        funext i
        simp [Pi.single_eq_of_ne hq]
      rw [h3]
      exact (Λ q).zero_mem
  have hv' : v = A.bc p (fun i => x i) - (N : (A.loc p).Ep) • (fun i => o i p) := by
    rw [hbc p]
    funext i
    simp
  rw [hv']
  exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, hX, rfl⟩) (hint _ fun i => ho i p)

end GlobalTheory.HL.Glue
