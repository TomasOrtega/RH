import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsCharOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFieldCharacterLabelsCompatNormPowInvStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelledCharactersEqAndCongrPrimeToPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOrbitRootPolynomialFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeDivisorsProdDistinctMonicIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenCuspidalCharIsCuspidalOfMinpolyOfParamStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInducedTypeCharEqProductListStatement

noncomputable section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters

namespace GlobalTheory.ParamLabel

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Use extensionality with `l`. Simplify using `only [BB, Formalism.CyclotomicNorms.BB, Formalism.CyclotomicNorms.Exc, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, ← pow_mul, mul_comm 4]`. Use `or_congr_right ⟨fun ⟨h, a, h1, h2, h3⟩ => ⟨a, h1, h2, h, h3⟩, fun ⟨a, h1, h2, h, h3⟩ => ⟨h, a, h1, h2, h3⟩⟩` and prove the remaining obligations.
-/
theorem bb_eq (p r : ℕ) : BB p r = Formalism.CyclotomicNorms.BB r p := by
  ext l
  simp only [BB, Formalism.CyclotomicNorms.BB, Formalism.CyclotomicNorms.Exc, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, ← pow_mul, mul_comm 4]
  refine or_congr_right ⟨fun ⟨h, a, h1, h2, h3⟩ => ⟨a, h1, h2, h, h3⟩, fun ⟨a, h1, h2, h, h3⟩ => ⟨h, a, h1, h2, h3⟩⟩

/- English proof (translation)
Set `β : Fbar p ≃* Fbar p` to `(iterateFrobeniusEquiv (Fbar p) p i).toMulEquiv`. Establish `h1 : z ^ p ^ i = β z` using `rfl`. Establish `h2 : β (algebraMap (ZMod p) (Fbar p) a) = algebraMap (ZMod p) (Fbar p) a` using `by show algebraMap (ZMod p) (Fbar p) a ^ p ^ i = _`. Rewrite using `[← map_pow, ZMod.pow_card_pow]`. Use `conv_lhs => rw [h1, ← h2, GlobalTheory.GoodCharsCompare.primeToPart_map, GlobalTheory.GoodCharsCompare.primeToPart_map]`.

Conclude with `β.injective.eq_iff`.
-/
theorem primeToPart_frob (l i : ℕ) (z : Fbar p) (a : ZMod p) :
    Formalism.CyclotomicNorms.primeToPart l (z ^ p ^ i) = Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) a) ↔
      Formalism.CyclotomicNorms.primeToPart l z = Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) a) := by
  let β : Fbar p ≃* Fbar p := (iterateFrobeniusEquiv (Fbar p) p i).toMulEquiv
  have h1 : z ^ p ^ i = β z := rfl
  have h2 : β (algebraMap (ZMod p) (Fbar p) a) = algebraMap (ZMod p) (Fbar p) a := by
    show algebraMap (ZMod p) (Fbar p) a ^ p ^ i = _
    rw [← map_pow, ZMod.pow_card_pow]
  conv_lhs => rw [h1, ← h2, GlobalTheory.GoodCharsCompare.primeToPart_map, GlobalTheory.GoodCharsCompare.primeToPart_map]
  exact β.injective.eq_iff

section Good

variable {L : GlobalTheory.GLq.LabelDatum p} {r : ℕ} {s : SSParam p ℂ r} {x : Cyc s.1 → Fbar p} {f : (ZMod p)[X]}

/- English proof (translation)
The claim follows from `(GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv p L _ r.factorial_pos).1 _ (cycLen_dvd s.1 y.1) _ _ _ (h.1 y.1)`.
-/
theorem Labels.root (h : Labels L s x f) (y) : LabelsChar L (rootChar s y) (rootElt x y) :=
  (GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv p L _ r.factorial_pos).1 _ (cycLen_dvd s.1 y.1) _ _ _ (h.1 y.1)

/- English proof (translation)
Use `(GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv p L _ r.factorial_pos).1 _ (cycLen_dvd s.1 c) _ _ 1 (h.1 c)` as an intermediate fact. Rewrite `this` using `[pow_one, pow_one]`. Then use the resulting hypothesis.
-/
theorem Labels.cyc (h : Labels L s x f) (c) : LabelsChar L (cycChar s c) (x c) := by
  have := (GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv p L _ r.factorial_pos).1 _ (cycLen_dvd s.1 c) _ _ 1 (h.1 c)
  rwa [pow_one, pow_one] at this

/- English proof (translation)
Rewrite using `[h.2.2.2]`. Simplify using the standard rewrite rules.
-/
theorem Labels.mem_roots (h : Labels L s x f) (z : Fbar p) : z ∈ Formalism.CyclotomicNorms.rootsBar f ↔ ∃ y, rootElt x y = z := by
  rw [h.2.2.2]; simp

/- English proof (translation)
Rewrite using `[(GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization p r _ x f h.2).2.2.1]`. Conclude with `forall₂_congr fun y y' => by`. Rewrite using `[(GlobalTheory.T.labelled_characters_eq_and_congr_primeToPart p L _ r.factorial_pos _ _ _ _ (h.root y) (h.root y')).1]`.
-/
theorem Labels.regular_iff (h : Labels L s x f) : IsRegularParam s ↔ Squarefree f := by
  rw [(GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization p r _ x f h.2).2.2.1]
  exact forall₂_congr fun y y' => by
    rw [(GlobalTheory.T.labelled_characters_eq_and_congr_primeToPart p L _ r.factorial_pos _ _ _ _ (h.root y) (h.root y')).1]

/- English proof (translation)
Establish `hi` using `(GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization p r _ x f h.2).2.2.1.1 hs`. Simplify using `only [h.mem_roots, forall_exists_index, forall_apply_eq_imp_iff, hi.eq_iff]`. Conclude with `forall₂_congr fun y y' => by`. Rewrite using `[(GlobalTheory.T.labelled_characters_eq_and_congr_primeToPart p L _ r.factorial_pos _ _ _ _ (h.root y) (h.root y')).2 l hl, not_imp_not]`.
-/
theorem Labels.two_iff (h : Labels L s x f) (hs : Squarefree f) {l : ℕ} (hl : l.Prime) :
    (∀ y y', y ≠ y' → ¬ CongrMod l (rootChar s y) (rootChar s y')) ↔
      ∀ z ∈ Formalism.CyclotomicNorms.rootsBar f, ∀ z' ∈ Formalism.CyclotomicNorms.rootsBar f, Formalism.CyclotomicNorms.primeToPart l z = Formalism.CyclotomicNorms.primeToPart l z' → z = z' := by
  have hi := (GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization p r _ x f h.2).2.2.1.1 hs
  simp only [h.mem_roots, forall_exists_index, forall_apply_eq_imp_iff, hi.eq_iff]
  exact forall₂_congr fun y y' => by
    rw [(GlobalTheory.T.labelled_characters_eq_and_congr_primeToPart p L _ r.factorial_pos _ _ _ _ (h.root y) (h.root y')).2 l hl, not_imp_not]

/- English proof (translation)
Establish `hχ` using `((GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv p L _ r.factorial_pos).2 χ a ha).1`. Simplify using `only [h.mem_roots, forall_exists_index, forall_apply_eq_imp_iff, rootElt, Ne, primeToPart_frob, (GlobalTheory.T.labelled_characters_eq_and_congr_primeToPart p L _ r.factorial_pos _ _ _ _ (h.cyc _) hχ).2 l hl]`. Conclude with `⟨fun H y => H y.1, fun H c => H ⟨c, ⟨0, cycLen_pos _ c⟩⟩⟩`.
-/
theorem Labels.three_iff (h : Labels L s x f) {χ : (ZMod p)ˣ →* ℂˣ} {a : (ZMod p)ˣ} (ha : LabelsTame L χ a)
    {l : ℕ} (hl : l.Prime) :
    (∀ c, ¬ CongrMod l (cycChar s c) (χ.comp (baseNorm p r.factorial))) ↔
      ∀ z ∈ Formalism.CyclotomicNorms.rootsBar f, Formalism.CyclotomicNorms.primeToPart l z ≠
        Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) (a : ZMod p)) := by
  have hχ := ((GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv p L _ r.factorial_pos).2 χ a ha).1
  simp only [h.mem_roots, forall_exists_index, forall_apply_eq_imp_iff, rootElt, Ne, primeToPart_frob,
    (GlobalTheory.T.labelled_characters_eq_and_congr_primeToPart p L _ r.factorial_pos _ _ _ _ (h.cyc _) hχ).2 l hl]
  exact ⟨fun H y => H y.1, fun H c => H ⟨c, ⟨0, cycLen_pos _ c⟩⟩⟩

/- English proof (translation)
Introduce `e` and use `by have hχ := ((GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv p L _ r.factorial_pos).2 χ a ha).1 have := (GlobalTheory.T.labelled_characters_eq_and_congr_primeToPart p L _ r.factorial_pos _ _ _ _ (h.root y) hχ).1.1 e exact H _ ((h.mem_roots _).2 ⟨y, rfl⟩) (by rw …`.
-/
theorem Labels.ne_of (h : Labels L s x f) {χ : (ZMod p)ˣ →* ℂˣ} {a : (ZMod p)ˣ} (ha : LabelsTame L χ a) {l : ℕ}
    (H : ∀ z ∈ Formalism.CyclotomicNorms.rootsBar f, Formalism.CyclotomicNorms.primeToPart l z ≠
        Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) (a : ZMod p))) (y) :
    rootChar s y ≠ χ.comp (baseNorm p r.factorial) := fun e => by
  have hχ := ((GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv p L _ r.factorial_pos).2 χ a ha).1
  have := (GlobalTheory.T.labelled_characters_eq_and_congr_primeToPart p L _ r.factorial_pos _ _ _ _ (h.root y) hχ).1.1 e
  exact H _ ((h.mem_roots _).2 ⟨y, rfl⟩) (by rw [this])

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `(GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization p r _ x f h.2).2.2.2 hs`. Use `GlobalTheory.T.natDegree_divisors_prod_distinct_monic_irreducible (ZMod p) _ _ (fun c => ⟨minpoly.monic (Algebra.IsIntegral.isIntegral (x c)), minpoly.irreducible (Algebra.IsIntegral.isIntegral (x c))⟩) h2` as an intermediate fact. Simplify using `only [h1, ← h3] at this`. Conclude with `this`.
-/
theorem Labels.dvd_iff (h : Labels L s x f) (hs : Squarefree f) :
    (∀ a : ℕ, (∃ q : (ZMod p)[X], q ∣ f ∧ q.natDegree = a) ↔ ∃ A : Finset (Cyc s.1), ∑ c ∈ A, cycLen s.1 c = a) ∧
    ∀ Q : ℕ → Prop, (∃ q : (ZMod p)[X], Irreducible q ∧ q ∣ f ∧ Q q.natDegree) ↔ ∃ c, Q (cycLen s.1 c) := by
  obtain ⟨h1, h2, h3⟩ := (GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization p r _ x f h.2).2.2.2 hs
  have := GlobalTheory.T.natDegree_divisors_prod_distinct_monic_irreducible (ZMod p) _ _ (fun c => ⟨minpoly.monic (Algebra.IsIntegral.isIntegral (x c)),
    minpoly.irreducible (Algebra.IsIntegral.isIntegral (x c))⟩) h2
  simp only [h1, ← h3] at this
  exact this

end Good

/- English proof (translation)
Establish `inv : ∀ {χ : (ZMod p)ˣ →* ℂˣ} {a}, LabelsTame L χ a → LabelsTame L χ⁻¹ a⁻¹` using `fun h => ((GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv p L 1 one_pos).2 _ _ h).2`. Establish `three : ∀ l : ℕ, l.Prime → ∀ v j, ((∀ c, ¬ CongrMod l (cycChar (s v) c) ((χ j).comp (baseNorm p r.factorial))) ∧ ∀ c, ¬ CongrMod l (cycChar (s v) c) ((χ j)⁻¹.comp (baseNorm p r.factorial))) ↔ (∀ z ∈ Formalism.CyclotomicNorms.rootsBar (f v), Formalism.CyclotomicNorms.primeToPart l …`. Introduce `l hl v j`. Break down `ha v j with H | H` into its components or cases. Rewrite using `[(h v).three_iff H hl, (h v).three_iff (inv H) hl]`.

Establish `H'` using `inv H`. Rewrite `H'` using `[inv_inv]`. Rewrite using `[(h v).three_iff H hl, (h v).three_iff H' hl, and_comm]`. Establish `base` using `fun v => GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization p r _ (x v) (f v) (h v).2`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨g1, g2, ⟨g3, -⟩, g4, g5⟩`. Establish `hs` using `fun v => (h v).regular_iff.1 (g1 v)`. Establish `k3` using `fun l hl hp v j => (three l hl v j).1 ⟨fun c => (g3 l hl hp v j c).1, fun c => (g3 l hl hp v j c).2⟩`. Establish `key : ∀ a' : ι → J → (ZMod p)ˣ, (∀ l : ℕ, l.Prime → l ≠ p → ∀ v j, ∀ z ∈ Formalism.CyclotomicNorms.rootsBar (f v), Formalism.CyclotomicNorms.primeToPart l z ≠ Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) (a' v j : ZMod p))) → Formalism.CyclotomicNorms.IsG …` using `fun a' H => by`. Use `⟨fun v => ⟨(h v).2.2.1, (base v).1, (base v).2.1⟩, hs, fun l hl hb v => ((h v).two_iff (hs v) hl).1 (g2 l hl (bb_eq p r ▸ hb) v), H, fun n h1 h2 => ?_, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hc push Not at hc`. Conclude with `g4 ⟨n, h1, h2, fun v => (((h v).dvd_iff (hs v)).1 n).1 (hc v)⟩`. Take `⟨v, hv⟩` from `g5`. Conclude with `⟨v, (((h v).dvd_iff (hs v)).2 fun d => d.Prime ∧ r < 2 * d ∧ d + 3 ≤ r).2 hv⟩`. Conclude with `⟨key _ fun l hl hp v j => (k3 l hl hp v j).1, key _ fun l hl hp v j => (k3 l hl hp v j).2⟩`.

Introduce and unpack `⟨⟨-, hs, g2, g3, g4, v₀, g5⟩, -, -, -, g3', -⟩`. Establish `k3` using `fun l hl hp v j => (three l hl v j).2 ⟨g3 l hl hp v j, g3' l hl hp v j⟩`. Use `⟨fun v => (h v).regular_iff.2 (hs v), fun l hl hb v => ((h v).two_iff (hs v) hl).2 (g2 l hl (bb_eq p r ▸ hb) v), ⟨fun l hl hp v j c => ⟨(k3 l hl hp v j).1 c, (k3 l hl hp v j).2 c⟩, fun v j y => ?_⟩, ?_, v₀, (((h v₀).dvd_iff (hs v₀)).2 fun d => d.Prime ∧ r < 2 * d ∧ d + 3 ≤ r).1 g …` and prove the remaining obligations. Establish `e1` using `g3 2 Nat.prime_two (by omega) v j`. Establish `e2` using `g3' 2 Nat.prime_two (by omega) v j`.

Break down `ha v j with H | H` into its components or cases. Conclude with `⟨(h v).ne_of H e1 y, (h v).ne_of (inv H) e2 y⟩`. Establish `H'` using `inv H`. Rewrite `H'` using `[inv_inv]`. Conclude with `⟨(h v).ne_of H' e2 y, (h v).ne_of H e1 y⟩`.

Introduce and unpack `⟨n, h1, h2, H⟩`. Take `⟨v, hv⟩` from `g4 n h1 h2`. Conclude with `hv ((((h v).dvd_iff (hs v)).1 n).2 (H v))`.
-/
theorem good_iff (L : GlobalTheory.GLq.LabelDatum p) (h5 : 5 ≤ p) {r : ℕ} {ι J : Type} (s : ι → SSParam p ℂ r)
    (x : ∀ v, Cyc (s v).1 → Fbar p) (f : ι → (ZMod p)[X]) (h : ∀ v, Labels L (s v) (x v) (f v))
    (χ : J → (ZMod p)ˣ →* ℂˣ) (a : ι → J → (ZMod p)ˣ)
    (ha : ∀ v j, LabelsTame L (χ j) (a v j) ∨ LabelsTame L (χ j)⁻¹ (a v j)) :
    GoodAt χ s ↔ Formalism.CyclotomicNorms.IsGood r p f a ∧ Formalism.CyclotomicNorms.IsGood r p f fun v j => (a v j)⁻¹ := by
  have inv : ∀ {χ : (ZMod p)ˣ →* ℂˣ} {a}, LabelsTame L χ a → LabelsTame L χ⁻¹ a⁻¹ := fun h =>
    ((GlobalTheory.T.finiteField_character_labels_compat_norm_pow_inv p L 1 one_pos).2 _ _ h).2
  have three : ∀ l : ℕ, l.Prime → ∀ v j,
      ((∀ c, ¬ CongrMod l (cycChar (s v) c) ((χ j).comp (baseNorm p r.factorial))) ∧
        ∀ c, ¬ CongrMod l (cycChar (s v) c) ((χ j)⁻¹.comp (baseNorm p r.factorial))) ↔
      (∀ z ∈ Formalism.CyclotomicNorms.rootsBar (f v), Formalism.CyclotomicNorms.primeToPart l z ≠
        Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) (a v j : ZMod p))) ∧
      ∀ z ∈ Formalism.CyclotomicNorms.rootsBar (f v), Formalism.CyclotomicNorms.primeToPart l z ≠
        Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) ((a v j)⁻¹ : (ZMod p)ˣ)) := by
    intro l hl v j
    rcases ha v j with H | H
    · rw [(h v).three_iff H hl, (h v).three_iff (inv H) hl]
    · have H' := inv H
      rw [inv_inv] at H'
      rw [(h v).three_iff H hl, (h v).three_iff H' hl, and_comm]
  have base := fun v => GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization p r _ (x v) (f v) (h v).2
  constructor
  · rintro ⟨g1, g2, ⟨g3, -⟩, g4, g5⟩
    have hs := fun v => (h v).regular_iff.1 (g1 v)
    have k3 := fun l hl hp v j => (three l hl v j).1 ⟨fun c => (g3 l hl hp v j c).1, fun c => (g3 l hl hp v j c).2⟩
    have key : ∀ a' : ι → J → (ZMod p)ˣ, (∀ l : ℕ, l.Prime → l ≠ p → ∀ v j, ∀ z ∈ Formalism.CyclotomicNorms.rootsBar (f v),
        Formalism.CyclotomicNorms.primeToPart l z ≠ Formalism.CyclotomicNorms.primeToPart l (algebraMap (ZMod p) (Fbar p) (a' v j : ZMod p))) →
        Formalism.CyclotomicNorms.IsGood r p f a' := fun a' H => by
      refine ⟨fun v => ⟨(h v).2.2.1, (base v).1, (base v).2.1⟩, hs,
        fun l hl hb v => ((h v).two_iff (hs v) hl).1 (g2 l hl (bb_eq p r ▸ hb) v), H, fun n h1 h2 => ?_, ?_⟩
      · by_contra hc
        push Not at hc
        exact g4 ⟨n, h1, h2, fun v => (((h v).dvd_iff (hs v)).1 n).1 (hc v)⟩
      · obtain ⟨v, hv⟩ := g5
        exact ⟨v, (((h v).dvd_iff (hs v)).2 fun d => d.Prime ∧ r < 2 * d ∧ d + 3 ≤ r).2 hv⟩
    exact ⟨key _ fun l hl hp v j => (k3 l hl hp v j).1, key _ fun l hl hp v j => (k3 l hl hp v j).2⟩
  · rintro ⟨⟨-, hs, g2, g3, g4, v₀, g5⟩, -, -, -, g3', -⟩
    have k3 := fun l hl hp v j => (three l hl v j).2 ⟨g3 l hl hp v j, g3' l hl hp v j⟩
    refine ⟨fun v => (h v).regular_iff.2 (hs v), fun l hl hb v => ((h v).two_iff (hs v) hl).2 (g2 l hl (bb_eq p r ▸ hb) v),
      ⟨fun l hl hp v j c => ⟨(k3 l hl hp v j).1 c, (k3 l hl hp v j).2 c⟩, fun v j y => ?_⟩, ?_,
      v₀, (((h v₀).dvd_iff (hs v₀)).2 fun d => d.Prime ∧ r < 2 * d ∧ d + 3 ≤ r).1 g5⟩
    · have e1 := g3 2 Nat.prime_two (by omega) v j
      have e2 := g3' 2 Nat.prime_two (by omega) v j
      rcases ha v j with H | H
      · exact ⟨(h v).ne_of H e1 y, (h v).ne_of (inv H) e2 y⟩
      · have H' := inv H
        rw [inv_inv] at H'
        exact ⟨(h v).ne_of H' e2 y, (h v).ne_of H e1 y⟩
    · rintro ⟨n, h1, h2, H⟩
      obtain ⟨v, hv⟩ := g4 n h1 h2
      exact hv ((((h v).dvd_iff (hs v)).1 n).2 (H v))

/- English proof (translation)
Take `⟨d1, d2, -, d3⟩` from `GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization p r _ x f h.2`. Take `⟨h1, h2, h3⟩` from `d3 hs`. Take `⟨l, hl, hl', e⟩` from `GlobalTheory.T.harishChandraInducedTypeChar_eq_productList p r s`. Set `Q : List ((ZMod p)[X] × GlobalTheory.GLq.Pc p)` to `l.map fun c => (minpoly (ZMod p) (x c), ⟨cycLen s.1 c, cuspOn (s.2 c)⟩)`. Establish `hsnd : Q.map Prod.snd = l.map fun c => (⟨cycLen s.1 c, cuspOn (s.2 c)⟩ : GlobalTheory.GLq.Pc p)`.

Rewrite using `[List.map_map]`. Both sides reduce to the same expression. Establish `hfst : Q.map Prod.fst = l.map fun c => minpoly (ZMod p) (x c)`. Rewrite using `[List.map_map]`. Both sides reduce to the same expression.

Establish `hQ : ∀ q ∈ Q, GlobalTheory.GLq.IsCuspOf L q.1 q.2.2`. Introduce `q hq`. Take `⟨c, -, rfl⟩` from `List.mem_map.1 hq`. Conclude with `GlobalTheory.T.greenCuspidalChar_isCuspidalOfMinpoly_of_param hG p L h5 _ (s.2 c) (x c) (cycLen_pos _ c) (h.1 c) (h1 c)`. Establish `hprod : f = (Q.map Prod.fst).prod` using `by classical`.

Rewrite using `[hfst, h3, ← List.prod_toFinset _ hl]`. Use `congr 1`. Conclude with `(Finset.eq_univ_of_forall fun c => List.mem_toFinset.2 (hl' c)).symm`. Establish `hdeg : GlobalTheory.GLq.degL (Q.map Prod.snd) = r`. Rewrite using `[← (GlobalTheory.GLq.Label.prod_props L Q hQ).2.1, ← hprod, d1]`.

Establish `hnd : (Q.map Prod.snd).Nodup`. Apply `List.Nodup.of_map (GlobalTheory.GLq.Label.lab L)` to reduce the goal to its premises. Rewrite using `[← GlobalTheory.GLq.Label.map_fst_eq L h5 Q hQ, hfst]`. Conclude with `hl.map h2`. Rewrite `e` using `[← hsnd]`.

Establish `hip` using `(GlobalTheory.T.characterPairing_harishChandra_cuspidal_mackey p _ _ r hdeg hdeg (GlobalTheory.GLq.Label.cusp_snd L Q hQ) (GlobalTheory.GLq.Label.cusp_snd L Q hQ)).2 hnd`. Establish `hirr : GlobalTheory.GLq.IsIrr (typeChar s)` using `e ▸ (GlobalTheory.T.character_decomposition_and_classFunction_expansion _ _).2.2.2.1 (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant p _ [] r hdeg.symm (GlobalTheory.GLq.Label.char_snd L Q hQ)).1 hip`. Establish `hlab : GlobalTheory.GLq.HasLabel L (typeChar s) f` using `⟨Q, hQ, hdeg, hprod, by rw [e, hip]; exact one_ne_zero⟩`. Take `⟨Q', -, -, -, hset⟩` from `GlobalTheory.GLq.Label.squarefree_series L h5 hG r f h.2.2.1 d1 d2 hs`. Establish `: typeChar s = GlobalTheory.GLq.hcL (Q'.map Prod.snd) r`.

Rewrite using `[← Set.mem_singleton_iff, ← hset]`. Conclude with `⟨hirr, hlab⟩`. Use `⟨this ▸ hset, ?_⟩` and prove the remaining obligations. Unfold `GlobalTheory.GLq.eSerC`. Rewrite using `[hset, finsum_mem_singleton, ← this]`.

Unfold `GlobalTheory.GLq.zOf centralIdem`. Rewrite using `[Nat.card_eq_fintype_card]`. Use `rfl` and compare the differences between its conclusion and the goal.
-/
theorem Labels.series (hG : GlobalTheory.GLq.Green) {L : GlobalTheory.GLq.LabelDatum p} (h5 : 5 ≤ p) {r : ℕ} {s : SSParam p ℂ r}
    {x : Cyc s.1 → Fbar p} {f : (ZMod p)[X]} (h : Labels L s x f) (hs : Squarefree f) :
    {χ | GlobalTheory.GLq.IsIrr χ ∧ GlobalTheory.GLq.HasLabel L χ f} = {typeChar s} ∧
      GlobalTheory.GLq.eSerC L r f = centralIdem (typeChar s) := by
  obtain ⟨d1, d2, -, d3⟩ := GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization p r _ x f h.2
  obtain ⟨h1, h2, h3⟩ := d3 hs
  obtain ⟨l, hl, hl', e⟩ := GlobalTheory.T.harishChandraInducedTypeChar_eq_productList p r s
  let Q : List ((ZMod p)[X] × GlobalTheory.GLq.Pc p) := l.map fun c => (minpoly (ZMod p) (x c), ⟨cycLen s.1 c, cuspOn (s.2 c)⟩)
  have hsnd : Q.map Prod.snd = l.map fun c => (⟨cycLen s.1 c, cuspOn (s.2 c)⟩ : GlobalTheory.GLq.Pc p) := by
    rw [List.map_map]; rfl
  have hfst : Q.map Prod.fst = l.map fun c => minpoly (ZMod p) (x c) := by
    rw [List.map_map]; rfl
  have hQ : ∀ q ∈ Q, GlobalTheory.GLq.IsCuspOf L q.1 q.2.2 := by
    intro q hq
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hq
    exact GlobalTheory.T.greenCuspidalChar_isCuspidalOfMinpoly_of_param hG p L h5 _ (s.2 c) (x c) (cycLen_pos _ c) (h.1 c) (h1 c)
  have hprod : f = (Q.map Prod.fst).prod := by
    classical
    rw [hfst, h3, ← List.prod_toFinset _ hl]
    congr 1
    exact (Finset.eq_univ_of_forall fun c => List.mem_toFinset.2 (hl' c)).symm
  have hdeg : GlobalTheory.GLq.degL (Q.map Prod.snd) = r := by
    rw [← (GlobalTheory.GLq.Label.prod_props L Q hQ).2.1, ← hprod, d1]
  have hnd : (Q.map Prod.snd).Nodup := by
    apply List.Nodup.of_map (GlobalTheory.GLq.Label.lab L)
    rw [← GlobalTheory.GLq.Label.map_fst_eq L h5 Q hQ, hfst]
    exact hl.map h2
  rw [← hsnd] at e
  have hip := (GlobalTheory.T.characterPairing_harishChandra_cuspidal_mackey p _ _ r hdeg hdeg (GlobalTheory.GLq.Label.cusp_snd L Q hQ) (GlobalTheory.GLq.Label.cusp_snd L Q hQ)).2 hnd
  have hirr : GlobalTheory.GLq.IsIrr (typeChar s) :=
    e ▸ (GlobalTheory.T.character_decomposition_and_classFunction_expansion _ _).2.2.2.1 (GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant p _ [] r hdeg.symm (GlobalTheory.GLq.Label.char_snd L Q hQ)).1 hip
  have hlab : GlobalTheory.GLq.HasLabel L (typeChar s) f := ⟨Q, hQ, hdeg, hprod, by rw [e, hip]; exact one_ne_zero⟩
  obtain ⟨Q', -, -, -, hset⟩ := GlobalTheory.GLq.Label.squarefree_series L h5 hG r f h.2.2.1 d1 d2 hs
  have : typeChar s = GlobalTheory.GLq.hcL (Q'.map Prod.snd) r := by
    rw [← Set.mem_singleton_iff, ← hset]; exact ⟨hirr, hlab⟩
  refine ⟨this ▸ hset, ?_⟩
  unfold GlobalTheory.GLq.eSerC
  rw [hset, finsum_mem_singleton, ← this]
  unfold GlobalTheory.GLq.zOf centralIdem
  rw [Nat.card_eq_fintype_card]
  convert rfl

end GlobalTheory.ParamLabel

end
