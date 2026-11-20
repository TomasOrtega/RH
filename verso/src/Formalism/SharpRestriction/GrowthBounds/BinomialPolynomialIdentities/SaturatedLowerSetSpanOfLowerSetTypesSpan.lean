import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.FormalSeriesConditionsB1ToB4
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.ComponentsInFiltrationContractionSingle

noncomputable section

open MvPolynomial Finset
open scoped Pointwise

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.Joints

/- English proof (translation)
Introduce `G hG`. Rewrite `hG` using `[Submodule.mem_iInf]`. Establish `h1 : ∀ i, ∃ z h : X →₀ R, z ∈ Finsupp.supported R R (A i) ∧ G = Finsupp.linearCombination R b (z + q • h)`. Introduce `i`. Take `⟨Z, hZ, Y, hY, hsum⟩` from `Submodule.mem_sup.1 (hG i)`.

Take `⟨z, hz, rfl⟩` from `(Finsupp.mem_span_image_iff_linearCombination R).1 hZ`. Take `⟨H, hH, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hY`. Take `⟨h, rfl⟩` from `(Finsupp.mem_span_range_iff_exists_finsupp).1 hH`. Use `⟨z, h, hz, ?_⟩` and prove the remaining obligations. Rewrite using `[← hsum, map_add, map_smul]`.

Both sides reduce to the same expression. Use `choose z h hz hG' using h1`. Take `⟨i0⟩` from `(inferInstance : Nonempty κ)`. Use `set c : X →₀ R := z i0 + q • h i0 with hc`. Establish `hci : ∀ i, z i + q • h i = c` using `fun i => hb ((hG' i).symm.trans (hG' i0))`.

Establish `hdiv : ∀ x, (¬ ∀ i, x ∈ A i) → ∃ d, c x = q * d`. Introduce `x hx`. Use `push Not at hx`. Take `⟨i, hi⟩` from `hx`. Use `⟨h i x, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hci i, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]`. Establish `: z i x = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hi ((Finsupp.mem_supported R (z i)).1 (hz i) (Finsupp.mem_support_iff.2 hne))`. Rewrite using `[this, zero_add]`.

Use `choose! d hd using hdiv`. Establish `hGc : G = ∑ x ∈ c.support, c x • b x`. Rewrite using `[hG' i0, Finsupp.linearCombination_apply, Finsupp.sum]`. Rewrite `hGc` using `[← Finset.sum_filter_add_sum_filter_not c.support (fun x => ∀ i, x ∈ A i)]`. Rewrite using `[hGc]`.

Use `Submodule.add_mem_sup ?_ ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_iInf]`. Introduce `i`. Use `Submodule.sum_mem _ fun x hx => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, ?_, rfl⟩)` and prove the remaining obligations. Conclude with `(Finset.mem_filter.1 hx).2 i`.

Rewrite using `[Submodule.mem_smul_pointwise_iff_exists]`. Use `⟨∑ x ∈ c.support.filter (fun x => ¬ ∀ i, x ∈ A i), d x • b x, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations.

Rewrite using `[hd x (Finset.mem_filter.1 hx).2, mul_smul]`.
-/
theorem iInf_span_sup_smul_le {R M X κ : Type*} [CommRing R] [AddCommGroup M] [Module R M] {b : X → M}
    (hb : LinearIndependent R b) (A : κ → Set X) [Nonempty κ] (q : R) :
    (⨅ i, (Submodule.span R (b '' A i) ⊔ q • Submodule.span R (Set.range b))) ≤
      (⨅ i, Submodule.span R (b '' A i)) ⊔ q • Submodule.span R (Set.range b) := by
  classical
  intro G hG
  rw [Submodule.mem_iInf] at hG
  have h1 : ∀ i, ∃ z h : X →₀ R, z ∈ Finsupp.supported R R (A i) ∧
      G = Finsupp.linearCombination R b (z + q • h) := by
    intro i
    obtain ⟨Z, hZ, Y, hY, hsum⟩ := Submodule.mem_sup.1 (hG i)
    obtain ⟨z, hz, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination R).1 hZ
    obtain ⟨H, hH, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hY
    obtain ⟨h, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hH
    refine ⟨z, h, hz, ?_⟩
    rw [← hsum, map_add, map_smul]
    rfl
  choose z h hz hG' using h1
  obtain ⟨i0⟩ := (inferInstance : Nonempty κ)
  set c : X →₀ R := z i0 + q • h i0 with hc
  have hci : ∀ i, z i + q • h i = c := fun i => hb ((hG' i).symm.trans (hG' i0))
  have hdiv : ∀ x, (¬ ∀ i, x ∈ A i) → ∃ d, c x = q * d := by
    intro x hx
    push Not at hx
    obtain ⟨i, hi⟩ := hx
    refine ⟨h i x, ?_⟩
    rw [← hci i, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    have : z i x = 0 := by
      by_contra hne
      exact hi ((Finsupp.mem_supported R (z i)).1 (hz i) (Finsupp.mem_support_iff.2 hne))
    rw [this, zero_add]
  choose! d hd using hdiv
  have hGc : G = ∑ x ∈ c.support, c x • b x := by
    rw [hG' i0, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [← Finset.sum_filter_add_sum_filter_not c.support (fun x => ∀ i, x ∈ A i)] at hGc
  rw [hGc]
  refine Submodule.add_mem_sup ?_ ?_
  · rw [Submodule.mem_iInf]
    intro i
    refine Submodule.sum_mem _ fun x hx => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, ?_, rfl⟩)
    exact (Finset.mem_filter.1 hx).2 i
  · rw [Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨∑ x ∈ c.support.filter (fun x => ¬ ∀ i, x ∈ A i), d x • b x, ?_, ?_⟩
    · exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
    · rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [hd x (Finset.mem_filter.1 hx).2, mul_smul]

section

variable {O : Type} [CommRing O] {N n : ℕ} (LL : Letters (Fin N)) (B : Fin N → ℕ)

def wd (R : Type) [CommRing R] (x : WI n N LL B) : MvPolynomial (Fin N × Fin n) R := Psi R x.1.1.mu x.1.2

/- English proof (translation)
Use `congr 1`. Use extensionality with `G`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨P, I, hI, hp, rfl⟩`. Conclude with `⟨⟨(P, I), hI⟩, hp, rfl⟩`.

Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨x.1.1, x.1.2, x.2, hx, rfl⟩`.
-/
theorem span_standard_words_eq (R : Type) [CommRing R] (cond : PPath n N LL B → Prop) :
    Submodule.span R {G | ∃ P : PPath n N LL B, ∃ I, IsSt P.mu I ∧ cond P ∧ G = Psi R P.mu I} =
      Submodule.span R (wd LL B R '' {x | cond x.1.1}) := by
  congr 1
  ext G
  constructor
  · rintro ⟨P, I, hI, hp, rfl⟩
    exact ⟨⟨(P, I), hI⟩, hp, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1.1, x.1.2, x.2, hx, rfl⟩

/- English proof (translation)
Rewrite using `[← (standardPath_basis_any_ring R N n LL B).2]`. Use `congr 1`. Use extensionality with `G`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`.

Conclude with `⟨x.1.1, x.1.2, x.2, rfl⟩`. Introduce and unpack `⟨P, I, hI, rfl⟩`. Conclude with `⟨⟨(P, I), hI⟩, rfl⟩`.
-/
theorem span_words_eq_polynomials (R : Type) [CommRing R] : Submodule.span R (Set.range (wd LL B R)) = Pol R n B := by
  rw [← (standardPath_basis_any_ring R N n LL B).2]
  congr 1
  ext G
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1.1, x.1.2, x.2, rfl⟩
  · rintro ⟨P, I, hI, rfl⟩
    exact ⟨⟨(P, I), hI⟩, rfl⟩

end

/- English proof (translation)
Introduce `O _ _ _ _ N n LL B pi hpi`. Establish `hinj : Function.Injective (algebraMap O (KK O))` using `IsFractionRing.injective O (KK O)`. Establish `hmapwd : ∀ x : WI n N LL B, MvPolynomial.map (algebraMap O (KK O)) (wd LL B O x) = wd LL B (KK O) x` using `fun x => Formalism.MainNotions.LemmaBAlt.map_Psi' (algebraMap O (KK O)) x.1.1.mu x.1.2`. Establish `hLIK : LinearIndependent (KK O) (wd LL B (KK O))` using `(standardPath_basis_any_ring (KK O) N n LL B).1`. Establish `hLIO : LinearIndependent O (wd LL B O)` using `(standardPath_basis_any_ring O N n LL B).1`.

Establish `hT : ∀ i : Fin (N + 1), Pol (KK O) n B ⊓ (⨆ lam ∈ pi i, isoSub (glOps (KK O) n LL {l | l.val < i.val}) lam) = Submodule.span (KK O) (wd LL B (KK O) '' {x | x.1.1.mu i ∈ pi i})`. Introduce `i`. Rewrite using `[hN2 (KK O) N n LL B i (pi i) (hpi i)]`. Conclude with `span_standard_words_eq LL B (KK O) (fun P => P.mu i ∈ pi i)`. Establish `hmaplc : ∀ c : WI n N LL B →₀ O, MvPolynomial.map (algebraMap O (KK O)) (Finsupp.linearCombination O (wd LL B O) c) = Finsupp.linearCombination (KK O) (wd LL B (KK O)) (c.mapRange (algebraMap O (KK O)) (map_zero _))`.

Introduce `c`. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by intro i; exact zero_smul _ _), Finsupp.sum, Finsupp.sum, map_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, hmapwd, ← MvPolynomial.smul_eq_C_mul]`. Prove the components needed by the constructor for the conclusion.

Introduce `Ix`. Establish `hspan : nestSpan O N n LL B pi Ix = Submodule.span O (wd LL B O '' {x | ∀ i ∈ Ix, x.1.1.mu i ∈ pi i})` using `span_standard_words_eq LL B O (fun P => ∀ i ∈ Ix, P.mu i ∈ pi i)`. Use extensionality with `G`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hG, hGi⟩`.

Rewrite `hG` using `[← span_words_eq_polynomials LL B O]`. Take `⟨c, rfl⟩` from `(Finsupp.mem_span_range_iff_exists_finsupp).1 hG`. Express the relevant statement in the definitionally equal form `(c.sum fun x a => a • wd LL B O x) ∈ nestSpan O N n LL B pi Ix`. Rewrite using `[hspan]`. Use `Submodule.sum_mem _ fun x hx => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, ?_, rfl⟩)` and prove the remaining obligations.

Introduce `i hi`. Establish `h1 : MvPolynomial.map (algebraMap O (KK O)) (Finsupp.linearCombination O (wd LL B O) c) ∈ Submodule.span (KK O) (wd LL B (KK O) '' {x | x.1.1.mu i ∈ pi i})`. Rewrite using `[← hT i]`. Use `⟨?_, hGi i hi⟩` and prove the remaining obligations. Rewrite using `[hmaplc, ← span_words_eq_polynomials LL B (KK O)]`.

Conclude with `Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨_, rfl⟩`. Take `⟨l, hl, hle⟩` from `(Finsupp.mem_span_image_iff_linearCombination (KK O)).1 h1`. Rewrite `hle` using `[hmaplc]`. Establish `hlc` using `hLIK hle`. Establish `hxl : x ∈ l.support`.

Rewrite using `[hlc, Finsupp.mem_support_iff, Finsupp.mapRange_apply]`. Introduce `h0`. Conclude with `(Finsupp.mem_support_iff.1 hx) (hinj (by rw [h0, map_zero]))`. Conclude with `(Finsupp.mem_supported (KK O) l).1 hl hxl`. Introduce `hG`.

Express the relevant statement in the definitionally equal form `G ∈ nestSpan O N n LL B pi Ix at hG`. Rewrite `hG` using `[hspan]`. Proceed by induction on `hG using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨x, hx, rfl⟩` from `hy`.

Use `⟨?_, fun i hi => ?_⟩` and prove the remaining obligations. Rewrite using `[← span_words_eq_polynomials LL B O]`. Conclude with `Submodule.subset_span ⟨x, rfl⟩`. Rewrite using `[hmapwd]`. Establish `: wd LL B (KK O) x ∈ Pol (KK O) n B ⊓ (⨆ lam ∈ pi i, isoSub (glOps (KK O) n LL {l | l.val < i.val}) lam)`.

Rewrite using `[hT i]`. Conclude with `Submodule.subset_span ⟨x, hx i hi, rfl⟩`. Conclude with `this.2`. Consider the case `zero => exact ⟨Submodule.zero_mem _, fun i _ => by rw [map_zero]; exact Submodule.zero_mem _⟩`. Consider the case `add x y _ _ hx hy`.

Conclude with `⟨Submodule.add_mem _ hx.1 hy.1, fun i hi => by`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ (hx.2 i hi) (hy.2 i hi)⟩`. Consider the case `smul a x _ hx`. Conclude with `⟨Submodule.smul_mem _ _ hx.1, fun i hi => by`.

Rewrite using `[MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ (hx.2 i hi)⟩`. Introduce `p E`. Establish `hspan : ∀ i : Fin (N + 1), nestSpan O N n LL B pi {i} = Submodule.span O (wd LL B O '' {x | x.1.1.mu i ∈ pi i})`. Introduce `i`.

Establish `h1 : {x : WI n N LL B | ∀ i' ∈ ({i} : Set (Fin (N + 1))), x.1.1.mu i' ∈ pi i'} = {x | x.1.1.mu i ∈ pi i}`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq]`. Rewrite using `[← h1]`. Conclude with `span_standard_words_eq LL B O (fun P => ∀ i' ∈ ({i} : Set (Fin (N + 1))), P.mu i' ∈ pi i')`.

Simplify using `only [hspan]`. Rewrite using `[Submodule.ideal_span_singleton_smul, ← span_words_eq_polynomials LL B O]`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `iInf_span_sup_smul_le hLIO _ _`. Conclude with `le_iInf fun i => sup_le_sup_right (iInf_le _ i) _`.
-/
theorem saturatedLowerSetSpan_of_lowerSetTypesSpan (D : Formalism.BasicNotions.D7) (hN2 : LowerSetTypesSpan) : SaturatedLowerSetSpan D := by
  classical
  intro O _ _ _ _ N n LL B pi hpi
  have hinj : Function.Injective (algebraMap O (KK O)) := IsFractionRing.injective O (KK O)
  have hmapwd : ∀ x : WI n N LL B, MvPolynomial.map (algebraMap O (KK O)) (wd LL B O x) = wd LL B (KK O) x :=
    fun x => Formalism.MainNotions.LemmaBAlt.map_Psi' (algebraMap O (KK O)) x.1.1.mu x.1.2
  have hLIK : LinearIndependent (KK O) (wd LL B (KK O)) := (standardPath_basis_any_ring (KK O) N n LL B).1
  have hLIO : LinearIndependent O (wd LL B O) := (standardPath_basis_any_ring O N n LL B).1
  have hT : ∀ i : Fin (N + 1), Pol (KK O) n B ⊓ (⨆ lam ∈ pi i, isoSub (glOps (KK O) n LL {l | l.val < i.val}) lam) =
      Submodule.span (KK O) (wd LL B (KK O) '' {x | x.1.1.mu i ∈ pi i}) := by
    intro i
    rw [hN2 (KK O) N n LL B i (pi i) (hpi i)]
    exact span_standard_words_eq LL B (KK O) (fun P => P.mu i ∈ pi i)
  have hmaplc : ∀ c : WI n N LL B →₀ O, MvPolynomial.map (algebraMap O (KK O)) (Finsupp.linearCombination O (wd LL B O) c) =
      Finsupp.linearCombination (KK O) (wd LL B (KK O)) (c.mapRange (algebraMap O (KK O)) (map_zero _)) := by
    intro c
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (by intro i; exact zero_smul _ _), Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, hmapwd, ← MvPolynomial.smul_eq_C_mul]
  constructor
  · intro Ix
    have hspan : nestSpan O N n LL B pi Ix = Submodule.span O (wd LL B O '' {x | ∀ i ∈ Ix, x.1.1.mu i ∈ pi i}) :=
      span_standard_words_eq LL B O (fun P => ∀ i ∈ Ix, P.mu i ∈ pi i)
    ext G
    constructor
    · rintro ⟨hG, hGi⟩
      rw [← span_words_eq_polynomials LL B O] at hG
      obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hG
      change (c.sum fun x a => a • wd LL B O x) ∈ nestSpan O N n LL B pi Ix
      rw [hspan]
      refine Submodule.sum_mem _ fun x hx => Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, ?_, rfl⟩)
      intro i hi
      have h1 : MvPolynomial.map (algebraMap O (KK O)) (Finsupp.linearCombination O (wd LL B O) c) ∈
          Submodule.span (KK O) (wd LL B (KK O) '' {x | x.1.1.mu i ∈ pi i}) := by
        rw [← hT i]
        refine ⟨?_, hGi i hi⟩
        rw [hmaplc, ← span_words_eq_polynomials LL B (KK O)]
        exact Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨_, rfl⟩
      obtain ⟨l, hl, hle⟩ := (Finsupp.mem_span_image_iff_linearCombination (KK O)).1 h1
      rw [hmaplc] at hle
      have hlc := hLIK hle
      have hxl : x ∈ l.support := by
        rw [hlc, Finsupp.mem_support_iff, Finsupp.mapRange_apply]
        intro h0
        exact (Finsupp.mem_support_iff.1 hx) (hinj (by rw [h0, map_zero]))
      exact (Finsupp.mem_supported (KK O) l).1 hl hxl
    · intro hG
      change G ∈ nestSpan O N n LL B pi Ix at hG
      rw [hspan] at hG
      induction hG using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        refine ⟨?_, fun i hi => ?_⟩
        · rw [← span_words_eq_polynomials LL B O]
          exact Submodule.subset_span ⟨x, rfl⟩
        · rw [hmapwd]
          have : wd LL B (KK O) x ∈ Pol (KK O) n B ⊓
              (⨆ lam ∈ pi i, isoSub (glOps (KK O) n LL {l | l.val < i.val}) lam) := by
            rw [hT i]
            exact Submodule.subset_span ⟨x, hx i hi, rfl⟩
          exact this.2
      | zero => exact ⟨Submodule.zero_mem _, fun i _ => by rw [map_zero]; exact Submodule.zero_mem _⟩
      | add x y _ _ hx hy =>
        exact ⟨Submodule.add_mem _ hx.1 hy.1, fun i hi => by
          rw [map_add]; exact Submodule.add_mem _ (hx.2 i hi) (hy.2 i hi)⟩
      | smul a x _ hx =>
        exact ⟨Submodule.smul_mem _ _ hx.1, fun i hi => by
          rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
          exact Submodule.smul_mem _ _ (hx.2 i hi)⟩
  · intro p E
    have hspan : ∀ i : Fin (N + 1), nestSpan O N n LL B pi {i} =
        Submodule.span O (wd LL B O '' {x | x.1.1.mu i ∈ pi i}) := by
      intro i
      have h1 : {x : WI n N LL B | ∀ i' ∈ ({i} : Set (Fin (N + 1))), x.1.1.mu i' ∈ pi i'} =
          {x | x.1.1.mu i ∈ pi i} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq]
      rw [← h1]
      exact span_standard_words_eq LL B O (fun P => ∀ i' ∈ ({i} : Set (Fin (N + 1))), P.mu i' ∈ pi i')
    simp only [hspan]
    rw [Submodule.ideal_span_singleton_smul, ← span_words_eq_polynomials LL B O]
    apply le_antisymm
    · exact iInf_span_sup_smul_le hLIO _ _
    · exact le_iInf fun i => sup_le_sup_right (iInf_le _ i) _

end Formalism.MainNotions.G.ColumnFamilies
