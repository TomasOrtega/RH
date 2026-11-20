import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfClosedCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfRingEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfSubsingletonStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `set K := I ⊓ J with hK`. Set `f` to `Ideal.Quotient.mk K`. Establish `hqA : IsUnit (q : R ⧸ K)` using `by simpa using hq.map f`. Establish `hinf : Ideal.map f I ⊓ Ideal.map f J ≤ nilradical (R ⧸ K)`. Introduce `x hx`.

Take `⟨a, ha, rfl⟩` from `(Ideal.mem_map_iff_of_surjective f Ideal.Quotient.mk_surjective).mp hx.1`. Take `⟨b, hb, hab⟩` from `(Ideal.mem_map_iff_of_surjective f Ideal.Quotient.mk_surjective).mp hx.2`. Establish `h1 : b - a ∈ K` using `Ideal.Quotient.eq.mp hab`. Establish `haJ : a ∈ J`. Use `J.sub_mem hb h1.2` as an intermediate fact.

Simplify using `using this`. Establish `: f a = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr ⟨ha, haJ⟩`. Rewrite using `[this]`. Conclude with `(nilradical (R ⧸ K)).zero_mem`. Establish `eI : (R ⧸ K) ⧸ Ideal.map f I ≃+* R ⧸ I` using `DoubleQuot.quotQuotEquivQuotOfLE inf_le_left`.

Establish `eJ : (R ⧸ K) ⧸ Ideal.map f J ≃+* R ⧸ J` using `DoubleQuot.quotQuotEquivQuotOfLE inf_le_right`. Establish `eIJ : (R ⧸ K) ⧸ (Ideal.map f I ⊔ Ideal.map f J) ≃+* R ⧸ (I ⊔ J)` using `(Ideal.quotEquivOfEq (Ideal.map_sup f I J).symm).trans (DoubleQuot.quotQuotEquivQuotOfLE (inf_le_left.trans le_sup_left))`. Conclude with `GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q (R ⧸ K) (Ideal.map f I) (Ideal.map f J) hinf hqA (GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ eI.symm hI) (GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ eJ.symm hJ) (GlobalTheory.T.et …`.
-/
theorem hInv_quot_inf (q : ℕ) [NeZero q] (R : Type) [CommRing R] (I J : Ideal R)
    (hq : IsUnit (q : R)) (hI : HInv q (R ⧸ I)) (hJ : HInv q (R ⧸ J))
    (hIJ : HInv q (R ⧸ (I ⊔ J))) : HInv q (R ⧸ (I ⊓ J)) := by
  set K := I ⊓ J with hK
  let f := Ideal.Quotient.mk K
  have hqA : IsUnit (q : R ⧸ K) := by simpa using hq.map f
  have hinf : Ideal.map f I ⊓ Ideal.map f J ≤ nilradical (R ⧸ K) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective f Ideal.Quotient.mk_surjective).mp hx.1
    obtain ⟨b, hb, hab⟩ := (Ideal.mem_map_iff_of_surjective f Ideal.Quotient.mk_surjective).mp hx.2
    have h1 : b - a ∈ K := Ideal.Quotient.eq.mp hab
    have haJ : a ∈ J := by
      have := J.sub_mem hb h1.2
      simpa using this
    have : f a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ⟨ha, haJ⟩
    rw [this]
    exact (nilradical (R ⧸ K)).zero_mem
  have eI : (R ⧸ K) ⧸ Ideal.map f I ≃+* R ⧸ I := DoubleQuot.quotQuotEquivQuotOfLE inf_le_left
  have eJ : (R ⧸ K) ⧸ Ideal.map f J ≃+* R ⧸ J := DoubleQuot.quotQuotEquivQuotOfLE inf_le_right
  have eIJ : (R ⧸ K) ⧸ (Ideal.map f I ⊔ Ideal.map f J) ≃+* R ⧸ (I ⊔ J) :=
    (Ideal.quotEquivOfEq (Ideal.map_sup f I J).symm).trans
      (DoubleQuot.quotQuotEquivQuotOfLE (inf_le_left.trans le_sup_left))
  exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q (R ⧸ K) (Ideal.map f I) (Ideal.map f J) hinf hqA
    (GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ eI.symm hI) (GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ eJ.symm hJ)
    (GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ eIJ.symm hIJ)

/- English proof (translation)
Take `⟨x, hxJ, hxp⟩` from `Set.not_subset.mp hJ`. Set `g` to `Ideal.Quotient.mk p`. Establish `hx0 : g x ≠ 0` using `fun h => hxp (Ideal.Quotient.eq_zero_iff_mem.mp h)`. Establish `hnzd : g x ∈ nonZeroDivisors (R ⧸ p)` using `mem_nonZeroDivisors_of_ne_zero hx0`. Establish `h1` using `ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd`.

Establish `hle : Ideal.span {g x} ≤ Ideal.map g (p ⊔ J)`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `Ideal.mem_map_of_mem g (Ideal.mem_sup_right hxJ)`. Establish `h2 : ringKrullDim ((R ⧸ p) ⧸ Ideal.map g (p ⊔ J)) ≤ ringKrullDim ((R ⧸ p) ⧸ Ideal.span {g x})` using `ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)`. Establish `e : (R ⧸ p) ⧸ Ideal.map g (p ⊔ J) ≃+* R ⧸ (p ⊔ J)` using `DoubleQuot.quotQuotEquivQuotOfLE le_sup_left`.

Establish `h3 : ringKrullDim (R ⧸ (p ⊔ J)) ≤ ringKrullDim ((R ⧸ p) ⧸ Ideal.map g (p ⊔ J))` using `ringKrullDim_le_of_surjective e.toRingHom e.surjective`. Establish `h4 : ringKrullDim (R ⧸ (p ⊔ J)) + 1 ≤ ringKrullDim ((R ⧸ p) ⧸ Ideal.span {g x}) + 1` using `by gcongr`. Conclude with `h3.trans h2`. Conclude with `h4.trans h1`.
-/
theorem ringKrullDim_quot_sup_succ_le (R : Type) [CommRing R] (p J : Ideal R) [p.IsPrime]
    (hJ : ¬ J ≤ p) : ringKrullDim (R ⧸ (p ⊔ J)) + 1 ≤ ringKrullDim (R ⧸ p) := by
  obtain ⟨x, hxJ, hxp⟩ := Set.not_subset.mp hJ
  let g := Ideal.Quotient.mk p
  have hx0 : g x ≠ 0 := fun h => hxp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hnzd : g x ∈ nonZeroDivisors (R ⧸ p) := mem_nonZeroDivisors_of_ne_zero hx0
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd
  have hle : Ideal.span {g x} ≤ Ideal.map g (p ⊔ J) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem g (Ideal.mem_sup_right hxJ)
  have h2 : ringKrullDim ((R ⧸ p) ⧸ Ideal.map g (p ⊔ J)) ≤
      ringKrullDim ((R ⧸ p) ⧸ Ideal.span {g x}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
  have e : (R ⧸ p) ⧸ Ideal.map g (p ⊔ J) ≃+* R ⧸ (p ⊔ J) :=
    DoubleQuot.quotQuotEquivQuotOfLE le_sup_left
  have h3 : ringKrullDim (R ⧸ (p ⊔ J)) ≤ ringKrullDim ((R ⧸ p) ⧸ Ideal.map g (p ⊔ J)) :=
    ringKrullDim_le_of_surjective e.toRingHom e.surjective
  have h4 : ringKrullDim (R ⧸ (p ⊔ J)) + 1 ≤ ringKrullDim ((R ⧸ p) ⧸ Ideal.span {g x}) + 1 := by
    gcongr
    exact h3.trans h2
  exact h4.trans h1

/- English proof (translation)
Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot => exact WithBot.bot_lt_coe _`. Consider the case `coe e`. Proceed by induction on `e using ENat.recTopCoe with`. Consider the case `top`.

It suffices to derive a contradiction. Establish `h2 : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((d : ℕ∞)) : WithBot ℕ∞)` using `by exact_mod_cast h`. Rewrite `h2` using `[WithBot.coe_le_coe]`. Simplify using `at h2`. Consider the case `coe n`.

Establish `h' : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞)` using `by exact_mod_cast h`. Establish `: n + 1 ≤ d` using `by exact_mod_cast h'`. Establish `: n < d` using `by omega`. Conclude with `this` after adjusting the coercions.
-/
theorem withBot_lt_of_add_one_le (a : WithBot ℕ∞) (d : ℕ) (h : a + 1 ≤ (d : WithBot ℕ∞)) :
    a < (d : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h2 : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((d : ℕ∞)) : WithBot ℕ∞) := by exact_mod_cast h
      rw [WithBot.coe_le_coe] at h2
      simp at h2
    | coe n =>
      have h' : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by exact_mod_cast h
      have : n + 1 ≤ d := by exact_mod_cast h'
      have : n < d := by omega
      exact_mod_cast this

end GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `q _ d hlt hdom R _ _ hq hd`. Establish `key : ∀ s : Finset (Ideal R), (∀ p ∈ s, p.IsPrime) → HInv q (R ⧸ s.inf id)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`.

Introduce `_`. Use `haveI : Subsingleton (R ⧸ (∅ : Finset (Ideal R)).inf id) := Ideal.Quotient.subsingleton_iff.mpr (by simp)`. Conclude with `GlobalTheory.T.etaleHomotopyInvariantTwists_of_subsingleton q _ inferInstance`. Consider the case `insert p s hps ih`. Introduce `hs`.

Establish `hp : p.IsPrime` using `hs p (Finset.mem_insert_self p s)`. Establish `ihs` using `ih (fun r hr => hs r (Finset.mem_insert_of_mem hr))`. Rewrite using `[Finset.inf_insert, id]`. Distinguish the cases in `hJ : s.inf id ≤ p`. Rewrite using `[inf_eq_right.mpr hJ]`.

Conclude with `ihs`. Use `haveI : @Algebra.FiniteType ℤ (R ⧸ p) _ _ (Ring.toIntAlgebra _) := by`. Use `(inferInstance : Algebra.FiniteType ℤ (R ⧸ p))` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first | rfl | exact Subsingleton.elim _ _`. Use `haveI : @Algebra.FiniteType ℤ (R ⧸ (p ⊔ s.inf id)) _ _ (Ring.toIntAlgebra _) := by`.

Use `(inferInstance : Algebra.FiniteType ℤ (R ⧸ (p ⊔ s.inf id)))` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first | rfl | exact Subsingleton.elim _ _`. Use `hInv_quot_inf q R p (s.inf id) hq ?_ ihs ?_` and prove the remaining obligations. Conclude with `hdom (R ⧸ p) (by simpa using hq.map (Ideal.Quotient.mk p)) ((ringKrullDim_le_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective).trans hd)`. Use `hlt (R ⧸ (p ⊔ s.inf id)) (by simpa using hq.map (Ideal.Quotient.mk (p ⊔ s.inf id))) ?_` and prove the remaining obligations.

Use `withBot_lt_of_add_one_le _ d ?_` and prove the remaining obligations. Conclude with `(ringKrullDim_quot_sup_succ_le R p (s.inf id) hJ).trans ((ringKrullDim_le_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective).trans hd)`. Use `haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R`. Establish `hfin` using `minimalPrimes.finite_of_isNoetherianRing R`. Establish `hN : hfin.toFinset.inf id = nilradical R`.

Rewrite using `[Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset, minimalPrimes, Ideal.sInf_minimalPrimes]`. Both sides reduce to the same expression. Establish `hred : HInv q (R ⧸ nilradical R)`. Rewrite using `[← hN]`. Use `key _ (fun p hp => ?_)` and prove the remaining obligations.

Rewrite `hp` using `[Set.Finite.mem_toFinset]`. Conclude with `hp.1.1`. Conclude with `GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q R (nilradical R) (nilradical R) (by simp) hq hred hred (by rwa [sup_idem])`.
-/
theorem hInv_of_domains_of_dim_lt : ∀ (q : ℕ) [NeZero q] (d : ℕ),
    (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) →
    (∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → HInv q D) →
    ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R ≤ d → HInv q R := by
  intro q _ d hlt hdom R _ _ hq hd
  have key : ∀ s : Finset (Ideal R), (∀ p ∈ s, p.IsPrime) → HInv q (R ⧸ s.inf id) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      haveI : Subsingleton (R ⧸ (∅ : Finset (Ideal R)).inf id) :=
        Ideal.Quotient.subsingleton_iff.mpr (by simp)
      exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_subsingleton q _ inferInstance
    | insert p s hps ih =>
      intro hs
      have hp : p.IsPrime := hs p (Finset.mem_insert_self p s)
      have ihs := ih (fun r hr => hs r (Finset.mem_insert_of_mem hr))
      rw [Finset.inf_insert, id]
      by_cases hJ : s.inf id ≤ p
      · rw [inf_eq_right.mpr hJ]; exact ihs
      · haveI : @Algebra.FiniteType ℤ (R ⧸ p) _ _ (Ring.toIntAlgebra _) := by
          convert (inferInstance : Algebra.FiniteType ℤ (R ⧸ p))
          all_goals first | rfl | exact Subsingleton.elim _ _
        haveI : @Algebra.FiniteType ℤ (R ⧸ (p ⊔ s.inf id)) _ _ (Ring.toIntAlgebra _) := by
          convert (inferInstance : Algebra.FiniteType ℤ (R ⧸ (p ⊔ s.inf id)))
          all_goals first | rfl | exact Subsingleton.elim _ _
        refine hInv_quot_inf q R p (s.inf id) hq ?_ ihs ?_
        · exact hdom (R ⧸ p) (by simpa using hq.map (Ideal.Quotient.mk p))
            ((ringKrullDim_le_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective).trans hd)
        · refine hlt (R ⧸ (p ⊔ s.inf id)) (by simpa using hq.map (Ideal.Quotient.mk (p ⊔ s.inf id))) ?_
          refine withBot_lt_of_add_one_le _ d ?_
          exact (ringKrullDim_quot_sup_succ_le R p (s.inf id) hJ).trans
            ((ringKrullDim_le_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective).trans hd)
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have hfin := minimalPrimes.finite_of_isNoetherianRing R
  have hN : hfin.toFinset.inf id = nilradical R := by
    rw [Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset, minimalPrimes, Ideal.sInf_minimalPrimes]
    rfl
  have hred : HInv q (R ⧸ nilradical R) := by
    rw [← hN]
    refine key _ (fun p hp => ?_)
    rw [Set.Finite.mem_toFinset] at hp
    exact hp.1.1
  exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q R (nilradical R) (nilradical R) (by simp) hq hred hred (by rwa [sup_idem])

end GlobalTheory
