import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RankOneBaseWeightEqCmTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.LevelPlaceSep

/- English proof (translation)
Take `⟨a, b, hab⟩ : IsCoprime (p : ℤ) (q : ℤ)` from `Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hpq)`. Establish `e` using `congrArg (Int.cast : ℤ → 𝓞 D.host.E) hab`. Move the coercions through the operations in `at e`. Apply `P.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← e]`.

Establish `h1' : ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal` using `h1`. Establish `h2' : ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal` using `h2`. Conclude with `P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h1') (P.asIdeal.mul_mem_left _ h2')`.
-/
theorem not_mem_two {D : D7} (P : PlE D.host) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h1 : P ∈ placesOver D.host.E p) (h2 : P ∈ placesOver D.host.E q) : False := by
  obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hpq)
  have e := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hab
  push_cast at e
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  have h1' : ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := h1
  have h2' : ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := h2
  exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h1') (P.asIdeal.mul_mem_left _ h2')

/- English proof (translation)
Establish `e : ((p : ℕ) : 𝓞 D.host.E) = (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) (p : 𝓞 (maximalRealSubfield D.host.E))` using `(map_natCast _ p).symm`. Use `show ((p : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal`. Establish `hP' : ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal` using `hP`. Rewrite using `[e, ← Ideal.mem_comap, ← h, Ideal.mem_comap, ← e]`. Conclude with `hP'`.
-/
theorem mem_placesOver_of_comap {D : D7} {P P' : PlE D.host}
    (h : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))) {p : ℕ}
    (hP : P ∈ placesOver D.host.E p) : P' ∈ placesOver D.host.E p := by
  have e : ((p : ℕ) : 𝓞 D.host.E) = (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) (p : 𝓞 (maximalRealSubfield D.host.E)) := (map_natCast _ p).symm
  show ((p : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal
  have hP' : ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := hP
  rw [e, ← Ideal.mem_comap, ← h, Ideal.mem_comap, ← e]
  exact hP'

/- English proof (translation)
Introduce `x y hxy`. Rewrite using `[GlobalTheory.SplitConjPlace.mem_conjPlE]`. Establish `: IsCMField.ringOfIntegersComplexConj D.host.E y = x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[IsCMField.coe_ringOfIntegersComplexConj, hxy, GlobalTheory.LocM.complexConj_eq_conj, GlobalTheory.FixedPlaceSplit.host_conj_conj]`.

Rewrite using `[this]`.
-/
theorem isConjPl_conjPlE {D : D7} (P : PlE D.host) : Formalism.BasicNotions.IsConjPl D.host P (GlobalTheory.SplitConjPlace.conjPlE P) := by
  intro x y hxy
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
  have : IsCMField.ringOfIntegersComplexConj D.host.E y = x := by
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, hxy, GlobalTheory.LocM.complexConj_eq_conj,
      GlobalTheory.FixedPlaceSplit.host_conj_conj]
  rw [this]

/- English proof (translation)
Break down `GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE P P' (hv'.trans hv.symm) with e | e` into its components or cases. Conclude with `e.symm`. Establish `hw : (Pq v).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = v.asIdeal` using `hPq v`. Establish `hS : Pq v ∈ S`. Break down `GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE P (Pq v) (hw.trans hv.symm) with e' | e'` into its components or cases.

Rewrite using `[e']`. Conclude with `qpOf_sub D Pq S hP`. Rewrite using `[e', ← e]`. Conclude with `qpOf_sub D Pq S hP'`. Conclude with `(qpOf_eq D Pq S hP hv hS).trans (qpOf_eq D Pq S hP' hv' hS).symm`.
-/
theorem eq_of_qpOf {D : D7} (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host)
    (hPq : ∀ v, NG.OverPl (Pq v) v) (S : Finset (PlE D.host)) {P P' : PlE D.host}
    (hP : P ∈ qpOf D Pq S) (hP' : P' ∈ qpOf D Pq S) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (hv : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = v.asIdeal) (hv' : P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = v.asIdeal) : P = P' := by
  rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE P P' (hv'.trans hv.symm) with e | e
  · exact e.symm
  have hw : (Pq v).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = v.asIdeal := hPq v
  have hS : Pq v ∈ S := by
    rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE P (Pq v) (hw.trans hv.symm) with e' | e'
    · rw [e']; exact qpOf_sub D Pq S hP
    · rw [e', ← e]; exact qpOf_sub D Pq S hP'
  exact (qpOf_eq D Pq S hP hv hS).trans (qpOf_eq D Pq S hP' hv' hS).symm

/- English proof (translation)
Establish `h0` using `D.host.g_ne`. Apply the tactic sequence `fin_cases k <;> fin_cases k' <;> simp_all [eq_comm]`.
-/
theorem g_ne_g {D : D7} {k k' : Fin 2} (h : k ≠ k') : D.host.g k ≠ D.host.g k' := by
  have h0 := D.host.g_ne
  fin_cases k <;> fin_cases k' <;> simp_all [eq_comm]

/- English proof (translation)
Introduce `D T i Q Pq sp hPq hQs hQ hpDs hsp`. Choose the witnesses or unpack the hypotheses as in `⟨pp, hpp, hne, hpD⟩ : ∃ pp : ℕ, pp.Prime ∧ (∀ k, pp ≠ D.host.g k) ∧ ∀ P, P ∈ T.pD i ↔ P ∈ placesOver D.host.E pp := by`. Use `⟨if T.l i = D.host.pde then D.host.pde' else D.host.pde, ?_, ?_, fun P => by rw [← Finset.mem_coe, T.pD_eq i]⟩` and prove the remaining obligations. Use `split_ifs`. Conclude with `D.host.pde'_prime`.

Conclude with `D.host.pde_prime`. Introduce `k split_ifs`. Conclude with `(D.host.pde_ne_g k).2`. Conclude with `(D.host.pde_ne_g k).1`. Establish `hG : ∀ kv, NX.pG D kv ∈ placesOver D.host.E (D.host.g kv.1)` using `fun kv => D.naut.plGw_over kv.1 kv.2`.

Establish `c2 : ∀ P ∈ qpOf D Pq Q, P ∉ qpOf D Pq (T.pD i)` using `fun P hP hP' => (hQ P (qpOf_sub D Pq Q hP)).1 (qpOf_sub D Pq _ hP')`. Establish `c3 : ∀ kv, NX.pG D kv ∉ qpOf D Pq Q ∧ NX.pG D kv ∉ qpOf D Pq (T.pD i)` using `fun kv => ⟨fun h => (hQ _ (qpOf_sub D Pq Q h)).2 kv.1 (hG kv), fun h => not_mem_two _ hpp (D.host.g_prime kv.1) (hne kv.1) ((hpD _).1 (qpOf_sub D Pq _ h)) (hG kv)⟩`. Establish `c4 : ∀ kv kv', NX.pG D kv = NX.pG D kv' → kv = kv'`. Introduce and unpack `⟨k, v⟩ ⟨k', v'⟩ h`. Distinguish the cases in `hk : k = k'`.

Substitute `hk` using the available equality. Establish `: v = v'` using `D.naut.plGw_inj k h`. Rewrite using `[this]`. Conclude with `(not_mem_two _ (D.host.g_prime k) (D.host.g_prime k') (g_ne_g hk) (hG ⟨k, v⟩) (by rw [h]; exact hG ⟨k', v'⟩)).elim`. Use `⟨?_, c2, c3, c4⟩` and prove the remaining obligations.

Introduce `P P' hP hP' hv`. Establish `hcP : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = (sp P).v.asIdeal`. Use `(sp P).w_under` as an intermediate fact. Rewrite `this` using `[hsp P hP]`. Conclude with `this`.

Establish `hcP' : P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = (sp P).v.asIdeal`. Use `(sp P').w_under` as an intermediate fact. Rewrite `this` using `[hsp P' hP']`. Rewrite using `[this, hv]`. Establish `hc : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))` using `hcP.trans hcP'.symm`.

Establish `same : ∀ {p : ℕ}, P' ∈ placesOver D.host.E p → P ∈ placesOver D.host.E p` using `fun h => mem_placesOver_of_comap hc.symm h`. Establish `same' : ∀ {p : ℕ}, P ∈ placesOver D.host.E p → P' ∈ placesOver D.host.E p` using `fun h => mem_placesOver_of_comap hc h`. Apply the tactic sequence `rcases hP with hP | hP | ⟨kv, rfl⟩ <;> rcases hP' with hP' | hP' | ⟨kv', rfl⟩`. Conclude with `eq_of_qpOf Pq hPq Q hP hP' _ hcP hcP'`. Conclude with `((hQ P (qpOf_sub D Pq Q hP)).1 ((hpD P).2 (same ((hpD P').1 (qpOf_sub D Pq _ hP'))))).elim`.

Conclude with `((hQ P (qpOf_sub D Pq Q hP)).2 kv'.1 (same (hG kv'))).elim`. Conclude with `((hQ P' (qpOf_sub D Pq Q hP')).1 ((hpD P').2 (same' ((hpD P).1 (qpOf_sub D Pq _ hP))))).elim`. Conclude with `eq_of_qpOf Pq hPq _ hP hP' _ hcP hcP'`. Conclude with `(not_mem_two P hpp (D.host.g_prime kv'.1) (hne kv'.1) ((hpD P).1 (qpOf_sub D Pq _ hP)) (same (hG kv'))).elim`. Conclude with `((hQ P' (qpOf_sub D Pq Q hP')).2 kv.1 (same' (hG kv))).elim`.

Conclude with `(not_mem_two P' hpp (D.host.g_prime kv.1) (hne kv.1) ((hpD P').1 (qpOf_sub D Pq _ hP')) (same' (hG kv))).elim`. Take `⟨k, v⟩` from `kv`. Take `⟨k', v'⟩` from `kv'`. Distinguish the cases in `hk : k = k'`. Substitute `hk` using the available equality.

Break down `GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE (NX.pG D ⟨k, v⟩) (NX.pG D ⟨k, v'⟩) hc.symm with e | e` into its components or cases. Conclude with `e.symm`. Establish `hc2` using `isConjPl_conjPlE (NX.pG D ⟨k, v⟩)`. Rewrite `hc2` using `[← e]`. Conclude with `(D.naut.plGw_nconj k v v' hc2).elim`.

Conclude with `(not_mem_two _ (D.host.g_prime k) (D.host.g_prime k') (g_ne_g hk) (hG ⟨k, v⟩) (same (hG ⟨k', v'⟩))).elim`.
-/
theorem levelPlaces_sep : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (Q : Finset (PlE D.host))
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (sp : PlE D.host → SplitPlace D.host.E),
    (∀ v, NG.OverPl (Pq v) v) → (∀ P ∈ Q, IsSplitPl D.host P) →
    (∀ P ∈ Q, P ∉ T.pD i ∧ ∀ k' : Fin 2, P ∉ placesOver D.host.E (D.host.g k')) → (∀ P ∈ T.pD i, IsSplitPl D.host P) →
    (∀ P, (P ∈ qpOf D Pq Q ∨ P ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P = NX.pG D kv) → (sp P).w = P) →
    (∀ P P', (P ∈ qpOf D Pq Q ∨ P ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P = NX.pG D kv) →
      (P' ∈ qpOf D Pq Q ∨ P' ∈ qpOf D Pq (T.pD i) ∨ ∃ kv, P' = NX.pG D kv) → (sp P).v = (sp P').v → P = P') ∧
    (∀ P ∈ qpOf D Pq Q, P ∉ qpOf D Pq (T.pD i)) ∧ (∀ kv, NX.pG D kv ∉ qpOf D Pq Q ∧ NX.pG D kv ∉ qpOf D Pq (T.pD i)) ∧
    ∀ kv kv', NX.pG D kv = NX.pG D kv' → kv = kv' := by
  intro D T i Q Pq sp hPq hQs hQ hpDs hsp
  obtain ⟨pp, hpp, hne, hpD⟩ : ∃ pp : ℕ, pp.Prime ∧ (∀ k, pp ≠ D.host.g k) ∧
      ∀ P, P ∈ T.pD i ↔ P ∈ placesOver D.host.E pp := by
    refine ⟨if T.l i = D.host.pde then D.host.pde' else D.host.pde, ?_, ?_,
      fun P => by rw [← Finset.mem_coe, T.pD_eq i]⟩
    · split_ifs
      · exact D.host.pde'_prime
      · exact D.host.pde_prime
    · intro k
      split_ifs
      · exact (D.host.pde_ne_g k).2
      · exact (D.host.pde_ne_g k).1
  have hG : ∀ kv, NX.pG D kv ∈ placesOver D.host.E (D.host.g kv.1) := fun kv => D.naut.plGw_over kv.1 kv.2
  have c2 : ∀ P ∈ qpOf D Pq Q, P ∉ qpOf D Pq (T.pD i) := fun P hP hP' =>
    (hQ P (qpOf_sub D Pq Q hP)).1 (qpOf_sub D Pq _ hP')
  have c3 : ∀ kv, NX.pG D kv ∉ qpOf D Pq Q ∧ NX.pG D kv ∉ qpOf D Pq (T.pD i) := fun kv =>
    ⟨fun h => (hQ _ (qpOf_sub D Pq Q h)).2 kv.1 (hG kv),
     fun h => not_mem_two _ hpp (D.host.g_prime kv.1) (hne kv.1) ((hpD _).1 (qpOf_sub D Pq _ h)) (hG kv)⟩
  have c4 : ∀ kv kv', NX.pG D kv = NX.pG D kv' → kv = kv' := by
    rintro ⟨k, v⟩ ⟨k', v'⟩ h
    by_cases hk : k = k'
    · subst hk
      have : v = v' := D.naut.plGw_inj k h
      rw [this]
    · exact (not_mem_two _ (D.host.g_prime k) (D.host.g_prime k') (g_ne_g hk) (hG ⟨k, v⟩)
        (by rw [h]; exact hG ⟨k', v'⟩)).elim
  refine ⟨?_, c2, c3, c4⟩
  intro P P' hP hP' hv
  have hcP : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = (sp P).v.asIdeal := by
    have := (sp P).w_under; rw [hsp P hP] at this; exact this
  have hcP' : P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = (sp P).v.asIdeal := by
    have := (sp P').w_under; rw [hsp P' hP'] at this; rw [this, hv]
  have hc : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := hcP.trans hcP'.symm
  have same : ∀ {p : ℕ}, P' ∈ placesOver D.host.E p → P ∈ placesOver D.host.E p :=
    fun h => mem_placesOver_of_comap hc.symm h
  have same' : ∀ {p : ℕ}, P ∈ placesOver D.host.E p → P' ∈ placesOver D.host.E p :=
    fun h => mem_placesOver_of_comap hc h
  rcases hP with hP | hP | ⟨kv, rfl⟩ <;> rcases hP' with hP' | hP' | ⟨kv', rfl⟩
  · exact eq_of_qpOf Pq hPq Q hP hP' _ hcP hcP'
  · exact ((hQ P (qpOf_sub D Pq Q hP)).1 ((hpD P).2 (same ((hpD P').1 (qpOf_sub D Pq _ hP'))))).elim
  · exact ((hQ P (qpOf_sub D Pq Q hP)).2 kv'.1 (same (hG kv'))).elim
  · exact ((hQ P' (qpOf_sub D Pq Q hP')).1 ((hpD P').2 (same' ((hpD P).1 (qpOf_sub D Pq _ hP))))).elim
  · exact eq_of_qpOf Pq hPq _ hP hP' _ hcP hcP'
  · exact (not_mem_two P hpp (D.host.g_prime kv'.1) (hne kv'.1) ((hpD P).1 (qpOf_sub D Pq _ hP))
      (same (hG kv'))).elim
  · exact ((hQ P' (qpOf_sub D Pq Q hP')).2 kv.1 (same' (hG kv))).elim
  · exact (not_mem_two P' hpp (D.host.g_prime kv.1) (hne kv.1) ((hpD P').1 (qpOf_sub D Pq _ hP'))
      (same' (hG kv))).elim
  · obtain ⟨k, v⟩ := kv
    obtain ⟨k', v'⟩ := kv'
    by_cases hk : k = k'
    · subst hk
      rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE (NX.pG D ⟨k, v⟩) (NX.pG D ⟨k, v'⟩) hc.symm with e | e
      · exact e.symm
      · have hc2 := isConjPl_conjPlE (NX.pG D ⟨k, v⟩)
        rw [← e] at hc2
        exact (D.naut.plGw_nconj k v v' hc2).elim
    · exact (not_mem_two _ (D.host.g_prime k) (D.host.g_prime k') (g_ne_g hk) (hG ⟨k, v⟩)
        (same (hG ⟨k', v'⟩))).elim

end GlobalTheory.LevelPlaceSep
