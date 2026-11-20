import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.T0

open IsLocalRing

/- English proof (translation)
Establish `hza : (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum S) < ⟨A, ‹A.IsPrime›⟩` using `h1`. Establish `hab : (⟨A, ‹A.IsPrime›⟩ : PrimeSpectrum S) < ⟨B, ‹B.IsPrime›⟩` using `h2`. Establish `e1` using `Order.height_add_one_le hza`. Establish `e2` using `Order.height_add_one_le hab`. Unfold `Ideal.height at hB`.

Use `absurd hB (not_le.mpr (lt_of_lt_of_le (show (1 : ℕ∞) < 2 by norm_num) (le_iInf₂ fun J hJ => ?_)))` and prove the remaining obligations. Establish `hJB : J = B`. Establish `h'` using `hJ`. Rewrite `h'` using `[Ideal.minimalPrimes_eq_subsingleton_self]`. Conclude with `h'`.

Substitute `hJB` using the available equality. Express the relevant statement in the definitionally equal form `(2 : ℕ∞) ≤ Order.height (⟨J, ‹J.IsPrime›⟩ : PrimeSpectrum S)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem av_no_two_chain {S : Type*} [CommRing S] [IsDomain S] {A B : Ideal S} [A.IsPrime]
    [B.IsPrime] (h1 : ⊥ < A) (h2 : A < B) (hB : B.height ≤ 1) : False := by
  have hza : (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum S) < ⟨A, ‹A.IsPrime›⟩ := h1
  have hab : (⟨A, ‹A.IsPrime›⟩ : PrimeSpectrum S) < ⟨B, ‹B.IsPrime›⟩ := h2
  have e1 := Order.height_add_one_le hza
  have e2 := Order.height_add_one_le hab
  unfold Ideal.height at hB
  refine absurd hB (not_le.mpr (lt_of_lt_of_le (show (1 : ℕ∞) < 2 by norm_num)
    (le_iInf₂ fun J hJ => ?_)))
  have hJB : J = B := by
    have h' := hJ
    rw [Ideal.minimalPrimes_eq_subsingleton_self] at h'
    exact h'
  subst hJB
  change (2 : ℕ∞) ≤ Order.height (⟨J, ‹J.IsPrime›⟩ : PrimeSpectrum S)
  calc (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ _ := le_trans (add_le_add (le_add_self.trans e1) le_rfl) e2

/- English proof (translation)
Assume the negation of the conclusion as `hQm`. Use `set m := IsLocalRing.maximalIdeal S with hm_def`. Establish `hQlt : Q < m` using `lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQ.ne_top) (fun h => hQm (h ▸ IsLocalRing.maximalIdeal.isMaximal S))`. Use `haveI : (Ideal.span {g}).IsPrincipal := ⟨⟨g, rfl⟩⟩`. Establish `hfin` using `Ideal.finite_minimalPrimes_of_isNoetherianRing S (Ideal.span {g})`.

Establish `hmin : ∀ P ∈ (Ideal.span {g}).minimalPrimes, P.IsPrime ∧ P ≠ ⊥ ∧ P.height ≤ 1`. Introduce `P hP`. Use `⟨hP.1.1, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Apply `hg` to reduce the goal to its premises.

Use `hP.1.2 (Ideal.mem_span_singleton_self g)` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `(Submodule.mem_bot S).mp this`. Conclude with `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP`. Establish `hbelow : ∀ P' : Ideal S, P'.IsPrime → P' ≠ ⊥ → ∃ P ∈ (Ideal.span {g}).minimalPrimes, P ≤ P'`.

Introduce `P' hP' h0`. Conclude with `Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).mpr (H P' hP' h0))`. Establish `hm_not : ∀ P ∈ (Ideal.span {g}).minimalPrimes, ¬ m ≤ P`. Introduce `P hP hmP`. Take `⟨P0, hP0, hP0Q⟩` from `hbelow Q hQ hQ0`.

Take `⟨hPp, -, hPh⟩` from `hmin P hP`. Take `⟨hP0p, hP00, -⟩` from `hmin P0 hP0`. Use `haveI := hPp`. Use `haveI := hP0p`. Conclude with `av_no_two_chain (bot_lt_iff_ne_bot.mpr hP00) (lt_of_le_of_lt hP0Q (lt_of_lt_of_le hQlt hmP)) hPh`.

Choose the witnesses or unpack the hypotheses as in `⟨x, hxm, hxP⟩ : ∃ x ∈ m, ∀ P ∈ (Ideal.span {g}).minimalPrimes, x ∉ P := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hsub : (m : Set S) ⊆ ⋃ P ∈ (hfin.toFinset : Set (Ideal S)), ((id P : Ideal S) : Set S)`. Introduce `y hy`.

Take `⟨P, hP, hyP⟩` from `hcon y hy`. Conclude with `Set.mem_iUnion₂.mpr ⟨P, by simpa using hP, hyP⟩`. Take `⟨P, hP, hle⟩` from `(Ideal.subset_union_prime (f := id) ⊥ ⊥ (fun P hP _ _ => (hmin P (by simpa using hP)).1)).mp hsub`. Conclude with `hm_not P (by simpa using hP) hle`. Take `⟨P0, hP0, -⟩` from `hbelow Q hQ hQ0`.

Establish `hx0 : x ≠ 0`. Introduce `h`. Apply `hxP P0 hP0` to reduce the goal to its premises. Rewrite using `[h]`. Conclude with `Submodule.zero_mem _`.

Take `⟨P', hP', -⟩` from `Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem m).mpr hxm)`. Use `haveI := hP'.1.1`. Establish `hxP' : x ∈ P'` using `hP'.1.2 (Ideal.mem_span_singleton_self x)`. Establish `hP'0 : P' ≠ ⊥`. Introduce `h`.

Rewrite `hxP'` using `[h]`. Conclude with `hx0 ((Submodule.mem_bot S).mp hxP')`. Use `haveI : (Ideal.span {x}).IsPrincipal := ⟨⟨x, rfl⟩⟩`. Establish `hP'h : P'.height ≤ 1` using `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P' hP'`. Take `⟨P, hP, hPP'⟩` from `hbelow P' hP'.1.1 hP'0`.

Take `⟨hPp, hP00, -⟩` from `hmin P hP`. Break down `lt_or_eq_of_le hPP' with hlt | heq` into its components or cases. Use `haveI := hPp`. Conclude with `av_no_two_chain (bot_lt_iff_ne_bot.mpr hP00) hlt hP'h`. Apply `hxP P hP` to reduce the goal to its premises.

Rewrite using `[heq]`. Conclude with `hxP'`.
-/
theorem av_key {S : Type*} [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsLocalRing S] (g : S)
    (hg : g ≠ 0) (H : ∀ Q : Ideal S, Q.IsPrime → Q ≠ ⊥ → g ∈ Q) (Q : Ideal S) (hQ : Q.IsPrime)
    (hQ0 : Q ≠ ⊥) : Q.IsMaximal := by
  classical
  by_contra hQm
  set m := IsLocalRing.maximalIdeal S with hm_def
  have hQlt : Q < m := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQ.ne_top)
    (fun h => hQm (h ▸ IsLocalRing.maximalIdeal.isMaximal S))
  haveI : (Ideal.span {g}).IsPrincipal := ⟨⟨g, rfl⟩⟩
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing S (Ideal.span {g})

  have hmin : ∀ P ∈ (Ideal.span {g}).minimalPrimes, P.IsPrime ∧ P ≠ ⊥ ∧ P.height ≤ 1 := by
    intro P hP
    refine ⟨hP.1.1, ?_, ?_⟩
    · intro h
      apply hg
      have := hP.1.2 (Ideal.mem_span_singleton_self g)
      rw [h] at this
      exact (Submodule.mem_bot S).mp this
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP

  have hbelow : ∀ P' : Ideal S, P'.IsPrime → P' ≠ ⊥ →
      ∃ P ∈ (Ideal.span {g}).minimalPrimes, P ≤ P' := by
    intro P' hP' h0
    exact Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).mpr (H P' hP' h0))

  have hm_not : ∀ P ∈ (Ideal.span {g}).minimalPrimes, ¬ m ≤ P := by
    intro P hP hmP
    obtain ⟨P0, hP0, hP0Q⟩ := hbelow Q hQ hQ0
    obtain ⟨hPp, -, hPh⟩ := hmin P hP
    obtain ⟨hP0p, hP00, -⟩ := hmin P0 hP0
    haveI := hPp
    haveI := hP0p
    exact av_no_two_chain (bot_lt_iff_ne_bot.mpr hP00)
      (lt_of_le_of_lt hP0Q (lt_of_lt_of_le hQlt hmP)) hPh

  obtain ⟨x, hxm, hxP⟩ : ∃ x ∈ m, ∀ P ∈ (Ideal.span {g}).minimalPrimes, x ∉ P := by
    by_contra hcon
    push_neg at hcon
    have hsub : (m : Set S) ⊆ ⋃ P ∈ (hfin.toFinset : Set (Ideal S)), ((id P : Ideal S) : Set S) := by
      intro y hy
      obtain ⟨P, hP, hyP⟩ := hcon y hy
      exact Set.mem_iUnion₂.mpr ⟨P, by simpa using hP, hyP⟩
    obtain ⟨P, hP, hle⟩ := (Ideal.subset_union_prime (f := id) ⊥ ⊥
      (fun P hP _ _ => (hmin P (by simpa using hP)).1)).mp hsub
    exact hm_not P (by simpa using hP) hle
  obtain ⟨P0, hP0, -⟩ := hbelow Q hQ hQ0
  have hx0 : x ≠ 0 := by
    intro h
    apply hxP P0 hP0
    rw [h]
    exact Submodule.zero_mem _
  obtain ⟨P', hP', -⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem m).mpr hxm)
  haveI := hP'.1.1
  have hxP' : x ∈ P' := hP'.1.2 (Ideal.mem_span_singleton_self x)
  have hP'0 : P' ≠ ⊥ := by
    intro h
    rw [h] at hxP'
    exact hx0 ((Submodule.mem_bot S).mp hxP')
  haveI : (Ideal.span {x}).IsPrincipal := ⟨⟨x, rfl⟩⟩
  have hP'h : P'.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P' hP'
  obtain ⟨P, hP, hPP'⟩ := hbelow P' hP'.1.1 hP'0
  obtain ⟨hPp, hP00, -⟩ := hmin P hP
  rcases lt_or_eq_of_le hPP' with hlt | heq
  · haveI := hPp
    exact av_no_two_chain (bot_lt_iff_ne_bot.mpr hP00) hlt hP'h
  · apply hxP P hP
    rw [heq]
    exact hxP'

/- English proof (translation)
Use `set m := IsLocalRing.maximalIdeal R with hm_def`. Establish `hm0 : m ≠ ⊥`. Introduce `e`. Establish `hF : IsField R` using `(IsLocalRing.isField_iff_maximalIdeal_eq).mpr e`. Rewrite `hdim` using `[ringKrullDim_eq_zero_of_isField hF]`.

Conclude with `absurd hdim (by norm_num)`. Take `⟨p, ⟨hpP, hhp, hpm⟩, hpmax⟩` from `set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R R) {q : Ideal R | q.IsPrime ∧ h ∉ q ∧ q ≠ m} ⟨⊥, Ideal.bot_prime, fun h' => hh ((Submodule.mem_bot R).mp h'), fun e => hm0 e.symm⟩`. Use `haveI := hpP`. Use `⟨p, hpP, ?_, hhp⟩` and prove the remaining obligations. Establish `hplt : p < m` using `lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hpP.ne_top) hpm`.

Take `⟨y, hym, hyp⟩` from `SetLike.exists_of_lt hplt`. Use `set f := Ideal.Quotient.mk p with hf_def`. Use `haveI : IsLocalRing (R ⧸ p) := IsLocalRing.of_surjective' f Ideal.Quotient.mk_surjective`. Establish `hfz : ∀ a : R, f a = 0 ↔ a ∈ p` using `fun a => Ideal.Quotient.eq_zero_iff_mem`. Establish `hg0 : f (h * y) ≠ 0`.

Rewrite using `[Ne, hfz]`. Introduce `hm'`. Break down `hpP.mem_or_mem hm' with h1 | h1` into its components or cases. Conclude with `hhp h1`. Conclude with `hyp h1`.

Establish `hall : ∀ Q : Ideal (R ⧸ p), Q.IsPrime → Q ≠ ⊥ → f (h * y) ∈ Q`. Introduce `Q hQ hQ0`. Use `haveI := hQ`. Establish `hq : (Q.comap f).IsPrime` using `inferInstance`. Establish `hpq : p < Q.comap f`.

Use `lt_of_le_of_ne (fun a ha => ?_) (fun e => hQ0 ?_)` and prove the remaining obligations. Use `show f a ∈ Q`. Rewrite using `[(hfz a).mpr ha]`. Conclude with `Q.zero_mem`. Rewrite using `[eq_bot_iff]`.

Introduce `z hz`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Establish `ha : a ∈ Q.comap f` using `hz`. Rewrite `ha` using `[← e]`. Conclude with `(Submodule.mem_bot _).mpr ((hfz a).mpr ha)`.

Use `show h * y ∈ Q.comap f`. Distinguish the cases in `hhq : h ∈ Q.comap f`. Conclude with `Ideal.mul_mem_right _ _ hhq`. Establish `hqm : Q.comap f = m`. Assume the negation of the conclusion as `hne`.

Conclude with `hpmax _ ⟨hq, hhq, hne⟩ hpq`. Rewrite using `[hqm]`. Conclude with `Ideal.mul_mem_left _ _ hym`. Establish `hmax : ∀ Q : Ideal (R ⧸ p), Q.IsPrime → Q ≠ ⊥ → Q.IsMaximal` using `fun Q hQ hQ0 => av_key (f (h * y)) hg0 hall Q hQ hQ0`. Apply `le_antisymm` to reduce the goal to its premises.

Unfold `ringKrullDim Order.krullDim`. Use `iSup_le fun s => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Establish `h2 : 2 ≤ s.length`. Assume the negation of the conclusion as `h2`.

Apply `hlt` to reduce the goal to its premises. Establish `: s.length ≤ 1` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `a01 : s ⟨0, by omega⟩ < s ⟨1, by omega⟩` using `s.strictMono (Fin.mk_lt_mk.mpr (by norm_num))`. Establish `a12 : s ⟨1, by omega⟩ < s ⟨2, by omega⟩` using `s.strictMono (Fin.mk_lt_mk.mpr (by norm_num))`.

Rewrite `a01`, `a12` using `[← PrimeSpectrum.asIdeal_lt_asIdeal]`. Establish `hne : (s ⟨1, by omega⟩).asIdeal ≠ ⊥` using `fun e => not_lt_bot (e ▸ a01)`. Establish `hM` using `hmax _ (s ⟨1, by omega⟩).isPrime hne`. Conclude with `a12.ne (hM.eq_of_le (s ⟨2, by omega⟩).isPrime.ne_top a12.le)`. Use `haveI hMp : (m.map f).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hplt.le)`.

Establish `hlt : (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum (R ⧸ p)) < ⟨m.map f, hMp⟩`. Rewrite using `[← PrimeSpectrum.asIdeal_lt_asIdeal]`. Use `bot_lt_iff_ne_bot.mpr fun e => ?_` and prove the remaining obligations. Establish `hy : f y ∈ m.map f` using `Ideal.mem_map_of_mem f hym`. Establish `e' : m.map f = ⊥` using `e`.

Rewrite `hy` using `[e']`. Conclude with `hyp ((hfz y).mp ((Submodule.mem_bot _).mp hy))`. Establish `e1` using `Order.height_add_one_le hlt`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem av_prime_dim_one {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    (hdim : 1 ≤ ringKrullDim R) (h : R) (hh : h ≠ 0) :
    ∃ p : Ideal R, p.IsPrime ∧ ringKrullDim (R ⧸ p) = 1 ∧ h ∉ p := by
  classical
  set m := IsLocalRing.maximalIdeal R with hm_def
  have hm0 : m ≠ ⊥ := by
    intro e
    have hF : IsField R := (IsLocalRing.isField_iff_maximalIdeal_eq).mpr e
    rw [ringKrullDim_eq_zero_of_isField hF] at hdim
    exact absurd hdim (by norm_num)

  obtain ⟨p, ⟨hpP, hhp, hpm⟩, hpmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R) {q : Ideal R | q.IsPrime ∧ h ∉ q ∧ q ≠ m}
    ⟨⊥, Ideal.bot_prime, fun h' => hh ((Submodule.mem_bot R).mp h'), fun e => hm0 e.symm⟩
  haveI := hpP
  refine ⟨p, hpP, ?_, hhp⟩
  have hplt : p < m := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hpP.ne_top) hpm
  obtain ⟨y, hym, hyp⟩ := SetLike.exists_of_lt hplt
  set f := Ideal.Quotient.mk p with hf_def
  haveI : IsLocalRing (R ⧸ p) := IsLocalRing.of_surjective' f Ideal.Quotient.mk_surjective
  have hfz : ∀ a : R, f a = 0 ↔ a ∈ p := fun a => Ideal.Quotient.eq_zero_iff_mem
  have hg0 : f (h * y) ≠ 0 := by
    rw [Ne, hfz]
    intro hm'
    rcases hpP.mem_or_mem hm' with h1 | h1
    · exact hhp h1
    · exact hyp h1

  have hall : ∀ Q : Ideal (R ⧸ p), Q.IsPrime → Q ≠ ⊥ → f (h * y) ∈ Q := by
    intro Q hQ hQ0
    haveI := hQ
    have hq : (Q.comap f).IsPrime := inferInstance
    have hpq : p < Q.comap f := by
      refine lt_of_le_of_ne (fun a ha => ?_) (fun e => hQ0 ?_)
      · show f a ∈ Q
        rw [(hfz a).mpr ha]
        exact Q.zero_mem
      · rw [eq_bot_iff]
        intro z hz
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
        have ha : a ∈ Q.comap f := hz
        rw [← e] at ha
        exact (Submodule.mem_bot _).mpr ((hfz a).mpr ha)
    show h * y ∈ Q.comap f
    by_cases hhq : h ∈ Q.comap f
    · exact Ideal.mul_mem_right _ _ hhq
    · have hqm : Q.comap f = m := by
        by_contra hne
        exact hpmax _ ⟨hq, hhq, hne⟩ hpq
      rw [hqm]
      exact Ideal.mul_mem_left _ _ hym
  have hmax : ∀ Q : Ideal (R ⧸ p), Q.IsPrime → Q ≠ ⊥ → Q.IsMaximal :=
    fun Q hQ hQ0 => av_key (f (h * y)) hg0 hall Q hQ hQ0
  apply le_antisymm
  · unfold ringKrullDim Order.krullDim
    refine iSup_le fun s => ?_
    by_contra hlt
    have h2 : 2 ≤ s.length := by
      by_contra h2
      apply hlt
      have : s.length ≤ 1 := by omega
      exact_mod_cast this
    have a01 : s ⟨0, by omega⟩ < s ⟨1, by omega⟩ := s.strictMono (Fin.mk_lt_mk.mpr (by norm_num))
    have a12 : s ⟨1, by omega⟩ < s ⟨2, by omega⟩ := s.strictMono (Fin.mk_lt_mk.mpr (by norm_num))
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at a01 a12
    have hne : (s ⟨1, by omega⟩).asIdeal ≠ ⊥ := fun e => not_lt_bot (e ▸ a01)
    have hM := hmax _ (s ⟨1, by omega⟩).isPrime hne
    exact a12.ne (hM.eq_of_le (s ⟨2, by omega⟩).isPrime.ne_top a12.le)
  · haveI hMp : (m.map f).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hplt.le)
    have hlt : (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum (R ⧸ p)) < ⟨m.map f, hMp⟩ := by
      rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
      refine bot_lt_iff_ne_bot.mpr fun e => ?_
      have hy : f y ∈ m.map f := Ideal.mem_map_of_mem f hym
      have e' : m.map f = ⊥ := e
      rw [e'] at hy
      exact hyp ((hfz y).mp ((Submodule.mem_bot _).mp hy))
    have e1 := Order.height_add_one_le hlt
    calc (1 : WithBot ℕ∞) ≤ ((Order.height (⟨m.map f, hMp⟩ : PrimeSpectrum (R ⧸ p)) : ℕ∞) :
          WithBot ℕ∞) := by exact_mod_cast (le_add_self.trans e1)
      _ ≤ ringKrullDim (R ⧸ p) := Order.height_le_krullDim _

end ReciprocityTheory.ChartRestriction.G.T0
