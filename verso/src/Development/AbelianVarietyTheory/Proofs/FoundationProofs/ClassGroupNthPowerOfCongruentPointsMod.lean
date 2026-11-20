import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DedekindFiniteTypeIdealCodimensionStatement
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `k A _ _ _ _ _ _ _ N _hN hyp hf c`. Take `⟨f, hf0, hfm⟩` from `hf`. Take `⟨_hfin, hmax, hadd, _hle⟩` from `GlobalTheory.T.dedekind_finiteType_ideal_codimension k A`. Establish `nz : ∀ I : Ideal A, I ≠ ⊥ → I ∈ nonZeroDivisors (Ideal A)` using `fun I hI => mem_nonZeroDivisors_of_ne_zero hI`. Take `⟨I, rfl⟩` from `ClassGroup.mk0_surjective c`.

Establish `hI0 : (I : Ideal A) ≠ ⊥` using `nonZeroDivisors.coe_ne_zero I`. Distinguish the cases in `hex : ∃ P₀ : Ideal A, P₀.IsMaximal ∧ P₀ ≠ ⊥`. Use `swap`. Use `push_neg at hex`. Establish `htop : (I : Ideal A) = ⊤`.

Assume the negation of the conclusion as `h`. Take `⟨M, hM, hIM⟩` from `Ideal.exists_le_maximal _ h`. Conclude with `hI0 (le_bot_iff.mp (hex M hM ▸ hIM))`. Use `⟨1, ?_⟩` and prove the remaining obligations. Establish `: I = 1` using `Subtype.ext (by rw [htop]; exact Ideal.one_eq_top.symm)`.

Rewrite using `[this, map_one, one_pow]`. Take `⟨P₀, hP₀, hP₀ne⟩` from `hex`. Set `H : Subgroup (ClassGroup A)` to `(powMonoidHom N : ClassGroup A →* ClassGroup A).range`. Set `π : ClassGroup A →* ClassGroup A ⧸ H` to `QuotientGroup.mk' H`. Establish `hπ : ∀ d : ClassGroup A, π (d ^ N) = 1` using `fun d => (QuotientGroup.eq_one_iff _).mpr ⟨d, rfl⟩`.

Set `γ : ClassGroup A` to `ClassGroup.mk0 ⟨P₀, nz P₀ hP₀ne⟩`. Establish `hbot : ¬ (⊥ : Ideal A).IsMaximal` using `fun h => hP₀ne (h.eq_of_le hP₀.ne_top bot_le).symm`. Establish `hjac : ∀ x : A, x ≠ 0 → ∃ Q : Ideal A, Q.IsMaximal ∧ x ∉ Q`. Introduce `x hx`. Use `haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)`.

Establish `hj : (⊥ : Ideal A).jacobson = ⊥` using `IsJacobsonRing.out' _ (Ideal.isPrime_bot).isRadical`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Apply `hx` to reduce the goal to its premises. Establish `: x ∈ (⊥ : Ideal A).jacobson`.

Rewrite using `[Ideal.jacobson]`. Conclude with `Submodule.mem_sInf.mpr fun J hJ => hne J hJ.2`. Rewrite `this` using `[hj]`. Conclude with `(Submodule.mem_bot A).mp this`. Establish `hmaxcls : ∀ (P : Ideal A) (hP : P.IsMaximal) (hPne : P ≠ ⊥), π (ClassGroup.mk0 ⟨P, nz P hPne⟩) = π γ`.

Introduce `P hP hPne`. Take `⟨a₀, ha₀, H0⟩` from `hyp P₀ hP₀ (nz P₀ hP₀ne)`. Take `⟨a₁, ha₁, H1⟩` from `hyp P hP (nz P hPne)`. Take `⟨Q, hQ, hQa⟩` from `hjac (a₀ * a₁) (mul_ne_zero ha₀ ha₁)`. Establish `hQne : Q ≠ ⊥` using `by rintro rfl; exact hbot hQ`.

Take `⟨d, hd⟩` from `H0 Q hQ (fun h => hQa (Q.mul_mem_right _ h)) (nz Q hQne)`. Take `⟨e, he⟩` from `H1 Q hQ (fun h => hQa (Q.mul_mem_left _ h)) (nz Q hQne)`. Establish `h1` using `congrArg π hd`. Establish `h2` using `congrArg π he`. Rewrite `h1`, `h2` using `[map_mul, hπ, mul_one]`.

Rewrite using `[← h2, h1]`. Establish `hall : ∀ J : Ideal A, ∀ hJ : J ∈ nonZeroDivisors (Ideal A), π (ClassGroup.mk0 ⟨J, hJ⟩) = π γ ^ Module.finrank k (A ⧸ J)`. Introduce `J`. Use `UniqueFactorizationMonoid.induction_on_prime (P := fun J : Ideal A => ∀ hJ : J ∈ nonZeroDivisors (Ideal A), π (ClassGroup.mk0 ⟨J, hJ⟩) = π γ ^ Module.finrank k (A ⧸ J)) J ?_ ?_ ?_` and prove the remaining obligations. Introduce `h`.

Conclude with `absurd rfl (nonZeroDivisors.ne_zero h)`. Introduce `x hx h`. Establish `hx' : x = ⊤` using `Ideal.isUnit_iff.mp hx`. Substitute `hx'` using the available equality. Establish `e1 : (⟨⊤, h⟩ : nonZeroDivisors (Ideal A)) = 1` using `Subtype.ext Ideal.one_eq_top.symm`.

Use `haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl`. Rewrite using `[e1, map_one, map_one, Module.finrank_zero_of_subsingleton, pow_zero]`. Introduce `a p ha hp ih h`. Establish `hpne : p ≠ ⊥` using `hp.ne_zero`. Establish `hpmax : p.IsMaximal` using `(Ideal.isPrime_of_prime hp).isMaximal hpne`.

Establish `e1 : (⟨p * a, h⟩ : nonZeroDivisors (Ideal A)) = ⟨p, nz p hpne⟩ * ⟨a, nz a ha⟩` using `rfl`. Rewrite using `[e1, map_mul, map_mul, hmaxcls p hpmax hpne, ih (nz a ha), hadd p a hpne ha, (hmax p hpmax).1, pow_add, pow_one]`. Establish `hγN : π γ ^ N = 1` using `by rw [← map_pow]; exact hπ γ`. Establish `hspan : Ideal.span {f} ≠ ⊥`. Simplify `hf0` using `[Ideal.span_singleton_eq_bot]`.

Establish `hγ1 : π γ = 1`. Establish `e` using `hall _ (nz _ hspan)`. Establish `e0 : ClassGroup.mk0 (⟨Ideal.span {f}, nz _ hspan⟩ : nonZeroDivisors (Ideal A)) = 1` using `(ClassGroup.mk0_eq_one_iff _).mpr ⟨⟨f, rfl⟩⟩`. Rewrite `e` using `[e0, map_one]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hc` using `hall I.1 I.2`. Rewrite `hc` using `[hγ1, one_pow]`. Establish `hmem : ClassGroup.mk0 I ∈ H` using `(QuotientGroup.eq_one_iff _).mp hc`. Take `⟨d, hd⟩` from `hmem`. Conclude with `⟨d, hd.symm⟩`.
-/
theorem classGroup_nthPower_of_codim_one_mod : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ), 1 ≤ N → (∀ P₀ : Ideal A, P₀.IsMaximal → ∀ h₀ : P₀ ∈ nonZeroDivisors (Ideal A), ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal → a ∉ P → ∀ h : P ∈ nonZeroDivisors (Ideal A), ∃ d : ClassGroup A, ClassGroup.mk0 ⟨P, h⟩ = ClassGroup.mk0 ⟨P₀, h₀⟩ * d ^ N) → (∃ f : A, f ≠ 0 ∧ Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N) → ∀ c : ClassGroup A, ∃ d, c = d ^ N := by
  intro k A _ _ _ _ _ _ _ N _hN hyp hf c
  obtain ⟨f, hf0, hfm⟩ := hf
  obtain ⟨_hfin, hmax, hadd, _hle⟩ := GlobalTheory.T.dedekind_finiteType_ideal_codimension k A
  have nz : ∀ I : Ideal A, I ≠ ⊥ → I ∈ nonZeroDivisors (Ideal A) := fun I hI =>
    mem_nonZeroDivisors_of_ne_zero hI
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  have hI0 : (I : Ideal A) ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
  by_cases hex : ∃ P₀ : Ideal A, P₀.IsMaximal ∧ P₀ ≠ ⊥
  swap
  · push_neg at hex
    have htop : (I : Ideal A) = ⊤ := by
      by_contra h
      obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ h
      exact hI0 (le_bot_iff.mp (hex M hM ▸ hIM))
    refine ⟨1, ?_⟩
    have : I = 1 := Subtype.ext (by rw [htop]; exact Ideal.one_eq_top.symm)
    rw [this, map_one, one_pow]
  obtain ⟨P₀, hP₀, hP₀ne⟩ := hex
  let H : Subgroup (ClassGroup A) := (powMonoidHom N : ClassGroup A →* ClassGroup A).range
  let π : ClassGroup A →* ClassGroup A ⧸ H := QuotientGroup.mk' H
  have hπ : ∀ d : ClassGroup A, π (d ^ N) = 1 := fun d =>
    (QuotientGroup.eq_one_iff _).mpr ⟨d, rfl⟩
  let γ : ClassGroup A := ClassGroup.mk0 ⟨P₀, nz P₀ hP₀ne⟩
  have hbot : ¬ (⊥ : Ideal A).IsMaximal := fun h =>
    hP₀ne (h.eq_of_le hP₀.ne_top bot_le).symm
  have hjac : ∀ x : A, x ≠ 0 → ∃ Q : Ideal A, Q.IsMaximal ∧ x ∉ Q := by
    intro x hx
    haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
    have hj : (⊥ : Ideal A).jacobson = ⊥ :=
      IsJacobsonRing.out' _ (Ideal.isPrime_bot).isRadical
    by_contra hne
    push_neg at hne
    apply hx
    have : x ∈ (⊥ : Ideal A).jacobson := by
      rw [Ideal.jacobson]
      exact Submodule.mem_sInf.mpr fun J hJ => hne J hJ.2
    rw [hj] at this
    exact (Submodule.mem_bot A).mp this
  have hmaxcls : ∀ (P : Ideal A) (hP : P.IsMaximal) (hPne : P ≠ ⊥),
      π (ClassGroup.mk0 ⟨P, nz P hPne⟩) = π γ := by
    intro P hP hPne
    obtain ⟨a₀, ha₀, H0⟩ := hyp P₀ hP₀ (nz P₀ hP₀ne)
    obtain ⟨a₁, ha₁, H1⟩ := hyp P hP (nz P hPne)
    obtain ⟨Q, hQ, hQa⟩ := hjac (a₀ * a₁) (mul_ne_zero ha₀ ha₁)
    have hQne : Q ≠ ⊥ := by rintro rfl; exact hbot hQ
    obtain ⟨d, hd⟩ := H0 Q hQ (fun h => hQa (Q.mul_mem_right _ h)) (nz Q hQne)
    obtain ⟨e, he⟩ := H1 Q hQ (fun h => hQa (Q.mul_mem_left _ h)) (nz Q hQne)
    have h1 := congrArg π hd
    have h2 := congrArg π he
    rw [map_mul, hπ, mul_one] at h1 h2
    rw [← h2, h1]
  have hall : ∀ J : Ideal A, ∀ hJ : J ∈ nonZeroDivisors (Ideal A),
      π (ClassGroup.mk0 ⟨J, hJ⟩) = π γ ^ Module.finrank k (A ⧸ J) := by
    intro J
    refine UniqueFactorizationMonoid.induction_on_prime (P := fun J : Ideal A => ∀ hJ : J ∈ nonZeroDivisors (Ideal A),
      π (ClassGroup.mk0 ⟨J, hJ⟩) = π γ ^ Module.finrank k (A ⧸ J)) J ?_ ?_ ?_
    · intro h; exact absurd rfl (nonZeroDivisors.ne_zero h)
    · intro x hx h
      have hx' : x = ⊤ := Ideal.isUnit_iff.mp hx
      subst hx'
      have e1 : (⟨⊤, h⟩ : nonZeroDivisors (Ideal A)) = 1 := Subtype.ext Ideal.one_eq_top.symm
      haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      rw [e1, map_one, map_one, Module.finrank_zero_of_subsingleton, pow_zero]
    · intro a p ha hp ih h
      have hpne : p ≠ ⊥ := hp.ne_zero
      have hpmax : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hpne
      have e1 : (⟨p * a, h⟩ : nonZeroDivisors (Ideal A)) = ⟨p, nz p hpne⟩ * ⟨a, nz a ha⟩ := rfl
      rw [e1, map_mul, map_mul, hmaxcls p hpmax hpne, ih (nz a ha), hadd p a hpne ha,
        (hmax p hpmax).1, pow_add, pow_one]
  have hγN : π γ ^ N = 1 := by rw [← map_pow]; exact hπ γ
  have hspan : Ideal.span {f} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hf0
  have hγ1 : π γ = 1 := by
    have e := hall _ (nz _ hspan)
    have e0 : ClassGroup.mk0 (⟨Ideal.span {f}, nz _ hspan⟩ : nonZeroDivisors (Ideal A)) = 1 :=
      (ClassGroup.mk0_eq_one_iff _).mpr ⟨⟨f, rfl⟩⟩
    rw [e0, map_one] at e
    calc π γ = π γ ^ (1 % N) := by rw [← pow_eq_pow_mod 1 hγN, pow_one]
      _ = π γ ^ (Module.finrank k (A ⧸ Ideal.span {f}) % N) := by rw [hfm]
      _ = 1 := by rw [← pow_eq_pow_mod _ hγN, ← e]
  have hc := hall I.1 I.2
  rw [hγ1, one_pow] at hc
  have hmem : ClassGroup.mk0 I ∈ H := (QuotientGroup.eq_one_iff _).mp hc
  obtain ⟨d, hd⟩ := hmem
  exact ⟨d, hd.symm⟩

end GlobalTheory
