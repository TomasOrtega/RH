import Mathlib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HopfFrob

/- English proof (translation)
Use `haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance`. Rewrite `hf` using `[← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]`. Use `push_neg at hf`. Take `⟨P, hP, hfP⟩` from `hf`. Use `haveI : P.IsPrime := hP`.

Use `haveI : P.IsMaximal := IsArtinianRing.isMaximal_of_isPrime P`. Use `letI : Field (A ⧸ P) := Ideal.Quotient.field P`. Establish `hbij : Function.Bijective (algebraMap k (A ⧸ P))` using `IsAlgClosed.algebraMap_bijective_of_isIntegral`. Set `e : k ≃ₐ[k] (A ⧸ P)` to `AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ P)) hbij`. Use `⟨(e.symm : (A ⧸ P) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k P), ?_⟩` and prove the remaining obligations.

Introduce `h`. Apply `hfP` to reduce the goal to its premises. Establish `h' : e.symm (Ideal.Quotient.mk P f) = 0` using `h`. Establish `h2 : Ideal.Quotient.mk P f = 0`. Simplify using `using h'`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp h2`.
-/
theorem exists_algHom_ne_zero_of_not_isNilpotent
    {k : Type} [Field k] [IsAlgClosed k] {A : Type} [CommRing A] [Algebra k A]
    [Module.Finite k A] {f : A} (hf : ¬ IsNilpotent f) :
    ∃ x : A →ₐ[k] k, x f ≠ 0 := by
  haveI : IsArtinianRing A := isArtinian_of_tower k inferInstance
  rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf] at hf
  push_neg at hf
  obtain ⟨P, hP, hfP⟩ := hf
  haveI : P.IsPrime := hP
  haveI : P.IsMaximal := IsArtinianRing.isMaximal_of_isPrime P
  letI : Field (A ⧸ P) := Ideal.Quotient.field P
  have hbij : Function.Bijective (algebraMap k (A ⧸ P)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] (A ⧸ P) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ P)) hbij
  refine ⟨(e.symm : (A ⧸ P) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k P), ?_⟩
  intro h
  apply hfP
  have h' : e.symm (Ideal.Quotient.mk P f) = 0 := h
  have h2 : Ideal.Quotient.mk P f = 0 := by
    simpa using h'
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

/- English proof (translation)
Take `⟨n, hn⟩` from `hf`. Establish `hex : ∃ m : ℕ, f ^ (p ^ m) = 0` using `⟨n, pow_eq_zero_of_le (Nat.lt_pow_self (by omega)).le hn⟩`. Establish `hspec` using `Nat.find_spec hex`. Establish `hpos : Nat.find hex ≠ 0`. Introduce `h0`.

Rewrite `hspec` using `[h0]`. Simplify using `at hspec`. Conclude with `hf0 hspec`. Take `⟨m, hm⟩` from `Nat.exists_eq_succ_of_ne_zero hpos`. Establish `hmem : ∀ j : ℕ, f ^ (p ^ j) ∈ S`.

Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simpa using hfS`. Consider the case `succ j ih`. Use `hS _ ih` as an intermediate fact.

Rewrite `this` using `[← pow_mul, ← pow_succ]`. Then use the resulting hypothesis. Use `⟨f ^ (p ^ m), hmem m, Nat.find_min hex (m := m) (by omega), ?_⟩` and prove the remaining obligations. Rewrite using `[← pow_mul, ← pow_succ]`. Rewrite `hspec` using `[hm]`. Conclude with `hspec`.
-/
theorem exists_pow_eq_zero_of_isNilpotent
    {A : Type} [CommRing A] {p : ℕ} (hp : 2 ≤ p) {S : Set A}
    (hS : ∀ f ∈ S, f ^ p ∈ S) {f : A} (hfS : f ∈ S) (hf0 : f ≠ 0) (hf : IsNilpotent f) :
    ∃ g ∈ S, g ≠ 0 ∧ g ^ p = 0 := by
  classical
  obtain ⟨n, hn⟩ := hf
  have hex : ∃ m : ℕ, f ^ (p ^ m) = 0 :=
    ⟨n, pow_eq_zero_of_le (Nat.lt_pow_self (by omega)).le hn⟩
  have hspec := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hspec
    simp at hspec
    exact hf0 hspec
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hmem : ∀ j : ℕ, f ^ (p ^ j) ∈ S := by
    intro j
    induction j with
    | zero => simpa using hfS
    | succ j ih =>
      have := hS _ ih
      rwa [← pow_mul, ← pow_succ] at this
  refine ⟨f ^ (p ^ m), hmem m, Nat.find_min hex (m := m) (by omega), ?_⟩
  rw [← pow_mul, ← pow_succ]
  rw [hm] at hspec
  exact hspec

/- English proof (translation)
Introduce `k _ _ p _ _ A _ _ _ V hV hVp`. Establish `hp : 2 ≤ p` using `(Fact.out : p.Prime).two_le`. Take `⟨f₀, hf₀V, hf₀⟩` from `(Submodule.ne_bot_iff V).mp hV`. Establish `key : ∀ n : ℕ, ∀ f ∈ V, f ≠ 0 → Module.finrank k (LinearMap.range (LinearMap.mulLeft k f)) = n → ∃ f ∈ V, f ≠ 0 ∧ (f ^ p = 0 ∨ f ^ p = f)`. Introduce `n`.

Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `f hfV hf0 hn`. Distinguish the cases in `hnil : IsNilpotent f`. Take `⟨g, hg, hg0, hgp⟩` from `exists_pow_eq_zero_of_isNilpotent (S := (V : Set A)) hp (fun a ha => hVp a ha) hfV hf0 hnil`.

Conclude with `⟨g, hg, hg0, Or.inl hgp⟩`. Take `⟨x, hx⟩` from `exists_algHom_ne_zero_of_not_isNilpotent (k := k) hnil`. Use `set c : k := (x f)⁻¹ with hc`. Use `set f' : A := c • f with hf'`. Establish `hf'V : f' ∈ V` using `V.smul_mem c hfV`.

Establish `hxf' : x f' = 1`. Simplify using `[hf', hc, hx]`. Establish `hf'0 : f' ≠ 0`. Introduce `h`. Rewrite `hxf'` using `[h]`.

Simplify using `at hxf'`. Use `set g : A := f' ^ p - f' with hg`. Establish `hgV : g ∈ V` using `V.sub_mem (hVp _ hf'V) hf'V`. Distinguish the cases in `hg0 : g = 0`. Conclude with `⟨f', hf'V, hf'0, Or.inr (sub_eq_zero.mp hg0)⟩`.

Establish `hxg : x g = 0`. Simplify using `[hg, hxf']`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq⟩ : ∃ q : A, g = f * q := by`. Take `⟨r, hr⟩ : ∃ r, p = r + 1` from `⟨p - 1, by omega⟩`. Use `⟨c • (f' ^ r - 1), ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `hlt : LinearMap.range (LinearMap.mulLeft k g) < LinearMap.range (LinearMap.mulLeft k f)`. Use `lt_of_le_of_ne ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `⟨q * a, by simp [hq, mul_assoc]⟩`.

Introduce `heq`. Establish `hmem : f ∈ LinearMap.range (LinearMap.mulLeft k g)`. Rewrite using `[heq]`. Conclude with `⟨1, by simp⟩`. Take `⟨a, ha⟩` from `hmem`.

Apply `hx` to reduce the goal to its premises. Establish `: g * a = f` using `by simpa using ha`. Rewrite using `[← this, map_mul, hxg, zero_mul]`. Establish `hrank` using `Submodule.finrank_lt_finrank_of_lt hlt`. Conclude with `ih _ (hn ▸ hrank) g hgV hg0 rfl`.

Conclude with `key _ f₀ hf₀V hf₀ rfl`.
-/
theorem exists_frobenius_fixed_or_killed :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (V : Submodule k A),
    V ≠ ⊥ → (∀ f ∈ V, f ^ p ∈ V) → ∃ f ∈ V, f ≠ 0 ∧ (f ^ p = 0 ∨ f ^ p = f) := by
  intro k _ _ p _ _ A _ _ _ V hV hVp
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨f₀, hf₀V, hf₀⟩ := (Submodule.ne_bot_iff V).mp hV
  have key : ∀ n : ℕ, ∀ f ∈ V, f ≠ 0 →
      Module.finrank k (LinearMap.range (LinearMap.mulLeft k f)) = n →
      ∃ f ∈ V, f ≠ 0 ∧ (f ^ p = 0 ∨ f ^ p = f) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f hfV hf0 hn
      by_cases hnil : IsNilpotent f
      · obtain ⟨g, hg, hg0, hgp⟩ := exists_pow_eq_zero_of_isNilpotent (S := (V : Set A)) hp
          (fun a ha => hVp a ha) hfV hf0 hnil
        exact ⟨g, hg, hg0, Or.inl hgp⟩
      obtain ⟨x, hx⟩ := exists_algHom_ne_zero_of_not_isNilpotent (k := k) hnil
      set c : k := (x f)⁻¹ with hc
      set f' : A := c • f with hf'
      have hf'V : f' ∈ V := V.smul_mem c hfV
      have hxf' : x f' = 1 := by
        simp [hf', hc, hx]
      have hf'0 : f' ≠ 0 := by
        intro h
        rw [h] at hxf'
        simp at hxf'
      set g : A := f' ^ p - f' with hg
      have hgV : g ∈ V := V.sub_mem (hVp _ hf'V) hf'V
      by_cases hg0 : g = 0
      · exact ⟨f', hf'V, hf'0, Or.inr (sub_eq_zero.mp hg0)⟩
      have hxg : x g = 0 := by
        simp [hg, hxf']
      obtain ⟨q, hq⟩ : ∃ q : A, g = f * q := by
        obtain ⟨r, hr⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
        refine ⟨c • (f' ^ r - 1), ?_⟩
        calc g = f' * (f' ^ r - 1) := by rw [hg, hr]; ring
          _ = f * (c • (f' ^ r - 1)) := by rw [mul_smul_comm, hf', smul_mul_assoc]
      have hlt : LinearMap.range (LinearMap.mulLeft k g) <
          LinearMap.range (LinearMap.mulLeft k f) := by
        refine lt_of_le_of_ne ?_ ?_
        · rintro _ ⟨a, rfl⟩
          exact ⟨q * a, by simp [hq, mul_assoc]⟩
        · intro heq
          have hmem : f ∈ LinearMap.range (LinearMap.mulLeft k g) := by
            rw [heq]
            exact ⟨1, by simp⟩
          obtain ⟨a, ha⟩ := hmem
          apply hx
          have : g * a = f := by simpa using ha
          rw [← this, map_mul, hxg, zero_mul]
      have hrank := Submodule.finrank_lt_finrank_of_lt hlt
      exact ih _ (hn ▸ hrank) g hgV hg0 rfl
  exact key _ f₀ hf₀V hf₀ rfl

end GlobalTheory.CompanionTheory.HopfFrob
