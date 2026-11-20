import Mathlib

/- English proof (translation)
Introduce `k inst n Q h0 hmono hunion hprime`. Establish `key : ∀ I : Ideal (MvPolynomial (Fin n) k), Q {c : Fin n → k | ∀ p ∈ I, MvPolynomial.eval c p = 0}`. Introduce `I`. Proceed by induction on `I using IsNoetherian.induction with`. Consider the case `_ I ih`.

Establish `step : ∀ g : MvPolynomial (Fin n) k, g ∉ I → Q {c : Fin n → k | (∀ p ∈ I, MvPolynomial.eval c p = 0) ∧ MvPolynomial.eval c g = 0}`. Introduce `g hg`. Establish `hlt : I < I ⊔ Ideal.span {g}`. Use `lt_of_le_of_ne le_sup_left ?_` and prove the remaining obligations. Introduce `h`.

Apply `hg` to reduce the goal to its premises. Rewrite using `[h]`. Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)`. Use `hmono _ _ ?_ (ih _ hlt)` and prove the remaining obligations. Introduce and unpack `c ⟨hc, hcg⟩`.

Establish `hle : I ⊔ Ideal.span {g} ≤ RingHom.ker (MvPolynomial.eval c)`. Use `sup_le (fun p hp => (RingHom.mem_ker).2 (hc p hp)) ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem]`. Conclude with `(RingHom.mem_ker).2 hcg`. Conclude with `fun p hp => (RingHom.mem_ker).1 (hle hp)`.

Distinguish the cases in `hP : Ideal.IsPrime I`. Take `⟨g, hg, hQ⟩` from `hprime I hP`. Use `hmono _ _ ?_ (hunion _ _ hQ (step g hg))` and prove the remaining obligations. Introduce `c hc`. Distinguish the cases in `hcg : MvPolynomial.eval c g = 0`.

Conclude with `Or.inr ⟨hc, hcg⟩`. Conclude with `Or.inl ⟨hc, hcg⟩`. Break down `Ideal.not_isPrime_iff.1 hP with htop | ⟨x, hx, y, hy, hxy⟩` into its components or cases. Use `hmono _ _ ?_ h0` and prove the remaining obligations. Introduce `c hc`.

Establish `h1` using `hc 1 (htop ▸ Submodule.mem_top)`. Simplify using `at h1`. Use `hmono _ _ ?_ (hunion _ _ (step x hx) (step y hy))` and prove the remaining obligations. Introduce `c hc`. Establish `h1` using `hc _ hxy`.

Rewrite `h1` using `[map_mul]`. Break down `mul_eq_zero.1 h1 with h | h` into its components or cases. Conclude with `Or.inl ⟨hc, h⟩`. Conclude with `Or.inr ⟨hc, h⟩`. Use `hmono _ _ ?_ (key ⊥)` and prove the remaining obligations.

Introduce `c _ p hp`. Rewrite using `[(Ideal.mem_bot).1 hp, map_zero]`.
-/
theorem UpperTheory.Reformulated.B.ZariskiNoetherianInduction.noetherian_induction_zariski :
    ∀ (k : Type) [inst : Field k] (n : ℕ) (Q : Set (Fin n → k) → Prop),
    Q ∅ →
      (∀ (s t : Set (Fin n → k)), s ⊆ t → Q t → Q s) →
        (∀ (s t : Set (Fin n → k)), Q s → Q t → Q (s ∪ t)) →
          (∀ (I : Ideal (MvPolynomial (Fin n) k)),
              I.IsPrime →
                ∃ g ∉ I,
                  Q
                    {c : Fin n → k |
                      (∀ p ∈ I, (MvPolynomial.eval c : MvPolynomial (Fin n) k → k) p = (0 : k)) ∧
                        (MvPolynomial.eval c : MvPolynomial (Fin n) k → k) g ≠ (0 : k)}) →
            Q Set.univ := by
  intro k inst n Q h0 hmono hunion hprime
  have key : ∀ I : Ideal (MvPolynomial (Fin n) k),
      Q {c : Fin n → k | ∀ p ∈ I, MvPolynomial.eval c p = 0} := by
    intro I
    induction I using IsNoetherian.induction with
    | _ I ih =>
      have step : ∀ g : MvPolynomial (Fin n) k, g ∉ I →
          Q {c : Fin n → k | (∀ p ∈ I, MvPolynomial.eval c p = 0) ∧
            MvPolynomial.eval c g = 0} := by
        intro g hg
        have hlt : I < I ⊔ Ideal.span {g} := by
          refine lt_of_le_of_ne le_sup_left ?_
          intro h
          apply hg
          rw [h]
          exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)
        refine hmono _ _ ?_ (ih _ hlt)
        rintro c ⟨hc, hcg⟩
        have hle : I ⊔ Ideal.span {g} ≤ RingHom.ker (MvPolynomial.eval c) := by
          refine sup_le (fun p hp => (RingHom.mem_ker).2 (hc p hp)) ?_
          rw [Ideal.span_singleton_le_iff_mem]
          exact (RingHom.mem_ker).2 hcg
        exact fun p hp => (RingHom.mem_ker).1 (hle hp)
      by_cases hP : Ideal.IsPrime I
      · obtain ⟨g, hg, hQ⟩ := hprime I hP
        refine hmono _ _ ?_ (hunion _ _ hQ (step g hg))
        intro c hc
        by_cases hcg : MvPolynomial.eval c g = 0
        · exact Or.inr ⟨hc, hcg⟩
        · exact Or.inl ⟨hc, hcg⟩
      · rcases Ideal.not_isPrime_iff.1 hP with htop | ⟨x, hx, y, hy, hxy⟩
        · refine hmono _ _ ?_ h0
          intro c hc
          have h1 := hc 1 (htop ▸ Submodule.mem_top)
          simp at h1
        · refine hmono _ _ ?_ (hunion _ _ (step x hx) (step y hy))
          intro c hc
          have h1 := hc _ hxy
          rw [map_mul] at h1
          rcases mul_eq_zero.1 h1 with h | h
          · exact Or.inl ⟨hc, h⟩
          · exact Or.inr ⟨hc, h⟩
  refine hmono _ _ ?_ (key ⊥)
  intro c _ p hp
  rw [(Ideal.mem_bot).1 hp, map_zero]
