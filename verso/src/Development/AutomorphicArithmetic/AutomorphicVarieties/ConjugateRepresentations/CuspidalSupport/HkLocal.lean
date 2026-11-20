import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

/- English proof (translation)
Introduce `hSum hMat E _ _ w r s ϖ hϖ hu _ j Φ hΦ`. Establish `hπ0 : ((⟨ϖ, hϖ⟩ : Ov E w) : HeightOneSpectrum.adicCompletion E w) ≠ 0`. Introduce `h0`. Establish `h1 : Valued.v ϖ = 0`. Establish `h2 : ϖ = 0` using `h0`.

Rewrite using `[h2, map_zero]`. Rewrite `h1` using `[hu]`. Conclude with `WithZero.coe_ne_zero h1`. Establish `hq : Fintype.card (satakeRes (Ov E w) ⟨ϖ, hϖ⟩) = qV E w`. Establish `key : ∀ z : WithZero (Multiplicative ℤ), z < 1 → z ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))`.

Introduce `z hz`. Proceed by induction on `z using WithZero.recZeroCoe with`. Consider the case `zero => exact zero_le'`. Consider the case `coe a`. Rewrite `hz` using `[← WithZero.coe_one, WithZero.coe_lt_coe]`.

Rewrite using `[WithZero.coe_le_coe]`. Establish `h1 : (Multiplicative.toAdd a : ℤ) < 0` using `hz`. Express the relevant statement in the definitionally equal form `(Multiplicative.toAdd a : ℤ) ≤ -1`. Use linear arithmetic over natural numbers and integers. Establish `hlt : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1`.

Rewrite using `[← WithZero.coe_one, WithZero.coe_lt_coe]`. Express the relevant statement in the definitionally equal form `(-1 : ℤ) < 0`. Use linear arithmetic over natural numbers and integers. Establish `hint` using `Valuation.valuationSubring.integers (Valued.v : Valuation (HeightOneSpectrum.adicCompletion E w) (WithZero (Multiplicative ℤ)))`. Establish `hmax : Ideal.span {(⟨ϖ, hϖ⟩ : HeightOneSpectrum.adicCompletionIntegers E w)} = IsLocalRing.maximalIdeal (HeightOneSpectrum.adicCompletionIntegers E w)`.

Use extensionality with `x`. Rewrite using `[Ideal.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h2` using `hint.le_of_dvd h`.

Conclude with `(Valuation.mem_maximalIdeal_iff (v := Valued.v)).2 (lt_of_le_of_lt (h2.trans_eq hu) hlt)`. Introduce `h`. Establish `h2` using `(Valuation.mem_maximalIdeal_iff (v := Valued.v)).1 h`. Conclude with `hint.dvd_of_le ((key _ h2).trans_eq hu.symm)`. Rewrite using `[Fintype.card_eq_nat_card, ← tjcosets_card_residue w]`.

Use `show Nat.card (↥(HeightOneSpectrum.adicCompletionIntegers E w) ⧸ Ideal.span {(⟨ϖ, hϖ⟩ : HeightOneSpectrum.adicCompletionIntegers E w)}) = _`. Rewrite using `[hmax]`. Both sides reduce to the same expression. Take `⟨T, hT⟩ : ∃ T : Finset (Fin r) → Finset (Fin s) → ℂ, ∀ A B, T A B = ∑ c₁ : satakePairs A → satakeRes (Ov E w) ⟨ϖ, hϖ⟩, ∑ c₂ : satakePairs B → satakeRes (Ov E w) ⟨ϖ, hϖ⟩, Φ (blk (satakeGL (Ov E w) hπ0 A (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₁ p))) (satakeGL (Ov E w) hπ0 B (fun p …` from `⟨_, fun _ _ => rfl⟩`. Take `⟨κ, hκ⟩ : ∃ κ : Finset (Fin r) × Finset (Fin s) → Fin (r + 1) × Fin (s + 1), ∀ AB, κ AB = (⟨AB.1.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ AB.1)⟩, ⟨AB.2.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ AB.2)⟩)` from `⟨_, fun _ => rfl⟩`.

Establish `hS : ∀ S : Finset (Fin (r + s)), ∑ c : satakePairs S → satakeRes (Ov E w) ⟨ϖ, hϖ⟩, Φ (satakeGL (Ov E w) hπ0 S (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c p))) = (qV E w : ℂ) ^ ((sub1 S).card * (s - (sub2 S).card)) * T (sub1 S) (sub2 S)`. Introduce `S`. Rewrite using `[hT]`. Establish `h` using `hSum r s (satakeRes (Ov E w) ⟨ϖ, hϖ⟩) S (fun c₁ c₂ => Φ (blk (satakeGL (Ov E w) hπ0 (sub1 S) (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₁ p))) (satakeGL (Ov E w) hπ0 (sub2 S) (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₂ p)))))`. Rewrite `h` using `[hq]`.

Rewrite using `[← h]`. Use `Finset.sum_congr rfl (fun c _ => ?_)` and prove the remaining obligations. Take `⟨X, hX⟩` from `hMat _ (Ov E w) r s _ hπ0 S (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c p))`. Rewrite using `[hX, hΦ]`. Both sides reduce to the same expression.

Establish `hcard : ∀ S : Finset (Fin (r + s)), S.card = (sub1 S).card + (sub2 S).card`. Introduce `S`. Combine the equalities or inequalities in the displayed calculation. Set `e : Finset (Fin (r + s)) ≃ Finset (Fin r) × Finset (Fin s)` to `{ toFun := fun S => (sub1 S, sub2 S) invFun := fun AB => AB.1.map (Fin.castAddEmb s) ∪ AB.2.map (Fin.natAddEmb r) left_inv := by`. Introduce `S`.

Use extensionality with `x`. Apply the tactic sequence `refine Fin.addCases (fun i => ?_) (fun i => ?_) x <;> simp [sub1, sub2] <;>`. Apply the tactic sequence `intro y hy h <;> rw [← h] <;> exact hy`. Use `right_inv := by`. Introduce and unpack `⟨A, B⟩`.

Apply the tactic sequence `ext i <;> simp [sub1, sub2] <;> intro y _ h <;> exfalso <;> rw [Fin.ext_iff] at h <;>`. Apply the tactic sequence `simp at h <;> have := i.isLt <;> have := y.isLt <;> omega }`. Establish `hsubj : ∀ F : Finset (Fin (r + s)) → ℂ, ∑ S : {S : Finset (Fin (r + s)) // S.card = j}, F S.1 = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin (r + s)) => S.card = j), F S` using `fun F => (Finset.sum_subtype _ (fun S => by simp) F).symm`. Establish `hG : ∑ i : SatakeIdx (n` using `r + s) w hϖ j, Φ (satakeB w hϖ hu i) = ∑ AB, coef (qV E w) r s j (κ AB) * T AB.1 AB.2 := by`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_filter]`. Simplify using `only [hS]`. Use `_ = ∑ S, coef (qV E w) r s j (κ (e S)) * T (e S).1 (e S).2 := by`. Use `Finset.sum_congr rfl (fun S _ => ?_)` and prove the remaining obligations. Simplify using `only [e, Equiv.coe_fn_mk, hκ, coef, hcard S]`.

Apply the tactic sequence `split_ifs <;> simp`. Use `_ = ∑ AB, coef (qV E w) r s j (κ AB) * T AB.1 AB.2 := Fintype.sum_equiv e _ _ (fun _ => rfl)`. Establish `hR : ∀ a b : ℕ, ∑ i₁ : SatakeIdx (n` using `r) w hϖ a, ∑ i₂ : SatakeIdx (n := s) w hϖ b, Φ (blk (satakeB w hϖ hu i₁) (satakeB w hϖ hu i₂)) = ∑ AB ∈ (Finset.univ.filter (fun A : Finset (Fin r) => A.card = a)) ×ˢ (Finset.univ.filter (fun B : Finset (Fin s) => B.card = b)), T AB.1 AB.2 := by`. Introduce `a b`. Rewrite using `[Finset.sum_product]`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl (fun A _ => ?_)` and prove the remaining obligations. Simplify using `only [hT]`. Use `(Finset.sum_congr rfl (fun c₁ _ => Fintype.sum_sigma _)).trans ?_` and prove the remaining obligations. Conclude with `Finset.sum_comm`.

Use `_ = _ := by`. Rewrite using `[← Finset.sum_subtype (Finset.univ.filter (fun A : Finset (Fin r) => A.card = a)) (by simp) (fun A => ∑ B : {B : Finset (Fin s) // B.card = b}, T A B.1)]`. Use `Finset.sum_congr rfl (fun A _ => ?_)` and prove the remaining obligations. Conclude with `(Finset.sum_subtype _ (by simp) _).symm`. Rewrite using `[hG]`.

Simplify using `only [hR]`. Rewrite using `[← Finset.sum_fiberwise Finset.univ κ]`. Use `Finset.sum_congr rfl (fun p _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Establish `hfib : Finset.univ.filter (fun AB => κ AB = p) = (Finset.univ.filter (fun A : Finset (Fin r) => A.card = (p.1 : ℕ))) ×ˢ (Finset.univ.filter (fun B : Finset (Fin s) => B.card = (p.2 : ℕ)))`.

Use extensionality with `⟨A, B⟩`. Simplify using `[hκ, Prod.ext_iff, Fin.ext_iff]`. Rewrite using `[hfib]`. Use `Finset.sum_congr rfl (fun AB hAB => ?_)` and prove the remaining obligations. Establish `hp : κ AB = p`.

Simplify using `only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hAB`. Rewrite using `[hκ]`. Apply the tactic sequence `ext <;> simp [hAB]`. Rewrite using `[hp]`.
-/
theorem UpperTheory.V.Cj.S.hkLocal :
    UpperTheory.V.Cj.S.SumInner → UpperTheory.V.Cj.S.MatBlock → UpperTheory.V.Cj.S.HkLocal := by
  intro hSum hMat E _ _ w r s ϖ hϖ hu _ j Φ hΦ
  have hπ0 : ((⟨ϖ, hϖ⟩ : Ov E w) : HeightOneSpectrum.adicCompletion E w) ≠ 0 := by
    intro h0
    have h1 : Valued.v ϖ = 0 := by
      have h2 : ϖ = 0 := h0
      rw [h2, map_zero]
    rw [hu] at h1
    exact WithZero.coe_ne_zero h1
  have hq : Fintype.card (satakeRes (Ov E w) ⟨ϖ, hϖ⟩) = qV E w := by
    have key : ∀ z : WithZero (Multiplicative ℤ), z < 1 → z ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      intro z hz
      induction z using WithZero.recZeroCoe with
      | zero => exact zero_le'
      | coe a =>
        rw [← WithZero.coe_one, WithZero.coe_lt_coe] at hz
        rw [WithZero.coe_le_coe]
        have h1 : (Multiplicative.toAdd a : ℤ) < 0 := hz
        change (Multiplicative.toAdd a : ℤ) ≤ -1
        omega
    have hlt : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
      rw [← WithZero.coe_one, WithZero.coe_lt_coe]
      change (-1 : ℤ) < 0
      omega
    have hint := Valuation.valuationSubring.integers
      (Valued.v : Valuation (HeightOneSpectrum.adicCompletion E w) (WithZero (Multiplicative ℤ)))
    have hmax : Ideal.span {(⟨ϖ, hϖ⟩ : HeightOneSpectrum.adicCompletionIntegers E w)} =
        IsLocalRing.maximalIdeal (HeightOneSpectrum.adicCompletionIntegers E w) := by
      ext x
      rw [Ideal.mem_span_singleton]
      constructor
      · intro h
        have h2 := hint.le_of_dvd h
        exact (Valuation.mem_maximalIdeal_iff (v := Valued.v)).2 (lt_of_le_of_lt (h2.trans_eq hu) hlt)
      · intro h
        have h2 := (Valuation.mem_maximalIdeal_iff (v := Valued.v)).1 h
        exact hint.dvd_of_le ((key _ h2).trans_eq hu.symm)
    rw [Fintype.card_eq_nat_card, ← tjcosets_card_residue w]
    show Nat.card (↥(HeightOneSpectrum.adicCompletionIntegers E w) ⧸
      Ideal.span {(⟨ϖ, hϖ⟩ : HeightOneSpectrum.adicCompletionIntegers E w)}) = _
    rw [hmax]
    rfl
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin r) → Finset (Fin s) → ℂ, ∀ A B, T A B =
      ∑ c₁ : satakePairs A → satakeRes (Ov E w) ⟨ϖ, hϖ⟩, ∑ c₂ : satakePairs B → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
        Φ (blk (satakeGL (Ov E w) hπ0 A (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₁ p)))
          (satakeGL (Ov E w) hπ0 B (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₂ p)))) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : Finset (Fin r) × Finset (Fin s) → Fin (r + 1) × Fin (s + 1),
      ∀ AB, κ AB = (⟨AB.1.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ AB.1)⟩,
        ⟨AB.2.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ AB.2)⟩) :=
    ⟨_, fun _ => rfl⟩
  have hS : ∀ S : Finset (Fin (r + s)),
      ∑ c : satakePairs S → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
        Φ (satakeGL (Ov E w) hπ0 S (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c p))) =
      (qV E w : ℂ) ^ ((sub1 S).card * (s - (sub2 S).card)) * T (sub1 S) (sub2 S) := by
    intro S
    rw [hT]
    have h := hSum r s (satakeRes (Ov E w) ⟨ϖ, hϖ⟩) S (fun c₁ c₂ =>
      Φ (blk (satakeGL (Ov E w) hπ0 (sub1 S) (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₁ p)))
        (satakeGL (Ov E w) hπ0 (sub2 S) (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₂ p)))))
    rw [hq] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    obtain ⟨X, hX⟩ := hMat _ (Ov E w) r s _ hπ0 S (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c p))
    rw [hX, hΦ]
    rfl
  have hcard : ∀ S : Finset (Fin (r + s)), S.card = (sub1 S).card + (sub2 S).card := by
    intro S
    calc S.card = ∑ i : Fin (r + s), if i ∈ S then 1 else 0 := by simp [Finset.sum_boole]
      _ = _ := Fin.sum_univ_add _
      _ = _ := by simp [sub1, sub2, Finset.sum_boole]
  let e : Finset (Fin (r + s)) ≃ Finset (Fin r) × Finset (Fin s) :=
    { toFun := fun S => (sub1 S, sub2 S)
      invFun := fun AB => AB.1.map (Fin.castAddEmb s) ∪ AB.2.map (Fin.natAddEmb r)
      left_inv := by
        intro S
        ext x
        refine Fin.addCases (fun i => ?_) (fun i => ?_) x <;> simp [sub1, sub2] <;>
          intro y hy h <;> rw [← h] <;> exact hy
      right_inv := by
        rintro ⟨A, B⟩
        ext i <;> simp [sub1, sub2] <;> intro y _ h <;> exfalso <;> rw [Fin.ext_iff] at h <;>
          simp at h <;> have := i.isLt <;> have := y.isLt <;> omega }
  have hsubj : ∀ F : Finset (Fin (r + s)) → ℂ,
      ∑ S : {S : Finset (Fin (r + s)) // S.card = j}, F S.1 =
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin (r + s)) => S.card = j), F S :=
    fun F => (Finset.sum_subtype _ (fun S => by simp) F).symm
  have hG : ∑ i : SatakeIdx (n := r + s) w hϖ j, Φ (satakeB w hϖ hu i) =
      ∑ AB, coef (qV E w) r s j (κ AB) * T AB.1 AB.2 := by
    calc ∑ i : SatakeIdx (n := r + s) w hϖ j, Φ (satakeB w hϖ hu i)
        = ∑ S : {S : Finset (Fin (r + s)) // S.card = j},
            ∑ c : satakePairs S.1 → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
              Φ (satakeGL (Ov E w) hπ0 S.1 (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c p))) :=
          Fintype.sum_sigma (fun i => Φ (satakeB w hϖ hu i))
      _ = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin (r + s)) => S.card = j),
            ∑ c : satakePairs S → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
              Φ (satakeGL (Ov E w) hπ0 S (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c p))) :=
          hsubj (fun S => ∑ c : satakePairs S → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
              Φ (satakeGL (Ov E w) hπ0 S (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c p))))
      _ = ∑ S : Finset (Fin (r + s)), if S.card = j then
            (qV E w : ℂ) ^ ((sub1 S).card * (s - (sub2 S).card)) * T (sub1 S) (sub2 S) else 0 := by
          rw [Finset.sum_filter]
          simp only [hS]
      _ = ∑ S, coef (qV E w) r s j (κ (e S)) * T (e S).1 (e S).2 := by
          refine Finset.sum_congr rfl (fun S _ => ?_)
          simp only [e, Equiv.coe_fn_mk, hκ, coef, hcard S]
          split_ifs <;> simp
      _ = ∑ AB, coef (qV E w) r s j (κ AB) * T AB.1 AB.2 :=
          Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hR : ∀ a b : ℕ, ∑ i₁ : SatakeIdx (n := r) w hϖ a, ∑ i₂ : SatakeIdx (n := s) w hϖ b,
      Φ (blk (satakeB w hϖ hu i₁) (satakeB w hϖ hu i₂)) =
      ∑ AB ∈ (Finset.univ.filter (fun A : Finset (Fin r) => A.card = a)) ×ˢ
        (Finset.univ.filter (fun B : Finset (Fin s) => B.card = b)), T AB.1 AB.2 := by
    intro a b
    rw [Finset.sum_product]
    calc _ = ∑ A : {A : Finset (Fin r) // A.card = a}, ∑ c₁ : satakePairs A.1 → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
            ∑ i₂ : SatakeIdx (n := s) w hϖ b,
              Φ (blk (satakeGL (Ov E w) hπ0 A.1 (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₁ p)))
                (satakeB w hϖ hu i₂)) :=
          Fintype.sum_sigma (fun i₁ => ∑ i₂ : SatakeIdx (n := s) w hϖ b,
            Φ (blk (satakeB w hϖ hu i₁) (satakeB w hϖ hu i₂)))
      _ = ∑ A : {A : Finset (Fin r) // A.card = a}, ∑ B : {B : Finset (Fin s) // B.card = b}, T A.1 B.1 := by
          refine Finset.sum_congr rfl (fun A _ => ?_)
          simp only [hT]
          refine (Finset.sum_congr rfl (fun c₁ _ => Fintype.sum_sigma _)).trans ?_
          exact Finset.sum_comm
      _ = _ := by
          rw [← Finset.sum_subtype (Finset.univ.filter (fun A : Finset (Fin r) => A.card = a)) (by simp)
            (fun A => ∑ B : {B : Finset (Fin s) // B.card = b}, T A B.1)]
          refine Finset.sum_congr rfl (fun A _ => ?_)
          exact (Finset.sum_subtype _ (by simp) _).symm
  rw [hG]
  simp only [hR]
  rw [← Finset.sum_fiberwise Finset.univ κ]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.mul_sum]
  have hfib : Finset.univ.filter (fun AB => κ AB = p) =
      (Finset.univ.filter (fun A : Finset (Fin r) => A.card = (p.1 : ℕ))) ×ˢ
        (Finset.univ.filter (fun B : Finset (Fin s) => B.card = (p.2 : ℕ))) := by
    ext ⟨A, B⟩
    simp [hκ, Prod.ext_iff, Fin.ext_iff]
  rw [hfib]
  refine Finset.sum_congr rfl (fun AB hAB => ?_)
  have hp : κ AB = p := by
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hAB
    rw [hκ]
    ext <;> simp [hAB]
  rw [hp]
