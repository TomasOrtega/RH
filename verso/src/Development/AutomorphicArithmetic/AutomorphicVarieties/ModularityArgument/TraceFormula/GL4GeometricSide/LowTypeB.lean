import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.LowTypeA
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTensorGK
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTensorGl
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PLieInv

noncomputable section

open Finset PositivityTheory.RgBcC.RealD PositivityTheory.Rg.Cz Formalism.REAL

namespace UpperTheory.V.Z.GSp4Splitting.Low

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

/- English proof (translation)
Rewrite using `[Finset.sum_apply, card_filter]`. Use `push_cast`. Conclude with `sum_congr rfl fun p _ => by simp only [ev, eq_comm]`.
-/
theorem sum_ev {P : Type} (S : Finset P) (I : P → Fin n) (a : Fin n) :
    (∑ p ∈ S, ev (I p)) a = ((S.filter fun p => I p = a).card : ℝ) := by
  rw [Finset.sum_apply, card_filter]
  push_cast
  exact sum_congr rfl fun p _ => by simp only [ev, eq_comm]

/- English proof (translation)
Set `h : (P → Fin n) → ℤ` to `fun I => ∑ p ∈ S₁, ((I p : ℕ) : ℤ) - ∑ p ∈ S₂, ((I p : ℕ) : ℤ)`. Establish `hne : (univ.filter fun I => ζ I ≠ 0).Nonempty`. Take `⟨I, hI⟩` from `Function.ne_iff.1 h0`. Conclude with `⟨I, mem_filter.2 ⟨mem_univ _, hI⟩⟩`. Take `⟨I, hI, hmax⟩` from `exists_max_image _ h hne`.

Establish `van : ∀ J, h I < h J → ζ J = 0` using `fun J hJ => by`. Assume the negation of the conclusion as `hz`. Conclude with `absurd (hmax J (mem_filter.2 ⟨mem_univ _, hz⟩)) (not_le.2 hJ)`. Establish `hin : ∀ (S : Finset P) p v, p ∈ S → ∑ q ∈ S, ((Function.update I p v q : ℕ) : ℤ) = ∑ q ∈ S, ((I q : ℕ) : ℤ) + (v : ℕ) - (I p : ℕ)` using `fun S p v hp => by`. Rewrite using `[← add_sum_erase S _ hp, ← add_sum_erase S (fun q => ((I q : ℕ) : ℤ)) hp, Function.update_self, sum_congr rfl fun q hq => by rw [Function.update_of_ne (ne_of_mem_erase hq)]]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hout : ∀ (S : Finset P) p v, p ∉ S → ∑ q ∈ S, ((Function.update I p v q : ℕ) : ℤ) = ∑ q ∈ S, ((I q : ℕ) : ℤ)` using `fun S p v hp => sum_congr rfl fun q hq => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hq hp)]`. Use `⟨I, (mem_filter.1 hI).2, fun a => ?_, fun a b hab _ => ?_⟩` and prove the remaining obligations. Establish `e : ∀ S : Finset P, (∑ p ∈ S, if I p = a then ζ (Function.update I p a) else 0) = (((S.filter fun p => I p = a).card : ℝ) : ℂ) • ζ I` using `fun S => by`. Rewrite using `[← sum_filter, sum_congr rfl (g := fun _ => ζ I) fun p hp => by`.

Rewrite using `[← (mem_filter.1 hp).2, Function.update_eq_self], sum_const, Complex.ofReal_natCast, Nat.cast_smul_eq_nsmul]`. Rewrite using `[hK, e, e, Pi.sub_apply, sum_ev, sum_ev, Complex.ofReal_sub, sub_smul]`. Establish `hab' : (a : ℕ) < b` using `hab`. Rewrite using `[hK, sum_eq_zero, sum_eq_zero, sub_self]`. Introduce `p hp split_ifs with e`.

Use `van _ ?_` and prove the remaining obligations. Simplify using `only [h]`. Rewrite using `[hin S₁ p b hp, hout S₂ p b (disjoint_left.1 hS hp), e]`. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression.

Introduce `p hp split_ifs with e`. Use `van _ ?_` and prove the remaining obligations. Simplify using `only [h]`. Rewrite using `[hin S₂ p a hp, hout S₁ p a (disjoint_right.1 hS hp), e]`. Use linear arithmetic over natural numbers and integers.

Both sides reduce to the same expression.
-/
theorem exists_high {P : Type} [Fintype P] [DecidableEq P] (S₁ S₂ : Finset P) (hS : Disjoint S₁ S₂)
    (K : Fin n → Fin n → Module.End ℂ M) (ζ : TV n M P) (h0 : ζ ≠ 0)
    (hK : ∀ a b I, K a b (ζ I) = (∑ p ∈ S₂, if I p = b then ζ (Function.update I p a) else 0) -
      ∑ p ∈ S₁, if I p = a then ζ (Function.update I p b) else 0) :
    ∃ I, ζ I ≠ 0 ∧ KHighest (fun _ => true) K (∑ p ∈ S₂, ev (I p) - ∑ p ∈ S₁, ev (I p)) (ζ I) := by
  classical
  let h : (P → Fin n) → ℤ := fun I => ∑ p ∈ S₁, ((I p : ℕ) : ℤ) - ∑ p ∈ S₂, ((I p : ℕ) : ℤ)
  have hne : (univ.filter fun I => ζ I ≠ 0).Nonempty := by
    obtain ⟨I, hI⟩ := Function.ne_iff.1 h0
    exact ⟨I, mem_filter.2 ⟨mem_univ _, hI⟩⟩
  obtain ⟨I, hI, hmax⟩ := exists_max_image _ h hne
  have van : ∀ J, h I < h J → ζ J = 0 := fun J hJ => by
    by_contra hz
    exact absurd (hmax J (mem_filter.2 ⟨mem_univ _, hz⟩)) (not_le.2 hJ)
  have hin : ∀ (S : Finset P) p v, p ∈ S → ∑ q ∈ S, ((Function.update I p v q : ℕ) : ℤ) =
      ∑ q ∈ S, ((I q : ℕ) : ℤ) + (v : ℕ) - (I p : ℕ) := fun S p v hp => by
    rw [← add_sum_erase S _ hp, ← add_sum_erase S (fun q => ((I q : ℕ) : ℤ)) hp, Function.update_self,
      sum_congr rfl fun q hq => by rw [Function.update_of_ne (ne_of_mem_erase hq)]]
    ring
  have hout : ∀ (S : Finset P) p v, p ∉ S → ∑ q ∈ S, ((Function.update I p v q : ℕ) : ℤ) =
      ∑ q ∈ S, ((I q : ℕ) : ℤ) := fun S p v hp =>
    sum_congr rfl fun q hq => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hq hp)]
  refine ⟨I, (mem_filter.1 hI).2, fun a => ?_, fun a b hab _ => ?_⟩
  · have e : ∀ S : Finset P, (∑ p ∈ S, if I p = a then ζ (Function.update I p a) else 0) =
        (((S.filter fun p => I p = a).card : ℝ) : ℂ) • ζ I := fun S => by
      rw [← sum_filter, sum_congr rfl (g := fun _ => ζ I) fun p hp => by
        rw [← (mem_filter.1 hp).2, Function.update_eq_self], sum_const, Complex.ofReal_natCast, Nat.cast_smul_eq_nsmul]
    rw [hK, e, e, Pi.sub_apply, sum_ev, sum_ev, Complex.ofReal_sub, sub_smul]
  · have hab' : (a : ℕ) < b := hab
    rw [hK, sum_eq_zero, sum_eq_zero, sub_self]
    · intro p hp
      split_ifs with e
      · refine van _ ?_
        simp only [h]
        rw [hin S₁ p b hp, hout S₂ p b (disjoint_left.1 hS hp), e]
        omega
      · rfl
    · intro p hp
      split_ifs with e
      · refine van _ ?_
        simp only [h]
        rw [hin S₂ p a hp, hout S₁ p a (disjoint_right.1 hS hp), e]
        omega
      · rfl

/- English proof (translation)
Establish `e` using `congrFun h I`. Rewrite `e` using `[pm_apply, hI, Pi.neg_apply, eq_neg_iff_add_eq_zero, ← two_smul ℂ]`. Conclude with `(smul_eq_zero.1 e).resolve_left two_ne_zero`.
-/
theorem eq_zero_of_anti {P : Type} (σ : Equiv.Perm P) (f : TV n M P) (h : pm σ f = -f) (I : P → Fin n)
    (hI : I ∘ σ = I) : f I = 0 := by
  have e := congrFun h I
  rw [pm_apply, hI, Pi.neg_apply, eq_neg_iff_add_eq_zero, ← two_smul ℂ] at e
  exact (smul_eq_zero.1 e).resolve_left two_ne_zero

section Alt

variable {Q ι : Type} [Fintype Q] [DecidableEq Q] [DecidableEq ι] {N : ℕ}

/- English proof (translation)
Establish `hs : ∀ p, tl (Equiv.swap k k' p) = tl p` using `fun p => by`. Rewrite using `[Equiv.swap_apply_def]`. Use `split_ifs with h1 h2`. Rewrite using `[h1, ht]`. Rewrite using `[h2, ht]`.

Both sides reduce to the same expression. Simplify using `only [altPair, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul, ← sum_neg_distrib]`. Use `sum_equiv (Equiv.mulLeft (Equiv.swap k k')) (fun σ => ?_) fun σ _ => ?_` and prove the remaining obligations. Simplify using `only [colG, mem_filter, mem_univ, true_and, Equiv.coe_mulLeft, Equiv.Perm.mul_apply, hs]`. Establish `e : (dbl (Equiv.swap k k' * σ) : Equiv.Perm (Q ⊕ (Fin N ⊕ Fin N))) = dbl (Equiv.swap k k') * dbl σ`.

Use extensionality with `x`. Apply the tactic sequence `rcases x with x | x | x <;> rfl`. Simplify using `only [Equiv.coe_mulLeft, e, pm_mul, map_mul, Equiv.Perm.sign_swap hk, Module.End.mul_apply]`. Simplify using the standard rewrite rules.
-/
theorem altPair_swap (tl : Fin N → ι) (k k' : Fin N) (hk : k ≠ k') (ht : tl k = tl k')
    (η : TV n M (Q ⊕ (Fin N ⊕ Fin N))) : pm (dbl (Equiv.swap k k')) (altPair tl η) = -altPair tl η := by
  have hs : ∀ p, tl (Equiv.swap k k' p) = tl p := fun p => by
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, ht]
    · rw [h2, ht]
    · rfl
  simp only [altPair, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul, ← sum_neg_distrib]
  refine sum_equiv (Equiv.mulLeft (Equiv.swap k k')) (fun σ => ?_) fun σ _ => ?_
  · simp only [colG, mem_filter, mem_univ, true_and, Equiv.coe_mulLeft, Equiv.Perm.mul_apply, hs]
  · have e : (dbl (Equiv.swap k k' * σ) : Equiv.Perm (Q ⊕ (Fin N ⊕ Fin N))) = dbl (Equiv.swap k k') * dbl σ := by
      ext x
      rcases x with x | x | x <;> rfl
    simp only [Equiv.coe_mulLeft, e, pm_mul, map_mul, Equiv.Perm.sign_swap hk, Module.End.mul_apply]
    simp

/- English proof (translation)
Simplify using `only [altPair, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul, ← sum_neg_distrib]`. Use `sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Establish `e : Equiv.swap (Sum.inl p) (Sum.inl p') * (dbl σ : Equiv.Perm (Q ⊕ (Fin N ⊕ Fin N))) = dbl σ * Equiv.swap (Sum.inl p) (Sum.inl p')`. Rewrite using `[Equiv.mul_swap_eq_swap_mul]`. Both sides reduce to the same expression.

Rewrite using `[← Module.End.mul_apply, ← pm_mul, e, pm_mul, Module.End.mul_apply, h, map_neg, smul_neg]`.
-/
theorem altPair_col (tl : Fin N → ι) (p p' : Q) (η : TV n M (Q ⊕ (Fin N ⊕ Fin N)))
    (h : pm (Equiv.swap (Sum.inl p) (Sum.inl p')) η = -η) :
    pm (Equiv.swap (Sum.inl p) (Sum.inl p')) (altPair tl η) = -altPair tl η := by
  simp only [altPair, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul, ← sum_neg_distrib]
  refine sum_congr rfl fun σ _ => ?_
  have e : Equiv.swap (Sum.inl p) (Sum.inl p') * (dbl σ : Equiv.Perm (Q ⊕ (Fin N ⊕ Fin N))) =
      dbl σ * Equiv.swap (Sum.inl p) (Sum.inl p') := by
    rw [Equiv.mul_swap_eq_swap_mul]
    rfl
  rw [← Module.End.mul_apply, ← pm_mul, e, pm_mul, Module.End.mul_apply, h, map_neg, smul_neg]

end Alt

/- English proof (translation)
Establish `hm : StrictMono fun i : Fin n => ((univ.filter fun p => A p ∧ b p = i).card : ℤ) + (i : ℕ)`. Introduce `i j hij`. Establish `h1 : (univ.filter fun p => A p ∧ b p = i).card ≤ (univ.filter fun p => A p ∧ b p = j).card`. Establish `ex : ∀ p, ∃ q, b p = i → col q = col p ∧ b q = j` using `fun p => by`. Distinguish the cases in `e : b p = i`.

Take `⟨q, hq⟩` from `hb.2 p j (e ▸ hij)`. Conclude with `⟨q, fun _ => hq⟩`. Conclude with `⟨p, fun e' => absurd e' e⟩`. Use `choose f hf using ex`. Use `card_le_card_of_injOn f (fun p hp => ?_) fun p hp q hq e => ?_` and prove the remaining obligations.

Establish `hp'` using `(mem_filter.1 hp).2`. Conclude with `mem_filter.2 ⟨mem_univ _, hA p _ (hf p hp'.2).1.symm hp'.1, (hf p hp'.2).2⟩`. Establish `hp'` using `(mem_filter.1 hp).2`. Establish `hq'` using `(mem_filter.1 hq).2`. Conclude with `hb.1 p q ((hf p hp'.2).1.symm.trans (e ▸ (hf q hq'.2).1)) (hp'.2.trans hq'.2.symm)`.

Establish `h2 : (i : ℕ) < j` using `hij`. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Use `congrFun ((hg.range_inj hm).1 ?_) i` and prove the remaining obligations. Rewrite using `[← funext hw, ← (w.trans v).surjective.range_comp g]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `[hl]`.
-/
theorem shape_eq {P C : Type} [Fintype P] (col : P → C) (b : P → Fin n) (hb : IsTab col b) (A : P → Prop) [DecidablePred A]
    (hA : ∀ p q, col p = col q → A p → A q) (g : Fin n → ℤ) (hg : StrictMono g) (l : Fin n → ℤ) (v : Equiv.Perm (Fin n))
    (hl : ∀ i, l i = g (v i)) (w : Equiv.Perm (Fin n))
    (hw : ∀ i, l (w i) = ((univ.filter fun p => A p ∧ b p = i).card : ℤ) + (i : ℕ)) (i : Fin n) :
    g i = ((univ.filter fun p => A p ∧ b p = i).card : ℤ) + (i : ℕ) := by
  have hm : StrictMono fun i : Fin n => ((univ.filter fun p => A p ∧ b p = i).card : ℤ) + (i : ℕ) := by
    intro i j hij
    have h1 : (univ.filter fun p => A p ∧ b p = i).card ≤ (univ.filter fun p => A p ∧ b p = j).card := by
      have ex : ∀ p, ∃ q, b p = i → col q = col p ∧ b q = j := fun p => by
        by_cases e : b p = i
        · obtain ⟨q, hq⟩ := hb.2 p j (e ▸ hij)
          exact ⟨q, fun _ => hq⟩
        · exact ⟨p, fun e' => absurd e' e⟩
      choose f hf using ex
      refine card_le_card_of_injOn f (fun p hp => ?_) fun p hp q hq e => ?_
      · have hp' := (mem_filter.1 hp).2
        exact mem_filter.2 ⟨mem_univ _, hA p _ (hf p hp'.2).1.symm hp'.1, (hf p hp'.2).2⟩
      · have hp' := (mem_filter.1 hp).2
        have hq' := (mem_filter.1 hq).2
        exact hb.1 p q ((hf p hp'.2).1.symm.trans (e ▸ (hf q hq'.2).1)) (hp'.2.trans hq'.2.symm)
    have h2 : (i : ℕ) < j := hij
    simp only
    omega
  refine congrFun ((hg.range_inj hm).1 ?_) i
  rw [← funext hw, ← (w.trans v).surjective.range_comp g]
  congr 1
  funext x
  simp [hl]

/- English proof (translation)
Take `⟨q, N, lab, col, b, tl, η, hcl, hb, htl, hsh, hinv, hanti, h0⟩` from `hd`. Establish `hT` using `tensorGK_of tensorGl_holds n M ι Γ bar κ E ρ hK hG _ (lab3 bar lab tl)`. Establish `inv : ∀ γ, actT (lab3 bar lab tl) κ ρ γ (altPair tl η) = altPair tl η` using `fun γ => by`. Simplify using `only [altPair, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul]`. Use `sum_congr rfl fun σ hσ => ?_` and prove the remaining obligations.

Establish `hσ' : ∀ p, tl (σ p) = tl p` using `by simpa only [colG, mem_filter, mem_univ, true_and] using hσ`. Establish `hc` using `hT.2 (dbl σ) (fun p => by`. Break down `p with p | p | p` into its components or cases. Both sides reduce to the same expression. Conclude with `hσ' p`.

Conclude with `congrArg bar (hσ' p)) γ`. Rewrite using `[← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply, hinv]`. Establish `lie` using `lieInv_holds n _ ι Γ bar κ _ _ hK hT.1 0 (altPair tl η) (fun γ => by simp [inv]) τ`. Establish `dis : Disjoint (fib (lab3 bar lab tl) τ) (fib (lab3 bar lab tl) (bar τ))` using `disjoint_left.2 fun p h h' => hK.ne τ ((mem_filter.1 h').2.symm.trans (mem_filter.1 h).2)`. Take `⟨I, hI, hH⟩` from `exists_high _ _ dis (fun a b => E τ a b - E (bar τ) b a) _ h0 fun a c I => by`.

Establish `e` using `congrFun (lie a c) I`. Simplify using `only [Pi.zero_apply, sub_self, Int.cast_zero, zero_smul, ite_self, Pi.sub_apply, tE_apply] at e`. Rewrite using `[LinearMap.sub_apply, ← sub_eq_zero]`. Use `Eq.trans ?_ e` and prove the remaining obligations. Normalize the expressions using the abelian group laws.

Use `⟨_, _, hI, hH, ?_⟩` and prove the remaining obligations. Establish `hIc : ∀ p p', col p = col p' → I (.inl p) = I (.inl p') → p = p'` using `fun p p' hc e => by`. Assume the negation of the conclusion as `hne`. Use `hI (eq_zero_of_anti _ _ (altPair_col tl p p' η (hanti p p' hc hne)) I (funext fun x => ?_))` and prove the remaining obligations. Conclude with `Equiv.apply_swap_eq_self e x`.

Establish `hIp : ∀ k k', tl k = tl k' → I (.inr (.inl k)) = I (.inr (.inl k')) → I (.inr (.inr k)) = I (.inr (.inr k')) → k = k'` using `fun k k' hc e e' => by`. Assume the negation of the conclusion as `hne`. Use `hI (eq_zero_of_anti _ _ (altPair_swap tl k k' hne hc η) I (funext fun x => ?_))` and prove the remaining obligations. Break down `x with x | x | x` into its components or cases. Both sides reduce to the same expression.

Conclude with `Equiv.apply_swap_eq_self (v := fun k => I (.inr (.inl k))) e x`. Conclude with `Equiv.apply_swap_eq_self (v := fun k => I (.inr (.inr k))) e' x`. Establish `hbar : ∀ t t', bar t = bar t' ↔ t = t'` using `fun t t' => ⟨fun h => by rw [← hK.invol t, h, hK.invol], congrArg bar⟩`. Establish `split : ∀ t, ∑ p ∈ fib (lab3 bar lab tl) t, ev (I p) = ∑ p ∈ fib lab t, ev (I (.inl p)) + (∑ k ∈ fib tl t, ev (I (.inr (.inl k))) + ∑ k ∈ fib tl (bar t), ev (I (.inr (.inr k))))` using `fun t => by`. Establish `e : ∀ k, bar (tl k) = t ↔ tl k = bar t` using `fun k => by rw [← hbar (tl k) (bar t), hK.invol]`.

Rewrite using `[fib, fib, fib, fib, sum_filter, sum_filter, sum_filter, sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]`. Conclude with `congrArg₂ _ rfl (congrArg₂ _ rfl (sum_congr rfl fun k _ => if_congr (e k) rfl rfl))`. Establish `sat : ∀ t p p', col p = col p' → p ∈ fib lab t → p' ∈ fib lab t` using `fun t p p' hc h => mem_filter.2 ⟨mem_univ _, (hcl p p' hc).symm.trans (mem_filter.1 h).2⟩`. Establish `c1` using `(cone_cols col b (fun p => I (.inl p)) _ (sat τ) hb hIc).1`. Establish `c2` using `(cone_cols col b (fun p => I (.inl p)) _ (sat (bar τ)) hb hIc).2`.

Establish `c3 : Cone ((fun a : Fin n => ((n : ℝ) - 1) - 2 * (a : ℕ)) - (∑ k ∈ fib tl τ, (ev (I (.inr (.inr k))) - ev (I (.inr (.inl k)))) + ∑ k ∈ fib tl (bar τ), (ev (I (.inr (.inl k))) - ev (I (.inr (.inr k))))))`. Distinguish the cases in `he : fib tl τ = ∅`. Rewrite using `[he, sum_empty, zero_add]`. Conclude with `cone_pairs _ (fun k => (I (.inr (.inl k)), I (.inr (.inr k)))) fun k hk k' hk' e => hIp k k' ((mem_filter.1 hk).2.trans (mem_filter.1 hk').2.symm) (congrArg Prod.fst e) (congrArg Prod.snd e)`. Take `⟨k₀, hk₀⟩` from `nonempty_iff_ne_empty.2 he`.

Establish `he' : fib tl (bar τ) = ∅` using `eq_empty_of_forall_notMem fun k hk => htl k k₀ ((mem_filter.1 hk).2.trans (congrArg bar (mem_filter.1 hk₀).2.symm))`. Rewrite using `[he', sum_empty, add_zero]`. Conclude with `cone_pairs _ (fun k => (I (.inr (.inr k)), I (.inr (.inl k)))) fun k hk k' hk' e => hIp k k' ((mem_filter.1 hk).2.trans (mem_filter.1 hk').2.symm) (congrArg Prod.snd e) (congrArg Prod.fst e)`. Establish `labc : ∀ t p p', col p = col p' → lab p = t → lab p' = t` using `fun t p p' hc h => (hcl p p' hc).symm.trans h`. Establish `s1 : ∀ a, (∑ p ∈ fib lab τ, ev (b p)) a = (s : ℝ) - lam a` using `fun a => by`.

Take `⟨w, hw⟩` from `hsh τ`. Establish `e` using `shape_eq col b hb (fun p => lab p = τ) (labc τ) (fun i => s - lam i + (i : ℕ)) (fun i j hij => by`. Use `hlam hij.le` as an intermediate fact. Establish `: (i : ℕ) < j` using `hij`. Simplify using `only`.

Use the proof step `omega) (fun i => s - l τ i) (Equiv.refl _) (fun i => by simp only [h1, Equiv.refl_apply]; ring) w hw a`. Rewrite using `[sum_ev, fib, filter_filter]`. Conclude with `(add_right_cancel e).symm` after adjusting the coercions. Establish `s2 : ∀ a, (∑ p ∈ fib lab (bar τ), ev (b p).rev) a = (s : ℝ) + lam a` using `fun a => by`. Take `⟨w, hw⟩` from `hsh (bar τ)`.

Establish `e` using `shape_eq col b hb (fun p => lab p = bar τ) (labc _) (fun i => s + lam i.rev + (i : ℕ)) (fun i j hij => by`. Use `hlam (Fin.rev_le_rev.2 hij.le)` as an intermediate fact. Establish `: (i : ℕ) < j` using `hij`. Simplify using `only`. Use the proof step `omega) (fun i => s - l (bar τ) i) Fin.revPerm (fun i => by`.

Use `i.2` as an intermediate fact. Simplify using `only [h2, Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]`. Use the proof step `omega) w hw a.rev`. Rewrite using `[sum_ev, fib, filter_filter]`. Simplify using `only [Fin.rev_rev] at e`.

Simplify using `only [Fin.rev_eq_iff]`. Conclude with `(add_right_cancel e).symm` after adjusting the coercions. Use `(c1.add c2).add c3 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `a`. Simplify using `only [split, hK.invol, sum_sub_distrib, Pi.add_apply, Pi.sub_apply, s1, s2, m0]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem low_abs {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ] (bar : ι → ι)
    (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (E : ι → Fin n → Fin n → Module.End ℂ M) (ρ : Γ → Module.End ℂ M)
    (hK : IsKD bar κ) (hG : IsGK bar κ E ρ) (l : ι → Fin n → ℤ) (s : ℤ) (hd : KTypeData bar κ ρ l s) (τ : ι)
    (lam : Fin n → ℤ) (hlam : Antitone lam) (h1 : ∀ a, l τ a = lam a - (a : ℕ))
    (h2 : ∀ a, l (bar τ) a = -lam a - ((n : ℤ) - 1) + (a : ℕ)) :
    ∃ (ν : Fin n → ℝ) (ψ : M), ψ ≠ 0 ∧ KHighest (fun _ => true) (fun a b => E τ a b - E (bar τ) b a) ν ψ ∧
      Cone (m0 lam - ν) := by
  obtain ⟨q, N, lab, col, b, tl, η, hcl, hb, htl, hsh, hinv, hanti, h0⟩ := hd
  have hT := tensorGK_of tensorGl_holds n M ι Γ bar κ E ρ hK hG _ (lab3 bar lab tl)
  have inv : ∀ γ, actT (lab3 bar lab tl) κ ρ γ (altPair tl η) = altPair tl η := fun γ => by
    simp only [altPair, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul]
    refine sum_congr rfl fun σ hσ => ?_
    have hσ' : ∀ p, tl (σ p) = tl p := by simpa only [colG, mem_filter, mem_univ, true_and] using hσ
    have hc := hT.2 (dbl σ) (fun p => by
      rcases p with p | p | p
      · rfl
      · exact hσ' p
      · exact congrArg bar (hσ' p)) γ
    rw [← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply, hinv]
  have lie := lieInv_holds n _ ι Γ bar κ _ _ hK hT.1 0 (altPair tl η) (fun γ => by simp [inv]) τ
  have dis : Disjoint (fib (lab3 bar lab tl) τ) (fib (lab3 bar lab tl) (bar τ)) :=
    disjoint_left.2 fun p h h' => hK.ne τ ((mem_filter.1 h').2.symm.trans (mem_filter.1 h).2)
  obtain ⟨I, hI, hH⟩ := exists_high _ _ dis (fun a b => E τ a b - E (bar τ) b a) _ h0 fun a c I => by
    have e := congrFun (lie a c) I
    simp only [Pi.zero_apply, sub_self, Int.cast_zero, zero_smul, ite_self, Pi.sub_apply, tE_apply] at e
    rw [LinearMap.sub_apply, ← sub_eq_zero]
    refine Eq.trans ?_ e
    abel
  refine ⟨_, _, hI, hH, ?_⟩
  have hIc : ∀ p p', col p = col p' → I (.inl p) = I (.inl p') → p = p' := fun p p' hc e => by
    by_contra hne
    refine hI (eq_zero_of_anti _ _ (altPair_col tl p p' η (hanti p p' hc hne)) I (funext fun x => ?_))
    exact Equiv.apply_swap_eq_self e x
  have hIp : ∀ k k', tl k = tl k' → I (.inr (.inl k)) = I (.inr (.inl k')) → I (.inr (.inr k)) = I (.inr (.inr k')) →
      k = k' := fun k k' hc e e' => by
    by_contra hne
    refine hI (eq_zero_of_anti _ _ (altPair_swap tl k k' hne hc η) I (funext fun x => ?_))
    rcases x with x | x | x
    · rfl
    · exact Equiv.apply_swap_eq_self (v := fun k => I (.inr (.inl k))) e x
    · exact Equiv.apply_swap_eq_self (v := fun k => I (.inr (.inr k))) e' x
  have hbar : ∀ t t', bar t = bar t' ↔ t = t' := fun t t' =>
    ⟨fun h => by rw [← hK.invol t, h, hK.invol], congrArg bar⟩
  have split : ∀ t, ∑ p ∈ fib (lab3 bar lab tl) t, ev (I p) = ∑ p ∈ fib lab t, ev (I (.inl p)) +
      (∑ k ∈ fib tl t, ev (I (.inr (.inl k))) + ∑ k ∈ fib tl (bar t), ev (I (.inr (.inr k)))) := fun t => by
    have e : ∀ k, bar (tl k) = t ↔ tl k = bar t := fun k => by rw [← hbar (tl k) (bar t), hK.invol]
    rw [fib, fib, fib, fib, sum_filter, sum_filter, sum_filter, sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]
    exact congrArg₂ _ rfl (congrArg₂ _ rfl (sum_congr rfl fun k _ => if_congr (e k) rfl rfl))
  have sat : ∀ t p p', col p = col p' → p ∈ fib lab t → p' ∈ fib lab t := fun t p p' hc h =>
    mem_filter.2 ⟨mem_univ _, (hcl p p' hc).symm.trans (mem_filter.1 h).2⟩
  have c1 := (cone_cols col b (fun p => I (.inl p)) _ (sat τ) hb hIc).1
  have c2 := (cone_cols col b (fun p => I (.inl p)) _ (sat (bar τ)) hb hIc).2
  have c3 : Cone ((fun a : Fin n => ((n : ℝ) - 1) - 2 * (a : ℕ)) -
      (∑ k ∈ fib tl τ, (ev (I (.inr (.inr k))) - ev (I (.inr (.inl k)))) +
        ∑ k ∈ fib tl (bar τ), (ev (I (.inr (.inl k))) - ev (I (.inr (.inr k)))))) := by
    by_cases he : fib tl τ = ∅
    · rw [he, sum_empty, zero_add]
      exact cone_pairs _ (fun k => (I (.inr (.inl k)), I (.inr (.inr k)))) fun k hk k' hk' e =>
        hIp k k' ((mem_filter.1 hk).2.trans (mem_filter.1 hk').2.symm) (congrArg Prod.fst e) (congrArg Prod.snd e)
    · obtain ⟨k₀, hk₀⟩ := nonempty_iff_ne_empty.2 he
      have he' : fib tl (bar τ) = ∅ := eq_empty_of_forall_notMem fun k hk =>
        htl k k₀ ((mem_filter.1 hk).2.trans (congrArg bar (mem_filter.1 hk₀).2.symm))
      rw [he', sum_empty, add_zero]
      exact cone_pairs _ (fun k => (I (.inr (.inr k)), I (.inr (.inl k)))) fun k hk k' hk' e =>
        hIp k k' ((mem_filter.1 hk).2.trans (mem_filter.1 hk').2.symm) (congrArg Prod.snd e) (congrArg Prod.fst e)
  have labc : ∀ t p p', col p = col p' → lab p = t → lab p' = t := fun t p p' hc h => (hcl p p' hc).symm.trans h
  have s1 : ∀ a, (∑ p ∈ fib lab τ, ev (b p)) a = (s : ℝ) - lam a := fun a => by
    obtain ⟨w, hw⟩ := hsh τ
    have e := shape_eq col b hb (fun p => lab p = τ) (labc τ) (fun i => s - lam i + (i : ℕ))
      (fun i j hij => by
        have := hlam hij.le
        have : (i : ℕ) < j := hij
        simp only
        omega) (fun i => s - l τ i) (Equiv.refl _) (fun i => by simp only [h1, Equiv.refl_apply]; ring) w hw a
    rw [sum_ev, fib, filter_filter]
    exact_mod_cast (add_right_cancel e).symm
  have s2 : ∀ a, (∑ p ∈ fib lab (bar τ), ev (b p).rev) a = (s : ℝ) + lam a := fun a => by
    obtain ⟨w, hw⟩ := hsh (bar τ)
    have e := shape_eq col b hb (fun p => lab p = bar τ) (labc _) (fun i => s + lam i.rev + (i : ℕ))
      (fun i j hij => by
        have := hlam (Fin.rev_le_rev.2 hij.le)
        have : (i : ℕ) < j := hij
        simp only
        omega) (fun i => s - l (bar τ) i) Fin.revPerm (fun i => by
          have := i.2
          simp only [h2, Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
          omega) w hw a.rev
    rw [sum_ev, fib, filter_filter]
    simp only [Fin.rev_rev] at e
    simp only [Fin.rev_eq_iff]
    exact_mod_cast (add_right_cancel e).symm
  convert (c1.add c2).add c3 using 1
  funext a
  simp only [split, hK.invol, sum_sub_distrib, Pi.add_apply, Pi.sub_apply, s1, s2, m0]
  ring

end UpperTheory.V.Z.GSp4Splitting.Low
