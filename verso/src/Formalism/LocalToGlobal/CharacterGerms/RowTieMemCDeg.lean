import Formalism.LocalToGlobal.CharacterGerms.IsWHLetterMinorK

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

/- English proof (translation)
Unfold `trueT`. Use `revert g t' s`. Evaluate the decidable proposition.
-/
theorem trueT_iff (g : Fin 2) (t' s : ZMod 2) : ((if g = 0 then t' else t' + 1) = s) ↔ t' = trueT g s := by
  unfold trueT
  revert g t' s
  decide

/- English proof (translation)
Unfold `trueT`. Evaluate the decidable proposition.
-/
theorem trueT_one : ∀ t : ZMod 2, trueT 1 (t + 1) = t := by
  unfold trueT
  decide

/- English proof (translation)
Unfold `RowData.rkF`. Establish `e : (Finset.univ.filter fun c : IIs r tau o => ((X o).G g).ty (Sum.inl c) = s) = Finset.univ.map (Function.Embedding.sigmaMk (β` using `fun t => Fin (r (tau o t))) (trueT g s)) := by`. Use extensionality with `⟨t', c⟩`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.sigmaMk_apply, H.hty]`. Rewrite using `[trueT_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `⟨c, rfl⟩`. Introduce and unpack `⟨c', h⟩`. Conclude with `(congrArg Sigma.fst h).symm`.

Rewrite using `[e, Finset.card_map, Finset.card_univ, Fintype.card_fin]`.
-/
theorem SelfConjugatePlaceSetting.rkF_eq {C : Type} [Field C] {V : VF C} {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
    {Orb : Type} [Fintype Orb] {tau : Orb → ZMod 2 → T} {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C}
    {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
    {X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)} {F : ∀ o, Flag (X o)}
    {gaC : Orb → ZMod 2 → ℕ → ℕ} {N : ℕ} {L : Orb → List (GlobalTheory 2 × ℝ)}
    {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N}
    (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod 2) :
    (X o).rkF g s = r (tau o (trueT g s)) := by
  unfold RowData.rkF
  have e : (Finset.univ.filter fun c : IIs r tau o => ((X o).G g).ty (Sum.inl c) = s) =
      Finset.univ.map (Function.Embedding.sigmaMk (β := fun t => Fin (r (tau o t))) (trueT g s)) := by
    ext ⟨t', c⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.sigmaMk_apply, H.hty]
    rw [trueT_iff]
    constructor
    · rintro rfl
      exact ⟨c, rfl⟩
    · rintro ⟨c', h⟩
      exact (congrArg Sigma.fst h).symm
  rw [e, Finset.card_map, Finset.card_univ, Fintype.card_fin]

open WeightHomogeneousMinors WeightHomogeneousLetters in
/- English proof (translation)
Introduce `C _ V T r cc a Orb _ tau gm J _ X F gaC N L pl H n plc m hm σ c0`. Rewrite using `[← weight_wLet]`. It suffices to establish `hWH : IsWeightedHomogeneous (wLet r n σ c0) (subG r tau gm plc (blkProd X F N L pl)) (a σ c0) from hWH (MvPolynomial.mem_support_iff.1 hm)`. Unfold `subG`. Use `isWH_aeval (w' := fun x => if (⟨tau x.2.1 x.2.2.2.1, x.2.2.2.2⟩ : Σ σ, Fin (r σ)) = ⟨σ, c0⟩ then 1 else 0) _ (fun x => ?_) ?_` and prove the remaining obligations.

Apply `IsWeightedHomogeneous.sum` to reduce the goal to its premises. Introduce `col _`. Establish `h` using `(isWeightedHomogeneous_C (wLet r n σ c0) (gm x.2.1 x.2.2.2.1 col x.2.2.1)).mul (isWeightedHomogeneous_X (R := C) (wLet r n σ c0) (⟨tau x.2.1 x.2.2.2.1, x.2.2.2.2, plc (x.1, col)⟩ : Letter T r n))`. Rewrite `h` using `[zero_add, wLet_mk]`. Conclude with `h`.

Distinguish the cases in `hσ : ∃ o t, tau o t = σ`. Take `⟨o0, t0, rfl⟩` from `hσ`. Establish `keyEq : ∀ o t (c : Fin (r (tau o t))), ((⟨tau o t, c⟩ : Σ σ, Fin (r σ)) = ⟨tau o0 t0, c0⟩) ↔ (o = o0 ∧ t = t0 ∧ (c : ℕ) = c0)`. Introduce `o t c`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h1 : tau o t = tau o0 t0` using `congrArg Sigma.fst h`. Establish `h2` using `H.inj (a₁ := (o, t)) (a₂ := (o0, t0)) h1`. Simplify using `only [Prod.mk.injEq] at h2`. Take `⟨rfl, rfl⟩` from `h2`.

Use `⟨rfl, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_of_heq (Sigma.mk.inj h).2]`. Introduce and unpack `⟨rfl, rfl, hc⟩`. Rewrite using `[Fin.ext hc]`. Establish `hT1 : trueT 1 (t0 + 1) = t0` using `trueT_one t0`.

Establish `hR0 : (X o0).rkF 0 t0 = r (tau o0 t0)` using `H.rkF_eq o0 0 t0`. Establish `hR1 : (X o0).rkF 1 (t0 + 1) = r (tau o0 t0)` using `by rw [H.rkF_eq o0 1 (t0 + 1), hT1]`. Establish `hD : a (tau o0 t0) c0 = ∑ o, (if o = o0 then ∑ i : Fin (L o).length, ((∑ k ∈ Finset.Icc ((c0 : ℕ) + 1) ((X o).rkF 0 t0), (blkAt L o i).wt (X o) 0 t0 k) + ∑ k ∈ Finset.Icc ((c0 : ℕ) + 1) ((X o).rkF 1 (t0 + 1)), (blkAt L o i).wt (X o) 1 (t0 + 1) k) else 0)`. Rewrite using `[Finset.sum_ite_eq', if_pos (Finset.mem_univ _), hR0, hR1, H.tie.1 o0 t0 c0 c0.2]`. Simplify using `only [← Finset.sum_add_distrib]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← H.wt o0 t0 k, ← Fin.sum_univ_fun_getElem]`. Both sides reduce to the same expression. Rewrite using `[hD]`.

Unfold `blkProd`. Use `IsWeightedHomogeneous.prod _ _ _ fun o _ => ?_` and prove the remaining obligations. Distinguish the cases in `ho : o = o0`. Substitute `ho` using the available equality. Rewrite using `[if_pos rfl]`.

Unfold `toAll`. Apply `isWH_rename` to reduce the goal to its premises. Unfold `prodAll`. Use `IsWeightedHomogeneous.prod _ _ _ fun i _ => ?_` and prove the remaining obligations. Apply `isWH_rename` to reduce the goal to its premises.

Use `isWH_congr ?_ (isWH_add (blockPoly_isWeightedHomogeneous' (X o) (F o) (fun _ x => x.2.val) (H.std o) (blkAt L o i) 0 t0 (c0 : ℕ)) (blockPoly_isWeightedHomogeneous' (X o) (F o) (fun _ x => x.2.val) (H.std o) (blkAt L o i) 1 (t0 + 1) (c0 : ℕ)))` and prove the remaining obligations. Introduce and unpack `⟨ρ, gg, tt, cc'⟩`. Simplify using `only [Function.comp_apply, keyEq, wRowG, true_and, H.hty]`. Apply the tactic sequence `fin_cases gg <;> simp`. Rewrite using `[if_neg ho]`.

Unfold `toAll`. Apply `isWH_rename` to reduce the goal to its premises. Use `isWH_of_zero (fun x => ?_) _` and prove the remaining obligations. Take `⟨ρ, gg, tt, cc'⟩` from `x`. Simplify using `only [Function.comp_apply, keyEq]`.

Rewrite using `[if_neg]`. Conclude with `fun hh => ho hh.1`. Use `push Not at hσ`. Rewrite using `[H.tie.2 σ hσ c0 c0.2]`. Use `isWH_of_zero (fun x => ?_) _` and prove the remaining obligations.

Take `⟨ρ, o, g, t, c⟩` from `x`. Use `show (if (⟨tau o t, c⟩ : Σ σ, Fin (r σ)) = ⟨σ, c0⟩ then 1 else 0) = 0`. Rewrite using `[if_neg]`. Conclude with `fun hh => hσ o t (congrArg Sigma.fst hh)`.
-/
theorem isotropic_to_std_subst_degree : IsotropicToStdSubstLineDegree := by
  intro C _ V T r cc a Orb _ tau gm J _ X F gaC N L pl H n plc m hm σ c0
  rw [← weight_wLet]
  suffices hWH : IsWeightedHomogeneous (wLet r n σ c0) (subG r tau gm plc (blkProd X F N L pl)) (a σ c0) from
    hWH (MvPolynomial.mem_support_iff.1 hm)
  unfold subG
  refine isWH_aeval (w' := fun x => if (⟨tau x.2.1 x.2.2.2.1, x.2.2.2.2⟩ : Σ σ, Fin (r σ)) = ⟨σ, c0⟩ then 1 else 0) _
    (fun x => ?_) ?_
  · apply IsWeightedHomogeneous.sum
    intro col _
    have h := (isWeightedHomogeneous_C (wLet r n σ c0) (gm x.2.1 x.2.2.2.1 col x.2.2.1)).mul
      (isWeightedHomogeneous_X (R := C) (wLet r n σ c0)
        (⟨tau x.2.1 x.2.2.2.1, x.2.2.2.2, plc (x.1, col)⟩ : Letter T r n))
    rw [zero_add, wLet_mk] at h
    exact h
  · by_cases hσ : ∃ o t, tau o t = σ
    · obtain ⟨o0, t0, rfl⟩ := hσ
      have keyEq : ∀ o t (c : Fin (r (tau o t))),
          ((⟨tau o t, c⟩ : Σ σ, Fin (r σ)) = ⟨tau o0 t0, c0⟩) ↔ (o = o0 ∧ t = t0 ∧ (c : ℕ) = c0) := by
        intro o t c
        constructor
        · intro h
          have h1 : tau o t = tau o0 t0 := congrArg Sigma.fst h
          have h2 := H.inj (a₁ := (o, t)) (a₂ := (o0, t0)) h1
          simp only [Prod.mk.injEq] at h2
          obtain ⟨rfl, rfl⟩ := h2
          refine ⟨rfl, rfl, ?_⟩
          rw [eq_of_heq (Sigma.mk.inj h).2]
        · rintro ⟨rfl, rfl, hc⟩
          rw [Fin.ext hc]
      have hT1 : trueT 1 (t0 + 1) = t0 := trueT_one t0
      have hR0 : (X o0).rkF 0 t0 = r (tau o0 t0) := H.rkF_eq o0 0 t0
      have hR1 : (X o0).rkF 1 (t0 + 1) = r (tau o0 t0) := by rw [H.rkF_eq o0 1 (t0 + 1), hT1]
      have hD : a (tau o0 t0) c0 = ∑ o, (if o = o0 then ∑ i : Fin (L o).length,
          ((∑ k ∈ Finset.Icc ((c0 : ℕ) + 1) ((X o).rkF 0 t0), (blkAt L o i).wt (X o) 0 t0 k) +
            ∑ k ∈ Finset.Icc ((c0 : ℕ) + 1) ((X o).rkF 1 (t0 + 1)), (blkAt L o i).wt (X o) 1 (t0 + 1) k) else 0) := by
        rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), hR0, hR1, H.tie.1 o0 t0 c0 c0.2]
        simp only [← Finset.sum_add_distrib]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← H.wt o0 t0 k, ← Fin.sum_univ_fun_getElem]
        rfl
      rw [hD]
      unfold blkProd
      refine IsWeightedHomogeneous.prod _ _ _ fun o _ => ?_
      by_cases ho : o = o0
      · subst ho
        rw [if_pos rfl]
        unfold toAll
        apply isWH_rename
        unfold prodAll
        refine IsWeightedHomogeneous.prod _ _ _ fun i _ => ?_
        apply isWH_rename
        refine isWH_congr ?_ (isWH_add
          (blockPoly_isWeightedHomogeneous' (X o) (F o) (fun _ x => x.2.val) (H.std o) (blkAt L o i) 0 t0 (c0 : ℕ))
          (blockPoly_isWeightedHomogeneous' (X o) (F o) (fun _ x => x.2.val) (H.std o) (blkAt L o i) 1 (t0 + 1) (c0 : ℕ)))
        rintro ⟨ρ, gg, tt, cc'⟩
        simp only [Function.comp_apply, keyEq, wRowG, true_and, H.hty]
        fin_cases gg <;> simp
      · rw [if_neg ho]
        unfold toAll
        apply isWH_rename
        refine isWH_of_zero (fun x => ?_) _
        obtain ⟨ρ, gg, tt, cc'⟩ := x
        simp only [Function.comp_apply, keyEq]
        rw [if_neg]
        exact fun hh => ho hh.1
    · push Not at hσ
      rw [H.tie.2 σ hσ c0 c0.2]
      refine isWH_of_zero (fun x => ?_) _
      obtain ⟨ρ, o, g, t, c⟩ := x
      show (if (⟨tau o t, c⟩ : Σ σ, Fin (r σ)) = ⟨σ, c0⟩ then 1 else 0) = 0
      rw [if_neg]
      exact fun hh => hσ o t (congrArg Sigma.fst hh)

end Formalism.L2.FormalSeriesBounds.RF
