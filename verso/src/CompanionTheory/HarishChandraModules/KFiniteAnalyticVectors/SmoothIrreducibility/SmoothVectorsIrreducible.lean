import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.OrbitDerivatives.HasDerivAtMatrixExpZero
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.BesselSplit

open Matrix

noncomputable section

namespace CompanionTheory.D.gk.Rec

open CompanionTheory.D.Upq.Sm

/- English proof (translation)
Proceed by induction on `W with`. Consider the case `nil => rfl`. Consider the case `cons X W ih => show Formalism.MainNotions.S.dsig (k := k) (r := r) σ X (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ W v) = _`. Rewrite using `[ih]`. Both sides reduce to the same expression.
-/
theorem dsigW_rec {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat (2 * r + k + 1) → (H →L[ℂ] H)) (W : List (Mat (2 * r + k + 1))) (v : H) :
    Formalism.MainNotions.S.dsigW (k := k) (r := r) σ W v = PI.UpqRep.dsigW (k := k) (r := r) σ W v := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    show Formalism.MainNotions.S.dsig (k := k) (r := r) σ X (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ W v) = _
    rw [ih]
    rfl

/- English proof (translation)
Introduce `k r ε lam H _ _ _ σ _ hσ w hw hw0 Wq _ _ l hadd hsm ⟨C, Ws, hW, hb⟩ hz v hv`. Establish `h : RepOn (PI.UpqRep.UH (PI.UpqRep.Hpk k r)) σ`. Take `⟨P, ⟨⟨hP, hPJ⟩, -⟩, -, -, ⟨⟨h1, hm⟩, -⟩, -⟩` from `hσ`. Conclude with `repOn_of_conj hP hPJ h1 hm`. Simplify using `only [dsigW_rec] at hb`.

Establish `hw' : IsSm _ σ w` using `hw`. Establish `h0 : ∀ (N : ℕ) (c : Fin N → ℂ) (g : Fin N → Mat (2 * r + k + 1)), (∀ i, g i ∈ PI.UpqRep.UH (PI.UpqRep.Hpk k r)) → ∀ s : Finset (Fin N), IsSm (PI.UpqRep.UH (PI.UpqRep.Hpk k r)) σ (∑ i ∈ s, c i • σ (g i) w) ∧ l (∑ i ∈ s, c i • σ (g i) w) = 0`. Introduce `N c g hg s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`.

Use `⟨by simpa using IsSm.zero, ?_⟩` and prove the remaining obligations. Use `hadd 0 IsSm.zero 0 IsSm.zero` as an intermediate fact. Simplify using `using this`. Consider the case `insert i s hi ih`. Establish `h1` using `hw'.apply h (hg i)`.

Rewrite using `[Finset.sum_insert hi]`. Use `⟨(h1.smul _).add ih.1, ?_⟩` and prove the remaining obligations. Rewrite using `[hadd _ (h1.smul _) _ ih.1, ih.2, add_zero]`. Apply the tactic sequence `rcases hsm with hs | hs <;> rw [hs _ _ h1, hz _ (hg i), smul_zero]`. Rewrite using `[← norm_le_zero_iff]`.

Use `le_of_forall_pos_le_add fun δ hδ => ?_` and prove the remaining obligations. Take `⟨N, c, g, hg, hlt⟩` from `cyc_of_smooth k r ε lam H σ w hσ hw0 hw v hv Ws hW (δ / (|C| + 1)) (by positivity)`. Take `⟨hs, hl⟩` from `h0 N c g hg Finset.univ`. Establish `hd` using `IsSm.sub (G := PI.UpqRep.UH (PI.UpqRep.Hpk k r)) (σ := σ) hv hs`. Establish `e : l v = l (v - ∑ i, c i • σ (g i) w)` using `by conv_lhs => rw [← sub_add_cancel v (∑ i, c i • σ (g i) w), hadd _ hd _ hs, hl, add_zero]`.

Rewrite using `[e, zero_add]`. Establish `hn : 0 ≤ (Ws.map fun w' => ‖PI.UpqRep.dsigW (k` using `k) (r := r) σ w' (v - ∑ i, c i • σ (g i) w)‖).sum := List.sum_nonneg fun _ h => by obtain ⟨W, -, rfl⟩ := List.mem_map.1 h; exact norm_nonneg _`. Use `(hb _ hd).trans ((mul_le_mul (le_abs_self C) hlt.le hn (abs_nonneg C)).trans ?_)` and prove the remaining obligations. Rewrite using `[← mul_div_assoc, div_le_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem smooth_vectors_irreducible : Formalism.L2.SG.BesselSplit.SmoothIrred := by
  intro k r ε lam H _ _ _ σ _ hσ w hw hw0 Wq _ _ l hadd hsm ⟨C, Ws, hW, hb⟩ hz v hv
  have h : RepOn (PI.UpqRep.UH (PI.UpqRep.Hpk k r)) σ := by
    obtain ⟨P, ⟨⟨hP, hPJ⟩, -⟩, -, -, ⟨⟨h1, hm⟩, -⟩, -⟩ := hσ
    exact repOn_of_conj hP hPJ h1 hm
  simp only [dsigW_rec] at hb
  have hw' : IsSm _ σ w := hw
  have h0 : ∀ (N : ℕ) (c : Fin N → ℂ) (g : Fin N → Mat (2 * r + k + 1)),
      (∀ i, g i ∈ PI.UpqRep.UH (PI.UpqRep.Hpk k r)) → ∀ s : Finset (Fin N),
      IsSm (PI.UpqRep.UH (PI.UpqRep.Hpk k r)) σ (∑ i ∈ s, c i • σ (g i) w) ∧ l (∑ i ∈ s, c i • σ (g i) w) = 0 := by
    intro N c g hg s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨by simpa using IsSm.zero, ?_⟩
      have := hadd 0 IsSm.zero 0 IsSm.zero
      simpa using this
    | insert i s hi ih =>
      have h1 := hw'.apply h (hg i)
      rw [Finset.sum_insert hi]
      refine ⟨(h1.smul _).add ih.1, ?_⟩
      rw [hadd _ (h1.smul _) _ ih.1, ih.2, add_zero]
      rcases hsm with hs | hs <;> rw [hs _ _ h1, hz _ (hg i), smul_zero]
  rw [← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨N, c, g, hg, hlt⟩ := cyc_of_smooth k r ε lam H σ w hσ hw0 hw v hv Ws hW (δ / (|C| + 1)) (by positivity)
  obtain ⟨hs, hl⟩ := h0 N c g hg Finset.univ
  have hd := IsSm.sub (G := PI.UpqRep.UH (PI.UpqRep.Hpk k r)) (σ := σ) hv hs
  have e : l v = l (v - ∑ i, c i • σ (g i) w) := by
    conv_lhs => rw [← sub_add_cancel v (∑ i, c i • σ (g i) w), hadd _ hd _ hs, hl, add_zero]
  rw [e, zero_add]
  have hn : 0 ≤ (Ws.map fun w' => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w' (v - ∑ i, c i • σ (g i) w)‖).sum :=
    List.sum_nonneg fun _ h => by obtain ⟨W, -, rfl⟩ := List.mem_map.1 h; exact norm_nonneg _
  refine (hb _ hd).trans ((mul_le_mul (le_abs_self C) hlt.le hn (abs_nonneg C)).trans ?_)
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
  nlinarith

end CompanionTheory.D.gk.Rec
