import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.CuspEmbP
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExhUnipRadOne

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Consider separately whether the proposition holds or fails. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem move_left (hM : MidP k) (hR : RefineP k) (hS : SwapP k) (hJ : JuxtP k) (hL : LinkP k) (x ρ : IrrGL k) :
    ∀ (A : List (IrrGL k)), (∀ a ∈ A, a.IsCusp ∧ ρ ≠ a.nu 1) → ∀ (Δ : Segment k) (b : IrrGL k) (B : List (IrrGL k)), Δ.first = ρ →
      IsLSeg Δ b.rep → EmbL x (A ++ [b] ++ B) → ∃ (Γ : Segment k) (c y : IrrGL k), Γ.first = ρ ∧ IsLSeg Γ c.rep ∧ EmbL x [c, y] := by
  intro A
  induction A using List.reverseRecOn with
  | nil =>
    intro _ Δ b B hΔ hb hx
    obtain ⟨σ, -, hσ⟩ := hM x [b] B [] (by simpa using hx)
    exact ⟨Δ, b, σ, hΔ, hb, by simpa using hσ⟩
  | append_singleton A' a ih =>
    intro hA Δ b B hΔ hb hx
    have hA' : ∀ a ∈ A', a.IsCusp ∧ ρ ≠ a.nu 1 := fun a' ha' => hA a' (List.mem_append_left _ ha')
    have ha := hA a (by simp)
    have hx' : EmbL x (A' ++ [a, b] ++ B) := by simpa using hx
    by_cases hlk : (Segment.single a ha.1).Linked Δ
    · rcases hL a ha.1 Δ hlk with h | h
      · exact (ha.2 (hΔ.symm.trans h)).elim
      · obtain ⟨σ, hσ, hxσ⟩ := hM x A' [a, b] B hx'
        rw [h] at hσ
        rcases hJ σ b Δ hb hσ with h2 | h2
        · have hup : (up Δ).first = ρ := by
            unfold up
            rw [Segment.first_ofFirst]
            exact hΔ
          exact ih hA' (up Δ) σ B hup h2 hxσ
        · have h3 := hR x σ A' [b, Δ.first.nu Δ.len] B h2 hxσ
          rw [← h] at h3
          exact ih hA' Δ b ([a] ++ B) hΔ hb (by simpa using h3)
    · have h3 := hS x a b A' B _ Δ (single_spec ha.1).2.1 hb hlk hx'
      exact ih hA' Δ b ([a] ++ B) hΔ hb (by simpa using h3)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the argument to an intermediate assertion. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem exhaustion_of_steps
    (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      MidP k ∧ RefineP k ∧ SwapP k ∧ CuspEmbP k ∧ SuppP k ∧ JuxtP k ∧ LinkP k ∧ MinP k ∧ PeelGoodP k) :
    GlobalTheory.Published.LanglandsExhaustionGL := by
  intro k _ _ _ _ _ x
  obtain ⟨hM, hR, hS, hC, hP, hJ, hL, hm, hG⟩ := H k
  suffices H : ∀ n : ℕ, ∀ x : IrrGL k, x.1 = n → ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep from H _ x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exact GlobalTheory.LocGL.exh_le_one x (by omega)
    obtain ⟨l, hl, hx⟩ := hC x
    have hne : l ≠ [] := by
      rintro rfl
      obtain ⟨hd, -⟩ := hx
      simp at hd
      omega
    obtain ⟨ρ, hρ, hmin⟩ := hm l hne hl
    obtain ⟨A, B, rfl⟩ := List.append_of_mem hρ
    obtain ⟨Γ, c, y, e, hc, hy⟩ := move_left hM hR hS hJ hL x ρ A
      (fun a ha => ⟨hl a (List.mem_append_left _ ha), by simpa using hmin a (List.mem_append_left _ ha) 1 one_pos⟩)
      (Segment.single ρ (hl ρ hρ)) ρ B rfl (single_spec (hl ρ hρ)).2.1 (by simpa using hx)
    obtain ⟨hd, f, hf⟩ := id hy
    have hdeg : Γ.deg = c.1 := hc.deg_eq
    have hpos' : 0 < Γ.deg := Nat.mul_pos Γ.len_pos Γ.d_pos
    have hd2 : c.1 + y.1 = x.1 := (Fin.sum_univ_two fun a => ([c, y].get a).1).symm.trans hd
    obtain ⟨𝔫, h𝔫⟩ := ih y.1 (by omega) y rfl
    refine ⟨_, hG x [c, y].get hd Γ 𝔫 hc h𝔫 ⟨f, hf⟩ fun Δ' hΔ' hp => ?_⟩
    obtain ⟨j, hj, ej⟩ := hp.2
    exact hmin _ (hP x c y _ 𝔫 hl hx hy h𝔫 Δ' hΔ') j hj (e.symm.trans ej)

end PositivityTheory.Exh

end
