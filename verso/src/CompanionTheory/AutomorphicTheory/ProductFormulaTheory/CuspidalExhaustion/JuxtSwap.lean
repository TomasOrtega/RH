import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.JuxtDefs
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CuspidalTwistInjectiveImports

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace CompanionTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Rewrite using `[IrrGL.nu_nu, Nat.cast_add]`.
-/
theorem nu_nu_nat (x : IrrGL k) (a b : ℕ) : (x.nu (a : ℂ)).nu (b : ℂ) = x.nu ((a + b : ℕ) : ℂ) := by
  rw [IrrGL.nu_nu, Nat.cast_add]

/- English proof (translation)
Introduce and unpack `⟨⟨Γ, hΓ⟩, -, -⟩`. Simplify using `only [Segment.carrier_single] at hΓ`. Establish `inj : ∀ a b : ℕ, ρ.nu (a : ℂ) = ρ.nu (b : ℂ) → a = b` using `fun a b h => GlobalTheory.T.cuspidal_twist_injective hA ρ hρ a b h`. Establish `ha : ρ.nu (n : ℂ) ∈ Γ.carrier` using `by rw [hΓ]; exact Or.inl rfl`. Establish `hb : ρ.nu (j : ℂ) ∈ Γ.carrier` using `by rw [hΓ]; exact Or.inr rfl`.

Take `⟨i, hi, ei⟩` from `Segment.mem_carrier.1 ha`. Take `⟨i', hi', ei'⟩` from `Segment.mem_carrier.1 hb`. Establish `key : ∀ s : ℕ, Γ.first.nu ((i' + s : ℕ) : ℂ) = ρ.nu ((j + s : ℕ) : ℂ)`. Introduce `s`. Rewrite using `[← nu_nu_nat, ei', nu_nu_nat]`.

Establish `key2 : ∀ s : ℕ, Γ.first.nu ((i + s : ℕ) : ℂ) = ρ.nu ((n + s : ℕ) : ℂ)`. Introduce `s`. Rewrite using `[← nu_nu_nat, ei, nu_nu_nat]`. Break down `lt_or_ge i' i with h | h` into its components or cases. Establish `e1` using `key (i - i')`.

Rewrite `e1` using `[show i' + (i - i') = i by omega, ei]`. Establish `h2` using `inj _ _ e1`. Establish `hc : Γ.first.nu ((i' + 1 : ℕ) : ℂ) ∈ Γ.carrier` using `Segment.mem_carrier.2 ⟨i' + 1, by omega, rfl⟩`. Rewrite `hc` using `[hΓ, key 1]`. Break down `hc with hc | hc` into its components or cases.

Use `inj _ _ (Set.mem_singleton_iff.1 hc)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `inj _ _ (Set.mem_singleton_iff.1 hc)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `e1` using `key2 (i' - i)`.

Rewrite `e1` using `[show i + (i' - i) = i' by omega, ei']`. Use `inj _ _ e1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem not_linked_single (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (ρ : IrrGL k) (hρ : ρ.IsCusp) (n j : ℕ)
    (hj : j + 2 ≤ n) :
    ¬ (Segment.single (ρ.nu (n : ℂ)) (hρ.nu _)).Linked (Segment.single (ρ.nu (j : ℂ)) (hρ.nu _)) := by
  rintro ⟨⟨Γ, hΓ⟩, -, -⟩
  simp only [Segment.carrier_single] at hΓ
  have inj : ∀ a b : ℕ, ρ.nu (a : ℂ) = ρ.nu (b : ℂ) → a = b := fun a b h => GlobalTheory.T.cuspidal_twist_injective hA ρ hρ a b h
  have ha : ρ.nu (n : ℂ) ∈ Γ.carrier := by rw [hΓ]; exact Or.inl rfl
  have hb : ρ.nu (j : ℂ) ∈ Γ.carrier := by rw [hΓ]; exact Or.inr rfl
  obtain ⟨i, hi, ei⟩ := Segment.mem_carrier.1 ha
  obtain ⟨i', hi', ei'⟩ := Segment.mem_carrier.1 hb
  have key : ∀ s : ℕ, Γ.first.nu ((i' + s : ℕ) : ℂ) = ρ.nu ((j + s : ℕ) : ℂ) := by
    intro s; rw [← nu_nu_nat, ei', nu_nu_nat]
  have key2 : ∀ s : ℕ, Γ.first.nu ((i + s : ℕ) : ℂ) = ρ.nu ((n + s : ℕ) : ℂ) := by
    intro s; rw [← nu_nu_nat, ei, nu_nu_nat]
  rcases lt_or_ge i' i with h | h
  · have e1 := key (i - i')
    rw [show i' + (i - i') = i by omega, ei] at e1
    have h2 := inj _ _ e1
    have hc : Γ.first.nu ((i' + 1 : ℕ) : ℂ) ∈ Γ.carrier := Segment.mem_carrier.2 ⟨i' + 1, by omega, rfl⟩
    rw [hΓ, key 1] at hc
    rcases hc with hc | hc
    · have := inj _ _ (Set.mem_singleton_iff.1 hc); omega
    · have := inj _ _ (Set.mem_singleton_iff.1 hc); omega
  · have e1 := key2 (i' - i)
    rw [show i + (i' - i) = i' by omega, ei'] at e1
    have := inj _ _ e1
    omega

/- English proof (translation)
Take `⟨m, hm, rfl⟩` from `List.getElem_of_mem hx`. Establish `hm' : m + 1 < Δ.len`. Use `hm` as an intermediate fact. Simplify using `[decW] at this`. Use linear arithmetic over natural numbers and integers.

Use `⟨Δ.len - (m + 2), by omega, ?_⟩` and prove the remaining obligations. Simplify using `only [List.getElem_tail, decW, List.getElem_ofFn, Segment.term, Fin.val_rev]`.
-/
theorem mem_tail_decW (Δ : Segment k) (x : IrrGL k) (hx : x ∈ (decW Δ).tail) :
    ∃ j : ℕ, j + 2 ≤ Δ.len ∧ x = Δ.first.nu (j : ℂ) := by
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hx
  have hm' : m + 1 < Δ.len := by
    have := hm
    simp [decW] at this
    omega
  refine ⟨Δ.len - (m + 2), by omega, ?_⟩
  simp only [List.getElem_tail, decW, List.getElem_ofFn, Segment.term, Fin.val_rev]

/- English proof (translation)
Introduce `Q`. Proceed by induction on `Q with`. Consider the case `nil => intro P _ h`. Simplify using `using h`. Consider the case `cons q Q ih`.

Introduce `P hQ h`. Take `⟨hq, hl⟩` from `hQ q (by simp)`. Establish `h2 : EmbL σ (P ++ [ρ, q] ++ Q)` using `by simpa using h`. Establish `h3` using `hS σ ρ q P Q _ _ (single_spec hρ).2.1 (single_spec hq).2.1 hl h2`. Establish `h4` using `ih (P ++ [q]) (fun q' hq' => hQ q' (by simp [hq'])) (by simpa using h3)`.

Simplify using `using h4`.
-/
theorem move_past (hS : SwapP k) (σ ρ : IrrGL k) (hρ : ρ.IsCusp) :
    ∀ (Q P : List (IrrGL k)), (∀ q ∈ Q, ∃ hq : q.IsCusp, ¬ (Segment.single ρ hρ).Linked (Segment.single q hq)) →
      EmbL σ (P ++ ρ :: Q) → EmbL σ (P ++ Q ++ [ρ]) := by
  intro Q
  induction Q with
  | nil => intro P _ h; simpa using h
  | cons q Q ih =>
    intro P hQ h
    obtain ⟨hq, hl⟩ := hQ q (by simp)
    have h2 : EmbL σ (P ++ [ρ, q] ++ Q) := by simpa using h
    have h3 := hS σ ρ q P Q _ _ (single_spec hρ).2.1 (single_spec hq).2.1 hl h2
    have h4 := ih (P ++ [q]) (fun q' hq' => hQ q' (by simp [hq'])) (by simpa using h3)
    simpa using h4

/- English proof (translation)
Take `⟨p, P', rfl⟩` from `List.exists_cons_of_ne_nil hP`. Rewrite using `[h1]`. Use `move_past hS σ (nxt Δ) (Δ.isCusp_first.nu _) Q (p :: P') ?_ he` and prove the remaining obligations. Introduce `q hq`. Establish `hq' : q ∈ (decW Δ).tail` using `by rw [h1]; simp [hq]`.

Take `⟨j, hj, rfl⟩` from `mem_tail_decW Δ q hq'`. Conclude with `⟨Δ.isCusp_first.nu _, not_linked_single hA Δ.first Δ.isCusp_first Δ.len j (by omega)⟩`.
-/
theorem emb_move_end (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hS : SwapP k) (σ : IrrGL k) (Δ : Segment k)
    (P Q : List (IrrGL k)) (h1 : decW Δ = P ++ Q) (hP : P ≠ []) (he : EmbL σ (P ++ nxt Δ :: Q)) :
    EmbL σ (decW Δ ++ [nxt Δ]) := by
  obtain ⟨p, P', rfl⟩ := List.exists_cons_of_ne_nil hP
  rw [h1]
  refine move_past hS σ (nxt Δ) (Δ.isCusp_first.nu _) Q (p :: P') ?_ he
  intro q hq
  have hq' : q ∈ (decW Δ).tail := by rw [h1]; simp [hq]
  obtain ⟨j, hj, rfl⟩ := mem_tail_decW Δ q hq'
  exact ⟨Δ.isCusp_first.nu _, not_linked_single hA Δ.first Δ.isCusp_first Δ.len j (by omega)⟩

end CompanionTheory.Exh

end
