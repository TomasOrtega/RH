import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitTwistBound

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.LeafB

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Introduce `N t`. Proceed by induction on `t with`. Consider the case `leaf V z`. Introduce `h`. Break down `h with ⟨rfl, rfl, rfl⟩ | ⟨-, hV, -⟩` into its components or cases.

Conclude with `⟨_, 0, hT E τ, rfl⟩`. Take `⟨m₀, hm₀⟩` from `hD E _ V hV τ`. Conclude with `⟨_, m₀, hm₀, rfl⟩`. Consider the case `node t₁ t₂ i₁ i₂`. Introduce `h`.

Take `⟨m₁, h₁⟩` from `i₁ h.1`. Take `⟨m₂, h₂⟩` from `i₂ h.2`. Conclude with `⟨_, m₁, m₂, h₁, h₂, rfl⟩`.
-/
theorem exists_infOf (hD : DiscInf) (hT : TopInf) (τ : E →+* ℂ) :
    ∀ {N : ℕ} {t : Tr E N}, t.Good → ∃ m', t.InfOf τ m' := by
  intro N t
  induction t with
  | leaf V z =>
    intro h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨-, hV, -⟩
    · exact ⟨_, 0, hT E τ, rfl⟩
    · obtain ⟨m₀, hm₀⟩ := hD E _ V hV τ
      exact ⟨_, m₀, hm₀, rfl⟩
  | node t₁ t₂ i₁ i₂ =>
    intro h
    obtain ⟨m₁, h₁⟩ := i₁ h.1
    obtain ⟨m₂, h₂⟩ := i₂ h.2
    exact ⟨_, m₁, m₂, h₁, h₂, rfl⟩

/- English proof (translation)
Introduce `N t`. Proceed by induction on `t with`. Consider the case `leaf V z`. Introduce `h hb hM`. Break down `h with ⟨h0, -, -⟩ | ⟨-, hV, -⟩` into its components or cases.

Use linear arithmetic over natural numbers and integers. Use `⟨hV, fun τ m₀ hm₀ x hx => ?_⟩` and prove the remaining obligations. Conclude with `hb τ (m₀.map (· + z)) ⟨m₀, hm₀, rfl⟩ _ (Multiset.mem_map_of_mem _ hx)`. Consider the case `node t₁ t₂ i₁ i₂`. Introduce `h hb`.

Use `⟨i₁ h.1 fun τ m₁ h₁ x hx => ?_, i₂ h.2 fun τ m₂ h₂ x hx => ?_⟩` and prove the remaining obligations. Take `⟨m₂, h₂⟩` from `exists_infOf hD hT τ h.2`. Conclude with `hb τ (m₁ + m₂) ⟨m₁, m₂, h₁, h₂, rfl⟩ x (Multiset.mem_add.2 (Or.inl hx))`. Take `⟨m₁, h₁⟩` from `exists_infOf hD hT τ h.1`. Conclude with `hb τ (m₁ + m₂) ⟨m₁, m₂, h₁, h₂, rfl⟩ x (Multiset.mem_add.2 (Or.inr hx))`.
-/
theorem leaf_entries (hD : DiscInf) (hT : TopInf) (B : ℝ) :
    ∀ {N : ℕ} {t : Tr E N}, t.Good → (∀ τ m', t.InfOf τ m' → ∀ x ∈ m', ‖x‖ ≤ B) →
      LeafZ (fun M V z => 0 < M → GlobalTheory.UnitaryBC.IsDiscrete V ∧
        ∀ (τ : E →+* ℂ) (m₀ : Multiset ℂ), HasInfCharGL V τ m₀ → ∀ x ∈ m₀, ‖x + z‖ ≤ B) t := by
  intro N t
  induction t with
  | leaf V z =>
    intro h hb hM
    rcases h with ⟨h0, -, -⟩ | ⟨-, hV, -⟩
    · omega
    · refine ⟨hV, fun τ m₀ hm₀ x hx => ?_⟩
      exact hb τ (m₀.map (· + z)) ⟨m₀, hm₀, rfl⟩ _ (Multiset.mem_map_of_mem _ hx)
  | node t₁ t₂ i₁ i₂ =>
    intro h hb
    refine ⟨i₁ h.1 fun τ m₁ h₁ x hx => ?_, i₂ h.2 fun τ m₂ h₂ x hx => ?_⟩
    · obtain ⟨m₂, h₂⟩ := exists_infOf hD hT τ h.2
      exact hb τ (m₁ + m₂) ⟨m₁, m₂, h₁, h₂, rfl⟩ x (Multiset.mem_add.2 (Or.inl hx))
    · obtain ⟨m₁, h₁⟩ := exists_infOf hD hT τ h.1
      exact hb τ (m₁ + m₂) ⟨m₁, m₂, h₁, h₂, rfl⟩ x (Multiset.mem_add.2 (Or.inr hx))

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih`. Rewrite using `[Multiset.sum_cons, Multiset.card_cons]`. Establish `h1` using `h a (Multiset.mem_cons_self a s)`.

Establish `h2` using `ih fun x hx => h x (Multiset.mem_cons_of_mem hx)`. Establish `h3` using `norm_add_le a s.sum`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_sum_le (s : Multiset ℂ) (B : ℝ) (h : ∀ x ∈ s, ‖x‖ ≤ B) :
    ‖s.sum‖ ≤ (Multiset.card s : ℝ) * B := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.sum_cons, Multiset.card_cons]
    have h1 := h a (Multiset.mem_cons_self a s)
    have h2 := ih fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have h3 := norm_add_le a s.sum
    push_cast
    linarith

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih`. Rewrite using `[Multiset.map_cons, Multiset.sum_cons, ih, Multiset.sum_cons, Multiset.card_cons]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_map_add_const (s : Multiset ℂ) (z : ℂ) :
    (s.map (· + z)).sum = s.sum + (Multiset.card s : ℂ) * z := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.sum_cons, Multiset.card_cons]
    push_cast
    ring

/- English proof (translation)
Use `choose m₀ hm₀ using hD E M V hV`. Establish `htr : ∑ τ, (m₀ τ).sum = 0` using `GlobalTheory.CompanionTheory.TotalTrace.total_trace_eq_zero hV hm₀`. Establish `hcard : ∀ τ, Multiset.card (m₀ τ) = M` using `fun τ => (hm₀ τ).1`. Take `⟨τ₀⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hd : 0 < Fintype.card (E →+* ℂ)` using `Fintype.card_pos_iff.2 ⟨τ₀⟩`.

Establish `hB : 0 ≤ B`. Take `⟨x, hx⟩` from `Multiset.card_pos_iff_exists_mem.1 (by rw [hcard τ₀]; exact hM)`. Conclude with `(norm_nonneg _).trans (hb τ₀ _ (hm₀ τ₀) x hx)`. Establish `hsum : ∑ τ, ((m₀ τ).map (· + z)).sum = (Fintype.card (E →+* ℂ) : ℂ) * ((M : ℂ) * z)`. Simplify using `only [sum_map_add_const, hcard, Finset.sum_add_distrib, htr, zero_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`.

Establish `hle : ‖∑ τ, ((m₀ τ).map (· + z)).sum‖ ≤ (Fintype.card (E →+* ℂ) : ℝ) * ((M : ℝ) * B)`. Use `(norm_sum_le_of_le Finset.univ (n := fun _ => (M : ℝ) * B) fun τ _ => ?_).trans_eq (by simp)` and prove the remaining obligations. Use `norm_sum_le ((m₀ τ).map (· + z)) B (fun y hy => by` as an intermediate fact. Take `⟨x, hx, rfl⟩` from `Multiset.mem_map.1 hy`. Conclude with `hb τ _ (hm₀ τ) x hx)`.

Simplify `this` using `[hcard]`. Establish `hz : ‖z‖ ≤ B`. Rewrite `hle` using `[hsum, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]`. Establish `hdM : (0 : ℝ) < (Fintype.card (E →+* ℂ) : ℝ) * (M : ℝ)` using `by positivity`. Establish `: ((Fintype.card (E →+* ℂ) : ℝ) * (M : ℝ)) * ‖z‖ ≤ ((Fintype.card (E →+* ℂ) : ℝ) * (M : ℝ)) * B`.

Use polynomial arithmetic with `[hle]`. Conclude with `le_of_mul_le_mul_left this hdM`. Use `⟨fun τ => ⟨m₀ τ, hm₀ τ, fun x hx => ?_⟩, by linarith⟩` and prove the remaining obligations. Establish `h1` using `hb τ _ (hm₀ τ) x hx`. Establish `h2 : ‖x‖ ≤ ‖x + z‖ + ‖z‖` using `by simpa using norm_sub_le (x + z) z`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem leaf_bound (hD : DiscInf) {M : ℕ} (hM : 0 < M) {V : Submodule ℂ (Sm E M)} (hV : GlobalTheory.UnitaryBC.IsDiscrete V) {z : ℂ} {B : ℝ}
    (hb : ∀ (τ : E →+* ℂ) (m₀ : Multiset ℂ), HasInfCharGL V τ m₀ → ∀ x ∈ m₀, ‖x + z‖ ≤ B) :
    InfBdd (2 * B) V ∧ ‖z‖ ≤ 2 * B := by
  choose m₀ hm₀ using hD E M V hV
  have htr : ∑ τ, (m₀ τ).sum = 0 := GlobalTheory.CompanionTheory.TotalTrace.total_trace_eq_zero hV hm₀
  have hcard : ∀ τ, Multiset.card (m₀ τ) = M := fun τ => (hm₀ τ).1
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hd : 0 < Fintype.card (E →+* ℂ) := Fintype.card_pos_iff.2 ⟨τ₀⟩
  have hB : 0 ≤ B := by
    obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.1 (by rw [hcard τ₀]; exact hM)
    exact (norm_nonneg _).trans (hb τ₀ _ (hm₀ τ₀) x hx)
  have hsum : ∑ τ, ((m₀ τ).map (· + z)).sum = (Fintype.card (E →+* ℂ) : ℂ) * ((M : ℂ) * z) := by
    simp only [sum_map_add_const, hcard, Finset.sum_add_distrib, htr, zero_add, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  have hle : ‖∑ τ, ((m₀ τ).map (· + z)).sum‖ ≤ (Fintype.card (E →+* ℂ) : ℝ) * ((M : ℝ) * B) := by
    refine (norm_sum_le_of_le Finset.univ (n := fun _ => (M : ℝ) * B) fun τ _ => ?_).trans_eq (by simp)
    have := norm_sum_le ((m₀ τ).map (· + z)) B (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hy
      exact hb τ _ (hm₀ τ) x hx)
    simpa [hcard] using this
  have hz : ‖z‖ ≤ B := by
    rw [hsum, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast] at hle
    have hdM : (0 : ℝ) < (Fintype.card (E →+* ℂ) : ℝ) * (M : ℝ) := by positivity
    have : ((Fintype.card (E →+* ℂ) : ℝ) * (M : ℝ)) * ‖z‖ ≤ ((Fintype.card (E →+* ℂ) : ℝ) * (M : ℝ)) * B := by
      nlinarith [hle]
    exact le_of_mul_le_mul_left this hdM
  refine ⟨fun τ => ⟨m₀ τ, hm₀ τ, fun x hx => ?_⟩, by linarith⟩
  have h1 := hb τ _ (hm₀ τ) x hx
  have h2 : ‖x‖ ≤ ‖x + z‖ + ‖z‖ := by simpa using norm_sub_le (x + z) z
  linarith

/- English proof (translation)
Introduce `N t`. Proceed by induction on `t with`. Consider the case `leaf V z`. Introduce `key hM`. Take `⟨hV, hb⟩` from `key hM`.

Conclude with `leaf_bound hD hM hV hb`. Consider the case `node t₁ t₂ i₁ i₂ => exact fun key => ⟨i₁ key.1, i₂ key.2⟩`.
-/
theorem leaves_of_entries (hD : DiscInf) (B : ℝ) : ∀ {N : ℕ} {t : Tr E N},
    LeafZ (fun M V z => 0 < M → GlobalTheory.UnitaryBC.IsDiscrete V ∧
      ∀ (τ : E →+* ℂ) (m₀ : Multiset ℂ), HasInfCharGL V τ m₀ → ∀ x ∈ m₀, ‖x + z‖ ≤ B) t →
    LeafZ (fun M V z => 0 < M → InfBdd (2 * B) V ∧ ‖z‖ ≤ 2 * B) t := by
  intro N t
  induction t with
  | leaf V z =>
    intro key hM
    obtain ⟨hV, hb⟩ := key hM
    exact leaf_bound hD hM hV hb
  | node t₁ t₂ i₁ i₂ => exact fun key => ⟨i₁ key.1, i₂ key.2⟩

/- English proof (translation)
Introduce `hD hT hQ E _ _ _ N t ψ m B hI hG hψ hψ0 hC hB`. Use `leaves_of_entries hD B (leaf_entries hD hT B hG fun τ m' hm' x hx => ?_)` and prove the remaining obligations. Rewrite `hx` using `[hQ E N t ψ m τ m' hI hm' hψ hψ0 hC]`. Conclude with `hB τ x hx`.
-/
theorem leafBound : DiscInf → TopInf → InfOfEq → LeafBound := by
  intro hD hT hQ E _ _ _ N t ψ m B hI hG hψ hψ0 hC hB
  refine leaves_of_entries hD B (leaf_entries hD hT B hG fun τ m' hm' x hx => ?_)
  rw [hQ E N t ψ m τ m' hI hm' hψ hψ0 hC] at hx
  exact hB τ x hx

end GlobalTheory.CompanionTheory.EGlue.LeafB

end
