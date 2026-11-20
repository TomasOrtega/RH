import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandA

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace GramDeterminantPositive

section

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Set `f : V →ₗ[K] (Fin k → K)` to `LinearMap.pi fun i => h (v i)`. Establish `hlt : finrank K (Fin k → K) < finrank K V`. Rewrite using `[Module.finrank_fin_fun]`. Conclude with `hk`. Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt)`.

Conclude with `⟨x, hx0, fun i => congrFun (LinearMap.mem_ker.1 hx) i⟩`.
-/
theorem exists_ortho_ne_zero [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {k : ℕ}
    (v : Fin k → V) (hk : k < finrank K V) : ∃ x : V, x ≠ 0 ∧ ∀ i, h (v i) x = 0 := by
  let f : V →ₗ[K] (Fin k → K) := LinearMap.pi fun i => h (v i)
  have hlt : finrank K (Fin k → K) < finrank K V := by
    rw [Module.finrank_fin_fun]; exact hk
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt)
  exact ⟨x, hx0, fun i => congrFun (LinearMap.mem_ker.1 hx) i⟩

/- English proof (translation)
Establish `hli : LinearIndependent K v` using `LinearMap.linearIndependent_of_isOrthoᵢ (B := h) (fun i j hij => ho i j hij) (fun i => hne i)`. Establish `htop : Submodule.span K (Set.range v) = ⊤` using `hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hk])`. Conclude with `⟨Basis.mk hli htop.ge, fun i => Basis.mk_apply hli htop.ge i⟩`.
-/
theorem exists_basis_of_ortho [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) {k : ℕ}
    (v : Fin k → V) (hk : finrank K V = k) (ho : ∀ i j, i ≠ j → h (v i) (v j) = 0)
    (hne : ∀ i, h (v i) (v i) ≠ 0) : ∃ e : Basis (Fin k) K V, ∀ i, e i = v i := by
  have hli : LinearIndependent K v :=
    LinearMap.linearIndependent_of_isOrthoᵢ (B := h) (fun i j hij => ho i j hij) (fun i => hne i)
  have htop : Submodule.span K (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hk])
  exact ⟨Basis.mk hli htop.ge, fun i => Basis.mk_apply hli htop.ge i⟩

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact fun _ => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩`. Consider the case `succ k ih`. Introduce `hk`.

Take `⟨v, ho, hne⟩` from `ih (by omega)`. Take `⟨x, hx0, hx⟩` from `exists_ortho_ne_zero h v (by omega)`. Use `⟨Fin.snoc v x, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j`.

Introduce `hij`. Conclude with `absurd rfl hij`. Introduce `_`. Rewrite using `[Fin.snoc_last, Fin.snoc_castSucc]`. Conclude with `hs.isRefl _ _ (hx j)`.

Introduce `_`. Rewrite using `[Fin.snoc_last, Fin.snoc_castSucc]`. Conclude with `hx i`. Introduce `hij`. Rewrite using `[Fin.snoc_castSucc, Fin.snoc_castSucc]`.

Conclude with `ho i j (fun e => hij (by rw [e]))`. Introduce `i`. Use `Fin.lastCases ?_ (fun i => ?_) i` and prove the remaining obligations. Rewrite using `[Fin.snoc_last]`. Conclude with `hx0`.

Rewrite using `[Fin.snoc_castSucc]`. Conclude with `hne i`.
-/
theorem exists_ortho_family [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) :
    ∀ k : ℕ, k ≤ finrank K V →
      ∃ v : Fin k → V, (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧ ∀ i, v i ≠ 0 := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨v, ho, hne⟩ := ih (by omega)
    obtain ⟨x, hx0, hx⟩ := exists_ortho_ne_zero h v (by omega)
    refine ⟨Fin.snoc v x, ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · intro hij; exact absurd rfl hij
      · intro _
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        exact hs.isRefl _ _ (hx j)
      · intro _
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        exact hx i
      · intro hij
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact ho i j (fun e => hij (by rw [e]))
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [Fin.snoc_last]; exact hx0
      · rw [Fin.snoc_castSucc]; exact hne i

end

end GramDeterminantPositive

/- English proof (translation)
Introduce `K _ _ _ hK V _ _ _ _ _ h hs hpos`. Establish `hne0 : ∀ x : V, x ≠ 0 → h x x ≠ 0`. Introduce `x hx h0`. Take `⟨φ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Use `hpos x hx φ` as an intermediate fact.

Rewrite `this` using `[h0, map_zero]`. Simplify using `at this`. Take `⟨v, ho, hne⟩` from `GramDeterminantPositive.exists_ortho_family h hs (finrank K V) le_rfl`. Take `⟨e, he⟩` from `GramDeterminantPositive.exists_basis_of_ortho h v rfl ho (fun i => hne0 _ (hne i))`. Use `⟨e, fun i j hij => by rw [he, he]; exact ho i j hij, fun i => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Conclude with `hs.eq (e i) (e i)`. Conclude with `hpos (e i) (e.ne_zero i)`.
-/
theorem orthBasisPos_holds : OrthBasisPos := by
  intro K _ _ _ hK V _ _ _ _ _ h hs hpos
  have hne0 : ∀ x : V, x ≠ 0 → h x x ≠ 0 := by
    intro x hx h0
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hpos x hx φ
    rw [h0, map_zero] at this
    simp at this
  obtain ⟨v, ho, hne⟩ := GramDeterminantPositive.exists_ortho_family h hs (finrank K V) le_rfl
  obtain ⟨e, he⟩ := GramDeterminantPositive.exists_basis_of_ortho h v rfl ho (fun i => hne0 _ (hne i))
  refine ⟨e, fun i j hij => by rw [he, he]; exact ho i j hij, fun i => ⟨?_, ?_⟩⟩
  · exact hs.eq (e i) (e i)
  · exact hpos (e i) (e.ne_zero i)

section

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

end

namespace GramDeterminantPositive

end GramDeterminantPositive

end Formalism.HermitianLattices.Ext.L3
