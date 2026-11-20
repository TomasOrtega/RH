import Formalism.TruncatedSeriesCounting.PowMemSpanOfMemSpanLinearDistinguished
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.LenBound

noncomputable section

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds

/- English proof (translation)
Apply `Submodule.map_injective_of_injective Z.injective_subtype` to reduce the goal to its premises. Establish `hle : Submodule.span O (s : Set M) ≤ Z` using `Submodule.span_le.2 fun x hx => hs x hx`. Establish `hr : Set.range (⇑Z.subtype ∘ fun x : s => (⟨x, hs x x.2⟩ : Z)) = (s : Set M)`. Use extensionality with `y`. Simplify using the standard rewrite rules.

Rewrite using `[Submodule.map_sup, Submodule.map_span, Submodule.map_comap_subtype, Submodule.map_comap_subtype, ← Set.range_comp, hr, inf_comm Z, sup_inf_assoc_of_le J hle, inf_comm J Z]`.
-/
private lemma comap_subtype_span_sup_eq_span_range_sup {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (Z J : Submodule O M) (s : Finset M) (hs : ∀ x ∈ s, x ∈ Z) :
    (Submodule.span O (s : Set M) ⊔ J).comap Z.subtype =
      Submodule.span O (Set.range fun x : s => (⟨x, hs x x.2⟩ : Z)) ⊔ J.comap Z.subtype := by
  apply Submodule.map_injective_of_injective Z.injective_subtype
  have hle : Submodule.span O (s : Set M) ≤ Z := Submodule.span_le.2 fun x hx => hs x hx
  have hr : Set.range (⇑Z.subtype ∘ fun x : s => (⟨x, hs x x.2⟩ : Z)) = (s : Set M) := by
    ext y
    simp
  rw [Submodule.map_sup, Submodule.map_span, Submodule.map_comap_subtype, Submodule.map_comap_subtype,
    ← Set.range_comp, hr, inf_comm Z, sup_inf_assoc_of_le J hle, inf_comm J Z]

/- English proof (translation)
Unfold `ColTwoStep`. Introduce `O M _ _ _ ℓ g g₀ e e' Z I s s₀ hIZ hs hs₀ hs₀Z hspan hZ hI`. Establish `hsZ : ∀ x ∈ s, x ∈ Z` using `fun x hx => by`. Rewrite using `[← hspan]`. Conclude with `Submodule.mem_sup_left (Submodule.subset_span hx)`.

Establish `hs₀Z' : ∀ x ∈ s₀, x ∈ Z` using `fun x hx => hs₀Z hx`. Establish `hIT : I.comap Z.subtype ≤ (Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype` using `Submodule.comap_mono le_sup_right`. Set `N` to `((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).map (I.comap Z.subtype).mkQ`. Establish `hsplit : Module.length O (Z ⧸ I.comap Z.subtype) = Module.length O N + Module.length O ((Z ⧸ I.comap Z.subtype) ⧸ N)` using `Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)`. Establish `hQN : Module.length O ((Z ⧸ I.comap Z.subtype) ⧸ N) = Module.length O (Z ⧸ (Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype)` using `(Submodule.quotientQuotientEquivQuotient _ _ hIT).length_eq`.

Set `q : s₀ → Z ⧸ I.comap Z.subtype` to `fun x => (I.comap Z.subtype).mkQ ⟨x, hs₀Z' x x.2⟩`. Establish `hNq : N = Submodule.span O (Set.range q)` using `by show ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).map (I.comap Z.subtype).mkQ = _`. Rewrite using `[comap_subtype_span_sup_eq_span_range_sup Z I s₀ hs₀Z', Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq, Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Set `v : s₀ → N` to `fun x => ⟨q x, by rw [hNq]; exact Submodule.subset_span ⟨x, rfl⟩⟩`.

Establish `hv_top : Submodule.span O (Set.range v) = ⊤`. Apply `Submodule.map_injective_of_injective N.injective_subtype` to reduce the goal to its premises. Rewrite using `[Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top]`. Conclude with `hNq.symm`. Establish `hv_kill : ∀ x, ((ℓ : O) ^ e') • v x = 0`.

Introduce `x`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((ℓ : O) ^ e') • q x = 0`. Simplify using `only [q, Submodule.mkQ_apply]`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`.

Use `show ((ℓ : O) ^ e') • (x : M) ∈ I`. Establish `h` using `hI x (Submodule.subset_span x.2)`. Rewrite `h` using `[← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]`. Then use the resulting hypothesis. Establish `hN : Module.length O N ≤ (g₀ : ℕ∞) * e' * Module.length O (O ⧸ Ideal.span {(ℓ : O)})`. Establish `h1` using `Formalism.WachCohomologyFacts.PLenBound.length_le_of_span v ((ℓ : O) ^ e') hv_top hv_kill`.

Establish `h2` using `Formalism.WachCohomologyFacts.PLenBound.length_quot_pow_le (ℓ : O) e'`. Combine the equalities or inequalities in the displayed calculation. Set `w : s → Z ⧸ (Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype` to `fun x => ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).mkQ ⟨x, hsZ x x.2⟩`. Establish `hw_top : Submodule.span O (Set.range w) = ⊤`. Establish `htop : (⊤ : Submodule O Z) = Submodule.span O (Set.range fun x : s => (⟨x, hsZ x x.2⟩ : Z)) ⊔ I.comap Z.subtype`.

Rewrite using `[← comap_subtype_span_sup_eq_span_range_sup Z I s hsZ, hspan, Submodule.comap_subtype_self]`. Establish `hmt : Submodule.map ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).mkQ ⊤ = ⊤`. Rewrite using `[Submodule.map_top, Submodule.range_mkQ]`. Establish `hbot : Submodule.map ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).mkQ (I.comap Z.subtype) = ⊥` using `le_bot_iff.1 ((Submodule.map_mono hIT).trans (Submodule.mkQ_map_self _).le)`. Rewrite using `[← hmt, htop, Submodule.map_sup, hbot, sup_bot_eq, Submodule.map_span, ← Set.range_comp]`.

Both sides reduce to the same expression. Establish `hw_kill : ∀ x, ((ℓ : O) ^ e) • w x = 0`. Introduce `x`. Simplify using `only [w, Submodule.mkQ_apply]`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`.

Use `show ((ℓ : O) ^ e) • (x : M) ∈ Submodule.span O (s₀ : Set M) ⊔ I`. Establish `h` using `hZ x (hsZ x x.2)`. Rewrite `h` using `[← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]`. Then use the resulting hypothesis. Establish `hZT : Module.length O (Z ⧸ (Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype) ≤ (g : ℕ∞) * e * Module.length O (O ⧸ Ideal.span {(ℓ : O)})`. Establish `h1` using `Formalism.WachCohomologyFacts.PLenBound.length_le_of_span w ((ℓ : O) ^ e) hw_top hw_kill`.

Establish `h2` using `Formalism.WachCohomologyFacts.PLenBound.length_quot_pow_le (ℓ : O) e`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hsplit, hQN]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem length_quotient_le_of_two_step : ColTwoStep := by
  unfold ColTwoStep
  intro O M _ _ _ ℓ g g₀ e e' Z I s s₀ hIZ hs hs₀ hs₀Z hspan hZ hI
  classical
  have hsZ : ∀ x ∈ s, x ∈ Z := fun x hx => by
    rw [← hspan]
    exact Submodule.mem_sup_left (Submodule.subset_span hx)
  have hs₀Z' : ∀ x ∈ s₀, x ∈ Z := fun x hx => hs₀Z hx
  have hIT : I.comap Z.subtype ≤ (Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype :=
    Submodule.comap_mono le_sup_right
  let N := ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).map (I.comap Z.subtype).mkQ
  have hsplit : Module.length O (Z ⧸ I.comap Z.subtype) =
      Module.length O N + Module.length O ((Z ⧸ I.comap Z.subtype) ⧸ N) :=
    Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N)
  have hQN : Module.length O ((Z ⧸ I.comap Z.subtype) ⧸ N) =
      Module.length O (Z ⧸ (Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype) :=
    (Submodule.quotientQuotientEquivQuotient _ _ hIT).length_eq
  let q : s₀ → Z ⧸ I.comap Z.subtype := fun x => (I.comap Z.subtype).mkQ ⟨x, hs₀Z' x x.2⟩
  have hNq : N = Submodule.span O (Set.range q) := by
    show ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).map (I.comap Z.subtype).mkQ = _
    rw [comap_subtype_span_sup_eq_span_range_sup Z I s₀ hs₀Z', Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq,
      Submodule.map_span, ← Set.range_comp]
    rfl
  let v : s₀ → N := fun x => ⟨q x, by rw [hNq]; exact Submodule.subset_span ⟨x, rfl⟩⟩
  have hv_top : Submodule.span O (Set.range v) = ⊤ := by
    apply Submodule.map_injective_of_injective N.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top]
    exact hNq.symm
  have hv_kill : ∀ x, ((ℓ : O) ^ e') • v x = 0 := by
    intro x
    apply Subtype.ext
    show ((ℓ : O) ^ e') • q x = 0
    simp only [q, Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    show ((ℓ : O) ^ e') • (x : M) ∈ I
    have h := hI x (Submodule.subset_span x.2)
    rwa [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow] at h
  have hN : Module.length O N ≤ (g₀ : ℕ∞) * e' * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) := by
    have h1 := Formalism.WachCohomologyFacts.PLenBound.length_le_of_span v ((ℓ : O) ^ e') hv_top hv_kill
    have h2 := Formalism.WachCohomologyFacts.PLenBound.length_quot_pow_le (ℓ : O) e'
    calc Module.length O N ≤ (Fintype.card s₀ : ℕ∞) *
          Module.length O (O ⧸ Ideal.span {(ℓ : O) ^ e'}) := h1
      _ ≤ (g₀ : ℕ∞) * ((e' : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})) :=
          mul_le_mul' (by simpa using hs₀) h2
      _ = _ := by ring
  let w : s → Z ⧸ (Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype :=
    fun x => ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).mkQ ⟨x, hsZ x x.2⟩
  have hw_top : Submodule.span O (Set.range w) = ⊤ := by
    have htop : (⊤ : Submodule O Z) = Submodule.span O (Set.range fun x : s => (⟨x, hsZ x x.2⟩ : Z)) ⊔
        I.comap Z.subtype := by
      rw [← comap_subtype_span_sup_eq_span_range_sup Z I s hsZ, hspan, Submodule.comap_subtype_self]
    have hmt : Submodule.map ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).mkQ ⊤ = ⊤ := by
      rw [Submodule.map_top, Submodule.range_mkQ]
    have hbot : Submodule.map ((Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype).mkQ
        (I.comap Z.subtype) = ⊥ :=
      le_bot_iff.1 ((Submodule.map_mono hIT).trans (Submodule.mkQ_map_self _).le)
    rw [← hmt, htop, Submodule.map_sup, hbot, sup_bot_eq, Submodule.map_span, ← Set.range_comp]
    rfl
  have hw_kill : ∀ x, ((ℓ : O) ^ e) • w x = 0 := by
    intro x
    simp only [w, Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    show ((ℓ : O) ^ e) • (x : M) ∈ Submodule.span O (s₀ : Set M) ⊔ I
    have h := hZ x (hsZ x x.2)
    rwa [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow] at h
  have hZT : Module.length O (Z ⧸ (Submodule.span O (s₀ : Set M) ⊔ I).comap Z.subtype) ≤
      (g : ℕ∞) * e * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) := by
    have h1 := Formalism.WachCohomologyFacts.PLenBound.length_le_of_span w ((ℓ : O) ^ e) hw_top hw_kill
    have h2 := Formalism.WachCohomologyFacts.PLenBound.length_quot_pow_le (ℓ : O) e
    calc _ ≤ (Fintype.card s : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O) ^ e}) := h1
      _ ≤ (g : ℕ∞) * ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})) :=
          mul_le_mul' (by simpa using hs) h2
      _ = _ := by ring
  rw [hsplit, hQN]
  calc _ ≤ (g₀ : ℕ∞) * e' * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) +
        (g : ℕ∞) * e * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) := add_le_add hN hZT
    _ = _ := by push_cast; ring

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds
