import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.IntFib

section Dim

variable {S : Type} [TopologicalSpace S]

/- English proof (translation)
Unfold `topologicalKrullDim at *`. Use `iSup_le fun q => ?_` and prove the remaining obligations. Set `f` to `IrreducibleCloseds.map (Subtype.val : C → S) continuous_subtype_val`. Establish `hf : StrictMono f` using `IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal`. Set `q'` to `q.map f hf`.

Set `top : IrreducibleCloseds S` to `⟨Set.univ, IrreducibleSpace.isIrreducible_univ S, isClosed_univ⟩`. Establish `hlt : q'.last < top`. Establish `hsub : (q'.last : Set S) ⊆ C` using `by show closure (Subtype.val '' (q.last : Set C)) ⊆ C`. Conclude with `closure_minimal (by rintro _ ⟨t, -, rfl⟩; exact t.2) hC`. Use `lt_of_le_of_ne (fun x _ => Set.mem_univ x) fun heq => hne ?_` and prove the remaining obligations.

Use `Set.eq_univ_of_univ_subset fun x _ => hsub ?_` and prove the remaining obligations. Rewrite using `[heq]`. Conclude with `Set.mem_univ x`. Establish `h1` using `Order.LTSeries.length_le_krullDim (q'.snoc top hlt)`. Establish `h2 : ((q.length + 1 : ℕ) : WithBot ℕ∞) ≤ ((D + 1 : ℕ) : WithBot ℕ∞)`.

Simplify `h1.trans hS` using `[q']`. Establish `h3 : q.length + 1 ≤ D + 1` using `by exact_mod_cast h2`. Conclude with `(by omega : q.length ≤ D)` after adjusting the coercions.
-/
theorem dim_le_of_ne_univ [IrreducibleSpace S] {C : Set S} (hC : IsClosed C) (hne : C ≠ Set.univ) {D : ℕ}
    (hS : topologicalKrullDim S ≤ ((D + 1 : ℕ) : WithBot ℕ∞)) : topologicalKrullDim C ≤ D := by
  unfold topologicalKrullDim at *
  refine iSup_le fun q => ?_
  let f := IrreducibleCloseds.map (Subtype.val : C → S) continuous_subtype_val
  have hf : StrictMono f := IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal
  let q' := q.map f hf
  let top : IrreducibleCloseds S := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ S, isClosed_univ⟩
  have hlt : q'.last < top := by
    have hsub : (q'.last : Set S) ⊆ C := by
      show closure (Subtype.val '' (q.last : Set C)) ⊆ C
      exact closure_minimal (by rintro _ ⟨t, -, rfl⟩; exact t.2) hC
    refine lt_of_le_of_ne (fun x _ => Set.mem_univ x) fun heq => hne ?_
    refine Set.eq_univ_of_univ_subset fun x _ => hsub ?_
    rw [heq]
    exact Set.mem_univ x
  have h1 := Order.LTSeries.length_le_krullDim (q'.snoc top hlt)
  have h2 : ((q.length + 1 : ℕ) : WithBot ℕ∞) ≤ ((D + 1 : ℕ) : WithBot ℕ∞) := by
    simpa [q'] using h1.trans hS
  have h3 : q.length + 1 ≤ D + 1 := by exact_mod_cast h2
  exact_mod_cast (by omega : q.length ≤ D)

/- English proof (translation)
Unfold `topologicalKrullDim at *`. Use `iSup_le fun q => ?_` and prove the remaining obligations. Set `f` to `IrreducibleCloseds.map (Subtype.val : T → S) continuous_subtype_val`. Establish `hf : StrictMono f` using `IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal`. Set `q'` to `q.map f hf`.

Take `⟨t, ht⟩` from `q.head.isIrreducible.nonempty`. Establish `htm : (t : S) ∈ (q'.head : Set S)` using `subset_closure ⟨t, ht, rfl⟩`. Take `⟨s, hs, hsc⟩` from `q'.head.isClosed.exists_closed_singleton ⟨_, htm⟩`. Set `bot : IrreducibleCloseds S` to `⟨{s}, isIrreducible_singleton, hsc⟩`. Establish `hlt : bot < q'.head`.

Use `lt_of_le_of_ne (fun x hx => (Set.mem_singleton_iff.1 hx) ▸ hs) fun heq => ?_` and prove the remaining obligations. Establish `: (t : S) ∈ (bot : Set S)` using `by rw [heq]; exact htm`. Establish `hts : (t : S) = s` using `this`. Conclude with `hT s hsc (hts ▸ t.2)`. Establish `h1` using `Order.LTSeries.length_le_krullDim (q'.cons bot hlt)`.

Establish `h2 : ((q.length + 1 : ℕ) : WithBot ℕ∞) ≤ ((D + 1 : ℕ) : WithBot ℕ∞)`. Simplify `h1.trans hS` using `[q']`. Establish `h3 : q.length + 1 ≤ D + 1` using `by exact_mod_cast h2`. Conclude with `(by omega : q.length ≤ D)` after adjusting the coercions.
-/
theorem dim_le_of_closedPoint_notMem [T0Space S] [CompactSpace S] {T : Set S}
    (hT : ∀ s : S, IsClosed ({s} : Set S) → s ∉ T) {D : ℕ}
    (hS : topologicalKrullDim S ≤ ((D + 1 : ℕ) : WithBot ℕ∞)) : topologicalKrullDim T ≤ D := by
  unfold topologicalKrullDim at *
  refine iSup_le fun q => ?_
  let f := IrreducibleCloseds.map (Subtype.val : T → S) continuous_subtype_val
  have hf : StrictMono f := IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal
  let q' := q.map f hf
  obtain ⟨t, ht⟩ := q.head.isIrreducible.nonempty
  have htm : (t : S) ∈ (q'.head : Set S) := subset_closure ⟨t, ht, rfl⟩
  obtain ⟨s, hs, hsc⟩ := q'.head.isClosed.exists_closed_singleton ⟨_, htm⟩
  let bot : IrreducibleCloseds S := ⟨{s}, isIrreducible_singleton, hsc⟩
  have hlt : bot < q'.head := by
    refine lt_of_le_of_ne (fun x hx => (Set.mem_singleton_iff.1 hx) ▸ hs) fun heq => ?_
    have : (t : S) ∈ (bot : Set S) := by rw [heq]; exact htm
    have hts : (t : S) = s := this
    exact hT s hsc (hts ▸ t.2)
  have h1 := Order.LTSeries.length_le_krullDim (q'.cons bot hlt)
  have h2 : ((q.length + 1 : ℕ) : WithBot ℕ∞) ≤ ((D + 1 : ℕ) : WithBot ℕ∞) := by
    simpa [q'] using h1.trans hS
  have h3 : q.length + 1 ≤ D + 1 := by exact_mod_cast h2
  exact_mod_cast (by omega : q.length ≤ D)

end Dim

variable {X : Scheme.{0}}

/- English proof (translation)
The claim follows from `(CharP.char_is_prime_or_zero (X.residueField x) _).symm`.
-/
theorem ringChar_eq_zero_or_prime (x : X) :
    ringChar (X.residueField x) = 0 ∨ (ringChar (X.residueField x)).Prime :=
  (CharP.char_is_prime_or_zero (X.residueField x) _).symm

/- English proof (translation)
Rewrite using `[← Scheme.evaluation_eq_zero_iff_notMem_basicOpen X x (show x ∈ (⊤ : X.Opens) from trivial)]`. Simplify using the standard rewrite rules.
-/
theorem natCast_eq_zero_iff (ℓ : ℕ) (x : X) :
    (ℓ : X.residueField x) = 0 ↔ x ∉ X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) := by
  rw [← Scheme.evaluation_eq_zero_iff_notMem_basicOpen X x (show x ∈ (⊤ : X.Opens) from trivial)]
  simp

/- English proof (translation)
Rewrite using `[← natCast_eq_zero_iff, ringChar.spec]`. Conclude with `(show ringChar (X.residueField x) = ℓ from hx) ▸ dvd_refl _`.
-/
theorem notMem_basicOpen_of_mem_fib {ℓ : ℕ} {x : X} (hx : x ∈ fib X ℓ) :
    x ∉ X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) := by
  rw [← natCast_eq_zero_iff, ringChar.spec]
  exact (show ringChar (X.residueField x) = ℓ from hx) ▸ dvd_refl _

/- English proof (translation)
Use `⟨notMem_basicOpen_of_mem_fib, fun h => ?_⟩` and prove the remaining obligations. Rewrite `h` using `[← natCast_eq_zero_iff, ringChar.spec]`. Break down `hℓ.eq_one_or_self_of_dvd _ h with h1 | h1` into its components or cases. Establish `h2 : ((1 : ℕ) : X.residueField x) = 0` using `(ringChar.spec _ 1).2 (by rw [h1])`. Simplify using `at h2`.

Conclude with `h1`.
-/
theorem mem_fib_iff_of_prime {ℓ : ℕ} (hℓ : ℓ.Prime) (x : X) :
    x ∈ fib X ℓ ↔ x ∉ X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) := by
  refine ⟨notMem_basicOpen_of_mem_fib, fun h => ?_⟩
  rw [← natCast_eq_zero_iff, ringChar.spec] at h
  rcases hℓ.eq_one_or_self_of_dvd _ h with h1 | h1
  · have h2 : ((1 : ℕ) : X.residueField x) = 0 := (ringChar.spec _ 1).2 (by rw [h1])
    simp at h2
  · exact h1

/- English proof (translation)
Distinguish the cases in `hp : ℓ.Prime`. Establish `e : fib X ℓ = ((X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) : Set X))ᶜ` using `Set.ext fun x => mem_fib_iff_of_prime hp x`. Rewrite using `[e]`. Conclude with `(X.basicOpen _).isOpen.isClosed_compl`. Establish `e : fib X ℓ = ∅` using `Set.eq_empty_iff_forall_notMem.2 fun x hx => by`.

Establish `hx' : ringChar (X.residueField x) = ℓ` using `hx`. Break down `ringChar_eq_zero_or_prime x with h | h` into its components or cases. Conclude with `hℓ (hx'.symm.trans h)`. Conclude with `hp (hx' ▸ h)`. Rewrite using `[e]`.

Conclude with `isClosed_empty`.
-/
theorem isClosed_fib {ℓ : ℕ} (hℓ : ℓ ≠ 0) : IsClosed (fib X ℓ) := by
  by_cases hp : ℓ.Prime
  · have e : fib X ℓ = ((X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) : Set X))ᶜ :=
      Set.ext fun x => mem_fib_iff_of_prime hp x
    rw [e]
    exact (X.basicOpen _).isOpen.isClosed_compl
  · have e : fib X ℓ = ∅ := Set.eq_empty_iff_forall_notMem.2 fun x hx => by
      have hx' : ringChar (X.residueField x) = ℓ := hx
      rcases ringChar_eq_zero_or_prime x with h | h
      · exact hℓ (hx'.symm.trans h)
      · exact hp (hx' ▸ h)
    rw [e]
    exact isClosed_empty

/- English proof (translation)
Break down `ringChar_eq_zero_or_prime x with h0 | hp` into its components or cases. Conclude with `h0`. Establish `hx : x ∈ fib X (ringChar (X.residueField x))` using `rfl`. Establish `hy' : ringChar (X.residueField y) = ringChar (X.residueField x)` using `h.mem_closed (isClosed_fib hp.ne_zero) hx`. Conclude with `absurd (hy'.symm.trans hy) hp.ne_zero`.
-/
theorem mem_fib_zero_of_specializes {x y : X} (h : x ⤳ y) (hy : y ∈ fib X 0) : x ∈ fib X 0 := by
  rcases ringChar_eq_zero_or_prime x with h0 | hp
  · exact h0
  · have hx : x ∈ fib X (ringChar (X.residueField x)) := rfl
    have hy' : ringChar (X.residueField y) = ringChar (X.residueField x) :=
      h.mem_closed (isClosed_fib hp.ne_zero) hx
    exact absurd (hy'.symm.trans hy) hp.ne_zero

variable {k : Type} [CommRing k] {p : X ⟶ Sp k} {D : ℕ}

/- English proof (translation)
Introduce `h`. Establish `hb : X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) = ⊥` using `eq_bot_iff.2 fun x hx => (notMem_basicOpen_of_mem_fib (h.symm ▸ Set.mem_univ x : x ∈ fib X ℓ) hx).elim`. Establish `h0` using `(AlgebraicGeometry.basicOpen_eq_bot_iff _).1 hb`. Use `hX.charZero` as an intermediate fact. Conclude with `hℓ (Nat.cast_eq_zero.1 h0)`.
-/
theorem fib_ne_univ [IsIntegral X] (hX : IsArithVar p D) {ℓ : ℕ} (hℓ : ℓ ≠ 0) : fib X ℓ ≠ Set.univ := by
  intro h
  have hb : X.basicOpen ((ℓ : ℕ) : Γ(X, ⊤)) = ⊥ :=
    eq_bot_iff.2 fun x hx => (notMem_basicOpen_of_mem_fib (h.symm ▸ Set.mem_univ x : x ∈ fib X ℓ) hx).elim
  have h0 := (AlgebraicGeometry.basicOpen_eq_bot_iff _).1 hb
  have := hX.charZero
  exact hℓ (Nat.cast_eq_zero.1 h0)

/- English proof (translation)
Introduce `h0`. Use `hX.finite_residueField hx` as an intermediate fact. Conclude with `CharP.char_ne_zero_of_finite (X.residueField x) (ringChar (X.residueField x)) h0`.
-/
theorem closedPoint_notMem_fib_zero (hX : IsArithVar p D) (x : X) (hx : IsClosed ({x} : Set X)) :
    x ∉ fib X 0 := by
  intro h0
  have := hX.finite_residueField hx
  exact CharP.char_ne_zero_of_finite (X.residueField x) (ringChar (X.residueField x)) h0

/- English proof (translation)
Introduce `k _ X _ p D hX`. Use `hX.isNoetherian` as an intermediate fact. Use `⟨fun x => ?_, fun ℓ hℓ => isClosed_fib hℓ, fun x y h hy => mem_fib_zero_of_specializes h hy, fun ℓ => ?_, fun W hW => ?_⟩` and prove the remaining obligations. Break down `ringChar_eq_zero_or_prime x with h | h` into its components or cases. Conclude with `.inl h`.

Conclude with `.inr ⟨_, h, rfl⟩`. Break down `eq_or_ne ℓ 0 with rfl | hℓ` into its components or cases. Conclude with `dim_le_of_closedPoint_notMem (fun s hs => closedPoint_notMem_fib_zero hX s hs) hX.dim_eq.le`. Conclude with `dim_le_of_ne_univ (isClosed_fib hℓ) (fib_ne_univ hX hℓ) hX.dim_eq.le`. Take `⟨T, hTf, hTc, hTi, rfl⟩` from `NoetherianSpace.exists_finite_set_isClosed_irreducible hW`.

Set `ch : Set X → ℕ` to `fun t => if h : IsIrreducible t then ringChar (X.residueField (IsIrreducible.genericPoint h)) else 0`. Use `⟨(hTf.toFinset.image ch).filter Nat.Prime, fun ℓ hℓ => (Finset.mem_filter.1 hℓ).2, ?_⟩` and prove the remaining obligations. Introduce and unpack `x ⟨t, ht, hxt⟩`. Establish `hct : ch t = ringChar (X.residueField (IsIrreducible.genericPoint (hTi t ht)))` using `dif_pos (hTi t ht)`. Establish `hg` using `IsIrreducible.isGenericPoint_genericPoint (hTi t ht) (hTc t ht)`.

Establish `hsp` using `hg.specializes hxt`. Break down `ringChar_eq_zero_or_prime (IsIrreducible.genericPoint (hTi t ht)) with h0 | hp` into its components or cases. Use `left`. Conclude with `hsp.mem_closed isClosed_closure (subset_closure ⟨⟨t, ht, hg.mem⟩, h0⟩)`. Use `right`.

Use `Set.mem_iUnion₂.2 ⟨ch t, Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨t, hTf.mem_toFinset.2 ht, rfl⟩, hct ▸ hp⟩, ?_⟩` and prove the remaining obligations. Conclude with `hsp.mem_closed (isClosed_fib (hct ▸ hp.ne_zero)) hct.symm`.
-/
theorem fib_structure : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → (∀ x : X, x ∈ fib X 0 ∨ ∃ ℓ : ℕ, ℓ.Prime ∧ x ∈ fib X ℓ) ∧
      (∀ ℓ : ℕ, ℓ ≠ 0 → IsClosed (fib X ℓ)) ∧ (∀ x y : X, x ⤳ y → y ∈ fib X 0 → x ∈ fib X 0) ∧
      (∀ ℓ : ℕ, topologicalKrullDim (fib X ℓ) ≤ D) ∧
      ∀ W : Set X, IsClosed W → ∃ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime) ∧
        W ⊆ closure (W ∩ fib X 0) ∪ ⋃ ℓ ∈ S, fib X ℓ := by
  intro k _ X _ p D hX
  have := hX.isNoetherian
  refine ⟨fun x => ?_, fun ℓ hℓ => isClosed_fib hℓ, fun x y h hy => mem_fib_zero_of_specializes h hy,
    fun ℓ => ?_, fun W hW => ?_⟩
  · rcases ringChar_eq_zero_or_prime x with h | h
    · exact .inl h
    · exact .inr ⟨_, h, rfl⟩
  · rcases eq_or_ne ℓ 0 with rfl | hℓ
    · exact dim_le_of_closedPoint_notMem (fun s hs => closedPoint_notMem_fib_zero hX s hs) hX.dim_eq.le
    · exact dim_le_of_ne_univ (isClosed_fib hℓ) (fib_ne_univ hX hℓ) hX.dim_eq.le
  · classical
    obtain ⟨T, hTf, hTc, hTi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hW
    let ch : Set X → ℕ := fun t =>
      if h : IsIrreducible t then ringChar (X.residueField (IsIrreducible.genericPoint h)) else 0
    refine ⟨(hTf.toFinset.image ch).filter Nat.Prime, fun ℓ hℓ => (Finset.mem_filter.1 hℓ).2, ?_⟩
    rintro x ⟨t, ht, hxt⟩
    have hct : ch t = ringChar (X.residueField (IsIrreducible.genericPoint (hTi t ht))) := dif_pos (hTi t ht)
    have hg := IsIrreducible.isGenericPoint_genericPoint (hTi t ht) (hTc t ht)
    have hsp := hg.specializes hxt
    rcases ringChar_eq_zero_or_prime (IsIrreducible.genericPoint (hTi t ht)) with h0 | hp
    · left
      exact hsp.mem_closed isClosed_closure (subset_closure ⟨⟨t, ht, hg.mem⟩, h0⟩)
    · right
      refine Set.mem_iUnion₂.2 ⟨ch t, Finset.mem_filter.2
        ⟨Finset.mem_image.2 ⟨t, hTf.mem_toFinset.2 ht, rfl⟩, hct ▸ hp⟩, ?_⟩
      exact hsp.mem_closed (isClosed_fib (hct ▸ hp.ne_zero)) hct.symm

end GlobalTheory.IntFib
