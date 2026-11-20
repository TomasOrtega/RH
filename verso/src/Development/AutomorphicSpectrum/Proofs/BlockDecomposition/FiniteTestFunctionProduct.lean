import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFamInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisExtra
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

noncomputable section

namespace GlobalTheory.CompanionTheory.FinActS

/- English proof (translation)
Establish `hu : (Set.univ : Set (α ⊕ β)) = Set.range Sum.inl ∪ Set.range Sum.inr`. Apply the tactic sequence `ext i; cases i <;> simp`. Establish `e₁ : (Set.range (Sum.inl : α → α ⊕ β) ∩ Function.mulSupport f).Finite`. Use `(h₁.image Sum.inl).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨x, rfl⟩, hx⟩`.

Conclude with `⟨x, hx, rfl⟩`. Establish `e₂ : (Set.range (Sum.inr : β → α ⊕ β) ∩ Function.mulSupport f).Finite`. Use `(h₂.image Sum.inr).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨x, rfl⟩, hx⟩`. Conclude with `⟨x, hx, rfl⟩`.

Establish `hd : Disjoint (Set.range (Sum.inl : α → α ⊕ β)) (Set.range (Sum.inr : β → α ⊕ β))` using `Set.disjoint_left.2 (by rintro _ ⟨x, rfl⟩ ⟨y, hy⟩; cases hy)`. Rewrite using `[← finprod_mem_univ, hu, finprod_mem_union' hd e₁ e₂, finprod_mem_range Sum.inl_injective, finprod_mem_range Sum.inr_injective]`.
-/
theorem finprod_sum_split {α β M : Type*} [CommMonoid M] (f : α ⊕ β → M)
    (h₁ : (Function.mulSupport fun x => f (Sum.inl x)).Finite)
    (h₂ : (Function.mulSupport fun x => f (Sum.inr x)).Finite) :
    ∏ᶠ i, f i = (∏ᶠ x, f (Sum.inl x)) * ∏ᶠ x, f (Sum.inr x) := by
  have hu : (Set.univ : Set (α ⊕ β)) = Set.range Sum.inl ∪ Set.range Sum.inr := by
    ext i; cases i <;> simp
  have e₁ : (Set.range (Sum.inl : α → α ⊕ β) ∩ Function.mulSupport f).Finite := by
    refine (h₁.image Sum.inl).subset ?_
    rintro _ ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, hx, rfl⟩
  have e₂ : (Set.range (Sum.inr : β → α ⊕ β) ∩ Function.mulSupport f).Finite := by
    refine (h₂.image Sum.inr).subset ?_
    rintro _ ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, hx, rfl⟩
  have hd : Disjoint (Set.range (Sum.inl : α → α ⊕ β)) (Set.range (Sum.inr : β → α ⊕ β)) :=
    Set.disjoint_left.2 (by rintro _ ⟨x, rfl⟩ ⟨y, hy⟩; cases hy)
  rw [← finprod_mem_univ, hu, finprod_mem_union' hd e₁ e₂,
    finprod_mem_range Sum.inl_injective, finprod_mem_range Sum.inr_injective]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

/- English proof (translation)
Use `set g₁ : Pl E → ℂ := fun w => φ₁ w (atW w y) with hg₁`. Use `set g₂ : Pl E → ℂ := fun w => if IsSplitAt w then φ₂ w (atW w (thP E a b y)) else 1 with hg₂`. Establish `o₁ : ∀ᶠ w in cofinite, g₁ w = 1` using `by filter_upwards [GlobalTheory.CompanionTheory.FinTestTw.eventually_eq_indicator h₁, (GlobalTheory.CompanionTheory.FinTestTw.isRestrW a b).eventually_mem y] with w e m`. Establish `m' : atW w y ∈ (K2 a b w : Set (GLw a w × GLw b w))` using `m`. Simplify using `only [hg₁]`.

Rewrite using `[e, Set.indicator_of_mem m']`. Simplify using the standard rewrite rules. Establish `o₂ : ∀ᶠ w in cofinite, φ₂ w (atW w (thP E a b y)) = 1` using `by filter_upwards [GlobalTheory.CompanionTheory.FinTestTw.eventually_eq_indicator h₂, (GlobalTheory.CompanionTheory.FinTestTw.isRestrW a b).eventually_mem (thP E a b y)] with w e m`. Establish `m' : atW w (thP E a b y) ∈ (K2 a b w : Set (GLw a w × GLw b w))` using `m`. Rewrite using `[e, Set.indicator_of_mem m']`.

Simplify using the standard rewrite rules. Establish `f₁ : (Function.mulSupport g₁).Finite` using `eventually_cofinite.1 o₁`. Establish `f₂' : (Function.mulSupport fun w => φ₂ w (atW w (thP E a b y))).Finite` using `eventually_cofinite.1 o₂`. Establish `f₂ : (Function.mulSupport g₂).Finite`. Use `f₂'.subset fun w hw => ?_` and prove the remaining obligations.

Distinguish the cases in `hs : IsSplitAt w`. Simplify `hw` using `[hg₂, hs, Function.mem_mulSupport]`. Conclude with `absurd (by simp [hg₂, hs]) hw`. Establish `l₁ : (Function.mulSupport fun x : {w // w ∈ S} => g₁ x.1).Finite` using `(f₁.preimage Subtype.val_injective.injOn).subset fun x hx => hx`. Establish `l₂ : (Function.mulSupport fun x : {w // w ∈ S ∧ IsSplitAt w} => φ₂ x.1 (atW x.1 (thP E a b y))).Finite` using `(f₂'.preimage Subtype.val_injective.injOn).subset fun x hx => hx`.

Establish `hs : ∏ᶠ i : Slot S, sf φ₁ φ₂ i (i.cp a b y) = (∏ᶠ x : {w // w ∈ S}, g₁ x.1) * ∏ᶠ x : {w // w ∈ S ∧ IsSplitAt w}, φ₂ x.1 (atW x.1 (thP E a b y))` using `finprod_sum_split (fun i : Slot S => sf φ₁ φ₂ i (i.cp a b y)) l₁ l₂`. Establish `c₁ : ∏ᶠ x : {w // w ∈ S}, g₁ x.1 = ∏ᶠ w ∈ S, g₁ w` using `finprod_subtype_eq_finprod_cond (f := g₁) (fun w => w ∈ S)`. Establish `c₂ : ∏ᶠ x : {w // w ∈ S ∧ IsSplitAt w}, φ₂ x.1 (atW x.1 (thP E a b y)) = ∏ᶠ w ∈ S, g₂ w`. Establish `e₀ : ∏ᶠ x : {w // w ∈ S ∧ IsSplitAt w}, φ₂ x.1 (atW x.1 (thP E a b y)) = ∏ᶠ x : {w // w ∈ S ∧ IsSplitAt w}, g₂ x.1` using `finprod_congr fun x => by simp [hg₂, x.2.2]`. Rewrite using `[e₀, finprod_subtype_eq_finprod_cond (f := g₂) (fun w => w ∈ S ∧ IsSplitAt w)]`.

Use `finprod_mem_inter_mulSupport_eq' g₂ {w | w ∈ S ∧ IsSplitAt w} S fun w hw => ?_` and prove the remaining obligations. Establish `hsp : IsSplitAt w`. Assume the negation of the conclusion as `hn`. Conclude with `hw (by simp [hg₂, hn])`. Conclude with `⟨fun h => h.1, fun h => ⟨h, hsp⟩⟩`.

Rewrite using `[hs, c₁, c₂]`. Conclude with `finprod_mem_mul_distrib' (f₁.subset Set.inter_subset_right) (f₂.subset Set.inter_subset_right)`.
-/
theorem finFn_eq_finprod_factor {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂)
    (y : Hf E a b) : finFn S φ₁ φ₂ y = ∏ᶠ i : Slot S, sf φ₁ φ₂ i (i.cp a b y) := by
  set g₁ : Pl E → ℂ := fun w => φ₁ w (atW w y) with hg₁
  set g₂ : Pl E → ℂ := fun w => if IsSplitAt w then φ₂ w (atW w (thP E a b y)) else 1 with hg₂
  have o₁ : ∀ᶠ w in cofinite, g₁ w = 1 := by
    filter_upwards [GlobalTheory.CompanionTheory.FinTestTw.eventually_eq_indicator h₁, (GlobalTheory.CompanionTheory.FinTestTw.isRestrW a b).eventually_mem y] with w e m
    have m' : atW w y ∈ (K2 a b w : Set (GLw a w × GLw b w)) := m
    simp only [hg₁]
    rw [e, Set.indicator_of_mem m']
    simp
  have o₂ : ∀ᶠ w in cofinite, φ₂ w (atW w (thP E a b y)) = 1 := by
    filter_upwards [GlobalTheory.CompanionTheory.FinTestTw.eventually_eq_indicator h₂,
      (GlobalTheory.CompanionTheory.FinTestTw.isRestrW a b).eventually_mem (thP E a b y)] with w e m
    have m' : atW w (thP E a b y) ∈ (K2 a b w : Set (GLw a w × GLw b w)) := m
    rw [e, Set.indicator_of_mem m']
    simp
  have f₁ : (Function.mulSupport g₁).Finite := eventually_cofinite.1 o₁
  have f₂' : (Function.mulSupport fun w => φ₂ w (atW w (thP E a b y))).Finite := eventually_cofinite.1 o₂
  have f₂ : (Function.mulSupport g₂).Finite := by
    refine f₂'.subset fun w hw => ?_
    by_cases hs : IsSplitAt w
    · simpa [hg₂, hs, Function.mem_mulSupport] using hw
    · exact absurd (by simp [hg₂, hs]) hw
  have l₁ : (Function.mulSupport fun x : {w // w ∈ S} => g₁ x.1).Finite :=
    (f₁.preimage Subtype.val_injective.injOn).subset fun x hx => hx
  have l₂ : (Function.mulSupport fun x : {w // w ∈ S ∧ IsSplitAt w} => φ₂ x.1 (atW x.1 (thP E a b y))).Finite :=
    (f₂'.preimage Subtype.val_injective.injOn).subset fun x hx => hx
  have hs : ∏ᶠ i : Slot S, sf φ₁ φ₂ i (i.cp a b y) =
      (∏ᶠ x : {w // w ∈ S}, g₁ x.1) * ∏ᶠ x : {w // w ∈ S ∧ IsSplitAt w}, φ₂ x.1 (atW x.1 (thP E a b y)) :=
    finprod_sum_split (fun i : Slot S => sf φ₁ φ₂ i (i.cp a b y)) l₁ l₂
  have c₁ : ∏ᶠ x : {w // w ∈ S}, g₁ x.1 = ∏ᶠ w ∈ S, g₁ w :=
    finprod_subtype_eq_finprod_cond (f := g₁) (fun w => w ∈ S)
  have c₂ : ∏ᶠ x : {w // w ∈ S ∧ IsSplitAt w}, φ₂ x.1 (atW x.1 (thP E a b y)) = ∏ᶠ w ∈ S, g₂ w := by
    have e₀ : ∏ᶠ x : {w // w ∈ S ∧ IsSplitAt w}, φ₂ x.1 (atW x.1 (thP E a b y)) =
        ∏ᶠ x : {w // w ∈ S ∧ IsSplitAt w}, g₂ x.1 :=
      finprod_congr fun x => by simp [hg₂, x.2.2]
    rw [e₀, finprod_subtype_eq_finprod_cond (f := g₂) (fun w => w ∈ S ∧ IsSplitAt w)]
    refine finprod_mem_inter_mulSupport_eq' g₂ {w | w ∈ S ∧ IsSplitAt w} S fun w hw => ?_
    have hsp : IsSplitAt w := by
      by_contra hn
      exact hw (by simp [hg₂, hn])
    exact ⟨fun h => h.1, fun h => ⟨h, hsp⟩⟩
  rw [hs, c₁, c₂]
  exact finprod_mem_mul_distrib' (f₁.subset Set.inter_subset_right) (f₂.subset Set.inter_subset_right)

end GlobalTheory.CompanionTheory.FinActS

end
