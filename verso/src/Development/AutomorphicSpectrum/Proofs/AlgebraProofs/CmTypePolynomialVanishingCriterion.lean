import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigCoordApply
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjSumSumEmbeddingsEqTrace

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.Block

/- English proof (translation)
Rewrite using `[← Finset.sum_filter_of_ne (p := D) (fun x _ hx => by_contra fun hD => hx (h x hD))]`. Conclude with `Finset.sum_subtype _ (fun x => by simp) G`.
-/
theorem sum_eq_sum_subtype {α β : Type} [Fintype α] [AddCommMonoid β] (D : α → Prop)
    [Fintype {s // D s}] (G : α → β) (h : ∀ s, ¬ D s → G s = 0) :
    ∑ s, G s = ∑ s : {s // D s}, G s.1 := by
  classical
  rw [← Finset.sum_filter_of_ne (p := D) (fun x _ hx => by_contra fun hD => hx (h x hD))]
  exact Finset.sum_subtype _ (fun x => by simp) G

section

variable {E : Type} [Field E] [NumberField E] {C : Type} [Field C] {w : Valuation C ℝ≥0}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_freeLattice {S : Type} {a : S → w.valuationSubring} {r : ℕ} {x : S → Fin r → C} :
    x ∈ freeLattice a r ↔ ∀ i, ∃ f : Polynomial w.valuationSubring, ∀ s,
      x s i = ((f.eval (a s) : w.valuationSubring) : C) := Iff.rfl

def valSpan (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring)) :
    Submodule w.valuationSubring ((E →+* C) → w.valuationSubring) :=
  Submodule.span w.valuationSubring (Set.range fun a : 𝓞 E => fun s => emb s a)

/- English proof (translation)
Unfold `valSpan at hf hg ⊢`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x h`. Take `⟨a, rfl⟩` from `h`. Proceed by induction on `hg using Submodule.span_induction with`.

Consider the case `mem y h`. Take `⟨b, rfl⟩` from `h`. Conclude with `Submodule.subset_span ⟨a * b, by funext s; simp⟩`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [mul_add]`.

Conclude with `add_mem hy hz`. Consider the case `smul c y _ hy => rw [mul_smul_comm]`. Conclude with `Submodule.smul_mem _ c hy`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [add_mul]`.

Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem mul_mem_valSpan (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring))
    {f g : (E →+* C) → w.valuationSubring} (hf : f ∈ valSpan emb) (hg : g ∈ valSpan emb) :
    f * g ∈ valSpan emb := by
  unfold valSpan at hf hg ⊢
  induction hf using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a, rfl⟩ := h
    induction hg using Submodule.span_induction with
    | mem y h =>
      obtain ⟨b, rfl⟩ := h
      exact Submodule.subset_span ⟨a * b, by funext s; simp⟩
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

variable {M : Type} [AddCommGroup M] [Module C M] [Module w.valuationSubring M]
  [IsScalarTower w.valuationSubring C M] {ρ : 𝓞 E →+* Module.End C M}
  {X : Submodule w.valuationSubring M} {N : ℕ} {t : Fin N → M}

/- English proof (translation)
Establish `e` using `congrArg (fun u => ρ u (t j)) ((RingOfIntegers.basis E).sum_repr a)`. Simplify using `only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply] at e`. Rewrite using `[← e]`. Use `sum_mem fun k _ => zsmul_mem ?_ _` and prove the remaining obligations. Rewrite using `[h.2.2]`.

Conclude with `Submodule.subset_span ⟨(j, k), rfl⟩`.
-/
theorem rho_mem (h : HT.IsFreeOn ρ X t) (a : 𝓞 E) (j : Fin N) : ρ a (t j) ∈ X := by
  have e := congrArg (fun u => ρ u (t j)) ((RingOfIntegers.basis E).sum_repr a)
  simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply] at e
  rw [← e]
  refine sum_mem fun k _ => zsmul_mem ?_ _
  rw [h.2.2]
  exact Submodule.subset_span ⟨(j, k), rfl⟩

/- English proof (translation)
Rewrite using `[eigCoord_apply]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (HT.LatBasic.eigProj_mem ρ s _)`.
-/
theorem eigCoord_mem (s : E →+* C) (v : Fin N → C) : eigCoord ρ t s v ∈ HT.eigSp ρ s := by
  rw [eigCoord_apply]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (HT.LatBasic.eigProj_mem ρ s _)

/- English proof (translation)
Rewrite `hy` using `[h.2.2]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨⟨j, k⟩, rfl⟩` from `hx`. Use `⟨fun i s => if i = j then emb s (RingOfIntegers.basis E k) else 0, fun i => ?_, fun s => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hij : i = j`. Simplify using `only [hij, if_true]`. Conclude with `Submodule.subset_span ⟨_, rfl⟩`. Simplify using `only [hij, if_false]`. Conclude with `zero_mem (valSpan emb)`.

Rewrite using `[HodgeDeterminantLattice.eigProj_act, Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]`. Simplify using `[hemb]`. Consider the case `zero => exact ⟨0, fun _ => zero_mem _, fun s => by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨F, hF, e⟩` from `hx`.

Take `⟨G, hG, e'⟩` from `hy`. Use `⟨F + G, fun j => add_mem (hF j) (hG j), fun s => ?_⟩` and prove the remaining obligations. Simplify using `[e s, e' s, add_smul, Finset.sum_add_distrib]`. Consider the case `smul c x _ hx`. Take `⟨F, hF, e⟩` from `hx`.

Use `⟨c • F, fun j => Submodule.smul_mem _ c (hF j), fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[← algebraMap_smul C c x, map_smul, e s, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`. Both sides reduce to the same expression.
-/
theorem exists_coord (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring))
    (hemb : ∀ s (a : 𝓞 E), ((emb s a : w.valuationSubring) : C) = s (a : E))
    (h : HT.IsFreeOn ρ X t) {y : M} (hy : y ∈ X) :
    ∃ F : Fin N → (E →+* C) → w.valuationSubring, (∀ j, F j ∈ valSpan emb) ∧
      ∀ s, HT.eigProj ρ s y = ∑ j, ((F j s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) := by
  classical
  rw [h.2.2] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨j, k⟩, rfl⟩ := hx
    refine ⟨fun i s => if i = j then emb s (RingOfIntegers.basis E k) else 0, fun i => ?_,
      fun s => ?_⟩
    · by_cases hij : i = j
      · simp only [hij, if_true]
        exact Submodule.subset_span ⟨_, rfl⟩
      · simp only [hij, if_false]
        exact zero_mem (valSpan emb)
    · rw [HodgeDeterminantLattice.eigProj_act, Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
      simp [hemb]
  | zero => exact ⟨0, fun _ => zero_mem _, fun s => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, hF, e⟩ := hx
    obtain ⟨G, hG, e'⟩ := hy
    refine ⟨F + G, fun j => add_mem (hF j) (hG j), fun s => ?_⟩
    simp [e s, e' s, add_smul, Finset.sum_add_distrib]
  | smul c x _ hx =>
    obtain ⟨F, hF, e⟩ := hx
    refine ⟨c • F, fun j => Submodule.smul_mem _ c (hF j), fun s => ?_⟩
    rw [← algebraMap_smul C c x, map_smul, e s, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul]
    rfl

/- English proof (translation)
Unfold `valSpan at hF`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`. Establish `e : ∑ s : E →+* C, ((emb s a : w.valuationSubring) : C) • HT.eigProj ρ s (t j) = ρ a (t j)`.

Establish `h1` using `congrArg (fun T : Module.End C M => T (ρ a (t j))) (HT.sum_eigProj_eq_one C M E ρ hcard)`. Simplify using `only [LinearMap.sum_apply, HodgeDeterminantLattice.eigProj_act, Module.End.one_apply] at h1`. Simplify `h1` using `only [hemb]`. Simplify `rho_mem h a j` using `only [e]`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy`. Simplify using `only [Pi.add_apply, AddMemClass.coe_add, add_smul, Finset.sum_add_distrib]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx`. Establish `e : ∑ s : E →+* C, (((c • x) s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) = c • ∑ s : E →+* C, ((x s : w.valuationSubring) : C) • HT.eigProj ρ s (t j)`.

Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul C c (((x s : w.valuationSubring) : C) • HT.eigProj ρ s (t j)), smul_smul]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem sum_smul_mem [CharZero C] [Fintype (E →+* C)]
    (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring))
    (hemb : ∀ s (a : 𝓞 E), ((emb s a : w.valuationSubring) : C) = s (a : E))
    (hcard : Fintype.card (E →+* C) = Module.finrank ℚ E)
    (h : HT.IsFreeOn ρ X t) (j : Fin N) {F : (E →+* C) → w.valuationSubring}
    (hF : F ∈ valSpan emb) :
    ∑ s, ((F s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) ∈ X := by
  unfold valSpan at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    have e : ∑ s : E →+* C, ((emb s a : w.valuationSubring) : C) • HT.eigProj ρ s (t j) =
        ρ a (t j) := by
      have h1 := congrArg (fun T : Module.End C M => T (ρ a (t j)))
        (HT.sum_eigProj_eq_one C M E ρ hcard)
      simp only [LinearMap.sum_apply, HodgeDeterminantLattice.eigProj_act, Module.End.one_apply] at h1
      simpa only [hemb] using h1
    simpa only [e] using rho_mem h a j
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply, AddMemClass.coe_add, add_smul, Finset.sum_add_distrib]
    exact add_mem hx hy
  | smul c x _ hx =>
    have e : ∑ s : E →+* C, (((c • x) s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) =
        c • ∑ s : E →+* C, ((x s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← algebraMap_smul C c (((x s : w.valuationSubring) : C) • HT.eigProj ρ s (t j)), smul_smul]
      rfl
    rw [e]
    exact Submodule.smul_mem _ c hx

end

/- English proof (translation)
Introduce `E _ _ C _ _ w _ emb hemb hcard D π H M _ _ _ _ ρ X N t hfree _`. Establish `hind : (fun s => if D s then (1 : w.valuationSubring) else 0) ∈ valSpan emb` using `(H _ (fun s hs => if_neg hs)).1 ⟨1, fun s hs => by simp [hs]⟩`. Establish `hpoly : ∀ F ∈ valSpan emb, ∃ g : Polynomial w.valuationSubring, ∀ s, D s → F s = g.eval (emb s π)`. Introduce `F hF`. Establish `hm` using `mul_mem_valSpan emb hind hF`.

Take `⟨g, hg⟩` from `(H _ (fun s hs => by simp [hs])).2 hm`. Conclude with `⟨g, fun s hs => by simpa [hs] using hg s hs⟩`. Use `⟨fun f => ⟨fun hx => ?_, fun hf => ?_⟩, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨F, hF, e⟩` from `exists_coord emb hemb hfree hx`. Establish `hD : ∀ s : {s // D s}, HT.eigProj ρ s.1 (∑ s, eigCoord ρ t s.1 (f s)) = eigCoord ρ t s.1 (f s)`.

Introduce `s`. Rewrite using `[map_sum, Finset.sum_eq_single s]`. Conclude with `HT.LatBasic.eigProj_of_mem (eigCoord_mem _ _)`. Introduce `s' _ hne`. Conclude with `HT.LatBasic.eigProj_of_ne (fun e => hne (Subtype.ext e.symm)) (eigCoord_mem _ _)`.

Simplify using the standard rewrite rules. Establish `hnD : ∀ s, ¬ D s → HT.eigProj ρ s (∑ s, eigCoord ρ t s.1 (f s)) = 0`. Introduce `s hs`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_eq_zero fun s' _ => HT.LatBasic.eigProj_of_ne (fun e : s = s'.1 => hs (by rw [e]; exact s'.2)) (eigCoord_mem _ _)`.

Establish `hF0 : ∀ j s, ¬ D s → F j s = 0`. Introduce `j s hs`. Establish `h1` using `Fintype.linearIndependent_iff.1 (HodgeDeterminantLattice.linearIndependent_eigProj s hfree) (fun j => ((F j s : w.valuationSubring) : C)) (by rw [← e s, hnD s hs]) j`. Conclude with `Subtype.ext h1`. Establish `hcoord : ∀ (s : {s // D s}) j, f s j = ((F j s.1 : w.valuationSubring) : C)`.

Introduce `s j`. Establish `h0` using `(hD s).symm.trans (e s.1)`. Rewrite `h0` using `[eigCoord_apply]`. Establish `h1` using `Fintype.linearIndependent_iff.1 (HodgeDeterminantLattice.linearIndependent_eigProj s.1 hfree) (fun j => f s j - ((F j s.1 : w.valuationSubring) : C)) (by simp only [sub_smul, Finset.sum_sub_distrib, h0, sub_self]) j`. Conclude with `sub_eq_zero.1 h1`.

Use `mem_freeLattice.2 fun j => ?_` and prove the remaining obligations. Take `⟨g, hg⟩` from `(H (F j) (hF0 j)).2 (hF j)`. Conclude with `⟨g, fun s => by rw [hcoord s j, hg s.1 s.2]⟩`. Use `choose g hg using mem_freeLattice.1 hf`. Set `F : Fin N → (E →+* C) → w.valuationSubring` to `fun j s => if D s then (g j).eval (emb s π) else 0`.

Establish `hFm : ∀ j, F j ∈ valSpan emb` using `fun j => (H (F j) (fun s hs => if_neg hs)).1 ⟨g j, fun s hs => if_pos hs⟩`. Establish `key : ∑ j, ∑ s, ((F j s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) ∈ X` using `sum_mem fun j _ => sum_smul_mem emb hemb hcard hfree j (hFm j)`. Establish `e : ∑ s, eigCoord ρ t s.1 (f s) = ∑ j, ∑ s, ((F j s : w.valuationSubring) : C) • HT.eigProj ρ s (t j)`. Simplify using `only [eigCoord_apply]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[sum_eq_sum_subtype D _ (fun s hs => by simp [F, hs])]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using `only [F, if_pos s.2, hg j s]`. Rewrite using `[e]`.

Conclude with `key`. Take `⟨F, hF, e⟩` from `exists_coord emb hemb hfree hy`. Use `⟨fun s j => ((F j s.1 : w.valuationSubring) : C), mem_freeLattice.2 fun j => ?_, fun s => ?_⟩` and prove the remaining obligations. Take `⟨g, hg⟩` from `hpoly _ (hF j)`. Conclude with `⟨g, fun s => by rw [hg s.1 s.2]⟩`.

Rewrite using `[e, eigCoord_apply]`.
-/
theorem block_freeLattice : ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] (w : Valuation C ℝ≥0) [Fintype (E →+* C)] (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring)), (∀ s (a : 𝓞 E), ((emb s a : w.valuationSubring) : C) = s (a : E)) → Fintype.card (E →+* C) = Module.finrank ℚ E → ∀ (D : (E →+* C) → Prop) (π : 𝓞 E), (∀ f : (E →+* C) → w.valuationSubring, (∀ s, ¬ D s → f s = 0) → ((∃ g : Polynomial w.valuationSubring, ∀ s, D s → f s = g.eval (emb s π)) ↔ f ∈ Submodule.span w.valuationSubring (Set.range fun a : 𝓞 E => fun s => emb s a))) → ∀ (M : Type) [AddCommGroup M] [Module C M] [Module w.valuationSubring M] [IsScalarTower w.valuationSubring C M] (ρ : 𝓞 E →+* Module.End C M) (X : Submodule w.valuationSubring M) (N : ℕ) (t : Fin N → M), HT.IsFreeOn ρ X t → ∀ [Fintype {s // D s}], (∀ f : {s // D s} → Fin N → C, (∑ s, eigCoord ρ t s.1 (f s)) ∈ X ↔ f ∈ freeLattice (fun s : {s // D s} => emb s.1 π) N) ∧ (∀ y ∈ X, ∃ f ∈ freeLattice (fun s : {s // D s} => emb s.1 π) N, ∀ s, HT.eigProj ρ s.1 y = eigCoord ρ t s.1 (f s)) := by
  intro E _ _ C _ _ w _ emb hemb hcard D π H M _ _ _ _ ρ X N t hfree _
  classical
  have hind : (fun s => if D s then (1 : w.valuationSubring) else 0) ∈ valSpan emb :=
    (H _ (fun s hs => if_neg hs)).1 ⟨1, fun s hs => by simp [hs]⟩
  have hpoly : ∀ F ∈ valSpan emb, ∃ g : Polynomial w.valuationSubring,
      ∀ s, D s → F s = g.eval (emb s π) := by
    intro F hF
    have hm := mul_mem_valSpan emb hind hF
    obtain ⟨g, hg⟩ := (H _ (fun s hs => by simp [hs])).2 hm
    exact ⟨g, fun s hs => by simpa [hs] using hg s hs⟩
  refine ⟨fun f => ⟨fun hx => ?_, fun hf => ?_⟩, fun y hy => ?_⟩
  · obtain ⟨F, hF, e⟩ := exists_coord emb hemb hfree hx
    have hD : ∀ s : {s // D s}, HT.eigProj ρ s.1 (∑ s, eigCoord ρ t s.1 (f s)) =
        eigCoord ρ t s.1 (f s) := by
      intro s
      rw [map_sum, Finset.sum_eq_single s]
      · exact HT.LatBasic.eigProj_of_mem (eigCoord_mem _ _)
      · intro s' _ hne
        exact HT.LatBasic.eigProj_of_ne (fun e => hne (Subtype.ext e.symm)) (eigCoord_mem _ _)
      · simp
    have hnD : ∀ s, ¬ D s → HT.eigProj ρ s (∑ s, eigCoord ρ t s.1 (f s)) = 0 := by
      intro s hs
      rw [map_sum]
      exact Finset.sum_eq_zero fun s' _ =>
        HT.LatBasic.eigProj_of_ne (fun e : s = s'.1 => hs (by rw [e]; exact s'.2)) (eigCoord_mem _ _)
    have hF0 : ∀ j s, ¬ D s → F j s = 0 := by
      intro j s hs
      have h1 := Fintype.linearIndependent_iff.1 (HodgeDeterminantLattice.linearIndependent_eigProj s hfree)
        (fun j => ((F j s : w.valuationSubring) : C)) (by rw [← e s, hnD s hs]) j
      exact Subtype.ext h1
    have hcoord : ∀ (s : {s // D s}) j, f s j = ((F j s.1 : w.valuationSubring) : C) := by
      intro s j
      have h0 := (hD s).symm.trans (e s.1)
      rw [eigCoord_apply] at h0
      have h1 := Fintype.linearIndependent_iff.1 (HodgeDeterminantLattice.linearIndependent_eigProj s.1 hfree)
        (fun j => f s j - ((F j s.1 : w.valuationSubring) : C))
        (by simp only [sub_smul, Finset.sum_sub_distrib, h0, sub_self]) j
      exact sub_eq_zero.1 h1
    refine mem_freeLattice.2 fun j => ?_
    obtain ⟨g, hg⟩ := (H (F j) (hF0 j)).2 (hF j)
    exact ⟨g, fun s => by rw [hcoord s j, hg s.1 s.2]⟩
  · choose g hg using mem_freeLattice.1 hf
    let F : Fin N → (E →+* C) → w.valuationSubring :=
      fun j s => if D s then (g j).eval (emb s π) else 0
    have hFm : ∀ j, F j ∈ valSpan emb := fun j =>
      (H (F j) (fun s hs => if_neg hs)).1 ⟨g j, fun s hs => if_pos hs⟩
    have key : ∑ j, ∑ s, ((F j s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) ∈ X :=
      sum_mem fun j _ => sum_smul_mem emb hemb hcard hfree j (hFm j)
    have e : ∑ s, eigCoord ρ t s.1 (f s) =
        ∑ j, ∑ s, ((F j s : w.valuationSubring) : C) • HT.eigProj ρ s (t j) := by
      simp only [eigCoord_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [sum_eq_sum_subtype D _ (fun s hs => by simp [F, hs])]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [F, if_pos s.2, hg j s]
    rw [e]
    exact key
  · obtain ⟨F, hF, e⟩ := exists_coord emb hemb hfree hy
    refine ⟨fun s j => ((F j s.1 : w.valuationSubring) : C), mem_freeLattice.2 fun j => ?_,
      fun s => ?_⟩
    · obtain ⟨g, hg⟩ := hpoly _ (hF j)
      exact ⟨g, fun s => by rw [hg s.1 s.2]⟩
    · rw [e, eigCoord_apply]

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.Block
