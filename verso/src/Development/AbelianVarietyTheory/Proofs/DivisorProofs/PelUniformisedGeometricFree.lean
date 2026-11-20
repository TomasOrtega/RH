import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockParOpp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPartMul
open MeasureTheory Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.OrbDesc

variable {H : Type} [Group H]

/- English proof (translation)
Take `⟨t, l, ht, hl, h⟩` from `DoubleCoset.mk_out_eq_mul T L x`. Rewrite using `[h, DoubleCoset.eq]`. Conclude with `⟨t⁻¹, P.inv_mem (hTP ht), l⁻¹, L.inv_mem hl, by group⟩`.
-/
theorem mk_out_of_le {T P L : Subgroup H} (hTP : T ≤ P) (x : H) :
    DoubleCoset.mk P L (Quotient.out (DoubleCoset.mk T L x)) = DoubleCoset.mk P L x := by
  obtain ⟨t, l, ht, hl, h⟩ := DoubleCoset.mk_out_eq_mul T L x
  rw [h, DoubleCoset.eq]
  exact ⟨t⁻¹, P.inv_mem (hTP ht), l⁻¹, L.inv_mem hl, by group⟩

/- English proof (translation)
Unfold `GlobalTheory.LKLoc.locPart`. Use extensionality with `g`. Simplify using `only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hg, k, ⟨_, l, hl, rfl⟩, rfl⟩`.

Conclude with `⟨hg, l, hl, by group⟩`. Introduce and unpack `⟨hg, l, hl, rfl⟩`. Use `⟨hg, y * l * y⁻¹, ⟨?_, l, hl, rfl⟩, by group⟩` and prove the remaining obligations. Establish `e : y * l * y⁻¹ = p⁻¹ * (p * y * l * (p * y)⁻¹) * p` using `by group`. Rewrite using `[e]`.

Conclude with `P.mul_mem (P.mul_mem (P.inv_mem hp) (hTP hg)) hp`.
-/
theorem locPart_inf_conj {T P L : Subgroup H} (hTP : T ≤ P) {p : H} (hp : p ∈ P) (y : H) :
    GlobalTheory.LKLoc.locPart T (P ⊓ L.map (MulAut.conj y).toMonoidHom) p = GlobalTheory.LKLoc.locPart T L (p * y) := by
  unfold GlobalTheory.LKLoc.locPart
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hg, k, ⟨_, l, hl, rfl⟩, rfl⟩
    exact ⟨hg, l, hl, by group⟩
  · rintro ⟨hg, l, hl, rfl⟩
    refine ⟨hg, y * l * y⁻¹, ⟨?_, l, hl, rfl⟩, by group⟩
    have e : y * l * y⁻¹ = p⁻¹ * (p * y * l * (p * y)⁻¹) * p := by group
    rw [e]
    exact P.mul_mem (P.mul_mem (P.inv_mem hp) (hTP hg)) hp

/- English proof (translation)
Use `set F : DoubleCoset.Quotient (T : Set H) (L : Set H) → ℂ := fun q => wt T L U Ψ (Quotient.out q) with hF`. Use `set π : DoubleCoset.Quotient (T : Set H) (L : Set H) → DoubleCoset.Quotient (P : Set H) (L : Set H) := fun q => DoubleCoset.mk P L (Quotient.out q) with hπ`. Establish `hdef : dsum T L U Ψ = ∑ᶠ q, F q` using `rfl`. Rewrite using `[hdef]`. Distinguish the cases in `hfin : (Function.support F).Finite`.

Use `swap`. Conclude with `finsum_of_infinite_support hfin`. Rewrite using `[finsum_eq_sum F hfin, ← Finset.sum_fiberwise_of_maps_to (g := π) (t := hfin.toFinset.image π) (fun _ h => Finset.mem_image_of_mem _ h)]`. Use `Finset.sum_eq_zero fun r _ => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩ : ∃ y, DoubleCoset.mk P L y = r` from `⟨Quotient.out r, DoubleCoset.out_eq' _ _ _⟩`.

Use `set Ly := P ⊓ L.map (MulAut.conj y).toMonoidHom with hLy`. Establish `hLyP : ∀ k ∈ Ly, k ∈ P` using `fun k hk => (Subgroup.mem_inf.1 hk).1`. Use `set G : DoubleCoset.Quotient (T : Set H) (Ly : Set H) → ℂ := fun q => wt T Ly U (fun x => if x ∈ P then Ψ (x * y) else 0) (Quotient.out q) with hG`. Use `set φ : DoubleCoset.Quotient (T : Set H) (Ly : Set H) → DoubleCoset.Quotient (T : Set H) (L : Set H) := fun q => DoubleCoset.mk T L (Quotient.out q * y) with hφ`. Use `set A : Set (DoubleCoset.Quotient (T : Set H) (Ly : Set H)) := {q | Quotient.out q ∈ P} with hA`.

Establish `h0 : ∑ᶠ q, G q = 0` using `hy y`. Establish `hsuppG : Function.support G ⊆ A`. Introduce `q hq`. Assume the negation of the conclusion as `hn`. Establish `hn' : Quotient.out q ∉ P` using `hn`.

Apply `hq` to reduce the goal to its premises. Use `show wt T Ly U (fun x => if x ∈ P then Ψ (x * y) else 0) (Quotient.out q) = 0`. Simplify using `only [wt, if_neg hn', mul_zero]`. Establish `hGF : ∀ q ∈ A, G q = F (φ q)`. Introduce `q hq`.

Establish `hq' : Quotient.out q ∈ P` using `hq`. Use `show wt T Ly U (fun x => if x ∈ P then Ψ (x * y) else 0) (Quotient.out q) = wt T L U Ψ (Quotient.out (DoubleCoset.mk T L (Quotient.out q * y)))`. Rewrite using `[wt_out U hT hΨl hΨr]`. Simplify using `only [wt, if_pos hq', hLy, locPart_inf_conj hTP hq' y]`. Establish `hinj : Set.InjOn φ A`.

Introduce `q₁ h₁ q₂ h₂ h`. Take `⟨t, ht, l, hl, e⟩` from `(DoubleCoset.eq T L _ _).1 h`. Rewrite using `[← DoubleCoset.out_eq' T Ly q₁, ← DoubleCoset.out_eq' T Ly q₂, DoubleCoset.eq]`. Use `⟨t, ht, y * l * y⁻¹, Subgroup.mem_inf.2 ⟨?_, l, hl, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `e' : y * l * y⁻¹ = (t * Quotient.out q₁)⁻¹ * Quotient.out q₂`.

Rewrite using `[show Quotient.out q₂ = t * (Quotient.out q₁ * y) * l * y⁻¹ by rw [← e]; group]`. Use `group`. Rewrite using `[e']`. Conclude with `P.mul_mem (P.inv_mem (P.mul_mem (hTP ht) h₁)) h₂`. Rewrite using `[show Quotient.out q₂ = t * (Quotient.out q₁ * y) * l * y⁻¹ by rw [← e]; group] group`.

Establish `himg : φ '' A = {q | π q = DoubleCoset.mk P L y}`. Use extensionality with `q`. Simplify using `only [Set.mem_image, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q', hq', rfl⟩`.

Simplify using `only [hπ, hφ, mk_out_of_le hTP, DoubleCoset.eq]`. Conclude with `⟨(Quotient.out q')⁻¹, P.inv_mem hq', 1, L.one_mem, by group⟩`. Introduce `hq`. Take `⟨p, hp, l, hl, e⟩` from `(DoubleCoset.eq P L _ _).1 hq`. Take `⟨t, k, ht, hk, ek⟩` from `DoubleCoset.mk_out_eq_mul T Ly p⁻¹`.

Use `⟨DoubleCoset.mk T Ly p⁻¹, ?_, ?_⟩` and prove the remaining obligations. Use `show Quotient.out (DoubleCoset.mk T Ly p⁻¹) ∈ P`. Rewrite using `[ek]`. Conclude with `P.mul_mem (P.mul_mem (hTP ht) (P.inv_mem hp)) (hLyP k hk)`. Take `⟨_, l', hl', rfl⟩` from `Subgroup.mem_inf.1 hk`.

Simplify using `only [hφ]`. Rewrite using `[ek, ← DoubleCoset.out_eq' T L q, DoubleCoset.eq]`. Use `⟨t⁻¹, T.inv_mem ht, l'⁻¹ * l⁻¹, L.mul_mem (L.inv_mem hl') (L.inv_mem hl), ?_⟩` and prove the remaining obligations. Simplify using `only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Rewrite using `[e]`.

Use `group`. Establish `hGA : ∑ᶠ q, G q = ∑ᶠ q ∈ A, G q`. Rewrite using `[← finsum_mem_inter_support, Set.inter_eq_right.2 hsuppG, finsum_mem_support]`. Rewrite using `[← h0, hGA, finsum_mem_congr rfl hGF, ← finsum_mem_image hinj, himg]`. Use `(finsum_mem_eq_sum_of_inter_support_eq F ?_).symm` and prove the remaining obligations.

Use extensionality with `q`. Simplify using `[Finset.mem_filter, Set.Finite.mem_toFinset]`. The claim follows by propositional logic.
-/
theorem dsum_eq_zero_of_par (H : Type) [Group H] (T P L U : Subgroup H) (Ψ : H → ℂ) (hTP : T ≤ P)
    (hT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s) (hΨl : ∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x)
    (hΨr : ∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x)
    (hy : ∀ y : H, dsum T (P ⊓ L.map (MulAut.conj y).toMonoidHom) U
      (fun x => if x ∈ P then Ψ (x * y) else 0) = 0) :
    dsum T L U Ψ = 0 := by
  set F : DoubleCoset.Quotient (T : Set H) (L : Set H) → ℂ := fun q => wt T L U Ψ (Quotient.out q) with hF
  set π : DoubleCoset.Quotient (T : Set H) (L : Set H) → DoubleCoset.Quotient (P : Set H) (L : Set H) :=
    fun q => DoubleCoset.mk P L (Quotient.out q) with hπ
  have hdef : dsum T L U Ψ = ∑ᶠ q, F q := rfl
  rw [hdef]
  by_cases hfin : (Function.support F).Finite
  swap
  · exact finsum_of_infinite_support hfin
  rw [finsum_eq_sum F hfin, ← Finset.sum_fiberwise_of_maps_to (g := π)
    (t := hfin.toFinset.image π) (fun _ h => Finset.mem_image_of_mem _ h)]
  refine Finset.sum_eq_zero fun r _ => ?_
  obtain ⟨y, rfl⟩ : ∃ y, DoubleCoset.mk P L y = r := ⟨Quotient.out r, DoubleCoset.out_eq' _ _ _⟩
  set Ly := P ⊓ L.map (MulAut.conj y).toMonoidHom with hLy
  have hLyP : ∀ k ∈ Ly, k ∈ P := fun k hk => (Subgroup.mem_inf.1 hk).1
  set G : DoubleCoset.Quotient (T : Set H) (Ly : Set H) → ℂ :=
    fun q => wt T Ly U (fun x => if x ∈ P then Ψ (x * y) else 0) (Quotient.out q) with hG
  set φ : DoubleCoset.Quotient (T : Set H) (Ly : Set H) → DoubleCoset.Quotient (T : Set H) (L : Set H) :=
    fun q => DoubleCoset.mk T L (Quotient.out q * y) with hφ
  set A : Set (DoubleCoset.Quotient (T : Set H) (Ly : Set H)) := {q | Quotient.out q ∈ P} with hA
  have h0 : ∑ᶠ q, G q = 0 := hy y
  have hsuppG : Function.support G ⊆ A := by
    intro q hq
    by_contra hn
    have hn' : Quotient.out q ∉ P := hn
    apply hq
    show wt T Ly U (fun x => if x ∈ P then Ψ (x * y) else 0) (Quotient.out q) = 0
    simp only [wt, if_neg hn', mul_zero]
  have hGF : ∀ q ∈ A, G q = F (φ q) := by
    intro q hq
    have hq' : Quotient.out q ∈ P := hq
    show wt T Ly U (fun x => if x ∈ P then Ψ (x * y) else 0) (Quotient.out q) =
      wt T L U Ψ (Quotient.out (DoubleCoset.mk T L (Quotient.out q * y)))
    rw [wt_out U hT hΨl hΨr]
    simp only [wt, if_pos hq', hLy, locPart_inf_conj hTP hq' y]
  have hinj : Set.InjOn φ A := by
    intro q₁ h₁ q₂ h₂ h
    obtain ⟨t, ht, l, hl, e⟩ := (DoubleCoset.eq T L _ _).1 h
    rw [← DoubleCoset.out_eq' T Ly q₁, ← DoubleCoset.out_eq' T Ly q₂, DoubleCoset.eq]
    refine ⟨t, ht, y * l * y⁻¹, Subgroup.mem_inf.2 ⟨?_, l, hl, rfl⟩, ?_⟩
    · have e' : y * l * y⁻¹ = (t * Quotient.out q₁)⁻¹ * Quotient.out q₂ := by
        rw [show Quotient.out q₂ = t * (Quotient.out q₁ * y) * l * y⁻¹ by rw [← e]; group]
        group
      rw [e']
      exact P.mul_mem (P.inv_mem (P.mul_mem (hTP ht) h₁)) h₂
    · rw [show Quotient.out q₂ = t * (Quotient.out q₁ * y) * l * y⁻¹ by rw [← e]; group]
      group
  have himg : φ '' A = {q | π q = DoubleCoset.mk P L y} := by
    ext q
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨q', hq', rfl⟩
      simp only [hπ, hφ, mk_out_of_le hTP, DoubleCoset.eq]
      exact ⟨(Quotient.out q')⁻¹, P.inv_mem hq', 1, L.one_mem, by group⟩
    · intro hq
      obtain ⟨p, hp, l, hl, e⟩ := (DoubleCoset.eq P L _ _).1 hq
      obtain ⟨t, k, ht, hk, ek⟩ := DoubleCoset.mk_out_eq_mul T Ly p⁻¹
      refine ⟨DoubleCoset.mk T Ly p⁻¹, ?_, ?_⟩
      · show Quotient.out (DoubleCoset.mk T Ly p⁻¹) ∈ P
        rw [ek]
        exact P.mul_mem (P.mul_mem (hTP ht) (P.inv_mem hp)) (hLyP k hk)
      · obtain ⟨_, l', hl', rfl⟩ := Subgroup.mem_inf.1 hk
        simp only [hφ]
        rw [ek, ← DoubleCoset.out_eq' T L q, DoubleCoset.eq]
        refine ⟨t⁻¹, T.inv_mem ht, l'⁻¹ * l⁻¹, L.mul_mem (L.inv_mem hl') (L.inv_mem hl), ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [e]
        group
  have hGA : ∑ᶠ q, G q = ∑ᶠ q ∈ A, G q := by
    rw [← finsum_mem_inter_support, Set.inter_eq_right.2 hsuppG, finsum_mem_support]
  rw [← h0, hGA, finsum_mem_congr rfl hGF,
    ← finsum_mem_image hinj, himg]
  refine (finsum_mem_eq_sum_of_inter_support_eq F ?_).symm
  ext q
  simp [Finset.mem_filter, Set.Finite.mem_toFinset]
  tauto

end GlobalTheory.OrbDesc
