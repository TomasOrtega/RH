import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion

open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.Iwahori

/- English proof (translation)
Introduce `L V _ _ _ _ s hs h hh g`. Take `⟨hadd2, hsmul2, hsymm, hnd⟩` from `hh`. Establish `hss` using `hs.1`. Establish `hadd1 : ∀ x x' y, h (x + x') y = h x y + h x' y`. Introduce `x x' y`.

Rewrite using `[hsymm y (x + x'), hadd2, map_add, ← hsymm, ← hsymm]`. Establish `hsmul1 : ∀ (a : L) x y, h (a • x) y = s a * h x y`. Introduce `a x y`. Rewrite using `[hsymm y (a • x), hsmul2, map_mul, ← hsymm]`. Set `ψ₀ : V → Module.Dual L V` to `fun x => { toFun := h x map_add' := hadd2 x map_smul' := fun a y => by simpa using hsmul2 a x y }`.

Establish `ψ₀_apply : ∀ x y, ψ₀ x y = h x y` using `fun _ _ => rfl`. Set `ψ : V →+ Module.Dual L V` to `AddMonoidHom.mk' ψ₀ (fun x x' => by`. Use extensionality with `y`. Simplify using `[ψ₀_apply, hadd1])`. Establish `ψ_apply : ∀ x y, ψ x y = h x y` using `fun _ _ => rfl`.

Establish `ψ_smul : ∀ (a : L) x, ψ (a • x) = s a • ψ x`. Introduce `a x`. Use extensionality with `y`. Simplify using `[ψ_apply, hsmul1]`. Establish `ψ_inj : ∀ x, ψ x = 0 → x = 0`.

Introduce `x hx`. Conclude with `hnd x (fun y => by rw [← ψ_apply, hx]; rfl)`. Establish `ψ_inj' : ∀ x x', ψ x = ψ x' → x = x'`. Introduce `x x' hxx`. Conclude with `sub_eq_zero.mp (ψ_inj _ (by rw [map_sub, hxx, sub_self]))`.

Set `b` to `Module.finBasis L V`. Establish `hli : LinearIndependent L (fun i => ψ (b i))`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc i`. Establish `h0 : ψ (∑ j, s (c j) • b j) = 0`.

Rewrite using `[map_sum, ← hc]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[ψ_smul, hss]`. Establish `h1` using `ψ_inj _ h0`. Establish `h2` using `(Fintype.linearIndependent_iff.mp b.linearIndependent) _ h1 i`.

Establish `h3` using `congrArg s h2`. Rewrite `h3` using `[hss, map_zero]`. Then use the resulting hypothesis. Establish `hspan : Submodule.span L (Set.range fun i => ψ (b i)) = ⊤`. Use `hli.span_eq_top_of_card_eq_finrank' ?_` and prove the remaining obligations. Rewrite using `[Subspace.dual_finrank_eq]`.

Simplify using the standard rewrite rules. Establish `ψ_surj : ∀ f : Module.Dual L V, ∃ z, ψ z = f`. Introduce `f`. Establish `hf : f ∈ Submodule.span L (Set.range fun i => ψ (b i))`. Rewrite using `[hspan]`.

Discharge the goal by the elementary cases of `trivial`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun L).mp hf`. Use `⟨∑ j, s (c j) • b j, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum, ← hc]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations.

Rewrite using `[ψ_smul, hss]`. Use `choose z hz using fun y => ψ_surj ((ψ y).comp g)`. Establish `hz' : ∀ y x, h (z y) x = h y (g x)`. Introduce `y x`. Rewrite using `[← ψ_apply, hz]`.

Both sides reduce to the same expression. Use `⟨{ toFun := z, map_add' := ?_, map_smul' := ?_ }, ?_⟩` and prove the remaining obligations. Introduce `y y'`. Apply `ψ_inj'` to reduce the goal to its premises. Rewrite using `[hz, map_add, map_add, hz, hz]`.

Both sides reduce to the same expression. Introduce `a y`. Apply `ψ_inj'` to reduce the goal to its premises. Rewrite using `[hz, RingHom.id_apply, ψ_smul, ψ_smul, hz]`. Both sides reduce to the same expression.

Introduce `x y show h (g x) y = h x (z y)`. Rewrite using `[hsymm (z y) x, hz', ← hsymm]`.
-/
theorem exists_adjoint_herm : ∀ {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] (s : L →+* L), IsInv s → ∀ h : V → V → L, IsHerm s h →
    ∀ g : Module.End L V, ∃ g' : Module.End L V, ∀ x y, h (g x) y = h x (g' y) := by
  intro L V _ _ _ _ s hs h hh g
  obtain ⟨hadd2, hsmul2, hsymm, hnd⟩ := hh
  have hss := hs.1
  have hadd1 : ∀ x x' y, h (x + x') y = h x y + h x' y := by
    intro x x' y
    rw [hsymm y (x + x'), hadd2, map_add, ← hsymm, ← hsymm]
  have hsmul1 : ∀ (a : L) x y, h (a • x) y = s a * h x y := by
    intro a x y
    rw [hsymm y (a • x), hsmul2, map_mul, ← hsymm]

  let ψ₀ : V → Module.Dual L V := fun x =>
    { toFun := h x
      map_add' := hadd2 x
      map_smul' := fun a y => by simpa using hsmul2 a x y }
  have ψ₀_apply : ∀ x y, ψ₀ x y = h x y := fun _ _ => rfl
  let ψ : V →+ Module.Dual L V := AddMonoidHom.mk' ψ₀ (fun x x' => by
    ext y
    simp [ψ₀_apply, hadd1])
  have ψ_apply : ∀ x y, ψ x y = h x y := fun _ _ => rfl
  have ψ_smul : ∀ (a : L) x, ψ (a • x) = s a • ψ x := by
    intro a x
    ext y
    simp [ψ_apply, hsmul1]
  have ψ_inj : ∀ x, ψ x = 0 → x = 0 := by
    intro x hx
    exact hnd x (fun y => by rw [← ψ_apply, hx]; rfl)
  have ψ_inj' : ∀ x x', ψ x = ψ x' → x = x' := by
    intro x x' hxx
    exact sub_eq_zero.mp (ψ_inj _ (by rw [map_sub, hxx, sub_self]))

  let b := Module.finBasis L V
  have hli : LinearIndependent L (fun i => ψ (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h0 : ψ (∑ j, s (c j) • b j) = 0 := by
      rw [map_sum, ← hc]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [ψ_smul, hss]
    have h1 := ψ_inj _ h0
    have h2 := (Fintype.linearIndependent_iff.mp b.linearIndependent) _ h1 i
    have h3 := congrArg s h2
    rwa [hss, map_zero] at h3
  have hspan : Submodule.span L (Set.range fun i => ψ (b i)) = ⊤ := by
    refine hli.span_eq_top_of_card_eq_finrank' ?_
    rw [Subspace.dual_finrank_eq]
    simp
  have ψ_surj : ∀ f : Module.Dual L V, ∃ z, ψ z = f := by
    intro f
    have hf : f ∈ Submodule.span L (Set.range fun i => ψ (b i)) := by
      rw [hspan]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp hf
    refine ⟨∑ j, s (c j) • b j, ?_⟩
    rw [map_sum, ← hc]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ψ_smul, hss]
  choose z hz using fun y => ψ_surj ((ψ y).comp g)
  have hz' : ∀ y x, h (z y) x = h y (g x) := by
    intro y x
    rw [← ψ_apply, hz]
    rfl
  refine ⟨{ toFun := z, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro y y'
    apply ψ_inj'
    rw [hz, map_add, map_add, hz, hz]
    rfl
  · intro a y
    apply ψ_inj'
    rw [hz, RingHom.id_apply, ψ_smul, ψ_smul, hz]
    rfl
  · intro x y
    show h (g x) y = h x (z y)
    rw [hsymm (z y) x, hz', ← hsymm]

end GlobalTheory.CompanionTheory.Iwahori
