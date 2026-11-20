import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSummandTw

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

namespace GlobalTheory.Pass.LocDual

/- English proof (translation)
Use `show Module.length O (↥(S ⊔ H) ⧸ H.comap (S ⊔ H).subtype) = _`. Establish `hker : LinearMap.ker (H.mkQ ∘ₗ (S ⊔ H).subtype) = H.comap (S ⊔ H).subtype`. Rewrite using `[LinearMap.ker_comp, Submodule.ker_mkQ]`. Establish `hrange : LinearMap.range (H.mkQ ∘ₗ (S ⊔ H).subtype) = S.map H.mkQ`. Rewrite using `[LinearMap.range_comp, Submodule.range_subtype, Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]`.

Rewrite using `[← Module.length_submodule]`. Conclude with `((Submodule.quotEquivOfEq _ _ hker.symm).trans ((H.mkQ ∘ₗ (S ⊔ H).subtype).quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))).length_eq`.
-/
theorem lenMod_eq_height_map {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S H : Submodule O M) : BlochKatoDuality.lenMod S H = Order.height (S.map H.mkQ) := by
  show Module.length O (↥(S ⊔ H) ⧸ H.comap (S ⊔ H).subtype) = _
  have hker : LinearMap.ker (H.mkQ ∘ₗ (S ⊔ H).subtype) = H.comap (S ⊔ H).subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : LinearMap.range (H.mkQ ∘ₗ (S ⊔ H).subtype) = S.map H.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_sup, Submodule.mkQ_map_self,
      sup_bot_eq]
  rw [← Module.length_submodule]
  exact ((Submodule.quotEquivOfEq _ _ hker.symm).trans
    ((H.mkQ ∘ₗ (S ⊔ H).subtype).quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))).length_eq

/- English proof (translation)
Rewrite using `[Order.height_le_iff]`. Introduce `p hp`. Establish `hx : ∀ i : Fin p.length, ∃ x ∈ p i.succ, x ∉ p i.castSucc` using `fun i => SetLike.exists_of_lt (p.step i)`. Use `choose x hxin hxout using hx`. Establish `hfin : ∀ i : Fin p.length, ∃ F : Finset M, (↑F : Set M) ⊆ S ∧ x i ∈ (Submodule.span O (↑F : Set M)).map f`.

Introduce `i`. Establish `hxi : x i ∈ (Submodule.span O S).map f` using `hp (p.monotone (Fin.le_last i.succ) (hxin i))`. Take `⟨y, hyS, hyx⟩` from `Submodule.mem_map.mp hxi`. Take `⟨T, hTS, hyT⟩` from `Submodule.mem_span_finite_of_mem_span hyS`. Conclude with `⟨T, hTS, Submodule.mem_map.mpr ⟨y, hyT, hyx⟩⟩`.

Use `choose F hFS hxF using hfin`. Set `G : Finset M` to `Finset.univ.biUnion F`. Establish `hGS : (↑G : Set M) ⊆ S`. Introduce `z hz`. Take `⟨i, -, hi⟩` from `Finset.mem_biUnion.mp hz`.

Conclude with `hFS i hi`. Establish `hFG : ∀ i, Submodule.span O (↑(F i) : Set M) ≤ Submodule.span O (↑G : Set M)` using `fun i => Submodule.span_mono (fun z hz => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hz⟩)`. Set `Q` to `(Submodule.span O (↑G : Set M)).map f`. Set `q : LTSeries (Submodule O N)` to `LTSeries.mk p.length (fun j => p j ⊓ Q) (by`. Apply `Fin.strictMono_iff_lt_succ.mpr` to reduce the goal to its premises.

Introduce `i`. Simplify using `only`. Use `lt_of_le_of_ne (inf_le_inf_right _ (p.monotone (Fin.castSucc_le_succ i))) ?_` and prove the remaining obligations. Introduce `heq`. Establish `h1 : x i ∈ p i.succ ⊓ Q` using `Submodule.mem_inf.mpr ⟨hxin i, Submodule.map_mono (hFG i) (hxF i)⟩`.

Rewrite `h1` using `[← heq]`. Conclude with `hxout i (Submodule.mem_inf.mp h1).1)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem height_map_span_le_of_finset {O M N : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (f : M →ₗ[O] N) (S : Set M) (b : ℕ∞)
    (h : ∀ F : Finset M, (↑F : Set M) ⊆ S →
      Order.height ((Submodule.span O (↑F : Set M)).map f) ≤ b) :
    Order.height ((Submodule.span O S).map f) ≤ b := by
  classical
  rw [Order.height_le_iff]
  intro p hp

  have hx : ∀ i : Fin p.length, ∃ x ∈ p i.succ, x ∉ p i.castSucc :=
    fun i => SetLike.exists_of_lt (p.step i)
  choose x hxin hxout using hx

  have hfin : ∀ i : Fin p.length, ∃ F : Finset M, (↑F : Set M) ⊆ S ∧
      x i ∈ (Submodule.span O (↑F : Set M)).map f := by
    intro i
    have hxi : x i ∈ (Submodule.span O S).map f := hp (p.monotone (Fin.le_last i.succ) (hxin i))
    obtain ⟨y, hyS, hyx⟩ := Submodule.mem_map.mp hxi
    obtain ⟨T, hTS, hyT⟩ := Submodule.mem_span_finite_of_mem_span hyS
    exact ⟨T, hTS, Submodule.mem_map.mpr ⟨y, hyT, hyx⟩⟩
  choose F hFS hxF using hfin
  let G : Finset M := Finset.univ.biUnion F
  have hGS : (↑G : Set M) ⊆ S := by
    intro z hz
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz
    exact hFS i hi
  have hFG : ∀ i, Submodule.span O (↑(F i) : Set M) ≤ Submodule.span O (↑G : Set M) := fun i =>
    Submodule.span_mono (fun z hz => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hz⟩)

  let Q := (Submodule.span O (↑G : Set M)).map f
  let q : LTSeries (Submodule O N) := LTSeries.mk p.length (fun j => p j ⊓ Q) (by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    dsimp only
    refine lt_of_le_of_ne (inf_le_inf_right _ (p.monotone (Fin.castSucc_le_succ i))) ?_
    intro heq
    have h1 : x i ∈ p i.succ ⊓ Q :=
      Submodule.mem_inf.mpr ⟨hxin i, Submodule.map_mono (hFG i) (hxF i)⟩
    rw [← heq] at h1
    exact hxout i (Submodule.mem_inf.mp h1).1)
  calc (p.length : ℕ∞) = q.length := rfl
    _ ≤ Order.height Q := Order.length_le_height inf_le_right
    _ ≤ b := h G hGS

/- English proof (translation)
Introduce `O M _ _ _ S H b h`. Rewrite using `[lenMod_eq_height_map]`. Apply `height_map_span_le_of_finset H.mkQ S b` to reduce the goal to its premises. Introduce `F hF`. Rewrite using `[← lenMod_eq_height_map]`.

Conclude with `h F hF`.
-/
theorem lenMod_span_le_of_finset : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S : Set M) (H : Submodule O M) (b : ℕ∞),
    (∀ F : Finset M, (↑F : Set M) ⊆ S → BlochKatoDuality.lenMod (Submodule.span O (↑F : Set M)) H ≤ b) →
    BlochKatoDuality.lenMod (Submodule.span O S) H ≤ b := by
  intro O M _ _ _ S H b h
  rw [lenMod_eq_height_map]
  apply height_map_span_le_of_finset H.mkQ S b
  intro F hF
  rw [← lenMod_eq_height_map]
  exact h F hF

end GlobalTheory.Pass.LocDual
