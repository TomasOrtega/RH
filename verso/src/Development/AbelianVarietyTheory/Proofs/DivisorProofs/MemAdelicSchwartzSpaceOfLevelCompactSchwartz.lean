import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.LevelSchwartz

/- English proof (translation)
Introduce `F _ _ N Φ ⟨U, hUo, hU⟩ ⟨K, hK, hKs⟩ hS`. Set `e` to `InfiniteAdeleRing.ringEquiv_mixedSpace F`. Set `ι : (Fin N → Af F) →+ (Fin N → AF F)` to `{ toFun := fun v i => pairA F 0 (v i) map_zero' := rfl map_add' := fun a b => by`. Use function extensionality and compare the values at `i`. Use `show (((0 : Ainf F), a i + b i) : Ainf F × Af F) = ((0 : Ainf F), a i) + ((0 : Ainf F), b i)`.

Simplify using `}`. Establish `hιc : Continuous ι` using `continuous_pi fun i => (show Continuous fun v : Fin N → Af F => (((0 : Ainf F), v i) : Ainf F × Af F) from continuous_const.prodMk (continuous_apply i))`. Establish `hιinf : ∀ v, inf (ι v) = 0` using `fun v => rfl`. Establish `hfin : ∀ a t, fin (ι a + embR t) = a` using `fun a t => by`. Use function extensionality and compare the values at `i`.

Use `show (a i + 0 : Af F) = a i`. Conclude with `add_zero _`. Establish `hdec : ∀ y : Fin N → AF F, y = ι (fin y) + embR (fun i => e (y i).1)` using `fun y => by`. Use function extensionality and compare the values at `i`. Use `show (y i : Ainf F × Af F) = (((0 : Ainf F), (y i).2) : Ainf F × Af F) + ((e.symm (e (y i).1), (0 : Af F)))`.

Rewrite using `[RingEquiv.symm_apply_apply]`. Apply the tactic sequence `refine Prod.ext ?_ ?_ <;> simp`. Set `W : AddSubgroup (Fin N → Af F)` to `U.comap ι`. Establish `hWo : IsOpen (W : Set (Fin N → Af F))` using `hUo.preimage hιc`. Establish `hWcl : IsClosed (W : Set (Fin N → Af F))` using `AddSubgroup.isClosed_of_isOpen W hWo`.

Establish `hinv : ∀ a b, -a + b ∈ W → ∀ z, Φ (ι b + z) = Φ (ι a + z)`. Introduce `a b hab z`. Rewrite using `[← hU (ι (-a + b)) hab (hιinf _) (ι a + z)]`. Use `congr 1`. Rewrite using `[map_add, map_neg]`.

Normalize the expressions using the abelian group laws. Take `⟨t, ht⟩` from `hK.elim_finite_subcover (fun a : Fin N → Af F => {b | -a + b ∈ W}) (fun a => hWo.preimage (continuous_const.add continuous_id)) (fun b _ => Set.mem_iUnion.2 ⟨b, show -b + b ∈ W by rw [neg_add_cancel]; exact W.zero_mem⟩)`. Set `T : Finset ((Fin N → Af F) ⧸ W)` to `t.image QuotientAddGroup.mk`. Use `choose g hg using fun q : (Fin N → Af F) ⧸ W => hS (ι q.out)`. Set `ind : ((Fin N → Af F) ⧸ W) → (Fin N → Af F) → ℂ` to `fun q a => if (QuotientAddGroup.mk a : (Fin N → Af F) ⧸ W) = q then 1 else 0`.

Establish `key : Φ = ∑ q ∈ T, GlobalTheory.WeilM.pureA F (g q) (ind q)`. Use function extensionality and compare the values at `y`. Rewrite using `[Finset.sum_apply]`. Use `show Φ y = ∑ q ∈ T, g q (fun i => e (y i).1) * (if (QuotientAddGroup.mk (fin y) : (Fin N → Af F) ⧸ W) = q then (1 : ℂ) else 0)`. Simplify using `only [mul_ite, mul_one, mul_zero]`.

Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with hT`. Rewrite using `[hg] conv_lhs => rw [hdec y]`. Conclude with `hinv _ _ (QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)) _`. Assume the negation of the conclusion as `hne`.

Take `⟨b, hb, hab⟩` from `Set.mem_iUnion₂.1 (ht (hKs y hne))`. Conclude with `hT (Finset.mem_image.2 ⟨b, hb, QuotientAddGroup.eq.2 hab⟩)`. Rewrite using `[key]`. Use `Submodule.sum_mem _ fun q _ => ?_` and prove the remaining obligations. Distinguish the cases in `h0 : ∀ s, g q s = 0`.

Establish `: GlobalTheory.WeilM.pureA F (g q) (ind q) = 0`. Use function extensionality and compare the values at `y`. Simplify using `[GlobalTheory.WeilM.pureA, h0]`. Rewrite using `[this]`. Conclude with `zero_mem _`.

Use `push_neg at h0`. Take `⟨s0, hs0⟩` from `h0`. Use `Submodule.subset_span ⟨g q, ind q, ?_, rfl⟩` and prove the remaining obligations. Set `C : Set (Fin N → Af F)` to `{a | -q.out + a ∈ W}`. Establish `hCcl : IsClosed C` using `hWcl.preimage (continuous_const.add continuous_id)`.

Establish `hCK : C ⊆ K`. Introduce `a ha`. Establish `h1 : Φ (ι a + embR s0) ≠ 0`. Rewrite using `[hinv _ _ ha, ← hg]`. Conclude with `hs0`.

Simplify `hKs _ h1` using `[hfin]`. Establish `hmk : IsLocallyConstant (fun a : Fin N → Af F => (a : (Fin N → Af F) ⧸ W))` using `(IsLocallyConstant.iff_exists_open _).2 fun x => ⟨{b | -b + x ∈ W}, hWo.preimage (continuous_neg.add continuous_const), by simp, fun b hb => QuotientAddGroup.eq.2 hb⟩`. Use `⟨hmk.comp fun q' => if q' = q then (1 : ℂ) else 0, ?_⟩` and prove the remaining obligations. Use `HasCompactSupport.intro' (hK.of_isClosed_subset hCcl hCK) hCcl fun x hx => ?_` and prove the remaining obligations. Use `show (if (QuotientAddGroup.mk x : (Fin N → Af F) ⧸ W) = q then (1 : ℂ) else 0) = 0`.

Rewrite using `[if_neg]`. Introduce `hq`. Apply `hx` to reduce the goal to its premises. Use `show -q.out + x ∈ W`. Conclude with `QuotientAddGroup.eq.1 (by rw [hq, QuotientAddGroup.out_eq'])`.
-/
theorem mem_schA_of_level : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (Φ : (Fin N → AF F) → ℂ),
    (∃ U : AddSubgroup (Fin N → AF F), IsOpen (U : Set (Fin N → AF F)) ∧ ∀ u ∈ U, inf u = 0 → ∀ x, Φ (x + u) = Φ x) →
    (∃ K : Set (Fin N → Af F), IsCompact K ∧ ∀ x, Φ x ≠ 0 → fin x ∈ K) →
    (∀ x, ∃ g : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ t, g t = Φ (x + embR t)) →
    Φ ∈ GlobalTheory.WeilM.schA F (Fin N) := by
  intro F _ _ N Φ ⟨U, hUo, hU⟩ ⟨K, hK, hKs⟩ hS
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let ι : (Fin N → Af F) →+ (Fin N → AF F) :=
    { toFun := fun v i => pairA F 0 (v i)
      map_zero' := rfl
      map_add' := fun a b => by
        funext i
        show (((0 : Ainf F), a i + b i) : Ainf F × Af F) = ((0 : Ainf F), a i) + ((0 : Ainf F), b i)
        simp }
  have hιc : Continuous ι := continuous_pi fun i =>
    (show Continuous fun v : Fin N → Af F => (((0 : Ainf F), v i) : Ainf F × Af F) from
      continuous_const.prodMk (continuous_apply i))
  have hιinf : ∀ v, inf (ι v) = 0 := fun v => rfl
  have hfin : ∀ a t, fin (ι a + embR t) = a := fun a t => by
    funext i
    show (a i + 0 : Af F) = a i
    exact add_zero _
  have hdec : ∀ y : Fin N → AF F, y = ι (fin y) + embR (fun i => e (y i).1) := fun y => by
    funext i
    show (y i : Ainf F × Af F) = (((0 : Ainf F), (y i).2) : Ainf F × Af F) + ((e.symm (e (y i).1), (0 : Af F)))
    rw [RingEquiv.symm_apply_apply]
    refine Prod.ext ?_ ?_ <;> simp
  let W : AddSubgroup (Fin N → Af F) := U.comap ι
  have hWo : IsOpen (W : Set (Fin N → Af F)) := hUo.preimage hιc
  have hWcl : IsClosed (W : Set (Fin N → Af F)) := AddSubgroup.isClosed_of_isOpen W hWo
  have hinv : ∀ a b, -a + b ∈ W → ∀ z, Φ (ι b + z) = Φ (ι a + z) := by
    intro a b hab z
    rw [← hU (ι (-a + b)) hab (hιinf _) (ι a + z)]
    congr 1
    rw [map_add, map_neg]
    abel
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun a : Fin N → Af F => {b | -a + b ∈ W})
    (fun a => hWo.preimage (continuous_const.add continuous_id))
    (fun b _ => Set.mem_iUnion.2 ⟨b, show -b + b ∈ W by rw [neg_add_cancel]; exact W.zero_mem⟩)
  let T : Finset ((Fin N → Af F) ⧸ W) := t.image QuotientAddGroup.mk
  choose g hg using fun q : (Fin N → Af F) ⧸ W => hS (ι q.out)
  let ind : ((Fin N → Af F) ⧸ W) → (Fin N → Af F) → ℂ := fun q a =>
    if (QuotientAddGroup.mk a : (Fin N → Af F) ⧸ W) = q then 1 else 0
  have key : Φ = ∑ q ∈ T, GlobalTheory.WeilM.pureA F (g q) (ind q) := by
    funext y
    rw [Finset.sum_apply]
    show Φ y = ∑ q ∈ T, g q (fun i => e (y i).1) *
      (if (QuotientAddGroup.mk (fin y) : (Fin N → Af F) ⧸ W) = q then (1 : ℂ) else 0)
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hT
    · rw [hg]
      conv_lhs => rw [hdec y]
      exact hinv _ _ (QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)) _
    · by_contra hne
      obtain ⟨b, hb, hab⟩ := Set.mem_iUnion₂.1 (ht (hKs y hne))
      exact hT (Finset.mem_image.2 ⟨b, hb, QuotientAddGroup.eq.2 hab⟩)
  rw [key]
  refine Submodule.sum_mem _ fun q _ => ?_
  by_cases h0 : ∀ s, g q s = 0
  · have : GlobalTheory.WeilM.pureA F (g q) (ind q) = 0 := by
      funext y
      simp [GlobalTheory.WeilM.pureA, h0]
    rw [this]
    exact zero_mem _
  push_neg at h0
  obtain ⟨s0, hs0⟩ := h0
  refine Submodule.subset_span ⟨g q, ind q, ?_, rfl⟩
  let C : Set (Fin N → Af F) := {a | -q.out + a ∈ W}
  have hCcl : IsClosed C := hWcl.preimage (continuous_const.add continuous_id)
  have hCK : C ⊆ K := by
    intro a ha
    have h1 : Φ (ι a + embR s0) ≠ 0 := by
      rw [hinv _ _ ha, ← hg]
      exact hs0
    simpa [hfin] using hKs _ h1
  have hmk : IsLocallyConstant (fun a : Fin N → Af F => (a : (Fin N → Af F) ⧸ W)) :=
    (IsLocallyConstant.iff_exists_open _).2 fun x => ⟨{b | -b + x ∈ W},
      hWo.preimage (continuous_neg.add continuous_const), by simp, fun b hb => QuotientAddGroup.eq.2 hb⟩
  refine ⟨hmk.comp fun q' => if q' = q then (1 : ℂ) else 0, ?_⟩
  refine HasCompactSupport.intro' (hK.of_isClosed_subset hCcl hCK) hCcl fun x hx => ?_
  show (if (QuotientAddGroup.mk x : (Fin N → Af F) ⧸ W) = q then (1 : ℂ) else 0) = 0
  rw [if_neg]
  intro hq
  apply hx
  show -q.out + x ∈ W
  exact QuotientAddGroup.eq.1 (by rw [hq, QuotientAddGroup.out_eq'])

end GlobalTheory.LevelSchwartz

end
