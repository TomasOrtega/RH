import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsPureML
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DixmierCommutantScalar

noncomputable section

namespace PositivityTheory.ThKF

/- English proof (translation)
Establish `on : ∀ {Q P : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup P] [Module ℂ P] {S : Submodule ℂ Q} {p : Q →ₗ[ℂ] P}, S.map p = ⊤ → ∀ y, ∃ x : S, p x = y` using `fun {Q P} _ _ _ _ S p h y => by`. Take `⟨x, hx, e⟩ : y ∈ S.map p` from `h ▸ Submodule.mem_top`. Conclude with `⟨⟨x, hx⟩, e⟩`. Take `⟨s, hs, hs'⟩` from `exists_section p S`. Take `⟨t, ht, ht'⟩` from `exists_section p₂' S'`.

Establish `he : ∀ x ∈ S, p₂ (s (p x)) = p₂ x` using `fun x hx => by`. Rewrite using `[← sub_eq_zero, ← map_sub]`. Conclude with `k _ (sub_mem (hs _) hx) (by rw [map_sub, hs' x hx, sub_self])`. Establish `hd : ∀ x ∈ S', p' (t (p₂' x)) = p' x` using `fun x hx => by`. Rewrite using `[← sub_eq_zero, ← map_sub]`.

Conclude with `(k' _ (sub_mem (ht _) hx)).2 (by rw [map_sub, ht' x hx, sub_self])`. Set `ρ : ι → Module.End ℂ P` to `fun i => p ∘ₗ A i ∘ₗ s.codRestrict S hs`. Establish `hρ : ∀ i (x : S), ρ i (p x) = p (A i x)` using `fun i x => by`. Take `⟨x', hx'⟩` from `on o' (p x)`. Rewrite using `[eq i x x' hx'.symm]`.

Conclude with `eq i ⟨s (p x), hs _⟩ x' ((hs' x x.2).trans hx'.symm)`. Set `U : Module.End ℂ P` to `p' ∘ₗ t ∘ₗ p₂ ∘ₗ s`. Establish `hU : ∀ (x : S) (x' : S'), p₂ x = p₂' x' → U (p x) = p' x'` using `fun x x' h => by`. Express the relevant statement in the definitionally equal form `p' (t (p₂ (s (p x)))) = _`. Rewrite using `[he x x.2, h, hd x' x'.2]`.

Establish `rkP : Module.rank ℂ P ≤ Cardinal.aleph0` using `(LinearMap.rank_le_of_surjective (p.domRestrict S) fun y => on o y).trans rk`. Take `⟨c, hc⟩` from `GlobalTheory.dixmier_commutant_scalar ι P ρ rkP (fun N hN => irr N fun i x hx => hρ i x ▸ hN i _ hx) U fun i => LinearMap.ext fun y => by`. Take `⟨x, rfl⟩` from `on o y`. Take `⟨x', hx'⟩` from `on o₂' (p₂ x)`. Take `⟨x₃, h₃⟩` from `on o (p' x')`.

Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, hρ, hU x x' hx'.symm, ← h₃, hρ, eq i x₃ x' h₃]`. Conclude with `hU ⟨_, hA i x⟩ ⟨_, hA' i x'⟩ (eq₂ i x x' hx'.symm)`. Establish `main : ∀ (x : S) (x' : S'), p x = p' x' → p₂ x = c • p₂' x'` using `fun x x' h => by`. Take `⟨y, hy⟩` from `on o₂' (p₂ x)`. Establish `h1` using `hU x y hy.symm`.

Rewrite `h1` using `[hc, LinearMap.smul_apply, Module.End.one_apply, h]`. Establish `h2` using `(k' _ (sub_mem y.2 (S'.smul_mem c x'.2))).1 (by rw [map_sub, map_smul, h1, sub_self])`. Rewrite `h2` using `[map_sub, map_smul, sub_eq_zero]`. Rewrite using `[← hy, h2]`. Use `⟨p₂ ∘ₗ s, c, fun h0 => ?_, he, fun x' hx' => ?_⟩` and prove the remaining obligations.

Take `⟨y, hy⟩` from `exists_ne (0 : P₂)`. Take `⟨x, rfl⟩` from `on o₂ y`. Take `⟨x', hx'⟩` from `on o' (p x)`. Conclude with `hy (by rw [main x x' hx'.symm, h0, zero_smul])`. Take `⟨x, hx⟩` from `on o (p' x')`.

Rewrite using `[← hx]`. Conclude with `(he x x.2).trans (main x ⟨x', hx'⟩ hx)`.
-/
theorem schur_match {Q Q' P P₂ ι : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Q'] [Module ℂ Q'] [AddCommGroup P]
    [Module ℂ P] [AddCommGroup P₂] [Module ℂ P₂] [Nontrivial P₂] (S : Submodule ℂ Q) (S' : Submodule ℂ Q')
    (p : Q →ₗ[ℂ] P) (p' : Q' →ₗ[ℂ] P) (p₂ : Q →ₗ[ℂ] P₂) (p₂' : Q' →ₗ[ℂ] P₂)
    (o : S.map p = ⊤) (o' : S'.map p' = ⊤) (o₂ : S.map p₂ = ⊤) (o₂' : S'.map p₂' = ⊤)
    (k : ∀ x ∈ S, p x = 0 → p₂ x = 0) (k' : ∀ x ∈ S', p' x = 0 ↔ p₂' x = 0)
    (A : ι → S →ₗ[ℂ] Q) (A' : ι → S' → Q') (hA : ∀ i x, A i x ∈ S) (hA' : ∀ i x, A' i x ∈ S')
    (eq : ∀ i (x : S) (x' : S'), p x = p' x' → p (A i x) = p' (A' i x'))
    (eq₂ : ∀ i (x : S) (x' : S'), p₂ x = p₂' x' → p₂ (A i x) = p₂' (A' i x'))
    (irr : ∀ N : Submodule ℂ P, (∀ i (x : S), p x ∈ N → p (A i x) ∈ N) → N = ⊥ ∨ N = ⊤)
    (rk : Module.rank ℂ S ≤ Cardinal.aleph0) :
    ∃ (e : P →ₗ[ℂ] P₂) (c : ℂ), c ≠ 0 ∧ (∀ x ∈ S, e (p x) = p₂ x) ∧ ∀ x ∈ S', e (p' x) = c • p₂' x := by
  have on : ∀ {Q P : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup P] [Module ℂ P] {S : Submodule ℂ Q} {p : Q →ₗ[ℂ] P},
      S.map p = ⊤ → ∀ y, ∃ x : S, p x = y := fun {Q P} _ _ _ _ S p h y => by
    obtain ⟨x, hx, e⟩ : y ∈ S.map p := h ▸ Submodule.mem_top
    exact ⟨⟨x, hx⟩, e⟩
  obtain ⟨s, hs, hs'⟩ := exists_section p S
  obtain ⟨t, ht, ht'⟩ := exists_section p₂' S'
  have he : ∀ x ∈ S, p₂ (s (p x)) = p₂ x := fun x hx => by
    rw [← sub_eq_zero, ← map_sub]
    exact k _ (sub_mem (hs _) hx) (by rw [map_sub, hs' x hx, sub_self])
  have hd : ∀ x ∈ S', p' (t (p₂' x)) = p' x := fun x hx => by
    rw [← sub_eq_zero, ← map_sub]
    exact (k' _ (sub_mem (ht _) hx)).2 (by rw [map_sub, ht' x hx, sub_self])
  let ρ : ι → Module.End ℂ P := fun i => p ∘ₗ A i ∘ₗ s.codRestrict S hs
  have hρ : ∀ i (x : S), ρ i (p x) = p (A i x) := fun i x => by
    obtain ⟨x', hx'⟩ := on o' (p x)
    rw [eq i x x' hx'.symm]
    exact eq i ⟨s (p x), hs _⟩ x' ((hs' x x.2).trans hx'.symm)
  let U : Module.End ℂ P := p' ∘ₗ t ∘ₗ p₂ ∘ₗ s
  have hU : ∀ (x : S) (x' : S'), p₂ x = p₂' x' → U (p x) = p' x' := fun x x' h => by
    change p' (t (p₂ (s (p x)))) = _
    rw [he x x.2, h, hd x' x'.2]
  have rkP : Module.rank ℂ P ≤ Cardinal.aleph0 :=
    (LinearMap.rank_le_of_surjective (p.domRestrict S) fun y => on o y).trans rk
  obtain ⟨c, hc⟩ := GlobalTheory.dixmier_commutant_scalar ι P ρ rkP
    (fun N hN => irr N fun i x hx => hρ i x ▸ hN i _ hx) U fun i => LinearMap.ext fun y => by
      obtain ⟨x, rfl⟩ := on o y
      obtain ⟨x', hx'⟩ := on o₂' (p₂ x)
      obtain ⟨x₃, h₃⟩ := on o (p' x')
      rw [Module.End.mul_apply, Module.End.mul_apply, hρ, hU x x' hx'.symm, ← h₃, hρ, eq i x₃ x' h₃]
      exact hU ⟨_, hA i x⟩ ⟨_, hA' i x'⟩ (eq₂ i x x' hx'.symm)
  have main : ∀ (x : S) (x' : S'), p x = p' x' → p₂ x = c • p₂' x' := fun x x' h => by
    obtain ⟨y, hy⟩ := on o₂' (p₂ x)
    have h1 := hU x y hy.symm
    rw [hc, LinearMap.smul_apply, Module.End.one_apply, h] at h1
    have h2 := (k' _ (sub_mem y.2 (S'.smul_mem c x'.2))).1 (by rw [map_sub, map_smul, h1, sub_self])
    rw [map_sub, map_smul, sub_eq_zero] at h2
    rw [← hy, h2]
  refine ⟨p₂ ∘ₗ s, c, fun h0 => ?_, he, fun x' hx' => ?_⟩
  · obtain ⟨y, hy⟩ := exists_ne (0 : P₂)
    obtain ⟨x, rfl⟩ := on o₂ y
    obtain ⟨x', hx'⟩ := on o' (p x)
    exact hy (by rw [main x x' hx'.symm, h0, zero_smul])
  · obtain ⟨x, hx⟩ := on o (p' x')
    rw [← hx]
    exact (he x x.2).trans (main x ⟨x', hx'⟩ hx)

/- English proof (translation)
Establish `hb` using `TopologicalSpace.isBasis_countableBasis Y`. Use `((Set.countable_setOf_finite_subset (TopologicalSpace.countable_countableBasis Y)).image fun s => ⋃₀ s).mono ?_` and prove the remaining obligations. Introduce and unpack `K ⟨h1, h2⟩`. Take `⟨S, hS, rfl⟩` from `hb.open_eq_sUnion h2`. Take `⟨t, ht, hf, hc⟩` from `h1.elim_finite_subcover_image (b := S) (c := id) (fun u hu => hb.isOpen (hS hu)) (by rw [Set.sUnion_eq_biUnion]; rfl)`.

Use `⟨t, ⟨hf, ht.trans hS⟩, Set.Subset.antisymm (Set.sUnion_mono ht) ?_⟩` and prove the remaining obligations. Use `show ⋃₀ S ⊆ ⋃₀ t`. Rewrite using `[Set.sUnion_eq_biUnion (s := t)]`. Conclude with `hc`.
-/
theorem countable_compactOpen (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] :
    {K : Set Y | IsCompact K ∧ IsOpen K}.Countable := by
  have hb := TopologicalSpace.isBasis_countableBasis Y
  refine ((Set.countable_setOf_finite_subset (TopologicalSpace.countable_countableBasis Y)).image fun s => ⋃₀ s).mono ?_
  rintro K ⟨h1, h2⟩
  obtain ⟨S, hS, rfl⟩ := hb.open_eq_sUnion h2
  obtain ⟨t, ht, hf, hc⟩ := h1.elim_finite_subcover_image (b := S) (c := id) (fun u hu => hb.isOpen (hS hu))
    (by rw [Set.sUnion_eq_biUnion]; rfl)
  refine ⟨t, ⟨hf, ht.trans hS⟩, Set.Subset.antisymm (Set.sUnion_mono ht) ?_⟩
  show ⋃₀ S ⊆ ⋃₀ t
  rw [Set.sUnion_eq_biUnion (s := t)]; exact hc

/- English proof (translation)
Set `I : Set (Y → ℂ)` to `(fun K => Set.indicator K 1) '' {K : Set Y | IsCompact K ∧ IsOpen K}`. Establish `hle : GlobalTheory.WeilM.SB Y ≤ Submodule.span ℂ I`. Introduce and unpack `f ⟨h1, h2⟩`. Establish `hs : IsCompact (Function.support f)` using `h2.of_isClosed_subset (h1.isClopen_fiber 0).compl.isClosed (subset_tsupport f)`. Establish `fin : (f '' Function.support f).Finite`.

Take `⟨t, ht⟩` from `hs.elim_finite_subcover (fun c : ℂ => f ⁻¹' {c}) (fun c => (h1.isClopen_fiber c).isOpen) fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩`. Use `t.finite_toSet.subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨c, hc, e⟩` from `Set.mem_iUnion₂.1 (ht hx)`. Rewrite using `[show f x = c from e]`.

Conclude with `hc`. Establish `e : f = ∑ c ∈ fin.toFinset, c • Set.indicator (f ⁻¹' {c}) 1`. Use function extensionality and compare the values at `x`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff, Pi.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Set.Finite.mem_toFinset]`. Use `split_ifs with h`.

Both sides reduce to the same expression. Assume the negation of the conclusion as `h0`. Conclude with `h ⟨x, h0, rfl⟩`. Rewrite using `[e]`. Use `sum_mem fun c hc => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨?_, (h1.isClopen_fiber c).isOpen⟩, rfl⟩)` and prove the remaining obligations.

Take `⟨x, hx, rfl⟩` from `(Set.Finite.mem_toFinset _).1 hc`. Conclude with `hs.of_isClosed_subset (h1.isClopen_fiber _).isClosed fun y hy => by`. Rewrite using `[Function.mem_support, show f y = f x from hy]`. Conclude with `hx`. Use `(Submodule.rank_mono hle).trans ((rank_span_le I).trans ?_)` and prove the remaining obligations.

Conclude with `Cardinal.le_aleph0_iff_set_countable.2 ((countable_compactOpen Y).image _)`.
-/
theorem rank_SB (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] :
    Module.rank ℂ (GlobalTheory.WeilM.SB Y) ≤ Cardinal.aleph0 := by
  classical
  let I : Set (Y → ℂ) := (fun K => Set.indicator K 1) '' {K : Set Y | IsCompact K ∧ IsOpen K}
  have hle : GlobalTheory.WeilM.SB Y ≤ Submodule.span ℂ I := by
    rintro f ⟨h1, h2⟩
    have hs : IsCompact (Function.support f) :=
      h2.of_isClosed_subset (h1.isClopen_fiber 0).compl.isClosed (subset_tsupport f)
    have fin : (f '' Function.support f).Finite := by
      obtain ⟨t, ht⟩ := hs.elim_finite_subcover (fun c : ℂ => f ⁻¹' {c}) (fun c => (h1.isClopen_fiber c).isOpen)
        fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩
      refine t.finite_toSet.subset ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, hc, e⟩ := Set.mem_iUnion₂.1 (ht hx)
      rw [show f x = c from e]; exact hc
    have e : f = ∑ c ∈ fin.toFinset, c • Set.indicator (f ⁻¹' {c}) 1 := by
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff,
        Pi.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Set.Finite.mem_toFinset]
      split_ifs with h
      · rfl
      · by_contra h0; exact h ⟨x, h0, rfl⟩
    rw [e]
    refine sum_mem fun c hc => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨?_, (h1.isClopen_fiber c).isOpen⟩, rfl⟩)
    obtain ⟨x, hx, rfl⟩ := (Set.Finite.mem_toFinset _).1 hc
    exact hs.of_isClosed_subset (h1.isClopen_fiber _).isClosed fun y hy => by
      rw [Function.mem_support, show f y = f x from hy]; exact hx
  refine (Submodule.rank_mono hle).trans ((rank_span_le I).trans ?_)
  exact Cardinal.le_aleph0_iff_set_countable.2 ((countable_compactOpen Y).image _)

end PositivityTheory.ThKF

end
