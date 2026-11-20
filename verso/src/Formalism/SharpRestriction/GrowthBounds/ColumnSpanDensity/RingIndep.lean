import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RestHLTransport

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

/- English proof (translation)
Unfold `LPRingIndep`. Introduce `p n' R₁ R₂ m r lam0 t D κ cStar hLP`. Take `⟨I⟩` from `h1 p n' R₁ R₂`. Take `⟨Φ, Ψ, hΨ, hLat, hEdge, hHL, hHLe, hdim⟩` from `h2 p n' R₁ R₂ I m lam0`. Establish `hwK : ∀ z : ℤ, I.φK (algebraMap R₁.O R₁.Kf R₁.w ^ z) = algebraMap R₂.O R₂.Kf R₂.w ^ z`.

Introduce `z`. Rewrite using `[map_zpow₀, I.hOK, I.hw]`. Establish `hpK : ∀ z : ℤ, I.φK ((p : R₁.Kf) ^ z) = (p : R₂.Kf) ^ z`. Introduce `z`. Rewrite using `[map_zpow₀, map_natCast]`.

Set `back : Edge R₂.W R₂.Qq (m + 1) → Edge R₁.W R₁.Qq (m + 1)` to `fun e => ⟨Φ.symm e.src, Φ.symm e.tgt⟩`. Establish `hback : ∀ e, (⟨Φ (back e).src, Φ (back e).tgt⟩ : Edge R₂.W R₂.Qq (m + 1)) = e`. Introduce `e`. Consider the cases of `e`. Simplify using `[back]`.

Establish `hbackEdge : ∀ e, IsEdge p n' r e → IsEdge p n' r (back e)`. Introduce `e he`. Rewrite using `[hEdge r (back e), hback]`. Conclude with `he`. Establish `hHLe' : ∀ e x, x ∈ HLe p R₁.ι R₁.σ R₁.w lam0 (back e) ↔ Ψ x ∈ HLe p R₂.ι R₂.σ R₂.w lam0 e`.

Introduce `e x`. Establish `h` using `hHLe (back e) x`. Rewrite `h` using `[hback]`. Then use the resulting hypothesis. Unfold `LPprime at hLP ⊢`. Take `⟨hc, hall⟩` from `hLP`.

Use `⟨hc, fun L hL => ?_⟩` and prove the remaining obligations. Establish `hL1 : IsLattice R₁.W (Φ.symm L)` using `by rw [hLat, Φ.apply_symm_apply]; exact hL`. Establish `hAt` using `hall _ hL1`. Unfold `LPprimeAt at hAt ⊢`. Take `⟨M, e, F, he, hF, hF', n, hn, hG⟩` from `hAt`.

Use `⟨M, fun i => ⟨Φ (e i).src, Φ (e i).tgt⟩, fun i => Ψ (F i), ?_, ?_, ?_, n, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Use `⟨(hEdge r (e i)).1 (he i).1, ?_⟩` and prove the remaining obligations. Use `show Φ (e i).tgt = L`. Rewrite using `[(he i).2, Φ.apply_symm_apply]`.

Introduce `i`. Establish `hFi` using `hF i`. Simplify using `only [Nsrc, Re, Submodule.mem_inf, Submodule.mem_iInf] at hFi ⊢`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h` using `sl_scale I.φK Ψ hΨ _ (hHL (e i).src) hFi.1`.

Rewrite `h` using `[hwK]`. Then use the resulting hypothesis. Introduce `e' he'`. Establish `hb : IsEdge p n' r (back e') ∧ (back e').src = (e i).src`. Use `⟨hbackEdge e' he'.1, ?_⟩` and prove the remaining obligations. Use `show Φ.symm e'.src = (e i).src`.

Rewrite using `[he'.2]`. Conclude with `Φ.symm_apply_apply _`. Establish `h` using `sl_scale I.φK Ψ hΨ _ (hHLe' e') (hFi.2 (back e') hb)`. Rewrite `h` using `[hwK]`. Then use the resulting hypothesis. Introduce `i e' he' hsrc hne`.

Establish `hb : (back e').src = (e i).src` using `by show Φ.symm e'.src = (e i).src`. Rewrite using `[hsrc]`. Conclude with `Φ.symm_apply_apply _`. Establish `hne' : back e' ≠ e i`. Introduce `h`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[← hback e', h]`. Establish `hx` using `hF' i (back e') (hbackEdge e' he') hb hne'`. Simplify using `only [Re] at hx ⊢`. Establish `h` using `sl_scale2 I.φK Ψ hΨ _ _ (hHLe' e') hx`.

Rewrite `h` using `[hwK, hwK]`. Then use the resulting hypothesis. Rewrite using `[← hdim]`. Conclude with `hn`. Establish `hN : ∀ G, G ∈ Ntgt p n' R₁.ι R₁.σ R₁.w r lam0 t (Φ.symm L) → dT I.φK Ψ hΨ G ∈ Ntgt p n' R₂.ι R₂.σ R₂.w r lam0 t L`. Introduce `G hG`.

Simplify using `only [Ntgt, Re', Submodule.mem_inf, Submodule.mem_iInf] at hG ⊢`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h` using `sl_scale_dual I.φO I.φK Ψ hΨ I.hOK _ (hHL (Φ.symm L)) hG.1`. Rewrite `h` using `[hwK, Φ.apply_symm_apply]`. Then use the resulting hypothesis. Introduce `e' he'`.

Establish `hb : IsEdge p n' r (back e') ∧ (back e').tgt = Φ.symm L`. Use `⟨hbackEdge e' he'.1, ?_⟩` and prove the remaining obligations. Use `show Φ.symm e'.tgt = Φ.symm L`. Rewrite using `[he'.2]`. Establish `h` using `sl_scale_dual I.φO I.φK Ψ hΨ I.hOK _ (hHLe' e') (hG.2 (back e') hb)`.

Rewrite `h` using `[hwK]`. Then use the resulting hypothesis. Unfold `GoodRankK at hG ⊢`. Take `⟨u, Mt, hu⟩` from `hG`. Establish `hdTv : ∀ (G : Module.Dual R₁.Kf (Vsp R₁.Kf lam0)) v, dT I.φK Ψ hΨ G v = I.φK (G (Ψ.symm v))` using `fun _ _ => rfl`. Set `u₂ : (Fin n → R₂.O) →ₗ[R₂.O] Ntgt p n' R₂.ι R₂.σ R₂.w r lam0 t L` to `{ toFun := fun x => ⟨dT I.φK Ψ hΨ (u fun j => I.φO.symm (x j)), hN _ (u _).2⟩ map_add' := by`.

Introduce `x y`. Establish `hx : (fun j => I.φO.symm ((x + y) j)) = (fun j => I.φO.symm (x j)) + (fun j => I.φO.symm (y j))`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [hx, map_add, Submodule.coe_add, LinearMap.add_apply, hdTv]`. Use the proof step `map_smul' := by`. Introduce `c x`.

Establish `hx : (fun j => I.φO.symm ((c • x) j)) = I.φO.symm c • (fun j => I.φO.symm (x j))`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Apply `Subtype.ext` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `v`. Use `show I.φK ((u fun j => I.φO.symm ((c • x) j) : Module.Dual R₁.Kf (Vsp R₁.Kf lam0)) (Ψ.symm v)) = (c • (dT I.φK Ψ hΨ (u fun j => I.φO.symm (x j)) : Module.Dual R₂.Kf (Vsp R₂.Kf lam0))) v`. Rewrite using `[hx, map_smul, LinearMap.smul_apply, hdTv]`. Simplify using `only [SetLike.val_smul, Submodule.coe_smul_of_tower, LinearMap.smul_apply]`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, I.hOK, RingEquiv.apply_symm_apply] }`.

Use `⟨u₂, Mt.map I.φO, ?_⟩` and prove the remaining obligations. Introduce `x j`. Establish `hbe : ∀ i (G : Module.Dual R₁.Kf (Vsp R₁.Kf lam0)), be p r lam0 (Ψ (F i)) (dT I.φK Ψ hΨ G) = I.φK (be p r lam0 (F i) G)`. Introduce `i G`. Simplify using `only [be]`.

Rewrite using `[← hpK, ← hΨ, dT_apply]`. Establish `hx` using `hu (fun j => I.φO.symm (x j)) j`. Use `show ∑ i, algebraMap R₂.O R₂.Kf (I.φO (Mt j i)) * be p r lam0 (Ψ (F i)) (dT I.φK Ψ hΨ (u fun j => I.φO.symm (x j))) = algebraMap R₂.O R₂.Kf ((p : R₂.O) ^ D * x j)`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hbe, map_mul, I.hOK]`. Use `_ = I.φK (∑ i, algebraMap R₁.O R₁.Kf (Mt j i) * be p r lam0 (F i) (u fun j => I.φO.symm (x j) : Module.Dual R₁.Kf (Vsp R₁.Kf lam0))) := (map_sum _ _ _).symm`. Use `_ = I.φK (algebraMap R₁.O R₁.Kf ((p : R₁.O) ^ D * I.φO.symm (x j))) := by rw [hx]`. Use `_ = algebraMap R₂.O R₂.Kf ((p : R₂.O) ^ D * x j) := by`. Rewrite using `[I.hOK, map_mul, map_pow, map_natCast, RingEquiv.apply_symm_apply]`.
-/
theorem lpRingIndep_of (h1 : RestRSIso) (h2 : RestHLTransport) : LPRingIndep := by
  unfold LPRingIndep
  intro p n' R₁ R₂ m r lam0 t D κ cStar hLP
  obtain ⟨I⟩ := h1 p n' R₁ R₂
  obtain ⟨Φ, Ψ, hΨ, hLat, hEdge, hHL, hHLe, hdim⟩ := h2 p n' R₁ R₂ I m lam0

  have hwK : ∀ z : ℤ, I.φK (algebraMap R₁.O R₁.Kf R₁.w ^ z) = algebraMap R₂.O R₂.Kf R₂.w ^ z := by
    intro z; rw [map_zpow₀, I.hOK, I.hw]
  have hpK : ∀ z : ℤ, I.φK ((p : R₁.Kf) ^ z) = (p : R₂.Kf) ^ z := by
    intro z; rw [map_zpow₀, map_natCast]

  let back : Edge R₂.W R₂.Qq (m + 1) → Edge R₁.W R₁.Qq (m + 1) := fun e => ⟨Φ.symm e.src, Φ.symm e.tgt⟩
  have hback : ∀ e, (⟨Φ (back e).src, Φ (back e).tgt⟩ : Edge R₂.W R₂.Qq (m + 1)) = e := by
    intro e; cases e; simp [back]
  have hbackEdge : ∀ e, IsEdge p n' r e → IsEdge p n' r (back e) := by
    intro e he; rw [hEdge r (back e), hback]; exact he
  have hHLe' : ∀ e x, x ∈ HLe p R₁.ι R₁.σ R₁.w lam0 (back e) ↔ Ψ x ∈ HLe p R₂.ι R₂.σ R₂.w lam0 e := by
    intro e x; have h := hHLe (back e) x; rwa [hback] at h
  unfold LPprime at hLP ⊢
  obtain ⟨hc, hall⟩ := hLP
  refine ⟨hc, fun L hL => ?_⟩
  have hL1 : IsLattice R₁.W (Φ.symm L) := by rw [hLat, Φ.apply_symm_apply]; exact hL
  have hAt := hall _ hL1
  unfold LPprimeAt at hAt ⊢
  obtain ⟨M, e, F, he, hF, hF', n, hn, hG⟩ := hAt
  refine ⟨M, fun i => ⟨Φ (e i).src, Φ (e i).tgt⟩, fun i => Ψ (F i), ?_, ?_, ?_, n, ?_, ?_⟩
  · intro i
    refine ⟨(hEdge r (e i)).1 (he i).1, ?_⟩
    show Φ (e i).tgt = L
    rw [(he i).2, Φ.apply_symm_apply]
  · intro i
    have hFi := hF i
    simp only [Nsrc, Re, Submodule.mem_inf, Submodule.mem_iInf] at hFi ⊢
    refine ⟨?_, ?_⟩
    · have h := sl_scale I.φK Ψ hΨ _ (hHL (e i).src) hFi.1
      rwa [hwK] at h
    · intro e' he'
      have hb : IsEdge p n' r (back e') ∧ (back e').src = (e i).src := by
        refine ⟨hbackEdge e' he'.1, ?_⟩
        show Φ.symm e'.src = (e i).src
        rw [he'.2]; exact Φ.symm_apply_apply _
      have h := sl_scale I.φK Ψ hΨ _ (hHLe' e') (hFi.2 (back e') hb)
      rwa [hwK] at h
  · intro i e' he' hsrc hne
    have hb : (back e').src = (e i).src := by
      show Φ.symm e'.src = (e i).src
      rw [hsrc]; exact Φ.symm_apply_apply _
    have hne' : back e' ≠ e i := by
      intro h; apply hne; rw [← hback e', h]
    have hx := hF' i (back e') (hbackEdge e' he') hb hne'
    simp only [Re] at hx ⊢
    have h := sl_scale2 I.φK Ψ hΨ _ _ (hHLe' e') hx
    rwa [hwK, hwK] at h
  · rw [← hdim]; exact hn
  ·
    have hN : ∀ G, G ∈ Ntgt p n' R₁.ι R₁.σ R₁.w r lam0 t (Φ.symm L) →
        dT I.φK Ψ hΨ G ∈ Ntgt p n' R₂.ι R₂.σ R₂.w r lam0 t L := by
      intro G hG
      simp only [Ntgt, Re', Submodule.mem_inf, Submodule.mem_iInf] at hG ⊢
      refine ⟨?_, ?_⟩
      · have h := sl_scale_dual I.φO I.φK Ψ hΨ I.hOK _ (hHL (Φ.symm L)) hG.1
        rwa [hwK, Φ.apply_symm_apply] at h
      · intro e' he'
        have hb : IsEdge p n' r (back e') ∧ (back e').tgt = Φ.symm L := by
          refine ⟨hbackEdge e' he'.1, ?_⟩
          show Φ.symm e'.tgt = Φ.symm L
          rw [he'.2]
        have h := sl_scale_dual I.φO I.φK Ψ hΨ I.hOK _ (hHLe' e') (hG.2 (back e') hb)
        rwa [hwK] at h
    unfold GoodRankK at hG ⊢
    obtain ⟨u, Mt, hu⟩ := hG
    have hdTv : ∀ (G : Module.Dual R₁.Kf (Vsp R₁.Kf lam0)) v, dT I.φK Ψ hΨ G v = I.φK (G (Ψ.symm v)) :=
      fun _ _ => rfl
    let u₂ : (Fin n → R₂.O) →ₗ[R₂.O] Ntgt p n' R₂.ι R₂.σ R₂.w r lam0 t L :=
      { toFun := fun x => ⟨dT I.φK Ψ hΨ (u fun j => I.φO.symm (x j)), hN _ (u _).2⟩
        map_add' := by
          intro x y
          have hx : (fun j => I.φO.symm ((x + y) j)) =
              (fun j => I.φO.symm (x j)) + (fun j => I.φO.symm (y j)) := by
            funext j; simp
          apply Subtype.ext
          apply LinearMap.ext
          intro v
          simp only [hx, map_add, Submodule.coe_add, LinearMap.add_apply, hdTv]
        map_smul' := by
          intro c x
          have hx : (fun j => I.φO.symm ((c • x) j)) = I.φO.symm c • (fun j => I.φO.symm (x j)) := by
            funext j; simp
          apply Subtype.ext
          apply LinearMap.ext
          intro v
          show I.φK ((u fun j => I.φO.symm ((c • x) j) : Module.Dual R₁.Kf (Vsp R₁.Kf lam0)) (Ψ.symm v)) =
            (c • (dT I.φK Ψ hΨ (u fun j => I.φO.symm (x j)) : Module.Dual R₂.Kf (Vsp R₂.Kf lam0))) v
          rw [hx, map_smul, LinearMap.smul_apply, hdTv]
          simp only [SetLike.val_smul, Submodule.coe_smul_of_tower, LinearMap.smul_apply]
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, I.hOK, RingEquiv.apply_symm_apply] }
    refine ⟨u₂, Mt.map I.φO, ?_⟩
    intro x j
    have hbe : ∀ i (G : Module.Dual R₁.Kf (Vsp R₁.Kf lam0)),
        be p r lam0 (Ψ (F i)) (dT I.φK Ψ hΨ G) = I.φK (be p r lam0 (F i) G) := by
      intro i G
      simp only [be]
      rw [← hpK, ← hΨ, dT_apply]
    have hx := hu (fun j => I.φO.symm (x j)) j
    show ∑ i, algebraMap R₂.O R₂.Kf (I.φO (Mt j i)) *
        be p r lam0 (Ψ (F i)) (dT I.φK Ψ hΨ (u fun j => I.φO.symm (x j))) =
      algebraMap R₂.O R₂.Kf ((p : R₂.O) ^ D * x j)
    calc ∑ i, algebraMap R₂.O R₂.Kf (I.φO (Mt j i)) *
          be p r lam0 (Ψ (F i)) (dT I.φK Ψ hΨ (u fun j => I.φO.symm (x j)))
        = ∑ i, I.φK (algebraMap R₁.O R₁.Kf (Mt j i) *
            be p r lam0 (F i) (u fun j => I.φO.symm (x j) : Module.Dual R₁.Kf (Vsp R₁.Kf lam0))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hbe, map_mul, I.hOK]
      _ = I.φK (∑ i, algebraMap R₁.O R₁.Kf (Mt j i) *
            be p r lam0 (F i) (u fun j => I.φO.symm (x j) : Module.Dual R₁.Kf (Vsp R₁.Kf lam0))) :=
          (map_sum _ _ _).symm
      _ = I.φK (algebraMap R₁.O R₁.Kf ((p : R₁.O) ^ D * I.φO.symm (x j))) := by rw [hx]
      _ = algebraMap R₂.O R₂.Kf ((p : R₂.O) ^ D * x j) := by
          rw [I.hOK, map_mul, map_pow, map_natCast, RingEquiv.apply_symm_apply]

end Formalism.MainNotions.flipOneThree.Pf

end
