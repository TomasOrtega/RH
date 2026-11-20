import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RGHyp

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG7

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

/- English proof (translation)
Take `⟨w, hw₁, hw₂⟩` from `(D.hθ m₁ m₂).1 h`. Establish `key : ((ψ.symm b - w : H.W0 t₁.f t₁.f') : V) ∈ t₁.abelian₂`. Rewrite using `[D.hth]`. Establish `e : ((ψ (ψ.symm b - w) : H.W0 t₂.f t₂.f') : V) = ((m₂ : V) + (b : V)) - ((m₂ : V) + ((ψ w : H.W0 t₂.f t₂.f') : V))`. Rewrite using `[map_sub, LinearEquiv.apply_symm_apply, Submodule.coe_sub]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `Λ₂.sub_mem hb hw₂`. Establish `e2 : (m₁ : V) + ((ψ.symm b : H.W0 t₁.f t₁.f') : V) = ((m₁ : V) + (w : V)) + ((ψ.symm b - w : H.W0 t₁.f t₁.f') : V)`. Rewrite using `[Submodule.coe_sub]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e2]`. Conclude with `t₁.abelian₂.add_mem hw₁ key`.
-/
private theorem add_psi_symm_mem_lam_of_theta_ddMk_eq {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V}
    {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')} {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂}
    {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'} (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    (m₁ : MMsharp H t₁) (m₂ : MMsharp H t₂) (h : θ (ddMk H t₁ m₁) = ddMk H t₂ m₂)
    (b : H.W0 t₂.f t₂.f') (hb : (m₂ : V) + (b : V) ∈ Λ₂) :
    (m₁ : V) + ((ψ.symm b : H.W0 t₁.f t₁.f') : V) ∈ t₁.abelian₂ := by
  obtain ⟨w, hw₁, hw₂⟩ := (D.hθ m₁ m₂).1 h
  have key : ((ψ.symm b - w : H.W0 t₁.f t₁.f') : V) ∈ t₁.abelian₂ := by
    rw [D.hth]
    have e : ((ψ (ψ.symm b - w) : H.W0 t₂.f t₂.f') : V) = ((m₂ : V) + (b : V)) - ((m₂ : V) + ((ψ w : H.W0 t₂.f t₂.f') : V)) := by
      rw [map_sub, LinearEquiv.apply_symm_apply, Submodule.coe_sub]
      abel
    rw [e]
    exact Λ₂.sub_mem hb hw₂
  have e2 : (m₁ : V) + ((ψ.symm b : H.W0 t₁.f t₁.f') : V) = ((m₁ : V) + (w : V)) + ((ψ.symm b - w : H.W0 t₁.f t₁.f') : V) := by
    rw [Submodule.coe_sub]
    abel
  rw [e2]
  exact t₁.abelian₂.add_mem hw₁ key

/- English proof (translation)
Introduce and unpack `p ⟨x', x, hx'L, hxL, hdiff, rfl⟩`. Take `⟨l, hl, hl_eq⟩` from `exists_of_mem_smulLat H hdiff`. Take `⟨a, ha, b, hb, hab⟩` from `dec_of D.hU₂ (x : V)`. Take `⟨a', ha', b', hb', hab'⟩` from `dec_of D.hU₂ (x' : V)`. Take `⟨a'', ha'', b'', hb'', hab''⟩` from `dec_of D.hU₂ l`.

Take `⟨hda, hdb⟩` from `dec_diff D.hU₂ _ ha ha' ha'' hb hb' hb'' hab hab' hab'' hl_eq`. Establish `hxL2 : a + b ∈ Λ₂` using `by rw [hab]; exact hxL`. Establish `hx'L2 : a' + b' ∈ Λ₂` using `by rw [hab']; exact hx'L`. Establish `hlL2 : a'' + b'' ∈ Λ₂` using `by rw [hab'']; exact hl`. Establish `sa : a ∈ MMsharp H t₂` using `part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha hb hxL2`.

Establish `sa' : a' ∈ MMsharp H t₂` using `part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha' hb' hx'L2`. Establish `sa'' : a'' ∈ MMsharp H t₂` using `part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha'' hb'' hlL2`. Establish `pa : a ∈ H.perp (H.X t₂.f)`. Establish `e : a = (x : V) - b` using `by rw [← hab]; abel`. Rewrite using `[e]`.

Conclude with `Submodule.sub_mem _ x.2 (mem_perp_isotropicSpan_of_mem_framePerp H hb)`. Establish `pa' : a' ∈ H.perp (H.X t₂.f')`. Establish `e : a' = (x' : V) - b'` using `by rw [← hab']; abel`. Rewrite using `[e]`. Conclude with `Submodule.sub_mem _ x'.2 (mem_perp_isotropicSpan_of_mem_framePerp' H hb')`.

Establish `hmem : (ddMk H t₂ ⟨a, sa⟩, ddMk H t₂ ⟨a'', sa''⟩, H.mkW t₂.f ⟨a, pa⟩, H.mkW t₂.f' ⟨a', pa'⟩) ∈ GamR H t₂ (algebraMap F E (g.q : F))` using `⟨⟨a, sa⟩, ⟨a', sa'⟩, ⟨a'', sa''⟩, pa, pa', hda, rfl⟩`. Rewrite `hmem` using `[← hG]`. Take `⟨q, ⟨u, u', u'', hu, hu', hdu, rfl⟩, hq⟩` from `hmem`. Simplify using `only [Prod.mk.injEq] at hq`. Take `⟨h1, h2, h3, h4⟩` from `hq`.

Establish `hy` using `add_psi_symm_mem_lam_of_theta_ddMk_eq H D u ⟨a, sa⟩ h1 ⟨b, hb⟩ hxL2`. Establish `hy''` using `add_psi_symm_mem_lam_of_theta_ddMk_eq H D u'' ⟨a'', sa''⟩ h2 ⟨b'', hb''⟩ hlL2`. Establish `hn' : ψ.symm ⟨b', hb'⟩ = ψ.symm ⟨b, hb⟩ - (algebraMap F E (g.q : F)) • ψ.symm ⟨b'', hb''⟩`. Rewrite using `[← map_smul, ← map_sub]`. Use `congr 1`.

Use `ext`. Simplify using `only [Submodule.coe_sub, Submodule.coe_smul]`. Rewrite using `[← hdb]`. Normalize the expressions using the abelian group laws. Establish `hu'e : (u' : V) = (u : V) - (algebraMap F E (g.q : F)) • (u'' : V)`.

Rewrite using `[← hdu]`. Normalize the expressions using the abelian group laws. Establish `hy'e : (u' : V) + ((ψ.symm ⟨b', hb'⟩ : H.W0 t₁.f t₁.f') : V) = ((u : V) + ((ψ.symm ⟨b, hb⟩ : H.W0 t₁.f t₁.f') : V)) - (algebraMap F E (g.q : F)) • ((u'' : V) + ((ψ.symm ⟨b'', hb''⟩ : H.W0 t₁.f t₁.f') : V))`. Rewrite using `[hn', hu'e, Submodule.coe_sub, Submodule.coe_smul, smul_add]`. Normalize the expressions using the abelian group laws.

Establish `py : (u : V) + ((ψ.symm ⟨b, hb⟩ : H.W0 t₁.f t₁.f') : V) ∈ H.perp (H.X t₁.f)` using `Submodule.add_mem _ hu (mem_perp_isotropicSpan_of_mem_framePerp H (ψ.symm ⟨b, hb⟩).2)`. Establish `py' : (u' : V) + ((ψ.symm ⟨b', hb'⟩ : H.W0 t₁.f t₁.f') : V) ∈ H.perp (H.X t₁.f')` using `Submodule.add_mem _ hu' (mem_perp_isotropicSpan_of_mem_framePerp' H (ψ.symm ⟨b', hb'⟩).2)`. Establish `hcy : (algebraMap F E (g.q : F)) • ((u'' : V) + ((ψ.symm ⟨b'', hb''⟩ : H.W0 t₁.f t₁.f') : V)) ∈ t₁.abelian₂` using `smul_mem_lat g t₁.abelian₂ hy''`. Establish `hyL' : (u' : V) + ((ψ.symm ⟨b', hb'⟩ : H.W0 t₁.f t₁.f') : V) ∈ t₁.abelian₂`. Rewrite using `[hy'e]`.

Conclude with `t₁.abelian₂.sub_mem hy hcy`. Establish `hdL : ((u : V) + ((ψ.symm ⟨b, hb⟩ : H.W0 t₁.f t₁.f') : V)) - ((u' : V) + ((ψ.symm ⟨b', hb'⟩ : H.W0 t₁.f t₁.f') : V)) ∈ H.smulLat (algebraMap F E (g.q : F)) t₁.abelian₂`. Rewrite using `[hy'e, sub_sub_cancel]`. Conclude with `Submodule.subset_span ⟨_, hy'', rfl⟩`. Use `⟨(H.mkW t₁.f' ⟨_, py'⟩, H.mkW t₁.f ⟨_, py⟩), ⟨⟨_, py'⟩, ⟨_, py⟩, hyL', hy, hdL, rfl⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [Prod.map]`. Use `congr 1`. Rewrite using `[mkW_add H _ _ hu' (mem_perp_isotropicSpan_of_mem_framePerp' H (ψ.symm ⟨b', hb'⟩).2), map_add, h4, D.hC1', LinearEquiv.apply_symm_apply, ← mkW_add]`. Conclude with `mkW_congr H _ _ hab'`. Rewrite using `[mkW_add H _ _ hu (mem_perp_isotropicSpan_of_mem_framePerp H (ψ.symm ⟨b, hb⟩).2), map_add, h3, D.hC1, LinearEquiv.apply_symm_apply, ← mkW_add]`.

Conclude with `mkW_congr H _ _ hab`.
-/
theorem rg_bwd_sup (g : SplitG M.L) {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V}
    {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')} {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂}
    {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'} (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    (hG : (fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' GamR H t₁ (algebraMap F E (g.q : F)) =
      GamR H t₂ (algebraMap F E (g.q : F))) :
    H.iotaGraph g ⟨Λ₂, t₂.f, t₂.f', t₂.T, t₂.T'⟩ ⊆ Prod.map φ' φ '' H.iotaGraph g t₁ := by
  rintro p ⟨x', x, hx'L, hxL, hdiff, rfl⟩
  obtain ⟨l, hl, hl_eq⟩ := exists_of_mem_smulLat H hdiff
  obtain ⟨a, ha, b, hb, hab⟩ := dec_of D.hU₂ (x : V)
  obtain ⟨a', ha', b', hb', hab'⟩ := dec_of D.hU₂ (x' : V)
  obtain ⟨a'', ha'', b'', hb'', hab''⟩ := dec_of D.hU₂ l
  obtain ⟨hda, hdb⟩ := dec_diff D.hU₂ _ ha ha' ha'' hb hb' hb'' hab hab' hab'' hl_eq
  have hxL2 : a + b ∈ Λ₂ := by rw [hab]; exact hxL
  have hx'L2 : a' + b' ∈ Λ₂ := by rw [hab']; exact hx'L
  have hlL2 : a'' + b'' ∈ Λ₂ := by rw [hab'']; exact hl
  have sa : a ∈ MMsharp H t₂ := part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha hb hxL2
  have sa' : a' ∈ MMsharp H t₂ := part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha' hb' hx'L2
  have sa'' : a'' ∈ MMsharp H t₂ := part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha'' hb'' hlL2
  have pa : a ∈ H.perp (H.X t₂.f) := by
    have e : a = (x : V) - b := by rw [← hab]; abel
    rw [e]
    exact Submodule.sub_mem _ x.2 (mem_perp_isotropicSpan_of_mem_framePerp H hb)
  have pa' : a' ∈ H.perp (H.X t₂.f') := by
    have e : a' = (x' : V) - b' := by rw [← hab']; abel
    rw [e]
    exact Submodule.sub_mem _ x'.2 (mem_perp_isotropicSpan_of_mem_framePerp' H hb')
  have hmem : (ddMk H t₂ ⟨a, sa⟩, ddMk H t₂ ⟨a'', sa''⟩, H.mkW t₂.f ⟨a, pa⟩, H.mkW t₂.f' ⟨a', pa'⟩) ∈
      GamR H t₂ (algebraMap F E (g.q : F)) :=
    ⟨⟨a, sa⟩, ⟨a', sa'⟩, ⟨a'', sa''⟩, pa, pa', hda, rfl⟩
  rw [← hG] at hmem
  obtain ⟨q, ⟨u, u', u'', hu, hu', hdu, rfl⟩, hq⟩ := hmem
  simp only [Prod.mk.injEq] at hq
  obtain ⟨h1, h2, h3, h4⟩ := hq
  have hy := add_psi_symm_mem_lam_of_theta_ddMk_eq H D u ⟨a, sa⟩ h1 ⟨b, hb⟩ hxL2
  have hy'' := add_psi_symm_mem_lam_of_theta_ddMk_eq H D u'' ⟨a'', sa''⟩ h2 ⟨b'', hb''⟩ hlL2
  have hn' : ψ.symm ⟨b', hb'⟩ = ψ.symm ⟨b, hb⟩ - (algebraMap F E (g.q : F)) • ψ.symm ⟨b'', hb''⟩ := by
    rw [← map_smul, ← map_sub]
    congr 1
    ext
    simp only [Submodule.coe_sub, Submodule.coe_smul]
    rw [← hdb]
    abel
  have hu'e : (u' : V) = (u : V) - (algebraMap F E (g.q : F)) • (u'' : V) := by
    rw [← hdu]; abel
  have hy'e : (u' : V) + ((ψ.symm ⟨b', hb'⟩ : H.W0 t₁.f t₁.f') : V) =
      ((u : V) + ((ψ.symm ⟨b, hb⟩ : H.W0 t₁.f t₁.f') : V)) -
        (algebraMap F E (g.q : F)) • ((u'' : V) + ((ψ.symm ⟨b'', hb''⟩ : H.W0 t₁.f t₁.f') : V)) := by
    rw [hn', hu'e, Submodule.coe_sub, Submodule.coe_smul, smul_add]
    abel
  have py : (u : V) + ((ψ.symm ⟨b, hb⟩ : H.W0 t₁.f t₁.f') : V) ∈ H.perp (H.X t₁.f) :=
    Submodule.add_mem _ hu (mem_perp_isotropicSpan_of_mem_framePerp H (ψ.symm ⟨b, hb⟩).2)
  have py' : (u' : V) + ((ψ.symm ⟨b', hb'⟩ : H.W0 t₁.f t₁.f') : V) ∈ H.perp (H.X t₁.f') :=
    Submodule.add_mem _ hu' (mem_perp_isotropicSpan_of_mem_framePerp' H (ψ.symm ⟨b', hb'⟩).2)
  have hcy : (algebraMap F E (g.q : F)) • ((u'' : V) + ((ψ.symm ⟨b'', hb''⟩ : H.W0 t₁.f t₁.f') : V)) ∈ t₁.abelian₂ :=
    smul_mem_lat g t₁.abelian₂ hy''
  have hyL' : (u' : V) + ((ψ.symm ⟨b', hb'⟩ : H.W0 t₁.f t₁.f') : V) ∈ t₁.abelian₂ := by
    rw [hy'e]; exact t₁.abelian₂.sub_mem hy hcy
  have hdL : ((u : V) + ((ψ.symm ⟨b, hb⟩ : H.W0 t₁.f t₁.f') : V)) -
      ((u' : V) + ((ψ.symm ⟨b', hb'⟩ : H.W0 t₁.f t₁.f') : V)) ∈
      H.smulLat (algebraMap F E (g.q : F)) t₁.abelian₂ := by
    rw [hy'e, sub_sub_cancel]
    exact Submodule.subset_span ⟨_, hy'', rfl⟩
  refine ⟨(H.mkW t₁.f' ⟨_, py'⟩, H.mkW t₁.f ⟨_, py⟩), ⟨⟨_, py'⟩, ⟨_, py⟩, hyL', hy, hdL, rfl⟩, ?_⟩
  simp only [Prod.map]
  congr 1
  · rw [mkW_add H _ _ hu' (mem_perp_isotropicSpan_of_mem_framePerp' H (ψ.symm ⟨b', hb'⟩).2), map_add, h4, D.hC1',
      LinearEquiv.apply_symm_apply, ← mkW_add]
    exact mkW_congr H _ _ hab'
  · rw [mkW_add H _ _ hu (mem_perp_isotropicSpan_of_mem_framePerp H (ψ.symm ⟨b, hb⟩).2), map_add, h3, D.hC1,
      LinearEquiv.apply_symm_apply, ← mkW_add]
    exact mkW_congr H _ _ hab

end RG7

end Formalism.L2.SG.LsDatumA
