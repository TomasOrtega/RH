import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlueBackOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocGlue

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Inj

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

/- English proof (translation)
Rewrite using `[Set.Sum.elim_range, Submodule.span_union]`. Both sides reduce to the same expression.
-/
theorem hermSp_W0_eq_perp_span_range_MMfam {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f f' : Fin (r + 1) → V) : H.W0 f f' = H.perp (Submodule.span E (Set.range (Sum.elim f f'))) := by
  rw [Set.Sum.elim_range, Submodule.span_union]
  rfl

/- English proof (translation)
Apply `Submodule.span_le.mpr` to reduce the goal to its premises. Introduce and unpack `_ ⟨i, rfl⟩`. Unfold `HermSp.MMfam`. Use `split`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`.

Name the introduced variables `g _`. Establish `hq : ((g.q : F)) ≠ 0`. Introduce `h0`. Conclude with `g.q_irr.ne_zero (Subtype.ext h0)`. Use `set c : E := algebraMap F E ((g.q : F))⁻¹ with hc`.

Establish `hcu : IsUnit c`. Rewrite using `[hc]`. Conclude with `(IsUnit.mk0 _ (inv_ne_zero hq)).map (algebraMap F E)`. Break down `i with a | a` into its components or cases. Conclude with `Submodule.subset_span ⟨Sum.inl a, rfl⟩`.

Establish `h1 : t.f a ∈ Submodule.span E (Set.range (Sum.elim t.f fun b => c • (t.f' b - t.f b)))` using `Submodule.subset_span ⟨Sum.inl a, rfl⟩`. Establish `h2 : c • (t.f' a - t.f a) ∈ Submodule.span E (Set.range (Sum.elim t.f fun b => c • (t.f' b - t.f b)))` using `Submodule.subset_span ⟨Sum.inr a, rfl⟩`. Establish `h3 : t.f' a = t.f a + (((hcu.unit)⁻¹ : Eˣ) : E) • (c • (t.f' a - t.f a))`. Rewrite using `[smul_smul, IsUnit.val_inv_mul, one_smul]`. Normalize the expressions using the abelian group laws.

Use `show t.f' a ∈ _`. Rewrite using `[h3]`. Conclude with `Submodule.add_mem _ h1 (Submodule.smul_mem _ _ h2)`.
-/
theorem span_frames_le_MM {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (t : Term V M r) :
    Submodule.span E (Set.range (Sum.elim t.f t.f')) ≤ Submodule.span E (Set.range (H.MMfam t)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  unfold HermSp.MMfam
  split
  · exact Submodule.subset_span ⟨i, rfl⟩
  · rename_i g _
    have hq : ((g.q : F)) ≠ 0 := by
      intro h0
      exact g.q_irr.ne_zero (Subtype.ext h0)
    set c : E := algebraMap F E ((g.q : F))⁻¹ with hc
    have hcu : IsUnit c := by
      rw [hc]
      exact (IsUnit.mk0 _ (inv_ne_zero hq)).map (algebraMap F E)
    rcases i with a | a
    · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    · have h1 : t.f a ∈ Submodule.span E (Set.range (Sum.elim t.f fun b => c • (t.f' b - t.f b))) :=
        Submodule.subset_span ⟨Sum.inl a, rfl⟩
      have h2 : c • (t.f' a - t.f a) ∈ Submodule.span E (Set.range (Sum.elim t.f fun b => c • (t.f' b - t.f b))) :=
        Submodule.subset_span ⟨Sum.inr a, rfl⟩
      have h3 : t.f' a = t.f a + (((hcu.unit)⁻¹ : Eˣ) : E) • (c • (t.f' a - t.f a)) := by
        rw [smul_smul, IsUnit.val_inv_mul, one_smul]
        abel
      show t.f' a ∈ _
      rw [h3]
      exact Submodule.add_mem _ h1 (Submodule.smul_mem _ _ h2)

/- English proof (translation)
Use `le_antisymm ?_ (span_frames_le_MM H t)` and prove the remaining obligations. Apply `Submodule.span_le.mpr` to reduce the goal to its premises. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `h` using `MMfam_mem_sup H t i`. Use `(sup_le ?_ ?_ : H.Xp t.f ⊔ H.Xp t.f' ≤ _) h` and prove the remaining obligations.

Conclude with `Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inl a, rfl⟩)`. Conclude with `Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inr a, rfl⟩)`.
-/
private theorem span_MMfam_eq_span_f_f' {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (t : Term V M r) :
    Submodule.span E (Set.range (H.MMfam t)) = Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
  refine le_antisymm ?_ (span_frames_le_MM H t)
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have h := MMfam_mem_sup H t i
  refine (sup_le ?_ ?_ : H.Xp t.f ⊔ H.Xp t.f' ≤ _) h
  · exact Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inl a, rfl⟩)
  · exact Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inr a, rfl⟩)

/- English proof (translation)
Establish `h` using `isCompl_span_frames_W0 H t.f t.f' t.T t.T' ⟨ht.1.2.1.2.1, ht.1.2.1.2.2.1⟩ ⟨ht.1.2.2.1.2.1, ht.1.2.2.1.2.2.1⟩ ht.1.2.2.2.1 (isUnit_Gdet H _ _ _ _ ht.1.2.2.2.2.1)`. Rewrite `h` using `[hermSp_W0_eq_perp_span_range_MMfam]`. Then use the resulting hypothesis.
-/
private theorem isCompl_span_perp_of_isGeneric {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (t : Term V M r) (ht : H.IsGeneric t) :
    IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f')))
      (H.perp (Submodule.span E (Set.range (Sum.elim t.f t.f')))) := by
  have h := isCompl_span_frames_W0 H t.f t.f' t.T t.T' ⟨ht.1.2.1.2.1, ht.1.2.1.2.2.1⟩
    ⟨ht.1.2.2.1.2.1, ht.1.2.2.1.2.2.1⟩ ht.1.2.2.2.1 (isUnit_Gdet H _ _ _ _ ht.1.2.2.2.2.1)
  rwa [hermSp_W0_eq_perp_span_range_MMfam] at h

/- English proof (translation)
Use `⟨by rw [span_MMfam_eq_span_f_f']; exact hu, ?_⟩` and prove the remaining obligations. Introduce `m hm`. Apply `hint m` to reduce the goal to its premises. Conclude with `(Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact hmem a)) hm`. Rewrite using `[← span_MMfam_eq_span_f_f' H t]`.

Conclude with `Submodule.span_le_restrictScalars (↥M.L.O) E _ hm`.
-/
private theorem mem_MMsharp_of_integral_pairing {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (t : Term V M r) (abelian₂ : Submodule (↥M.L.O) V) (hmem : ∀ a, H.MMfam t a ∈ abelian₂) (u : V)
    (hu : u ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')))
    (hint : ∀ y ∈ abelian₂, y ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) → H.h u y ∈ M.L.O) :
    u ∈ MMsharp H t := by
  refine ⟨by rw [span_MMfam_eq_span_f_f']; exact hu, ?_⟩
  intro m hm
  apply hint m
  · exact (Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact hmem a)) hm
  · rw [← span_MMfam_eq_span_f_f' H t]
    exact Submodule.span_le_restrictScalars (↥M.L.O) E _ hm

/- English proof (translation)
Introduce `V _ _ H hn t₁ f₂ f₂' φ φ' hT Λ₂ Λ₂' hG hTh hG' hTh' hrel`. Take `⟨ψ, hψh, hψ⟩` from `hC V H hn t₁ f₂ f₂' φ φ' hT hG.1.2.2.2.1`. Establish `hW₁` using `hermSp_W0_eq_perp_span_range_MMfam H t₁.f t₁.f'`. Establish `hW₂` using `hermSp_W0_eq_perp_span_range_MMfam H f₂ f₂'`. Establish `hU₁` using `isCompl_span_perp_of_isGeneric H t₁ hT.1`.

Establish `key : ∀ A B : Submodule (↥M.L.O) V, H.IsGeneric { abelian₂` using `A, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } → ThCond H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } A φ φ' → ThCond H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } B φ φ' → (∀ (m₁ : ↥(MMsharp H t₁)) (m₂ : ↥(MMsharp H { abelian₂ := ⊥, f : …`. Introduce `A B hGA hThA hThB hAB x hx`. Set `U₂ : Submodule E V` to `Submodule.span E (Set.range (Sum.elim f₂ f₂'))`. Set `U₁ : Submodule E V` to `Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))`. Establish `hU₂ : IsCompl U₂ (H.perp U₂)` using `isCompl_span_perp_of_isGeneric H _ hGA`.

Establish `gA` using `local_hermitian_glue F E M hM V H A hGA.1.1 U₂ hU₂`. Establish `g₁` using `local_hermitian_glue F E M hM V H t₁.abelian₂ hT.1.1.1 U₁ hU₁`. Take `⟨p, hp, hpint, q, hq, hqint, hxpq⟩ : ∃ p ∈ U₂, (∀ y ∈ A, y ∈ U₂ → H.h p y ∈ M.L.O) ∧ ∃ q ∈ H.perp U₂, (∀ y ∈ A, y ∈ H.perp U₂ → H.h q y ∈ M.L.O) ∧ p + q = x` from `⟨_, Submodule.coe_mem _, (gA.1 _ (Submodule.coe_mem _)).mp ⟨x, hx, rfl⟩, _, Submodule.coe_mem _, (gA.2 _ (Submodule.coe_mem _)).mp ⟨x, hx, rfl⟩, Submodule.projection_add_projection_eq_self hU₂ x⟩`. Establish `hpS : p ∈ MMsharp H { abelian₂` using `⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } := mem_MMsharp_of_integral_pairing H _ A hGA.2.1 p hp hpint`. Establish `hqW : q ∈ H.W0 f₂ f₂'` using `hW₂.ge hq`.

Take `⟨n₁, hψn₁⟩ : ∃ n₁ : ↥(H.W0 t₁.f t₁.f'), (ψ n₁ : V) = q` from `⟨ψ.symm ⟨q, hqW⟩, by simp⟩`. Establish `hcorr₁ : Corr H t₁ { abelian₂` using `⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } φ φ' (n₁ : V) q := (hψ _ _).mpr ⟨n₁.2, hψn₁⟩`. Establish `hn₁int : ∀ y ∈ t₁.abelian₂, y ∈ H.perp U₁ → H.h (n₁ : V) y ∈ M.L.O`. Introduce `y hy hyp`. Establish `hyW : y ∈ H.W0 t₁.f t₁.f'` using `hW₁.ge hyp`.

Establish `hc : Corr H t₁ { abelian₂` using `⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } φ φ' y (ψ ⟨y, hyW⟩ : V) := (hψ _ _).mpr ⟨hyW, rfl⟩`. Establish `hyA : (ψ ⟨y, hyW⟩ : V) ∈ A` using `(hThA _ _ hc).mp hy`. Establish `hyp2 : (ψ ⟨y, hyW⟩ : V) ∈ H.perp U₂` using `hW₂.le (ψ ⟨y, hyW⟩).2`. Establish `e : H.h (n₁ : V) y = H.h q (ψ ⟨y, hyW⟩ : V)`. Rewrite using `[← hψn₁]`.

Conclude with `(hψh n₁ ⟨y, hyW⟩).symm`. Rewrite using `[e]`. Conclude with `hqint _ hyA hyp2`. Establish `hn₁p : (n₁ : V) ∈ H.perp U₁` using `hW₁.le n₁.2`. Take `⟨z, hz, hzn⟩` from `(g₁.2 _ hn₁p).mpr hn₁int`.

Establish `hmS : (U₁.linearProjOfIsCompl (H.perp U₁) hU₁ z : V) ∈ MMsharp H t₁` using `mem_MMsharp_of_integral_pairing H t₁ t₁.abelian₂ hT.1.2.1 _ (Submodule.coe_mem _) ((g₁.1 _ (Submodule.coe_mem _)).mp ⟨z, hz, rfl⟩)`. Establish `hzsum : (U₁.linearProjOfIsCompl (H.perp U₁) hU₁ z : V) + (n₁ : V) = z`. Rewrite using `[← hzn]`. Conclude with `Submodule.projection_add_projection_eq_self hU₁ z`. Establish `hz' : (U₁.linearProjOfIsCompl (H.perp U₁) hU₁ z : V) + (n₁ : V) ∈ t₁.abelian₂`.

Rewrite using `[hzsum]`. Conclude with `hz`. Establish `hglA : GlueRel H t₁ { abelian₂` using `⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } A φ φ' ⟨_, hmS⟩ ⟨p, hpS⟩ := ⟨n₁, q, hcorr₁, hz', by show p + q ∈ A; rw [hxpq]; exact hx⟩`. Take `⟨n₁', n₂', hc', h1', h2'⟩` from `hAB _ _ hglA`. Take `⟨hn₁'W, hψ'⟩` from `(hψ _ _).mp hc'`.

Establish `h1'' : (U₁.linearProjOfIsCompl (H.perp U₁) hU₁ z : V) + n₁' ∈ t₁.abelian₂` using `h1'`. Establish `hd : n₁' - (n₁ : V) ∈ t₁.abelian₂`. Establish `h0` using `t₁.abelian₂.sub_mem h1'' hz'`. Rewrite `h0` using `[add_sub_add_left_eq_sub]`. Then use the resulting hypothesis. Establish `hdW : n₁' - (n₁ : V) ∈ H.W0 t₁.f t₁.f'` using `Submodule.sub_mem _ hn₁'W n₁.2`.

Establish `hψd : (ψ ⟨n₁' - n₁, hdW⟩ : V) = n₂' - q`. Establish `e : (⟨n₁' - n₁, hdW⟩ : ↥(H.W0 t₁.f t₁.f')) = ⟨n₁', hn₁'W⟩ - n₁` using `rfl`. Rewrite using `[e, map_sub, Submodule.coe_sub, hψ', hψn₁]`. Establish `hcd : Corr H t₁ { abelian₂` using `⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } φ φ' (n₁' - n₁) (n₂' - q) := (hψ _ _).mpr ⟨hdW, hψd⟩`. Establish `hB : n₂' - q ∈ B` using `(hThB _ _ hcd).mp hd`.

Establish `h2'' : p + n₂' ∈ B` using `h2'`. Establish `h0` using `B.sub_mem h2'' hB`. Establish `e : p + n₂' - (n₂' - q) = x` using `by rw [← hxpq]; abel`. Rewrite `h0` using `[e]`. Then use the resulting hypothesis. Conclude with `le_antisymm (key Λ₂ Λ₂' hG hTh hTh' (fun m₁ m₂ => (hrel m₁ m₂).mp)) (key Λ₂' Λ₂ hG' hTh' hTh (fun m₁ m₂ => (hrel m₁ m₂).mpr))`.
-/
theorem glueInj_of (M : Model F E) (r n : ℕ) (hM : M.OK) (hC : CorrIso M r n) : GlueInj M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hT Λ₂ Λ₂' hG hTh hG' hTh' hrel
  obtain ⟨ψ, hψh, hψ⟩ := hC V H hn t₁ f₂ f₂' φ φ' hT hG.1.2.2.2.1
  have hW₁ := hermSp_W0_eq_perp_span_range_MMfam H t₁.f t₁.f'
  have hW₂ := hermSp_W0_eq_perp_span_range_MMfam H f₂ f₂'
  have hU₁ := isCompl_span_perp_of_isGeneric H t₁ hT.1
  have key : ∀ A B : Submodule (↥M.L.O) V,
      H.IsGeneric { abelian₂ := A, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } →
      ThCond H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } A φ φ' →
      ThCond H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } B φ φ' →
      (∀ (m₁ : ↥(MMsharp H t₁))
          (m₂ : ↥(MMsharp H { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' })),
          GlueRel H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } A φ φ' m₁ m₂ →
          GlueRel H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } B φ φ' m₁ m₂) →
      A ≤ B := by
    intro A B hGA hThA hThB hAB x hx
    let U₂ : Submodule E V := Submodule.span E (Set.range (Sum.elim f₂ f₂'))
    let U₁ : Submodule E V := Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))
    have hU₂ : IsCompl U₂ (H.perp U₂) := isCompl_span_perp_of_isGeneric H _ hGA
    have gA := local_hermitian_glue F E M hM V H A hGA.1.1 U₂ hU₂
    have g₁ := local_hermitian_glue F E M hM V H t₁.abelian₂ hT.1.1.1 U₁ hU₁
    obtain ⟨p, hp, hpint, q, hq, hqint, hxpq⟩ : ∃ p ∈ U₂, (∀ y ∈ A, y ∈ U₂ → H.h p y ∈ M.L.O) ∧
        ∃ q ∈ H.perp U₂, (∀ y ∈ A, y ∈ H.perp U₂ → H.h q y ∈ M.L.O) ∧ p + q = x :=
      ⟨_, Submodule.coe_mem _, (gA.1 _ (Submodule.coe_mem _)).mp ⟨x, hx, rfl⟩,
       _, Submodule.coe_mem _, (gA.2 _ (Submodule.coe_mem _)).mp ⟨x, hx, rfl⟩,
       Submodule.projection_add_projection_eq_self hU₂ x⟩
    have hpS : p ∈ MMsharp H { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } :=
      mem_MMsharp_of_integral_pairing H _ A hGA.2.1 p hp hpint
    have hqW : q ∈ H.W0 f₂ f₂' := hW₂.ge hq
    obtain ⟨n₁, hψn₁⟩ : ∃ n₁ : ↥(H.W0 t₁.f t₁.f'), (ψ n₁ : V) = q := ⟨ψ.symm ⟨q, hqW⟩, by simp⟩
    have hcorr₁ : Corr H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } φ φ' (n₁ : V) q :=
      (hψ _ _).mpr ⟨n₁.2, hψn₁⟩
    have hn₁int : ∀ y ∈ t₁.abelian₂, y ∈ H.perp U₁ → H.h (n₁ : V) y ∈ M.L.O := by
      intro y hy hyp
      have hyW : y ∈ H.W0 t₁.f t₁.f' := hW₁.ge hyp
      have hc : Corr H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } φ φ' y
          (ψ ⟨y, hyW⟩ : V) := (hψ _ _).mpr ⟨hyW, rfl⟩
      have hyA : (ψ ⟨y, hyW⟩ : V) ∈ A := (hThA _ _ hc).mp hy
      have hyp2 : (ψ ⟨y, hyW⟩ : V) ∈ H.perp U₂ := hW₂.le (ψ ⟨y, hyW⟩).2
      have e : H.h (n₁ : V) y = H.h q (ψ ⟨y, hyW⟩ : V) := by
        rw [← hψn₁]
        exact (hψh n₁ ⟨y, hyW⟩).symm
      rw [e]
      exact hqint _ hyA hyp2
    have hn₁p : (n₁ : V) ∈ H.perp U₁ := hW₁.le n₁.2
    obtain ⟨z, hz, hzn⟩ := (g₁.2 _ hn₁p).mpr hn₁int
    have hmS : (U₁.linearProjOfIsCompl (H.perp U₁) hU₁ z : V) ∈ MMsharp H t₁ :=
      mem_MMsharp_of_integral_pairing H t₁ t₁.abelian₂ hT.1.2.1 _ (Submodule.coe_mem _)
        ((g₁.1 _ (Submodule.coe_mem _)).mp ⟨z, hz, rfl⟩)
    have hzsum : (U₁.linearProjOfIsCompl (H.perp U₁) hU₁ z : V) + (n₁ : V) = z := by
      rw [← hzn]
      exact Submodule.projection_add_projection_eq_self hU₁ z
    have hz' : (U₁.linearProjOfIsCompl (H.perp U₁) hU₁ z : V) + (n₁ : V) ∈ t₁.abelian₂ := by
      rw [hzsum]; exact hz
    have hglA : GlueRel H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } A φ φ'
        ⟨_, hmS⟩ ⟨p, hpS⟩ :=
      ⟨n₁, q, hcorr₁, hz', by show p + q ∈ A; rw [hxpq]; exact hx⟩
    obtain ⟨n₁', n₂', hc', h1', h2'⟩ := hAB _ _ hglA
    obtain ⟨hn₁'W, hψ'⟩ := (hψ _ _).mp hc'
    have h1'' : (U₁.linearProjOfIsCompl (H.perp U₁) hU₁ z : V) + n₁' ∈ t₁.abelian₂ := h1'
    have hd : n₁' - (n₁ : V) ∈ t₁.abelian₂ := by
      have h0 := t₁.abelian₂.sub_mem h1'' hz'
      rwa [add_sub_add_left_eq_sub] at h0
    have hdW : n₁' - (n₁ : V) ∈ H.W0 t₁.f t₁.f' := Submodule.sub_mem _ hn₁'W n₁.2
    have hψd : (ψ ⟨n₁' - n₁, hdW⟩ : V) = n₂' - q := by
      have e : (⟨n₁' - n₁, hdW⟩ : ↥(H.W0 t₁.f t₁.f')) = ⟨n₁', hn₁'W⟩ - n₁ := rfl
      rw [e, map_sub, Submodule.coe_sub, hψ', hψn₁]
    have hcd : Corr H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } φ φ'
        (n₁' - n₁) (n₂' - q) := (hψ _ _).mpr ⟨hdW, hψd⟩
    have hB : n₂' - q ∈ B := (hThB _ _ hcd).mp hd
    have h2'' : p + n₂' ∈ B := h2'
    have h0 := B.sub_mem h2'' hB
    have e : p + n₂' - (n₂' - q) = x := by rw [← hxpq]; abel
    rwa [e] at h0
  exact le_antisymm (key Λ₂ Λ₂' hG hTh hTh' (fun m₁ m₂ => (hrel m₁ m₂).mp))
    (key Λ₂' Λ₂ hG' hTh' hTh (fun m₁ m₂ => (hrel m₁ m₂).mpr))

end Inj

end Formalism.L2.SG.LsDatumA
