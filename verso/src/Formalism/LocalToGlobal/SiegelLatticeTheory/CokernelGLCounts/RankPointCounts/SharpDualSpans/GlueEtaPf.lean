import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGlueCut
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocGlue

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace PI.LocCntLat.GE

section Basic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

/- English proof (translation)
Rewrite using `[H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]`.
-/
theorem h_add_right' (H : HermSp M V) (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]

/- English proof (translation)
Rewrite using `[H.h_add_left, h_add_right', h_add_right']`. Normalize the expressions using the abelian group laws.
-/
theorem h_expand (H : HermSp M V) (x a y b : V) :
    H.h (x + a) (y + b) = H.h x y + H.h x b + H.h a y + H.h a b := by
  rw [H.h_add_left, h_add_right', h_add_right']
  abel

/- English proof (translation)
Unfold `HermSp.MMfam`. Break down `hs : M.split with _ | g` into its components or cases. Both sides reduce to the same expression. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i | i, rfl⟩`. Conclude with `Submodule.subset_span ⟨Sum.inl i, rfl⟩`. Conclude with `Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩) (Submodule.subset_span ⟨Sum.inl i, rfl⟩))`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i | i, rfl⟩`.

Conclude with `Submodule.subset_span ⟨Sum.inl i, rfl⟩`. Establish `hq : (g.q : F) ≠ 0` using `fun h => g.q_irr.ne_zero (Subtype.ext h)`. Establish `e : t.f' i = algebraMap F E (g.q : F) • (algebraMap F E ((g.q : F)⁻¹) • (t.f' i - t.f i)) + t.f i`. Rewrite using `[smul_smul, ← map_mul, mul_inv_cancel₀ hq, map_one, one_smul, sub_add_cancel]`. Use `show t.f' i ∈ _`.

Rewrite using `[e]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩)) (Submodule.subset_span ⟨Sum.inl i, rfl⟩)`.
-/
theorem span_MMfam (H : HermSp M V) {r : ℕ} (t : Term V M r) :
    Submodule.span E (Set.range (H.MMfam t)) = Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
  unfold HermSp.MMfam
  rcases hs : M.split with _ | g
  · rfl
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i | i, rfl⟩
      · exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
      · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩)
          (Submodule.subset_span ⟨Sum.inl i, rfl⟩))
    · rw [Submodule.span_le]
      rintro _ ⟨i | i, rfl⟩
      · exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
      · have hq : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
        have e : t.f' i = algebraMap F E (g.q : F) • (algebraMap F E ((g.q : F)⁻¹) • (t.f' i - t.f i)) + t.f i := by
          rw [smul_smul, ← map_mul, mul_inv_cancel₀ hq, map_one, one_smul, sub_add_cancel]
        show t.f' i ∈ _
        rw [e]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩))
          (Submodule.subset_span ⟨Sum.inl i, rfl⟩)

/- English proof (translation)
Unfold `HermSp.W0`. Use `congr 1`. Rewrite using `[span_MMfam H t, Set.Sum.elim_range, Submodule.span_union]`. Both sides reduce to the same expression.
-/
theorem hermSp_W0_eq_perp_span_range_MMfam (H : HermSp M V) {r : ℕ} (t : Term V M r) :
    H.W0 t.f t.f' = H.perp (Submodule.span E (Set.range (H.MMfam t))) := by
  unfold HermSp.W0
  congr 1
  rw [span_MMfam H t, Set.Sum.elim_range, Submodule.span_union]
  rfl

/- English proof (translation)
Establish `hT` using `hg.1`. Establish `hF : Formalism.MainNotions.ThinScalesBound.FrameK H t.f t.T` using `⟨hT.2.1.2.1, hT.2.1.2.2.1⟩`. Establish `hF' : Formalism.MainNotions.ThinScalesBound.FrameK H t.f' t.T'` using `⟨hT.2.2.1.2.1, hT.2.2.1.2.2.1⟩`. Establish `h` using `isCompl_span_frames_W0 (H := H) t.f t.f' t.T t.T' hF hF' hT.2.2.2.1 (isUnit_Gdet (H := H) t.f t.f' t.T t.T' hT.2.2.2.2.1)`. Rewrite using `[← hermSp_W0_eq_perp_span_range_MMfam H t, span_MMfam H t]`.

Conclude with `h`.
-/
theorem isCompl_MM (H : HermSp M V) {r : ℕ} (t : Term V M r) (hg : H.IsGeneric t) :
    IsCompl (Submodule.span E (Set.range (H.MMfam t))) (H.perp (Submodule.span E (Set.range (H.MMfam t)))) := by
  have hT := hg.1
  have hF : Formalism.MainNotions.ThinScalesBound.FrameK H t.f t.T := ⟨hT.2.1.2.1, hT.2.1.2.2.1⟩
  have hF' : Formalism.MainNotions.ThinScalesBound.FrameK H t.f' t.T' := ⟨hT.2.2.1.2.1, hT.2.2.1.2.2.1⟩
  have h := isCompl_span_frames_W0 (H := H) t.f t.f' t.T t.T' hF hF' hT.2.2.2.1
    (isUnit_Gdet (H := H) t.f t.f' t.T t.T' hT.2.2.2.2.1)
  rw [← hermSp_W0_eq_perp_span_range_MMfam H t, span_MMfam H t]
  exact h

/- English proof (translation)
The claim follows from `Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hg.2.1 a)`.
-/
theorem MMo_le (H : HermSp M V) {r : ℕ} (t : Term V M r) (hg : H.IsGeneric t) : MMo H t ≤ t.abelian₂ := Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hg.2.1 a)

/- English proof (translation)
Conclude with `(Submodule.span_le (p := (Submodule.span E (Set.range (H.MMfam t))).restrictScalars M.L.O)).2 Submodule.subset_span hm`.
-/
theorem mem_spanE_of_mem_MMo (H : HermSp M V) {r : ℕ} (t : Term V M r) {m : V} (hm : m ∈ MMo H t) :
    m ∈ Submodule.span E (Set.range (H.MMfam t)) := by
  exact (Submodule.span_le (p := (Submodule.span E (Set.range (H.MMfam t))).restrictScalars M.L.O)).2
    Submodule.subset_span hm

/- English proof (translation)
Establish `hn' : n ∈ H.perp (Submodule.span E (Set.range (H.MMfam t)))`. Rewrite using `[← hermSp_W0_eq_perp_span_range_MMfam H t]`. Conclude with `hn`. Rewrite using `[H.h_herm n m, hn' m hm, map_zero]`.
-/
theorem hermitian_span_orthogonal_W0 (H : HermSp M V) {r : ℕ} (t : Term V M r) {m n : V}
    (hm : m ∈ Submodule.span E (Set.range (H.MMfam t))) (hn : n ∈ H.W0 t.f t.f') : H.h m n = 0 := by
  have hn' : n ∈ H.perp (Submodule.span E (Set.range (H.MMfam t))) := by
    rw [← hermSp_W0_eq_perp_span_range_MMfam H t]
    exact hn
  rw [H.h_herm n m, hn' m hm, map_zero]

/- English proof (translation)
Establish `hn' : n ∈ H.perp (Submodule.span E (Set.range (H.MMfam t)))`. Rewrite using `[← hermSp_W0_eq_perp_span_range_MMfam H t]`. Conclude with `hn`. Conclude with `hn' m hm`.
-/
theorem hermitian_W0_orthogonal_span (H : HermSp M V) {r : ℕ} (t : Term V M r) {m n : V}
    (hm : m ∈ Submodule.span E (Set.range (H.MMfam t))) (hn : n ∈ H.W0 t.f t.f') : H.h n m = 0 := by
  have hn' : n ∈ H.perp (Submodule.span E (Set.range (H.MMfam t))) := by
    rw [← hermSp_W0_eq_perp_span_range_MMfam H t]
    exact hn
  exact hn' m hm

/- English proof (translation)
Unfold `ddMk`. Rewrite using `[Submodule.Quotient.eq, Submodule.mem_comap, map_sub]`. Both sides reduce to the same expression.
-/
theorem ddMk_eq_iff (H : HermSp M V) {r : ℕ} (t : Term V M r) (a b : ↥(MMsharp H t)) :
    ddMk H t a = ddMk H t b ↔ (a : V) - b ∈ MMo H t := by
  unfold ddMk
  rw [Submodule.Quotient.eq, Submodule.mem_comap, map_sub]
  rfl

/- English proof (translation)
Unfold `dwMk`. Rewrite using `[Submodule.Quotient.eq, Submodule.mem_comap, map_sub]`. Both sides reduce to the same expression.
-/
theorem dwMk_eq_iff (H : HermSp M V) {r : ℕ} (t : Term V M r) (N : Submodule M.L.O V)
    (a b : ↥(ThSharp H t N)) : dwMk H t N a = dwMk H t N b ↔ (a : V) - b ∈ N := by
  unfold dwMk
  rw [Submodule.Quotient.eq, Submodule.mem_comap, map_sub]
  rfl

end Basic

section Halves

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

/- English proof (translation)
Establish `hU` using `isCompl_MM H t hg`. Take `⟨h1, -⟩` from `local_hermitian_glue F E M hOK V H t.abelian₂ hg.1.1 _ hU`. Take `⟨x, hx, hxu⟩` from `(h1 u hu.1).2 (fun y hy hyU => hu.2 y (hg.2.2.2 y hy hyU))`. Use `⟨x - u, ?_, by convert hx using 1; abel⟩` and prove the remaining obligations. Rewrite using `[hermSp_W0_eq_perp_span_range_MMfam H t, ← hxu]`.

Conclude with `PI.LocHerm.Glue.sub_proj_mem hU x`.
-/
theorem prM (hOK : M.OK) (H : HermSp M V) {r : ℕ} (t : Term V M r) (hg : H.IsGeneric t)
    (u : V) (hu : u ∈ MMsharp H t) : ∃ n ∈ H.W0 t.f t.f', u + n ∈ t.abelian₂ := by
  have hU := isCompl_MM H t hg
  obtain ⟨h1, -⟩ := local_hermitian_glue F E M hOK V H t.abelian₂ hg.1.1 _ hU
  obtain ⟨x, hx, hxu⟩ := (h1 u hu.1).2 (fun y hy hyU => hu.2 y (hg.2.2.2 y hy hyU))
  refine ⟨x - u, ?_, by convert hx using 1; abel⟩
  rw [hermSp_W0_eq_perp_span_range_MMfam H t, ← hxu]
  exact PI.LocHerm.Glue.sub_proj_mem hU x

/- English proof (translation)
Establish `hU` using `isCompl_MM H t hg`. Take `⟨-, h2⟩` from `local_hermitian_glue F E M hOK V H t.abelian₂ hg.1.1 _ hU`. Establish `hwp : w ∈ H.perp (Submodule.span E (Set.range (H.MMfam t)))`. Rewrite using `[← hermSp_W0_eq_perp_span_range_MMfam H t]`. Conclude with `hw.1`.

Take `⟨x, hx, hxw⟩` from `(h2 w hwp).2 (fun y hy hyp => hw.2 y ⟨hy, by show y ∈ H.W0 t.f t.f'`. Rewrite using `[hermSp_W0_eq_perp_span_range_MMfam H t]`. Conclude with `hyp⟩)`. Establish `hmU : x - w ∈ Submodule.span E (Set.range (H.MMfam t))`. Rewrite using `[← hxw]`.

Conclude with `PI.LocHerm.Glue.sub_proj_mem hU.symm x`. Use `⟨x - w, ⟨hmU, fun m' hm' => ?_⟩, by convert hx using 1; abel⟩` and prove the remaining obligations. Establish `e` using `H.h_add_left (x - w) w m'`. Rewrite `e` using `[sub_add_cancel, hermitian_W0_orthogonal_span H t (mem_spanE_of_mem_MMo H t hm') hw.1, add_zero]`. Rewrite using `[← e]`.

Conclude with `(hg.1.1.2.2 x).1 hx m' (MMo_le H t hg hm')`.
-/
theorem prN (hOK : M.OK) (H : HermSp M V) {r : ℕ} (t : Term V M r) (hg : H.IsGeneric t)
    (w : V) (hw : w ∈ ThSharp H t (ThL H t)) :
    ∃ m ∈ MMsharp H t, m + w ∈ t.abelian₂ := by
  have hU := isCompl_MM H t hg
  obtain ⟨-, h2⟩ := local_hermitian_glue F E M hOK V H t.abelian₂ hg.1.1 _ hU
  have hwp : w ∈ H.perp (Submodule.span E (Set.range (H.MMfam t))) := by
    rw [← hermSp_W0_eq_perp_span_range_MMfam H t]
    exact hw.1
  obtain ⟨x, hx, hxw⟩ := (h2 w hwp).2 (fun y hy hyp => hw.2 y ⟨hy, by
    show y ∈ H.W0 t.f t.f'
    rw [hermSp_W0_eq_perp_span_range_MMfam H t]
    exact hyp⟩)
  have hmU : x - w ∈ Submodule.span E (Set.range (H.MMfam t)) := by
    rw [← hxw]
    exact PI.LocHerm.Glue.sub_proj_mem hU.symm x
  refine ⟨x - w, ⟨hmU, fun m' hm' => ?_⟩, by convert hx using 1; abel⟩
  have e := H.h_add_left (x - w) w m'
  rw [sub_add_cancel, hermitian_W0_orthogonal_span H t (mem_spanE_of_mem_MMo H t hm') hw.1, add_zero] at e
  rw [← e]
  exact (hg.1.1.2.2 x).1 hx m' (MMo_le H t hg hm')

end Halves

section Eta

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

/- English proof (translation)
Introduce `hOK V _ _ H t hg`. Establish `hSD` using `hg.1.1`. Establish `hLam : ∀ x y : V, x ∈ t.abelian₂ → y ∈ t.abelian₂ → H.h x y ∈ M.L.O` using `fun x y hx hy => (hSD.2.2 x).1 hx y hy`. Establish `liftM : ∀ m : ↥(MMsharp H t), ∃ w : ↥(ThSharp H t (ThL H t)), (m : V) + w ∈ t.abelian₂`. Introduce `m`.

Take `⟨n, hn, hmn⟩` from `prM hOK H t hg m m.2`. Use `⟨⟨n, hn, fun n' hn' => ?_⟩, hmn⟩` and prove the remaining obligations. Establish `e` using `H.h_add_left (m : V) n n'`. Rewrite `e` using `[hermitian_span_orthogonal_W0 H t m.2.1 hn'.2, zero_add]`. Rewrite using `[← e]`.

Conclude with `hLam _ _ hmn hn'.1`. Establish `liftW : ∀ w : ↥(ThSharp H t (ThL H t)), ∃ m : ↥(MMsharp H t), (m : V) + w ∈ t.abelian₂`. Introduce `w`. Take `⟨m, hm, hmw⟩` from `prN hOK H t hg w w.2`. Conclude with `⟨⟨m, hm⟩, hmw⟩`.

Set `G : Submodule M.L.O (↥(MMsharp H t) × ↥(ThSharp H t (ThL H t)))` to `{ carrier := {p | (p.1 : V) + (p.2 : V) ∈ t.abelian₂} add_mem' := fun {a b} ha hb => by show ((a.1 + b.1 : ↥(MMsharp H t)) : V) + ((a.2 + b.2 : ↥(ThSharp H t (ThL H t))) : V) ∈ t.abelian₂`. Rewrite using `[Submodule.coe_add, Submodule.coe_add, add_add_add_comm]`. Conclude with `t.abelian₂.add_mem ha hb`. Use the proof step `zero_mem' := by show ((0 : ↥(MMsharp H t)) : V) + ((0 : ↥(ThSharp H t (ThL H t))) : V) ∈ t.abelian₂`. Rewrite using `[Submodule.coe_zero, Submodule.coe_zero, add_zero]`.

Conclude with `t.abelian₂.zero_mem`. Use the proof step `smul_mem' := fun c p hp => by show ((c • p.1 : ↥(MMsharp H t)) : V) + ((c • p.2 : ↥(ThSharp H t (ThL H t))) : V) ∈ t.abelian₂`. Rewrite using `[Submodule.coe_smul, Submodule.coe_smul, ← smul_add]`. Conclude with `t.abelian₂.smul_mem c hp }`. Set `α : G →ₗ[M.L.O] DDt H t` to `(Submodule.mkQ _).comp ((LinearMap.fst M.L.O _ _).comp G.subtype)`.

Set `β : G →ₗ[M.L.O] DDW H t (ThL H t)` to `(Submodule.mkQ _).comp ((LinearMap.snd M.L.O _ _).comp G.subtype)`. Establish `hα : Function.Surjective α`. Introduce `q`. Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Take `⟨w, hw⟩` from `liftM m`.

Conclude with `⟨⟨(m, w), hw⟩, rfl⟩`. Establish `hβ : Function.Surjective β`. Introduce `q`. Take `⟨w, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Take `⟨m, hm⟩` from `liftW w`.

Conclude with `⟨⟨(m, w), hm⟩, rfl⟩`. Establish `hker : LinearMap.ker α = LinearMap.ker β`. Use extensionality with `p`. Rewrite using `[LinearMap.mem_ker, LinearMap.mem_ker]`. Express the relevant statement in the definitionally equal form `(Submodule.Quotient.mk p.val.1 : DDt H t) = 0 ↔ (Submodule.Quotient.mk p.val.2 : DDW H t (ThL H t)) = 0`.

Rewrite using `[Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply, Submodule.subtype_apply]`. Establish `hp : (p.val.1 : V) + (p.val.2 : V) ∈ t.abelian₂` using `p.2`. Prove the components needed by the constructor for the conclusion. Introduce `hm`. Use `⟨?_, p.val.2.2.1⟩` and prove the remaining obligations.

Use `t.abelian₂.sub_mem hp (MMo_le H t hg hm)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel_left]`. Then use the resulting hypothesis. Introduce `hw`. Establish `h1 : (p.val.1 : V) ∈ t.abelian₂`. Use `t.abelian₂.sub_mem hp hw.1` as an intermediate fact.

Rewrite `this` using `[add_sub_cancel_right]`. Then use the resulting hypothesis. Conclude with `hg.2.2.2 _ h1 p.val.1.2.1`. Set `η : DDt H t ≃ₗ[M.L.O] DDW H t (ThL H t)` to `(α.quotKerEquivOfSurjective hα).symm.trans ((Submodule.quotEquivOfEq _ _ hker).trans (β.quotKerEquivOfSurjective hβ))`. Establish `hη : ∀ g : G, η (α g) = β g`. Introduce `g`.

Use `show (β.quotKerEquivOfSurjective hβ) (Submodule.quotEquivOfEq _ _ hker ((α.quotKerEquivOfSurjective hα).symm (α g))) = β g`. Establish `e1 : (α.quotKerEquivOfSurjective hα).symm (α g) = Submodule.Quotient.mk g`. Rewrite using `[LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]`. Rewrite using `[e1, Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]`. Establish `key : ∀ (m : ↥(MMsharp H t)) (w : ↥(ThSharp H t (ThL H t))), η (ddMk H t m) = dwMk H t _ w ↔ (m : V) + w ∈ t.abelian₂`.

Introduce `m w`. Take `⟨w0, hw0⟩` from `liftM m`. Establish `e : η (ddMk H t m) = dwMk H t _ w0` using `hη ⟨(m, w0), hw0⟩`. Rewrite using `[e, dwMk_eq_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hl, -⟩`. Establish `e2 : (m : V) + w = ((m : V) + w0) - ((w0 : V) - w)` using `by abel`. Rewrite using `[e2]`. Conclude with `t.abelian₂.sub_mem hw0 hl`. Introduce `hmw`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `e2 : (w0 : V) - w = ((m : V) + w0) - ((m : V) + w)` using `by abel`. Rewrite using `[e2]`. Conclude with `t.abelian₂.sub_mem hw0 hmw`. Conclude with `(H.W0 t.f t.f').sub_mem w0.2.1 w.2.1`.

Use `⟨η, key, fun m m' w w' h1 h2 => ?_⟩` and prove the remaining obligations. Use `hLam _ _ ((key m w).1 h1) ((key m' w').1 h2)` as an intermediate fact. Rewrite `this` using `[h_expand, hermitian_span_orthogonal_W0 H t m.2.1 w'.2.1, hermitian_W0_orthogonal_span H t m'.2.1 w.2.1, add_zero, add_zero]`. Conclude with `this`.
-/
theorem glueEta_holds (M : Model F E) (r : ℕ) : GlueEta M r := by
  intro hOK V _ _ H t hg
  have hSD := hg.1.1
  have hLam : ∀ x y : V, x ∈ t.abelian₂ → y ∈ t.abelian₂ → H.h x y ∈ M.L.O := fun x y hx hy => (hSD.2.2 x).1 hx y hy
  have liftM : ∀ m : ↥(MMsharp H t), ∃ w : ↥(ThSharp H t (ThL H t)), (m : V) + w ∈ t.abelian₂ := by
    intro m
    obtain ⟨n, hn, hmn⟩ := prM hOK H t hg m m.2
    refine ⟨⟨n, hn, fun n' hn' => ?_⟩, hmn⟩
    have e := H.h_add_left (m : V) n n'
    rw [hermitian_span_orthogonal_W0 H t m.2.1 hn'.2, zero_add] at e
    rw [← e]
    exact hLam _ _ hmn hn'.1
  have liftW : ∀ w : ↥(ThSharp H t (ThL H t)), ∃ m : ↥(MMsharp H t), (m : V) + w ∈ t.abelian₂ := by
    intro w
    obtain ⟨m, hm, hmw⟩ := prN hOK H t hg w w.2
    exact ⟨⟨m, hm⟩, hmw⟩
  let G : Submodule M.L.O (↥(MMsharp H t) × ↥(ThSharp H t (ThL H t))) :=
    { carrier := {p | (p.1 : V) + (p.2 : V) ∈ t.abelian₂}
      add_mem' := fun {a b} ha hb => by
        show ((a.1 + b.1 : ↥(MMsharp H t)) : V) + ((a.2 + b.2 : ↥(ThSharp H t (ThL H t))) : V) ∈ t.abelian₂
        rw [Submodule.coe_add, Submodule.coe_add, add_add_add_comm]
        exact t.abelian₂.add_mem ha hb
      zero_mem' := by
        show ((0 : ↥(MMsharp H t)) : V) + ((0 : ↥(ThSharp H t (ThL H t))) : V) ∈ t.abelian₂
        rw [Submodule.coe_zero, Submodule.coe_zero, add_zero]
        exact t.abelian₂.zero_mem
      smul_mem' := fun c p hp => by
        show ((c • p.1 : ↥(MMsharp H t)) : V) + ((c • p.2 : ↥(ThSharp H t (ThL H t))) : V) ∈ t.abelian₂
        rw [Submodule.coe_smul, Submodule.coe_smul, ← smul_add]
        exact t.abelian₂.smul_mem c hp }
  let α : G →ₗ[M.L.O] DDt H t :=
    (Submodule.mkQ _).comp ((LinearMap.fst M.L.O _ _).comp G.subtype)
  let β : G →ₗ[M.L.O] DDW H t (ThL H t) :=
    (Submodule.mkQ _).comp ((LinearMap.snd M.L.O _ _).comp G.subtype)
  have hα : Function.Surjective α := by
    intro q
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨w, hw⟩ := liftM m
    exact ⟨⟨(m, w), hw⟩, rfl⟩
  have hβ : Function.Surjective β := by
    intro q
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨m, hm⟩ := liftW w
    exact ⟨⟨(m, w), hm⟩, rfl⟩
  have hker : LinearMap.ker α = LinearMap.ker β := by
    ext p
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    change (Submodule.Quotient.mk p.val.1 : DDt H t) = 0 ↔
      (Submodule.Quotient.mk p.val.2 : DDW H t (ThL H t)) = 0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.subtype_apply]
    have hp : (p.val.1 : V) + (p.val.2 : V) ∈ t.abelian₂ := p.2
    constructor
    · intro hm
      refine ⟨?_, p.val.2.2.1⟩
      have := t.abelian₂.sub_mem hp (MMo_le H t hg hm)
      rwa [add_sub_cancel_left] at this
    · intro hw
      have h1 : (p.val.1 : V) ∈ t.abelian₂ := by
        have := t.abelian₂.sub_mem hp hw.1
        rwa [add_sub_cancel_right] at this
      exact hg.2.2.2 _ h1 p.val.1.2.1
  let η : DDt H t ≃ₗ[M.L.O] DDW H t (ThL H t) :=
    (α.quotKerEquivOfSurjective hα).symm.trans
      ((Submodule.quotEquivOfEq _ _ hker).trans (β.quotKerEquivOfSurjective hβ))
  have hη : ∀ g : G, η (α g) = β g := by
    intro g
    show (β.quotKerEquivOfSurjective hβ) (Submodule.quotEquivOfEq _ _ hker
      ((α.quotKerEquivOfSurjective hα).symm (α g))) = β g
    have e1 : (α.quotKerEquivOfSurjective hα).symm (α g) = Submodule.Quotient.mk g := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    rw [e1, Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  have key : ∀ (m : ↥(MMsharp H t)) (w : ↥(ThSharp H t (ThL H t))),
      η (ddMk H t m) = dwMk H t _ w ↔ (m : V) + w ∈ t.abelian₂ := by
    intro m w
    obtain ⟨w0, hw0⟩ := liftM m
    have e : η (ddMk H t m) = dwMk H t _ w0 := hη ⟨(m, w0), hw0⟩
    rw [e, dwMk_eq_iff]
    constructor
    · rintro ⟨hl, -⟩
      have e2 : (m : V) + w = ((m : V) + w0) - ((w0 : V) - w) := by abel
      rw [e2]
      exact t.abelian₂.sub_mem hw0 hl
    · intro hmw
      refine ⟨?_, ?_⟩
      · have e2 : (w0 : V) - w = ((m : V) + w0) - ((m : V) + w) := by abel
        rw [e2]
        exact t.abelian₂.sub_mem hw0 hmw
      · exact (H.W0 t.f t.f').sub_mem w0.2.1 w.2.1
  refine ⟨η, key, fun m m' w w' h1 h2 => ?_⟩
  have := hLam _ _ ((key m w).1 h1) ((key m' w').1 h2)
  rw [h_expand, hermitian_span_orthogonal_W0 H t m.2.1 w'.2.1, hermitian_W0_orthogonal_span H t m'.2.1 w.2.1, add_zero, add_zero] at this
  exact this

end Eta

end PI.LocCntLat.GE
