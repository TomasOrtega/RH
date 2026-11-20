import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlueFwdOf
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Back

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def GramMM (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    IsUnit (H.Dl f₂ f₂' (r + 1)) → IsUnit (H.gram (H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r))).det

def ThFG (M : Model F E) (r : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t : Term V M r), H.IsGeneric t → (ThL H t).FG

def ThSpan (M : Model F E) (r : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t : Term V M r), H.IsGeneric t →
    Submodule.span E (ThL H t : Set V) = H.W0 t.f t.f'

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `V _ _ H hn t₁ f₂ f₂' φ φ' hT hDl hMM θ hθ`. Set `t₀ : Term V M r` to `{ abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' }`. Establish `memS : ∀ (t : Term V M r) (N : Submodule M.L.O V) (w : V), w ∈ ThSharp H t N ↔ (w ∈ H.W0 t.f t.f' ∧ ∀ n ∈ N, H.h w n ∈ M.L.O)` using `fun _ _ _ => Iff.rfl`. Establish `memL : ∀ (t : Term V M r) (w : V), w ∈ ThL H t ↔ (w ∈ t.abelian₂ ∧ w ∈ H.W0 t.f t.f')` using `fun _ _ => Iff.rfl`. Establish `hG₁ : H.IsGeneric t₁`.

Take `⟨h, -⟩` from `id hT`. Conclude with `h`. Establish `hsd : ∀ x : V, x ∈ t₁.abelian₂ ↔ ∀ y ∈ t₁.abelian₂, H.h x y ∈ M.L.O`. Take `⟨⟨⟨-, -, h⟩, -⟩, -⟩` from `id hG₁`. Conclude with `h`.

Take `⟨ψ, hψh, hψC⟩` from `hC V H hn t₁ f₂ f₂' φ φ' hT hDl`. Take `⟨η₁, hη₁a, hη₁b⟩` from `hE hM V H t₁ hG₁`. Set `g : ThL H t₁ →ₗ[M.L.O] V` to `{ toFun := fun x => (ψ ⟨x, ((memL _ _).1 x.2).2⟩ : V) map_add' := fun a b => by`. Establish `h` using `congrArg Subtype.val (map_add ψ ⟨(a : V), ((memL _ _).1 a.2).2⟩ ⟨(b : V), ((memL _ _).1 b.2).2⟩)`. Conclude with `h`.

Use the proof step `map_smul' := fun c a => by`. Establish `h` using `congrArg Subtype.val (map_smul ψ (c : E) ⟨(a : V), ((memL _ _).1 a.2).2⟩)`. Conclude with `h }`. Establish `hg : ∀ y : ThL H t₁, g y = (ψ ⟨y, ((memL _ _).1 y.2).2⟩ : V)` using `fun _ => rfl`. Take `⟨N₂, hN₂⟩ : ∃ N : Submodule M.L.O V, N = Submodule.map g ⊤` from `⟨_, rfl⟩`.

Establish `memN : ∀ v : V, v ∈ N₂ ↔ ∃ y, g y = v`. Introduce `v`. Rewrite using `[hN₂]`. Simplify using `only [Submodule.mem_map, Submodule.mem_top, true_and]`. Establish `keyN : ∀ (x : V) (hx : x ∈ H.W0 t₁.f t₁.f'), x ∈ t₁.abelian₂ ↔ (ψ ⟨x, hx⟩ : V) ∈ N₂`.

Introduce `x hx`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `(memN _).2 ⟨⟨x, (memL _ _).2 ⟨h, hx⟩⟩, rfl⟩`. Introduce `h`.

Take `⟨y, hy⟩` from `(memN _).1 h`. Rewrite `hy` using `[hg]`. Establish `h2 : (y : V) = x` using `congrArg Subtype.val (ψ.injective (Subtype.ext hy))`. Rewrite using `[← h2]`. Conclude with `((memL _ _).1 y.2).1`.

Establish `fwd : ∀ (w : V) (hw : w ∈ ThSharp H t₁ (ThL H t₁)), (ψ ⟨w, ((memS _ _ _).1 hw).1⟩ : V) ∈ ThSharp H t₀ N₂`. Introduce `w hw`. Use `(memS _ _ _).2 ⟨(ψ _).2, ?_⟩` and prove the remaining obligations. Introduce `n hn'`. Take `⟨y, rfl⟩` from `(memN _).1 hn'`.

Rewrite using `[hg, hψh]`. Conclude with `((memS _ _ _).1 hw).2 _ y.2`. Establish `bwd : ∀ (w : V) (hw : w ∈ ThSharp H t₀ N₂), (ψ.symm ⟨w, ((memS _ _ _).1 hw).1⟩ : V) ∈ ThSharp H t₁ (ThL H t₁)`. Introduce `w hw`. Use `(memS _ _ _).2 ⟨(ψ.symm _).2, ?_⟩` and prove the remaining obligations.

Introduce `n hn'`. Take `⟨hnΛ, hnW⟩` from `(memL _ _).1 hn'`. Establish `h2` using `hψh (ψ.symm ⟨w, ((memS _ _ _).1 hw).1⟩) ⟨n, hnW⟩`. Simplify using `only [LinearEquiv.apply_symm_apply] at h2`. Rewrite using `[← h2]`.

Conclude with `((memS _ _ _).1 hw).2 _ ((memN _).2 ⟨⟨n, hn'⟩, rfl⟩)`. Set `e : ThSharp H t₁ (ThL H t₁) ≃ₗ[M.L.O] ThSharp H t₀ N₂` to `{ toFun := fun w => ⟨_, fwd w.1 w.2⟩ invFun := fun w => ⟨_, bwd w.1 w.2⟩ map_add' := by`. Introduce `a b`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h` using `congrArg Subtype.val (map_add ψ ⟨(a : V), ((memS _ _ _).1 a.2).1⟩ ⟨(b : V), ((memS _ _ _).1 b.2).1⟩)`.

Conclude with `h`. Use the proof step `map_smul' := by`. Introduce `c a`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h` using `congrArg Subtype.val (map_smul ψ (c : E) ⟨(a : V), ((memS _ _ _).1 a.2).1⟩)`.

Conclude with `h`. Use `left_inv := by`. Introduce `a`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules.

Use `right_inv := by`. Introduce `a`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `}`. Establish `hPQ : Submodule.map (e : ThSharp H t₁ (ThL H t₁) →ₗ[M.L.O] ThSharp H t₀ N₂) (Submodule.comap (ThSharp H t₁ (ThL H t₁)).subtype (ThL H t₁)) = Submodule.comap (ThSharp H t₀ N₂).subtype N₂`.

Use extensionality with `x`. Simplify using `only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `(memN _).2 ⟨⟨y, hy⟩, rfl⟩`.

Introduce `hx`. Use `⟨e.symm x, ?_, e.apply_symm_apply x⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `(memN _).1 hx`. Rewrite `hy` using `[hg]`. Establish `h4 : ψ.symm ⟨(x : V), ((memS _ _ _).1 x.2).1⟩ = ⟨(y : V), ((memL _ _).1 y.2).2⟩` using `(LinearEquiv.symm_apply_eq ψ).2 (Subtype.ext hy).symm`.

Establish `h3 : (e.symm x : V) = y` using `congrArg Subtype.val h4`. Rewrite using `[h3]`. Conclude with `y.2`. Set `κ : DDW H t₁ (ThL H t₁) ≃ₗ[M.L.O] DDW H t₀ N₂` to `Submodule.Quotient.equiv _ _ e hPQ`. Establish `hκ : ∀ w, κ (dwMk H t₁ (ThL H t₁) w) = dwMk H t₀ N₂ (e w)` using `fun w => rfl`.

Establish `surj : ∀ m : MMsharp H t₁, ∃ w, η₁ (ddMk H t₁ m) = dwMk H t₁ (ThL H t₁) w`. Introduce `m`. Take `⟨w, hw⟩` from `Submodule.Quotient.mk_surjective _ (η₁ (ddMk H t₁ m))`. Conclude with `⟨w, hw.symm⟩`. Establish `hh : ∀ a b : ThSharp H t₀ N₂, H.h (e.symm a : V) (e.symm b : V) = H.h a b`.

Introduce `a b`. Establish `h` using `hψh (ψ.symm ⟨(a : V), ((memS _ _ _).1 a.2).1⟩) (ψ.symm ⟨(b : V), ((memS _ _ _).1 b.2).1⟩)`. Simplify using `only [LinearEquiv.apply_symm_apply] at h`. Conclude with `h.symm`. Set `η : DDt H t₀ ≃ₗ[M.L.O] DDW H t₀ N₂` to `(θ.symm.trans η₁).trans κ`.

Establish `hle : N₂ ≤ Submodule.restrictScalars M.L.O (H.W0 t₀.f t₀.f')`. Introduce `v hv`. Take `⟨y, rfl⟩` from `(memN v).1 hv`. Conclude with `(ψ _).2`. Establish `hfg : N₂.FG`.

Rewrite using `[hN₂]`. Use `haveI : Module.Finite M.L.O (ThL H t₁) := Module.Finite.iff_fg.2 (hFG V H t₁ hG₁)`. Conclude with `(Module.Finite.fg_top).map g`. Establish `hS1` using `hS V H t₁ hG₁`. Establish `hspan : Submodule.span E (N₂ : Set V) = H.W0 t₀.f t₀.f'`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce `v hv`. Conclude with `hle hv`. Introduce `v hv`.

Establish `hu : ((ψ.symm ⟨v, hv⟩ : H.W0 t₁.f t₁.f') : V) ∈ Submodule.span E (ThL H t₁ : Set V)`. Rewrite using `[hS1]`. Conclude with `(ψ.symm _).2`. Establish `main : ∀ (x : V) (hx : x ∈ Submodule.span E (ThL H t₁ : Set V)), ∀ h : x ∈ H.W0 t₁.f t₁.f', (ψ ⟨x, h⟩ : V) ∈ Submodule.span E (N₂ : Set V)`. Introduce `x hx`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Introduce `h`. Conclude with `Submodule.subset_span ((keyN x h).1 ((memL _ _).1 hx).1)`. Consider the case `zero`.

Introduce `h`. Establish `h0 : (⟨0, h⟩ : H.W0 t₁.f t₁.f') = 0` using `rfl`. Rewrite using `[h0, map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y hx hy ihx ihy`.

Introduce `h`. Establish `hx' : x ∈ H.W0 t₁.f t₁.f'`. Rewrite using `[← hS1]`. Conclude with `hx`. Establish `hy' : y ∈ H.W0 t₁.f t₁.f'`.

Rewrite using `[← hS1]`. Conclude with `hy`. Establish `h0 : (⟨x + y, h⟩ : H.W0 t₁.f t₁.f') = ⟨x, hx'⟩ + ⟨y, hy'⟩` using `rfl`. Rewrite using `[h0, map_add, Submodule.coe_add]`. Conclude with `Submodule.add_mem _ (ihx hx') (ihy hy')`.

Consider the case `smul a x hx ihx`. Introduce `h`. Establish `hx' : x ∈ H.W0 t₁.f t₁.f'`. Rewrite using `[← hS1]`. Conclude with `hx`.

Establish `h0 : (⟨a • x, h⟩ : H.W0 t₁.f t₁.f') = a • ⟨x, hx'⟩` using `rfl`. Rewrite using `[h0, map_smul, Submodule.coe_smul]`. Conclude with `Submodule.smul_mem _ a (ihx hx')`. Establish `h4` using `main _ hu (ψ.symm ⟨v, hv⟩).2`. Simplify using `using h4`.

Establish `hint : ∀ x ∈ N₂, ∀ y ∈ N₂, H.h x y ∈ M.L.O`. Introduce `x hx y hy`. Take `⟨a, rfl⟩` from `(memN x).1 hx`. Take `⟨b, rfl⟩` from `(memN y).1 hy`. Rewrite using `[hg, hg, hψh]`.

Conclude with `(hsd _).1 ((memL _ _).1 a.2).1 _ ((memL _ _).1 b.2).1`. Establish `hpair : ∀ (m m' : MMsharp H t₀) (w w' : ThSharp H t₀ N₂), η (ddMk H t₀ m) = dwMk H t₀ N₂ w → η (ddMk H t₀ m') = dwMk H t₀ N₂ w' → H.h m m' + H.h w w' ∈ M.L.O`. Introduce `m m' w w' hw hw'`. Take `⟨x, hx⟩` from `Submodule.Quotient.mk_surjective _ (θ.symm (ddMk H t₀ m))`. Take `⟨x', hx'⟩` from `Submodule.Quotient.mk_surjective _ (θ.symm (ddMk H t₀ m'))`.

Establish `hθx : θ (ddMk H t₁ x) = ddMk H t₀ m`. Rewrite using `[show ddMk H t₁ x = θ.symm (ddMk H t₀ m) from hx, LinearEquiv.apply_symm_apply]`. Establish `hθx' : θ (ddMk H t₁ x') = ddMk H t₀ m'`. Rewrite using `[show ddMk H t₁ x' = θ.symm (ddMk H t₀ m') from hx', LinearEquiv.apply_symm_apply]`. Establish `h1 : η₁ (ddMk H t₁ x) = dwMk H t₁ (ThL H t₁) (e.symm w)`.

Apply `κ.injective` to reduce the goal to its premises. Rewrite using `[hκ, LinearEquiv.apply_symm_apply, ← hw]`. Use `show κ (η₁ (ddMk H t₁ x)) = κ (η₁ (θ.symm (ddMk H t₀ m)))`. Rewrite using `[← hx]`. Both sides reduce to the same expression.

Establish `h1' : η₁ (ddMk H t₁ x') = dwMk H t₁ (ThL H t₁) (e.symm w')`. Apply `κ.injective` to reduce the goal to its premises. Rewrite using `[hκ, LinearEquiv.apply_symm_apply, ← hw']`. Use `show κ (η₁ (ddMk H t₁ x')) = κ (η₁ (θ.symm (ddMk H t₀ m')))`. Rewrite using `[← hx']`.

Both sides reduce to the same expression. Establish `a1` using `hη₁b x x' (e.symm w) (e.symm w') h1 h1'`. Rewrite `a1` using `[hh]`. Establish `a2` using `hθ x x' m m' hθx hθx'`. Establish `a3` using `add_mem a2 a1`.

Use `a3 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `hGr` using `hG V H hn t₁ f₂ f₂' φ φ' hT hDl`. Take `⟨Λ, ⟨hsd2, hprim, hcap, hη⟩, -⟩` from `hV hM V H t₀ hGr hMM N₂ hle hfg hspan hint η hpair`. Establish `hgen` using `hP hM V H hn t₁ f₂ f₂' φ φ' hT hDl Λ hsd2 hprim`.

Establish `hthc : ThCond H t₁ t₀ Λ φ φ'`. Introduce `n₁ n₂ hc`. Take `⟨hn₁, rfl⟩` from `(hψC n₁ n₂).1 hc`. Rewrite using `[keyN n₁ hn₁, ← hcap]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `(Submodule.mem_inf.1 h).1`. Introduce `h`. Conclude with `Submodule.mem_inf.2 ⟨h, (ψ _).2⟩`. Use `⟨Λ, hgen, hthc, ?_⟩` and prove the remaining obligations.

Introduce `m₁ m₂`. Take `⟨w, hw⟩` from `surj m₁`. Establish `hmw : (m₁ : V) + w ∈ t₁.abelian₂` using `(hη₁a m₁ w).1 hw`. Establish `step : θ (ddMk H t₁ m₁) = ddMk H t₀ m₂ ↔ η (ddMk H t₀ m₂) = dwMk H t₀ N₂ (e w)`. Prove the components needed by the constructor for the conclusion.

Introduce `h show κ (η₁ (θ.symm (ddMk H t₀ m₂))) = _`. Rewrite using `[← h, LinearEquiv.symm_apply_apply, hw, hκ]`. Introduce `h`. Establish `h2 : κ (η₁ (θ.symm (ddMk H t₀ m₂))) = κ (η₁ (ddMk H t₁ m₁))`. Rewrite using `[hw, hκ]`.

Conclude with `h`. Establish `h3` using `η₁.injective (κ.injective h2)`. Rewrite using `[← h3, LinearEquiv.apply_symm_apply]`. Use `step.trans ((hη m₂ (e w)).trans ?_)` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `⟨w, e w, (hψC _ _).2 ⟨((memS _ _ _).1 w.2).1, rfl⟩, hmw, h⟩`. Introduce and unpack `⟨n₁, n₂, hc, h1, h2⟩`. Take `⟨hn₁, rfl⟩` from `(hψC n₁ n₂).1 hc`. Establish `hd : n₁ - w ∈ H.W0 t₁.f t₁.f'` using `Submodule.sub_mem _ hn₁ ((memS _ _ _).1 w.2).1`.

Establish `hdL : n₁ - w ∈ t₁.abelian₂`. Establish `h4` using `t₁.abelian₂.sub_mem h1 hmw`. Simplify using `using h4`. Establish `h3 : (ψ ⟨n₁ - w, hd⟩ : V) ∈ Λ`. Establish `h5` using `(keyN _ hd).1 hdL`.

Rewrite `h5` using `[← hcap]`. Conclude with `(Submodule.mem_inf.1 h5).1`. Establish `hψd : (ψ ⟨n₁ - w, hd⟩ : V) = (ψ ⟨n₁, hn₁⟩ : V) - (e w : V)`. Establish `h6` using `congrArg Subtype.val (map_sub ψ ⟨n₁, hn₁⟩ ⟨(w : V), ((memS _ _ _).1 w.2).1⟩)`. Conclude with `h6`.

Rewrite `h3` using `[hψd]`. Establish `h5` using `Λ.sub_mem h2 h3`. Use `h5 using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws.
-/
theorem glueBack_of (M : Model F E) (r n : ℕ) (hM : M.OK) (hC : CorrIso M r n) (hE : GlueEta M r) (hV : GlueConv M r)
    (hP : GenOfPrim M r n) (hG : GramMM M r n) (hFG : ThFG M r) (hS : ThSpan M r) : GlueBack M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hT hDl hMM θ hθ
  let t₀ : Term V M r := { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' }
  have memS : ∀ (t : Term V M r) (N : Submodule M.L.O V) (w : V),
      w ∈ ThSharp H t N ↔ (w ∈ H.W0 t.f t.f' ∧ ∀ n ∈ N, H.h w n ∈ M.L.O) :=
    fun _ _ _ => Iff.rfl
  have memL : ∀ (t : Term V M r) (w : V), w ∈ ThL H t ↔ (w ∈ t.abelian₂ ∧ w ∈ H.W0 t.f t.f') :=
    fun _ _ => Iff.rfl
  have hG₁ : H.IsGeneric t₁ := by
    obtain ⟨h, -⟩ := id hT
    exact h
  have hsd : ∀ x : V, x ∈ t₁.abelian₂ ↔ ∀ y ∈ t₁.abelian₂, H.h x y ∈ M.L.O := by
    obtain ⟨⟨⟨-, -, h⟩, -⟩, -⟩ := id hG₁
    exact h
  obtain ⟨ψ, hψh, hψC⟩ := hC V H hn t₁ f₂ f₂' φ φ' hT hDl
  obtain ⟨η₁, hη₁a, hη₁b⟩ := hE hM V H t₁ hG₁
  let g : ThL H t₁ →ₗ[M.L.O] V :=
    { toFun := fun x => (ψ ⟨x, ((memL _ _).1 x.2).2⟩ : V)
      map_add' := fun a b => by
        have h := congrArg Subtype.val
          (map_add ψ ⟨(a : V), ((memL _ _).1 a.2).2⟩ ⟨(b : V), ((memL _ _).1 b.2).2⟩)
        exact h
      map_smul' := fun c a => by
        have h := congrArg Subtype.val (map_smul ψ (c : E) ⟨(a : V), ((memL _ _).1 a.2).2⟩)
        exact h }
  have hg : ∀ y : ThL H t₁, g y = (ψ ⟨y, ((memL _ _).1 y.2).2⟩ : V) := fun _ => rfl
  obtain ⟨N₂, hN₂⟩ : ∃ N : Submodule M.L.O V, N = Submodule.map g ⊤ := ⟨_, rfl⟩
  have memN : ∀ v : V, v ∈ N₂ ↔ ∃ y, g y = v := by
    intro v
    rw [hN₂]
    simp only [Submodule.mem_map, Submodule.mem_top, true_and]
  have keyN : ∀ (x : V) (hx : x ∈ H.W0 t₁.f t₁.f'), x ∈ t₁.abelian₂ ↔ (ψ ⟨x, hx⟩ : V) ∈ N₂ := by
    intro x hx
    constructor
    · intro h
      exact (memN _).2 ⟨⟨x, (memL _ _).2 ⟨h, hx⟩⟩, rfl⟩
    · intro h
      obtain ⟨y, hy⟩ := (memN _).1 h
      rw [hg] at hy
      have h2 : (y : V) = x := congrArg Subtype.val (ψ.injective (Subtype.ext hy))
      rw [← h2]
      exact ((memL _ _).1 y.2).1
  have fwd : ∀ (w : V) (hw : w ∈ ThSharp H t₁ (ThL H t₁)),
      (ψ ⟨w, ((memS _ _ _).1 hw).1⟩ : V) ∈ ThSharp H t₀ N₂ := by
    intro w hw
    refine (memS _ _ _).2 ⟨(ψ _).2, ?_⟩
    intro n hn'
    obtain ⟨y, rfl⟩ := (memN _).1 hn'
    rw [hg, hψh]
    exact ((memS _ _ _).1 hw).2 _ y.2
  have bwd : ∀ (w : V) (hw : w ∈ ThSharp H t₀ N₂),
      (ψ.symm ⟨w, ((memS _ _ _).1 hw).1⟩ : V) ∈ ThSharp H t₁ (ThL H t₁) := by
    intro w hw
    refine (memS _ _ _).2 ⟨(ψ.symm _).2, ?_⟩
    intro n hn'
    obtain ⟨hnΛ, hnW⟩ := (memL _ _).1 hn'
    have h2 := hψh (ψ.symm ⟨w, ((memS _ _ _).1 hw).1⟩) ⟨n, hnW⟩
    simp only [LinearEquiv.apply_symm_apply] at h2
    rw [← h2]
    exact ((memS _ _ _).1 hw).2 _ ((memN _).2 ⟨⟨n, hn'⟩, rfl⟩)
  let e : ThSharp H t₁ (ThL H t₁) ≃ₗ[M.L.O] ThSharp H t₀ N₂ :=
    { toFun := fun w => ⟨_, fwd w.1 w.2⟩
      invFun := fun w => ⟨_, bwd w.1 w.2⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        have h := congrArg Subtype.val
          (map_add ψ ⟨(a : V), ((memS _ _ _).1 a.2).1⟩ ⟨(b : V), ((memS _ _ _).1 b.2).1⟩)
        exact h
      map_smul' := by
        intro c a
        apply Subtype.ext
        have h := congrArg Subtype.val (map_smul ψ (c : E) ⟨(a : V), ((memS _ _ _).1 a.2).1⟩)
        exact h
      left_inv := by
        intro a
        apply Subtype.ext
        simp
      right_inv := by
        intro a
        apply Subtype.ext
        simp }
  have hPQ : Submodule.map (e : ThSharp H t₁ (ThL H t₁) →ₗ[M.L.O] ThSharp H t₀ N₂)
      (Submodule.comap (ThSharp H t₁ (ThL H t₁)).subtype (ThL H t₁)) =
      Submodule.comap (ThSharp H t₀ N₂).subtype N₂ := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (memN _).2 ⟨⟨y, hy⟩, rfl⟩
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      obtain ⟨y, hy⟩ := (memN _).1 hx
      rw [hg] at hy
      have h4 : ψ.symm ⟨(x : V), ((memS _ _ _).1 x.2).1⟩ = ⟨(y : V), ((memL _ _).1 y.2).2⟩ :=
        (LinearEquiv.symm_apply_eq ψ).2 (Subtype.ext hy).symm
      have h3 : (e.symm x : V) = y := congrArg Subtype.val h4
      rw [h3]
      exact y.2
  let κ : DDW H t₁ (ThL H t₁) ≃ₗ[M.L.O] DDW H t₀ N₂ := Submodule.Quotient.equiv _ _ e hPQ
  have hκ : ∀ w, κ (dwMk H t₁ (ThL H t₁) w) = dwMk H t₀ N₂ (e w) := fun w => rfl
  have surj : ∀ m : MMsharp H t₁, ∃ w, η₁ (ddMk H t₁ m) = dwMk H t₁ (ThL H t₁) w := by
    intro m
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (η₁ (ddMk H t₁ m))
    exact ⟨w, hw.symm⟩
  have hh : ∀ a b : ThSharp H t₀ N₂, H.h (e.symm a : V) (e.symm b : V) = H.h a b := by
    intro a b
    have h := hψh (ψ.symm ⟨(a : V), ((memS _ _ _).1 a.2).1⟩) (ψ.symm ⟨(b : V), ((memS _ _ _).1 b.2).1⟩)
    simp only [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  let η : DDt H t₀ ≃ₗ[M.L.O] DDW H t₀ N₂ := (θ.symm.trans η₁).trans κ
  have hle : N₂ ≤ Submodule.restrictScalars M.L.O (H.W0 t₀.f t₀.f') := by
    intro v hv
    obtain ⟨y, rfl⟩ := (memN v).1 hv
    exact (ψ _).2
  have hfg : N₂.FG := by
    rw [hN₂]
    haveI : Module.Finite M.L.O (ThL H t₁) := Module.Finite.iff_fg.2 (hFG V H t₁ hG₁)
    exact (Module.Finite.fg_top).map g
  have hS1 := hS V H t₁ hG₁
  have hspan : Submodule.span E (N₂ : Set V) = H.W0 t₀.f t₀.f' := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro v hv
      exact hle hv
    · intro v hv
      have hu : ((ψ.symm ⟨v, hv⟩ : H.W0 t₁.f t₁.f') : V) ∈ Submodule.span E (ThL H t₁ : Set V) := by
        rw [hS1]
        exact (ψ.symm _).2
      have main : ∀ (x : V) (hx : x ∈ Submodule.span E (ThL H t₁ : Set V)),
          ∀ h : x ∈ H.W0 t₁.f t₁.f', (ψ ⟨x, h⟩ : V) ∈ Submodule.span E (N₂ : Set V) := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          intro h
          exact Submodule.subset_span ((keyN x h).1 ((memL _ _).1 hx).1)
        | zero =>
          intro h
          have h0 : (⟨0, h⟩ : H.W0 t₁.f t₁.f') = 0 := rfl
          rw [h0, map_zero]
          exact Submodule.zero_mem _
        | add x y hx hy ihx ihy =>
          intro h
          have hx' : x ∈ H.W0 t₁.f t₁.f' := by
            rw [← hS1]
            exact hx
          have hy' : y ∈ H.W0 t₁.f t₁.f' := by
            rw [← hS1]
            exact hy
          have h0 : (⟨x + y, h⟩ : H.W0 t₁.f t₁.f') = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
          rw [h0, map_add, Submodule.coe_add]
          exact Submodule.add_mem _ (ihx hx') (ihy hy')
        | smul a x hx ihx =>
          intro h
          have hx' : x ∈ H.W0 t₁.f t₁.f' := by
            rw [← hS1]
            exact hx
          have h0 : (⟨a • x, h⟩ : H.W0 t₁.f t₁.f') = a • ⟨x, hx'⟩ := rfl
          rw [h0, map_smul, Submodule.coe_smul]
          exact Submodule.smul_mem _ a (ihx hx')
      have h4 := main _ hu (ψ.symm ⟨v, hv⟩).2
      simpa using h4
  have hint : ∀ x ∈ N₂, ∀ y ∈ N₂, H.h x y ∈ M.L.O := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := (memN x).1 hx
    obtain ⟨b, rfl⟩ := (memN y).1 hy
    rw [hg, hg, hψh]
    exact (hsd _).1 ((memL _ _).1 a.2).1 _ ((memL _ _).1 b.2).1
  have hpair : ∀ (m m' : MMsharp H t₀) (w w' : ThSharp H t₀ N₂),
      η (ddMk H t₀ m) = dwMk H t₀ N₂ w → η (ddMk H t₀ m') = dwMk H t₀ N₂ w' →
      H.h m m' + H.h w w' ∈ M.L.O := by
    intro m m' w w' hw hw'
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (θ.symm (ddMk H t₀ m))
    obtain ⟨x', hx'⟩ := Submodule.Quotient.mk_surjective _ (θ.symm (ddMk H t₀ m'))
    have hθx : θ (ddMk H t₁ x) = ddMk H t₀ m := by
      rw [show ddMk H t₁ x = θ.symm (ddMk H t₀ m) from hx, LinearEquiv.apply_symm_apply]
    have hθx' : θ (ddMk H t₁ x') = ddMk H t₀ m' := by
      rw [show ddMk H t₁ x' = θ.symm (ddMk H t₀ m') from hx', LinearEquiv.apply_symm_apply]
    have h1 : η₁ (ddMk H t₁ x) = dwMk H t₁ (ThL H t₁) (e.symm w) := by
      apply κ.injective
      rw [hκ, LinearEquiv.apply_symm_apply, ← hw]
      show κ (η₁ (ddMk H t₁ x)) = κ (η₁ (θ.symm (ddMk H t₀ m)))
      rw [← hx]
      rfl
    have h1' : η₁ (ddMk H t₁ x') = dwMk H t₁ (ThL H t₁) (e.symm w') := by
      apply κ.injective
      rw [hκ, LinearEquiv.apply_symm_apply, ← hw']
      show κ (η₁ (ddMk H t₁ x')) = κ (η₁ (θ.symm (ddMk H t₀ m')))
      rw [← hx']
      rfl
    have a1 := hη₁b x x' (e.symm w) (e.symm w') h1 h1'
    rw [hh] at a1
    have a2 := hθ x x' m m' hθx hθx'
    have a3 := add_mem a2 a1
    convert a3 using 1
    ring
  have hGr := hG V H hn t₁ f₂ f₂' φ φ' hT hDl
  obtain ⟨Λ, ⟨hsd2, hprim, hcap, hη⟩, -⟩ :=
    hV hM V H t₀ hGr hMM N₂ hle hfg hspan hint η hpair
  have hgen := hP hM V H hn t₁ f₂ f₂' φ φ' hT hDl Λ hsd2 hprim
  have hthc : ThCond H t₁ t₀ Λ φ φ' := by
    intro n₁ n₂ hc
    obtain ⟨hn₁, rfl⟩ := (hψC n₁ n₂).1 hc
    rw [keyN n₁ hn₁, ← hcap]
    constructor
    · intro h
      exact (Submodule.mem_inf.1 h).1
    · intro h
      exact Submodule.mem_inf.2 ⟨h, (ψ _).2⟩
  refine ⟨Λ, hgen, hthc, ?_⟩
  intro m₁ m₂
  obtain ⟨w, hw⟩ := surj m₁
  have hmw : (m₁ : V) + w ∈ t₁.abelian₂ := (hη₁a m₁ w).1 hw
  have step : θ (ddMk H t₁ m₁) = ddMk H t₀ m₂ ↔ η (ddMk H t₀ m₂) = dwMk H t₀ N₂ (e w) := by
    constructor
    · intro h
      show κ (η₁ (θ.symm (ddMk H t₀ m₂))) = _
      rw [← h, LinearEquiv.symm_apply_apply, hw, hκ]
    · intro h
      have h2 : κ (η₁ (θ.symm (ddMk H t₀ m₂))) = κ (η₁ (ddMk H t₁ m₁)) := by
        rw [hw, hκ]
        exact h
      have h3 := η₁.injective (κ.injective h2)
      rw [← h3, LinearEquiv.apply_symm_apply]
  refine step.trans ((hη m₂ (e w)).trans ?_)
  constructor
  · intro h
    exact ⟨w, e w, (hψC _ _).2 ⟨((memS _ _ _).1 w.2).1, rfl⟩, hmw, h⟩
  · rintro ⟨n₁, n₂, hc, h1, h2⟩
    obtain ⟨hn₁, rfl⟩ := (hψC n₁ n₂).1 hc
    have hd : n₁ - w ∈ H.W0 t₁.f t₁.f' := Submodule.sub_mem _ hn₁ ((memS _ _ _).1 w.2).1
    have hdL : n₁ - w ∈ t₁.abelian₂ := by
      have h4 := t₁.abelian₂.sub_mem h1 hmw
      simpa using h4
    have h3 : (ψ ⟨n₁ - w, hd⟩ : V) ∈ Λ := by
      have h5 := (keyN _ hd).1 hdL
      rw [← hcap] at h5
      exact (Submodule.mem_inf.1 h5).1
    have hψd : (ψ ⟨n₁ - w, hd⟩ : V) = (ψ ⟨n₁, hn₁⟩ : V) - (e w : V) := by
      have h6 := congrArg Subtype.val (map_sub ψ ⟨n₁, hn₁⟩ ⟨(w : V), ((memS _ _ _).1 w.2).1⟩)
      exact h6
    rw [hψd] at h3
    have h5 := Λ.sub_mem h2 h3
    convert h5 using 1
    abel

end Back

end Formalism.L2.SG.LsDatumA
