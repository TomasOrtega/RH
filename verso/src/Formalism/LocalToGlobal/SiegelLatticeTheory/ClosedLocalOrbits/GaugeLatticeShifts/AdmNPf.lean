import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianModuleBetaCongruence

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.NormCut

section InAtAlg

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

/- English proof (translation)
Conclude with `natCast_mem _ c`.
-/
theorem natCast_mem_Int (c : ℕ) : ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) ∈ IntAf X.B.I.F X.B.I.E := by
  exact natCast_mem _ c

/- English proof (translation)
Conclude with `(mL X.B.I X.B.g).smul_mem ⟨s, hs⟩ hw`.
-/
theorem smul_mem_mL_int {s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hs : s ∈ IntAf X.B.I.F X.B.I.E) {w : VA X.B.I}
    (hw : w ∈ mL X.B.I X.B.g) : s • w ∈ mL X.B.I X.B.g := by
  exact (mL X.B.I X.B.g).smul_mem ⟨s, hs⟩ hw

/- English proof (translation)
Take `⟨c, hc, hca⟩` from `ha`. Take `⟨d, hd, hdb⟩` from `hb`. Use `⟨c * d, Nat.Coprime.mul hc hd, ?_⟩` and prove the remaining obligations. Establish `e : ((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (a + b) = ((d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (((c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • a) + ((c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (((d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • b)`. Rewrite using `[Nat.cast_mul, smul_add, ← mul_smul, ← mul_smul, mul_comm ((d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)]`.

Rewrite using `[e]`. Conclude with `(mL X.B.I X.B.g).add_mem (smul_mem_mL_int X (natCast_mem_Int X d) hca) (smul_mem_mL_int X (natCast_mem_Int X c) hdb)`.
-/
theorem InAt_add {a b : VA X.B.I} (ha : InAt X.B.I X.B.g X.B.g a) (hb : InAt X.B.I X.B.g X.B.g b) :
    InAt X.B.I X.B.g X.B.g (a + b) := by
  obtain ⟨c, hc, hca⟩ := ha
  obtain ⟨d, hd, hdb⟩ := hb
  refine ⟨c * d, Nat.Coprime.mul hc hd, ?_⟩
  have e : ((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (a + b) =
      ((d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (((c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • a) +
        ((c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (((d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • b) := by
    rw [Nat.cast_mul, smul_add, ← mul_smul, ← mul_smul, mul_comm ((d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)]
  rw [e]
  exact (mL X.B.I X.B.g).add_mem (smul_mem_mL_int X (natCast_mem_Int X d) hca)
    (smul_mem_mL_int X (natCast_mem_Int X c) hdb)

/- English proof (translation)
Take `⟨c, hc, hca⟩` from `ha`. Conclude with `⟨c, hc, by rw [smul_neg]; exact (mL X.B.I X.B.g).neg_mem hca⟩`.
-/
theorem InAt_neg {a : VA X.B.I} (ha : InAt X.B.I X.B.g X.B.g a) : InAt X.B.I X.B.g X.B.g (-a) := by
  obtain ⟨c, hc, hca⟩ := ha
  exact ⟨c, hc, by rw [smul_neg]; exact (mL X.B.I X.B.g).neg_mem hca⟩

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `InAt_add X ha (InAt_neg X hb)`.
-/
theorem InAt_sub {a b : VA X.B.I} (ha : InAt X.B.I X.B.g X.B.g a) (hb : InAt X.B.I X.B.g X.B.g b) :
    InAt X.B.I X.B.g X.B.g (a - b) := by
  rw [sub_eq_add_neg]
  exact InAt_add X ha (InAt_neg X hb)

/- English proof (translation)
Conclude with `⟨1, Nat.coprime_one_left _, by rw [smul_zero]; exact (mL X.B.I X.B.g).zero_mem⟩`.
-/
theorem InAt_zero : InAt X.B.I X.B.g X.B.g 0 := by
  exact ⟨1, Nat.coprime_one_left _, by rw [smul_zero]; exact (mL X.B.I X.B.g).zero_mem⟩

/- English proof (translation)
Take `⟨c, hc, hca⟩` from `ha`. Conclude with `⟨c, hc, by rw [smul_comm]; exact smul_mem_mL_int X hs hca⟩`.
-/
theorem InAt_smul {s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hs : s ∈ IntAf X.B.I.F X.B.I.E) {a : VA X.B.I}
    (ha : InAt X.B.I X.B.g X.B.g a) : InAt X.B.I X.B.g X.B.g (s • a) := by
  obtain ⟨c, hc, hca⟩ := ha
  exact ⟨c, hc, by rw [smul_comm]; exact smul_mem_mL_int X hs hca⟩

/- English proof (translation)
Conclude with `Finset.sum_induction f (fun y => InAt X.B.I X.B.g X.B.g y) (fun _ _ => InAt_add X) (InAt_zero X) h`.
-/
theorem InAt_sum {ι : Type} (t : Finset ι) (f : ι → VA X.B.I) (h : ∀ i ∈ t, InAt X.B.I X.B.g X.B.g (f i)) :
    InAt X.B.I X.B.g X.B.g (∑ i ∈ t, f i) := by
  exact Finset.sum_induction f (fun y => InAt X.B.I X.B.g X.B.g y) (fun _ _ => InAt_add X) (InAt_zero X) h

/- English proof (translation)
Take `⟨c, hc, h⟩` from `ha`. Conclude with `⟨c, hc, by rw [← Matrix.mulVec_smul]; exact mem_mL_of_Kset X hκ _ h⟩`.
-/
theorem InAt_K {κ : X.B.I.Gf} (hκ : κ ∈ X.B.I.Kset) {a : VA X.B.I} (ha : InAt X.B.I X.B.g X.B.g a) :
    InAt X.B.I X.B.g X.B.g (X.B.I.fmat κ *ᵥ a) := by
  obtain ⟨c, hc, h⟩ := ha
  exact ⟨c, hc, by rw [← Matrix.mulVec_smul]; exact mem_mL_of_Kset X hκ _ h⟩

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf]`.
-/
theorem crd_add' (v w : (VS D).V) : X.crd (v + w) = X.crd v + X.crd w := by
  funext i
  simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf]`.
-/
theorem crd_sub' (v w : (VS D).V) : X.crd (v - w) = X.crd v - X.crd w := by
  funext i
  simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf]`.
-/
theorem crd_smul' (a : D.host.E) (v : (VS D).V) : X.crd (a • v) = X.ιE.symm a • X.crd v := by
  funext i
  simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf, map_sum, Finset.sum_apply]`.
-/
theorem crd_sum' {ι : Type} (t : Finset ι) (f : ι → (VS D).V) : X.crd (∑ i ∈ t, f i) = ∑ i ∈ t, X.crd (f i) := by
  funext i
  simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf, map_sum, Finset.sum_apply]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[incl]`.
-/
theorem incl_sub' (x y : Fin X.B.I.n → X.B.I.E) : incl X.B.I (x - y) = incl X.B.I x - incl X.B.I y := by
  funext i
  simp [incl]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[incl]`.
-/
theorem incl_smul' (c : X.B.I.E) (x : Fin X.B.I.n → X.B.I.E) :
    incl X.B.I (c • x) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) c • incl X.B.I x := by
  funext i
  simp [incl]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[incl, map_sum, Finset.sum_apply]`.
-/
theorem incl_sum' {ι : Type} (t : Finset ι) (x : ι → Fin X.B.I.n → X.B.I.E) :
    incl X.B.I (∑ j ∈ t, x j) = ∑ j ∈ t, incl X.B.I (x j) := by
  funext i
  simp [incl, map_sum, Finset.sum_apply]

/- English proof (translation)
Take `⟨M, -, -, hfm, hcrd⟩` from `h`. Rewrite using `[hcrd, hfm]`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec _ _ _ i`.
-/
theorem ratLink_incl {x : X.B.I.GA} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (h : RatLink X x γ) (y : (VS D).V) :
    incl X.B.I (X.crd (γ y)) = X.B.I.fmat x.2 *ᵥ incl X.B.I (X.crd y) := by
  obtain ⟨M, -, -, hfm, hcrd⟩ := h
  rw [hcrd, hfm]
  funext i
  exact RingHom.map_mulVec _ _ _ i

/- English proof (translation)
Use `inclE_mem X.B.I ?_` and prove the remaining obligations. Establish `hint : IsIntegral ℤ (X.ιE.symm (ξ : D.host.E))`. Use `(ξ.2 : IsIntegral ℤ (ξ : D.host.E))` as an intermediate fact. Conclude with `this.map (X.ιE.symm.toRingHom.toIntAlgHom)`. Conclude with `⟨⟨_, hint⟩, rfl⟩`.
-/
theorem inclE_int (ξ : 𝓞 D.host.E) :
    Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm (ξ : D.host.E)) ∈ IntAf X.B.I.F X.B.I.E := by
  refine inclE_mem X.B.I ?_
  have hint : IsIntegral ℤ (X.ιE.symm (ξ : D.host.E)) := by
    have := (ξ.2 : IsIntegral ℤ (ξ : D.host.E))
    exact this.map (X.ιE.symm.toRingHom.toIntAlgHom)
  exact ⟨⟨_, hint⟩, rfl⟩

end InAtAlg

section AdmNMain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def ModGAt : Prop :=
  ∀ (g1 : X.B.I.Gf) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    (∀ y, y ∈ Λ ↔ X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf) →
    ∀ v, ModG (VS D) Λ (gS D) v → InAt X.B.I X.B.g X.B.g (X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd v))

/- English proof (translation)
Unfold `frame mapLF`. Rewrite using `[dif_pos hγ]`. Use `show (mapFlag γ hγ F.fl).fvec c = γ (F.fl.fvec c)`. Simplify using `only [FlagG.fvec, mapFlag]`. Proceed by induction on `c using Fin.lastCases with`.

Consider the case `last => simp only [Fin.snoc_last]`. Consider the case `cast i => simp only [Fin.snoc_castSucc]`.
-/
theorem frame_mapLF {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (c : Fin (D.R.rS + 1)) : frame (mapLF γ F) c = γ (frame F c) := by
  unfold frame mapLF
  rw [dif_pos hγ]
  show (mapFlag γ hγ F.fl).fvec c = γ (F.fl.fvec c)
  simp only [FlagG.fvec, mapFlag]
  induction c using Fin.lastCases with
  | last => simp only [Fin.snoc_last]
  | cast i => simp only [Fin.snoc_castSucc]

/- English proof (translation)
Conclude with `map_sum (Matrix.mulVecLin M) f t`.
-/
theorem mulVec_fsum (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) {ι : Type}
    (t : Finset ι) (f : ι → VA X.B.I) : M *ᵥ (∑ i ∈ t, f i) = ∑ i ∈ t, M *ᵥ f i := by
  exact map_sum (Matrix.mulVecLin M) f t

variable {X} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')

/- English proof (translation)
Introduce `t`. Take `⟨hE0, hF0, hZ0, hB, hBd⟩` from `frame_Lf X`. Use `set g1 : X.B.I.Gf := (cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u with hg1`. Use `set g2 : X.B.I.Gf := (cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u' with hg2`. Establish `hκK` using `hK t`.

Use `set κ := kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt with hκ`. Establish `hκ' : κ = g1⁻¹ * t.pt.2 * g2` using `rfl`. Establish `hb : cs.lamOf (cs.base t.lam) = t.lam` using `cs.base_lam _ t.mem`. Establish `hRL : RatLink X t.pt t.lin` using `t.rep.2.1`. Establish `hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `t.rep.2.2.1`.

Take `⟨-, ⟨ξ, hξl, hξd, hξm⟩, -⟩` from `t.rep.2.2.2.2`. Establish `hlat : ∀ y, y ∈ t.lam ↔ X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf` using `fun y => by`. Rewrite using `[← hb]`. Conclude with `cs.lat_eq _ y`. Use `set s : Fin (D.R.rS + 1) → Fin (D.R.rS + 1) → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := fun a c => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ a c : 𝓞 D.host.E) : D.host.E)) with hs`.

Establish `hsI : ∀ a c, s a c ∈ IntAf X.B.I.F X.B.I.E` using `fun a c => inclE_int X (ξ a c)`. Use `set Y : Fin (D.R.rS + 1) → VA X.B.I := fun a => X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd (F0.fvec a)) with hY`. Use `set Y' : Fin (D.R.rS + 1) → VA X.B.I := fun c => X.B.I.fmat g2⁻¹ *ᵥ incl X.B.I (X.crd (F0'.fvec c)) with hY'`. Establish `key2 : ∀ c, InAt X.B.I X.B.g X.B.g (X.B.I.fmat κ *ᵥ Y' c - ∑ a, s a c • Y a)`. Introduce `c`.

Establish `h1` using `hM g1 t.lam hlat _ (hξm c)`. Use `erw [frame_mapLF hiso] at h1`. Establish `e : X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd (t.lin (frame (lf D F0') c) - frameAct (frame (lf D F0)) ξ c)) = X.B.I.fmat κ *ᵥ Y' c - ∑ a, s a c • Y a`. Simplify using `only [frameAct, crd_sub', crd_sum', crd_smul', incl_sub', incl_sum', incl_smul', Matrix.mulVec_sub, mulVec_fsum, Matrix.mulVec_smul, ratLink_incl X hRL]`. Use `congr 1`.

Simplify using `only [hY', Matrix.mulVec_mulVec, hκ', ← fmat_mul]`. Use `congr 2`. Use `group`. Rewrite `h1` using `[e]`. Conclude with `h1`.

Establish `fixE : ∀ (w : D.what₂.Word) (h : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X w) (a : Fin D.R.rS), X.B.I.fmat ((h : X.B.I.Gf) * X.xu w)⁻¹ *ᵥ incl X.B.I (X.crd (X.eX a)) = incl X.B.I (X.crd (X.eX a))` using `fun w h a => fixes_inv X (fixes_mul X (h.2 _ (Or.inl (Or.inl ⟨a, rfl⟩))) ((X.xu_fix w a).1))`. Establish `fixZ : ∀ (w : D.what₂.Word) (h : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X w), X.B.I.fmat ((h : X.B.I.Gf) * X.xu w)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu w)) = X.B.I.fmat (X.xu w)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu w))`. Introduce `w h`. Establish `hz : X.B.I.fmat (h : X.B.I.Gf)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu w)) = incl X.B.I (X.crd (X.zu w))` using `fixes_inv X (h.2 _ (Or.inr rfl))`. Rewrite using `[_root_.mul_inv_rev, fmat_mul, ← Matrix.mulVec_mulVec, hz]`.

Use `set e0v : Fin (D.R.rS + 1) → VA X.B.I := Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 with he0v`. Establish `hYa : ∀ a, InAt X.B.I X.B.g X.B.g (e0v a - Y a)`. Introduce `a`. Use `Fin.lastCases ?_ (fun i => ?_) a` and prove the remaining obligations. Simplify using `only [he0v, hY, Fin.snoc_last, FlagG.fvec, hTF.2.1, hg1, fixZ]`.

Use `InAt_neg X (X.xu_z u)` as an intermediate fact. Rewrite `this` using `[neg_sub]`. Then use the resulting hypothesis. Simplify using `only [he0v, hY, Fin.snoc_castSucc, FlagG.fvec, hTF.1 i, hg1, fixE]`. Conclude with `(X.basisApprox i).1`. Establish `hY'a : ∀ c, InAt X.B.I X.B.g X.B.g (e0v c - Y' c)`.

Introduce `c`. Use `Fin.lastCases ?_ (fun i => ?_) c` and prove the remaining obligations. Simplify using `only [he0v, hY', Fin.snoc_last, FlagG.fvec, hTF.2.2.2, hg2, fixZ]`. Use `InAt_neg X (X.xu_z u')` as an intermediate fact. Rewrite `this` using `[neg_sub]`. Then use the resulting hypothesis.

Simplify using `only [he0v, hY', Fin.snoc_castSucc, FlagG.fvec, hTF.2.2.1 i, hg2, fixE]`. Conclude with `(X.basisApprox i).1`. Establish `he0vL : ∀ a, e0v a ∈ X.B.I.Lf` using `fun a => by`. Use `Fin.lastCases ?_ (fun i => ?_) a` and prove the remaining obligations. Simplify using `only [he0v, Fin.snoc_last]`.

Conclude with `hZ0`. Simplify using `only [he0v, Fin.snoc_castSucc]`. Conclude with `hE0 i`. Establish `key4 : ∀ c, X.B.I.fmat κ *ᵥ e0v c - ∑ a, s a c • e0v a ∈ mL X.B.I X.B.g`. Introduce `c`.

Establish `hsm : ∀ (z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (w : VA X.B.I), z ∈ IntAf X.B.I.F X.B.I.E → w ∈ X.B.I.Lf → z • w ∈ X.B.I.Lf` using `fun z w hz hw => by`. Establish `: z • w = (⟨z, hz⟩ : IntAf X.B.I.F X.B.I.E) • w` using `rfl`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hw`. Use `mem_mL_of_InAt X (sub_mem (K_mv X.B.I hκK (he0vL c)) (sum_mem fun a _ => hsm _ _ (hsI a c) (he0vL a))) ?_` and prove the remaining obligations.

Establish `e : X.B.I.fmat κ *ᵥ e0v c - ∑ a, s a c • e0v a = (X.B.I.fmat κ *ᵥ Y' c - ∑ a, s a c • Y a) + X.B.I.fmat κ *ᵥ (e0v c - Y' c) - ∑ a, s a c • (e0v a - Y a)`. Simplify using `only [Matrix.mulVec_sub, smul_sub, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `InAt_sub X (InAt_add X (key2 c) (InAt_K X hκK (hY'a c))) (InAt_sum X _ _ fun a _ => InAt_smul X (hsI a c) (hYa a))`.

Establish `hsdiag : ∀ a, s a a = 1` using `fun a => by simp [hs, hξd a]`. Establish `hslow : ∀ a c, c < a → s a c = 0` using `fun a c h => by simp [hs, hξl a c h]`. Use `⟨fun a => ?_, ?_⟩` and prove the remaining obligations. Establish `h4` using `key4 (Fin.castSucc a)`. Rewrite `h4` using `[Fin.sum_univ_castSucc, hslow (Fin.last _) (Fin.castSucc a) (Fin.castSucc_lt_last a), zero_smul, add_zero]`.

Establish `e : (X.B.I.fmat κ - 1) *ᵥ X.e0 a = (X.B.I.fmat κ *ᵥ e0v (Fin.castSucc a) - ∑ i : Fin D.R.rS, s (Fin.castSucc i) (Fin.castSucc a) • e0v (Fin.castSucc i)) + ∑ i : Fin D.R.rS, (s (Fin.castSucc i) (Fin.castSucc a) - if i = a then 1 else 0) • X.e0 i`. Simplify using `only [he0v, Fin.snoc_castSucc, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.sub_mulVec, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Use `add_mem (mL_Mo X.B.I h4) (sum_mem fun i _ => ?_)` and prove the remaining obligations.

Distinguish the cases in `hi : i.1 < a.1`. Establish `hne : i ≠ a` using `fun h => by subst h; exact lt_irrefl _ hi`. Rewrite using `[if_neg hne, sub_zero]`. Establish `: s (Fin.castSucc i) (Fin.castSucc a) • X.e0 i = (⟨_, hsI _ _⟩ : IntAf X.B.I.F X.B.I.E) • X.e0 i` using `rfl`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ (sub_Mo X.B.I ⟨i, hi, rfl⟩)`. Distinguish the cases in `hia : i = a`. Substitute `hia` using the available equality. Rewrite using `[if_pos rfl, hsdiag, sub_self, zero_smul]`. Conclude with `zero_mem _`.

Establish `hlt : Fin.castSucc a < Fin.castSucc i`. Rewrite using `[Fin.castSucc_lt_castSucc_iff]`. Conclude with `lt_of_le_of_ne (not_lt.1 hi) (fun h => hia h.symm)`. Rewrite using `[if_neg hia, hslow _ _ hlt, sub_zero, zero_smul]`. Conclude with `zero_mem _`.

Establish `h4` using `key4 (Fin.last _)`. Rewrite `h4` using `[Fin.sum_univ_castSucc, hsdiag, one_smul]`. Establish `e : (X.B.I.fmat κ - 1) *ᵥ X.z0 = (X.B.I.fmat κ *ᵥ e0v (Fin.last _) - (∑ i : Fin D.R.rS, s (Fin.castSucc i) (Fin.last _) • e0v (Fin.castSucc i) + e0v (Fin.last _))) + ∑ i : Fin D.R.rS, s (Fin.castSucc i) (Fin.last _) • X.e0 i`. Simplify using `only [he0v, Fin.snoc_castSucc, Fin.snoc_last, Matrix.sub_mulVec, Matrix.one_mulVec]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Use `add_mem (mL_Mo X.B.I h4) (sum_mem fun i _ => ?_)` and prove the remaining obligations. Establish `: s (Fin.castSucc i) (Fin.last _) • X.e0 i = (⟨_, hsI _ _⟩ : IntAf X.B.I.F X.B.I.E) • X.e0 i` using `rfl`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (sub_Mo X.B.I ⟨i, rfl⟩)`.
-/
theorem adm_norm_of_fixed_frames (hTF : FrameTie X u u' F0 F0') (hK : TermK F0 F0' cs cs') (hM : ModGAt X) :
    AdmN F0 F0' cs cs' := by
  intro t
  obtain ⟨hE0, hF0, hZ0, hB, hBd⟩ := frame_Lf X
  set g1 : X.B.I.Gf := (cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u with hg1
  set g2 : X.B.I.Gf := (cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u' with hg2
  have hκK := hK t
  set κ := kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt with hκ
  have hκ' : κ = g1⁻¹ * t.pt.2 * g2 := rfl
  have hb : cs.lamOf (cs.base t.lam) = t.lam := cs.base_lam _ t.mem
  have hRL : RatLink X t.pt t.lin := t.rep.2.1
  have hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  obtain ⟨-, ⟨ξ, hξl, hξd, hξm⟩, -⟩ := t.rep.2.2.2.2
  have hlat : ∀ y, y ∈ t.lam ↔ X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf := fun y => by
    rw [← hb]; exact cs.lat_eq _ y

  set s : Fin (D.R.rS + 1) → Fin (D.R.rS + 1) → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F :=
    fun a c => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ a c : 𝓞 D.host.E) : D.host.E)) with hs
  have hsI : ∀ a c, s a c ∈ IntAf X.B.I.F X.B.I.E := fun a c => inclE_int X (ξ a c)

  set Y : Fin (D.R.rS + 1) → VA X.B.I := fun a => X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd (F0.fvec a)) with hY
  set Y' : Fin (D.R.rS + 1) → VA X.B.I := fun c => X.B.I.fmat g2⁻¹ *ᵥ incl X.B.I (X.crd (F0'.fvec c)) with hY'
  have key2 : ∀ c, InAt X.B.I X.B.g X.B.g (X.B.I.fmat κ *ᵥ Y' c - ∑ a, s a c • Y a) := by
    intro c
    have h1 := hM g1 t.lam hlat _ (hξm c)
    erw [frame_mapLF hiso] at h1
    have e : X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd (t.lin (frame (lf D F0') c) -
        frameAct (frame (lf D F0)) ξ c)) = X.B.I.fmat κ *ᵥ Y' c - ∑ a, s a c • Y a := by
      simp only [frameAct, crd_sub', crd_sum', crd_smul', incl_sub', incl_sum', incl_smul', Matrix.mulVec_sub,
        mulVec_fsum, Matrix.mulVec_smul, ratLink_incl X hRL]
      congr 1
      simp only [hY', Matrix.mulVec_mulVec, hκ', ← fmat_mul]
      congr 2
      group
    rw [e] at h1
    exact h1

  have fixE : ∀ (w : D.what₂.Word) (h : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X w) (a : Fin D.R.rS),
      X.B.I.fmat ((h : X.B.I.Gf) * X.xu w)⁻¹ *ᵥ incl X.B.I (X.crd (X.eX a)) = incl X.B.I (X.crd (X.eX a)) :=
    fun w h a => fixes_inv X (fixes_mul X (h.2 _ (Or.inl (Or.inl ⟨a, rfl⟩))) ((X.xu_fix w a).1))
  have fixZ : ∀ (w : D.what₂.Word) (h : Formalism.L2.SG.PoincareInHH.PoincareSetting.Hfin X w),
      X.B.I.fmat ((h : X.B.I.Gf) * X.xu w)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu w)) =
        X.B.I.fmat (X.xu w)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu w)) := by
    intro w h
    have hz : X.B.I.fmat (h : X.B.I.Gf)⁻¹ *ᵥ incl X.B.I (X.crd (X.zu w)) = incl X.B.I (X.crd (X.zu w)) :=
      fixes_inv X (h.2 _ (Or.inr rfl))
    rw [_root_.mul_inv_rev, fmat_mul, ← Matrix.mulVec_mulVec, hz]
  set e0v : Fin (D.R.rS + 1) → VA X.B.I := Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 with he0v
  have hYa : ∀ a, InAt X.B.I X.B.g X.B.g (e0v a - Y a) := by
    intro a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp only [he0v, hY, Fin.snoc_last, FlagG.fvec, hTF.2.1, hg1, fixZ]
      have := InAt_neg X (X.xu_z u)
      rwa [neg_sub] at this
    · simp only [he0v, hY, Fin.snoc_castSucc, FlagG.fvec, hTF.1 i, hg1, fixE]
      exact (X.basisApprox i).1
  have hY'a : ∀ c, InAt X.B.I X.B.g X.B.g (e0v c - Y' c) := by
    intro c
    refine Fin.lastCases ?_ (fun i => ?_) c
    · simp only [he0v, hY', Fin.snoc_last, FlagG.fvec, hTF.2.2.2, hg2, fixZ]
      have := InAt_neg X (X.xu_z u')
      rwa [neg_sub] at this
    · simp only [he0v, hY', Fin.snoc_castSucc, FlagG.fvec, hTF.2.2.1 i, hg2, fixE]
      exact (X.basisApprox i).1
  have he0vL : ∀ a, e0v a ∈ X.B.I.Lf := fun a => by
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp only [he0v, Fin.snoc_last]; exact hZ0
    · simp only [he0v, Fin.snoc_castSucc]; exact hE0 i
  have key4 : ∀ c, X.B.I.fmat κ *ᵥ e0v c - ∑ a, s a c • e0v a ∈ mL X.B.I X.B.g := by
    intro c
    have hsm : ∀ (z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (w : VA X.B.I), z ∈ IntAf X.B.I.F X.B.I.E → w ∈ X.B.I.Lf →
        z • w ∈ X.B.I.Lf := fun z w hz hw => by
      have : z • w = (⟨z, hz⟩ : IntAf X.B.I.F X.B.I.E) • w := rfl
      rw [this]; exact Submodule.smul_mem _ _ hw
    refine mem_mL_of_InAt X (sub_mem (K_mv X.B.I hκK (he0vL c)) (sum_mem fun a _ => hsm _ _ (hsI a c) (he0vL a))) ?_
    have e : X.B.I.fmat κ *ᵥ e0v c - ∑ a, s a c • e0v a =
        (X.B.I.fmat κ *ᵥ Y' c - ∑ a, s a c • Y a) + X.B.I.fmat κ *ᵥ (e0v c - Y' c) -
          ∑ a, s a c • (e0v a - Y a) := by
      simp only [Matrix.mulVec_sub, smul_sub, Finset.sum_sub_distrib]; abel
    rw [e]
    exact InAt_sub X (InAt_add X (key2 c) (InAt_K X hκK (hY'a c)))
      (InAt_sum X _ _ fun a _ => InAt_smul X (hsI a c) (hYa a))

  have hsdiag : ∀ a, s a a = 1 := fun a => by simp [hs, hξd a]
  have hslow : ∀ a c, c < a → s a c = 0 := fun a c h => by simp [hs, hξl a c h]
  refine ⟨fun a => ?_, ?_⟩
  · have h4 := key4 (Fin.castSucc a)
    rw [Fin.sum_univ_castSucc, hslow (Fin.last _) (Fin.castSucc a) (Fin.castSucc_lt_last a), zero_smul,
      add_zero] at h4
    have e : (X.B.I.fmat κ - 1) *ᵥ X.e0 a = (X.B.I.fmat κ *ᵥ e0v (Fin.castSucc a) -
        ∑ i : Fin D.R.rS, s (Fin.castSucc i) (Fin.castSucc a) • e0v (Fin.castSucc i)) +
        ∑ i : Fin D.R.rS, (s (Fin.castSucc i) (Fin.castSucc a) - if i = a then 1 else 0) • X.e0 i := by
      simp only [he0v, Fin.snoc_castSucc, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    rw [e]
    refine add_mem (mL_Mo X.B.I h4) (sum_mem fun i _ => ?_)
    by_cases hi : i.1 < a.1
    · have hne : i ≠ a := fun h => by subst h; exact lt_irrefl _ hi
      rw [if_neg hne, sub_zero]
      have : s (Fin.castSucc i) (Fin.castSucc a) • X.e0 i =
          (⟨_, hsI _ _⟩ : IntAf X.B.I.F X.B.I.E) • X.e0 i := rfl
      rw [this]
      exact Submodule.smul_mem _ _ (sub_Mo X.B.I ⟨i, hi, rfl⟩)
    · by_cases hia : i = a
      · subst hia; rw [if_pos rfl, hsdiag, sub_self, zero_smul]; exact zero_mem _
      · have hlt : Fin.castSucc a < Fin.castSucc i := by
          rw [Fin.castSucc_lt_castSucc_iff]
          exact lt_of_le_of_ne (not_lt.1 hi) (fun h => hia h.symm)
        rw [if_neg hia, hslow _ _ hlt, sub_zero, zero_smul]; exact zero_mem _
  · have h4 := key4 (Fin.last _)
    rw [Fin.sum_univ_castSucc, hsdiag, one_smul] at h4
    have e : (X.B.I.fmat κ - 1) *ᵥ X.z0 = (X.B.I.fmat κ *ᵥ e0v (Fin.last _) -
        (∑ i : Fin D.R.rS, s (Fin.castSucc i) (Fin.last _) • e0v (Fin.castSucc i) + e0v (Fin.last _))) +
        ∑ i : Fin D.R.rS, s (Fin.castSucc i) (Fin.last _) • X.e0 i := by
      simp only [he0v, Fin.snoc_castSucc, Fin.snoc_last, Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    rw [e]
    refine add_mem (mL_Mo X.B.I h4) (sum_mem fun i _ => ?_)
    have : s (Fin.castSucc i) (Fin.last _) • X.e0 i = (⟨_, hsI _ _⟩ : IntAf X.B.I.F X.B.I.E) • X.e0 i := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (sub_Mo X.B.I ⟨i, rfl⟩)

end AdmNMain

end Formalism.L2.SG.NormCut
