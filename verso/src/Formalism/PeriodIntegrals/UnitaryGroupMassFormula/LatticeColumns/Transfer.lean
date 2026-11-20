import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.ClassCount
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bridge
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxGroup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.PoincareInHH PI.MassDataKppVolLemmas
open scoped TensorProduct
open Matrix

/- English proof (translation)
Establish `himg : ∀ a : G, φ '' DoubleCoset.doubleCoset a (Γ : Set G) (K : Set G) = DoubleCoset.doubleCoset (φ a) (Γ' : Set G') (K' : Set G')`. Introduce `a`. Substitute `hΓ hK` using the available equality. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, rfl⟩`. Take `⟨h, hh, k, hk, rfl⟩` from `DoubleCoset.mem_doubleCoset.1 hx`. Conclude with `DoubleCoset.mem_doubleCoset.2 ⟨φ h, ⟨h, hh, rfl⟩, φ k, ⟨k, hk, rfl⟩, by simp [map_mul]⟩`. Introduce `hy`. Take `⟨h', ⟨h, hh, rfl⟩, k', ⟨k, hk, rfl⟩, rfl⟩` from `DoubleCoset.mem_doubleCoset.1 hy`.

Conclude with `⟨h * a * k, DoubleCoset.mem_doubleCoset.2 ⟨h, hh, k, hk, rfl⟩, by simp [map_mul]⟩`. Use `Nat.card_congr (Quotient.congr φ.toEquiv fun a b => ?_)` and prove the remaining obligations. Use `show DoubleCoset.doubleCoset a (Γ : Set G) (K : Set G) = DoubleCoset.doubleCoset b (Γ : Set G) (K : Set G) ↔ DoubleCoset.doubleCoset (φ a) (Γ' : Set G') (K' : Set G') = DoubleCoset.doubleCoset (φ b) (Γ' : Set G') (K' : Set G')`. Rewrite using `[← himg, ← himg]`. Conclude with `(Set.image_injective.2 φ.injective).eq_iff.symm`.
-/
theorem card_dc_congr {G G' : Type} [Group G] [Group G'] (φ : G ≃* G') (Γ K : Subgroup G) (Γ' K' : Subgroup G')
    (hΓ : Γ.map φ.toMonoidHom = Γ') (hK : K.map φ.toMonoidHom = K') :
    Nat.card (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) =
      Nat.card (DoubleCoset.Quotient (Γ' : Set G') (K' : Set G')) := by
  classical
  have himg : ∀ a : G, φ '' DoubleCoset.doubleCoset a (Γ : Set G) (K : Set G) =
      DoubleCoset.doubleCoset (φ a) (Γ' : Set G') (K' : Set G') := by
    intro a
    subst hΓ hK
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨h, hh, k, hk, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hx
      exact DoubleCoset.mem_doubleCoset.2 ⟨φ h, ⟨h, hh, rfl⟩, φ k, ⟨k, hk, rfl⟩, by simp [map_mul]⟩
    · intro hy
      obtain ⟨h', ⟨h, hh, rfl⟩, k', ⟨k, hk, rfl⟩, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hy
      exact ⟨h * a * k, DoubleCoset.mem_doubleCoset.2 ⟨h, hh, k, hk, rfl⟩, by simp [map_mul]⟩
  refine Nat.card_congr (Quotient.congr φ.toEquiv fun a b => ?_)
  show DoubleCoset.doubleCoset a (Γ : Set G) (K : Set G) = DoubleCoset.doubleCoset b (Γ : Set G) (K : Set G) ↔
    DoubleCoset.doubleCoset (φ a) (Γ' : Set G') (K' : Set G') =
      DoubleCoset.doubleCoset (φ b) (Γ' : Set G') (K' : Set G')
  rw [← himg, ← himg]
  exact (Set.image_injective.2 φ.injective).eq_iff.symm

def tfE (I : Formalism.MainNotions.S.AutInst) (hb : AdBridgeIso I) : I.Gf ≃* HA (Af I.F) I.cm.sig I.J :=
  MulEquiv.ofBijective (tfHom I hb) ⟨Bridge_tf_injective I hb, Bridge_tf_surjective I hb⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tfE_apply (I : Formalism.MainNotions.S.AutInst) (hb : AdBridgeIso I) (x : I.Gf) : tfE I hb x = tf I hb x := rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[ratV, swapE, Formalism.UG.inclE, inclR]`.
-/
theorem ratV_eq_swap (I : Formalism.MainNotions.S.AutInst) (w : Fin I.n → I.E) :
    ratV (F := I.F) (Af I.F) w = fun i => swapE I (Formalism.UG.inclE (F := I.F) (Af I.F) (w i)) := by
  funext i
  simp [ratV, swapE, Formalism.UG.inclE, inclR]

/- English proof (translation)
Establish `hm` using `Bridge_mat I hb x`. Simplify using `only [lin, Matrix.mulVecLin_apply]`. Rewrite using `[hm, ratV_eq_swap]`. Establish `key : ∀ v : Fin I.n → I.E ⊗[I.F] Af I.F, (I.fmat x).map (swapE I) *ᵥ (fun i => swapE I (v i)) = fun i => swapE I ((I.fmat x *ᵥ v) i)`. Introduce `v`.

Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec (swapE I : I.E ⊗[I.F] Af I.F →+* Af I.F ⊗[I.F] I.E) (I.fmat x) v i).symm`. Rewrite using `[key]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use function extensionality and compare the values at `i`. Conclude with `(swapE I).injective (congrFun h i)`. Introduce `h`. Rewrite using `[h]`.
-/
theorem lin_tf_fix_iff (I : Formalism.MainNotions.S.AutInst) (hb : AdBridgeIso I) (x : I.Gf) (w : Fin I.n → I.E) :
    lin (Af I.F) I.cm.sig I.J (tf I hb x) (ratV (F := I.F) (Af I.F) w) = ratV (F := I.F) (Af I.F) w ↔
      I.fmat x *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (w i)) =
        (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (w i)) := by
  have hm := Bridge_mat I hb x
  simp only [lin, Matrix.mulVecLin_apply]
  rw [hm, ratV_eq_swap]
  have key : ∀ v : Fin I.n → I.E ⊗[I.F] Af I.F,
      (I.fmat x).map (swapE I) *ᵥ (fun i => swapE I (v i)) = fun i => swapE I ((I.fmat x *ᵥ v) i) := by
    intro v
    funext i
    exact (RingHom.map_mulVec (swapE I : I.E ⊗[I.F] Af I.F →+* Af I.F ⊗[I.F] I.E) (I.fmat x) v i).symm
  rw [key]
  constructor
  · intro h
    funext i
    exact (swapE I).injective (congrFun h i)
  · intro h
    rw [h]

/- English proof (translation)
Unfold `Hsub`. Rewrite using `[mem_stabT]`. Simplify using `only [lin_tf_fix_iff]`. Use `show (∀ y ∈ PoincareSetting.fixSet X u, X.B.I.fmat x *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I y = Formalism.L2.SG.HidaSetting.incl X.B.I y) ↔ _`. Prove the components needed by the constructor for the conclusion.

Introduce `h b`. Use `Fin.addCases (fun i => ?_) (fun j => ?_) b` and prove the remaining obligations. Rewrite using `[tupH, Fin.append_left]`. Use `Fin.lastCases ?_ (fun k => ?_) i` and prove the remaining obligations. Rewrite using `[F0, Fin.snoc_last]`.

Conclude with `h _ (Or.inr rfl)`. Rewrite using `[F0, Fin.snoc_castSucc]`. Conclude with `h _ (Or.inl (Or.inl ⟨k, rfl⟩))`. Rewrite using `[tupH, Fin.append_right]`. Conclude with `h _ (Or.inl (Or.inr ⟨j, rfl⟩))`.

Introduce `h y hy`. Break down `hy with ((⟨a, rfl⟩ | ⟨a, rfl⟩) | hz)` into its components or cases. Use `h (Fin.castAdd D.R.rS (Fin.castSucc a))` as an intermediate fact. Rewrite `this` using `[tupH, Fin.append_left, F0, Fin.snoc_castSucc]`. Conclude with `this`.

Use `h (Fin.natAdd (D.R.rS + 1) a)` as an intermediate fact. Rewrite `this` using `[tupH, Fin.append_right]`. Conclude with `this`. Rewrite `hz` using `[Set.mem_singleton_iff]`. Substitute `hz` using the available equality.

Use `h (Fin.castAdd D.R.rS (Fin.last D.R.rS))` as an intermediate fact. Rewrite `this` using `[tupH, Fin.append_left, F0, Fin.snoc_last]`. Conclude with `this`.
-/
theorem mem_Hfin_iff {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (x : X.B.I.Gf) :
    x ∈ PoincareSetting.Hfin X u ↔ tf X.B.I hb x ∈ Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) := by
  unfold Hsub
  rw [mem_stabT]
  simp only [lin_tf_fix_iff]
  show (∀ y ∈ PoincareSetting.fixSet X u, X.B.I.fmat x *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I y =
    Formalism.L2.SG.HidaSetting.incl X.B.I y) ↔ _
  constructor
  · intro h b
    refine Fin.addCases (fun i => ?_) (fun j => ?_) b
    · rw [tupH, Fin.append_left]
      refine Fin.lastCases ?_ (fun k => ?_) i
      · rw [F0, Fin.snoc_last]
        exact h _ (Or.inr rfl)
      · rw [F0, Fin.snoc_castSucc]
        exact h _ (Or.inl (Or.inl ⟨k, rfl⟩))
    · rw [tupH, Fin.append_right]
      exact h _ (Or.inl (Or.inr ⟨j, rfl⟩))
  · intro h y hy
    rcases hy with ((⟨a, rfl⟩ | ⟨a, rfl⟩) | hz)
    · have := h (Fin.castAdd D.R.rS (Fin.castSucc a))
      rw [tupH, Fin.append_left, F0, Fin.snoc_castSucc] at this
      exact this
    · have := h (Fin.natAdd (D.R.rS + 1) a)
      rw [tupH, Fin.append_right] at this
      exact this
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      have := h (Fin.castAdd D.R.rS (Fin.last D.R.rS))
      rw [tupH, Fin.append_left, F0, Fin.snoc_last] at this
      exact this

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[Subgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `(mem_Hfin_iff X hb u x).1 hx`.

Introduce `hy`. Take `⟨x, rfl⟩` from `Bridge_tf_surjective X.B.I hb y`. Conclude with `⟨x, (mem_Hfin_iff X hb u x).2 hy, rfl⟩`.
-/
theorem map_Hfin {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) :
    (PoincareSetting.Hfin X u).map (tfE X.B.I hb).toMonoidHom =
      Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_Hfin_iff X hb u x).1 hx
  · intro hy
    obtain ⟨x, rfl⟩ := Bridge_tf_surjective X.B.I hb y
    exact ⟨x, (mem_Hfin_iff X hb u x).2 hy, rfl⟩

def hE {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) :
    ↥(PoincareSetting.Hfin X u) ≃* ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) :=
  ((tfE X.B.I hb).subgroupMap (PoincareSetting.Hfin X u)).trans (MulEquiv.subgroupCongr (map_Hfin X hb u))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hE_val {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (h : PoincareSetting.Hfin X u) :
    ((hE X hb u h : Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) =
      tf X.B.I hb (h : X.B.I.Gf) := rfl

/- English proof (translation)
Unfold `unitaryLevelClosureSubgroup`. Establish `: (Subtype.val ⁻¹' K2u X hb u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) = (unitaryLevelIntersection X hb hK u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))` using `rfl`. Rewrite using `[this, Subgroup.closure_eq]`.
-/
theorem coe_K2Hg {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word) :
    (unitaryLevelClosureSubgroup X hb u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) = Subtype.val ⁻¹' K2u X hb u := by
  unfold unitaryLevelClosureSubgroup
  have : (Subtype.val ⁻¹' K2u X hb u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) =
      (unitaryLevelIntersection X hb hK u : Set (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) := rfl
  rw [this, Subgroup.closure_eq]

/- English proof (translation)
Rewrite using `[mem_conjugate_level_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, e⟩`. Establish `e' : tfE X.B.I hb (X.xu u * k * (X.xu u)⁻¹) = tfE X.B.I hb x`. Rewrite using `[map_mul, map_mul, map_inv]`.

Conclude with `e`. Use `(tfE X.B.I hb).injective e'` as an intermediate fact. Rewrite using `[← this]`. Simplify `hk` using `[mul_assoc]`. Introduce `h`.

Use `⟨_, h, ?_⟩` and prove the remaining obligations. Establish `: finHA X hb (X.xu u) * finHA X hb ((X.xu u)⁻¹ * x * X.xu u) * (finHA X hb (X.xu u))⁻¹ = tfE X.B.I hb (X.xu u * ((X.xu u)⁻¹ * x * X.xu u) * (X.xu u)⁻¹)`. Rewrite using `[map_mul, map_mul, map_inv]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Simplify using `[mul_assoc, tfE_apply]`.
-/
theorem mem_conjugate_level_finite_iff {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (x : X.B.I.Gf) :
    tf X.B.I hb x ∈ K2u X hb u ↔ (X.xu u)⁻¹ * x * X.xu u ∈ X.K2 := by
  rw [mem_conjugate_level_iff]
  constructor
  · rintro ⟨k, hk, e⟩
    have e' : tfE X.B.I hb (X.xu u * k * (X.xu u)⁻¹) = tfE X.B.I hb x := by
      rw [map_mul, map_mul, map_inv]
      exact e
    have := (tfE X.B.I hb).injective e'
    rw [← this]
    simpa [mul_assoc] using hk
  · intro h
    refine ⟨_, h, ?_⟩
    have : finHA X hb (X.xu u) * finHA X hb ((X.xu u)⁻¹ * x * X.xu u) * (finHA X hb (X.xu u))⁻¹ =
        tfE X.B.I hb (X.xu u * ((X.xu u)⁻¹ * x * X.xu u) * (X.xu u)⁻¹) := by
      rw [map_mul, map_mul, map_inv]
      rfl
    rw [this]
    simp [mul_assoc, tfE_apply]

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[Subgroup.mem_map]`. Establish `hy : y ∈ unitaryLevelClosureSubgroup X hb u ↔ (y : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ K2u X hb u`. Rewrite using `[← SetLike.mem_coe, coe_K2Hg X hb hK u]`. Both sides reduce to the same expression.

Rewrite using `[hy]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, hh, rfl⟩`. Rewrite using `[MulEquiv.coe_toMonoidHom, hE_val, mem_conjugate_level_finite_iff]`. Conclude with `hh`.

Introduce `h2`. Take `⟨h, rfl⟩` from `(hE X hb u).surjective y`. Use `⟨h, ?_, rfl⟩` and prove the remaining obligations. Rewrite `h2` using `[hE_val, mem_conjugate_level_finite_iff]`. Conclude with `h2`.
-/
theorem map_Ku {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word) :
    (PoincareSetting.Ku X u hK).map (hE X hb u).toMonoidHom = unitaryLevelClosureSubgroup X hb u := by
  ext y
  rw [Subgroup.mem_map]
  have hy : y ∈ unitaryLevelClosureSubgroup X hb u ↔ (y : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈ K2u X hb u := by
    rw [← SetLike.mem_coe, coe_K2Hg X hb hK u]
    rfl
  rw [hy]
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, hE_val, mem_conjugate_level_finite_iff]
    exact hh
  · intro h2
    obtain ⟨h, rfl⟩ := (hE X hb u).surjective y
    refine ⟨h, ?_, rfl⟩
    rw [hE_val, mem_conjugate_level_finite_iff] at h2
    exact h2

/- English proof (translation)
Establish `hB` using `(toHA_isBridge I hb γ).2`. Rewrite using `[hB]`. Use extensionality with `i j`. Simplify using `only [ofHAFin, Matrix.map_apply]`. Rewrite using `[← Bridge_tens_eq]`.

Both sides reduce to the same expression.
-/
theorem fin_mat (I : Formalism.MainNotions.S.AutInst) (hb : AdBridgeIso I) (γ : I.GA) :
    ((HA.mat (Af I.F) I.cm.sig I.J ((splitA I.cm.sig I.J (toHA I hb γ)).2) : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) _) = (I.fmat γ.2).map (swapE I) := by
  have hB := (toHA_isBridge I hb γ).2
  rw [hB]
  ext i j
  simp only [ofHAFin, Matrix.map_apply]
  rw [← Bridge_tens_eq]
  rfl

/- English proof (translation)
Conclude with `RingHom.ext fun e => by simp [inclR, sigR]`.
-/
theorem inclR_comp_sig {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) : (inclR (F := F) R).comp (σ : E →+* E) = (sigR R σ).comp (inclR (F := F) R) := by
  exact RingHom.ext fun e => by simp [inclR, sigR]

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[Subgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, ⟨γ, rfl⟩, rfl⟩`. Take `⟨M, hM, -, hf⟩` from `(Subgroup.mem_inf.1 γ.2).1`.

Use `show (HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (tf X.B.I hb (γ : X.B.I.GA).2) : GL (Fin X.B.I.n) _) ∈ HFin (Af X.B.I.F) X.B.I.cm.sig X.B.I.J`. Use `⟨M, hM, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Use `show (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (F := X.B.I.F) (Af X.B.I.F)) = _`. Rewrite using `[Bridge_mat, hf, Matrix.map_map]`.

Use `congr 1`. Introduce `hy`. Establish `hy' : (HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (y : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) : GL (Fin X.B.I.n) _) ∈ HFin (Af X.B.I.F) X.B.I.cm.sig X.B.I.J` using `hy`. Take `⟨M, hM, hMy⟩` from `Subgroup.mem_map.1 hy'`. Set `Hf : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J` to `⟨Formalism.UG.bc (inclR (F := X.B.I.F) (AF X.B.I.F)) M, Formalism.UG.P.bc_mem _ _ _ (inclR_comp_sig (AF X.B.I.F) X.B.I.cm.sig) _ M hM⟩`.

Establish `hrat : Hf ∈ ratHA X.B.I` using `⟨M, hM, rfl⟩`. Rewrite `hrat` using `[← hGF (toHA X.B.I hb) (toHA_isBridge X.B.I hb)]`. Take `⟨γ, hγ, hγe⟩` from `hrat`. Establish `htf : tf X.B.I hb γ.2 = (y : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)`. Apply `Bridge_HA_ext` to reduce the goal to its premises.

Rewrite using `[Bridge_mat, ← fin_mat X.B.I hb γ, hγe]`. Rewrite using `[← hMy]`. Use `show ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (F := X.B.I.F) (AF X.B.I.F))).map (tensMap (E := X.B.I.E) (sndA X.B.I.F)) = (M : Matrix _ _ _).map (inclR (F := X.B.I.F) (Af X.B.I.F))`. Rewrite using `[Matrix.map_map]`. Use `congr 1`.

Establish `hγ2 : γ.2 ∈ PoincareSetting.Hfin X u` using `(mem_Hfin_iff X hb u γ.2).2 (htf ▸ y.2)`. Take `⟨M', hM', hinf, hfin⟩` from `hγ`. Establish `hγ1 : γ.1 ∈ PoincareSetting.Hinf X u`. Introduce `v x hx`. Establish `hfix : (M' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x`.

Establish `h0` using `hγ2 x hx`. Rewrite `h0` using `[hfin]`. Use function extensionality and compare the values at `i`. Use `PIW.AdelClassFin.DictRing.nontrivial (F := X.B.I.F)` as an intermediate fact. Apply `Formalism.UG.P.inclE_injective X.B.I.F X.B.I.E (Af X.B.I.F)` to reduce the goal to its premises.

Establish `h1` using `congrFun h0 i`. Establish `h2` using `RingHom.map_mulVec (Formalism.UG.inclE (F := X.B.I.F) (E := X.B.I.E) (Af X.B.I.F)) (M' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) x i`. Conclude with `h2.trans h1`. Establish `hPP : X.B.I.P v * (X.B.I.P v)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v))`. Rewrite using `[hinf v]`.

Simplify using `only [rv]`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hPP, Matrix.mul_one, ← Matrix.mulVec_mulVec]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Establish `h3` using `RingHom.map_mulVec (X.B.I.φ v) (M' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) x i`.

Rewrite `h3` using `[hfix]`. Conclude with `h3.symm`. Use `⟨⟨γ.2, hγ2⟩, ⟨⟨γ, Subgroup.mem_inf.2 ⟨⟨M', hM', hinf, hfin⟩, Subgroup.mem_prod.2 ⟨hγ1, hγ2⟩⟩⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `htf`.
-/
theorem map_iotaF {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (hGF : AdBridgeGF X.B.I) :
    (PoincareSetting.iotaF X u).range.map (hE X hb u).toMonoidHom = GamHA X u := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, ⟨γ, rfl⟩, rfl⟩
    obtain ⟨M, hM, -, hf⟩ := (Subgroup.mem_inf.1 γ.2).1
    show (HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (tf X.B.I hb (γ : X.B.I.GA).2) : GL (Fin X.B.I.n) _) ∈
      HFin (Af X.B.I.F) X.B.I.cm.sig X.B.I.J
    refine ⟨M, hM, ?_⟩
    apply Units.ext
    show (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (F := X.B.I.F) (Af X.B.I.F)) = _
    rw [Bridge_mat, hf, Matrix.map_map]
    congr 1
  · intro hy
    have hy' : (HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (y : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) :
        GL (Fin X.B.I.n) _) ∈ HFin (Af X.B.I.F) X.B.I.cm.sig X.B.I.J := hy
    obtain ⟨M, hM, hMy⟩ := Subgroup.mem_map.1 hy'
    let Hf : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J :=
      ⟨Formalism.UG.bc (inclR (F := X.B.I.F) (AF X.B.I.F)) M,
        Formalism.UG.P.bc_mem _ _ _ (inclR_comp_sig (AF X.B.I.F) X.B.I.cm.sig) _ M hM⟩
    have hrat : Hf ∈ ratHA X.B.I := ⟨M, hM, rfl⟩
    rw [← hGF (toHA X.B.I hb) (toHA_isBridge X.B.I hb)] at hrat
    obtain ⟨γ, hγ, hγe⟩ := hrat
    have htf : tf X.B.I hb γ.2 = (y : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := by
      apply Bridge_HA_ext
      rw [Bridge_mat, ← fin_mat X.B.I hb γ, hγe]
      rw [← hMy]
      show ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (F := X.B.I.F) (AF X.B.I.F))).map
        (tensMap (E := X.B.I.E) (sndA X.B.I.F)) = (M : Matrix _ _ _).map (inclR (F := X.B.I.F) (Af X.B.I.F))
      rw [Matrix.map_map]
      congr 1
    have hγ2 : γ.2 ∈ PoincareSetting.Hfin X u := (mem_Hfin_iff X hb u γ.2).2 (htf ▸ y.2)
    obtain ⟨M', hM', hinf, hfin⟩ := hγ
    have hγ1 : γ.1 ∈ PoincareSetting.Hinf X u := by
      intro v x hx
      have hfix : (M' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x := by
        have h0 := hγ2 x hx
        rw [hfin] at h0
        funext i
        have := PIW.AdelClassFin.DictRing.nontrivial (F := X.B.I.F)
        apply Formalism.UG.P.inclE_injective X.B.I.F X.B.I.E (Af X.B.I.F)
        have h1 := congrFun h0 i
        have h2 := RingHom.map_mulVec (Formalism.UG.inclE (F := X.B.I.F) (E := X.B.I.E) (Af X.B.I.F))
          (M' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) x i
        exact h2.trans h1
      have hPP : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 :=
        Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v))
      rw [hinf v]
      simp only [rv]
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hPP, Matrix.mul_one, ← Matrix.mulVec_mulVec]
      congr 1
      funext i
      have h3 := RingHom.map_mulVec (X.B.I.φ v) (M' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) x i
      rw [hfix] at h3
      exact h3.symm
    refine ⟨⟨γ.2, hγ2⟩, ⟨⟨γ, Subgroup.mem_inf.2 ⟨⟨M', hM', hinf, hfin⟩, Subgroup.mem_prod.2 ⟨hγ1, hγ2⟩⟩⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    exact htf

/- English proof (translation)
Introduce `D X hb hK u hGF _hL`. Conclude with `card_dc_congr (hE X hb u) _ _ _ _ (map_iotaF X hb u hGF) (map_Ku X hb hK u)`.
-/
theorem class_sets_equal_card : ClassBijStep := by
  intro D X hb hK u hGF _hL
  exact card_dc_congr (hE X hb u) _ _ _ _ (map_iotaF X hb u hGF) (map_Ku X hb hK u)

/- English proof (translation)
Introduce `D X hb hK u hGF _hL hn x'`. Rewrite using `[eq_bot_iff]`. Introduce `y hy`. Take `⟨hy1, hy2⟩` from `Subgroup.mem_inf.1 hy`. Rewrite `hy1` using `[← map_iotaF X hb u hGF]`.

Take `⟨h, ⟨γ, rfl⟩, rfl⟩` from `Subgroup.mem_map.1 hy1`. Take `⟨k', hk', hke⟩` from `Subgroup.mem_map.1 hy2`. Rewrite `hk'` using `[← map_Ku X hb hK u]`. Take `⟨k, hk, rfl⟩` from `Subgroup.mem_map.1 hk'`. Take `⟨x, rfl⟩` from `(hE X hb u).surjective x'`.

Establish `e : PoincareSetting.iotaF X u γ = x * k * x⁻¹`. Apply `(hE X hb u).injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, map_inv]`. Conclude with `hke.symm`. Establish `h1 : x⁻¹ * PoincareSetting.iotaF X u γ * x ∈ PoincareSetting.Ku X u hK`.

Rewrite using `[e]`. Simplify `hk` using `[mul_assoc]`. Establish `h2` using `hn x γ h1`. Rewrite using `[Subgroup.mem_bot, h2]`. Simplify using the standard rewrite rules.
-/
theorem stabilizers_trivial_of_neat : HAStabTrivStep := by
  intro D X hb hK u hGF _hL hn x'
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
  rw [← map_iotaF X hb u hGF] at hy1
  obtain ⟨h, ⟨γ, rfl⟩, rfl⟩ := Subgroup.mem_map.1 hy1
  obtain ⟨k', hk', hke⟩ := Subgroup.mem_map.1 hy2
  rw [← map_Ku X hb hK u] at hk'
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hk'
  obtain ⟨x, rfl⟩ := (hE X hb u).surjective x'
  have e : PoincareSetting.iotaF X u γ = x * k * x⁻¹ := by
    apply (hE X hb u).injective
    rw [map_mul, map_mul, map_inv]
    exact hke.symm
  have h1 : x⁻¹ * PoincareSetting.iotaF X u γ * x ∈ PoincareSetting.Ku X u hK := by
    rw [e]
    simpa [mul_assoc] using hk
  have h2 := hn x γ h1
  rw [Subgroup.mem_bot, h2]
  simp

end PIW.MassDataColumns
