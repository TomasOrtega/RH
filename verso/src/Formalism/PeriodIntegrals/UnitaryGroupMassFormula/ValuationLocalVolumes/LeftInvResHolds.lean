import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LeftInvResGen

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

/- English proof (translation)
Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin Mb) (LinearMap.ker_eq_bot.2 h)`. Use `⟨LinearMap.toMatrix' g, ?_⟩` and prove the remaining obligations. Establish `: LinearMap.toMatrix' g * LinearMap.toMatrix' (Matrix.mulVecLin Mb) = 1`. Rewrite using `[← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]`. Establish `hMb : LinearMap.toMatrix' (Matrix.mulVecLin Mb) = Mb`.

Rewrite using `[← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']`. Rewrite `this` using `[hMb]`. Then use the resulting hypothesis.
-/
theorem linv_field {K : Type} [Field K] {n a : ℕ} (Mb : Matrix (Fin n) (Fin a) K)
    (h : Function.Injective Mb.mulVec) : ∃ Nb : Matrix (Fin a) (Fin n) K, Nb * Mb = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin Mb) (LinearMap.ker_eq_bot.2 h)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have : LinearMap.toMatrix' g * LinearMap.toMatrix' (Matrix.mulVecLin Mb) = 1 := by
    rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  have hMb : LinearMap.toMatrix' (Matrix.mulVecLin Mb) = Mb := by
    rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  rwa [hMb] at this

/- English proof (translation)
Establish `hfst : ∀ c : Fin a → k × k, ∀ r, ((Mb.mulVec c) r).1 = ((Mb.map (RingHom.fst k k)).mulVec (fun i => (c i).1)) r` using `fun c r => RingHom.map_mulVec (RingHom.fst k k) Mb c r`. Establish `hsnd : ∀ c : Fin a → k × k, ∀ r, ((Mb.mulVec c) r).2 = ((Mb.map (RingHom.snd k k)).mulVec (fun i => (c i).2)) r` using `fun c r => RingHom.map_mulVec (RingHom.snd k k) Mb c r`. Establish `h1 : Function.Injective (Mb.map (RingHom.fst k k)).mulVec`. Introduce `x y hxy`. Establish `: Mb.mulVec (fun i => (x i, 0)) = Mb.mulVec (fun i => (y i, 0))`.

Use function extensionality and compare the values at `r`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Rewrite using `[hfst, hfst]`. Conclude with `congrFun hxy r`. Rewrite using `[hsnd, hsnd]`.

Use `h this` as an intermediate fact. Use function extensionality and compare the values at `i`. Conclude with `congrArg Prod.fst (congrFun this i)`. Establish `h2 : Function.Injective (Mb.map (RingHom.snd k k)).mulVec`. Introduce `x y hxy`.

Establish `: Mb.mulVec (fun i => (0, x i)) = Mb.mulVec (fun i => (0, y i))`. Use function extensionality and compare the values at `r`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Rewrite using `[hfst, hfst]`. Rewrite using `[hsnd, hsnd]`.

Conclude with `congrFun hxy r`. Use `h this` as an intermediate fact. Use function extensionality and compare the values at `i`. Conclude with `congrArg Prod.snd (congrFun this i)`. Take `⟨N1, hN1⟩` from `linv_field _ h1`.

Take `⟨N2, hN2⟩` from `linv_field _ h2`. Use `set Nb : Matrix (Fin a) (Fin n) (k × k) := Matrix.of fun i r => (N1 i r, N2 i r) with hNbd`. Use `⟨Nb, ?_⟩` and prove the remaining obligations. Establish `e1 : (Nb * Mb).map (RingHom.fst k k) = 1`. Rewrite using `[Matrix.map_mul]`.

Establish `: Nb.map (RingHom.fst k k) = N1` using `by ext i r; rfl`. Rewrite using `[this]`. Conclude with `hN1`. Establish `e2 : (Nb * Mb).map (RingHom.snd k k) = 1`. Rewrite using `[Matrix.map_mul]`.

Establish `: Nb.map (RingHom.snd k k) = N2` using `by ext i r; rfl`. Rewrite using `[this]`. Conclude with `hN2`. Use extensionality with `i j`. Use `congrFun (congrFun e1 i) j` as an intermediate fact.

Simplify using `only [Matrix.map_apply, RingHom.coe_fst] at this`. Rewrite using `[this, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> rfl`. Use `congrFun (congrFun e2 i) j` as an intermediate fact. Simplify using `only [Matrix.map_apply, RingHom.coe_snd] at this`.

Rewrite using `[this, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem linv_prod {k : Type} [Field k] {n a : ℕ} (Mb : Matrix (Fin n) (Fin a) (k × k))
    (h : Function.Injective Mb.mulVec) : ∃ Nb : Matrix (Fin a) (Fin n) (k × k), Nb * Mb = 1 := by
  have hfst : ∀ c : Fin a → k × k, ∀ r, ((Mb.mulVec c) r).1 = ((Mb.map (RingHom.fst k k)).mulVec (fun i => (c i).1)) r :=
    fun c r => RingHom.map_mulVec (RingHom.fst k k) Mb c r
  have hsnd : ∀ c : Fin a → k × k, ∀ r, ((Mb.mulVec c) r).2 = ((Mb.map (RingHom.snd k k)).mulVec (fun i => (c i).2)) r :=
    fun c r => RingHom.map_mulVec (RingHom.snd k k) Mb c r
  have h1 : Function.Injective (Mb.map (RingHom.fst k k)).mulVec := by
    intro x y hxy
    have : Mb.mulVec (fun i => (x i, 0)) = Mb.mulVec (fun i => (y i, 0)) := by
      funext r
      refine Prod.ext ?_ ?_
      · rw [hfst, hfst]; exact congrFun hxy r
      · rw [hsnd, hsnd]
    have := h this
    funext i
    exact congrArg Prod.fst (congrFun this i)
  have h2 : Function.Injective (Mb.map (RingHom.snd k k)).mulVec := by
    intro x y hxy
    have : Mb.mulVec (fun i => (0, x i)) = Mb.mulVec (fun i => (0, y i)) := by
      funext r
      refine Prod.ext ?_ ?_
      · rw [hfst, hfst]
      · rw [hsnd, hsnd]; exact congrFun hxy r
    have := h this
    funext i
    exact congrArg Prod.snd (congrFun this i)
  obtain ⟨N1, hN1⟩ := linv_field _ h1
  obtain ⟨N2, hN2⟩ := linv_field _ h2
  set Nb : Matrix (Fin a) (Fin n) (k × k) := Matrix.of fun i r => (N1 i r, N2 i r) with hNbd
  refine ⟨Nb, ?_⟩
  have e1 : (Nb * Mb).map (RingHom.fst k k) = 1 := by
    rw [Matrix.map_mul]
    have : Nb.map (RingHom.fst k k) = N1 := by ext i r; rfl
    rw [this]; exact hN1
  have e2 : (Nb * Mb).map (RingHom.snd k k) = 1 := by
    rw [Matrix.map_mul]
    have : Nb.map (RingHom.snd k k) = N2 := by ext i r; rfl
    rw [this]; exact hN2
  ext i j
  · have := congrFun (congrFun e1 i) j
    simp only [Matrix.map_apply, RingHom.coe_fst] at this
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  · have := congrFun (congrFun e2 i) j
    simp only [Matrix.map_apply, RingHom.coe_snd] at this
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Introduce `hS hUn ϖ hϖ M hM hsat`. Establish `hR : Red.ResAlg σ J ψ v` using `Red.resAlg_of_sp σ J ψ v (Red.etaSp_holds σ J ψ v)`. Take `⟨k, _, _, -, h⟩` from `hR hS hUn ϖ hϖ`. Break down `h with ⟨-, K, _, _, σ', π, -, -, -, hres⟩ | ⟨-, π, hres⟩` into its components or cases. Conclude with `leftInvRes_gen v ϖ hϖ π hres.1 hres.2.1 (fun Mb h => linv_field Mb h) M hM hsat`.

Conclude with `leftInvRes_gen v ϖ hϖ π hres.1 hres.2.1 (fun Mb h => linv_prod Mb h) M hM hsat`.
-/
theorem leftInvRes_holds (a : ℕ) : LeftInvRes σ J ψ v (n := n) a := by
  intro hS hUn ϖ hϖ M hM hsat
  have hR : Red.ResAlg σ J ψ v := Red.resAlg_of_sp σ J ψ v (Red.etaSp_holds σ J ψ v)
  obtain ⟨k, _, _, -, h⟩ := hR hS hUn ϖ hϖ
  rcases h with ⟨-, K, _, _, σ', π, -, -, -, hres⟩ | ⟨-, π, hres⟩
  · exact leftInvRes_gen v ϖ hϖ π hres.1 hres.2.1 (fun Mb h => linv_field Mb h) M hM hsat
  · exact leftInvRes_gen v ϖ hϖ π hres.1 hres.2.1 (fun Mb h => linv_prod Mb h) M hM hsat

/- English proof (translation)
The claim follows from `leftInvO_of σ J ψ v a (leftInvRes_holds σ J ψ v a)`.
-/
theorem leftInvO_holds (a : ℕ) : LeftInvO σ J ψ v (n := n) a :=
  leftInvO_of σ J ψ v a (leftInvRes_holds σ J ψ v a)

end Gen

section Loc

open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

/- English proof (translation)
The claim follows from `omVBadT_of_isoW X u' ψ hStd hLat hGram hIso (fun v => leftInvO_holds _ _ _ v _) hRed hFI hFS`.
-/
theorem omVBadT_of_last (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hIso : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      IsoW X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hRed : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      RedP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hFI : FFInertB) (hFS : FFSplitB) :
    OmVBadT X u' ψ :=
  omVBadT_of_isoW X u' ψ hStd hLat hGram hIso (fun v => leftInvO_holds _ _ _ v _) hRed hFI hFS

/- English proof (translation)
The claim follows from `omVBadT_of_last X u' ψ hStd hLat hGram hIso hRed hFI hFS`.
-/
theorem omVBadT_of_lastX (hStd : Formalism.L2.SG.Pf.NcX.OmVSt.OmVStd X ψ) (hLat : Formalism.L2.SG.Pf.NcX.OmVSt.OmVLat X)
    (hGram : Formalism.L2.SG.Pf.NcX.OmVSt.OmVGram X u')
    (hIso : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      IsoW X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hRed : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      RedP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hFI : FFInertB) (hFS : FFSplitB) :
    Formalism.L2.SG.Pf.NcX.OmVSt.OmVBadT X u' ψ :=
  omVBadT_of_last X u' ψ hStd hLat hGram hIso hRed hFI hFS

end Loc

end PI.OmVd
