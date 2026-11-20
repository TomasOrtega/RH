import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KchainSt

noncomputable section

open Matrix Finset
open scoped ContDiff ComplexConjugate ComplexOrder

namespace PositivityTheory.RgBcC.LfSt.Kchain.KcInv

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}

/- English proof (translation)
The claim follows from `contDiff_apply_apply ℝ ℂ a b`.
-/
theorem entry_contDiff (a b : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y a b) :=
  contDiff_apply_apply ℝ ℂ a b

/- English proof (translation)
Establish `: ContDiffOn ℝ ∞ (fun x => (F x : Fin n → Fin n → ℂ)) s` using `contDiffOn_pi.2 fun a => contDiffOn_pi.2 fun b => h a b`. Conclude with `this`.
-/
theorem mat_contDiffOn {F : E → Mat n} (h : ∀ a b, ContDiffOn ℝ ∞ (fun x => F x a b) s) :
    ContDiffOn ℝ ∞ F s := by
  have : ContDiffOn ℝ ∞ (fun x => (F x : Fin n → Fin n → ℂ)) s :=
    contDiffOn_pi.2 fun a => contDiffOn_pi.2 fun b => h a b
  exact this

/- English proof (translation)
Rewrite using `[← contDiffOn_univ]`. Conclude with `mat_contDiffOn fun a b => (h a b).contDiffOn`.
-/
theorem mat_contDiff {F : E → Mat n} (h : ∀ a b, ContDiff ℝ ∞ (fun x => F x a b)) : ContDiff ℝ ∞ F := by
  rw [← contDiffOn_univ]
  exact mat_contDiffOn fun a b => (h a b).contDiffOn

/- English proof (translation)
The claim follows from `(entry_contDiff a b).comp_contDiffOn h`.
-/
theorem entry_of {F : E → Mat n} (h : ContDiffOn ℝ ∞ F s) (a b : Fin n) : ContDiffOn ℝ ∞ (fun x => F x a b) s :=
  (entry_contDiff a b).comp_contDiffOn h

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Conclude with `ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)`.
-/
theorem det_contDiffOn {F : E → Mat n} (h : ∀ a b, ContDiffOn ℝ ∞ (fun x => F x a b) s) :
    ContDiffOn ℝ ∞ (fun x => (F x).det) s := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

/- English proof (translation)
Rewrite using `[← contDiffOn_univ]`. Conclude with `det_contDiffOn fun a b => (entry_contDiff a b).contDiffOn`.
-/
theorem det_contDiff : ContDiff ℝ ∞ (fun y : Mat n => y.det) := by
  rw [← contDiffOn_univ]
  exact det_contDiffOn fun a b => (entry_contDiff a b).contDiffOn

/- English proof (translation)
Use `mat_contDiffOn fun a b => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply]`. Conclude with `ContDiffOn.sum fun c _ => (entry_of hF a c).mul (entry_of hH c b)`.
-/
theorem mul_contDiffOn {F H : E → Mat n} (hF : ContDiffOn ℝ ∞ F s) (hH : ContDiffOn ℝ ∞ H s) :
    ContDiffOn ℝ ∞ (fun x => F x * H x) s := by
  refine mat_contDiffOn fun a b => ?_
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun c _ => (entry_of hF a c).mul (entry_of hH c b)

/- English proof (translation)
The claim follows from `isOpen_ne.preimage (continuous_id.matrix_det (n := Fin n) (R := ℂ))`.
-/
theorem isOpen_GLs' : IsOpen (GLs n) :=
  isOpen_ne.preimage (continuous_id.matrix_det (n := Fin n) (R := ℂ))

/- English proof (translation)
Use `mat_contDiffOn fun a b => ?_` and prove the remaining obligations. Establish `hd : ContDiffOn ℝ ∞ (fun y : Mat n => y.det) (GLs n)` using `det_contDiff.contDiffOn`. Establish `hadj : ContDiffOn ℝ ∞ (fun y : Mat n => y.adjugate a b) (GLs n)`. Simplify using `only [Matrix.adjugate_apply]`. Use `det_contDiffOn fun i j => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.updateRow_apply]`. Use `split_ifs`. Conclude with `contDiffOn_const`. Conclude with `(entry_contDiff _ _).contDiffOn`. Establish `: ContDiffOn ℝ ∞ (fun y : Mat n => (y.det)⁻¹ * y.adjugate a b) (GLs n)` using `(hd.inv fun y hy => hy).mul hadj`.

Use `this.congr fun y _ => ?_` and prove the remaining obligations. Simplify using `[Matrix.inv_def, Ring.inverse_eq_inv]`.
-/
theorem inv_contDiffOn : ContDiffOn ℝ ∞ (fun y : Mat n => y⁻¹) (GLs n) := by
  refine mat_contDiffOn fun a b => ?_
  have hd : ContDiffOn ℝ ∞ (fun y : Mat n => y.det) (GLs n) := det_contDiff.contDiffOn
  have hadj : ContDiffOn ℝ ∞ (fun y : Mat n => y.adjugate a b) (GLs n) := by
    simp only [Matrix.adjugate_apply]
    refine det_contDiffOn fun i j => ?_
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact contDiffOn_const
    · exact (entry_contDiff _ _).contDiffOn
  have : ContDiffOn ℝ ∞ (fun y : Mat n => (y.det)⁻¹ * y.adjugate a b) (GLs n) :=
    (hd.inv fun y hy => hy).mul hadj
  refine this.congr fun y _ => ?_
  simp [Matrix.inv_def, Ring.inverse_eq_inv]

/- English proof (translation)
The claim follows from `mat_contDiff fun a b => by simp only [Matrix.conjTranspose_apply] exact Complex.conjCLE.contDiff.comp (entry_contDiff b a)`.
-/
theorem star_contDiff : ContDiff ℝ ∞ (fun y : Mat n => yᴴ) :=
  mat_contDiff fun a b => by
    simp only [Matrix.conjTranspose_apply]
    exact Complex.conjCLE.contDiff.comp (entry_contDiff b a)

/- English proof (translation)
Simplify using `only [GLs, Set.mem_ofPred_eq, Matrix.det_conjTranspose] at *`. Conclude with `(star_ne_zero).2 hy`.
-/
theorem conjT_mem {y : Mat n} (hy : y ∈ GLs n) : yᴴ ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_conjTranspose] at *
  exact (star_ne_zero).2 hy

/- English proof (translation)
Simplify using `only [GLs, Set.mem_ofPred_eq, Matrix.det_nonsing_inv] at *`. Rewrite using `[Ring.inverse_eq_inv]`. Conclude with `inv_ne_zero hy`.
-/
theorem inv_mem {y : Mat n} (hy : y ∈ GLs n) : y⁻¹ ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_nonsing_inv] at *
  rw [Ring.inverse_eq_inv]; exact inv_ne_zero hy

/- English proof (translation)
Simplify using `only [GLs, Set.mem_ofPred_eq, Matrix.det_mul] at *`. Conclude with `mul_ne_zero hx hy`.
-/
theorem mul_mem {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

/- English proof (translation)
Introduce `n`. Use `⟨isOpen_GLs', inv_contDiffOn, ?_, det_contDiff, star_contDiff⟩` and prove the remaining obligations. Conclude with `inv_contDiffOn.comp star_contDiff.contDiffOn fun y hy => conjT_mem hy`.
-/
theorem invSmooth : InvSmooth := by
  intro n
  refine ⟨isOpen_GLs', inv_contDiffOn, ?_, det_contDiff, star_contDiff⟩
  exact inv_contDiffOn.comp star_contDiff.contDiffOn fun y hy => conjT_mem hy

/- English proof (translation)
Introduce `n σ hσ v hv`. Establish `hpd : (hOf v).PosDef` using `hv`. Establish `hd : (hOf v).det ≠ 0` using `hpd.det_pos.ne'`. Use `⟨?_, hd⟩` and prove the remaining obligations. Establish `h1` using `congrArg Matrix.det (hσ v hv)`.

Rewrite `h1` using `[Matrix.det_mul]`. Introduce `h0`. Conclude with `hd (by rw [← h1, h0, zero_mul])`.
-/
theorem coneGL : ConeGL := by
  intro n σ hσ v hv
  have hpd : (hOf v).PosDef := hv
  have hd : (hOf v).det ≠ 0 := hpd.det_pos.ne'
  refine ⟨?_, hd⟩
  have h1 := congrArg Matrix.det (hσ v hv)
  rw [Matrix.det_mul] at h1
  intro h0
  exact hd (by rw [← h1, h0, zero_mul])

/- English proof (translation)
Unfold `hOf`. Use `ContDiff.sum fun p _ => ?_` and prove the remaining obligations. Conclude with `(Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ p)).smul contDiff_const`.
-/
theorem hOf_contDiff : ContDiff ℝ ∞ (fun v : Fin n × Fin n → ℝ => hOf v) := by
  unfold hOf
  refine ContDiff.sum fun p _ => ?_
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ p)).smul contDiff_const

/- English proof (translation)
Introduce `n V _ _ σ c Fr k Γ T d hd hσs hσ hFr hk`. Establish `hgl` using `coneGL n σ hσ`. Set `U` to `cone n ×ˢ cone n`. Establish `h1 : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => σ y.1) U` using `hσs.comp contDiff_fst.contDiffOn fun y hy => hy.1`. Establish `h2 : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => σ y.2) U` using `hσs.comp contDiff_snd.contDiffOn fun y hy => hy.2`.

Establish `m1 : ∀ y ∈ U, σ y.1 ∈ GLs n` using `fun y hy => (hgl y.1 hy.1).1`. Establish `m2 : ∀ y ∈ U, σ y.2 ∈ GLs n` using `fun y hy => (hgl y.2 hy.2).1`. Establish `hi1 : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ y.1)⁻¹) U` using `inv_contDiffOn.comp h1 m1`. Establish `hi2 : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ y.2)⁻¹) U` using `inv_contDiffOn.comp h2 m2`. Establish `hs2 : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ y.2)ᴴ⁻¹) U` using `inv_contDiffOn.comp (star_contDiff.comp_contDiffOn h2) fun y hy => conjT_mem (m2 y hy)`.

Establish `hw : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ y.1)⁻¹ * d * (σ y.2)ᴴ⁻¹) U` using `mul_contDiffOn (mul_contDiffOn hi1 contDiffOn_const) hs2`. Establish `hwm : ∀ y ∈ U, (σ y.1)⁻¹ * d * (σ y.2)ᴴ⁻¹ ∈ GLs n` using `fun y hy => mul_mem (mul_mem (inv_mem (m1 y hy)) hd) (inv_mem (conjT_mem (m2 y hy)))`. Establish `hK : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => Kf Fr k Γ T d (σ y.1) (σ y.2)) U`. Unfold `Kf`. Use `ContDiffOn.mul (ContDiffOn.mul (ContDiffOn.mul (ContDiffOn.mul (hFr.comp h1 m1) (hk.comp hw hwm)) contDiffOn_const) contDiffOn_const) (hFr.comp hi2 fun y hy => inv_mem (m2 y hy))` and prove the remaining obligations.

Establish `hW : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (c : ℂ) * ((hOf y.2).det ^ n)⁻¹) U`. Use `contDiffOn_const.mul (ContDiffOn.inv ?_ fun y hy => pow_ne_zero _ (hgl y.2 hy.2).2)` and prove the remaining obligations. Conclude with `((det_contDiff.comp hOf_contDiff).comp contDiff_snd).contDiffOn.pow n`. Conclude with `hW.smul hK`.
-/
theorem kcSmooth : KcSmooth := by
  intro n V _ _ σ c Fr k Γ T d hd hσs hσ hFr hk
  have hgl := coneGL n σ hσ
  let U := cone n ×ˢ cone n
  have h1 : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => σ y.1) U :=
    hσs.comp contDiff_fst.contDiffOn fun y hy => hy.1
  have h2 : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => σ y.2) U :=
    hσs.comp contDiff_snd.contDiffOn fun y hy => hy.2
  have m1 : ∀ y ∈ U, σ y.1 ∈ GLs n := fun y hy => (hgl y.1 hy.1).1
  have m2 : ∀ y ∈ U, σ y.2 ∈ GLs n := fun y hy => (hgl y.2 hy.2).1
  have hi1 : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ y.1)⁻¹) U :=
    inv_contDiffOn.comp h1 m1
  have hi2 : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ y.2)⁻¹) U :=
    inv_contDiffOn.comp h2 m2
  have hs2 : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ y.2)ᴴ⁻¹) U :=
    inv_contDiffOn.comp (star_contDiff.comp_contDiffOn h2) fun y hy => conjT_mem (m2 y hy)
  have hw : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) => (σ y.1)⁻¹ * d * (σ y.2)ᴴ⁻¹) U :=
    mul_contDiffOn (mul_contDiffOn hi1 contDiffOn_const) hs2
  have hwm : ∀ y ∈ U, (σ y.1)⁻¹ * d * (σ y.2)ᴴ⁻¹ ∈ GLs n := fun y hy =>
    mul_mem (mul_mem (inv_mem (m1 y hy)) hd) (inv_mem (conjT_mem (m2 y hy)))
  have hK : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) =>
      Kf Fr k Γ T d (σ y.1) (σ y.2)) U := by
    unfold Kf
    refine ContDiffOn.mul (ContDiffOn.mul (ContDiffOn.mul (ContDiffOn.mul (hFr.comp h1 m1) (hk.comp hw hwm))
      contDiffOn_const) contDiffOn_const) (hFr.comp hi2 fun y hy => inv_mem (m2 y hy))
  have hW : ContDiffOn ℝ ∞ (fun y : (Fin n × Fin n → ℝ) × (Fin n × Fin n → ℝ) =>
      (c : ℂ) * ((hOf y.2).det ^ n)⁻¹) U := by
    refine contDiffOn_const.mul (ContDiffOn.inv ?_ fun y hy => pow_ne_zero _ (hgl y.2 hy.2).2)
    exact ((det_contDiff.comp hOf_contDiff).comp contDiff_snd).contDiffOn.pow n
  exact hW.smul hK

end PositivityTheory.RgBcC.LfSt.Kchain.KcInv
