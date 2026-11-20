import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DownLift.ReadAdj

open GlobalTheory.AdelicLatMove

variable {D : D7}

/- English proof (translation)
Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, RingHom.map_zero _⟩`. Consider the case `add x y hx hy`. Take `⟨a, rfl⟩` from `hx`.

Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a + b, RingHom.map_add _ _ _⟩`. Consider the case `tmul x a => exact ⟨pairA D.host.F 0 a ⊗ₜ[D.host.F] x, rfl⟩`.
-/
theorem toEAf_onto : Function.Surjective (toEAf D) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩
  | tmul x a => exact ⟨pairA D.host.F 0 a ⊗ₜ[D.host.F] x, rfl⟩

/- English proof (translation)
Take `⟨a, rfl⟩` from `toEAf_onto z`. Conclude with `GlobalTheory.PlaceVec.cF_cF_toEAf a`.
-/
theorem cF_cF (z : Formalism.IndefR.Datum.EAf D) : cF D (cF D z) = z := by
  obtain ⟨a, rfl⟩ := toEAf_onto z
  exact GlobalTheory.PlaceVec.cF_cF_toEAf a

/- English proof (translation)
Rewrite using `[GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.PlaceVec.frMapAdj_eq]`. Establish `: (((a • x : WO S T).map (toEAf D)).map (cF D))ᵀ = toEAf D (cA D a) • ((x.map (toEAf D)).map (cF D))ᵀ` using `Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul, toEAf_cA]`. Rewrite using `[this, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem frMapAdj_smul_eq (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) (a : AE D)
    (x : WO S T) : frMapAdj S T βS βT (a • x) = toEAf D (cA D a) • frMapAdj S T βS βT x := by
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.PlaceVec.frMapAdj_eq]
  have : (((a • x : WO S T).map (toEAf D)).map (cF D))ᵀ = toEAf D (cA D a) • ((x.map (toEAf D)).map (cF D))ᵀ :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul, toEAf_cA]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Use `conv_rhs => rw [← (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hx]`. Rewrite using `[frMapAdj_smul_eq, GlobalTheory.DualPairCheck.cA_cA]`.
-/
theorem frMapAdj_half (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) {e : AE D}
    {x : WO S T} (hx : IsHalf (cA D e) x) : toEAf D e • frMapAdj S T βS βT x = frMapAdj S T βS βT x := by
  conv_rhs => rw [← (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hx]
  rw [frMapAdj_smul_eq, GlobalTheory.DualPairCheck.cA_cA]

/- English proof (translation)
Establish `h` using `GlobalTheory.PlaceVec.frMapAdj_add S T βS βT (x - y) y`. Rewrite `h` using `[sub_add_cancel]`. Rewrite using `[h, add_sub_cancel_right]`.
-/
theorem frMapAdj_sub (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) (x y : WO S T) :
    frMapAdj S T βS βT (x - y) = frMapAdj S T βS βT x - frMapAdj S T βS βT y := by
  have h := GlobalTheory.PlaceVec.frMapAdj_add S T βS βT (x - y) y
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

/- English proof (translation)
Establish `h1` using `congrArg (fun N => (S.gram.map (eToEAf D) * βS.val) * N * ((βT⁻¹).val * (T.gram⁻¹).map (eToEAf D))) h`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul] at h1`. Rewrite `h1` using `[GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.PlaceVec.sandwich_cancel _ _ _ _ _ _ _ _ _ βS.mul_inv (GlobalTheory.PlaceVec.gram_map_mul_inv S) βT.mul_inv (GlobalTheory.PlaceVec.gram_map_mul_inv T)]`. Use extensionality with `i j`. Establish `h2` using `congrFun (congrFun h1 j) i`.

Simplify using `only [Matrix.transpose_apply, Matrix.map_apply, Matrix.zero_apply] at h2`. Establish `h3` using `congrArg (cF D) h2`. Rewrite `h3` using `[cF_cF, map_zero]`. Simplify using `using h3`.
-/
theorem frMapAdj_eq_zero (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) {x : WO S T}
    (h : frMapAdj S T βS βT x = 0) : x.map (toEAf D) = 0 := by
  have h1 := congrArg (fun N => (S.gram.map (eToEAf D) * βS.val) * N * ((βT⁻¹).val * (T.gram⁻¹).map (eToEAf D))) h
  simp only [Matrix.mul_zero, Matrix.zero_mul] at h1
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.PlaceVec.sandwich_cancel _ _ _ _ _ _ _ _ _ βS.mul_inv
    (GlobalTheory.PlaceVec.gram_map_mul_inv S) βT.mul_inv (GlobalTheory.PlaceVec.gram_map_mul_inv T)] at h1
  ext i j
  have h2 := congrFun (congrFun h1 j) i
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.zero_apply] at h2
  have h3 := congrArg (cF D) h2
  rw [cF_cF, map_zero] at h3
  simpa using h3

/- English proof (translation)
Establish `h : toEAf D e * (toEAf D e - 1) = 0`. Rewrite using `[mul_sub, mul_one, ← map_mul, he, sub_self]`. Use `(hker _).2 h` as an intermediate fact. Rewrite `this` using `[map_sub, map_one, sub_eq_zero]`. Conclude with `this`.
-/
theorem phi_toEAf_idem {e : AE D} (he : e * e = e) {F : Type} [CommRing F] (φ : Formalism.IndefR.Datum.EAf D →+* F)
    (hker : ∀ z, φ z = 0 ↔ toEAf D e * z = 0) : φ (toEAf D e) = 1 := by
  have h : toEAf D e * (toEAf D e - 1) = 0 := by
    rw [mul_sub, mul_one, ← map_mul, he, sub_self]
  have := (hker _).2 h
  rw [map_sub, map_one, sub_eq_zero] at this
  exact this

/- English proof (translation)
The claim follows from `(Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective (by rw [map_zero]; exact h)`.
-/
theorem finPart_eq_zero_of_toEAf {a : AE D} (h : toEAf D a = 0) : finPart D a = 0 :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective (by rw [map_zero]; exact h)

/- English proof (translation)
The claim follows from `mul_eq_one_comm.1 (GlobalTheory.PlaceVec.gram_map_mul_inv S)`.
-/
theorem gram_inv_map_mul (S : HSp D) : (S.gram⁻¹).map (eToEAf D) * S.gram.map (eToEAf D) = 1 :=
  mul_eq_one_comm.1 (GlobalTheory.PlaceVec.gram_map_mul_inv S)

/- English proof (translation)
Introduce `D S T βS βT e PP v φ ι hI hL`. Take `⟨hsurj, hker, hint, hred⟩` from `hL`. Establish `hs : IsSplitIdem D e` using `hI.1`. Establish `hc : IsSplitIdem D (cA D e)` using `GlobalTheory.SplitScalar.isSplitIdem_conj hs`. Establish `h1 : φ (toEAf D e) = 1` using `phi_toEAf_idem hs.1 φ hker`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `m choose N hN using fun i j => hsurj (m i j) set Q : Matrix (Fin S.rank) (Fin T.rank) (Formalism.IndefR.Datum.EAf D) := (S.gram.map (eToEAf D) * βS.val) * Matrix.of N * ((βT⁻¹).val * (T.gram⁻¹).map (eToEAf D)) with hQ choose w hw using fun (i : Fin T.rank) (j : Fin S.rank) => toE …`. Establish `hfx : frMapAdj S T βS βT x' = Matrix.of N`. Rewrite using `[GlobalTheory.PlaceVec.frMapAdj_eq]`. Establish `hX : ((x'.map (toEAf D)).map (cF D))ᵀ = Q`.

Use extensionality with `i j`. Simplify using `only [Matrix.transpose_apply, Matrix.map_apply, hx', Matrix.of_apply, toEAf_cA, cF_cF, hw]`. Rewrite using `[hX, hQ]`. Conclude with `GlobalTheory.PlaceVec.sandwich_cancel _ _ _ _ _ _ _ _ _ (gram_inv_map_mul S) βS.inv_mul (gram_inv_map_mul T) βT.inv_mul`. Use `⟨cA D e • x', fun i j => ?_, ?_⟩` and prove the remaining obligations.

Use `show cA D e * (cA D e * x' i j) = cA D e * x' i j`. Rewrite using `[← mul_assoc, hc.1]`. Use extensionality with `i j`. Simplify using `only [rdAdj, Matrix.map_apply, frMapAdj_smul_eq, GlobalTheory.DualPairCheck.cA_cA, hfx, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.of_apply, hN]`. Rewrite using `[show φ (toEAf D e) = 1 from h1, one_mul]`.

Introduce `x x' hx hx' h`. Establish `hd : IsHalf (cA D e) (x - x')` using `fun i j => by show cA D e * (x i j - x' i j) = x i j - x' i j`. Rewrite using `[mul_sub, hx i j, hx' i j]`. Establish `h0 : frMapAdj S T βS βT (x - x') = 0`. Use extensionality with `i j`.

Establish `e1` using `congrFun (congrFun h i) j`. Simplify using `only [rdAdj, Matrix.map_apply] at e1`. Establish `e2 : φ (frMapAdj S T βS βT (x - x') i j) = 0`. Rewrite using `[frMapAdj_sub, Matrix.sub_apply, map_sub, e1, sub_self]`. Establish `e3` using `(hker _).1 e2`.

Establish `e4` using `congrFun (congrFun (frMapAdj_half S T βS βT hd) i) j`. Rewrite `e4` using `[Matrix.smul_apply, smul_eq_mul, e3]`. Rewrite using `[← e4, Matrix.zero_apply]`. Establish `hf` using `frMapAdj_eq_zero S T βS βT h0`. Establish `hinf` using `GlobalTheory.SplitScalar.half_fin hc hd`.

Use extensionality with `i j`. Use `sub_eq_zero.1 (GlobalTheory.SplitScalar.adele_ext ?_ ?_)` and prove the remaining obligations. Use `congrFun (congrFun hinf i) j` as an intermediate fact. Rewrite using `[map_zero]`. Conclude with `this`.

Rewrite using `[map_zero]`. Conclude with `finPart_eq_zero_of_toEAf (congrFun (congrFun hf i) j)`. Introduce `x hx`. Establish `hh` using `fun i j => congrFun (congrFun (frMapAdj_half S T βS βT hx) i) j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul] at hh`.

Prove the components needed by the constructor for the conclusion. Introduce `hI'`. Use `⟨Matrix.of fun i j => ⟨φ (frMapAdj S T βS βT x i j), (hint _).1 (by rw [hh i j]; exact hI' i j)⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Both sides reduce to the same expression.

Introduce and unpack `⟨z, hz⟩ i j`. Establish `e1` using `congrFun (congrFun hz i) j`. Simplify using `only [rdAdj, Matrix.map_apply] at e1`. Establish `e2 : φ (frMapAdj S T βS βT x i j) ∈ v.adicCompletionIntegers D.host.F`. Rewrite using `[e1]`.

Conclude with `(z i j).2`. Rewrite using `[← hh i j]`. Conclude with `(hint _).2 e2`. Introduce `x z hI' hz`. Use extensionality with `i j`.

Establish `e1` using `congrFun (congrFun hz i) j`. Simplify using `only [rdAdj, Matrix.map_apply] at e1`. Simplify using `only [Matrix.map_apply, redM, dif_pos (hI' i j)]`. Conclude with `hred ⟨_, hI' i j⟩ (z i j) e1.symm`.
-/
theorem rdAdj_read : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D))
    (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F))
    (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)),
    Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι →
    (∀ m, ∃ x : WO S T, IsHalf (cA D e) x ∧ rdAdj S T βS βT φ x = m) ∧
    (∀ x x' : WO S T, IsHalf (cA D e) x → IsHalf (cA D e) x' → rdAdj S T βS βT φ x = rdAdj S T βS βT φ x' → x = x') ∧
    (∀ x : WO S T, IsHalf (cA D e) x → (IsIntM (frMapAdj S T βS βT x) ↔
      ∃ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v),
        rdAdj S T βS βT φ x = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))) ∧
    ∀ (x : WO S T) (z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v)), IsIntM (frMapAdj S T βS βT x) →
      rdAdj S T βS βT φ x = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) →
      (redM PP (frMapAdj S T βS βT x)).map ι = z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)) := by
  intro D S T βS βT e PP v φ ι hI hL
  obtain ⟨hsurj, hker, hint, hred⟩ := hL
  have hs : IsSplitIdem D e := hI.1
  have hc : IsSplitIdem D (cA D e) := GlobalTheory.SplitScalar.isSplitIdem_conj hs
  have h1 : φ (toEAf D e) = 1 := phi_toEAf_idem hs.1 φ hker
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m
    choose N hN using fun i j => hsurj (m i j)
    set Q : Matrix (Fin S.rank) (Fin T.rank) (Formalism.IndefR.Datum.EAf D) :=
      (S.gram.map (eToEAf D) * βS.val) * Matrix.of N * ((βT⁻¹).val * (T.gram⁻¹).map (eToEAf D)) with hQ
    choose w hw using fun (i : Fin T.rank) (j : Fin S.rank) => toEAf_onto (Q j i)
    set x' : WO S T := Matrix.of fun i j => cA D (w i j) with hx'
    have hfx : frMapAdj S T βS βT x' = Matrix.of N := by
      rw [GlobalTheory.PlaceVec.frMapAdj_eq]
      have hX : ((x'.map (toEAf D)).map (cF D))ᵀ = Q := by
        ext i j
        simp only [Matrix.transpose_apply, Matrix.map_apply, hx', Matrix.of_apply, toEAf_cA, cF_cF, hw]
      rw [hX, hQ]
      exact GlobalTheory.PlaceVec.sandwich_cancel _ _ _ _ _ _ _ _ _ (gram_inv_map_mul S) βS.inv_mul (gram_inv_map_mul T)
        βT.inv_mul
    refine ⟨cA D e • x', fun i j => ?_, ?_⟩
    · show cA D e * (cA D e * x' i j) = cA D e * x' i j
      rw [← mul_assoc, hc.1]
    · ext i j
      simp only [rdAdj, Matrix.map_apply, frMapAdj_smul_eq, GlobalTheory.DualPairCheck.cA_cA, hfx, Matrix.smul_apply,
        smul_eq_mul, map_mul, Matrix.of_apply, hN]
      rw [show φ (toEAf D e) = 1 from h1, one_mul]
  · intro x x' hx hx' h
    have hd : IsHalf (cA D e) (x - x') := fun i j => by
      show cA D e * (x i j - x' i j) = x i j - x' i j
      rw [mul_sub, hx i j, hx' i j]
    have h0 : frMapAdj S T βS βT (x - x') = 0 := by
      ext i j
      have e1 := congrFun (congrFun h i) j
      simp only [rdAdj, Matrix.map_apply] at e1
      have e2 : φ (frMapAdj S T βS βT (x - x') i j) = 0 := by
        rw [frMapAdj_sub, Matrix.sub_apply, map_sub, e1, sub_self]
      have e3 := (hker _).1 e2
      have e4 := congrFun (congrFun (frMapAdj_half S T βS βT hd) i) j
      rw [Matrix.smul_apply, smul_eq_mul, e3] at e4
      rw [← e4, Matrix.zero_apply]
    have hf := frMapAdj_eq_zero S T βS βT h0
    have hinf := GlobalTheory.SplitScalar.half_fin hc hd
    ext i j
    refine sub_eq_zero.1 (GlobalTheory.SplitScalar.adele_ext ?_ ?_)
    · have := congrFun (congrFun hinf i) j
      rw [map_zero]; exact this
    · rw [map_zero]
      exact finPart_eq_zero_of_toEAf (congrFun (congrFun hf i) j)
  · intro x hx
    have hh := fun i j => congrFun (congrFun (frMapAdj_half S T βS βT hx) i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hh
    constructor
    · intro hI'
      refine ⟨Matrix.of fun i j => ⟨φ (frMapAdj S T βS βT x i j), (hint _).1 (by rw [hh i j]; exact hI' i j)⟩, ?_⟩
      ext i j
      rfl
    · rintro ⟨z, hz⟩ i j
      have e1 := congrFun (congrFun hz i) j
      simp only [rdAdj, Matrix.map_apply] at e1
      have e2 : φ (frMapAdj S T βS βT x i j) ∈ v.adicCompletionIntegers D.host.F := by
        rw [e1]; exact (z i j).2
      rw [← hh i j]
      exact (hint _).2 e2
  · intro x z hI' hz
    ext i j
    have e1 := congrFun (congrFun hz i) j
    simp only [rdAdj, Matrix.map_apply] at e1
    simp only [Matrix.map_apply, redM, dif_pos (hI' i j)]
    exact hred ⟨_, hI' i j⟩ (z i j) e1.symm

end GlobalTheory.DownLift.ReadAdj

end
