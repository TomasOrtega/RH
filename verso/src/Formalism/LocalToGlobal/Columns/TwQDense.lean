import Formalism.LocalToGlobal.Columns.TwQSpP

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.UG.P Formalism.L2.DIV

section Dense

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (φ : E →+* v.adicCompletion F)
  (hint : ∀ r : 𝓞 E, Valued.v (φ (algebraMap (𝓞 E) E r)) ≤ 1)
  (hPv : ∀ r : 𝓞 E, Valued.v (φ (algebraMap (𝓞 E) E r)) < 1 ↔ r ∈ P.asIdeal)
  (hF : ∀ x : F, φ (algebraMap F E x) = algebraMap F (v.adicCompletion F) x)
  (hvP : IsOver v P)

/- English proof (translation)
Take `⟨r, y, hy, e⟩` from `integral_adele_approximation_holds F D hD (afsplitI v x) (afsplitI_mem_intAd v _ hx)`. Use `⟨r, y v, hy v, ?_⟩` and prove the remaining obligations. Use `congrArg (fun z : Formalism.L2.Herm.Af F => z v) e` as an intermediate fact. Rewrite `this` using `[afsplitI_self]`. Conclude with `this`.
-/
theorem qsp_approx (D : 𝓞 F) (hD : D ≠ 0) (x : v.adicCompletion F) (hx : x ∈ v.adicCompletionIntegers F) :
    ∃ (r : 𝓞 F) (y : v.adicCompletion F), y ∈ v.adicCompletionIntegers F ∧
      x = algebraMap (𝓞 F) (v.adicCompletion F) r + algebraMap (𝓞 F) (v.adicCompletion F) D * y := by
  obtain ⟨r, y, hy, e⟩ := integral_adele_approximation_holds F D hD (afsplitI v x) (afsplitI_mem_intAd v _ hx)
  refine ⟨r, y v, hy v, ?_⟩
  have := congrArg (fun z : Formalism.L2.Herm.Af F => z v) e
  rw [afsplitI_self] at this
  exact this

/- English proof (translation)
Introduce `i _`. Establish `h : ∀ j, x j ∈ (1 : Submodule (𝓞 E) E)` using `fun j => hx j trivial`. Use `show (M.map (algebraMap (𝓞 F) E)).mulVec x i ∈ (1 : Submodule (𝓞 E) E)`. Rewrite using `[Matrix.mulVec, dotProduct]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Take `⟨a, ha⟩` from `Submodule.mem_one.1 (h j)`. Use `Submodule.mem_one.2 ⟨algebraMap (𝓞 F) (𝓞 E) (M i j) * a, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.map_apply, ← ha, map_mul, ← IsScalarTower.algebraMap_apply]`.
-/
theorem qsp_std_mulVec {M : Matrix (Fin n) (Fin n) (𝓞 F)} {x : Sp E n} (hx : x ∈ stdLat E n) :
    (M.map (algebraMap (𝓞 F) E)).mulVec x ∈ stdLat E n := by
  intro i _
  have h : ∀ j, x j ∈ (1 : Submodule (𝓞 E) E) := fun j => hx j trivial
  show (M.map (algebraMap (𝓞 F) E)).mulVec x i ∈ (1 : Submodule (𝓞 E) E)
  rw [Matrix.mulVec, dotProduct]
  refine Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h j)
  refine Submodule.mem_one.2 ⟨algebraMap (𝓞 F) (𝓞 E) (M i j) * a, ?_⟩
  rw [Matrix.map_apply, ← ha, map_mul, ← IsScalarTower.algebraMap_apply]

set_option maxHeartbeats 4000000 in
include hint hPv hF hvP in

/- English proof (translation)
Use `choose r y hy e using fun i j => qsp_approx D hD ((k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) (hk i j)`. Set `R : Matrix (Fin n) (Fin n) (𝓞 F)` to `fun i j => r i j`. Set `ME : Matrix (Fin n) (Fin n) E` to `R.map (algebraMap (𝓞 F) E)`. Set `O` to `v.adicCompletionIntegers F`. Establish `hDval : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) < 1`.

Rewrite using `[csApprox_val_int]`. Conclude with `(HeightOneSpectrum.intValuation_lt_one_iff_mem v D).2 hDv`. Set `kO : Matrix (Fin n) (Fin n) O` to `fun i j => ⟨_, hk i j⟩`. Set `kiO : Matrix (Fin n) (Fin n) O` to `fun i j => ⟨_, hk' i j⟩`. Set `RO : Matrix (Fin n) (Fin n) O` to `fun i j => ⟨_, glo_algMap_int v (r i j)⟩`.

Establish `hkk : kO * kiO = 1`. Establish `h1 : (O.subtype).mapMatrix (kO * kiO) = (O.subtype).mapMatrix 1`. Rewrite using `[map_mul, map_one]`. Use `show ((k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * ((k⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))) = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Conclude with `Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h1 i) j)`. Establish `hdetk : IsUnit kO.det` using `Matrix.isUnit_det_of_right_inverse hkk`. Establish `hres : (IsLocalRing.residue O).mapMatrix kO = (IsLocalRing.residue O).mapMatrix RO`. Use extensionality with `i j`. Use `show IsLocalRing.residue O (kO i j) = IsLocalRing.residue O (RO i j)`.

Rewrite using `[← sub_eq_zero, ← map_sub]`. Apply `glo_res_zero v` to reduce the goal to its premises. Use `show Valued.v ((k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j - algebraMap (𝓞 F) (v.adicCompletion F) (r i j)) < 1`. Rewrite using `[e i j, add_sub_cancel_left, map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hy i j))) hDval`.

Establish `hRO : IsLocalRing.residue O RO.det ≠ 0`. Rewrite using `[RingHom.map_det, ← hres, ← RingHom.map_det]`. Conclude with `(hdetk.map (IsLocalRing.residue O)).ne_zero`. Establish `hROval : ((RO.det : O) : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) R.det`. Establish `h1 : (O.subtype).mapMatrix RO = (algebraMap (𝓞 F) (v.adicCompletion F)).mapMatrix R` using `rfl`.

Establish `h2` using `RingHom.map_det (O.subtype) RO`. Rewrite `h2` using `[h1, ← RingHom.map_det]`. Conclude with `h2`. Establish `hdetv : R.det ∉ v.asIdeal` using `fun h => by`. Apply `hRO` to reduce the goal to its premises.

Apply `glo_res_zero v` to reduce the goal to its premises. Rewrite using `[hROval, csApprox_val_int]`. Conclude with `(HeightOneSpectrum.intValuation_lt_one_iff_mem v _).2 h`. Establish `hdetE : ME.det = algebraMap (𝓞 F) E R.det` using `(RingHom.map_det _ R).symm`. Establish `hdet0 : ME.det ≠ 0`.

Rewrite using `[hdetE]`. Introduce `h0`. Apply `hdetv` to reduce the goal to its premises. Establish `: R.det = 0`. Establish `hinj : Function.Injective (algebraMap (𝓞 F) E)`.

Rewrite using `[IsScalarTower.algebraMap_eq (𝓞 F) F E]`. Conclude with `(algebraMap F E).injective.comp (IsFractionRing.injective (𝓞 F) F)`. Conclude with `hinj (by rw [h0, map_zero])`. Rewrite using `[this]`. Conclude with `zero_mem _`.

Establish `hdetP : algebraMap (𝓞 F) (𝓞 E) R.det ∉ P.asIdeal` using `fun h => hdetv (by rw [hvP]; exact h)`. Set `Mu : GL (Fin n) E` to `Matrix.GeneralLinearGroup.mkOfDetNeZero ME hdet0`. Set `g : Sp E n ≃ₗ[E] Sp E n` to `(toGLm E n).symm Mu`. Establish `hgx : ∀ x, g x = ME.mulVec x` using `fun x => rfl`. Establish `hg : g ∈ GLint E n P`.

Introduce `x`. Rewrite using `[hgx]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨s, hs, hsx⟩` from `(qsp_mem_locP P).1 hx`.

Use `(qsp_mem_locP P).2 ⟨s * algebraMap (𝓞 F) (𝓞 E) R.det, P.asIdeal.primeCompl.mul_mem hs hdetP, ?_⟩` and prove the remaining obligations. Establish `h1 : (ME.adjugate).mulVec (s • ME.mulVec x) = (s * algebraMap (𝓞 F) (𝓞 E) R.det) • x`. Rewrite using `[Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec, hdetE, mul_smul]`. Use `congr 1`. Rewrite using `[← h1]`.

Establish `hadj : ME.adjugate = R.adjugate.map (algebraMap (𝓞 F) E)` using `(RingHom.map_adjugate _ R).symm`. Rewrite using `[hadj]`. Conclude with `qsp_std_mulVec hsx`. Introduce `hx`. Take `⟨s, hs, hsx⟩` from `(qsp_mem_locP P).1 hx`.

Use `(qsp_mem_locP P).2 ⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_smul]`. Conclude with `qsp_std_mulVec hsx`. Use `⟨⟨g, hg⟩, ?_⟩` and prove the remaining obligations. Establish `hιg : ∀ i j, ((qbIota P φ ⟨g, hg⟩ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j = algebraMap (𝓞 F) (v.adicCompletion F) (r i j)` using `fun i j => by`.

Rewrite using `[qbIota_apply]`. Establish `hM : toGLm E n g = Mu` using `(toGLm E n).apply_symm_apply Mu`. Rewrite using `[show ((⟨g, hg⟩ : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) = g from rfl, hM]`. Use `show φ (ME i j) = _`. Use `show φ (algebraMap (𝓞 F) E (r i j)) = _`.

Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 F) F E, hF, ← IsScalarTower.algebraMap_apply]`. Establish `hι1` using `qbIota_int P φ hint hPv ⟨g, hg⟩`. Establish `hι2` using `qbIota_int_inv P φ hint hPv ⟨g, hg⟩`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul]`.

Conclude with `qbInt_mul hι2 hk`. Rewrite using `[mul_inv_rev, inv_inv, Units.val_mul]`. Conclude with `qbInt_mul hk' hι1`. Establish `hh : (((qbIota P φ ⟨g, hg⟩)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * ((qbIota P φ ⟨g, hg⟩ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`.

Establish `e2 : (((qbIota P φ ⟨g, hg⟩)⁻¹ * k : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) - 1 = (((qbIota P φ ⟨g, hg⟩)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * ((k : Matrix (Fin n) (Fin n) (v.adicCompletion F) …`. Rewrite using `[Units.val_mul, _root_.mul_sub, hh]`. Rewrite using `[e2]`. Use `qbDiv_mul_left hι2 fun i j => ⟨y i j, hy i j, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.sub_apply, hιg, e i j, add_sub_cancel_left]`.
-/
theorem qsp_dense (D : 𝓞 F) (hD : D ≠ 0) (hDv : D ∈ v.asIdeal) (k : GL (Fin n) (v.adicCompletion F))
    (hk : qbInt (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)))
    (hk' : qbInt ((k⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))) :
    ∃ g : ↥(GLint E n P), (qbIota P φ g)⁻¹ * k ∈ qbK (algebraMap (𝓞 F) (v.adicCompletion F) D) := by
  classical
  choose r y hy e using fun i j => qsp_approx D hD ((k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) (hk i j)
  let R : Matrix (Fin n) (Fin n) (𝓞 F) := fun i j => r i j
  let ME : Matrix (Fin n) (Fin n) E := R.map (algebraMap (𝓞 F) E)
  let O := v.adicCompletionIntegers F
  have hDval : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) < 1 := by
    rw [csApprox_val_int]; exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v D).2 hDv

  let kO : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, hk i j⟩
  let kiO : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, hk' i j⟩
  let RO : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, glo_algMap_int v (r i j)⟩
  have hkk : kO * kiO = 1 := by
    have h1 : (O.subtype).mapMatrix (kO * kiO) = (O.subtype).mapMatrix 1 := by
      rw [map_mul, map_one]
      show ((k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * ((k⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))) = 1
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    exact Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h1 i) j)
  have hdetk : IsUnit kO.det := Matrix.isUnit_det_of_right_inverse hkk
  have hres : (IsLocalRing.residue O).mapMatrix kO = (IsLocalRing.residue O).mapMatrix RO := by
    ext i j
    show IsLocalRing.residue O (kO i j) = IsLocalRing.residue O (RO i j)
    rw [← sub_eq_zero, ← map_sub]
    apply glo_res_zero v
    show Valued.v ((k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j - algebraMap (𝓞 F) (v.adicCompletion F) (r i j)) < 1
    rw [e i j, add_sub_cancel_left, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hy i j))) hDval
  have hRO : IsLocalRing.residue O RO.det ≠ 0 := by
    rw [RingHom.map_det, ← hres, ← RingHom.map_det]
    exact (hdetk.map (IsLocalRing.residue O)).ne_zero
  have hROval : ((RO.det : O) : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) R.det := by
    have h1 : (O.subtype).mapMatrix RO = (algebraMap (𝓞 F) (v.adicCompletion F)).mapMatrix R := rfl
    have h2 := RingHom.map_det (O.subtype) RO
    rw [h1, ← RingHom.map_det] at h2
    exact h2
  have hdetv : R.det ∉ v.asIdeal := fun h => by
    apply hRO
    apply glo_res_zero v
    rw [hROval, csApprox_val_int]
    exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v _).2 h
  have hdetE : ME.det = algebraMap (𝓞 F) E R.det := (RingHom.map_det _ R).symm
  have hdet0 : ME.det ≠ 0 := by
    rw [hdetE]
    intro h0
    apply hdetv
    have : R.det = 0 := by
      have hinj : Function.Injective (algebraMap (𝓞 F) E) := by
        rw [IsScalarTower.algebraMap_eq (𝓞 F) F E]
        exact (algebraMap F E).injective.comp (IsFractionRing.injective (𝓞 F) F)
      exact hinj (by rw [h0, map_zero])
    rw [this]; exact zero_mem _
  have hdetP : algebraMap (𝓞 F) (𝓞 E) R.det ∉ P.asIdeal := fun h => hdetv (by rw [hvP]; exact h)
  let Mu : GL (Fin n) E := Matrix.GeneralLinearGroup.mkOfDetNeZero ME hdet0
  let g : Sp E n ≃ₗ[E] Sp E n := (toGLm E n).symm Mu
  have hgx : ∀ x, g x = ME.mulVec x := fun x => rfl
  have hg : g ∈ GLint E n P := by
    intro x
    rw [hgx]
    constructor
    · intro hx
      obtain ⟨s, hs, hsx⟩ := (qsp_mem_locP P).1 hx
      refine (qsp_mem_locP P).2 ⟨s * algebraMap (𝓞 F) (𝓞 E) R.det, P.asIdeal.primeCompl.mul_mem hs hdetP, ?_⟩
      have h1 : (ME.adjugate).mulVec (s • ME.mulVec x) = (s * algebraMap (𝓞 F) (𝓞 E) R.det) • x := by
        rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
          hdetE, mul_smul]
        congr 1
      rw [← h1]
      have hadj : ME.adjugate = R.adjugate.map (algebraMap (𝓞 F) E) := (RingHom.map_adjugate _ R).symm
      rw [hadj]
      exact qsp_std_mulVec hsx
    · intro hx
      obtain ⟨s, hs, hsx⟩ := (qsp_mem_locP P).1 hx
      refine (qsp_mem_locP P).2 ⟨s, hs, ?_⟩
      rw [← Matrix.mulVec_smul]
      exact qsp_std_mulVec hsx
  refine ⟨⟨g, hg⟩, ?_⟩
  have hιg : ∀ i j, ((qbIota P φ ⟨g, hg⟩ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j =
      algebraMap (𝓞 F) (v.adicCompletion F) (r i j) := fun i j => by
    rw [qbIota_apply]
    have hM : toGLm E n g = Mu := (toGLm E n).apply_symm_apply Mu
    rw [show ((⟨g, hg⟩ : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) = g from rfl, hM]
    show φ (ME i j) = _
    show φ (algebraMap (𝓞 F) E (r i j)) = _
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F E, hF, ← IsScalarTower.algebraMap_apply]
  have hι1 := qbIota_int P φ hint hPv ⟨g, hg⟩
  have hι2 := qbIota_int_inv P φ hint hPv ⟨g, hg⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul]; exact qbInt_mul hι2 hk
  · rw [mul_inv_rev, inv_inv, Units.val_mul]; exact qbInt_mul hk' hι1
  · have hh : (((qbIota P φ ⟨g, hg⟩)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
        ((qbIota P φ ⟨g, hg⟩ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e2 : (((qbIota P φ ⟨g, hg⟩)⁻¹ * k : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) - 1 =
        (((qbIota P φ ⟨g, hg⟩)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
          ((k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) - ((qbIota P φ ⟨g, hg⟩ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))) := by
      rw [Units.val_mul, _root_.mul_sub, hh]
    rw [e2]
    refine qbDiv_mul_left hι2 fun i j => ⟨y i j, hy i j, ?_⟩
    rw [Matrix.sub_apply, hιg, e i j, add_sub_cancel_left]

end Dense

end Formalism.L2.Col
