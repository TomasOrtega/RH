import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantUnitMatrixBcrisFrame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameAinfMatrixFrobeniusGaloisEqsStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

/- English proof (translation)
Introduce `l _ K bk τ hτ`. Establish `hFφ : ∀ a : Ainf l, WittVector.frobenius a = Per.φA l a` using `fun a => (GlobalTheory.RingBasics.φA_apply l a).symm`. Use `set f : Ainf l →+* Per.Bcris l := (Per.aB l).comp (Per.φA l) with hf`. Use `set alg : Per.Acris l →+* Per.Bcris l := algebraMap (Per.Acris l) (Per.Bcris l) with halg`. Establish `hif : ∀ a : Ainf l, iB l (fI l a) = f a` using `fun a => by`.

Simplify using `only [fI, iB, iA, hFφ, hf, RingHom.comp_apply, GlobalTheory.RingIface.aB_eq_alg]`. Establish `hw : IsUnit (f τ)`. Take `⟨-, e, η, ⟨he1, he2⟩, hτe⟩` from `hτ`. Establish `hne : e ≠ 1`. Introduce and unpack `rfl`.

Apply `he2` to reduce the goal to its premises. Simplify using the standard rewrite rules. Establish `hmu : IsUnit (Per.aB l (WittVector.teichmuller l e - 1))` using `GlobalTheory.CrisLoc.unit_of_root_aB l e he1 hne`. Establish `: f τ = Per.aB l (η : Ainf l) * Per.aB l (WittVector.teichmuller l e - 1)`. Simplify using `only [hf, RingHom.comp_apply, ← hFφ, hτe, map_mul]`.

Rewrite using `[this]`. Conclude with `(η.isUnit.map _).mul hmu`. Use `⟨by rw [hif]; exact hw, ?_⟩` and prove the remaining obligations. Introduce `N k d ρ F Y Y' Q Q' hY hYY hQQ hε`. Establish `hgal : ∀ g : ↥(GK K), τ ^ N • ((ρ g).val.map (Per.zA l) * Y.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • (Y * F.ε g)` using `(GlobalTheory.T.frame_ainf_matrix_frobenius_galois_eqs l K bk τ hτ N d _ F Y Y' hY hYY).2.1`.

Establish `e2 : (⇑alg ∘ ⇑(fI l)) = ⇑f` using `funext hif`. Take `⟨W, hW⟩` from `hw.pow N`. Use `set A := Y.map f with hA`. Use `set B := Q.map alg with hB`. Use `⟨((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • (A * B), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Establish `hB' : B * Q'.map alg = alg ((l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Bcris l))`. Rewrite using `[hB, ← Matrix.map_mul, hQQ, GlobalTheory.BcrisInv.map_smul_matrix, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hA' : A * Y'.map f = f τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Bcris l))`. Rewrite using `[hA, ← Matrix.map_mul, hYY, GlobalTheory.BcrisInv.map_smul_matrix, Matrix.map_one _ (map_zero _) (map_one _), map_pow]`. Establish `hc : IsUnit (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) * alg ((l : Per.Acris l) ^ (2 * k)) * f τ ^ (2 * N))`.

Use `(W⁻¹.isUnit.mul ?_).mul (hw.pow _)` and prove the remaining obligations. Establish `h` using `(isUnit_l_Bcris l).pow (2 * k)`. Simplify `h` using `[halg, map_pow, map_natCast]`. Take `⟨c, hcv⟩` from `hc`. Use `set V := Q'.map alg * Y'.map f`.

Establish `hUV : (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • (A * B)) * V = (c : Per.Bcris l) • (1 : Matrix (Fin d) (Fin d) (Per.Bcris l))`. Rewrite using `[hcv, smul_mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc B, hB', smul_mul_assoc, Matrix.one_mul, mul_smul_comm, hA', smul_smul, smul_smul, mul_assoc]`. Establish `h1 : (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • (A * B)) * (((c⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • V) = 1`. Rewrite using `[Matrix.mul_smul, hUV, smul_smul, Units.inv_mul, one_smul]`. Conclude with `⟨⟨_, _, h1, mul_eq_one_comm.mp h1⟩, rfl⟩`.

Introduce `g set σ := Per.σB (g : GQ l) with hσ`. Establish `hσaB : ∀ a : Ainf l, σ (Per.aB l a) = Per.aB l (Per.σA (g : GQ l) a)` using `(ActLaws.act_laws l).2.2.2.2.2.1 (g : GQ l)`. Establish `hσf : ∀ a : Ainf l, σ (f a) = f (Per.σA (g : GQ l) a)` using `fun a => by`. Simplify using `only [hf, RingHom.comp_apply, hσaB, ActLaws.φA_σA]`. Establish `hfz : ∀ z : ℤ_[l], f (Per.zA l z) = Per.zB l z` using `fun z => by`.

Simplify using `only [hf, RingHom.comp_apply, GlobalTheory.RingIface.zB_eq_aB_zA, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.1 z]`. Establish `hσalg : ∀ x : Per.Acris l, σ (alg x) = alg (sigA (g : GQ l) x)` using `(ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.1 (g : GQ l)`. Establish `hG` using `congrArg (fun M => M.map f) (hgal g)`. Simplify using `only [GlobalTheory.BcrisInv.map_smul_matrix, Matrix.map_mul, Matrix.map_map, map_pow] at hG`. Establish `e1 : (⇑f ∘ ⇑(Per.zA l)) = ⇑(Per.zB l)` using `funext hfz`.

Rewrite `hG` using `[e1, ← hσf]`. Establish `hE` using `congrArg (fun M => M.map alg) (hε g)`. Simplify using `only [Matrix.map_mul, Matrix.map_map] at hE`. Rewrite `hE` using `[e2]`. Establish `eA : A.map σ = Y.map (⇑f ∘ ⇑(Per.σA (g : GQ l)))`.

Rewrite using `[hA, Matrix.map_map]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Conclude with `hσf a`. Establish `eB : B.map σ = Q.map (⇑alg ∘ ⇑(sigA (g : GQ l)))`.

Rewrite using `[hB, Matrix.map_map]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Conclude with `hσalg a`. Rewrite using `[GlobalTheory.BcrisInv.map_smul_matrix, Matrix.map_mul, eA, eB]`.

Establish `hsW : σ ((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) * σ (W : Per.Bcris l) = 1`. Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Establish `hσW : σ (f τ) ^ N = σ (W : Per.Bcris l)` using `by rw [hW, map_pow]`. Rewrite `hG` using `[hσW, ← hW]`. Establish `hZ : (ρ g).val.map (Per.zB l) * Y.map (⇑f ∘ ⇑(Per.σA (g : GQ l))) = (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) * σ (W : Per.Bcris l)) • (A * (F.ε g).map f)`.

Rewrite using `[← smul_smul, ← hG, smul_smul, Units.inv_mul, one_smul]`. Rewrite using `[mul_smul_comm, ← Matrix.mul_assoc, hZ, smul_mul_assoc, Matrix.mul_assoc, hE, smul_smul, mul_left_comm, hsW, mul_one]`. Rewrite using `[hif, ← hW, smul_smul, Units.mul_inv, one_smul, hA, hB, Matrix.map_mul, Matrix.map_map]`. Establish `e3 : (⇑(iB l) ∘ ⇑(fI l)) = ⇑f` using `funext hif`. Rewrite using `[e3]`.
-/
theorem invU_holds : InvU := by
  intro l _ K bk τ hτ
  have hFφ : ∀ a : Ainf l, WittVector.frobenius a = Per.φA l a := fun a => (GlobalTheory.RingBasics.φA_apply l a).symm
  set f : Ainf l →+* Per.Bcris l := (Per.aB l).comp (Per.φA l) with hf
  set alg : Per.Acris l →+* Per.Bcris l := algebraMap (Per.Acris l) (Per.Bcris l) with halg
  have hif : ∀ a : Ainf l, iB l (fI l a) = f a := fun a => by
    simp only [fI, iB, iA, hFφ, hf, RingHom.comp_apply, GlobalTheory.RingIface.aB_eq_alg]
  have hw : IsUnit (f τ) := by
    obtain ⟨-, e, η, ⟨he1, he2⟩, hτe⟩ := hτ
    have hne : e ≠ 1 := by
      rintro rfl; apply he2; simp
    have hmu : IsUnit (Per.aB l (WittVector.teichmuller l e - 1)) :=
      GlobalTheory.CrisLoc.unit_of_root_aB l e he1 hne
    have : f τ = Per.aB l (η : Ainf l) * Per.aB l (WittVector.teichmuller l e - 1) := by
      simp only [hf, RingHom.comp_apply, ← hFφ, hτe, map_mul]
    rw [this]; exact (η.isUnit.map _).mul hmu
  refine ⟨by rw [hif]; exact hw, ?_⟩
  intro N k d ρ F Y Y' Q Q' hY hYY hQQ hε
  have hgal : ∀ g : ↥(GK K), τ ^ N • ((ρ g).val.map (Per.zA l) * Y.map (Per.σA (g : GQ l))) =
      Per.σA (g : GQ l) τ ^ N • (Y * F.ε g) :=
    (GlobalTheory.T.frame_ainf_matrix_frobenius_galois_eqs l K bk τ hτ N d _ F Y Y' hY hYY).2.1
  have e2 : (⇑alg ∘ ⇑(fI l)) = ⇑f := funext hif
  obtain ⟨W, hW⟩ := hw.pow N
  set A := Y.map f with hA
  set B := Q.map alg with hB
  refine ⟨((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • (A * B), ⟨?_, ?_⟩, ?_⟩
  ·
    have hB' : B * Q'.map alg = alg ((l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Bcris l)) := by
      rw [hB, ← Matrix.map_mul, hQQ, GlobalTheory.BcrisInv.map_smul_matrix, Matrix.map_one _ (map_zero _) (map_one _)]
    have hA' : A * Y'.map f = f τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Bcris l)) := by
      rw [hA, ← Matrix.map_mul, hYY, GlobalTheory.BcrisInv.map_smul_matrix, Matrix.map_one _ (map_zero _) (map_one _), map_pow]
    have hc : IsUnit (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) * alg ((l : Per.Acris l) ^ (2 * k)) * f τ ^ (2 * N)) := by
      refine (W⁻¹.isUnit.mul ?_).mul (hw.pow _)
      have h := (isUnit_l_Bcris l).pow (2 * k)
      simpa [halg, map_pow, map_natCast] using h
    obtain ⟨c, hcv⟩ := hc
    set V := Q'.map alg * Y'.map f
    have hUV : (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • (A * B)) * V = (c : Per.Bcris l) • (1 : Matrix (Fin d) (Fin d) (Per.Bcris l)) := by
      rw [hcv, smul_mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc B, hB', smul_mul_assoc, Matrix.one_mul,
        mul_smul_comm, hA', smul_smul, smul_smul, mul_assoc]
    have h1 : (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • (A * B)) * (((c⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • V) = 1 := by
      rw [Matrix.mul_smul, hUV, smul_smul, Units.inv_mul, one_smul]
    exact ⟨⟨_, _, h1, mul_eq_one_comm.mp h1⟩, rfl⟩
  · intro g
    set σ := Per.σB (g : GQ l) with hσ
    have hσaB : ∀ a : Ainf l, σ (Per.aB l a) = Per.aB l (Per.σA (g : GQ l) a) :=
      (ActLaws.act_laws l).2.2.2.2.2.1 (g : GQ l)
    have hσf : ∀ a : Ainf l, σ (f a) = f (Per.σA (g : GQ l) a) := fun a => by
      simp only [hf, RingHom.comp_apply, hσaB, ActLaws.φA_σA]
    have hfz : ∀ z : ℤ_[l], f (Per.zA l z) = Per.zB l z := fun z => by
      simp only [hf, RingHom.comp_apply, GlobalTheory.RingIface.zB_eq_aB_zA, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.1 z]
    have hσalg : ∀ x : Per.Acris l, σ (alg x) = alg (sigA (g : GQ l) x) :=
      (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.1 (g : GQ l)
    have hG := congrArg (fun M => M.map f) (hgal g)
    simp only [GlobalTheory.BcrisInv.map_smul_matrix, Matrix.map_mul, Matrix.map_map, map_pow] at hG
    have e1 : (⇑f ∘ ⇑(Per.zA l)) = ⇑(Per.zB l) := funext hfz
    rw [e1, ← hσf] at hG
    have hE := congrArg (fun M => M.map alg) (hε g)
    simp only [Matrix.map_mul, Matrix.map_map] at hE
    rw [e2] at hE
    have eA : A.map σ = Y.map (⇑f ∘ ⇑(Per.σA (g : GQ l))) := by
      rw [hA, Matrix.map_map]; congr 1; funext a; exact hσf a
    have eB : B.map σ = Q.map (⇑alg ∘ ⇑(sigA (g : GQ l))) := by
      rw [hB, Matrix.map_map]; congr 1; funext a; exact hσalg a
    rw [GlobalTheory.BcrisInv.map_smul_matrix, Matrix.map_mul, eA, eB]
    have hsW : σ ((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) * σ (W : Per.Bcris l) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hσW : σ (f τ) ^ N = σ (W : Per.Bcris l) := by rw [hW, map_pow]
    rw [hσW, ← hW] at hG
    have hZ : (ρ g).val.map (Per.zB l) * Y.map (⇑f ∘ ⇑(Per.σA (g : GQ l))) =
        (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) * σ (W : Per.Bcris l)) • (A * (F.ε g).map f) := by
      rw [← smul_smul, ← hG, smul_smul, Units.inv_mul, one_smul]
    rw [mul_smul_comm, ← Matrix.mul_assoc, hZ, smul_mul_assoc, Matrix.mul_assoc, hE, smul_smul, mul_left_comm, hsW,
      mul_one]
  · rw [hif, ← hW, smul_smul, Units.mul_inv, one_smul, hA, hB, Matrix.map_mul, Matrix.map_map]
    have e3 : (⇑(iB l) ∘ ⇑(fI l)) = ⇑f := funext hif
    rw [e3]

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
