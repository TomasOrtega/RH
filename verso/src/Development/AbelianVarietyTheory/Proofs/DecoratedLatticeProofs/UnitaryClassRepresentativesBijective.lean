import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.RdVal
variable {D : D7}

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r e`. Simplify using `[toEAf, finPart, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.UG.sigR, sigD]`. Consider the case `add a b ha hb`.

Rewrite using `[RingHom.map_add, RingHom.map_add, ha, hb, RingHom.map_add, RingHom.map_add]`.
-/
theorem toEAf_sig (a : AE D) :
    toEAf D (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig a) =
      Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (toEAf D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [toEAf, finPart, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.UG.sigR, sigD]
  | add a b ha hb =>
    rw [RingHom.map_add, RingHom.map_add, ha, hb, RingHom.map_add, RingHom.map_add]

/- English proof (translation)
Simplify using `[toEAf, finPart, incA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Formalism.UG.inclE]`.
-/
theorem toEAf_incl (e : D.host.E) :
    toEAf D (incA D e) = Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) e := by
  simp [toEAf, finPart, incA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Formalism.UG.inclE]

/- English proof (translation)
The claim follows from `(Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (matHom V g))`.
-/
theorem isUnit_det_mt (V : HSp D) (g : GA D V) : IsUnit (mt V g).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (matHom V g))

/- English proof (translation)
Conclude with `(show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig V.gram from g).2`.
-/
theorem mt_unitary (V : HSp D) (g : GA D V) :
    Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (mt V g) * V.gram.map (incA D) * mt V g =
      V.gram.map (incA D) := by
  exact (show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig V.gram from g).2

/- English proof (translation)
Establish `hdet : IsUnit (finM V hn g).det`. Simplify using `only [finM, Matrix.det_reindex_self]`. Establish `hm` using `RingHom.map_det (toEAf D) (mt V g)`. Rewrite `hm` using `[RingHom.mapMatrix_apply]`. Rewrite using `[← hm]`.

Conclude with `(isUnit_det_mt V g).map _`. Use `⟨⟨((Matrix.isUnit_iff_isUnit_det _).mpr hdet).unit, ?_⟩, rfl⟩` and prove the remaining obligations. Use `show Formalism.UG.cT _ (finM V hn g) * J.map _ * finM V hn g = J.map _`. Establish `key : Formalism.UG.cT (Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (finM V hn g) = ((Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (mt V g)).map (toEAf D)).reindex (finCongr hn) (finCongr hn)`. Use extensionality with `i j`.

Simplify using `[finM, Formalism.UG.cT, Matrix.reindex_apply, toEAf_sig]`. Establish `hJ' : J.map (Formalism.UG.inclE (F` using `D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) = ((V.gram.map (incA D)).map (toEAf D)).reindex (finCongr hn) (finCongr hn) := by`. Substitute `hJ` using the available equality. Use extensionality with `i j`. Simplify using `[Matrix.reindex_apply, toEAf_incl]`.

Rewrite using `[key, hJ', finM]`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, ← Matrix.map_mul, mt_unitary]`.
-/
theorem finM_mem (V : HSp D) {n : ℕ} (hn : V.rank = n) (J : Matrix (Fin n) (Fin n) D.host.E)
    (hJ : J = V.gram.reindex (finCongr hn) (finCongr hn)) (g : GA D V) :
    ∃ x : UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F), x.1.1 = finM V hn g := by
  have hdet : IsUnit (finM V hn g).det := by
    simp only [finM, Matrix.det_reindex_self]
    have hm := RingHom.map_det (toEAf D) (mt V g)
    rw [RingHom.mapMatrix_apply] at hm
    rw [← hm]
    exact (isUnit_det_mt V g).map _
  refine ⟨⟨((Matrix.isUnit_iff_isUnit_det _).mpr hdet).unit, ?_⟩, rfl⟩
  show Formalism.UG.cT _ (finM V hn g) * J.map _ * finM V hn g = J.map _
  have key : Formalism.UG.cT (Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (finM V hn g) =
      ((Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (mt V g)).map (toEAf D)).reindex
        (finCongr hn) (finCongr hn) := by
    ext i j; simp [finM, Formalism.UG.cT, Matrix.reindex_apply, toEAf_sig]
  have hJ' : J.map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) =
      ((V.gram.map (incA D)).map (toEAf D)).reindex (finCongr hn) (finCongr hn) := by
    subst hJ; ext i j; simp [Matrix.reindex_apply, toEAf_incl]
  rw [key, hJ', finM]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, ← Matrix.map_mul, mt_unitary]

/- English proof (translation)
Simplify using `only [infM, Matrix.det_reindex_self]`. Establish `hm` using `RingHom.map_det ((θ τ).comp (infPart D)) (mt V g)`. Rewrite `hm` using `[RingHom.mapMatrix_apply]`. Establish `e : compAt θ τ (mt V g) = (mt V g).map ((θ τ).comp (infPart D))` using `rfl`. Rewrite using `[e, ← hm]`.

Conclude with `(isUnit_det_mt V g).map _`.
-/
theorem infM_unit (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (τ : D.what₂.Tau) :
    IsUnit (infM θ V hn g τ).det := by
  simp only [infM, Matrix.det_reindex_self]
  have hm := RingHom.map_det ((θ τ).comp (infPart D)) (mt V g)
  rw [RingHom.mapMatrix_apply] at hm
  have e : compAt θ τ (mt V g) = (mt V g).map ((θ τ).comp (infPart D)) := rfl
  rw [e, ← hm]
  exact (isUnit_det_mt V g).map _

/- English proof (translation)
Simplify using `only [atInf, ← Matrix.map_mul, Units.mul_inv]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem atInf_mul_inv {n : ℕ} (γ : GL (Fin n) D.host.E) (τ : D.what₂.Tau) :
    atInf (embT D) (γ : Matrix (Fin n) (Fin n) D.host.E) τ * atInf (embT D) ((γ⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) τ = 1 := by
  simp only [atInf, ← Matrix.map_mul, Units.mul_inv]
  exact Matrix.map_one _ (map_zero _) (map_one _)

end GlobalTheory.AdForm.RdVal

open GlobalTheory.AdForm.RdVal in

/- English proof (translation)
Introduce `D θ _ V n hn J hJ T f bad S cl yc hbij Ψ hΨ y g`. Use `⟨finM_mem V hn J hJ g, fun τ => infM_unit θ V hn g τ, ?_⟩` and prove the remaining obligations. Introduce `x y' hx hy`. Take `⟨c, hc⟩` from `hbij.2 (Quotient.mk'' x : Cls S)`. Establish `hex : ∃ p, IsDec S yc (finM V hn g) p`.

Take `⟨h, hh, k, hk, hxe⟩` from `(DoubleCoset.eq _ _ _ _).mp hc`. Take `⟨γ, hγ, hγe⟩` from `Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hh)`. Use `⟨(c, γ, ⟨k.1, Subgroup.mem_subgroupOf.mp hk⟩), hγ, ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hγe, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← hxe, hx]`.

Establish `hp` using `hex.choose_spec`. Establish `hfr : ∀ τ, IsUnit (atInf (embT D) ((hex.choose.2.1)⁻¹ : GL (Fin n) D.host.E).1 τ * infM θ V hn g τ * y.1 τ).det`. Introduce `τ`. Rewrite using `[Matrix.det_mul, Matrix.det_mul]`. Conclude with `((Matrix.isUnit_det_of_left_inverse (atInf_mul_inv hex.choose.2.1 τ)).mul (infM_unit θ V hn g τ)).mul (y.2 τ)`.

Unfold `rdS`. Rewrite using `[dif_pos hex, atFr, dif_pos hfr]`. Establish `law` using `hΨ hex.choose.2.1 hp.1 (yc hex.choose.1) x hex.choose.2.2 (Units.ext (hx.trans hp.2)) y' ⟨_, hfr⟩ (by`. Introduce `τ`. Use `show y'.1 τ = _`.

Rewrite using `[hy τ]`. Simplify using `only [← Matrix.mul_assoc, atInf_mul_inv, Matrix.one_mul])`. Conclude with `law.symm`.
-/
theorem GlobalTheory.AdForm.rdS_val : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (hn : V.rank = n) (J : Matrix (Fin n) (Fin n) D.host.E), J = V.gram.reindex (finCongr hn) (finCongr hn) → ∀ (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 D.host.F))) (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (cl : Type) (yc : cl → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)) → ∀ Ψ ∈ AdFun S (embT D), ∀ (y : Frames (gramC J (embT D))) (g : GA D V), (∃ x : UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F), x.1.1 = finM V hn g) ∧ (∀ τ, IsUnit (infM θ V hn g τ).det) ∧ ∀ (x : UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (y' : Frames (gramC J (embT D))), x.1.1 = finM V hn g → IsTr (infM θ V hn g) y y' → rdS θ V hn S yc (fun c => Ψ (yc c)) y g = Ψ x y' := by
  intro D θ _ V n hn J hJ T f bad S cl yc hbij Ψ hΨ y g
  refine ⟨finM_mem V hn J hJ g, fun τ => infM_unit θ V hn g τ, ?_⟩
  intro x y' hx hy
  obtain ⟨c, hc⟩ := hbij.2 (Quotient.mk'' x : Cls S)
  have hex : ∃ p, IsDec S yc (finM V hn g) p := by
    obtain ⟨h, hh, k, hk, hxe⟩ := (DoubleCoset.eq _ _ _ _).mp hc
    obtain ⟨γ, hγ, hγe⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hh)
    refine ⟨(c, γ, ⟨k.1, Subgroup.mem_subgroupOf.mp hk⟩), hγ, ?_⟩
    dsimp only
    rw [hγe, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← hxe, hx]
  have hp := hex.choose_spec
  have hfr : ∀ τ, IsUnit (atInf (embT D) ((hex.choose.2.1)⁻¹ : GL (Fin n) D.host.E).1 τ * infM θ V hn g τ * y.1 τ).det := by
    intro τ
    rw [Matrix.det_mul, Matrix.det_mul]
    exact ((Matrix.isUnit_det_of_left_inverse (atInf_mul_inv hex.choose.2.1 τ)).mul (infM_unit θ V hn g τ)).mul (y.2 τ)
  unfold rdS
  rw [dif_pos hex, atFr, dif_pos hfr]
  have law := hΨ hex.choose.2.1 hp.1 (yc hex.choose.1) x hex.choose.2.2 (Units.ext (hx.trans hp.2)) y' ⟨_, hfr⟩ (by
    intro τ
    show y'.1 τ = _
    rw [hy τ]
    simp only [← Matrix.mul_assoc, atInf_mul_inv, Matrix.one_mul])
  exact law.symm
