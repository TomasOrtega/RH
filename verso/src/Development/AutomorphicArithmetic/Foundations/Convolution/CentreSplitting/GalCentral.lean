import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsTw
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdUnique
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

/- English proof (translation)
The claim follows from `(UpperTheory.ConvolutionTheory.K.adUnique E σ s.toRingHom h.1 h.2.1).trans (UpperTheory.ConvolutionTheory.K.adUnique E σ (UpperTheory.V.FieldIso.adm σ) (UpperTheory.V.FieldIso.continuous_adm σ) (UpperTheory.V.FieldIso.adm_algebraMap σ)).symm`.
-/
private theorem galAd_eq_adm {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (σ : E ≃+* E)
    (s : Ad E ≃+* Ad E) (h : UpperTheory.CBC.IsGalAd σ s) : s.toRingHom = UpperTheory.V.FieldIso.adm σ :=
  (UpperTheory.ConvolutionTheory.K.adUnique E σ s.toRingHom h.1 h.2.1).trans
    (UpperTheory.ConvolutionTheory.K.adUnique E σ (UpperTheory.V.FieldIso.adm σ) (UpperTheory.V.FieldIso.continuous_adm σ)
      (UpperTheory.V.FieldIso.adm_algebraMap σ)).symm

open Neutral.B1 Formalism.L2.Host Formalism.L2.Host.CT GlobalTheory.CuspRep in
/- English proof (translation)
Use function extensionality and compare the values at `u`. Express the relevant statement in the definitionally equal form `coord _ _ = _`. Unfold `coord`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem cinf_real {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (σ : E ≃+* E) (c : ℝ) :
    UpperTheory.V.FieldIso.cinf σ (fun _ => (c : ℂ)) = fun _ => (c : ℂ) := by
  funext u
  change coord _ _ = _
  unfold coord
  split_ifs <;> simp

/- English proof (translation)
Unfold `GlobalTheory.UnitaryBC.splitCentre`. Rewrite using `[UpperTheory.V.FieldIso.gaMap_infGL]`. Use `congr 1`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `UpperTheory.V.FieldIso.cinf σ (Matrix.diagonal (fun _ => fun _ : InfinitePlace E => Complex.exp (t : ℂ)) i j) = Matrix.diagonal (fun _ => fun _ : InfinitePlace E => Complex.exp (t : ℂ)) i j`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[Matrix.diagonal_apply_eq, ← Complex.ofReal_exp]`. Conclude with `cinf_real σ _`. Rewrite using `[Matrix.diagonal_apply_ne _ h]`.

Conclude with `map_zero _`.
-/
private theorem map_splitCentre {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (σ : E ≃+* E) (a : ℕ)
    (t : ℝ) : UpperTheory.V.FieldIso.gaMap a σ (GlobalTheory.UnitaryBC.splitCentre E a t) = GlobalTheory.UnitaryBC.splitCentre E a t := by
  unfold GlobalTheory.UnitaryBC.splitCentre
  rw [UpperTheory.V.FieldIso.gaMap_infGL]
  congr 1
  refine Units.ext (Matrix.ext fun i j => ?_)
  change UpperTheory.V.FieldIso.cinf σ (Matrix.diagonal (fun _ => fun _ : InfinitePlace E => Complex.exp (t : ℂ)) i j) =
    Matrix.diagonal (fun _ => fun _ : InfinitePlace E => Complex.exp (t : ℂ)) i j
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, ← Complex.ofReal_exp]
    exact cinf_real σ _
  · rw [Matrix.diagonal_apply_ne _ h]
    exact map_zero _

/- English proof (translation)
Introduce `E _ _ _ n σ s h`. Use `⟨fun s' h' => RingEquiv.ext fun x => ?_, fun t => ?_⟩` and prove the remaining obligations. Establish `e` using `(galAd_eq_adm σ s' h').trans (galAd_eq_adm σ s h).symm`. Conclude with `congrArg (fun f : Ad E →+* Ad E => f x) e`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases.

Conclude with `Units.ext (Matrix.ext fun i => i.elim0)`. Establish `hd : (Module.finrank ℚ E : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 Module.finrank_pos.ne'`. Establish `hn' : (n : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 hn.ne'`. Establish `ht : t = ⟨Real.exp (n * Module.finrank ℚ E * (Real.log t / (n * Module.finrank ℚ E))), Real.exp_pos _⟩`. Use `Subtype.ext ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(t : ℝ) = Real.exp _`. Rewrite using `[mul_div_cancel₀ _ (mul_ne_zero hn' hd), Real.exp_log t.2]`. Rewrite using `[ht, ← UpperTheory.V.KernelIndexFullLattice.splitEq_holds E n, galAd_eq_adm σ s h]`. Conclude with `map_splitCentre σ n _`.
-/
theorem UpperTheory.ConvolutionTheory.Dp.galCentral :
    UpperTheory.ConvolutionTheory.Dp.GalCentral := by
  intro E _ _ _ n σ s h
  refine ⟨fun s' h' => RingEquiv.ext fun x => ?_, fun t => ?_⟩
  · have e := (galAd_eq_adm σ s' h').trans (galAd_eq_adm σ s h).symm
    exact congrArg (fun f : Ad E →+* Ad E => f x) e
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Units.ext (Matrix.ext fun i => i.elim0)
    · have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
      have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      have ht : t = ⟨Real.exp (n * Module.finrank ℚ E * (Real.log t / (n * Module.finrank ℚ E))), Real.exp_pos _⟩ := by
        refine Subtype.ext ?_
        change (t : ℝ) = Real.exp _
        rw [mul_div_cancel₀ _ (mul_ne_zero hn' hd), Real.exp_log t.2]
      rw [ht, ← UpperTheory.V.KernelIndexFullLattice.splitEq_holds E n, galAd_eq_adm σ s h]
      exact map_splitCentre σ n _
