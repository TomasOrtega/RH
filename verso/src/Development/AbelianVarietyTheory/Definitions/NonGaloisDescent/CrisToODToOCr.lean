import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCanonicalAcrisToBdRPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApprox
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK
open scoped Formalism.Per

namespace GlobalTheory.BKReal

variable {l : ℕ} [hl : Fact l.Prime]

scoped instance algZlBdRp : Algebra ℤ_[l] (Per.BdRp l) :=
  ((GlobalTheory.MemLoc.aDp l).comp (algebraMap ℤ_[l] (Ainf l))).toAlgebra

variable (l) in

def ainfToBdRp : Ainf l →ₐ[ℤ_[l]] Per.BdRp l where
  toRingHom := GlobalTheory.MemLoc.aDp l
  commutes' _ := rfl

variable (l) in

def crisP : Per.Acris l →+* Per.BdRp l := (GlobalTheory.MemLoc.exists_isCrisP l).choose

variable (l) in

/- English proof (translation)
The claim follows from `(GlobalTheory.MemLoc.exists_isCrisP l).choose_spec`.
-/
theorem isCrisP_crisP : GlobalTheory.MemLoc.IsCrisP (crisP l) := (GlobalTheory.MemLoc.exists_isCrisP l).choose_spec

/- English proof (translation)
The claim follows from `(GlobalTheory.MemLoc.crisP_unique_equivariant l _ (isCrisP_crisP l)).1 j h`.
-/
theorem eq_crisP {j : Per.Acris l →+* Per.BdRp l} (h : GlobalTheory.MemLoc.IsCrisP j) : j = crisP l :=
  (GlobalTheory.MemLoc.crisP_unique_equivariant l _ (isCrisP_crisP l)).1 j h

/- English proof (translation)
The claim follows from `(congrArg (crisP l) (GlobalTheory.RingIface.tower l x)).trans ((isCrisP_crisP l).on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) x))`.
-/
theorem crisP_ainf (x : Ainf l) : crisP l (ainfToAcris l x) = ainfToBdRp l x :=
  (congrArg (crisP l) (GlobalTheory.RingIface.tower l x)).trans
    ((isCrisP_crisP l).on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) x))

variable (l) in

def acrisToBdRp : Per.Acris l →ₐ[ℤ_[l]] Per.BdRp l where
  toRingHom := crisP l
  commutes' _ := crisP_ainf _

/- English proof (translation)
Take `⟨ζ, e, h0, -, h1, hr⟩` from `GlobalTheory.MemLoc.exists_zeta_eps l`. Establish `he : e.untilt = 1` using `Subtype.ext (by`. Use `hr 0` as an intermediate fact. Rewrite `this` using `[h0, map_one]`. Conclude with `this)`.

Establish `hE : GlobalTheory.MemLoc.IsEps e` using `⟨he, fun hh => h1 (by`. Apply `(algebraMap (Om l) ℂ_[l]).injective` to reduce the goal to its premises. Rewrite using `[← hr 1, map_one]`. Conclude with `congrArg Subtype.val hh)⟩`. Establish `h2` using `congrArg (Ideal.map (GlobalTheory.MemLoc.aDp l)) (hd.trans (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE))`.

Rewrite `h2` using `[Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]`. Establish `h3` using `(GlobalTheory.MemLoc.filtration_eq_xi_pow l e hE).2.2.1`. Rewrite `h3` using `[← h2]`. Conclude with `h3`.
-/
theorem complete_BdRp {d : Ainf l} (hd : Ideal.span {d} = RingHom.ker (Per.θ l)) :
    IsAdicComplete (Ideal.span {ainfToBdRp l d}) (Per.BdRp l) := by
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps e := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have h2 := congrArg (Ideal.map (GlobalTheory.MemLoc.aDp l)) (hd.trans (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE))
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton] at h2
  have h3 := (GlobalTheory.MemLoc.filtration_eq_xi_pow l e hE).2.2.1
  rw [← h2] at h3
  exact h3

variable {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (t : Wq l a →ₐ[ℤ_[l]] O)

variable (l O) in

abbrev OD : Type := O ⊗[ℤ_[l]] Per.BdRp l

variable (l O) in

def toOD : OA l O →ₐ[O] OD l O := Algebra.TensorProduct.map (AlgHom.id _ _) (ainfToBdRp l)

variable (l O) in

def crisToOD : OCr l O →ₐ[O] OD l O := Algebra.TensorProduct.map (AlgHom.id _ _) (acrisToBdRp l)

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul o w => exact congrArg (fun y : Per.BdRp l => o ⊗ₜ[ℤ_[l]] y) (crisP_ainf w)`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem crisToOD_toOCr (x : OA l O) : crisToOD l O (toOCr l O x) = toOD l O x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => exact congrArg (fun y : Per.BdRp l => o ⊗ₜ[ℤ_[l]] y) (crisP_ainf w)
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Simplify `(GlobalTheory.MemLoc.isUnit_l_BdRp l).map (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O)` using `only [map_natCast]`.
-/
theorem isUnit_l_OD : IsUnit (l : OD l O) := by
  simpa only [map_natCast] using (GlobalTheory.MemLoc.isUnit_l_BdRp l).map
    (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O)

def constD : (ZMod a → O) →ₐ[O] OD l O := (toOD l O).comp (constA t)

namespace PiSys

variable [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] {e : ℕ} [NeZero e] (O) (K : Type) [NormedField K]
  [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e)

omit [NeZero e] in

def iAl : invL l (A O K) →+* OD l O :=
  IsLocalization.Away.lift (l : A O K) (g := ((toOD l O).comp (ϖ.iA O K)).toRingHom)
    (by rw [map_natCast]; exact isUnit_l_OD)

omit [NeZero e] in

/- English proof (translation)
The claim follows from `IsLocalization.Away.lift_eq (S := invL l (A O K)) (l : A O K) (g := ((toOD l O).comp (ϖ.iA O K)).toRingHom) (by rw [map_natCast]; exact isUnit_l_OD) ⟨f, h⟩`.
-/
theorem iAl_of_mem {f : K⟦X⟧} (h : f ∈ A O K) (h' : f ∈ invL l (A O K)) :
    ϖ.iAl O K ⟨f, h'⟩ = toOD l O (ϖ.iA O K ⟨f, h⟩) :=
  IsLocalization.Away.lift_eq (S := invL l (A O K)) (l : A O K)
    (g := ((toOD l O).comp (ϖ.iA O K)).toRingHom) (by rw [map_natCast]; exact isUnit_l_OD) ⟨f, h⟩

/- English proof (translation)
Rewrite using `[show ϖ.iAl O K (EIn l e _) = 1 ⊗ₜ ainfToBdRp l (ϖ.ev 1 (eis l 1 e)) from (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))]`. Conclude with `GlobalTheory.HWL.TensorWitt.complete_tensor (Module.Free.chooseBasis ℤ_[l] O) _ (h := complete_BdRp (ϖ.span_ev_eis 1))`.
-/
theorem complete_OD : IsAdicComplete (Ideal.span {ϖ.iAl O K (EIn l e _)}) (OD l O) := by
  rw [show ϖ.iAl O K (EIn l e _) = 1 ⊗ₜ ainfToBdRp l (ϖ.ev 1 (eis l 1 e)) from
    (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))]
  exact GlobalTheory.HWL.TensorWitt.complete_tensor (Module.Free.chooseBasis ℤ_[l] O) _
    (h := complete_BdRp (ϖ.span_ev_eis 1))

def iHatRing : Ahat O K l e →+* OD l O :=
  haveI := ϖ.complete_OD O K
  (AdicCompletion.ofAlgEquiv (Ideal.span {ϖ.iAl O K (EIn l e _)})).symm.toRingEquiv.toRingHom.comp
    (GlobalTheory.AdicMaps.adicMap (idE O K l e) _ (ϖ.iAl O K) (by simp [Ideal.span_le]))

/- English proof (translation)
The claim follows from `haveI := ϖ.complete_OD O K (congrArg (AdicCompletion.ofAlgEquiv (Ideal.span {ϖ.iAl O K (EIn l e _)})).symm (GlobalTheory.AdicMaps.adicMap_alg _ _ _ _ f)).trans ((AdicCompletion.ofAlgEquiv _).symm.commutes _)`.
-/
theorem iHatRing_ofAl (f : invL l (A O K)) : ϖ.iHatRing O K (ofAl O K l e f) = ϖ.iAl O K f :=
  haveI := ϖ.complete_OD O K
  (congrArg (AdicCompletion.ofAlgEquiv (Ideal.span {ϖ.iAl O K (EIn l e _)})).symm
    (GlobalTheory.AdicMaps.adicMap_alg _ _ _ _ f)).trans ((AdicCompletion.ofAlgEquiv _).symm.commutes _)

def iHat : Ahat O K l e →ₐ[O] OD l O where
  toRingHom := ϖ.iHatRing O K
  commutes' o := (ϖ.iHatRing_ofAl O K (algebraMap O _ o)).trans
    ((ϖ.iAl_of_mem O K (algebraMap O (A O K) o).2 _).trans (((toOD l O).comp (ϖ.iA O K)).commutes o))

/- English proof (translation)
The claim follows from `ϖ.iHatRing_ofAl O K f`.
-/
theorem iHat_ofAl (f : invL l (A O K)) : ϖ.iHat O K (ofAl O K l e f) = ϖ.iAl O K f := ϖ.iHatRing_ofAl O K f

/- English proof (translation)
The claim follows from `(ϖ.iHat_ofAl O K _).trans (ϖ.iAl_of_mem O K f.2 _)`.
-/
theorem iHat_ofA (f : A O K) : ϖ.iHat O K (ofA O K l e f) = toOD l O (ϖ.iA O K f) :=
  (ϖ.iHat_ofAl O K _).trans (ϖ.iAl_of_mem O K f.2 _)

def iSD : invL l (S O K e) →+* OD l O :=
  IsLocalization.Away.lift (l : S O K e) (g := ((crisToOD l O).comp (ϖ.iS O K)).toRingHom)
    (by rw [map_natCast]; exact isUnit_l_OD)

/- English proof (translation)
The claim follows from `IsLocalization.Away.lift_eq (S := invL l (S O K e)) (l : S O K e) (g := ((crisToOD l O).comp (ϖ.iS O K)).toRingHom) (by rw [map_natCast]; exact isUnit_l_OD) ⟨f, h⟩`.
-/
theorem iSD_of_mem {f : K⟦X⟧} (h : f ∈ S O K e) (h' : f ∈ invL l (S O K e)) :
    ϖ.iSD O K ⟨f, h'⟩ = crisToOD l O (ϖ.iS O K ⟨f, h⟩) :=
  IsLocalization.Away.lift_eq (S := invL l (S O K e)) (l : S O K e)
    (g := ((crisToOD l O).comp (ϖ.iS O K)).toRingHom) (by rw [map_natCast]; exact isUnit_l_OD) ⟨f, h⟩

variable {O}

def iD : (ZMod a → Ahat O K l e) →ₐ[O] OD l O := glue (constD t) (ϖ.iHat O K)

/- English proof (translation)
The claim follows from `(map_glue (toOD l O).toRingHom 0 (fun τ => by rw [add_zero]; rfl) fun τ => by rw [sub_zero]; exact (ϖ.iHat_ofA O K _).symm).symm`.
-/
theorem iD_ofA (f : ZMod a → A O K) : ϖ.iD t K (fun τ => ofA O K l e (f τ)) = toOD l O (ϖ.iTot t K f) :=
  (map_glue (toOD l O).toRingHom 0 (fun τ => by rw [add_zero]; rfl) fun τ => by
    rw [sub_zero]; exact (ϖ.iHat_ofA O K _).symm).symm

end PiSys

end GlobalTheory.BKReal
