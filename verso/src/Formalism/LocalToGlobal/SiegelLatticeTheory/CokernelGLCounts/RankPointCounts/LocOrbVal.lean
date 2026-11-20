import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbCut

noncomputable section

namespace Formalism.L2.SG.Pf.LocOrbCut

open MeasureTheory Formalism.MainNotions.S Formalism.L2.SG.Pf.LocOrbSumPf
open Classical

section Cast

variable {K : Type} [CommRing K]

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem sLow_cast {n n' : ℕ} (h : n' = n) (A : Matrix (Fin n) (Fin n) K) :
    Formalism.DoubleCosetMeasures.sLow (A.submatrix (finCongr h) (finCongr h)) = Formalism.DoubleCosetMeasures.sLow A := by
  subst h
  rfl

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem sUp_cast {n n' : ℕ} (h : n' = n) (A : Matrix (Fin n) (Fin n) K) :
    Formalism.DoubleCosetMeasures.sUp (A.submatrix (finCongr h) (finCongr h)) = Formalism.DoubleCosetMeasures.sUp A := by
  subst h
  rfl

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hA`.
-/
theorem lowUni_cast {n n' : ℕ} (h : n' = n) {A : Matrix (Fin n) (Fin n) K} (hA : Formalism.DoubleCosetMeasures.IsLowUni A) :
    Formalism.DoubleCosetMeasures.IsLowUni (A.submatrix (finCongr h) (finCongr h)) := by
  subst h
  exact hA

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hA`.
-/
theorem upUni_cast {n n' : ℕ} (h : n' = n) {A : Matrix (Fin n) (Fin n) K} (hA : Formalism.DoubleCosetMeasures.IsUpUni A) :
    Formalism.DoubleCosetMeasures.IsUpUni (A.submatrix (finCongr h) (finCongr h)) := by
  subst h
  exact hA

/- English proof (translation)
Simplify using `[Formalism.DoubleCosetMeasures.sLow, Matrix.one_apply, Fin.ext_iff]`.
-/
theorem sLow_one {n : ℕ} : Formalism.DoubleCosetMeasures.sLow (1 : Matrix (Fin n) (Fin n) K) = 0 := by
  simp [Formalism.DoubleCosetMeasures.sLow, Matrix.one_apply, Fin.ext_iff]

/- English proof (translation)
Simplify using `[Formalism.DoubleCosetMeasures.sUp, Matrix.one_apply, Fin.ext_iff]`.
-/
theorem sUp_one {n : ℕ} : Formalism.DoubleCosetMeasures.sUp (1 : Matrix (Fin n) (Fin n) K) = 0 := by
  simp [Formalism.DoubleCosetMeasures.sUp, Matrix.one_apply, Fin.ext_iff]

/- English proof (translation)
Unfold `Formalism.DoubleCosetMeasures.sLow`. Use `Subring.sum_mem R (fun j _ => ?_)` and prove the remaining obligations. Use `split_ifs`. Conclude with `hA _ _`. Conclude with `R.zero_mem`.
-/
theorem sLow_mem (R : Subring K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, A i j ∈ R) :
    Formalism.DoubleCosetMeasures.sLow A ∈ R := by
  unfold Formalism.DoubleCosetMeasures.sLow
  refine Subring.sum_mem R (fun j _ => ?_)
  split_ifs
  · exact hA _ _
  · exact R.zero_mem

/- English proof (translation)
Unfold `Formalism.DoubleCosetMeasures.sUp`. Use `Subring.sum_mem R (fun j _ => ?_)` and prove the remaining obligations. Use `split_ifs`. Conclude with `hA _ _`. Conclude with `R.zero_mem`.
-/
theorem sUp_mem (R : Subring K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, A i j ∈ R) :
    Formalism.DoubleCosetMeasures.sUp A ∈ R := by
  unfold Formalism.DoubleCosetMeasures.sUp
  refine Subring.sum_mem R (fun j _ => ?_)
  split_ifs
  · exact hA _ _
  · exact R.zero_mem

end Cast

section Val

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] [IsTopologicalRing E]

/- English proof (translation)
Use `⟨fun i j hij => ?_, fun a => ?_⟩` and prove the remaining obligations. Establish `h' : i < j` using `OrderDual.toDual_lt_toDual.mp hij`. Simplify using `only [Loc.uLow]`. Rewrite using `[if_neg (ne_of_lt h'), dif_neg (not_lt.mpr h'.le)]`. Simplify using `[Loc.uLow]`.
-/
theorem uLow_lowUni {n : ℕ} (x : Loc.IL n → E) : Formalism.DoubleCosetMeasures.IsLowUni (Loc.uLow x) := by
  refine ⟨fun i j hij => ?_, fun a => ?_⟩
  · have h' : i < j := OrderDual.toDual_lt_toDual.mp hij
    simp only [Loc.uLow]
    rw [if_neg (ne_of_lt h'), dif_neg (not_lt.mpr h'.le)]
  · simp [Loc.uLow]

/- English proof (translation)
Use `⟨fun i j hij => ?_, fun a => ?_⟩` and prove the remaining obligations. Establish `h' : j < i` using `hij`. Simplify using `only [Loc.uUp]`. Rewrite using `[if_neg (ne_of_gt h'), dif_neg (fun h => absurd h.1 (not_lt.mpr h'.le))]`. Simplify using `[Loc.uUp]`.
-/
theorem uUp_upUni {n : ℕ} (w : Loc.Pt E n) (y : Loc.IN w → E) : Formalism.DoubleCosetMeasures.IsUpUni (Loc.uUp w y) := by
  refine ⟨fun i j hij => ?_, fun a => ?_⟩
  · have h' : j < i := hij
    simp only [Loc.uUp]
    rw [if_neg (ne_of_gt h'), dif_neg (fun h => absurd h.1 (not_lt.mpr h'.le))]
  · simp [Loc.uUp]

def rI {m : ℕ} (a : Loc.Pt E (m + 1)) (B : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E :=
  B.submatrix (finCongr (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a)) (finCongr (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a))

/- English proof (translation)
Unfold `rI`. Rewrite using `[Matrix.submatrix_mul_equiv]`.
-/
theorem rI_mul {m : ℕ} (a : Loc.Pt E (m + 1)) (A B : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    rI a (A * B) = rI a A * rI a B := by
  unfold rI
  rw [Matrix.submatrix_mul_equiv]

/- English proof (translation)
Unfold `rI`. Rewrite using `[Formalism.MainNotions.LocalModelPeriodLattices.mat_eq]`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem rI_mat {m : ℕ} (a : Loc.Pt E (m + 1)) :
    rI a a.mat = Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 := by
  unfold rI
  rw [Formalism.MainNotions.LocalModelPeriodLattices.mat_eq]
  ext i j
  simp

/- English proof (translation)
Unfold `rI zQ`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem rI_zQ {m : ℕ} (R : Subring E) (a : Loc.Pt E (m + 1)) (q : Formalism.FourierDecayAlt.A5.Cos R (Formalism.MainNotions.LocalModelPeriodLattices.tr a)) :
    rI a (zQ R a q) = Formalism.FourierDecayAlt.A5.orbZ (Formalism.MainNotions.LocalModelPeriodLattices.tr a) (Formalism.FourierDecayAlt.A5.rep R q) := by
  unfold rI zQ
  ext i j
  simp

/- English proof (translation)
The claim follows from `lowUni_cast (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a) hA`.
-/
theorem lowUni_rI {m : ℕ} (a : Loc.Pt E (m + 1)) {A : Matrix (Fin (m + 1)) (Fin (m + 1)) E}
    (hA : Formalism.DoubleCosetMeasures.IsLowUni A) : Formalism.DoubleCosetMeasures.IsLowUni (rI a A) := lowUni_cast (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a) hA

/- English proof (translation)
The claim follows from `upUni_cast (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a) hA`.
-/
theorem upUni_rI {m : ℕ} (a : Loc.Pt E (m + 1)) {A : Matrix (Fin (m + 1)) (Fin (m + 1)) E}
    (hA : Formalism.DoubleCosetMeasures.IsUpUni A) : Formalism.DoubleCosetMeasures.IsUpUni (rI a A) := upUni_cast (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a) hA

/- English proof (translation)
The claim follows from `sLow_cast (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a) A`.
-/
theorem sLow_rI {m : ℕ} (a : Loc.Pt E (m + 1)) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    Formalism.DoubleCosetMeasures.sLow (rI a A) = Formalism.DoubleCosetMeasures.sLow A := sLow_cast (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a) A

/- English proof (translation)
The claim follows from `sUp_cast (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a) A`.
-/
theorem sUp_rI {m : ℕ} (a : Loc.Pt E (m + 1)) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    Formalism.DoubleCosetMeasures.sUp (rI a A) = Formalism.DoubleCosetMeasures.sUp A := sUp_cast (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a) A

/- English proof (translation)
Establish `hψ : ∀ x ∈ M.R, M.psiR x = 1` using `fun r hr => by`. Simplify using `using (Formalism.MainNotions.LocalModelPeriodLattices.selfDual_of_core M hOK 1).2 M.R.one_mem r hr`. Establish `hLo : Formalism.DoubleCosetMeasures.IsLowUni (rI a l * rI a (Loc.uLow xy.1))` using `Formalism.DoubleCosetMeasures.isLowUni_mul E (lowUni_rI a (lowUni_of M hl)) (lowUni_rI a (uLow_lowUni xy.1))`. Establish `hUp : Formalism.DoubleCosetMeasures.IsUpUni (rI a (Loc.uUp a xy.2) * rI a ρ)` using `Formalism.DoubleCosetMeasures.isUpUni_mul E (upUni_rI a (uUp_upUni a xy.2)) (upUni_rI a (upUni_of M hρ))`. Establish `hv : Formalism.DoubleCosetMeasures.IsLowUni (((Formalism.FourierDecayAlt.A5.rep M.R q).1 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeri …` using `(Formalism.FourierDecayAlt.A5.rep M.R q).1.2.1`.

Establish `hu : Formalism.DoubleCosetMeasures.IsUpUni (((Formalism.FourierDecayAlt.A5.rep M.R q).2 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPerio …` using `(Formalism.FourierDecayAlt.A5.rep M.R q).2.2`. Establish `hvPu : (((Formalism.FourierDecayAlt.A5.rep M.R q).1 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) * Formalis …`. Establish `h` using `congrArg (rI a) hq`. Rewrite `h` using `[rI_zQ]`. Unfold `zAt at h`.

Rewrite `h` using `[rI_mul, rI_mul, rI_mul, rI_mul, rI_mat]`. Unfold `Formalism.FourierDecayAlt.A5.orbZ at h`. Rewrite using `[h]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hLd : IsUnit (rI a l * rI a (Loc.uLow xy.1)).det` using `by rw [Formalism.DoubleCosetMeasures.isLowUni_det E hLo]; exact isUnit_one`.

Establish `hUd : IsUnit (rI a (Loc.uUp a xy.2) * rI a ρ).det` using `by rw [Formalism.DoubleCosetMeasures.isUpUni_det E hUp]; exact isUnit_one`. Establish `hfix : ((rI a l * rI a (Loc.uLow xy.1))⁻¹ * (((Formalism.FourierDecayAlt.A5.rep M.R q).1 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeri …`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = ((rI a l * rI a (Loc.uLow xy.1))⁻¹ * (rI a l * rI a (Loc.uLow xy.1))) * Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 * ((rI a (Loc.uUp a xy.2) * rI a ρ) * (rI a (Loc.uUp a xy.2 …`.

Rewrite using `[hvPu]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [Matrix.nonsing_inv_mul _ hLd, Matrix.mul_nonsing_inv _ hUd, Matrix.one_mul, Matrix.mul_one]`. Establish `h0` using `Formalism.DoubleCosetMeasures.Final.phaseWellDef E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 _ _ (Formalism.DoubleCosetMeasures.isLowUni_mul E (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hv) (Formalism.D …`. Establish `sa` using `Formalism.DoubleCosetMeasures.Final.simpleAdd E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum`.

Rewrite `h0` using `[(sa _ _).1 (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hv, (sa _ _).2 hu (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)]`. Establish `hLi` using `(sa (rI a l * rI a (Loc.uLow xy.1))⁻¹ (rI a l * rI a (Loc.uLow xy.1))).1 (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hLo`. Rewrite `hLi` using `[Matrix.nonsing_inv_mul _ hLd, sLow_one]`. Establish `hUi` using `(sa (rI a (Loc.uUp a xy.2) * rI a ρ) (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹).2 hUp (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)`. Rewrite `hUi` using `[Matrix.mul_nonsing_inv _ hUd, sUp_one]`.

Rewrite `hLi` using `[(sa _ _).1 (lowUni_rI a (lowUni_of M hl)) (lowUni_rI a (uLow_lowUni xy.1))]`. Rewrite `hUi` using `[(sa _ _).2 (upUni_rI a (uUp_upUni a xy.2)) (upUni_rI a (upUni_of M hρ))]`. Establish `hph : phQ M.R a q = Formalism.DoubleCosetMeasures.sLow (rI a l) + Formalism.DoubleCosetMeasures.sUp (rI a ρ) + (Formalism.DoubleCosetMeasures.sLow (rI a (Loc.uLow xy.1)) + Formalism.DoubleCosetMeasures.sUp (rI a (Loc.uUp a xy.2)))`. Unfold `phQ`. Take the linear combination `h0 + hLi + hUi`.

Establish `h1 : Formalism.DoubleCosetMeasures.sLow (rI a l) + Formalism.DoubleCosetMeasures.sUp (rI a ρ) ∈ M.R` using `add_mem (by rw [sLow_rI]; exact sLow_mem M.R _ hl.2.2) (by rw [sUp_rI]; exact sUp_mem M.R _ hρ.2.2)`. Rewrite using `[hph, AddChar.map_add_eq_mul, hψ _ h1, one_mul]`. Rewrite using `[sLow_rI, sUp_rI, Formalism.MainNotions.LocalOrbitGerms.Cls.simpleLow_eq, Formalism.MainNotions.LocalOrbitGerms.Cls.simpleUp_eq]`.
-/
theorem phase_eq (M : Loc.Model F E) (hOK : M.OK) {m : ℕ} (a : Loc.Pt E (m + 1))
    (q : Formalism.FourierDecayAlt.A5.Cos M.R (Formalism.MainNotions.LocalModelPeriodLattices.tr a)) (xy : (Loc.IL (m + 1) → E) × (Loc.IN a → E))
    (l ρ : Matrix (Fin (m + 1)) (Fin (m + 1)) E) (hl : Formalism.MainNotions.S.TieN.IntLow M l) (hρ : Formalism.MainNotions.S.TieN.IntUp M ρ)
    (hq : zQ M.R a q = l * zAt a xy * ρ) :
    M.psiR (phQ M.R a q) = M.psiR (Loc.simpleLow (Loc.uLow xy.1) + Loc.simpleUp (Loc.uUp a xy.2)) := by
  have hψ : ∀ x ∈ M.R, M.psiR x = 1 := fun r hr => by
    simpa using (Formalism.MainNotions.LocalModelPeriodLattices.selfDual_of_core M hOK 1).2 M.R.one_mem r hr
  have hLo : Formalism.DoubleCosetMeasures.IsLowUni (rI a l * rI a (Loc.uLow xy.1)) :=
    Formalism.DoubleCosetMeasures.isLowUni_mul E (lowUni_rI a (lowUni_of M hl)) (lowUni_rI a (uLow_lowUni xy.1))
  have hUp : Formalism.DoubleCosetMeasures.IsUpUni (rI a (Loc.uUp a xy.2) * rI a ρ) :=
    Formalism.DoubleCosetMeasures.isUpUni_mul E (upUni_rI a (uUp_upUni a xy.2)) (upUni_rI a (upUni_of M hρ))
  have hv : Formalism.DoubleCosetMeasures.IsLowUni (((Formalism.FourierDecayAlt.A5.rep M.R q).1 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) := (Formalism.FourierDecayAlt.A5.rep M.R q).1.2.1
  have hu : Formalism.DoubleCosetMeasures.IsUpUni (((Formalism.FourierDecayAlt.A5.rep M.R q).2 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) := (Formalism.FourierDecayAlt.A5.rep M.R q).2.2
  have hvPu : (((Formalism.FourierDecayAlt.A5.rep M.R q).1 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) *
      Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 * (((Formalism.FourierDecayAlt.A5.rep M.R q).2 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) =
      (rI a l * rI a (Loc.uLow xy.1)) * Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
        (rI a (Loc.uUp a xy.2) * rI a ρ) := by
    have h := congrArg (rI a) hq
    rw [rI_zQ] at h
    unfold zAt at h
    rw [rI_mul, rI_mul, rI_mul, rI_mul, rI_mat] at h
    unfold Formalism.FourierDecayAlt.A5.orbZ at h
    rw [h]
    simp only [Matrix.mul_assoc]
  have hLd : IsUnit (rI a l * rI a (Loc.uLow xy.1)).det := by rw [Formalism.DoubleCosetMeasures.isLowUni_det E hLo]; exact isUnit_one
  have hUd : IsUnit (rI a (Loc.uUp a xy.2) * rI a ρ).det := by rw [Formalism.DoubleCosetMeasures.isUpUni_det E hUp]; exact isUnit_one
  have hfix : ((rI a l * rI a (Loc.uLow xy.1))⁻¹ * (((Formalism.FourierDecayAlt.A5.rep M.R q).1 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E)) *
      Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
      ((((Formalism.FourierDecayAlt.A5.rep M.R q).2 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) * (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹) =
      Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 := by
    calc _ = (rI a l * rI a (Loc.uLow xy.1))⁻¹ * ((((Formalism.FourierDecayAlt.A5.rep M.R q).1 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) *
          Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
          (((Formalism.FourierDecayAlt.A5.rep M.R q).2 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E)) * (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = ((rI a l * rI a (Loc.uLow xy.1))⁻¹ * (rI a l * rI a (Loc.uLow xy.1))) *
          Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
          ((rI a (Loc.uUp a xy.2) * rI a ρ) * (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹) := by
          rw [hvPu]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.nonsing_inv_mul _ hLd, Matrix.mul_nonsing_inv _ hUd, Matrix.one_mul, Matrix.mul_one]
  have h0 := Formalism.DoubleCosetMeasures.Final.phaseWellDef E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 _ _
    (Formalism.DoubleCosetMeasures.isLowUni_mul E (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hv) (Formalism.DoubleCosetMeasures.isUpUni_mul E hu (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)) hfix
  have sa := Formalism.DoubleCosetMeasures.Final.simpleAdd E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum
  rw [(sa _ _).1 (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hv, (sa _ _).2 hu (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)] at h0
  have hLi := (sa (rI a l * rI a (Loc.uLow xy.1))⁻¹ (rI a l * rI a (Loc.uLow xy.1))).1
    (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hLo
  rw [Matrix.nonsing_inv_mul _ hLd, sLow_one] at hLi
  have hUi := (sa (rI a (Loc.uUp a xy.2) * rI a ρ) (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹).2
    hUp (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)
  rw [Matrix.mul_nonsing_inv _ hUd, sUp_one] at hUi
  rw [(sa _ _).1 (lowUni_rI a (lowUni_of M hl)) (lowUni_rI a (uLow_lowUni xy.1))] at hLi
  rw [(sa _ _).2 (upUni_rI a (uUp_upUni a xy.2)) (upUni_rI a (upUni_of M hρ))] at hUi
  have hph : phQ M.R a q = Formalism.DoubleCosetMeasures.sLow (rI a l) + Formalism.DoubleCosetMeasures.sUp (rI a ρ) +
      (Formalism.DoubleCosetMeasures.sLow (rI a (Loc.uLow xy.1)) + Formalism.DoubleCosetMeasures.sUp (rI a (Loc.uUp a xy.2))) := by
    unfold phQ
    linear_combination h0 + hLi + hUi
  have h1 : Formalism.DoubleCosetMeasures.sLow (rI a l) + Formalism.DoubleCosetMeasures.sUp (rI a ρ) ∈ M.R :=
    add_mem (by rw [sLow_rI]; exact sLow_mem M.R _ hl.2.2) (by rw [sUp_rI]; exact sUp_mem M.R _ hρ.2.2)
  rw [hph, AddChar.map_add_eq_mul, hψ _ h1, one_mul]
  rw [sLow_rI, sUp_rI, Formalism.MainNotions.LocalOrbitGerms.Cls.simpleLow_eq, Formalism.MainNotions.LocalOrbitGerms.Cls.simpleUp_eq]

/- English proof (translation)
Substitute `hZ` using the available equality. Unfold `Loc.Model.nIso`. Rewrite using `[Nat.card_congr (Formalism.MainNotions.LocalOrbitGerms.Cls.isoEquiv M _ Z0), Nat.card_congr (Formalism.MainNotions.LocalOrbitGerms.Cls.isoEquiv M _ Z0), Formalism.MainNotions.LocalOrbitGerms.Cls.toMat_map, Formalism.MainNotions.LocalOrbitGerms.Cls.toMat_map]`. Conclude with `Formalism.DoubleCosetMeasures.Final.isoInv E M.R (n + 1) l ρ Z (lowUni_of M hl) (upUni_of M hρ) hl.2.2 hρ.2.2 _ _ _`.
-/
theorem nIso_orb (M : Loc.Model F E) {n : ℕ} {Z Z' : Matrix (Fin (n + 1)) (Fin (n + 1)) E}
    (l ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hl : Formalism.MainNotions.S.TieN.IntLow M l) (hρ : Formalism.MainNotions.S.TieN.IntUp M ρ)
    (hZ : Z' = l * Z * ρ) (h1 : ∀ i j, Z' i j ∈ M.R) (h2 : IsUnit Z'.det) (h1' : ∀ i j, Z i j ∈ M.R)
    (h2' : IsUnit Z.det) (Z0 : M.Mat (n + 1)) :
    M.nIso (Formalism.MainNotions.LocalOrbitGerms.Cls.toMat M Z' h1 h2) Z0 = M.nIso (Formalism.MainNotions.LocalOrbitGerms.Cls.toMat M Z h1' h2') Z0 := by
  subst hZ
  unfold Loc.Model.nIso
  rw [Nat.card_congr (Formalism.MainNotions.LocalOrbitGerms.Cls.isoEquiv M _ Z0), Nat.card_congr (Formalism.MainNotions.LocalOrbitGerms.Cls.isoEquiv M _ Z0),
    Formalism.MainNotions.LocalOrbitGerms.Cls.toMat_map, Formalism.MainNotions.LocalOrbitGerms.Cls.toMat_map]
  exact Formalism.DoubleCosetMeasures.Final.isoInv E M.R (n + 1) l ρ Z (lowUni_of M hl) (upUni_of M hρ) hl.2.2 hρ.2.2 _ _ _

/- English proof (translation)
Introduce `q xy hI hmem`. Take `⟨l, ρ, hl, hρ, hq⟩` from `hmem`. Establish `hIq : ∀ i j, zQ M.R a q i j ∈ M.R` using `int_of_mem M hI ⟨l, ρ, hl, hρ, hq⟩`. Establish `hdq : IsUnit (zQ M.R a q).det` using `Formalism.MainNotions.LocalOrbitGerms.Cls.isUnit_det_sub a _`. Establish `hI' : ∀ i j, (Loc.uLow xy.1 * a.mat * Loc.uUp a xy.2) i j ∈ M.R` using `hI`.

Establish `hdz : IsUnit (Loc.uLow xy.1 * a.mat * Loc.uUp a xy.2).det`. Rewrite using `[Matrix.det_mul, Matrix.det_mul, Formalism.L2.SG.Pf.LocModel.uLow_det, Formalism.L2.SG.Pf.LocModel.uUp_det, one_mul, mul_one, Formalism.MainNotions.LocalModelPeriodLattices.det_eq]`. Conclude with `Formalism.FourierDecayAlt.P.A5x6.pt_det_isUnit _`. Rewrite using `[Formalism.MainNotions.LocalOrbitGerms.Cls.bbIntegrand_eq]`. Unfold `valQ Formalism.MainNotions.LocalOrbitGerms.Cls.GG`.

Rewrite using `[dif_pos ⟨hIq, hdq⟩, dif_pos ⟨hI', hdz⟩, phase_eq M hOK a q xy l ρ hl hρ hq, nIso_orb M l ρ hl hρ hq hIq hdq hI' hdz]`. Both sides reduce to the same expression.
-/
theorem val (M : Loc.Model F E) (hOK : M.OK) {m : ℕ} (a : Loc.Pt E (m + 1)) (c : M.Cls m) : IntegrandConstantOnOrbit M a c := by
  intro q xy hI hmem
  obtain ⟨l, ρ, hl, hρ, hq⟩ := hmem
  have hIq : ∀ i j, zQ M.R a q i j ∈ M.R := int_of_mem M hI ⟨l, ρ, hl, hρ, hq⟩
  have hdq : IsUnit (zQ M.R a q).det := Formalism.MainNotions.LocalOrbitGerms.Cls.isUnit_det_sub a _
  have hI' : ∀ i j, (Loc.uLow xy.1 * a.mat * Loc.uUp a xy.2) i j ∈ M.R := hI
  have hdz : IsUnit (Loc.uLow xy.1 * a.mat * Loc.uUp a xy.2).det := by
    rw [Matrix.det_mul, Matrix.det_mul, Formalism.L2.SG.Pf.LocModel.uLow_det, Formalism.L2.SG.Pf.LocModel.uUp_det, one_mul,
      mul_one, Formalism.MainNotions.LocalModelPeriodLattices.det_eq]
    exact Formalism.FourierDecayAlt.P.A5x6.pt_det_isUnit _
  rw [Formalism.MainNotions.LocalOrbitGerms.Cls.bbIntegrand_eq]
  unfold valQ Formalism.MainNotions.LocalOrbitGerms.Cls.GG
  rw [dif_pos ⟨hIq, hdq⟩, dif_pos ⟨hI', hdz⟩, phase_eq M hOK a q xy l ρ hl hρ hq,
    nIso_orb M l ρ hl hρ hq hIq hdq hI' hdz]
  rfl

end Val

end Formalism.L2.SG.Pf.LocOrbCut
