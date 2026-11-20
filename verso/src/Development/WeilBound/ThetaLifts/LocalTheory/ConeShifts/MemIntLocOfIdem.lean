import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ExistsPowIdem
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Vaceigen
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Inertof
import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasAd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone.Vf

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open PositivityTheory.ThK PositivityTheory.ThK.Vac PositivityTheory.ThKH.Iwas GlobalTheory.Doubling

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {v : Pl F}

/- English proof (translation)
Establish `e0 : ∀ (a : AF F) (x : E), a • inclR (F` using `F) (AF F) x = a ⊗ₜ[F] x := fun a x => by`. Express the relevant statement in the definitionally equal form `(a * 1) ⊗ₜ[F] x = _`. Rewrite using `[mul_one]`. Establish `key : ∀ y ∈ latW W v, At (evFin F v) y ∧ compFin F E v ∘ y ∈ latLoc F W.L v` using `fun y hy => by`. Proceed by induction on `hy using AddSubgroup.closure_induction with`.

Consider the case `mem y hy`. Take `⟨a, ha, ha', x, hx, rfl⟩` from `hy`. Use `⟨fun u hu => funext fun i => ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `u • a • inclR (F := F) (AF F) (x i) = 0`. Rewrite using `[smul_smul, show u * a = 0 from ha u hu, zero_smul]`.

Use `tmul_mem_latLoc ha' hx using 1` and compare the differences between its conclusion and the goal. Conclude with `funext fun i => congrArg (compFin F E v) (e0 a (x i))`. Consider the case `zero`. Use `⟨at_zero, ?_⟩` and prove the remaining obligations. Use `zero_mem (latLoc F W.L v) using 1` and compare the differences between its conclusion and the goal.

Conclude with `funext fun i => map_zero _`. Consider the case `add y z _ _ hy hz`. Use `⟨at_add hy.1 hz.1, ?_⟩` and prove the remaining obligations. Use `add_mem hy.2 hz.2 using 1` and compare the differences between its conclusion and the goal. Conclude with `funext fun i => map_add _ _ _`.

Consider the case `neg y _ hy`. Use `⟨by simpa using at_sub at_zero hy.1, ?_⟩` and prove the remaining obligations. Use `neg_mem hy.2 using 1` and compare the differences between its conclusion and the goal. Conclude with `funext fun i => map_neg _ _`. Establish `key' : ∀ z ∈ latLoc F W.L v, (fun i => sgE E v (z i)) ∈ latW W v` using `fun z hz => by`.

Use `latLoc_induction (p := fun z => (fun i => sgE E v (z i)) ∈ latW W v) (fun a ha x hx => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hz` and prove the remaining obligations. Conclude with `AddSubgroup.subset_closure ⟨sg v a, at_sg a, by rwa [ev_sg], x, hx, funext fun i => (e0 _ _).symm⟩`. Use `zero_mem (latW W v) using 1` and compare the differences between its conclusion and the goal. Conclude with `funext fun i => map_zero _`. Use `add_mem hy hz using 1` and compare the differences between its conclusion and the goal.

Conclude with `funext fun i => map_add _ _ _`. Use `neg_mem hy using 1` and compare the differences between its conclusion and the goal. Conclude with `funext fun i => map_neg _ _`. Use `⟨key y, fun hy => ?_⟩` and prove the remaining obligations. Use `key' _ hy.2 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i`. Use `sub_eq_zero.1 (eq_zero_of_at (v := v) (at_sub (fun u hu => congrFun (hy.1 u hu) i) (at_sgE _)) ?_)` and prove the remaining obligations. Rewrite using `[map_sub, comp_sgE]`. Conclude with `sub_self _`.
-/
theorem mem_latW_loc (W : Spc F E n) (y : Fin n → AE F E) :
    y ∈ latW W v ↔ At (evFin F v) y ∧ compFin F E v ∘ y ∈ latLoc F W.L v := by
  have e0 : ∀ (a : AF F) (x : E), a • inclR (F := F) (AF F) x = a ⊗ₜ[F] x := fun a x => by
    change (a * 1) ⊗ₜ[F] x = _
    rw [mul_one]
  have key : ∀ y ∈ latW W v, At (evFin F v) y ∧ compFin F E v ∘ y ∈ latLoc F W.L v := fun y hy => by
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, ha', x, hx, rfl⟩ := hy
      refine ⟨fun u hu => funext fun i => ?_, ?_⟩
      · change u • a • inclR (F := F) (AF F) (x i) = 0
        rw [smul_smul, show u * a = 0 from ha u hu, zero_smul]
      · convert tmul_mem_latLoc ha' hx using 1
        exact funext fun i => congrArg (compFin F E v) (e0 a (x i))
    | zero =>
      refine ⟨at_zero, ?_⟩
      convert zero_mem (latLoc F W.L v) using 1
      exact funext fun i => map_zero _
    | add y z _ _ hy hz =>
      refine ⟨at_add hy.1 hz.1, ?_⟩
      convert add_mem hy.2 hz.2 using 1
      exact funext fun i => map_add _ _ _
    | neg y _ hy =>
      refine ⟨by simpa using at_sub at_zero hy.1, ?_⟩
      convert neg_mem hy.2 using 1
      exact funext fun i => map_neg _ _
  have key' : ∀ z ∈ latLoc F W.L v, (fun i => sgE E v (z i)) ∈ latW W v := fun z hz => by
    refine latLoc_induction (p := fun z => (fun i => sgE E v (z i)) ∈ latW W v) (fun a ha x hx => ?_) ?_
      (fun y z hy hz => ?_) (fun y hy => ?_) hz
    · exact AddSubgroup.subset_closure ⟨sg v a, at_sg a, by rwa [ev_sg], x, hx, funext fun i => (e0 _ _).symm⟩
    · convert zero_mem (latW W v) using 1
      exact funext fun i => map_zero _
    · convert add_mem hy hz using 1
      exact funext fun i => map_add _ _ _
    · convert neg_mem hy using 1
      exact funext fun i => map_neg _ _
  refine ⟨key y, fun hy => ?_⟩
  convert key' _ hy.2 using 1
  funext i
  refine sub_eq_zero.1 (eq_zero_of_at (v := v) (at_sub (fun u hu => congrFun (hy.1 u hu) i) (at_sgE _)) ?_)
  rw [map_sub, comp_sgE]; exact sub_self _

variable (v) in

def Pres (X : Spc F E n) : Subring (Matrix (Fin n) (Fin n) (AE F E)) where
  carrier := {M | ∀ y ∈ latW X v, M *ᵥ y ∈ latW X v}
  one_mem' y hy := by rwa [Matrix.one_mulVec]
  zero_mem' y _ := by rw [Matrix.zero_mulVec]; exact zero_mem _
  add_mem' ha hb y hy := by rw [Matrix.add_mulVec]; exact add_mem (ha y hy) (hb y hy)
  mul_mem' ha hb y hy := by rw [← Matrix.mulVec_mulVec]; exact ha _ (hb y hy)
  neg_mem' ha y hy := by rw [Matrix.neg_mulVec]; exact neg_mem (ha y hy)

variable (v) in

def fr (a : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (AE F E) →+* Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) where
  toFun M := (a⁻¹).1 * M.map (compFin F E v) * a.1
  map_one' := by rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Units.inv_mul]
  map_zero' := by rw [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul]
  map_add' M N := by rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]
  map_mul' M N := by rw [Matrix.map_mul]; simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fr_apply (a : GL (Fin n) (Fv F v ⊗[F] E)) (M) : fr v a M = (a⁻¹).1 * M.map (compFin F E v) * a.1 := rfl

/- English proof (translation)
Rewrite using `[fr_apply, Matrix.det_units_conj', RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem fr_det (a : GL (Fin n) (Fv F v ⊗[F] E)) (M) : (fr v a M).det = compFin F E v M.det := by
  rw [fr_apply, Matrix.det_units_conj', RingHom.map_det]; rfl

/- English proof (translation)
Rewrite using `[fr_apply, fr_apply, ← Matrix.smul_mul, ← Matrix.mul_smul]`. Use `congr 2`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem fr_smul (a : GL (Fin n) (Fv F v ⊗[F] E)) (z : AE F E) (M) : fr v a (z • M) = compFin F E v z • fr v a M := by
  rw [fr_apply, fr_apply, ← Matrix.smul_mul, ← Matrix.mul_smul]
  congr 2
  ext i j; simp

/- English proof (translation)
Take `⟨P, h1, h2⟩` from `Frames.exists_rational_frame X.L v`. Establish `ha` using `Frames.frame_of_rational P h1 h2`. Use `set a : GL (Fin n) (Fv F v ⊗[F] E) := bc (inclR (F := F) (Fv F v)) P`. Establish `mv : ∀ (M : Matrix (Fin n) (Fin n) (AE F E)) y, compFin F E v ∘ (M *ᵥ y) = M.map (compFin F E v) *ᵥ (compFin F E v ∘ y)` using `fun M y => funext fun i => RingHom.map_mulVec _ M y i`. Establish `co : ∀ z ∈ latLoc F X.L v, ∀ i, ((a⁻¹).1 *ᵥ z) i ∈ intLoc F E v` using `fun z hz => (ha _).2 (by rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec])`.

Use `⟨a, fun M => ⟨fun hM => ?_, ?_⟩⟩` and prove the remaining obligations. Establish `: ∀ i j, fr v a M i j ∈ intLoc F E v` using `fun i j => by`. Set `z` to `a.1 *ᵥ fun k => (1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) k j`. Establish `hz : z ∈ latLoc F X.L v` using `(ha _).1 fun k => by`. Rewrite using `[Matrix.one_apply]`.

Use `split_ifs`. Use `exacts [one_mem _, zero_mem _]`. Establish `ey : compFin F E v ∘ (fun i => sgE E v (z i)) = z` using `funext fun i => comp_sgE _`. Establish `h1` using `((mem_latW_loc X _).1 (hM _ ((mem_latW_loc X (fun i => sgE E v (z i))).2 ⟨fun u hu => funext fun i => at_sgE _ u hu, ey.symm ▸ hz⟩))).2`. Establish `h2` using `co _ h1 i`.

Rewrite `h2` using `[mv, ey, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`. Express the relevant statement in the definitionally equal form `(fr v a M * 1 : Matrix _ _ _) i j ∈ _ at h2`. Rewrite `h2` using `[Matrix.mul_one]`. Then use the resulting hypothesis. Conclude with `⟨fun i j => ⟨_, this i j⟩, rfl⟩`. Introduce and unpack `⟨N, hN⟩ y hy`.

Take `⟨h1, h2⟩` from `(mem_latW_loc X y).1 hy`. Use `(mem_latW_loc X _).2 ⟨at_mulVec_right _ h1, ?_⟩` and prove the remaining obligations. Use `(ha (fr v a M *ᵥ ((a⁻¹).1 *ᵥ (compFin F E v ∘ y)))).1 fun i => by` as an intermediate fact. Rewrite using `[← hN]`. Conclude with `sum_mem (t := Finset.univ) (f := fun j => (N i j).1 * ((a⁻¹).1 *ᵥ (compFin F E v ∘ y)) j) fun j _ => mul_mem (N i j).2 (co _ h2 j)`.

Rewrite `this` using `[fr_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← mv]`. Then use the resulting hypothesis.
-/
theorem exists_fr (X : Spc F E n) (hL : X.L.IsLattice E) : ∃ a : GL (Fin n) (Fv F v ⊗[F] E),
    ∀ M, M ∈ Pres v X ↔ ∃ N : Matrix (Fin n) (Fin n) (intLoc F E v), (intLoc F E v).subtype.mapMatrix N = fr v a M := by
  obtain ⟨P, h1, h2⟩ := Frames.exists_rational_frame X.L v
  have ha := Frames.frame_of_rational P h1 h2
  set a : GL (Fin n) (Fv F v ⊗[F] E) := bc (inclR (F := F) (Fv F v)) P
  have mv : ∀ (M : Matrix (Fin n) (Fin n) (AE F E)) y, compFin F E v ∘ (M *ᵥ y) = M.map (compFin F E v) *ᵥ (compFin F E v ∘ y) :=
    fun M y => funext fun i => RingHom.map_mulVec _ M y i
  have co : ∀ z ∈ latLoc F X.L v, ∀ i, ((a⁻¹).1 *ᵥ z) i ∈ intLoc F E v := fun z hz =>
    (ha _).2 (by rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec])
  refine ⟨a, fun M => ⟨fun hM => ?_, ?_⟩⟩
  · have : ∀ i j, fr v a M i j ∈ intLoc F E v := fun i j => by
      let z := a.1 *ᵥ fun k => (1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) k j
      have hz : z ∈ latLoc F X.L v := (ha _).1 fun k => by
        rw [Matrix.one_apply]; split_ifs
        exacts [one_mem _, zero_mem _]
      have ey : compFin F E v ∘ (fun i => sgE E v (z i)) = z := funext fun i => comp_sgE _
      have h1 := ((mem_latW_loc X _).1 (hM _ ((mem_latW_loc X (fun i => sgE E v (z i))).2
        ⟨fun u hu => funext fun i => at_sgE _ u hu, ey.symm ▸ hz⟩))).2
      have h2 := co _ h1 i
      rw [mv, ey, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at h2
      change (fr v a M * 1 : Matrix _ _ _) i j ∈ _ at h2
      rwa [Matrix.mul_one] at h2
    exact ⟨fun i j => ⟨_, this i j⟩, rfl⟩
  · rintro ⟨N, hN⟩ y hy
    obtain ⟨h1, h2⟩ := (mem_latW_loc X y).1 hy
    refine (mem_latW_loc X _).2 ⟨at_mulVec_right _ h1, ?_⟩
    have := (ha (fr v a M *ᵥ ((a⁻¹).1 *ᵥ (compFin F E v ∘ y)))).1 fun i => by
      rw [← hN]
      exact sum_mem (t := Finset.univ) (f := fun j => (N i j).1 * ((a⁻¹).1 *ᵥ (compFin F E v ∘ y)) j)
        fun j _ => mul_mem (N i j).2 (co _ h2 j)
    rwa [fr_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv,
      Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← mv] at this

/- English proof (translation)
Take `⟨a, ha⟩` from `exists_fr (v := v) X hL`. Take `⟨N, hN⟩` from `(ha M).1 hM`. Use `(ha _).2 ⟨(⟨_, hz⟩ : intLoc F E v) • N, ?_⟩` and prove the remaining obligations. Rewrite using `[fr_smul, ← hN]`. Use extensionality with `i j`.

Both sides reduce to the same expression.
-/
theorem smul_mem_Pres {X : Spc F E n} (hL : X.L.IsLattice E) {z : AE F E} (hz : compFin F E v z ∈ intLoc F E v) {M}
    (hM : M ∈ Pres v X) : z • M ∈ Pres v X := by
  obtain ⟨a, ha⟩ := exists_fr (v := v) X hL
  obtain ⟨N, hN⟩ := (ha M).1 hM
  refine (ha _).2 ⟨(⟨_, hz⟩ : intLoc F E v) • N, ?_⟩
  rw [fr_smul, ← hN]; ext i j; rfl

/- English proof (translation)
Set `I : Ideal (AE F E)` to `{ carrier := {z | At (evFin F v) z} add_mem' := at_add zero_mem' := at_zero smul_mem' := fun c z hz u hu => by rw [smul_eq_mul, ← mul_smul_comm, hz u hu, mul_zero] }`. Establish `: (Ideal.Quotient.mk I).mapMatrix M = 1`. Rewrite using `[← map_one (Ideal.Quotient.mk I).mapMatrix]`. Use extensionality with `i j`. Conclude with `Ideal.Quotient.eq.2 fun u hu => congrFun (congrFun (hM u hu) i) j`.

Establish `h2 : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I 1` using `by rw [RingHom.map_det, this, Matrix.det_one, map_one]`. Conclude with `Ideal.Quotient.eq.1 h2`.
-/
theorem at_det {M : Matrix (Fin n) (Fin n) (AE F E)} (hM : At (evFin F v) (M - 1)) : At (evFin F v) (M.det - 1) := by
  let I : Ideal (AE F E) :=
    { carrier := {z | At (evFin F v) z}
      add_mem' := at_add
      zero_mem' := at_zero
      smul_mem' := fun c z hz u hu => by rw [smul_eq_mul, ← mul_smul_comm, hz u hu, mul_zero] }
  have : (Ideal.Quotient.mk I).mapMatrix M = 1 := by
    rw [← map_one (Ideal.Quotient.mk I).mapMatrix]
    ext i j
    exact Ideal.Quotient.eq.2 fun u hu => congrFun (congrFun (hM u hu) i) j
  have h2 : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I 1 := by rw [RingHom.map_det, this, Matrix.det_one, map_one]
  exact Ideal.Quotient.eq.1 h2

/- English proof (translation)
Introduce `u hu` and use `by rw [← mul_smul_comm, hz u hu, mul_zero]`.
-/
theorem at_mul_l {z : AE F E} (hz : At (evFin F v) z) (y : AE F E) : At (evFin F v) (y * z) := fun u hu => by
  rw [← mul_smul_comm, hz u hu, mul_zero]

/- English proof (translation)
Use `sub_eq_zero.1 (eq_zero_of_at (v := v) ?_ ?_)` and prove the remaining obligations. Rewrite using `[show z - (1 - sgE E v 1 + sgE E v (compFin F E v z)) = (z - 1) + sgE E v 1 - sgE E v (compFin F E v z) by ring]`. Conclude with `at_sub (at_add hz (at_sgE _)) (at_sgE _)`. Simplify using `[comp_sgE]`.
-/
theorem eq_ext {z : AE F E} (hz : At (evFin F v) (z - 1)) : z = 1 - sgE E v 1 + sgE E v (compFin F E v z) := by
  refine sub_eq_zero.1 (eq_zero_of_at (v := v) ?_ ?_)
  · rw [show z - (1 - sgE E v 1 + sgE E v (compFin F E v z)) = (z - 1) + sgE E v 1 - sgE E v (compFin F E v z) by ring]
    exact at_sub (at_add hz (at_sgE _)) (at_sgE _)
  · simp [comp_sgE]

/- English proof (translation)
Take `⟨a, ha⟩` from `exists_fr (v := v) X hL`. Establish `hd : ∀ M ∈ Pres v X, compFin F E v M.det ∈ intLoc F E v` using `fun M hM => by`. Take `⟨N, hN⟩` from `(ha M).1 hM`. Rewrite using `[← fr_det a, ← hN, ← RingHom.map_det]`. Conclude with `N.det.2`.

Establish `e : Matrix.GeneralLinearGroup.det t = ideleAt F E v (unitFin F E v (Matrix.GeneralLinearGroup.det t))` using `Units.ext (eq_ext (at_det h3))`. Rewrite using `[e]`. Use `charAt_eq_one_of_unrAt χ v _ (hd _ h1) ?_ hχ` and prove the remaining obligations. Rewrite using `[← map_inv, ← map_inv]`. Conclude with `hd _ h2`.
-/
theorem chi_det {X : Spc F E n} (hL : X.L.IsLattice E) (χ : Chr F E)
    (hχ : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χ w) (t : GL (Fin n) (AE F E))
    (h1 : t.1 ∈ Pres v X) (h2 : (t⁻¹).1 ∈ Pres v X) (h3 : At (evFin F v) (t.1 - 1)) :
    χ (Matrix.GeneralLinearGroup.det t) = 1 := by
  obtain ⟨a, ha⟩ := exists_fr (v := v) X hL
  have hd : ∀ M ∈ Pres v X, compFin F E v M.det ∈ intLoc F E v := fun M hM => by
    obtain ⟨N, hN⟩ := (ha M).1 hM
    rw [← fr_det a, ← hN, ← RingHom.map_det]; exact N.det.2
  have e : Matrix.GeneralLinearGroup.det t = ideleAt F E v (unitFin F E v (Matrix.GeneralLinearGroup.det t)) :=
    Units.ext (eq_ext (at_det h3))
  rw [e]
  refine charAt_eq_one_of_unrAt χ v _ (hd _ h1) ?_ hχ
  rw [← map_inv, ← map_inv]
  exact hd _ h2

/- English proof (translation)
Take `⟨w, hw⟩` from `hu.exists_right_inv`. Establish `hw' : compFin F E v f.det * w.1 = 1`. Rewrite using `[← fr_det a, ← hN, ← RingHom.map_det]`. Conclude with `congrArg Subtype.val hw`. Establish `hD : f.det * (1 - sgE E v 1 + sgE E v w.1) = 1`.

Use `sub_eq_zero.1 (eq_zero_of_at (v := v) ?_ ?_)` and prove the remaining obligations. Rewrite using `[show f.det * (1 - sgE E v 1 + sgE E v w.1) - 1 = (f.det - 1) - f.det * sgE E v 1 + f.det * sgE E v w.1 by ring]`. Conclude with `at_add (at_sub (at_det h3) (at_mul_l (at_sgE _) _)) (at_mul_l (at_sgE _) _)`. Simplify using `[comp_sgE, hw']`. Establish `hf` using `Matrix.mul_nonsing_inv f (IsUnit.of_mul_eq_one _ hD)`.

Use `⟨f⁻¹, (ha _).2 ⟨N⁻¹, ?_⟩, hf⟩` and prove the remaining obligations. Establish `e1 : fr v a f⁻¹ * fr v a f = 1` using `by rw [← map_mul, mul_eq_one_comm.1 hf, map_one]`. Rewrite using `[← Matrix.one_mul ((intLoc F E v).subtype.mapMatrix N⁻¹), ← e1, Matrix.mul_assoc, ← hN, ← map_mul, Matrix.mul_nonsing_inv N hu, map_one, Matrix.mul_one]`.
-/
theorem exists_inv {X : Spc F E n} {a : GL (Fin n) (Fv F v ⊗[F] E)}
    (ha : ∀ M, M ∈ Pres v X ↔ ∃ N : Matrix (Fin n) (Fin n) (intLoc F E v), (intLoc F E v).subtype.mapMatrix N = fr v a M)
    {f : Matrix (Fin n) (Fin n) (AE F E)} (h3 : At (evFin F v) (f - 1)) {N : Matrix (Fin n) (Fin n) (intLoc F E v)}
    (hN : (intLoc F E v).subtype.mapMatrix N = fr v a f) (hu : IsUnit N.det) : ∃ f' ∈ Pres v X, f * f' = 1 := by
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have hw' : compFin F E v f.det * w.1 = 1 := by
    rw [← fr_det a, ← hN, ← RingHom.map_det]; exact congrArg Subtype.val hw
  have hD : f.det * (1 - sgE E v 1 + sgE E v w.1) = 1 := by
    refine sub_eq_zero.1 (eq_zero_of_at (v := v) ?_ ?_)
    · rw [show f.det * (1 - sgE E v 1 + sgE E v w.1) - 1 = (f.det - 1) - f.det * sgE E v 1 + f.det * sgE E v w.1 by ring]
      exact at_add (at_sub (at_det h3) (at_mul_l (at_sgE _) _)) (at_mul_l (at_sgE _) _)
    · simp [comp_sgE, hw']
  have hf := Matrix.mul_nonsing_inv f (IsUnit.of_mul_eq_one _ hD)
  refine ⟨f⁻¹, (ha _).2 ⟨N⁻¹, ?_⟩, hf⟩
  have e1 : fr v a f⁻¹ * fr v a f = 1 := by rw [← map_mul, mul_eq_one_comm.1 hf, map_one]
  rw [← Matrix.one_mul ((intLoc F E v).subtype.mapMatrix N⁻¹), ← e1, Matrix.mul_assoc, ← hN, ← map_mul,
    Matrix.mul_nonsing_inv N hu, map_one, Matrix.mul_one]

/- English proof (translation)
Set `Y : Af F ⊗[F] E` to `TensorProduct.map (singleFin v) LinearMap.id y`. Establish `ev : ∀ u (y : Fv F v ⊗[F] E), Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u) (AlgHom.id F E) (TensorProduct.map (singleFin v) LinearMap.id y) = compFin F E u (sgE E v y)` using `fun u y => by`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => rfl`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `hi : sgE E v y * sgE E v y = sgE E v y`. Use `sub_eq_zero.1 (eq_zero_of_at (v := v) (at_sub (at_mul_l (at_sgE _) _) (at_sgE _)) ?_)` and prove the remaining obligations. Simplify using `[comp_sgE, hy]`. Establish `hY` using `(mem_int_iff Y).2 fun P => by`.

Rewrite using `[finAdEquiv_apply rfl, ev]`. Use `set z := toCompl (rfl : P.under (𝓞 F) = _) (compFin F E _ (sgE E v y))`. Establish `hz : z * z = z` using `by rw [← map_mul, ← map_mul, hi]`. Break down `eq_or_ne z 0 with h | h` into its components or cases. Rewrite using `[h, map_zero]`.

Conclude with `zero_le_one`. Rewrite using `[mul_right_cancel₀ h (hz.trans (one_mul z).symm), map_one]`. Establish `: ∀ Z ∈ AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) Z ∈ intLoc F E v` using `fun Z hZ => by`. Proceed by induction on `hZ using AddSubgroup.closure_induction with`. Consider the case `mem Z hZ`.

Take `⟨a, ha, x, rfl⟩` from `hZ`. Conclude with `AddSubgroup.subset_closure ⟨_, ha v, x, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [map_neg]`. Conclude with `neg_mem hx`. Use `this Y hY` as an intermediate fact. Rewrite `this` using `[ev, comp_sgE]`. Then use the resulting hypothesis.
-/
theorem mem_intLoc_of_idem {y : Fv F v ⊗[F] E} (hy : y * y = y) : y ∈ intLoc F E v := by
  let Y : Af F ⊗[F] E := TensorProduct.map (singleFin v) LinearMap.id y
  have ev : ∀ u (y : Fv F v ⊗[F] E), Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u) (AlgHom.id F E)
      (TensorProduct.map (singleFin v) LinearMap.id y) = compFin F E u (sgE E v y) := fun u y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hi : sgE E v y * sgE E v y = sgE E v y := by
    refine sub_eq_zero.1 (eq_zero_of_at (v := v) (at_sub (at_mul_l (at_sgE _) _) (at_sgE _)) ?_)
    simp [comp_sgE, hy]
  have hY := (mem_int_iff Y).2 fun P => by
    rw [finAdEquiv_apply rfl, ev]
    set z := toCompl (rfl : P.under (𝓞 F) = _) (compFin F E _ (sgE E v y))
    have hz : z * z = z := by rw [← map_mul, ← map_mul, hi]
    rcases eq_or_ne z 0 with h | h
    · rw [h, map_zero]; exact zero_le_one
    · rw [mul_right_cancel₀ h (hz.trans (one_mul z).symm), map_one]
  have : ∀ Z ∈ AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)},
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) Z ∈ intLoc F E v := fun Z hZ => by
    induction hZ using AddSubgroup.closure_induction with
    | mem Z hZ =>
      obtain ⟨a, ha, x, rfl⟩ := hZ
      exact AddSubgroup.subset_closure ⟨_, ha v, x, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  have := this Y hY
  rwa [ev, comp_sgE] at this

def eps (v : Pl F) : AE F E := algebraMap (AF F) (AE F E) (sg v 1)

/- English proof (translation)
Use `hz (1 - sg v 1) (by rw [map_sub, map_one, ev_sg, sub_self])` as an intermediate fact. Rewrite `this` using `[sub_smul, one_smul, sub_eq_zero]`. Rewrite using `[eps, algebraMap_smul, ← this]`.
-/
theorem eps_smul {M : Type} [AddCommGroup M] [Module (AF F) M] [Module (AE F E) M] [IsScalarTower (AF F) (AE F E) M] {z : M}
    (hz : At (evFin F v) z) : (eps v : AE F E) • z = z := by
  have := hz (1 - sg v 1) (by rw [map_sub, map_one, ev_sg, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at this
  rw [eps, algebraMap_smul, ← this]

/- English proof (translation)
Introduce `u hu` and use `by rw [eps, Algebra.smul_def, ← map_mul, show u * sg v 1 = 0 from at_sg 1 u hu, map_zero]`.
-/
theorem at_eps : At (evFin F v) (eps v : AE F E) := fun u hu => by
  rw [eps, Algebra.smul_def, ← map_mul, show u * sg v 1 = 0 from at_sg 1 u hu, map_zero]

/- English proof (translation)
Rewrite using `[← smul_eq_mul]`. Conclude with `eps_smul (v := v) at_eps`.
-/
theorem eps_mul : (eps v : AE F E) * eps v = eps v := by
  rw [← smul_eq_mul]; exact eps_smul (v := v) at_eps

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem comp_alg (a : AF F) : compFin F E v (algebraMap (AF F) (AE F E) a) = evFin F v a ⊗ₜ[F] 1 := rfl

/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨_, ha, 1, rfl⟩`.
-/
theorem comp_alg_mem {a : AF F} (ha : evFin F v a ∈ v.adicCompletionIntegers F) :
    compFin F E v (algebraMap (AF F) (AE F E) a) ∈ intLoc F E v := AddSubgroup.subset_closure ⟨_, ha, 1, rfl⟩

/- English proof (translation)
Establish `hs` using `sigma_sigma hσ`. Use `haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective`. Establish `sm : ∀ (a : F) (z : E), σ (a • z) = a • σ z` using `fun a z => by`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul σ, σ.commutes]`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, σ x ≠ x := by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Take `⟨φ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Use `hσ.2.1` as an intermediate fact. Conclude with `IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun y => by`.

Use `hσ.2.2.2 φ y` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `this.symm))`. Use `set ξ := x - σ x with hξ`. Establish `h0 : ξ ≠ 0` using `sub_ne_zero.2 hx.symm`.

Establish `hc : σ ξ = -ξ` using `by rw [hξ, map_sub, hs, neg_sub]`. Choose the witnesses or unpack the hypotheses as in `⟨D, hD⟩ : ∃ D : F, algebraMap F E D = ξ * ξ := by`. Establish `li : LinearIndependent F ![(1 : E), ξ]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `a b hab`.

Establish `h1` using `congrArg σ hab`. Rewrite `h1` using `[map_add σ, sm, sm, map_one σ, hc, map_zero σ, smul_neg]`. Establish `h2 : (2 * b) • ξ = 0` using `by rw [mul_smul, two_smul]; linear_combination hab - h1`. Establish `hb : b = 0` using `by simpa [h0] using h2`. Rewrite `hab` using `[hb, zero_smul, add_zero]`.

Conclude with `⟨by simpa using hab, hb⟩`. Set `bs` to `basisOfLinearIndependentOfCardEqFinrank li (by simp [hσ.2.2.1])`. Establish `e` using `bs.sum_repr (ξ * ξ)`. Rewrite `e` using `[Fin.sum_univ_two]`. Establish `b0 : bs 0 = 1` using `by simp [bs]`.

Establish `b1 : bs 1 = ξ` using `by simp [bs]`. Rewrite `e` using `[b0, b1]`. Establish `h1` using `congrArg σ e`. Rewrite `h1` using `[map_add σ, sm, sm, map_one σ, hc, map_mul σ, hc, neg_mul_neg, smul_neg]`. Use `⟨bs.repr (ξ * ξ) 0, ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Establish `: (2 : E) * (bs.repr (ξ * ξ) 0 • (1 : E)) = 2 * (ξ * ξ)` using `by linear_combination e + h1`. Conclude with `mul_left_cancel₀ two_ne_zero this`. Establish `t0 : τ ξ ≠ 0` using `(map_ne_zero τ).2 h0`. Establish `tD : algebraMap F (Fv F v) D = τ ξ * τ ξ` using `by rw [← map_mul, ← hD, AlgHom.commutes]`.

Set `y : Fv F v ⊗[F] E` to `(2⁻¹ : Fv F v) ⊗ₜ[F] 1 + (2 * τ ξ)⁻¹ ⊗ₜ[F] ξ`. Establish `hy : y * y = y`. Establish `e1 : ((2 * τ ξ)⁻¹ * (2 * τ ξ)⁻¹) ⊗ₜ[F] (ξ * ξ) = (2⁻¹ * 2⁻¹ : Fv F v) ⊗ₜ[F] (1 : E)`. Rewrite using `[← hD, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, tD]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Simplify using `only [y, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, e1]`. Rewrite using `[show ∀ a b c : Fv F v ⊗[F] E, a + b + (c + a) = (a + a) + (b + c) from fun a b c => by abel, ← TensorProduct.add_tmul, ← TensorProduct.add_tmul]`. Use `congr 2`. Evaluate the numerical expressions.

Clear the denominators using the available nonvanishing facts. Evaluate the numerical expressions. Use `⟨sgE E v y, at_sgE _, ?_, ?_⟩` and prove the remaining obligations. Use `sub_eq_zero.1 (eq_zero_of_at (v := v) (at_sub (at_mul_l (at_sgE _) _) (at_sgE _)) ?_)` and prove the remaining obligations. Simplify using `[comp_sgE, hy]`.

Establish `e : sgE E v y = sg v 2⁻¹ ⊗ₜ[F] 1 + sg v (2 * τ ξ)⁻¹ ⊗ₜ[F] ξ` using `by simp [y, sgE]`. Establish `e2 : cA σ (sgE E v y) = sg v 2⁻¹ ⊗ₜ[F] 1 - sg v (2 * τ ξ)⁻¹ ⊗ₜ[F] ξ`. Rewrite using `[e, map_add]`. Express the relevant statement in the definitionally equal form `_ ⊗ₜ[F] σ 1 + _ ⊗ₜ[F] σ ξ = _`. Rewrite using `[map_one, hc, TensorProduct.tmul_neg, ← sub_eq_add_neg]`.

Both sides reduce to the same expression. Rewrite using `[e2, e, add_add_sub_cancel, ← TensorProduct.add_tmul, ← map_add]`. Evaluate the numerical expressions. Both sides reduce to the same expression.
-/
theorem exists_eta (hσ : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) :
    ∃ η : AE F E, At (evFin F v) η ∧ η * η = η ∧ η + cA σ η = eps v := by
  have hs := sigma_sigma hσ
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  have sm : ∀ (a : F) (z : E), σ (a • z) = a • σ z := fun a z => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul σ, σ.commutes]
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra h
    push Not at h
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := hσ.2.1
    exact IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun y => by
      have := hσ.2.2.2 φ y
      rw [h] at this
      exact this.symm))
  set ξ := x - σ x with hξ
  have h0 : ξ ≠ 0 := sub_ne_zero.2 hx.symm
  have hc : σ ξ = -ξ := by rw [hξ, map_sub, hs, neg_sub]
  obtain ⟨D, hD⟩ : ∃ D : F, algebraMap F E D = ξ * ξ := by
    have li : LinearIndependent F ![(1 : E), ξ] := by
      rw [LinearIndependent.pair_iff]
      intro a b hab
      have h1 := congrArg σ hab
      rw [map_add σ, sm, sm, map_one σ, hc, map_zero σ, smul_neg] at h1
      have h2 : (2 * b) • ξ = 0 := by rw [mul_smul, two_smul]; linear_combination hab - h1
      have hb : b = 0 := by simpa [h0] using h2
      rw [hb, zero_smul, add_zero] at hab
      exact ⟨by simpa using hab, hb⟩
    let bs := basisOfLinearIndependentOfCardEqFinrank li (by simp [hσ.2.2.1])
    have e := bs.sum_repr (ξ * ξ)
    rw [Fin.sum_univ_two] at e
    have b0 : bs 0 = 1 := by simp [bs]
    have b1 : bs 1 = ξ := by simp [bs]
    rw [b0, b1] at e
    have h1 := congrArg σ e
    rw [map_add σ, sm, sm, map_one σ, hc, map_mul σ, hc, neg_mul_neg, smul_neg] at h1
    refine ⟨bs.repr (ξ * ξ) 0, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    have : (2 : E) * (bs.repr (ξ * ξ) 0 • (1 : E)) = 2 * (ξ * ξ) := by linear_combination e + h1
    exact mul_left_cancel₀ two_ne_zero this
  have t0 : τ ξ ≠ 0 := (map_ne_zero τ).2 h0
  have tD : algebraMap F (Fv F v) D = τ ξ * τ ξ := by rw [← map_mul, ← hD, AlgHom.commutes]
  let y : Fv F v ⊗[F] E := (2⁻¹ : Fv F v) ⊗ₜ[F] 1 + (2 * τ ξ)⁻¹ ⊗ₜ[F] ξ
  have hy : y * y = y := by
    have e1 : ((2 * τ ξ)⁻¹ * (2 * τ ξ)⁻¹) ⊗ₜ[F] (ξ * ξ) = (2⁻¹ * 2⁻¹ : Fv F v) ⊗ₜ[F] (1 : E) := by
      rw [← hD, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, tD]
      congr 1; field_simp
    simp only [y, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, e1]
    rw [show ∀ a b c : Fv F v ⊗[F] E, a + b + (c + a) = (a + a) + (b + c) from fun a b c => by abel, ← TensorProduct.add_tmul,
      ← TensorProduct.add_tmul]
    congr 2
    · norm_num
    · field_simp; norm_num
  refine ⟨sgE E v y, at_sgE _, ?_, ?_⟩
  · refine sub_eq_zero.1 (eq_zero_of_at (v := v) (at_sub (at_mul_l (at_sgE _) _) (at_sgE _)) ?_)
    simp [comp_sgE, hy]
  · have e : sgE E v y = sg v 2⁻¹ ⊗ₜ[F] 1 + sg v (2 * τ ξ)⁻¹ ⊗ₜ[F] ξ := by simp [y, sgE]
    have e2 : cA σ (sgE E v y) = sg v 2⁻¹ ⊗ₜ[F] 1 - sg v (2 * τ ξ)⁻¹ ⊗ₜ[F] ξ := by
      rw [e, map_add]
      change _ ⊗ₜ[F] σ 1 + _ ⊗ₜ[F] σ ξ = _
      rw [map_one, hc, TensorProduct.tmul_neg, ← sub_eq_add_neg]; rfl
    rw [e2, e, add_add_sub_cancel, ← TensorProduct.add_tmul, ← map_add]
    norm_num
    rfl

/- English proof (translation)
Establish `cc` using `cA_cA (F := F) (sigma_sigma hB.cm)`. Establish `hm : At (evFin F v) (1 - mat k)` using `by simpa using at_sub at_zero h0`. Establish `hk : mat k * mat k⁻¹ = 1` using `k.1.mul_inv`. Use `set h : AE F E := algebraMap (AF F) (AE F E) ⅟(2 : AF F) with hh`. Establish `hh2 : h + h = 1` using `by rw [hh, ← map_add, invOf_two_add_invOf_two, map_one]`.

Establish `ch : cA σ h = h` using `(cA σ).commutes _`. Establish `ce : cA σ (eps v) = eps v` using `(cA σ).commutes _`. Break down `isEmpty_or_nonempty (E →ₐ[F] Fv F v) with he | ⟨⟨τ⟩⟩` into its components or cases. Take `⟨w, hw⟩` from `inert_of_local F E σ B hB v he`. Establish `hu : w.under (𝓞 F) = v` using `(under_eq_iff hw w).2 rfl`.

Take `⟨c, hc, -⟩` from `existsUnique_isConjAt σ hw hu`. Take `⟨ϖ, hcc, hv, -, -, ⟨x, hx, hx1⟩, -⟩` from `exists_isUnramInv hB.cm hw hc`. Take `⟨y, hy⟩` from `(toCompl_bijective hw hu).2 (c x - x)`. Use `set δ := sgE E v y`. Establish `pδ : piE hu δ = c x - x` using `by rw [piE, RingHom.comp_apply, comp_sgE, hy]`.

Establish `cδ : cA σ δ = -δ`. Use `eq_neg_of_add_eq_zero_left (eq_zero_of_at (v := v) (at_add (fun u hu => ?_) (at_sgE _)) ((toCompl_bijective hw hu).1 ?_))` and prove the remaining obligations. Rewrite using `[← map_smul, at_sgE y u hu, map_zero]`. Express the relevant statement in the definitionally equal form `piE hu _ = _`. Rewrite using `[map_add, piE_cA hc, pδ, map_sub, hcc, map_zero]`.

Expand and normalize the polynomial expressions, which then agree. Establish `iδ : compFin F E v δ ∈ intLoc F E v` using `(mem_intLoc_iff hw hu _).2 (by`. Express the relevant statement in the definitionally equal form `piE hu δ ∈ _`. Rewrite using `[pδ]`. Conclude with `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx1.le)`.

Establish `ih : compFin F E v h ∈ intLoc F E v` using `comp_alg_mem (by`. Establish `e2 : evFin F v ⅟(2 : AF F) * 2 = 1`. Rewrite using `[show (2 : Fv F v) = evFin F v 2 from (map_ofNat _ 2).symm, ← map_mul, invOf_mul_self, map_one]`. Establish `v2 : Valued.v (2 : Fv F v) = 1`. Rewrite using `[show (2 : Fv F v) = algebraMap F (Fv F v) (algebraMap (𝓞 F) F 2) by simp [map_ofNat], valued_alg]`.

Conclude with `(HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 (hB.inert v w hw).1`. Use `congrArg Valued.v e2` as an intermediate fact. Rewrite `this` using `[map_mul, v2, mul_one, map_one]`. Conclude with `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 this.le)`. Take `⟨a, ha⟩` from `exists_fr (v := v) X hL`.

Take `⟨N, hN⟩` from `(ha _).1 h1`. Take `⟨N', hN'⟩` from `(ha _).1 h2`. Use `haveI : Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) := Formalism.UG.P.tjcosets_finite w`. Set `ρ : intLoc F E v →+* w.adicCompletionIntegers E` to `((toCompl hu).comp (intLoc F E v).subtype).codRestrict (w.adicCompletionIntegers E).toSubring fun z => toCompl_mem hu z.2`. Set `r` to `(IsLocalRing.residue (w.adicCompletionIntegers E)).comp ρ`.

Establish `un : ∀ z, r z ≠ 0 ↔ IsUnit (ρ z)` using `fun z => IsLocalRing.residue_ne_zero_iff_isUnit _`. Establish `inj : Function.Injective ((intLoc F E v).subtype.mapMatrix (m` using `Fin n)) := fun A B e => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun e i) j)`. Establish `hNN : N' * N = 1` using `inj (by rw [map_mul, hN, hN', ← map_mul, mul_eq_one_comm.1 hk, map_one, map_one])`. Take `⟨m, hm'⟩` from `exists_det_ne (k := r.mapMatrix N) (k' := r.mapMatrix N') (h := r ⟨_, ih⟩) (δ := r ⟨_, iδ⟩) (by rw [← map_mul, hNN, map_one]) (by rw [← map_add, ← map_one r]; congr 1; exact Subtype.ext (by change _ + _ = 1; rw [← map_add, hh2, map_one])) ((un _).2 (HeightOneSpectrum.adicCompleti …`. Express the relevant statement in the definitionally equal form `Valued.v (piE hu δ) = 1`.

Rewrite using `[pδ, hx1])))`. Use `set x := 1 + 1 + mat k + mat k⁻¹ with hxd`. Establish `ax : Adj (cA σ) (incM F X.J) x x`. Use `((Adj.one.add Adj.one).add (adj_unit k)).add (adj_unit k⁻¹)` as an intermediate fact. Rewrite `this` using `[inv_inv, add_right_comm (1 + 1) _ (k.1.1)]`.

Conclude with `this`. Establish `ap` using `Adj.one.sub (ax.pow m)`. Set `fN` to `1 + (1 - N) * ((-(⟨_, ih⟩ : intLoc F E v)) • 1 + (⟨_, iδ⟩ : intLoc F E v) • (1 - (1 + 1 + N + N') ^ m))`. Establish `ms : ∀ {S : Type} [CommRing S] (g : intLoc F E v →+* S) (z : intLoc F E v) (M : Matrix (Fin n) (Fin n) (intLoc F E v)), g.mapMatrix (z • M) = g z • g.mapMatrix M` using `fun g z M => by ext i j; simp`. Establish `hfu : IsUnit fN.det`.

Establish `: r fN.det ≠ 0`. Rewrite using `[RingHom.map_det]`. Simplify `hm'` using `only [fN, map_add, map_mul, map_sub, map_one, map_pow, ms, map_neg]`. Take `⟨u, hu'⟩` from `((un _).1 this).exists_right_inv`. Take `⟨z, hz⟩` from `(toCompl_bijective hw hu).2 u.1`.

Use `IsUnit.of_mul_eq_one ⟨z, (mem_intLoc_iff hw hu _).2 (hz ▸ u.2)⟩ (Subtype.ext ((toCompl_bijective hw hu).1 ?_))` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `toCompl hu (_ * z) = toCompl hu 1`. Rewrite using `[map_mul, hz, map_one]`. Conclude with `congrArg Subtype.val hu'`. Establish `xp : x ∈ Pres v X` using `add_mem (add_mem (add_mem (one_mem _) (one_mem _)) h1) h2`.

Take `⟨f', hf', e⟩` from `exists_inv ha (f := 1 + (1 - mat k) * ((-h) • 1 + δ • (1 - x ^ m))) (N := fN) (by rw [add_sub_cancel_left]; exact at_mul_left hm _) (by`. Simplify using `only [fN, hxd, map_add, map_mul, map_sub, map_one, map_pow, ms, fr_smul, map_neg, hN, hN']`. Use the proof step `rfl) hfu`. Use `⟨(-h) • 1 + δ • (1 - x ^ m), (-h) • 1 + (-δ) • (1 - x ^ m), f', (Adj.one.smul (by rw [map_neg, ch])).add (ap.smul (by rw [map_neg, cδ, neg_neg])), (Adj.one.smul (by rw [map_neg, ch])).add (ap.smul cδ), ?_, add_mem (smul_mem_Pres hL (by rw [map_neg]; exact neg_mem ih) (one_mem _)) …` and prove the remaining obligations. Rewrite using `[add_add_add_comm, ← add_smul, ← add_smul, add_neg_cancel, zero_smul, add_zero, ← neg_add, hh2, neg_smul, one_smul]`.

Take `⟨η, a1, a2, a3⟩` from `exists_eta hB.cm τ`. Establish `iη : compFin F E v η ∈ intLoc F E v` using `mem_intLoc_of_idem (by rw [← map_mul, a2])`. Establish `c1 : compFin F E v (eps v : AE F E) = 1` using `by rw [eps, comp_alg, ev_sg]; rfl`. Use `set θ := η + (1 - eps v) * h with hθ`. Establish `e1 : (1 - mat k) * ((-θ) • 1) = -(η • (1 - mat k))`.

Establish `: (1 - eps v : AE F E) • (1 - mat k) = 0` using `by rw [sub_smul, one_smul, eps_smul hm, sub_self]`. Rewrite using `[Matrix.mul_smul, Matrix.mul_one, neg_smul, hθ, add_smul, mul_comm, mul_smul, this, smul_zero, add_zero]`. Use `⟨(-θ) • 1, (-cA σ θ) • 1, 1 - η • (1 - mat k⁻¹), Adj.one.smul (by rw [map_neg, cc]), Adj.one.smul (map_neg _ _), ?_, smul_mem_Pres hL (by rw [map_neg, hθ, map_add, map_mul, map_sub, map_one, c1, sub_self, zero_mul, add_zero]; exact neg_mem iη) (one_mem _), sub_mem (one_mem _) (sm …` and prove the remaining obligations. Rewrite using `[← add_smul, ← neg_add, neg_smul, hθ, map_add, map_mul, map_sub, map_one, ce, ch, show η + (1 - eps v) * h + (cA σ η + (1 - eps v) * h) = 1 by linear_combination a3 + (1 - eps v) * hh2, one_smul]`. Rewrite using `[e1, Matrix.add_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, a2, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hk]`.

Simplify using `only [smul_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_beta {B : Base F E} (hB : B.IsGood σ) {X : Spc F E n} (hL : X.L.IsLattice E) (k : UA σ X.J)
    (h0 : At (evFin F v) (mat k - 1)) (h1 : mat k ∈ Pres v X) (h2 : mat k⁻¹ ∈ Pres v X) :
    ∃ b b' f', Adj (cA σ) (incM F X.J) b b' ∧ Adj (cA σ) (incM F X.J) b' b ∧ b + b' = -1 ∧ b ∈ Pres v X ∧ f' ∈ Pres v X ∧
      (1 + (1 - mat k) * b) * f' = 1 := by
  have cc := cA_cA (F := F) (sigma_sigma hB.cm)
  have hm : At (evFin F v) (1 - mat k) := by simpa using at_sub at_zero h0
  have hk : mat k * mat k⁻¹ = 1 := k.1.mul_inv
  set h : AE F E := algebraMap (AF F) (AE F E) ⅟(2 : AF F) with hh
  have hh2 : h + h = 1 := by rw [hh, ← map_add, invOf_two_add_invOf_two, map_one]
  have ch : cA σ h = h := (cA σ).commutes _
  have ce : cA σ (eps v) = eps v := (cA σ).commutes _
  rcases isEmpty_or_nonempty (E →ₐ[F] Fv F v) with he | ⟨⟨τ⟩⟩
  · obtain ⟨w, hw⟩ := inert_of_local F E σ B hB v he
    have hu : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
    obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw hu
    obtain ⟨ϖ, hcc, hv, -, -, ⟨x, hx, hx1⟩, -⟩ := exists_isUnramInv hB.cm hw hc
    obtain ⟨y, hy⟩ := (toCompl_bijective hw hu).2 (c x - x)
    set δ := sgE E v y
    have pδ : piE hu δ = c x - x := by rw [piE, RingHom.comp_apply, comp_sgE, hy]
    have cδ : cA σ δ = -δ := by
      refine eq_neg_of_add_eq_zero_left (eq_zero_of_at (v := v) (at_add (fun u hu => ?_) (at_sgE _))
        ((toCompl_bijective hw hu).1 ?_))
      · rw [← map_smul, at_sgE y u hu, map_zero]
      · change piE hu _ = _
        rw [map_add, piE_cA hc, pδ, map_sub, hcc, map_zero]; ring
    have iδ : compFin F E v δ ∈ intLoc F E v := (mem_intLoc_iff hw hu _).2 (by
      change piE hu δ ∈ _
      rw [pδ]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx1.le)
    have ih : compFin F E v h ∈ intLoc F E v := comp_alg_mem (by
      have e2 : evFin F v ⅟(2 : AF F) * 2 = 1 := by
        rw [show (2 : Fv F v) = evFin F v 2 from (map_ofNat _ 2).symm, ← map_mul, invOf_mul_self, map_one]
      have v2 : Valued.v (2 : Fv F v) = 1 := by
        rw [show (2 : Fv F v) = algebraMap F (Fv F v) (algebraMap (𝓞 F) F 2) by simp [map_ofNat], valued_alg]
        exact (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 (hB.inert v w hw).1
      have := congrArg Valued.v e2
      rw [map_mul, v2, mul_one, map_one] at this
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 this.le)
    obtain ⟨a, ha⟩ := exists_fr (v := v) X hL
    obtain ⟨N, hN⟩ := (ha _).1 h1
    obtain ⟨N', hN'⟩ := (ha _).1 h2
    haveI : Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) := Formalism.UG.P.tjcosets_finite w
    let ρ : intLoc F E v →+* w.adicCompletionIntegers E :=
      ((toCompl hu).comp (intLoc F E v).subtype).codRestrict (w.adicCompletionIntegers E).toSubring fun z => toCompl_mem hu z.2
    let r := (IsLocalRing.residue (w.adicCompletionIntegers E)).comp ρ
    have un : ∀ z, r z ≠ 0 ↔ IsUnit (ρ z) := fun z => IsLocalRing.residue_ne_zero_iff_isUnit _
    have inj : Function.Injective ((intLoc F E v).subtype.mapMatrix (m := Fin n)) := fun A B e =>
      Matrix.ext fun i j => Subtype.ext (congrFun (congrFun e i) j)
    have hNN : N' * N = 1 := inj (by rw [map_mul, hN, hN', ← map_mul, mul_eq_one_comm.1 hk, map_one, map_one])
    obtain ⟨m, hm'⟩ := exists_det_ne (k := r.mapMatrix N) (k' := r.mapMatrix N') (h := r ⟨_, ih⟩) (δ := r ⟨_, iδ⟩)
      (by rw [← map_mul, hNN, map_one])
      (by rw [← map_add, ← map_one r]; congr 1; exact Subtype.ext (by change _ + _ = 1; rw [← map_add, hh2, map_one]))
      ((un _).2 (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 (by
        change Valued.v (piE hu δ) = 1
        rw [pδ, hx1])))
    set x := 1 + 1 + mat k + mat k⁻¹ with hxd
    have ax : Adj (cA σ) (incM F X.J) x x := by
      have := ((Adj.one.add Adj.one).add (adj_unit k)).add (adj_unit k⁻¹)
      rw [inv_inv, add_right_comm (1 + 1) _ (k.1.1)] at this
      exact this
    have ap := Adj.one.sub (ax.pow m)
    let fN := 1 + (1 - N) * ((-(⟨_, ih⟩ : intLoc F E v)) • 1 + (⟨_, iδ⟩ : intLoc F E v) • (1 - (1 + 1 + N + N') ^ m))
    have ms : ∀ {S : Type} [CommRing S] (g : intLoc F E v →+* S) (z : intLoc F E v) (M : Matrix (Fin n) (Fin n) (intLoc F E v)),
        g.mapMatrix (z • M) = g z • g.mapMatrix M := fun g z M => by ext i j; simp
    have hfu : IsUnit fN.det := by
      have : r fN.det ≠ 0 := by
        rw [RingHom.map_det]
        simpa only [fN, map_add, map_mul, map_sub, map_one, map_pow, ms, map_neg] using hm'
      obtain ⟨u, hu'⟩ := ((un _).1 this).exists_right_inv
      obtain ⟨z, hz⟩ := (toCompl_bijective hw hu).2 u.1
      refine IsUnit.of_mul_eq_one ⟨z, (mem_intLoc_iff hw hu _).2 (hz ▸ u.2)⟩ (Subtype.ext ((toCompl_bijective hw hu).1 ?_))
      change toCompl hu (_ * z) = toCompl hu 1
      rw [map_mul, hz, map_one]
      exact congrArg Subtype.val hu'
    have xp : x ∈ Pres v X := add_mem (add_mem (add_mem (one_mem _) (one_mem _)) h1) h2
    obtain ⟨f', hf', e⟩ := exists_inv ha (f := 1 + (1 - mat k) * ((-h) • 1 + δ • (1 - x ^ m))) (N := fN)
      (by rw [add_sub_cancel_left]; exact at_mul_left hm _) (by
        simp only [fN, hxd, map_add, map_mul, map_sub, map_one, map_pow, ms, fr_smul, map_neg, hN, hN']
        rfl) hfu
    refine ⟨(-h) • 1 + δ • (1 - x ^ m), (-h) • 1 + (-δ) • (1 - x ^ m), f',
      (Adj.one.smul (by rw [map_neg, ch])).add (ap.smul (by rw [map_neg, cδ, neg_neg])),
      (Adj.one.smul (by rw [map_neg, ch])).add (ap.smul cδ), ?_,
      add_mem (smul_mem_Pres hL (by rw [map_neg]; exact neg_mem ih) (one_mem _))
        (smul_mem_Pres hL iδ (sub_mem (one_mem _) (pow_mem xp m))), hf', e⟩
    rw [add_add_add_comm, ← add_smul, ← add_smul, add_neg_cancel, zero_smul, add_zero, ← neg_add, hh2, neg_smul, one_smul]
  · obtain ⟨η, a1, a2, a3⟩ := exists_eta hB.cm τ
    have iη : compFin F E v η ∈ intLoc F E v := mem_intLoc_of_idem (by rw [← map_mul, a2])
    have c1 : compFin F E v (eps v : AE F E) = 1 := by rw [eps, comp_alg, ev_sg]; rfl
    set θ := η + (1 - eps v) * h with hθ
    have e1 : (1 - mat k) * ((-θ) • 1) = -(η • (1 - mat k)) := by
      have : (1 - eps v : AE F E) • (1 - mat k) = 0 := by rw [sub_smul, one_smul, eps_smul hm, sub_self]
      rw [Matrix.mul_smul, Matrix.mul_one, neg_smul, hθ, add_smul, mul_comm, mul_smul, this, smul_zero, add_zero]
    refine ⟨(-θ) • 1, (-cA σ θ) • 1, 1 - η • (1 - mat k⁻¹), Adj.one.smul (by rw [map_neg, cc]), Adj.one.smul (map_neg _ _), ?_,
      smul_mem_Pres hL (by rw [map_neg, hθ, map_add, map_mul, map_sub, map_one, c1, sub_self, zero_mul, add_zero]; exact neg_mem iη)
        (one_mem _), sub_mem (one_mem _) (smul_mem_Pres hL iη (sub_mem (one_mem _) h2)), ?_⟩
    · rw [← add_smul, ← neg_add, neg_smul, hθ, map_add, map_mul, map_sub, map_one, ce, ch,
        show η + (1 - eps v) * h + (cA σ η + (1 - eps v) * h) = 1 by linear_combination a3 + (1 - eps v) * hh2, one_smul]
    · rw [e1, Matrix.add_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul, a2, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hk]
      simp only [smul_sub]; abel

end PositivityTheory.ThKG.Loc.Cone.Vf

end
