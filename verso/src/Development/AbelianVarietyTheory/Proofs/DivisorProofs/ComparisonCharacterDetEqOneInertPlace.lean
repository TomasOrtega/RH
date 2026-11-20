import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqOfInert
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertDetChr

open GlobalTheory.LFun GlobalTheory.Doubling

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Introduce `u hu`. Establish `h` using `ht u hu`. Use `set c := algebraMap (AF F) (AE F E) u with hc`. Set `I : Ideal (AE F E)` to `(Submodule.span (AE F E) {c}).annihilator`. Establish `hmem : ∀ x : AE F E, x ∈ I ↔ c * x = 0` using `fun x => by`.

Rewrite using `[Submodule.mem_annihilator_span_singleton, smul_eq_mul, mul_comm]`. Establish `hent : ∀ i j, (t : Matrix (Fin n) (Fin n) (AE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AE F E)) i j ∈ I` using `fun i j => by`. Rewrite using `[hmem]`. Use `congrFun (congrFun h i) j` as an intermediate fact. Simplify `this` using `[Matrix.sub_apply, Algebra.smul_def, hc]`.

Establish `hq : (Ideal.Quotient.mk I).mapMatrix (t : Matrix (Fin n) (Fin n) (AE F E)) = (Ideal.Quotient.mk I).mapMatrix (1 : Matrix (Fin n) (Fin n) (AE F E))`. Use extensionality with `i j`. Conclude with `Ideal.Quotient.eq.2 (hent i j)`. Establish `hd` using `congrArg Matrix.det hq`. Rewrite `hd` using `[← RingHom.map_det, ← RingHom.map_det, Matrix.det_one]`.

Use `(hmem _).1 (Ideal.Quotient.eq.1 hd)` as an intermediate fact. Rewrite using `[Algebra.smul_def, Matrix.GeneralLinearGroup.val_det_apply]`. Conclude with `this`.
-/
theorem at_det_sub_one {n : ℕ} (v : Pl F) (t : GL (Fin n) (AE F E))
    (ht : At (evFin F v) ((t : Matrix (Fin n) (Fin n) (AE F E)) - 1)) :
    At (evFin F v) (((Matrix.GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) - 1) := by
  intro u hu
  have h := ht u hu
  set c := algebraMap (AF F) (AE F E) u with hc
  let I : Ideal (AE F E) := (Submodule.span (AE F E) {c}).annihilator
  have hmem : ∀ x : AE F E, x ∈ I ↔ c * x = 0 := fun x => by
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul, mul_comm]
  have hent : ∀ i j, (t : Matrix (Fin n) (Fin n) (AE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AE F E)) i j ∈ I :=
    fun i j => by
      rw [hmem]
      have := congrFun (congrFun h i) j
      simpa [Matrix.sub_apply, Algebra.smul_def, hc] using this
  have hq : (Ideal.Quotient.mk I).mapMatrix (t : Matrix (Fin n) (Fin n) (AE F E)) =
      (Ideal.Quotient.mk I).mapMatrix (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    ext i j
    exact Ideal.Quotient.eq.2 (hent i j)
  have hd := congrArg Matrix.det hq
  rw [← RingHom.map_det, ← RingHom.map_det, Matrix.det_one] at hd
  have := (hmem _).1 (Ideal.Quotient.eq.1 hd)
  rw [Algebra.smul_def, Matrix.GeneralLinearGroup.val_det_apply]
  exact this

/- English proof (translation)
Simplify using `[compFin, Algebra.TensorProduct.algebraMap_apply]`.
-/
theorem compFin_algebraMap (u : Pl F) (a : AF F) :
    compFin F E u (algebraMap (AF F) (AE F E) a) = algebraMap (Fv F u) (Fv F u ⊗[F] E) (evFin F u a) := by
  simp [compFin, Algebra.TensorProduct.algebraMap_apply]

/- English proof (translation)
Simplify using `[compInf, Algebra.TensorProduct.algebraMap_apply]`.
-/
theorem compInf_algebraMap (w : InfinitePlace F) (a : AF F) :
    compInf F E w (algebraMap (AF F) (AE F E) a) = algebraMap w.Completion (w.Completion ⊗[F] E) (evInf F w a) := by
  simp [compInf, Algebra.TensorProduct.algebraMap_apply]

/- English proof (translation)
The claim follows from `evalV_singleFin_self v x`.
-/
theorem evFin_inFin_self (v : Pl F) (x : Fv F v) : evFin F v (inFin v x) = x :=
  evalV_singleFin_self v x

/- English proof (translation)
The claim follows from `evalV_singleFin_ne h x`.
-/
theorem evFin_inFin_ne {u v : Pl F} (h : u ≠ v) (x : Fv F v) : evFin F u (inFin v x) = 0 :=
  evalV_singleFin_ne h x

/- English proof (translation)
Use `show GlobalTheory.AutFunCompare.evW w 0 = 0`. Conclude with `map_zero _`.
-/
theorem evInf_inFin (w : InfinitePlace F) (v : Pl F) (x : Fv F v) : evInf F w (inFin v x) = 0 := by
  show GlobalTheory.AutFunCompare.evW w 0 = 0
  exact map_zero _

/- English proof (translation)
Introduce `u hu`. Rewrite using `[smul_eq_mul]`. Use `Prod.ext (mul_zero _) (af_ext fun u' => ?_)` and prove the remaining obligations. Use `show evalV F u' (u.2 * singleFin v 1) = evalV F u' 0`. Rewrite using `[map_mul, map_zero]`.

Distinguish the cases in `e : u' = v`. Substitute `e` using the available equality. Conclude with `mul_eq_zero_of_left hu _`. Rewrite using `[evalV_singleFin_ne e, mul_zero]`.
-/
theorem at_inFin_one (v : Pl F) : At (evFin F v) (inFin v (1 : Fv F v)) := by
  intro u hu
  rw [smul_eq_mul]
  refine Prod.ext (mul_zero _) (af_ext fun u' => ?_)
  show evalV F u' (u.2 * singleFin v 1) = evalV F u' 0
  rw [map_mul, map_zero]
  by_cases e : u' = v
  · subst e
    exact mul_eq_zero_of_left hu _
  · rw [evalV_singleFin_ne e, mul_zero]

/- English proof (translation)
Use `set e : AF F := inFin v 1`. Establish `key` using `hz (1 - e) (by rw [map_sub, map_one, evFin_inFin_self, sub_self])`. Rewrite `key` using `[Algebra.smul_def]`. Use `idele_ext (fun w => ?_) (fun u => ?_)` and prove the remaining obligations. Rewrite using `[unitInf_ideleAt]`.

Use `Units.ext ?_` and prove the remaining obligations. Use `congrArg (compInf F E w) key` as an intermediate fact. Rewrite `this` using `[map_mul, compInf_algebraMap, map_sub, map_one, evInf_inFin, sub_zero, map_one, one_mul, map_zero, map_sub, map_one, sub_eq_zero]`. Conclude with `this`. Distinguish the cases in `huv : u = v`.

Substitute `huv` using the available equality. Rewrite using `[unitFin_ideleAt_self]`. Rewrite using `[unitFin_ideleAt_ne huv]`. Use `Units.ext ?_` and prove the remaining obligations. Use `congrArg (compFin F E u) key` as an intermediate fact.

Rewrite `this` using `[map_mul, compFin_algebraMap, map_sub, map_one, evFin_inFin_ne huv, sub_zero, map_one, one_mul, map_zero, map_sub, map_one, sub_eq_zero]`. Conclude with `this`.
-/
theorem eq_ideleAt {v : Pl F} {z : (AE F E)ˣ} (hz : At (evFin F v) ((z : AE F E) - 1)) :
    z = ideleAt F E v (unitFin F E v z) := by
  set e : AF F := inFin v 1
  have key := hz (1 - e) (by rw [map_sub, map_one, evFin_inFin_self, sub_self])
  rw [Algebra.smul_def] at key
  refine idele_ext (fun w => ?_) (fun u => ?_)
  · rw [unitInf_ideleAt]
    refine Units.ext ?_
    have := congrArg (compInf F E w) key
    rw [map_mul, compInf_algebraMap, map_sub, map_one, evInf_inFin, sub_zero, map_one, one_mul, map_zero, map_sub,
      map_one, sub_eq_zero] at this
    exact this
  · by_cases huv : u = v
    · subst huv
      rw [unitFin_ideleAt_self]
    · rw [unitFin_ideleAt_ne huv]
      refine Units.ext ?_
      have := congrArg (compFin F E u) key
      rw [map_mul, compFin_algebraMap, map_sub, map_one, evFin_inFin_ne huv, sub_zero, map_one, one_mul, map_zero,
        map_sub, map_one, sub_eq_zero] at this
      exact this

section Lat

variable {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v)

def piW' : AE F E →+* w.adicCompletion E := (toCompl h).comp (compFin F E v)

/- English proof (translation)
Rewrite using `[piW', RingHom.comp_apply, compFin_algebraMap, Algebra.TensorProduct.algebraMap_apply, toCompl_tmul]`. Simplify using the standard rewrite rules.
-/
theorem piW'_algebraMap (a : AF F) : piW' h (algebraMap (AF F) (AE F E) a) = complMap h (evFin F v a) := by
  rw [piW', RingHom.comp_apply, compFin_algebraMap, Algebra.TensorProduct.algebraMap_apply, toCompl_tmul]
  simp

/- English proof (translation)
Rewrite using `[piW', RingHom.comp_apply]`. Establish `: compFin F E v (inclR (F` using `F) (AF F) y) = (1 : Fv F v) ⊗ₜ[F] y := by show Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] y) = _`. Rewrite using `[Algebra.TensorProduct.map_tmul, map_one]`. Both sides reduce to the same expression. Rewrite using `[this, toCompl_tmul, map_one, one_mul]`.
-/
theorem piW'_inclR (y : E) : piW' h (inclR (F := F) (AF F) y) = algebraMap E _ y := by
  rw [piW', RingHom.comp_apply]
  have : compFin F E v (inclR (F := F) (AF F) y) = (1 : Fv F v) ⊗ₜ[F] y := by
    show Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] y) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
  rw [this, toCompl_tmul, map_one, one_mul]

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, -, ha, y, hy, rfl⟩` from `hz`. Establish `e : piW' h ∘ (a • fun i => inclR (F` using `F) (AF F) (y i)) = (⟨complMap h (evFin F v a), complMap_mem h ha⟩ : Formalism.UG.Ov E w) • (fun i => algebraMap E (w.adicCompletion E) (y i)) := by`. Use function extensionality and compare the values at `i`.

Use `show piW' h (a • inclR (F := F) (AF F) (y i)) = _`. Rewrite using `[Algebra.smul_def, map_mul, piW'_algebraMap, piW'_inclR]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hy, rfl⟩)`.

Consider the case `zero`. Use `zero_mem (latAt w W.L) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Conclude with `map_zero _`. Consider the case `add x y _ _ hx hy`.

Use `add_mem hx hy using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Conclude with `map_add _ _ _`. Consider the case `neg x _ hx`. Use `neg_mem hx using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i`. Conclude with `map_neg _ _`.
-/
theorem comp_mem_latAt {d : ℕ} (W : Spc F E d) {z : Fin d → AE F E} (hz : z ∈ GlobalTheory.InertSph.latAt W v) :
    piW' h ∘ z ∈ latAt w W.L := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, y, hy, rfl⟩ := hz
    have e : piW' h ∘ (a • fun i => inclR (F := F) (AF F) (y i)) =
        (⟨complMap h (evFin F v a), complMap_mem h ha⟩ : Formalism.UG.Ov E w) •
          (fun i => algebraMap E (w.adicCompletion E) (y i)) := by
      funext i
      show piW' h (a • inclR (F := F) (AF F) (y i)) = _
      rw [Algebra.smul_def, map_mul, piW'_algebraMap, piW'_inclR]
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hy, rfl⟩)
  | zero =>
    convert zero_mem (latAt w W.L) using 1
    funext i; exact map_zero _
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    funext i; exact map_add _ _ _
  | neg x _ hx =>
    convert neg_mem hx using 1
    funext i; exact map_neg _ _

/- English proof (translation)
Use `⟨AddSubgroup.subset_closure ⟨_, at_inFin_one v, ?_, y, hy, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[evFin_inFin_self]`. Conclude with `one_mem _`. Use function extensionality and compare the values at `i show piW' h (inFin v (1 : Fv F v) • inclR (F := F) (AF F) (y i)) = _`. Rewrite using `[Algebra.smul_def, map_mul, piW'_algebraMap, piW'_inclR, evFin_inFin_self, map_one, one_mul]`.
-/
theorem lift_mem_latAt {d : ℕ} (W : Spc F E d) {y : Fin d → E} (hy : y ∈ W.L) :
    (inFin v (1 : Fv F v) • fun i => inclR (F := F) (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt W v ∧
      piW' h ∘ (inFin v (1 : Fv F v) • fun i => inclR (F := F) (AF F) (y i)) =
        fun i => algebraMap E (w.adicCompletion E) (y i) := by
  refine ⟨AddSubgroup.subset_closure ⟨_, at_inFin_one v, ?_, y, hy, rfl⟩, ?_⟩
  · rw [evFin_inFin_self]; exact one_mem _
  · funext i
    show piW' h (inFin v (1 : Fv F v) • inclR (F := F) (AF F) (y i)) = _
    rw [Algebra.smul_def, map_mul, piW'_algebraMap, piW'_inclR, evFin_inFin_self, map_one, one_mul]

/- English proof (translation)
Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨y, hy, rfl⟩` from `hz`. Take `⟨h1, h2⟩` from `lift_mem_latAt h W hy`.

Use `show (piW' h).mapMatrix g *ᵥ (fun i => algebraMap E (w.adicCompletion E) (y i)) ∈ _`. Rewrite using `[← h2]`. Establish `e : (piW' h).mapMatrix g *ᵥ (piW' h ∘ (inFin v (1 : Fv F v) • fun i => inclR (F` using `F) (AF F) (y i))) = piW' h ∘ (g *ᵥ (inFin v (1 : Fv F v) • fun i => inclR (F := F) (AF F) (y i))) :=`. Use function extensionality and compare the values at `fun i => (RingHom.map_mulVec (piW' h) g _ i).symm`. Rewrite using `[e]`.

Conclude with `comp_mem_latAt h W (hg _ h1)`. Consider the case `zero => rw [Matrix.mulVec_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [Matrix.mulVec_add]`. Conclude with `add_mem hx hy`.

Consider the case `smul c x _ hx`. Establish `e : (piW' h).mapMatrix g *ᵥ (c • x) = c • ((piW' h).mapMatrix g *ᵥ x)`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, Finset.mul_sum, Subring.smul_def, mul_left_comm]`. Rewrite using `[e]`.

Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem mulVec_mem_latAt {d : ℕ} (W : Spc F E d) (g : Matrix (Fin d) (Fin d) (AE F E))
    (hg : ∀ z ∈ GlobalTheory.InertSph.latAt W v, g *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    ∀ z ∈ latAt w W.L, (piW' h).mapMatrix g *ᵥ z ∈ latAt w W.L := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨h1, h2⟩ := lift_mem_latAt h W hy
    show (piW' h).mapMatrix g *ᵥ (fun i => algebraMap E (w.adicCompletion E) (y i)) ∈ _
    rw [← h2]
    have e : (piW' h).mapMatrix g *ᵥ (piW' h ∘ (inFin v (1 : Fv F v) • fun i => inclR (F := F) (AF F) (y i))) =
        piW' h ∘ (g *ᵥ (inFin v (1 : Fv F v) • fun i => inclR (F := F) (AF F) (y i))) :=
      funext fun i => (RingHom.map_mulVec (piW' h) g _ i).symm
    rw [e]
    exact comp_mem_latAt h W (hg _ h1)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have e : (piW' h).mapMatrix g *ᵥ (c • x) = c • ((piW' h).mapMatrix g *ᵥ x) := by
      funext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, Subring.smul_def, mul_left_comm]
    rw [e]
    exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Take `⟨c', hc'⟩` from `hc.exists_right_inv`. Establish `h1 : Valued.v (c : w.adicCompletion E) ≤ 1` using `c.2`. Establish `h2 : Valued.v (c' : w.adicCompletion E) ≤ 1` using `c'.2`. Establish `h3 : Valued.v (c : w.adicCompletion E) * Valued.v (c' : w.adicCompletion E) = 1`. Rewrite using `[← map_mul, ← Subring.coe_mul, hc']`.

Simplify using the standard rewrite rules. Use `le_antisymm h1 ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem valued_eq_one_of_isUnit {c : Formalism.UG.Ov E w} (hc : IsUnit c) : Valued.v (c : w.adicCompletion E) = 1 := by
  obtain ⟨c', hc'⟩ := hc.exists_right_inv
  have h1 : Valued.v (c : w.adicCompletion E) ≤ 1 := c.2
  have h2 : Valued.v (c' : w.adicCompletion E) ≤ 1 := c'.2
  have h3 : Valued.v (c : w.adicCompletion E) * Valued.v (c' : w.adicCompletion E) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, hc']; simp
  refine le_antisymm h1 ?_
  calc (1 : _) = _ := h3.symm
    _ ≤ Valued.v (c : w.adicCompletion E) := mul_le_of_le_one_right' h2

/- English proof (translation)
Use `set T : GL (Fin d) (w.adicCompletion E) := Formalism.UG.bc (piW' h) t with hT`. Establish `hT1 : (T : Matrix (Fin d) (Fin d) (w.adicCompletion E)) = (piW' h).mapMatrix (t : Matrix _ _ _)` using `rfl`. Establish `hT2 : ((T⁻¹ : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)) = (piW' h).mapMatrix ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix _ _ _)`. Rewrite using `[hT, ← map_inv]`. Both sides reduce to the same expression.

Establish `hstab : ∀ z, z ∈ latAt w W.L ↔ (T : Matrix _ _ _) *ᵥ z ∈ latAt w W.L` using `fun z => by`. Use `⟨fun hz => hT1 ▸ mulVec_mem_latAt h W _ (fun z hz => (ht z hz).1) z hz, fun hz => ?_⟩` and prove the remaining obligations. Use `mulVec_mem_latAt h W _ (fun z hz => (ht z hz).2) _ hz` as an intermediate fact. Rewrite `this` using `[← hT2, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Then use the resulting hypothesis. Take `⟨a, ha⟩` from `InertChart.exists_isFrameAt hw hL.fg hL.span_eq_top`.

Take `⟨m, hm⟩` from `((InertChart.isFrameAt_mul ha (one_mem _)).2 T).1 hstab`. Establish `hdet : Matrix.GeneralLinearGroup.det (a⁻¹ * T * a) = Matrix.GeneralLinearGroup.det T`. Rewrite using `[map_mul, map_mul, map_inv, mul_comm _ (Matrix.GeneralLinearGroup.det a), ← mul_assoc, mul_inv_cancel, one_mul]`. Establish `e2 : (piW' h (t : Matrix (Fin d) (Fin d) (AE F E)).det) = ((Matrix.GeneralLinearGroup.det T : (w.adicCompletion E)ˣ) : w.adicCompletion E)`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, hT1, RingHom.map_det]`.

Rewrite using `[e2, ← hdet, ← hm, Matrix.GeneralLinearGroup.val_det_apply]`. Establish `e3 : ((Formalism.UG.bc (Formalism.UG.Ov E w).subtype m : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)).det = ((m.val.det : Formalism.UG.Ov E w) : w.adicCompletion E)` using `by show ((Formalism.UG.Ov E w).subtype.mapMatrix m.val).det = _`. Rewrite using `[← RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[e3]`.

Conclude with `valued_eq_one_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit m))`.
-/
theorem valued_det_eq_one (hw : Formalism.UG.IsInertAt F E v w) {d : ℕ} (W : Spc F E d) (hL : W.L.IsLattice E)
    (t : GL (Fin d) (AE F E))
    (ht : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
      ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    Valued.v (piW' h (t : Matrix (Fin d) (Fin d) (AE F E)).det) = 1 := by
  set T : GL (Fin d) (w.adicCompletion E) := Formalism.UG.bc (piW' h) t with hT
  have hT1 : (T : Matrix (Fin d) (Fin d) (w.adicCompletion E)) = (piW' h).mapMatrix (t : Matrix _ _ _) := rfl
  have hT2 : ((T⁻¹ : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)) =
      (piW' h).mapMatrix ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix _ _ _) := by
    rw [hT, ← map_inv]; rfl
  have hstab : ∀ z, z ∈ latAt w W.L ↔ (T : Matrix _ _ _) *ᵥ z ∈ latAt w W.L := fun z => by
    refine ⟨fun hz => hT1 ▸ mulVec_mem_latAt h W _ (fun z hz => (ht z hz).1) z hz, fun hz => ?_⟩
    have := mulVec_mem_latAt h W _ (fun z hz => (ht z hz).2) _ hz
    rwa [← hT2, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  obtain ⟨a, ha⟩ := InertChart.exists_isFrameAt hw hL.fg hL.span_eq_top
  obtain ⟨m, hm⟩ := ((InertChart.isFrameAt_mul ha (one_mem _)).2 T).1 hstab
  have hdet : Matrix.GeneralLinearGroup.det (a⁻¹ * T * a) = Matrix.GeneralLinearGroup.det T := by
    rw [map_mul, map_mul, map_inv, mul_comm _ (Matrix.GeneralLinearGroup.det a), ← mul_assoc, mul_inv_cancel, one_mul]
  have e2 : (piW' h (t : Matrix (Fin d) (Fin d) (AE F E)).det) =
      ((Matrix.GeneralLinearGroup.det T : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hT1, RingHom.map_det]
  rw [e2, ← hdet, ← hm, Matrix.GeneralLinearGroup.val_det_apply]
  have e3 : ((Formalism.UG.bc (Formalism.UG.Ov E w).subtype m : GL (Fin d) (w.adicCompletion E)) :
      Matrix (Fin d) (Fin d) (w.adicCompletion E)).det = ((m.val.det : Formalism.UG.Ov E w) : w.adicCompletion E) := by
    show ((Formalism.UG.Ov E w).subtype.mapMatrix m.val).det = _
    rw [← RingHom.map_det]; rfl
  rw [e3]
  exact valued_eq_one_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit m))

end Lat

end GlobalTheory.InertDetChr

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hTr v w hw hvT t ht`. Take `⟨ht1, ht2⟩` from `ht`. Establish `h : w.under (𝓞 F) = v` using `(GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl`. Establish `e1` using `GlobalTheory.InertDetChr.eq_ideleAt (GlobalTheory.InertDetChr.at_det_sub_one v t ht1)`. Rewrite using `[e1, GlobalTheory.LFun.ideleAt_eq_locIdele_of_isInertAt h hw]`.

Establish `hunr : GlobalTheory.LFun.UnrAt X.α w` using `hTr.chars.unrα w (by show ¬ (w.under (𝓞 F) ∈ (X.T : Set (Pl F)))`. Rewrite using `[h]`. Conclude with `hvT)` after adjusting the coercions. Establish `hv1` using `GlobalTheory.InertDetChr.valued_det_eq_one h hw G.W hTr.geo.hW.lat t ht2`. Use `set y : (w.adicCompletion E)ˣ := Units.map (toCompl h).toMonoidHom (GlobalTheory.Doubling.unitFin F E v (Matrix.GeneralLinearGroup.det t)) with hy`.

Establish `hyv : (y : w.adicCompletion E) = GlobalTheory.InertDetChr.piW' h ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)).det)`. Rewrite using `[hy, Units.coe_map, GlobalTheory.InertDetChr.piW', RingHom.comp_apply, ← Matrix.GeneralLinearGroup.val_det_apply]`. Both sides reduce to the same expression. Establish `hu : Formalism.L2.Host.IsUnitAt w y`. Unfold `Formalism.L2.Host.IsUnitAt`.

Rewrite using `[hyv]`. Conclude with `hv1`. Establish `hu2` using `hunr y hu`. Establish `hu' : ((Circle.toUnits (X.α (GlobalTheory.LFun.locIdele F w y)) : ℂˣ) : ℂ) = 1` using `congrArg Units.val hu2`. Rewrite `hu'` using `[Circle.toUnits_apply, Units.val_mk0]`.

Conclude with `Circle.ext (by simpa using hu')`.
-/
theorem GlobalTheory.InertDetChr.alpha_det_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ t : GL (Fin (a + a')) (AE F E), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      X.α (Matrix.GeneralLinearGroup.det t) = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hw hvT t ht
  obtain ⟨ht1, ht2⟩ := ht
  have h : w.under (𝓞 F) = v := (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl
  have e1 := GlobalTheory.InertDetChr.eq_ideleAt (GlobalTheory.InertDetChr.at_det_sub_one v t ht1)
  rw [e1, GlobalTheory.LFun.ideleAt_eq_locIdele_of_isInertAt h hw]
  have hunr : GlobalTheory.LFun.UnrAt X.α w := hTr.chars.unrα w (by
    show ¬ (w.under (𝓞 F) ∈ (X.T : Set (Pl F)))
    rw [h]; exact_mod_cast hvT)
  have hv1 := GlobalTheory.InertDetChr.valued_det_eq_one h hw G.W hTr.geo.hW.lat t ht2
  set y : (w.adicCompletion E)ˣ :=
    Units.map (toCompl h).toMonoidHom (GlobalTheory.Doubling.unitFin F E v (Matrix.GeneralLinearGroup.det t)) with hy
  have hyv : (y : w.adicCompletion E) =
      GlobalTheory.InertDetChr.piW' h ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)).det) := by
    rw [hy, Units.coe_map, GlobalTheory.InertDetChr.piW', RingHom.comp_apply, ← Matrix.GeneralLinearGroup.val_det_apply]
    rfl
  have hu : Formalism.L2.Host.IsUnitAt w y := by
    unfold Formalism.L2.Host.IsUnitAt
    rw [hyv]; exact hv1
  have hu2 := hunr y hu
  have hu' : ((Circle.toUnits (X.α (GlobalTheory.LFun.locIdele F w y)) : ℂˣ) : ℂ) = 1 := congrArg Units.val hu2
  rw [Circle.toUnits_apply, Units.val_mk0] at hu'
  exact Circle.ext (by simpa using hu')
