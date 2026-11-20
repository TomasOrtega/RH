import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FixedMemOfOrbitHeightStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependentStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixLatticeIndexIntegralTranslationInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntGramOfFixedStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsConjugateModelExtremalDualParameterStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedLocalDualPairSwapHermitianAdjointStatement

noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

section Glue

open Formalism.UG

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Take `⟨k, rfl⟩` from `hh`. Simplify using `[Formalism.UG.bc]`.
-/
theorem int_entry {m : ℕ} {h : GL (Fin m) L} (hh : h ∈ GLint (Fin m) (intL L)) (i j : Fin m) :
    (h : Matrix (Fin m) (Fin m) L) i j ∈ intL L := by
  obtain ⟨k, rfl⟩ := hh; simp [Formalism.UG.bc]

/- English proof (translation)
Rewrite `hu`, the goal using `[mem_intMat]`. Introduce `i j`. Rewrite using `[Matrix.mul_apply]`. Apply the tactic sequence `exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (int_entry hh i k) (hu k j)`.
-/
theorem mul_mem_intMat {a b : ℕ} {h : GL (Fin a) L} (hh : h ∈ GLint (Fin a) (intL L)) {u : Matrix (Fin a) (Fin b) L}
    (hu : u ∈ intMat L a b) : (h : Matrix (Fin a) (Fin a) L) * u ∈ intMat L a b := by
  rw [mem_intMat] at hu ⊢
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (int_entry hh i k) (hu k j)

def lmulQ {a b : ℕ} (h : GL (Fin a) L) (hh : h ∈ GLint (Fin a) (intL L)) :
    Matrix (Fin a) (Fin b) L ⧸ intMat L a b →+ Matrix (Fin a) (Fin b) L ⧸ intMat L a b :=
  QuotientAddGroup.map _ _
    { toFun := fun x => (h : Matrix (Fin a) (Fin a) L) * x, map_zero' := Matrix.mul_zero _,
      map_add' := Matrix.mul_add _ }
    (fun _ hu => mul_mem_intMat hh hu)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lmulQ_mk {a b : ℕ} (h : GL (Fin a) L) (hh : h ∈ GLint (Fin a) (intL L)) (x : Matrix (Fin a) (Fin b) L) :
    lmulQ h hh (QuotientAddGroup.mk x) = QuotientAddGroup.mk ((h : Matrix (Fin a) (Fin a) L) * x) := rfl

/- English proof (translation)
Proceed by induction on `c using QuotientAddGroup.induction_on with`. Consider the case `H x => simp only [lmulQ_mk, Units.val_mul, Matrix.mul_assoc]`.
-/
theorem lmulQ_mul {a b : ℕ} (h h' : GL (Fin a) L) (hh : h ∈ GLint (Fin a) (intL L)) (hh' : h' ∈ GLint (Fin a) (intL L))
    (hhh : h * h' ∈ GLint (Fin a) (intL L)) (c : Matrix (Fin a) (Fin b) L ⧸ intMat L a b) :
    lmulQ (h * h') hhh c = lmulQ h hh (lmulQ h' hh' c) := by
  induction c using QuotientAddGroup.induction_on with
  | H x => simp only [lmulQ_mk, Units.val_mul, Matrix.mul_assoc]

abbrev KT (σ : L →+* L) {a : ℕ} (J : Matrix (Fin a) (Fin a) L) : Subgroup (UJ σ J) :=
  (GLint (Fin a) (intL L)).comap (UJ σ J).subtype

def actQ (σ : L →+* L) {a b : ℕ} (J : Matrix (Fin a) (Fin a) L) :
    MulAction (KT σ J) (Matrix (Fin a) (Fin b) L ⧸ intMat L a b) where
  smul k c := lmulQ ((k : UJ σ J) : GL (Fin a) L) (Subgroup.mem_comap.1 k.2) c
  one_smul c := by
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      show lmulQ _ _ _ = _
      simp [lmulQ]
  mul_smul k k' c :=
    lmulQ_mul (((k : UJ σ J) : GL (Fin a) L)) (((k' : UJ σ J) : GL (Fin a) L)) _ _ _ c

/- English proof (translation)
Introduce `h`. Use `ψ.map_add_eq_mul a (-a)` as an intermediate fact. Rewrite `this` using `[add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul]`. Conclude with `one_ne_zero this`.
-/
theorem psi_ne_zero (ψ : AddChar L ℂ) (a : L) : ψ a ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

end Glue

section Data

open Formalism.UG

variable {L : Type} [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L}
    {σ : L →+* L} {q : ℕ} {δ : L} {n n' : ℕ} {JS : GL (Fin n) L} {JT : GL (Fin n') L} {ψ : AddChar L ℂ} {M : Type}
    [AddCommGroup M] [Module ℂ M] {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M}
    {ω : UJ σ (JS : Matrix (Fin n) (Fin n) L) × UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M}

/- English proof (translation)
Establish `h1` using `congrArg (fun T : Module.End ℂ M => T s) (hP.rho_mul x u)`. Simplify using `only [Module.End.mul_apply, LinearMap.smul_apply, hs u ((mem_intMat u).1 hu)] at h1`. Take `⟨c, hc, h2⟩ : ∃ c : ℂ, c ≠ 0 ∧ ρ x s = c • ρ (x + u) s` from `⟨_, psi_ne_zero ψ _, h1⟩`. Conclude with `⟨c⁻¹, inv_ne_zero hc, by rw [h2, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩`.
-/
theorem rho_add_int (hP : GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω) {s : M} (hs : GlobalTheory.Hk3.LocVac ρ s)
    (x u : Matrix (Fin n') (Fin n) L) (hu : u ∈ intMat L n' n) : ∃ c : ℂ, c ≠ 0 ∧ ρ (x + u) s = c • ρ x s := by
  have h1 := congrArg (fun T : Module.End ℂ M => T s) (hP.rho_mul x u)
  simp only [Module.End.mul_apply, LinearMap.smul_apply, hs u ((mem_intMat u).1 hu)] at h1
  obtain ⟨c, hc, h2⟩ : ∃ c : ℂ, c ≠ 0 ∧ ρ x s = c • ρ (x + u) s := ⟨_, psi_ne_zero ψ _, h1⟩
  exact ⟨c⁻¹, inv_ne_zero hc, by rw [h2, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

/- English proof (translation)
Establish `hu : -y + x ∈ intMat L n' n` using `QuotientAddGroup.eq.1 hxy.symm`. Take `⟨c, -, hc⟩` from `rho_add_int hP hs y (-y + x) hu`. Rewrite `hc` using `[add_neg_cancel_left]`. Rewrite using `[hc]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span rfl)`.
-/
theorem rho_mem_of_mk_eq (hP : GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω) {s : M} (hs : GlobalTheory.Hk3.LocVac ρ s)
    {x y : Matrix (Fin n') (Fin n) L}
    (hxy : (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) = QuotientAddGroup.mk y) :
    ρ x s ∈ Submodule.span ℂ {ρ y s} := by
  have hu : -y + x ∈ intMat L n' n := QuotientAddGroup.eq.1 hxy.symm
  obtain ⟨c, -, hc⟩ := rho_add_int hP hs y (-y + x) hu
  rw [add_neg_cancel_left] at hc
  rw [hc]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

/- English proof (translation)
Establish `h1` using `congrArg (fun T : Module.End ℂ M => T s) (hP.norm 1 h x)`. Establish `hfix` using `hP.fix 1 h (by simpa using (GLint (Fin n) (intL L)).one_mem) hh s hs`. Simplify using `only [Module.End.mul_apply] at h1`. Rewrite using `[h1, hfix]`. Establish `h1' : (((1 : UJ σ (JS : Matrix (Fin n) (Fin n) L)) : GL (Fin n) L)⁻¹ : GL (Fin n) L) = 1`.

Rewrite using `[OneMemClass.coe_one, inv_one]`. Rewrite using `[h1', Units.val_one, Matrix.mul_one]`.
-/
theorem om_rho (hP : GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω) {s : M} (hs : GlobalTheory.Hk3.LocVac ρ s)
    (h : UJ σ (JT : Matrix (Fin n') (Fin n') L)) (hh : (h : GL (Fin n') L) ∈ GLint (Fin n') (intL L))
    (x : Matrix (Fin n') (Fin n) L) : ω (1, h) (ρ x s) = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s := by
  have h1 := congrArg (fun T : Module.End ℂ M => T s) (hP.norm 1 h x)
  have hfix := hP.fix 1 h (by simpa using (GLint (Fin n) (intL L)).one_mem) hh s hs
  simp only [Module.End.mul_apply] at h1
  rw [h1, hfix]
  have h1' : (((1 : UJ σ (JS : Matrix (Fin n) (Fin n) L)) : GL (Fin n) L)⁻¹ : GL (Fin n) L) = 1 := by
    rw [OneMemClass.coe_one, inv_one]
  rw [h1', Units.val_one, Matrix.mul_one]

/- English proof (translation)
Take `⟨l, hl, hg⟩` from `GlobalTheory.T.exists_int_gram_of_fixed_alt L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hs0 hs hspan x hfix`. Take `⟨v, hv, u, hu, h1, h2⟩` from `GlobalTheory.T.exists_conjugateModel_extremal_dual_parameter L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hs0 hs hspan (x - l) hg`. Establish `hidx : latIdx (x - l) = latIdx x`. Rewrite using `[sub_eq_add_neg]`. Conclude with `(GlobalTheory.T.matrixLatticeIndex_integral_translation_invariance L n' n x).1 _ (neg_mem hl)`.

Use `⟨v, hv, u, by rwa [hidx] at hu, ?_, h2⟩` and prove the remaining obligations. Use `Submodule.span_le.2 ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨h, hh, rfl⟩`. Establish `hm : (QuotientAddGroup.mk (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * (x - l)) : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) = QuotientAddGroup.mk (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x)`. Rewrite using `[QuotientAddGroup.eq, Matrix.mul_sub]`.

Establish `: -(((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * l) + ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x = ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * l` using `by abel`. Rewrite using `[this]`. Conclude with `mul_mem_intMat hh hl`. Establish `hmem : ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧ v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin …` using `Submodule.subset_span ⟨h, hh, rfl⟩`. Conclude with `(Submodule.span_singleton_le_iff_mem _ _).2 hmem (rho_mem_of_mk_eq hP hs hm)`.
-/
theorem step (hP : GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω) (s : M) (hs0 : s ≠ 0) (hs : GlobalTheory.Hk3.LocVac ρ s)
    (hspan : Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤) (x : Matrix (Fin n') (Fin n) L)
    (hfix : ∃ w : M, w ≠ 0 ∧ (∀ h : UJ σ (JT : Matrix (Fin n') (Fin n') L),
        (h : GL (Fin n') L) ∈ GLint (Fin n') (intL L) → ω (1, h) w = w) ∧ w ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s}) :
    ∃ v ∈ Submodule.span ℂ (Set.range fun g : UJ σ (JS : Matrix (Fin n) (Fin n) L) => ω (g, 1) s),
      ∃ u ∈ Submodule.span ℂ {v : M | ∃ y : Matrix (Fin n') (Fin n) L, latIdx y < latIdx x ∧ v = ρ y s},
        v - u ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s} ∧ v - u ≠ 0 := by
  obtain ⟨l, hl, hg⟩ := GlobalTheory.T.exists_int_gram_of_fixed_alt L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hs0 hs hspan x hfix
  obtain ⟨v, hv, u, hu, h1, h2⟩ := GlobalTheory.T.exists_conjugateModel_extremal_dual_parameter L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hs0 hs hspan (x - l) hg
  have hidx : latIdx (x - l) = latIdx x := by
    rw [sub_eq_add_neg]; exact (GlobalTheory.T.matrixLatticeIndex_integral_translation_invariance L n' n x).1 _ (neg_mem hl)
  refine ⟨v, hv, u, by rwa [hidx] at hu, ?_, h2⟩
  refine Submodule.span_le.2 ?_ h1
  rintro _ ⟨h, hh, rfl⟩
  have hm : (QuotientAddGroup.mk (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * (x - l)) :
      Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) = QuotientAddGroup.mk (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) := by
    rw [QuotientAddGroup.eq, Matrix.mul_sub]
    have : -(((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * l) +
        ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x = ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * l := by abel
    rw [this]; exact mul_mem_intMat hh hl
  have hmem : ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s} :=
    Submodule.subset_span ⟨h, hh, rfl⟩
  exact (Submodule.span_singleton_le_iff_mem _ _).2 hmem (rho_mem_of_mk_eq hP hs hm)

end Data

section Half

open Formalism.UG

variable {L : Type} [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L}
    {σ : L →+* L} {q : ℕ} {δ : L} {n n' : ℕ} {JS : GL (Fin n) L} {JT : GL (Fin n') L} {ψ : AddChar L ℂ} {M : Type}
    [AddCommGroup M] [Module ℂ M] {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M}
    {ω : UJ σ (JS : Matrix (Fin n) (Fin n) L) × UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M}

/- English proof (translation)
Use `letI := actQ (b := n) σ (JT : Matrix (Fin n') (Fin n') L)`. Set `V : (Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) → Submodule ℂ M` to `fun c => Submodule.span ℂ {w : M | ∃ x : Matrix (Fin n') (Fin n) L, (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) = c ∧ w = ρ x s}`. Set `π : KT σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M` to `(ω.comp (MonoidHom.inr _ _)).comp (KT σ (JT : Matrix (Fin n') (Fin n') L)).subtype`. Set `μ : (Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) → ℕ` to `fun c => latIdx (Quotient.out c)`. Set `S` to `Submodule.span ℂ (Set.range fun g : UJ σ (JS : Matrix (Fin n) (Fin n) L) => ω (g, 1) s)`.

Establish `hπ_apply : ∀ k v, π k v = ω (1, (k : UJ σ (JT : Matrix (Fin n') (Fin n') L))) v` using `fun _ _ => rfl`. Establish `hsmul : ∀ (k : KT σ (JT : Matrix (Fin n') (Fin n') L)) (x : Matrix (Fin n') (Fin n) L), k • (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) = QuotientAddGroup.mk ((((k : UJ σ (JT : Matrix (Fin n') (Fin n') L)) : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x …` using `fun _ _ => rfl`. Establish `hμmk : ∀ x, μ (QuotientAddGroup.mk x) = latIdx x`. Introduce `x`. Establish `hu : -Quotient.out (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) + x ∈ intMat L n' n` using `QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)`.

Use `(GlobalTheory.T.matrixLatticeIndex_integral_translation_invariance L n' n (Quotient.out (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n))).1 _ hu` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_left]`. Conclude with `this.symm`. Establish `hmemV : ∀ x, ρ x s ∈ V (QuotientAddGroup.mk x)` using `fun x => Submodule.subset_span ⟨x, rfl, rfl⟩`. Establish `hVle : ∀ x, V (QuotientAddGroup.mk x) ≤ Submodule.span ℂ {ρ x s}`.

Introduce `x`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `rho_mem_of_mk_eq hP hs hy`. Establish `hind` using `GlobalTheory.T.latticeModel_vacuumTranslate_classes_independent L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hs`.

Establish `htop : (⨆ c, V c) = ⊤`. Use `eq_top_iff.2 ?_` and prove the remaining obligations. Rewrite using `[← hspan]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`.

Conclude with `Submodule.mem_iSup_of_mem (QuotientAddGroup.mk x) (hmemV x)`. Establish `hline : ∀ c, ∃ v : M, V c ≤ Submodule.span ℂ {v}`. Introduce `c`. Proceed by induction on `c using QuotientAddGroup.induction_on with`. Consider the case `H x => exact ⟨ρ x s, hVle x⟩`.

Establish `hπ : ∀ (k : KT σ (JT : Matrix (Fin n') (Fin n') L)) c, (V c).map (π k) ≤ V (k • c)`. Introduce `k c`. Rewrite using `[Submodule.map_span]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨x, rfl, rfl⟩, rfl⟩`.

Rewrite using `[hπ_apply, om_rho hP hs _ (Subgroup.mem_comap.1 k.2), hsmul]`. Conclude with `hmemV _`. Establish `hμ : ∀ (k : KT σ (JT : Matrix (Fin n') (Fin n') L)) c, μ (k • c) = μ c`. Introduce `k c`. Proceed by induction on `c using QuotientAddGroup.induction_on with`.

Consider the case `H x`. Rewrite using `[hsmul, hμmk, hμmk]`. Conclude with `(GlobalTheory.T.matrixLatticeIndex_integral_translation_invariance L n' n x).2 _ (Subgroup.mem_comap.1 k.2)`. Establish `hS : ∀ v ∈ S, ∀ k, π k v = v`. Introduce `v hv k`.

Establish `hle : S ≤ LinearMap.eqLocus (π k) LinearMap.id`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, rfl⟩`. Use `show π k (ω (g, 1) s) = ω (g, 1) s`. Rewrite using `[hπ_apply, ← Module.End.mul_apply, ← map_mul]`.

Establish `e : ((1 : UJ σ (JS : Matrix (Fin n) (Fin n) L)), (k : UJ σ (JT : Matrix (Fin n') (Fin n') L))) * (g, 1) = (g, 1) * (1, (k : UJ σ (JT : Matrix (Fin n') (Fin n') L)))`. Simplify using the standard rewrite rules. Rewrite using `[e, map_mul, Module.End.mul_apply, hP.fix 1 _ (by simpa using (GLint (Fin n) (intL L)).one_mem) (Subgroup.mem_comap.1 k.2) s hs]`. Conclude with `hle hv`. Establish `hstep : ∀ c, (∃ w : M, w ≠ 0 ∧ (∀ k, π k w = w) ∧ w ∈ ⨆ k : KT σ (JT : Matrix (Fin n') (Fin n') L), V (k • c)) → ∃ v ∈ S, ∃ u ∈ ⨆ (j) (_ : μ j < μ c), V j, v - u ∈ (⨆ k : KT σ (JT : Matrix (Fin n') (Fin n') L), V (k • c)) ∧ v - u ≠ 0`.

Introduce `c hc`. Proceed by induction on `c using QuotientAddGroup.induction_on with`. Consider the case `H x`. Establish `horb1 : (⨆ k : KT σ (JT : Matrix (Fin n') (Fin n') L), V (k • QuotientAddGroup.mk x)) ≤ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧ v = ρ (((h : GL (Fin n') L) : Mat …`. Use `iSup_le fun k => ?_` and prove the remaining obligations.

Rewrite using `[hsmul]`. Use `(hVle _).trans ?_` and prove the remaining obligations. Conclude with `(Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.subset_span ⟨k, Subgroup.mem_comap.1 k.2, rfl⟩)`. Establish `horb2 : Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧ v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s} ≤ (⨆ k : KT σ (JT : Matrix (Fin n') (Fin n') L) …`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨h, hh, rfl⟩`. Use `Submodule.mem_iSup_of_mem (⟨h, hh⟩ : KT σ (JT : Matrix (Fin n') (Fin n') L)) ?_` and prove the remaining obligations. Rewrite using `[hsmul]`. Conclude with `hmemV _`. Take `⟨w, hw0, hwf, hwm⟩` from `hc`.

Take `⟨v, hv, u, hu, h1, h2⟩` from `step hP s hs0 hs hspan x ⟨w, hw0, fun h hh => hwf ⟨h, hh⟩, horb1 hwm⟩`. Use `⟨v, hv, u, ?_, horb2 h1, h2⟩` and prove the remaining obligations. Use `Submodule.span_le.2 ?_ hu` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `Submodule.mem_iSup_of_mem (QuotientAddGroup.mk y) (Submodule.mem_iSup_of_mem ?_ (hmemV y))` and prove the remaining obligations.

Rewrite using `[hμmk, hμmk]`. Conclude with `hy`. Conclude with `GlobalTheory.T.invariant_mem_of_orbit_height_separation π V hind htop hline hπ μ hμ S hS hstep w (fun k => hw k (Subgroup.mem_comap.1 k.2))`.
-/
theorem fixed_mem_span (hP : GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω) (s : M) (hs0 : s ≠ 0) (hs : GlobalTheory.Hk3.LocVac ρ s)
    (hspan : Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤) (w : M)
    (hw : ∀ h : UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ GLint (Fin n') (intL L) → ω (1, h) w = w) :
    w ∈ Submodule.span ℂ (Set.range fun g : UJ σ (JS : Matrix (Fin n) (Fin n) L) => ω (g, 1) s) := by
  letI := actQ (b := n) σ (JT : Matrix (Fin n') (Fin n') L)
  let V : (Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) → Submodule ℂ M := fun c =>
    Submodule.span ℂ {w : M | ∃ x : Matrix (Fin n') (Fin n) L,
      (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) = c ∧ w = ρ x s}
  let π : KT σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M :=
    (ω.comp (MonoidHom.inr _ _)).comp (KT σ (JT : Matrix (Fin n') (Fin n') L)).subtype
  let μ : (Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) → ℕ := fun c => latIdx (Quotient.out c)
  let S := Submodule.span ℂ (Set.range fun g : UJ σ (JS : Matrix (Fin n) (Fin n) L) => ω (g, 1) s)
  have hπ_apply : ∀ k v, π k v = ω (1, (k : UJ σ (JT : Matrix (Fin n') (Fin n') L))) v := fun _ _ => rfl
  have hsmul : ∀ (k : KT σ (JT : Matrix (Fin n') (Fin n') L)) (x : Matrix (Fin n') (Fin n) L),
      k • (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) =
        QuotientAddGroup.mk ((((k : UJ σ (JT : Matrix (Fin n') (Fin n') L)) : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) := fun _ _ => rfl
  have hμmk : ∀ x, μ (QuotientAddGroup.mk x) = latIdx x := by
    intro x
    have hu : -Quotient.out (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n) + x ∈ intMat L n' n :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
    have := (GlobalTheory.T.matrixLatticeIndex_integral_translation_invariance L n' n (Quotient.out (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ intMat L n' n))).1 _ hu
    rw [add_neg_cancel_left] at this
    exact this.symm
  have hmemV : ∀ x, ρ x s ∈ V (QuotientAddGroup.mk x) := fun x => Submodule.subset_span ⟨x, rfl, rfl⟩
  have hVle : ∀ x, V (QuotientAddGroup.mk x) ≤ Submodule.span ℂ {ρ x s} := by
    intro x
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact rho_mem_of_mk_eq hP hs hy
  have hind := GlobalTheory.T.latticeModel_vacuumTranslate_classes_independent L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hs
  have htop : (⨆ c, V c) = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← hspan]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_iSup_of_mem (QuotientAddGroup.mk x) (hmemV x)
  have hline : ∀ c, ∃ v : M, V c ≤ Submodule.span ℂ {v} := by
    intro c
    induction c using QuotientAddGroup.induction_on with
    | H x => exact ⟨ρ x s, hVle x⟩
  have hπ : ∀ (k : KT σ (JT : Matrix (Fin n') (Fin n') L)) c, (V c).map (π k) ≤ V (k • c) := by
    intro k c
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨x, rfl, rfl⟩, rfl⟩
    rw [hπ_apply, om_rho hP hs _ (Subgroup.mem_comap.1 k.2), hsmul]
    exact hmemV _
  have hμ : ∀ (k : KT σ (JT : Matrix (Fin n') (Fin n') L)) c, μ (k • c) = μ c := by
    intro k c
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      rw [hsmul, hμmk, hμmk]
      exact (GlobalTheory.T.matrixLatticeIndex_integral_translation_invariance L n' n x).2 _ (Subgroup.mem_comap.1 k.2)
  have hS : ∀ v ∈ S, ∀ k, π k v = v := by
    intro v hv k
    have hle : S ≤ LinearMap.eqLocus (π k) LinearMap.id := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl⟩
      show π k (ω (g, 1) s) = ω (g, 1) s
      rw [hπ_apply, ← Module.End.mul_apply, ← map_mul]
      have e : ((1 : UJ σ (JS : Matrix (Fin n) (Fin n) L)), (k : UJ σ (JT : Matrix (Fin n') (Fin n') L))) * (g, 1) =
          (g, 1) * (1, (k : UJ σ (JT : Matrix (Fin n') (Fin n') L))) := by
        simp
      rw [e, map_mul, Module.End.mul_apply,
        hP.fix 1 _ (by simpa using (GLint (Fin n) (intL L)).one_mem) (Subgroup.mem_comap.1 k.2) s hs]
    exact hle hv
  have hstep : ∀ c, (∃ w : M, w ≠ 0 ∧ (∀ k, π k w = w) ∧ w ∈ ⨆ k : KT σ (JT : Matrix (Fin n') (Fin n') L), V (k • c)) →
      ∃ v ∈ S, ∃ u ∈ ⨆ (j) (_ : μ j < μ c), V j,
        v - u ∈ (⨆ k : KT σ (JT : Matrix (Fin n') (Fin n') L), V (k • c)) ∧ v - u ≠ 0 := by
    intro c hc
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      have horb1 : (⨆ k : KT σ (JT : Matrix (Fin n') (Fin n') L), V (k • QuotientAddGroup.mk x)) ≤
          Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s} := by
        refine iSup_le fun k => ?_
        rw [hsmul]
        refine (hVle _).trans ?_
        exact (Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.subset_span ⟨k, Subgroup.mem_comap.1 k.2, rfl⟩)
      have horb2 : Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s} ≤
          (⨆ k : KT σ (JT : Matrix (Fin n') (Fin n') L), V (k • QuotientAddGroup.mk x)) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨h, hh, rfl⟩
        refine Submodule.mem_iSup_of_mem (⟨h, hh⟩ : KT σ (JT : Matrix (Fin n') (Fin n') L)) ?_
        rw [hsmul]
        exact hmemV _
      obtain ⟨w, hw0, hwf, hwm⟩ := hc
      obtain ⟨v, hv, u, hu, h1, h2⟩ := step hP s hs0 hs hspan x ⟨w, hw0, fun h hh => hwf ⟨h, hh⟩, horb1 hwm⟩
      refine ⟨v, hv, u, ?_, horb2 h1, h2⟩
      refine Submodule.span_le.2 ?_ hu
      rintro _ ⟨y, hy, rfl⟩
      refine Submodule.mem_iSup_of_mem (QuotientAddGroup.mk y) (Submodule.mem_iSup_of_mem ?_ (hmemV y))
      rw [hμmk, hμmk]
      exact hy
  exact GlobalTheory.T.invariant_mem_of_orbit_height_separation π V hind htop hline hπ μ hμ S hS hstep w (fun k => hw k (Subgroup.mem_comap.1 k.2))

end Half

end GlobalTheory.Hk3.HoweDuality

namespace GlobalTheory.Hk3

open GlobalTheory.Hk3.HoweDuality

/- English proof (translation)
Introduce `L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hs0 hs hspan`. Use `⟨?_, fixed_mem_span hP s hs0 hs hspan⟩` and prove the remaining obligations. Introduce `w hw`. Take `⟨hP', hv', hsp'⟩` from `GlobalTheory.T.unramifiedLocalDualPair_swap_hermitianAdjoint L ϖ σ q δ n n' JS JT ψ M ρ ω hP`. Use `fixed_mem_span hP' s hs0 (hv' s hs) (hsp' s hspan) w (fun h hh => by simpa using hw h hh)` as an intermediate fact.

Simplify using `using this`.
-/
theorem howeUnram_holds : HoweUnram := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hs0 hs hspan
  refine ⟨?_, fixed_mem_span hP s hs0 hs hspan⟩
  intro w hw
  obtain ⟨hP', hv', hsp'⟩ := GlobalTheory.T.unramifiedLocalDualPair_swap_hermitianAdjoint L ϖ σ q δ n n' JS JT ψ M ρ ω hP
  have := fixed_mem_span hP' s hs0 (hv' s hs) (hsp' s hspan) w (fun h hh => by simpa using hw h hh)
  simpa using this

end GlobalTheory.Hk3

end
