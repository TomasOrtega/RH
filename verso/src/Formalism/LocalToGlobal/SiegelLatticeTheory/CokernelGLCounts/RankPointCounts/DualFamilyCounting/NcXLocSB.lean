import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXKfOrb
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DetAdmA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DetAdmC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensFibV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoGram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatStab
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensPos

noncomputable section

namespace Formalism.L2.SG.Pf.NcX.LocSBPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol NumberField IsDedekindDomain
  MeasureTheory Topology Filter
open Formalism.L2.SG.Pf.NcX.FinVolSk Formalism.L2.SG.Pf.NcX.KfOrbPf
open scoped TensorProduct

def WittLocT : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (a : ℕ) (X0 : Fin a → Fin n → E),
    IsCMExt F E σ → IsHermND σ J → (gramE σ J X0).det ≠ 0 →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (X : Fin a → Fin n → Fv F v ⊗[F] E),
      gramR (Fv F v) σ J X = (gramE σ J X0).map (inclR (Fv F v)) →
      ∃ g : HA (Fv F v) σ J, g • ratTup (F := F) (Fv F v) X0 = X

def IntWittAE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (a : ℕ) (X0 : Fin a → Fin n → E)
    (Λ : Set (Fin n → E)),
    IsCMExt F E σ → IsHermND σ J → (gramE σ J X0).det ≠ 0 →
    (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E),
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ X ∈ latV (M := n) (n := a) b v,
      gramR (Fv F v) σ J X = (gramE σ J X0).map (inclR (Fv F v)) →
      ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, k • ratTup (F := F) (Fv F v) X0 = X

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Establish `hg : Formalism.UG.cT (sigR R σ) ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) _) * JR R J * ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) _) = JR R J` using `g.2`. Use `show Formalism.UG.hform (sigR R σ) (JR R J) (((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) _).mulVec (X i)) (((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) _).mulVec (X j)) = Formalism.UG.hform (sigR R σ) (JR R J) (X i) (X j)`. Rewrite using `[PI.VolStabW.TopoGram.hform_mulVec, hg]`.
-/
theorem gram_smul (R : Type) [CommRing R] [Algebra F R] {a : ℕ} (g : HA R σ J)
    (X : Fin a → Fin n → R ⊗[F] E) : gramR R σ J (g • X) = gramR R σ J X := by
  funext i j
  have hg : Formalism.UG.cT (sigR R σ) ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) _) *
      JR R J * ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) _) = JR R J := g.2
  show Formalism.UG.hform (sigR R σ) (JR R J)
      (((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) _).mulVec (X i))
      (((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) _).mulVec (X j)) =
    Formalism.UG.hform (sigR R σ) (JR R J) (X i) (X j)
  rw [PI.VolStabW.TopoGram.hform_mulVec, hg]

/- English proof (translation)
Rewrite using `[Kf, Subgroup.mem_iInf]`. Conclude with `Iff.rfl`.
-/
theorem mem_Kf_iff (Λ : Set (Fin n → E)) (k : HA (Af F) σ J) :
    k ∈ Kf σ J Λ ↔ ∀ v, haMap σ J (evalV F v) k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v := by
  rw [Kf, Subgroup.mem_iInf]
  exact Iff.rfl

variable [FiniteDimensional F E]

/- English proof (translation)
Set `mat : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)` to `fun v => ((HA.mat (Fv F v) σ J (kv v) : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))`. Set `imat : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)` to `fun v => (((HA.mat (Fv F v) σ J (kv v))⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))`. Take `⟨Γ, -, hΓ⟩` from `PI.VolStabW.rpGlue_holds F E n n _ b`. Set `A : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)` to `projFin (Γ (0, mat))`. Set `A' : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)` to `projFin (Γ (0, imat))`.

Establish `hA : ∀ v, A.map (tensMap (E` using `E) (evalV F v)) = mat v := (hΓ (0, mat) h1).2`. Establish `hA' : ∀ v, A'.map (tensMap (E` using `E) (evalV F v)) = imat v := (hΓ (0, imat) h2).2`. Establish `hAA' : A * A' = 1`. Use `Formalism.L2.SG.Pf.NcX.OmDecompPf.projV_ext b fun v => ?_` and prove the remaining obligations. Rewrite using `[projV_eq_map, projV_eq_map, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA, hA']`.

Conclude with `Units.mul_inv (HA.mat (Fv F v) σ J (kv v))`. Establish `hA'A : A' * A = 1`. Use `Formalism.L2.SG.Pf.NcX.OmDecompPf.projV_ext b fun v => ?_` and prove the remaining obligations. Rewrite using `[projV_eq_map, projV_eq_map, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA, hA']`. Conclude with `Units.inv_mul (HA.mat (Fv F v) σ J (kv v))`.

Set `gGL : GL (Fin n) (Af F ⊗[F] E)` to `⟨A, A', hAA', hA'A⟩`. Establish `hcT : ∀ v (X : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)), (Formalism.UG.cT (sigR (Af F) σ) X).map (tensMap (E` using `E) (evalV F v)) = Formalism.UG.cT (sigR (Fv F v) σ) (X.map (tensMap (E := E) (evalV F v))) := by`. Introduce `v X`. Use extensionality with `i j`. Simplify using `only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]`.

Conclude with `PI.VolStabW.RestrProdG.map_sigR (evalV F v) σ (X j i)`. Establish `hJR : ∀ v, (JR (Af F) J).map (tensMap (E` using `E) (evalV F v)) = JR (Fv F v) J := by`. Introduce `v`. Use extensionality with `i j`. Conclude with `PI.VolStabW.RestrProdG.map_inclR (evalV F v) (J i j)`.

Establish `hmem : gGL ∈ HR (Af F) σ J` using `by show Formalism.UG.cT (sigR (Af F) σ) A * JR (Af F) J * A = JR (Af F) J`. Use `Formalism.L2.SG.Pf.NcX.OmDecompPf.projV_ext b fun v => ?_` and prove the remaining obligations. Rewrite using `[projV_eq_map, projV_eq_map, Matrix.map_mul, Matrix.map_mul, hcT, hJR, hA]`. Conclude with `(kv v).2`. Use `⟨(⟨gGL, hmem⟩ : HR (Af F) σ J), fun v => ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `hA v`.
-/
theorem glue_HA {d : ℕ} (b : Module.Basis (Fin d) F E) (kv : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J)
    (h1 : ∀ᶠ v in cofinite, (((HA.mat (Fv F v) σ J (kv v) : GL (Fin n) (Fv F v ⊗[F] E)) :
      Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : Fin n → Fin n → Fv F v ⊗[F] E) ∈ latV b v)
    (h2 : ∀ᶠ v in cofinite, ((((HA.mat (Fv F v) σ J (kv v))⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) :
      Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : Fin n → Fin n → Fv F v ⊗[F] E) ∈ latV b v) :
    ∃ k : HA (Af F) σ J, ∀ v, haMap σ J (evalV F v) k = kv v := by
  classical
  let mat : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := fun v =>
    ((HA.mat (Fv F v) σ J (kv v) : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
  let imat : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := fun v =>
    (((HA.mat (Fv F v) σ J (kv v))⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
  obtain ⟨Γ, -, hΓ⟩ := PI.VolStabW.rpGlue_holds F E n n _ b
  let A : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) := projFin (Γ (0, mat))
  let A' : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) := projFin (Γ (0, imat))
  have hA : ∀ v, A.map (tensMap (E := E) (evalV F v)) = mat v := (hΓ (0, mat) h1).2
  have hA' : ∀ v, A'.map (tensMap (E := E) (evalV F v)) = imat v := (hΓ (0, imat) h2).2
  have hAA' : A * A' = 1 := by
    refine Formalism.L2.SG.Pf.NcX.OmDecompPf.projV_ext b fun v => ?_
    rw [projV_eq_map, projV_eq_map, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA, hA']
    exact Units.mul_inv (HA.mat (Fv F v) σ J (kv v))
  have hA'A : A' * A = 1 := by
    refine Formalism.L2.SG.Pf.NcX.OmDecompPf.projV_ext b fun v => ?_
    rw [projV_eq_map, projV_eq_map, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA, hA']
    exact Units.inv_mul (HA.mat (Fv F v) σ J (kv v))
  let gGL : GL (Fin n) (Af F ⊗[F] E) := ⟨A, A', hAA', hA'A⟩
  have hcT : ∀ v (X : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)),
      (Formalism.UG.cT (sigR (Af F) σ) X).map (tensMap (E := E) (evalV F v)) =
        Formalism.UG.cT (sigR (Fv F v) σ) (X.map (tensMap (E := E) (evalV F v))) := by
    intro v X
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
    exact PI.VolStabW.RestrProdG.map_sigR (evalV F v) σ (X j i)
  have hJR : ∀ v, (JR (Af F) J).map (tensMap (E := E) (evalV F v)) = JR (Fv F v) J := by
    intro v
    ext i j
    exact PI.VolStabW.RestrProdG.map_inclR (evalV F v) (J i j)
  have hmem : gGL ∈ HR (Af F) σ J := by
    show Formalism.UG.cT (sigR (Af F) σ) A * JR (Af F) J * A = JR (Af F) J
    refine Formalism.L2.SG.Pf.NcX.OmDecompPf.projV_ext b fun v => ?_
    rw [projV_eq_map, projV_eq_map, Matrix.map_mul, Matrix.map_mul, hcT, hJR, hA]
    exact (kv v).2
  refine ⟨(⟨gGL, hmem⟩ : HR (Af F) σ J), fun v => ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact hA v

/- English proof (translation)
Establish `hmat : Continuous (fun g : HA R σ J => ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)))` using `Units.continuous_val.comp continuous_subtype_val`. Use `continuous_pi fun c => ?_` and prove the remaining obligations. Use `show Continuous (fun p : HA R σ J × (Fin a → Fin n → R ⊗[F] E) => ((HA.mat R σ J p.1 : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).mulVec (p.2 c))`. Conclude with `(hmat.comp continuous_fst).matrix_mulVec ((continuous_apply c).comp continuous_snd)`.
-/
theorem continuous_act (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] {a : ℕ} :
    Continuous (fun p : HA R σ J × (Fin a → Fin n → R ⊗[F] E) => p.1 • p.2) := by
  have hmat : Continuous (fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))) :=
    Units.continuous_val.comp continuous_subtype_val
  refine continuous_pi fun c => ?_
  show Continuous (fun p : HA R σ J × (Fin a → Fin n → R ⊗[F] E) =>
    ((HA.mat R σ J p.1 : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).mulVec (p.2 c))
  exact (hmat.comp continuous_fst).matrix_mulVec ((continuous_apply c).comp continuous_snd)

/- English proof (translation)
Set `b` to `Module.finBasis F E`. Establish `: LocallyCompactSpace (Fv F v)` using `PI.VolStabW.locallyCompact_Fv F v`. Establish `hone : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in cofinite, ((1 : Matrix (Fin n) (Fin n) (Fv F w ⊗[F] E)) : Fin n → Fin n → Fv F w ⊗[F] E) ∈ latV b w` using `by filter_upwards [ev_crd_oev b] with w hw`. Introduce `i j l`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Simplify using `only [Matrix.one_apply_eq]`. Establish `h1mem : (1 : Fv F w ⊗[F] E) ∈ OEv (E` using `E) w := by show (1 : Fv F w ⊗[F] E) ∈ Submodule.span (w.adicCompletionIntegers F) ((fun x : 𝓞 E => inclR (F := F) (Fv F w) (x : E)) '' Set.univ)`. Establish `: inclR (F` using `F) (Fv F w) ((1 : 𝓞 E) : E) ∈ Submodule.span (w.adicCompletionIntegers F) ((fun x : 𝓞 E => inclR (F := F) (Fv F w) (x : E)) '' Set.univ) := Submodule.subset_span (Set.mem_image_of_mem _ (Set.mem_univ _))`. Establish `e1 : inclR (F` using `F) (Fv F w) ((1 : 𝓞 E) : E) = 1 := by simp [inclR, Algebra.TensorProduct.one_def]`.

Rewrite `this` using `[e1]`. Then use the resulting hypothesis. Conclude with `hw 1 h1mem l`. Simplify using `only [Matrix.one_apply_ne h]`. Conclude with `hw 0 (Submodule.zero_mem _) l`. Establish `hsurj : ∀ g : HA (Fv F v) σ J, ∃ k : HA (Af F) σ J, (∀ w, w ≠ v → haMap σ J (evalV F w) k = 1) ∧ haMap σ J (evalV F v) k = g`.

Introduce `g`. Set `kv : ∀ w : HeightOneSpectrum (𝓞 F), HA (Fv F w) σ J` to `Function.update (fun w => 1) v g`. Establish `hev : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in cofinite, kv w = 1` using `(Filter.eventually_cofinite_ne v).mono fun w hw => by simp [kv, Function.update_of_ne hw]`. Take `⟨k, hk⟩` from `glue_HA σ J b kv (by filter_upwards [hev, hone] with w hw h1`. Rewrite using `[hw]`.

Use `show (((1 : GL (Fin n) (Fv F w ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F w ⊗[F] E)) : Fin n → Fin n → Fv F w ⊗[F] E) ∈ _`. Rewrite using `[Units.val_one]`. Conclude with `h1)`. Use the proof step `(by filter_upwards [hev, hone] with w hw h1`. Rewrite using `[hw]`.

Use `show ((((1 : GL (Fin n) (Fv F w ⊗[F] E))⁻¹ : GL (Fin n) (Fv F w ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F w ⊗[F] E)) : Fin n → Fin n → Fv F w ⊗[F] E) ∈ _`. Rewrite using `[inv_one, Units.val_one]`. Conclude with `h1)`. Use `⟨k, fun w hw => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hk w]`.

Simplify using `[kv, Function.update_of_ne hw]`. Rewrite using `[hk v]`. Simplify using `[kv]`. Establish `hone_mem : ∀ w, (1 : HA (Fv F w) σ J) ∈ Formalism.L2.SG.TypedSets.Kv σ J (L : Set (Fin n → E)) w` using `fun w => (Kloc (E := E) w (L : Set (Fin n → E))).one_mem`. Establish `himg : Formalism.L2.SG.TypedSets.Kv σ J (L : Set (Fin n → E)) v = haMap σ J (evalV F v) '' (Kf σ J (L : Set (Fin n → E)) : Set (HA (Af F) σ J))`.

Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce `hg`. Take `⟨k, hk1, hk2⟩` from `hsurj g`. Use `⟨k, (mem_Kf_iff σ J _ k).2 fun w => ?_, hk2⟩` and prove the remaining obligations.

Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[hk2]`. Conclude with `hg`. Rewrite using `[hk1 w hw]`.

Conclude with `hone_mem w`. Introduce and unpack `⟨k, hk, rfl⟩`. Conclude with `(mem_Kf_iff σ J _ k).1 hk v`. Establish `hcont : Continuous (haMap σ J (evalV F v))` using `PI.UnitaryGroupMassFormula.MeasWCore.continuous_haMap σ J (evalV F v) (MassDataMassesW.KCptW.continuous_tensEval v)`. Take `⟨hKc, hKo⟩` from `Formalism.L2.SG.Pf.NcX.AdTupPf.kf_compact_open σ J L hL`.

Use `⟨himg ▸ hKc.image hcont, ?_⟩` and prove the remaining obligations. Establish `: SecondCountableTopology (HA (Af F) σ J)` using `PI.VolStabW.TopoAF.secondCountable_HA_of (Af F) σ J`. Establish `: SigmaCompactSpace (HA (Af F) σ J)` using `sigmaCompactSpace_of_locallyCompact_secondCountable`. Establish `: T2Space (Fv F v ⊗[F] E)` using `PI.VolStabW.RestrProdG.t2_tensor_product (Fv F v)`. Establish `hopen` using `MonoidHom.isOpenMap_of_sigmaCompact (haMap σ J (evalV F v)) (fun g => (hsurj g).elim fun k hk => ⟨k, hk.2⟩) hcont`.

Rewrite using `[himg]`. Conclude with `hopen _ hKo`.
-/
theorem kv_compact_open (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (Formalism.L2.SG.TypedSets.Kv σ J (L : Set (Fin n → E)) v) ∧
      IsOpen (Formalism.L2.SG.TypedSets.Kv σ J (L : Set (Fin n → E)) v) := by
  classical
  let b := Module.finBasis F E
  have : LocallyCompactSpace (Fv F v) := PI.VolStabW.locallyCompact_Fv F v
  have hone : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in cofinite,
      ((1 : Matrix (Fin n) (Fin n) (Fv F w ⊗[F] E)) : Fin n → Fin n → Fv F w ⊗[F] E) ∈ latV b w := by
    filter_upwards [ev_crd_oev b] with w hw
    intro i j l
    by_cases h : i = j
    · subst h
      simp only [Matrix.one_apply_eq]
      have h1mem : (1 : Fv F w ⊗[F] E) ∈ OEv (E := E) w := by
        show (1 : Fv F w ⊗[F] E) ∈ Submodule.span (w.adicCompletionIntegers F)
          ((fun x : 𝓞 E => inclR (F := F) (Fv F w) (x : E)) '' Set.univ)
        have : inclR (F := F) (Fv F w) ((1 : 𝓞 E) : E) ∈ Submodule.span (w.adicCompletionIntegers F)
            ((fun x : 𝓞 E => inclR (F := F) (Fv F w) (x : E)) '' Set.univ) :=
          Submodule.subset_span (Set.mem_image_of_mem _ (Set.mem_univ _))
        have e1 : inclR (F := F) (Fv F w) ((1 : 𝓞 E) : E) = 1 := by simp [inclR, Algebra.TensorProduct.one_def]
        rwa [e1] at this
      exact hw 1 h1mem l
    · simp only [Matrix.one_apply_ne h]
      exact hw 0 (Submodule.zero_mem _) l
  have hsurj : ∀ g : HA (Fv F v) σ J, ∃ k : HA (Af F) σ J,
      (∀ w, w ≠ v → haMap σ J (evalV F w) k = 1) ∧ haMap σ J (evalV F v) k = g := by
    intro g
    let kv : ∀ w : HeightOneSpectrum (𝓞 F), HA (Fv F w) σ J := Function.update (fun w => 1) v g
    have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in cofinite, kv w = 1 :=
      (Filter.eventually_cofinite_ne v).mono fun w hw => by simp [kv, Function.update_of_ne hw]
    obtain ⟨k, hk⟩ := glue_HA σ J b kv
      (by
        filter_upwards [hev, hone] with w hw h1
        rw [hw]
        show (((1 : GL (Fin n) (Fv F w ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F w ⊗[F] E)) :
          Fin n → Fin n → Fv F w ⊗[F] E) ∈ _
        rw [Units.val_one]; exact h1)
      (by
        filter_upwards [hev, hone] with w hw h1
        rw [hw]
        show ((((1 : GL (Fin n) (Fv F w ⊗[F] E))⁻¹ : GL (Fin n) (Fv F w ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (Fv F w ⊗[F] E)) : Fin n → Fin n → Fv F w ⊗[F] E) ∈ _
        rw [inv_one, Units.val_one]; exact h1)
    refine ⟨k, fun w hw => ?_, ?_⟩
    · rw [hk w]; simp [kv, Function.update_of_ne hw]
    · rw [hk v]; simp [kv]
  have hone_mem : ∀ w, (1 : HA (Fv F w) σ J) ∈ Formalism.L2.SG.TypedSets.Kv σ J (L : Set (Fin n → E)) w :=
    fun w => (Kloc (E := E) w (L : Set (Fin n → E))).one_mem
  have himg : Formalism.L2.SG.TypedSets.Kv σ J (L : Set (Fin n → E)) v =
      haMap σ J (evalV F v) '' (Kf σ J (L : Set (Fin n → E)) : Set (HA (Af F) σ J)) := by
    ext g
    constructor
    · intro hg
      obtain ⟨k, hk1, hk2⟩ := hsurj g
      refine ⟨k, (mem_Kf_iff σ J _ k).2 fun w => ?_, hk2⟩
      by_cases hw : w = v
      · subst hw; rw [hk2]; exact hg
      · rw [hk1 w hw]; exact hone_mem w
    · rintro ⟨k, hk, rfl⟩
      exact (mem_Kf_iff σ J _ k).1 hk v
  have hcont : Continuous (haMap σ J (evalV F v)) :=
    PI.UnitaryGroupMassFormula.MeasWCore.continuous_haMap σ J (evalV F v) (MassDataMassesW.KCptW.continuous_tensEval v)
  obtain ⟨hKc, hKo⟩ := Formalism.L2.SG.Pf.NcX.AdTupPf.kf_compact_open σ J L hL
  refine ⟨himg ▸ hKc.image hcont, ?_⟩
  have : SecondCountableTopology (HA (Af F) σ J) :=
    PI.VolStabW.TopoAF.secondCountable_HA_of (Af F) σ J
  have : SigmaCompactSpace (HA (Af F) σ J) := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : T2Space (Fv F v ⊗[F] E) := PI.VolStabW.RestrProdG.t2_tensor_product (Fv F v)
  have hopen := MonoidHom.isOpenMap_of_sigmaCompact (haMap σ J (evalV F v))
    (fun g => (hsurj g).elim fun k hk => ⟨k, hk.2⟩) hcont
  rw [himg]
  exact hopen _ hKo

/- English proof (translation)
Set `b` to `Module.finBasis F E`. Establish `: LocallyCompactSpace (Fv F v)` using `PI.VolStabW.locallyCompact_Fv F v`. Set `h` to `PI.VolStabW.DeterminantAdmissible.crdH (a := a) (M := n) b (Fv F v)`. Take `⟨V, hV, hpV, hVO⟩` from `(loc_compact_Haus_tot_disc_of_zero_dim (H := Fin a × Fin n × Fin (Module.finrank F E) → Fv F v)).exists_subset_of_mem_open (Set.mem_image_of_mem h hy) (h.isOpenMap O hO)`. Set `K : Set (Fin a × Fin n × Fin (Module.finrank F E) → Fv F v)` to `Set.pi Set.univ fun c => (Homeomorph.subRight (h y c)) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))`.

Establish `hKo : IsClopen K` using `⟨isClosed_set_pi fun c _ => (PI.VolStabW.DeterminantAdmissible.isClopen_translate v (h y c)).isClosed, isOpen_set_pi Set.finite_univ fun c _ => (PI.VolStabW.DeterminantAdmissible.isClopen_translate v (h y c)).isOpen⟩`. Establish `hKc : IsCompact K` using `isCompact_univ_pi fun c => PI.VolStabW.DeterminantAdmissible.isCompact_translate v (h y c)`. Establish `hpK : h y ∈ K` using `fun c _ => PI.VolStabW.DeterminantAdmissible.mem_translate v (h y c)`. Use `⟨h ⁻¹' (V ∩ K), (hV.inter hKo).preimage h.continuous, h.isCompact_preimage.2 (hKc.of_isClosed_subset (hV.inter hKo).isClosed Set.inter_subset_right), ⟨hpV, hpK⟩, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨z', hz', hzz⟩` from `hVO hz.1`.

Rewrite using `[← h.injective hzz]`. Conclude with `hz'`.
-/
theorem exists_cc_tup (v : HeightOneSpectrum (𝓞 F)) {a : ℕ} {O : Set (Fin a → Fin n → Fv F v ⊗[F] E)}
    (hO : IsOpen O) {y : Fin a → Fin n → Fv F v ⊗[F] E} (hy : y ∈ O) :
    ∃ W, IsClopen W ∧ IsCompact W ∧ y ∈ W ∧ W ⊆ O := by
  classical
  let b := Module.finBasis F E
  have : LocallyCompactSpace (Fv F v) := PI.VolStabW.locallyCompact_Fv F v
  let h := PI.VolStabW.DeterminantAdmissible.crdH (a := a) (M := n) b (Fv F v)
  obtain ⟨V, hV, hpV, hVO⟩ :=
    (loc_compact_Haus_tot_disc_of_zero_dim (H := Fin a × Fin n × Fin (Module.finrank F E) → Fv F v)).exists_subset_of_mem_open
      (Set.mem_image_of_mem h hy) (h.isOpenMap O hO)
  let K : Set (Fin a × Fin n × Fin (Module.finrank F E) → Fv F v) :=
    Set.pi Set.univ fun c => (Homeomorph.subRight (h y c)) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))
  have hKo : IsClopen K :=
    ⟨isClosed_set_pi fun c _ => (PI.VolStabW.DeterminantAdmissible.isClopen_translate v (h y c)).isClosed,
      isOpen_set_pi Set.finite_univ fun c _ => (PI.VolStabW.DeterminantAdmissible.isClopen_translate v (h y c)).isOpen⟩
  have hKc : IsCompact K := isCompact_univ_pi fun c => PI.VolStabW.DeterminantAdmissible.isCompact_translate v (h y c)
  have hpK : h y ∈ K := fun c _ => PI.VolStabW.DeterminantAdmissible.mem_translate v (h y c)
  refine ⟨h ⁻¹' (V ∩ K), (hV.inter hKo).preimage h.continuous,
    h.isCompact_preimage.2 (hKc.of_isClosed_subset (hV.inter hKo).isClosed Set.inter_subset_right),
    ⟨hpV, hpK⟩, fun z hz => ?_⟩
  obtain ⟨z', hz', hzz⟩ := hVO hz.1
  rw [← h.injective hzz]
  exact hz'

end Gen

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {a : ℕ} (X0 : Fin a → Fin n → E)

/- English proof (translation)
Establish `: LocallyCompactSpace (Fv F v)` using `PI.VolStabW.locallyCompact_Fv F v`. Establish `: T2Space (Fv F v ⊗[F] E)` using `PI.VolStabW.RestrProdG.t2_tensor_product (Fv F v)`. Use `set Tv : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := (gramE σ J X0).map (inclR (F := F) (Fv F v)) with hTv`. Use `set Yv := ratTup (F := F) (Fv F v) X0 with hYv`. Use `set LT : Set (Fin a → Fin n → Fv F v ⊗[F] E) := {X | gramR (Fv F v) σ J X = Tv} with hLT`.

Use `set KY : Set (Fin a → Fin n → Fv F v ⊗[F] E) := {X | ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J (L : Set (Fin n → E)) v, X = k • Yv} with hKY`. Establish `hYLT : Yv ∈ LT` using `PI.VolStabW.LocPosW.gramR_ratTup (Fv F v) σ J X0`. Establish `hLTcl : IsClosed LT`. Establish `: T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))` using `inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))`. Conclude with `isClosed_eq (PI.VolStabW.continuous_gramR (Fv F v) σ J) continuous_const`.

Establish `hsmulLT : ∀ (g : HA (Fv F v) σ J) (X : Fin a → Fin n → Fv F v ⊗[F] E), X ∈ LT → g • X ∈ LT`. Introduce `g X hX`. Use `show gramR (Fv F v) σ J (g • X) = Tv`. Rewrite using `[gram_smul]`. Conclude with `hX`.

Set `S : SubMulAction (HA (Fv F v) σ J) (Fin a → Fin n → Fv F v ⊗[F] E)` to `{ carrier := LT, smul_mem' := fun g X hX => hsmulLT g X hX }`. Establish `: ContinuousSMul (HA (Fv F v) σ J) S` using `⟨continuous_induced_rng.2 ((continuous_act σ J (Fv F v)).comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))⟩`. Establish `: MulAction.IsPretransitive (HA (Fv F v) σ J) S` using `⟨fun x y => by`. Take `⟨g, hg⟩` from `hW x.1 x.2`. Take `⟨h, hh⟩` from `hW y.1 y.2`.

Use `⟨h * g⁻¹, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show (h * g⁻¹) • x.1 = y.1`. Rewrite using `[← hg, smul_smul, inv_mul_cancel_right, hh]⟩`. Establish `: LocallyCompactSpace S` using `hLTcl.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Establish `: SecondCountableTopology (HA (Fv F v) σ J)` using `PI.VolStabW.TopoAF.secondCountable_HA_of (Fv F v) σ J`.

Establish `: SigmaCompactSpace (HA (Fv F v) σ J)` using `sigmaCompactSpace_of_locallyCompact_secondCountable`. Establish `hop` using `isOpenMap_smul_of_sigmaCompact (G := HA (Fv F v) σ J) (X := S) ⟨Yv, hYLT⟩`. Take `⟨hKc, hKo⟩` from `kv_compact_open σ J L hL v`. Take `⟨O, hOo, hOeq⟩` from `isOpen_induced_iff.1 (hop _ hKo)`. Establish `hKYO : KY ⊆ O`.

Introduce and unpack `_ ⟨k, hk, rfl⟩`. Establish `: (⟨k • Yv, hsmulLT k Yv hYLT⟩ : S) ∈ Subtype.val ⁻¹' O`. Rewrite using `[hOeq]`. Conclude with `⟨k, hk, rfl⟩`. Conclude with `this`.

Establish `hOLT : O ∩ LT ⊆ KY`. Introduce and unpack `X ⟨hXO, hXT⟩`. Establish `: (⟨X, hXT⟩ : S) ∈ Subtype.val ⁻¹' O` using `hXO`. Rewrite `this` using `[hOeq]`. Take `⟨k, hk, hkX⟩` from `this`.

Conclude with `⟨k, hk, (congrArg Subtype.val hkX).symm⟩`. Establish `hKYLT : KY ⊆ LT`. Introduce and unpack `_ ⟨k, hk, rfl⟩`. Conclude with `hsmulLT k Yv hYLT`. Establish `hKYc : IsCompact KY`.

Establish `e : KY = (fun k : HA (Fv F v) σ J => k • Yv) '' (Formalism.L2.SG.TypedSets.Kv σ J (L : Set (Fin n → E)) v)`. Use extensionality with `X`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`. Conclude with `⟨k, hk, rfl⟩`.

Introduce and unpack `⟨k, hk, rfl⟩`. Conclude with `⟨k, hk, rfl⟩`. Rewrite using `[e]`. Conclude with `hKc.image ((continuous_act σ J (Fv F v)).comp (continuous_id.prodMk continuous_const))`. Use `choose W hWo hWc hyW hWO using fun y : KY => exists_cc_tup v hOo (hKYO y.2)`.

Take `⟨t, ht⟩` from `hKYc.elim_finite_subcover (fun y : KY => W y) (fun y => (hWo y).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyW _⟩)`. Use `⟨⋃ y ∈ t, W y, isClopen_biUnion_finset fun y _ => hWo y, t.isCompact_biUnion fun y _ => hWc y, ?_⟩` and prove the remaining obligations. Use extensionality with `X`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hXC, hXT⟩`.

Take `⟨y, -, hy⟩` from `Set.mem_iUnion₂.1 hXC`. Conclude with `hOLT ⟨hWO y hy, hXT⟩`. Introduce `hX`. Conclude with `⟨ht hX, hKYLT hX⟩`.
-/
theorem exists_C (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (hW : ∀ X : Fin a → Fin n → Fv F v ⊗[F] E, gramR (Fv F v) σ J X = (gramE σ J X0).map (inclR (Fv F v)) →
      ∃ g : HA (Fv F v) σ J, g • ratTup (F := F) (Fv F v) X0 = X) :
    ∃ C : Set (Fin a → Fin n → Fv F v ⊗[F] E), IsClopen C ∧ IsCompact C ∧
      C ∩ {X | gramR (Fv F v) σ J X = (gramE σ J X0).map (inclR (Fv F v))} =
        {X | ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J (L : Set (Fin n → E)) v, X = k • ratTup (F := F) (Fv F v) X0} := by
  classical
  have : LocallyCompactSpace (Fv F v) := PI.VolStabW.locallyCompact_Fv F v
  have : T2Space (Fv F v ⊗[F] E) := PI.VolStabW.RestrProdG.t2_tensor_product (Fv F v)
  set Tv : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := (gramE σ J X0).map (inclR (F := F) (Fv F v)) with hTv
  set Yv := ratTup (F := F) (Fv F v) X0 with hYv
  set LT : Set (Fin a → Fin n → Fv F v ⊗[F] E) := {X | gramR (Fv F v) σ J X = Tv} with hLT
  set KY : Set (Fin a → Fin n → Fv F v ⊗[F] E) :=
    {X | ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J (L : Set (Fin n → E)) v, X = k • Yv} with hKY
  have hYLT : Yv ∈ LT := PI.VolStabW.LocPosW.gramR_ratTup (Fv F v) σ J X0
  have hLTcl : IsClosed LT := by
    have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
      inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
    exact isClosed_eq (PI.VolStabW.continuous_gramR (Fv F v) σ J) continuous_const
  have hsmulLT : ∀ (g : HA (Fv F v) σ J) (X : Fin a → Fin n → Fv F v ⊗[F] E), X ∈ LT → g • X ∈ LT := by
    intro g X hX
    show gramR (Fv F v) σ J (g • X) = Tv
    rw [gram_smul]
    exact hX
  let S : SubMulAction (HA (Fv F v) σ J) (Fin a → Fin n → Fv F v ⊗[F] E) :=
    { carrier := LT, smul_mem' := fun g X hX => hsmulLT g X hX }
  have : ContinuousSMul (HA (Fv F v) σ J) S :=
    ⟨continuous_induced_rng.2 ((continuous_act σ J (Fv F v)).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))⟩
  have : MulAction.IsPretransitive (HA (Fv F v) σ J) S := ⟨fun x y => by
    obtain ⟨g, hg⟩ := hW x.1 x.2
    obtain ⟨h, hh⟩ := hW y.1 y.2
    refine ⟨h * g⁻¹, Subtype.ext ?_⟩
    show (h * g⁻¹) • x.1 = y.1
    rw [← hg, smul_smul, inv_mul_cancel_right, hh]⟩
  have : LocallyCompactSpace S := hLTcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (HA (Fv F v) σ J) :=
    PI.VolStabW.TopoAF.secondCountable_HA_of (Fv F v) σ J
  have : SigmaCompactSpace (HA (Fv F v) σ J) := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hop := isOpenMap_smul_of_sigmaCompact (G := HA (Fv F v) σ J) (X := S) ⟨Yv, hYLT⟩
  obtain ⟨hKc, hKo⟩ := kv_compact_open σ J L hL v
  obtain ⟨O, hOo, hOeq⟩ := isOpen_induced_iff.1 (hop _ hKo)
  have hKYO : KY ⊆ O := by
    rintro _ ⟨k, hk, rfl⟩
    have : (⟨k • Yv, hsmulLT k Yv hYLT⟩ : S) ∈ Subtype.val ⁻¹' O := by
      rw [hOeq]; exact ⟨k, hk, rfl⟩
    exact this
  have hOLT : O ∩ LT ⊆ KY := by
    rintro X ⟨hXO, hXT⟩
    have : (⟨X, hXT⟩ : S) ∈ Subtype.val ⁻¹' O := hXO
    rw [hOeq] at this
    obtain ⟨k, hk, hkX⟩ := this
    exact ⟨k, hk, (congrArg Subtype.val hkX).symm⟩
  have hKYLT : KY ⊆ LT := by
    rintro _ ⟨k, hk, rfl⟩
    exact hsmulLT k Yv hYLT
  have hKYc : IsCompact KY := by
    have e : KY = (fun k : HA (Fv F v) σ J => k • Yv) ''
        (Formalism.L2.SG.TypedSets.Kv σ J (L : Set (Fin n → E)) v) := by
      ext X
      constructor
      · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
      · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
    rw [e]
    exact hKc.image ((continuous_act σ J (Fv F v)).comp (continuous_id.prodMk continuous_const))
  choose W hWo hWc hyW hWO using fun y : KY => exists_cc_tup v hOo (hKYO y.2)
  obtain ⟨t, ht⟩ := hKYc.elim_finite_subcover (fun y : KY => W y) (fun y => (hWo y).isOpen)
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyW _⟩)
  refine ⟨⋃ y ∈ t, W y, isClopen_biUnion_finset fun y _ => hWo y, t.isCompact_biUnion fun y _ => hWc y, ?_⟩
  ext X
  constructor
  · rintro ⟨hXC, hXT⟩
    obtain ⟨y, -, hy⟩ := Set.mem_iUnion₂.1 hXC
    exact hOLT ⟨hWO y hy, hXT⟩
  · intro hX
    exact ⟨ht hX, hKYLT hX⟩

end Place

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J a X0 Λ hCM hJ hdet hLat`. Establish `: FiniteDimensional F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `hI'` using `hI F E σ n J a X0 Λ hCM hJ hdet hLat`. Take `⟨L, hL, rfl⟩` from `hLat`. Set `b` to `Module.finBasis F E`.

Use `choose C' hC'o hC'c hC'eq using fun v => exists_C σ J X0 v L hL (hW F E σ n J a X0 hCM hJ hdet v)`. Set `KY : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin n → Fv F v ⊗[F] E)` to `fun v => {X | ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J (L : Set (Fin n → E)) v, X = k • ratTup (F := F) (Fv F v) X0}`. Set `LT : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin n → Fv F v ⊗[F] E)` to `fun v => {X | gramR (Fv F v) σ J X = (gramE σ J X0).map (inclR (Fv F v))}`. Establish `hsub : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, KY v ⊆ latV b v`. Take `⟨N, hN0, hN⟩` from `MassDataLevelSSteps.LatTop.exists_common_mult (MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) MassDataMassesW.KCptW.span_std X0`.

Use `filter_upwards [ev_latLoc_std L hL, ev_int ((N : F)⁻¹), ev_crd_oev b] with v hv hNv hc`. Introduce and unpack `_ ⟨k, hk, rfl⟩`. Introduce `c i l`. Establish `hk' : HA.mat (Fv F v) σ J k ∈ Kloc (E` using `E) v ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by`. Introduce `y`.

Rewrite using `[← hv]`. Conclude with `hk y`. Establish `hYc : ratTup (F` using `F) (Fv F v) X0 c ∈ latLoc (E := E) v ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by`. Apply `int_smul_mem v N hN0 hNv` to reduce the goal to its premises. Rewrite using `[show N • ratTup (F := F) (Fv F v) X0 c = ratV (F := F) (Fv F v) (N • X0 c) from (MassDataMassesW.KCptW.ratV_zsmul v N (X0 c)).symm]`.

Conclude with `Submodule.subset_span ⟨_, hN c, rfl⟩`. Establish `h2` using `(hk' _).1 hYc`. Conclude with `hc _ (mem_oev_of_std v _ h2 i) l`. Establish `hgood : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, latV b v ∩ LT v = KY v` using `by filter_upwards [hI' _ b, hsub] with v h1 h2`. Use extensionality with `X`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hX, hXT⟩`. Take `⟨k, hk, hkX⟩` from `h1 X hX hXT`. Conclude with `⟨k, hk, hkX.symm⟩`. Introduce `hX`.

Use `⟨h2 hX, ?_⟩` and prove the remaining obligations. Take `⟨k, hk, rfl⟩` from `hX`. Use `show gramR (Fv F v) σ J (k • ratTup (F := F) (Fv F v) X0) = _`. Rewrite using `[gram_smul]`. Conclude with `PI.VolStabW.LocPosW.gramR_ratTup (Fv F v) σ J X0`.

Set `C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin n → Fv F v ⊗[F] E)` to `fun v => if latV b v ∩ LT v = KY v then latV b v else C' v`. Establish `hCo : ∀ v, IsClopen (C v) ∧ IsCompact (C v)`. Introduce `v`. Distinguish the cases in `h : latV b v ∩ LT v = KY v`. Simplify using `only [C, if_pos h]`.

Conclude with `⟨PI.VolStabW.PositiveNearLattice.isClopen_latV b v a n, PI.VolStabW.PositiveNearLattice.isCompact_latV b v a n⟩`. Simplify using `only [C, if_neg h]`. Conclude with `⟨hC'o v, hC'c v⟩`. Use `⟨_, b, C, fun v => ?_, fun v => (hCo v).1.isOpen.measurableSet, fun v => ?_, ?_⟩` and prove the remaining obligations. Conclude with `⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) (hCo v).1).isLocallyConstant, HasCompactSupport.intro' (hCo v).2 (hCo v).1.isClosed fun Y hY => Set.indicator_of_notMem hY _⟩`.

Distinguish the cases in `h : latV b v ∩ LT v = KY v`. Simplify using `only [C, if_pos h]`. Conclude with `h`. Simplify using `only [C, if_neg h]`. Conclude with `hC'eq v`.

Use `filter_upwards [hgood] with v hv`. Simplify using `only [C, if_pos hv]`.
-/
theorem locSB_of (hW : WittLocT) (hI : IntWittAE) : LocSB := by
  intro F E _ _ _ _ _ σ n J a X0 Λ hCM hJ hdet hLat
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hI' := hI F E σ n J a X0 Λ hCM hJ hdet hLat
  obtain ⟨L, hL, rfl⟩ := hLat
  let b := Module.finBasis F E
  choose C' hC'o hC'c hC'eq using fun v => exists_C σ J X0 v L hL (hW F E σ n J a X0 hCM hJ hdet v)
  let KY : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin n → Fv F v ⊗[F] E) := fun v =>
    {X | ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J (L : Set (Fin n → E)) v, X = k • ratTup (F := F) (Fv F v) X0}
  let LT : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin n → Fv F v ⊗[F] E) := fun v =>
    {X | gramR (Fv F v) σ J X = (gramE σ J X0).map (inclR (Fv F v))}
  have hsub : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, KY v ⊆ latV b v := by
    obtain ⟨N, hN0, hN⟩ := MassDataLevelSSteps.LatTop.exists_common_mult
      (MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) MassDataMassesW.KCptW.span_std X0
    filter_upwards [ev_latLoc_std L hL, ev_int ((N : F)⁻¹), ev_crd_oev b] with v hv hNv hc
    rintro _ ⟨k, hk, rfl⟩
    intro c i l
    have hk' : HA.mat (Fv F v) σ J k ∈ Kloc (E := E) v
        ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
      intro y; rw [← hv]; exact hk y
    have hYc : ratTup (F := F) (Fv F v) X0 c ∈ latLoc (E := E) v
        ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
      apply int_smul_mem v N hN0 hNv
      rw [show N • ratTup (F := F) (Fv F v) X0 c = ratV (F := F) (Fv F v) (N • X0 c) from
        (MassDataMassesW.KCptW.ratV_zsmul v N (X0 c)).symm]
      exact Submodule.subset_span ⟨_, hN c, rfl⟩
    have h2 := (hk' _).1 hYc
    exact hc _ (mem_oev_of_std v _ h2 i) l
  have hgood : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, latV b v ∩ LT v = KY v := by
    filter_upwards [hI' _ b, hsub] with v h1 h2
    ext X
    constructor
    · rintro ⟨hX, hXT⟩
      obtain ⟨k, hk, hkX⟩ := h1 X hX hXT
      exact ⟨k, hk, hkX.symm⟩
    · intro hX
      refine ⟨h2 hX, ?_⟩
      obtain ⟨k, hk, rfl⟩ := hX
      show gramR (Fv F v) σ J (k • ratTup (F := F) (Fv F v) X0) = _
      rw [gram_smul]
      exact PI.VolStabW.LocPosW.gramR_ratTup (Fv F v) σ J X0
  let C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin n → Fv F v ⊗[F] E) := fun v =>
    if latV b v ∩ LT v = KY v then latV b v else C' v
  have hCo : ∀ v, IsClopen (C v) ∧ IsCompact (C v) := by
    intro v
    by_cases h : latV b v ∩ LT v = KY v
    · simp only [C, if_pos h]
      exact ⟨PI.VolStabW.PositiveNearLattice.isClopen_latV b v a n, PI.VolStabW.PositiveNearLattice.isCompact_latV b v a n⟩
    · simp only [C, if_neg h]
      exact ⟨hC'o v, hC'c v⟩
  refine ⟨_, b, C, fun v => ?_, fun v => (hCo v).1.isOpen.measurableSet, fun v => ?_, ?_⟩
  · exact ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) (hCo v).1).isLocallyConstant,
      HasCompactSupport.intro' (hCo v).2 (hCo v).1.isClosed fun Y hY => Set.indicator_of_notMem hY _⟩
  · by_cases h : latV b v ∩ LT v = KY v
    · simp only [C, if_pos h]
      exact h
    · simp only [C, if_neg h]
      exact hC'eq v
  · filter_upwards [hgood] with v hv
    simp only [C, if_pos hv]

end Formalism.L2.SG.Pf.NcX.LocSBPf
