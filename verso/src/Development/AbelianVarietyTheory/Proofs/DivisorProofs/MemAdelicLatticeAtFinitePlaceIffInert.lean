import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InLat2
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertSphLat

open GlobalTheory.InertLocField InertChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Rewrite using `[show inclR (F := F) (AF F) e = (1 : AF F) ⊗ₜ[F] e from rfl, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.
-/
theorem smul_inclR (a : AF F) (e : E) : a • inclR (F := F) (AF F) e = a ⊗ₜ[F] e := by
  rw [show inclR (F := F) (AF F) e = (1 : AF F) ⊗ₜ[F] e from rfl, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/- English proof (translation)
Use `show liftT E v ((complEquiv hw (under_eq_of_isInertAt hw)).symm (complEquiv hw (under_eq_of_isInertAt hw) y)) = liftT E v y`. Rewrite using `[RingEquiv.symm_apply_apply]`.
-/
theorem iotaW_toCompl {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (y : Fv F v ⊗[F] E) :
    GlobalTheory.InertBigCell.iotaW hw (toCompl (under_eq_of_isInertAt hw) y) = liftT E v y := by
  show liftT E v ((complEquiv hw (under_eq_of_isInertAt hw)).symm
    (complEquiv hw (under_eq_of_isInertAt hw) y)) = liftT E v y
  rw [RingEquiv.symm_apply_apply]

/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v t, GlobalTheory.LatVac.at_liftV v t, by rw [GlobalTheory.LatVac.evFin_liftV]; exact ht, y, hy, by funext i; rw [Pi.smul_apply, smul_inclR]⟩`.
-/
theorem gen_mem {v : Pl F} {d : ℕ} (W : Spc F E d) {t : Fv F v} (ht : t ∈ v.adicCompletionIntegers F)
    {y : Fin d → E} (hy : y ∈ W.L) :
    (fun i => GlobalTheory.LatVac.liftV v t ⊗ₜ[F] y i) ∈ GlobalTheory.InertSph.latAt W v :=
  AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v t, GlobalTheory.LatVac.at_liftV v t,
    by rw [GlobalTheory.LatVac.evFin_liftV]; exact ht, y, hy, by funext i; rw [Pi.smul_apply, smul_inclR]⟩

/- English proof (translation)
Establish `h` using `under_eq_of_isInertAt hw`. Set `f : (Fin d → w.adicCompletion E) →+ (Fin d → AE F E)` to `AddMonoidHom.compLeft (GlobalTheory.InertBigCell.iotaW hw) (Fin d)`. Establish `hf : ∀ u, f u = fun i => GlobalTheory.InertBigCell.iotaW hw (u i)` using `fun _ => rfl`. Prove the components needed by the constructor for the conclusion. Introduce `hz`.

Establish `hle : GlobalTheory.InertSph.latAt W v ≤ (GlobalTheory.LFun.latAt w W.L).toAddSubgroup.map f`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, haO, y, hy, rfl⟩`. Use `⟨fun i => complMap h (evFin F v a) * algebraMap E _ (y i), ?_, ?_⟩` and prove the remaining obligations. Establish `e1 : (fun i => complMap h (evFin F v a) * algebraMap E (w.adicCompletion E) (y i)) = (⟨complMap h (evFin F v a), complMap_mem h haO⟩ : Formalism.UG.Ov E w) • (fun i => algebraMap E (w.adicCompletion E) (y i))` using `rfl`.

Rewrite using `[Submodule.coe_toAddSubgroup, SetLike.mem_coe, e1]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hy, rfl⟩)`. Use function extensionality and compare the values at `i`. Rewrite using `[hf]`. Simplify using `only`.

Rewrite using `[← toCompl_tmul, iotaW_toCompl, liftT_tmul, ← eq_liftV_of_at v ha, Pi.smul_apply, smul_inclR]`. Take `⟨u, hu, e⟩` from `AddSubgroup.mem_map.1 (hle hz)`. Conclude with `⟨u, hu, e.symm⟩`. Introduce and unpack `⟨u, hu, rfl⟩`. Establish `key : ∀ u ∈ GlobalTheory.LFun.latAt w W.L, ∀ o : Formalism.UG.Ov E w, f (o • u) ∈ GlobalTheory.InertSph.latAt W v`.

Introduce `u hu`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, hy, rfl⟩` from `hx`. Introduce `o`.

Take `⟨t, ht⟩` from `toCompl_surjective h (o : w.adicCompletion E)`. Establish `htI : t ∈ intLoc F E v` using `(mem_intLoc_iff hw h t).2 (ht ▸ o.2)`. Establish `e1 : f (o • fun i => algebraMap E (w.adicCompletion E) (y i)) = fun i => liftT E v (t * ((1 : Fv F v) ⊗ₜ[F] y i))`. Use function extensionality and compare the values at `i`. Rewrite using `[hf]`.

Simplify using `only`. Rewrite using `[Pi.smul_apply, Subring.smul_def, smul_eq_mul, ← ht, show algebraMap E (w.adicCompletion E) (y i) = toCompl h ((1 : Fv F v) ⊗ₜ[F] y i) by`. Rewrite using `[toCompl_tmul, map_one, one_mul], ← map_mul, iotaW_toCompl]`. Rewrite using `[e1]`. Use `intLoc_induction (p := fun t => (fun i => liftT E v (t * ((1 : Fv F v) ⊗ₜ[F] y i))) ∈ GlobalTheory.InertSph.latAt W v) (fun a ha x => ?_) ?_ (fun p q hp hq => ?_) (fun p hp => ?_) htI` and prove the remaining obligations.

Use `gen_mem W ha (W.L.smul_mem x hy) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, liftT_tmul, Pi.smul_apply, Algebra.smul_def]`. Use `(zero_mem (GlobalTheory.InertSph.latAt W v)) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Use `add_mem hp hq using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[add_mul, map_add]`. Use `neg_mem hp using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i`. Simplify using `[neg_mul, map_neg]`. Consider the case `zero => intro o`. Rewrite using `[smul_zero, map_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy => intro o`. Rewrite using `[smul_add, map_add]`. Conclude with `add_mem (hx o) (hy o)`. Consider the case `smul a x _ hx => intro o`. Rewrite using `[smul_smul]`.

Conclude with `hx (o * a)`. Use `key u hu 1` as an intermediate fact. Rewrite `this` using `[one_smul]`. Conclude with `this`.
-/
theorem mem_latAt_iff {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) {d : ℕ}
    (W : Spc F E d) (z : Fin d → AE F E) :
    z ∈ GlobalTheory.InertSph.latAt W v ↔ ∃ u ∈ GlobalTheory.LFun.latAt w W.L, z = fun i => GlobalTheory.InertBigCell.iotaW hw (u i) := by
  have h := under_eq_of_isInertAt hw
  let f : (Fin d → w.adicCompletion E) →+ (Fin d → AE F E) :=
    AddMonoidHom.compLeft (GlobalTheory.InertBigCell.iotaW hw) (Fin d)
  have hf : ∀ u, f u = fun i => GlobalTheory.InertBigCell.iotaW hw (u i) := fun _ => rfl
  constructor
  · intro hz
    have hle : GlobalTheory.InertSph.latAt W v ≤ (GlobalTheory.LFun.latAt w W.L).toAddSubgroup.map f := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨a, ha, haO, y, hy, rfl⟩
      refine ⟨fun i => complMap h (evFin F v a) * algebraMap E _ (y i), ?_, ?_⟩
      · have e1 : (fun i => complMap h (evFin F v a) * algebraMap E (w.adicCompletion E) (y i)) =
            (⟨complMap h (evFin F v a), complMap_mem h haO⟩ : Formalism.UG.Ov E w) •
              (fun i => algebraMap E (w.adicCompletion E) (y i)) := rfl
        rw [Submodule.coe_toAddSubgroup, SetLike.mem_coe, e1]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hy, rfl⟩)
      · funext i
        rw [hf]
        dsimp only
        rw [← toCompl_tmul, iotaW_toCompl, liftT_tmul, ← eq_liftV_of_at v ha, Pi.smul_apply, smul_inclR]
    obtain ⟨u, hu, e⟩ := AddSubgroup.mem_map.1 (hle hz)
    exact ⟨u, hu, e.symm⟩
  · rintro ⟨u, hu, rfl⟩
    have key : ∀ u ∈ GlobalTheory.LFun.latAt w W.L, ∀ o : Formalism.UG.Ov E w, f (o • u) ∈ GlobalTheory.InertSph.latAt W v := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        intro o
        obtain ⟨t, ht⟩ := toCompl_surjective h (o : w.adicCompletion E)
        have htI : t ∈ intLoc F E v := (mem_intLoc_iff hw h t).2 (ht ▸ o.2)
        have e1 : f (o • fun i => algebraMap E (w.adicCompletion E) (y i)) =
            fun i => liftT E v (t * ((1 : Fv F v) ⊗ₜ[F] y i)) := by
          funext i
          rw [hf]
          dsimp only
          rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, ← ht,
            show algebraMap E (w.adicCompletion E) (y i) = toCompl h ((1 : Fv F v) ⊗ₜ[F] y i) by
              rw [toCompl_tmul, map_one, one_mul], ← map_mul, iotaW_toCompl]
        rw [e1]
        refine intLoc_induction (p := fun t => (fun i => liftT E v (t * ((1 : Fv F v) ⊗ₜ[F] y i))) ∈
          GlobalTheory.InertSph.latAt W v) (fun a ha x => ?_) ?_ (fun p q hp hq => ?_) (fun p hp => ?_) htI
        · convert gen_mem W ha (W.L.smul_mem x hy) using 1
          funext i
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, liftT_tmul, Pi.smul_apply, Algebra.smul_def]
        · convert (zero_mem (GlobalTheory.InertSph.latAt W v)) using 1
          funext i
          simp
        · convert add_mem hp hq using 1
          funext i
          simp [add_mul, map_add]
        · convert neg_mem hp using 1
          funext i
          simp [neg_mul, map_neg]
      | zero => intro o; rw [smul_zero, map_zero]; exact zero_mem _
      | add x y _ _ hx hy => intro o; rw [smul_add, map_add]; exact add_mem (hx o) (hy o)
      | smul a x _ hx => intro o; rw [smul_smul]; exact hx (o * a)
    have := key u hu 1
    rw [one_smul] at this
    exact this

end GlobalTheory.InertSphLat
