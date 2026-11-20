import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.AdelicLatticeSwap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))

/- English proof (translation)
Introduce `v`. Conclude with `ha v`.
-/
private lemma mem_intAf_of_mem_intAd {a : Af F} (ha : a ∈ Formalism.UG.intAd F) : a ∈ Formalism.MainNotions.StandardLattice.intAf F := by
  intro v
  exact ha v

/- English proof (translation)
Introduce `v`. Conclude with `ha v`.
-/
private lemma mem_intAd_of_mem_intAf {a : Af F} (ha : a ∈ Formalism.MainNotions.StandardLattice.intAf F) : a ∈ Formalism.UG.intAd F := by
  intro v
  exact ha v

/- English proof (translation)
Introduce `v`. Rewrite using `[map_mul]`. Conclude with `mul_mem (ha v) (hb v)`.
-/
private lemma intAf_mul_mem {a b : Af F} (ha : a ∈ Formalism.MainNotions.StandardLattice.intAf F) (hb : b ∈ Formalism.MainNotions.StandardLattice.intAf F) :
    a * b ∈ Formalism.MainNotions.StandardLattice.intAf F := by
  intro v
  rw [map_mul]
  exact mul_mem (ha v) (hb v)

/- English proof (translation)
Introduce `v`. Rewrite using `[map_one]`. Conclude with `one_mem _`.
-/
private lemma one_mem_intAf_flag_measures : (1 : Af F) ∈ Formalism.MainNotions.StandardLattice.intAf F := by
  intro v
  rw [map_one]
  exact one_mem _

omit [NumberField E] in

/- English proof (translation)
Unfold `Formalism.MainNotions.StandardLattice.latHat at hy ⊢`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨b, hb, x, hx, rfl⟩` from `hw`. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises.

Use `⟨a * b, intAf_mul_mem (mem_intAf_of_mem_intAd ha) hb, c • x, L.smul_mem c hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]`. Both sides reduce to the same expression. Consider the case `zero => rw [smul_zero]`.

Conclude with `zero_mem _`. Consider the case `add u w _ _ hu hw => rw [smul_add]`. Conclude with `add_mem hu hw`. Consider the case `neg u _ hu => rw [smul_neg]`. Conclude with `neg_mem hu`.
-/
theorem gen_smul_mem (a : Af F) (ha : a ∈ Formalism.UG.intAd F) (c : 𝓞 E)
    (y : Fin n → Af F ⊗[F] E) (hy : y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))) :
    (a ⊗ₜ[F] (c : E) : Af F ⊗[F] E) • y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) := by
  unfold Formalism.MainNotions.StandardLattice.latHat at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hw
    apply AddSubgroup.subset_closure
    refine ⟨a * b, intAf_mul_mem (mem_intAf_of_mem_intAd ha) hb, c • x, L.smul_mem c hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [smul_add]; exact add_mem hu hw
  | neg u _ hu => rw [smul_neg]; exact neg_mem hu

/- English proof (translation)
Unfold `Formalism.MainNotions.S.IntAf Formalism.UG.tensInt at ht`. Proceed by induction on `ht using Subring.closure_induction with`. Consider the case `mem s hs`. Introduce `y hy`. Break down `hs with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩` into its components or cases.

Take `⟨c, rfl⟩` from `he`. Rewrite using `[Algebra.TensorProduct.comm_symm_tmul]`. Conclude with `gen_smul_mem L 1 (one_mem _) c y hy`. Rewrite using `[Algebra.TensorProduct.comm_symm_tmul]`. Simplify using `using gen_smul_mem L b hb 1 y hy`.

Consider the case `zero => intro y _`. Rewrite using `[map_zero, zero_smul]`. Conclude with `zero_mem _`. Consider the case `one => intro y hy`. Rewrite using `[map_one, one_smul]`.

Conclude with `hy`. Consider the case `add s u _ _ hs hu => intro y hy`. Rewrite using `[map_add, add_smul]`. Conclude with `add_mem (hs y hy) (hu y hy)`. Consider the case `neg s _ hs => intro y hy`.

Rewrite using `[map_neg, neg_smul]`. Conclude with `neg_mem (hs y hy)`. Consider the case `mul s u _ _ hs hu => intro y hy`. Rewrite using `[map_mul, mul_smul]`. Conclude with `hs _ (hu y hy)`.
-/
theorem int_smul_mem (t : E ⊗[F] Af F) (ht : t ∈ Formalism.MainNotions.S.IntAf F E) :
    ∀ y : Fin n → Af F ⊗[F] E, y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) →
      (Algebra.TensorProduct.comm F (Af F) E).symm t • y ∈
        Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) := by
  unfold Formalism.MainNotions.S.IntAf Formalism.UG.tensInt at ht
  induction ht using Subring.closure_induction with
  | mem s hs =>
    intro y hy
    rcases hs with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩
    · obtain ⟨c, rfl⟩ := he
      rw [Algebra.TensorProduct.comm_symm_tmul]
      exact gen_smul_mem L 1 (one_mem _) c y hy
    · rw [Algebra.TensorProduct.comm_symm_tmul]
      simpa using gen_smul_mem L b hb 1 y hy
  | zero => intro y _; rw [map_zero, zero_smul]; exact zero_mem _
  | one => intro y hy; rw [map_one, one_smul]; exact hy
  | add s u _ _ hs hu => intro y hy; rw [map_add, add_smul]; exact add_mem (hs y hy) (hu y hy)
  | neg s _ hs => intro y hy; rw [map_neg, neg_smul]; exact neg_mem (hs y hy)
  | mul s u _ _ hs hu => intro y hy; rw [map_mul, mul_smul]; exact hs _ (hu y hy)

/- English proof (translation)
Unfold `Formalism.MainNotions.S.lamAf at hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨⟨x, hx⟩, rfl⟩` from `hw`. Unfold `Formalism.MainNotions.StandardLattice.latHat`.

Apply `AddSubgroup.subset_closure` to reduce the goal to its premises. Use `⟨1, one_mem_intAf_flag_measures, x, hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `show (Algebra.TensorProduct.comm F (Af F) E).symm ((x i) ⊗ₜ[F] (1 : Af F)) = (1 : Af F) ⊗ₜ[F] x i`. Simplify using the standard rewrite rules.

Consider the case `zero`. Establish `h0 : (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm ((0 : Fin n → E ⊗[F] Af F) i)) = 0`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[h0]`.

Conclude with `zero_mem _`. Consider the case `add u w _ _ hu hw`. Establish `h1 : (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm ((u + w) i)) = (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (u i)) + fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (w i)`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Rewrite using `[h1]`. Conclude with `add_mem hu hw`. Consider the case `smul s u _ hu`. Establish `h2 : (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm ((s • u) i)) = (Algebra.TensorProduct.comm F (Af F) E).symm (s : E ⊗[F] Af F) • fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (u i)`. Use function extensionality and compare the values at `i`.

Simplify using `[Subring.smul_def]`. Rewrite using `[h2]`. Conclude with `int_smul_mem L s s.2 _ hu`.
-/
theorem symm_mem_of_mem (z : Fin n → E ⊗[F] Af F) (hz : z ∈ Formalism.MainNotions.S.lamAf (F := F) L) :
    (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (z i)) ∈
      Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) := by
  unfold Formalism.MainNotions.S.lamAf at hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨x, hx⟩, rfl⟩ := hw
    unfold Formalism.MainNotions.StandardLattice.latHat
    apply AddSubgroup.subset_closure
    refine ⟨1, one_mem_intAf_flag_measures, x, hx, ?_⟩
    funext i
    show (Algebra.TensorProduct.comm F (Af F) E).symm ((x i) ⊗ₜ[F] (1 : Af F)) = (1 : Af F) ⊗ₜ[F] x i
    simp
  | zero =>
    have h0 : (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm ((0 : Fin n → E ⊗[F] Af F) i)) = 0 := by
      funext i
      simp
    rw [h0]
    exact zero_mem _
  | add u w _ _ hu hw =>
    have h1 : (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm ((u + w) i)) =
        (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (u i)) +
          fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (w i) := by
      funext i
      simp
    rw [h1]
    exact add_mem hu hw
  | smul s u _ hu =>
    have h2 : (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm ((s • u) i)) =
        (Algebra.TensorProduct.comm F (Af F) E).symm (s : E ⊗[F] Af F) •
          fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (u i) := by
      funext i
      simp [Subring.smul_def]
    rw [h2]
    exact int_smul_mem L s s.2 _ hu

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy`. Unfold `Formalism.MainNotions.StandardLattice.latHat at hy`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem w hw`.

Take `⟨a, ha, x, hx, rfl⟩` from `hw`. Establish `hg : (fun i => Formalism.UG.inclE (F` using `F) (Af F) (x i)) ∈ Formalism.MainNotions.S.lamAf (F := F) L := Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩`. Establish `hs : ((1 : E) ⊗ₜ[F] a : E ⊗[F] Af F) ∈ Formalism.MainNotions.S.IntAf F E` using `Subring.subset_closure (Or.inr ⟨⟨a, mem_intAd_of_mem_intAf ha⟩, rfl⟩)`. Use `Submodule.smul_mem _ (⟨_, hs⟩ : Formalism.MainNotions.S.IntAf F E) hg using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`.

Simplify using `[Subring.smul_def, Formalism.UG.inclE, Algebra.TensorProduct.tmul_mul_tmul]`. Consider the case `zero`. Use `zero_mem (Formalism.MainNotions.S.lamAf (F := F) L) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Consider the case `add u w _ _ hu hw`. Use `add_mem hu hw using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Consider the case `neg u _ hu`.

Use `neg_mem hu using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Introduce `hz`. Simplify using `using symm_mem_of_mem L _ hz`.
-/
theorem mem_latHat_iff_comm_mem_lamAf (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E))
    (y : Fin n → Af F ⊗[F] E) :
    y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔
      (fun i => Algebra.TensorProduct.comm F (Af F) E (y i)) ∈ Formalism.MainNotions.S.lamAf (F := F) L := by
  constructor
  · intro hy
    unfold Formalism.MainNotions.StandardLattice.latHat at hy
    induction hy using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hw
      have hg : (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) ∈ Formalism.MainNotions.S.lamAf (F := F) L :=
        Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
      have hs : ((1 : E) ⊗ₜ[F] a : E ⊗[F] Af F) ∈ Formalism.MainNotions.S.IntAf F E :=
        Subring.subset_closure (Or.inr ⟨⟨a, mem_intAd_of_mem_intAf ha⟩, rfl⟩)
      convert Submodule.smul_mem _ (⟨_, hs⟩ : Formalism.MainNotions.S.IntAf F E) hg using 1
      funext i
      simp [Subring.smul_def, Formalism.UG.inclE, Algebra.TensorProduct.tmul_mul_tmul]
    | zero =>
      convert zero_mem (Formalism.MainNotions.S.lamAf (F := F) L) using 1
      funext i
      simp
    | add u w _ _ hu hw =>
      convert add_mem hu hw using 1
      funext i
      simp
    | neg u _ hu =>
      convert neg_mem hu using 1
      funext i
      simp
  · intro hz
    simpa using symm_mem_of_mem L _ hz

end GlobalTheory.AdelicLatticeSwap
