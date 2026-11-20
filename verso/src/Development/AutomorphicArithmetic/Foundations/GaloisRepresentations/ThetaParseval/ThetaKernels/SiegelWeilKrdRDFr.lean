import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.FrameOfSig
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRDSt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Krd
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d`. Take `⟨ε, hε⟩` from `d.ok.frame.1`. Use `⟨ε, hε, ?_⟩` and prove the remaining obligations. Establish `hss : ∀ x, σ (σ x) = x` using `PositivityTheory.ThKG.Tow.Levi.sig_sig d.cm`. Establish `i : Fin d.n` using `⟨0, d.ok.hn⟩`.

Establish `key : ∀ c : E, (∀ i j, σ (d.Y.J j i) = c * d.Y.J i j) → ((ε : ℤ) : E) = c` using `fun c hc => by`. Establish `e` using `congrFun (congrFun (conjT_frame c d.Y.J hc hss d.b.1) (Sum.inl i)) (Sum.inr i)`. Rewrite `e` using `[hε]`. Simplify `e` using `[Matrix.fromBlocks]`. Break down `d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩` into its components or cases.

Use `Or.inl ⟨hA, ?_⟩` and prove the remaining obligations. Establish `e` using `key (-1) fun i j => by rw [hY, neg_one_mul]`. Establish `e' : ((ε : ℤ) : E) = ((-1 : ℤ) : E)` using `by rw [e]; push_cast; rfl`. Conclude with `Units.ext (by simpa using Int.cast_injective (α := E) e')`. Use `Or.inr ⟨hA, ?_⟩` and prove the remaining obligations.

Establish `e` using `key 1 fun i j => by rw [hY, one_mul]`. Establish `e' : ((ε : ℤ) : E) = ((1 : ℤ) : E)` using `by rw [e]; push_cast; rfl`. Conclude with `Units.ext (by simpa using Int.cast_injective (α := E) e')`.
-/
theorem epsEx_k : _root_.PositivityTheory.SiegelWeilFormula.Krd.EpsEx_k := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  refine ⟨ε, hε, ?_⟩
  have hss : ∀ x, σ (σ x) = x := PositivityTheory.ThKG.Tow.Levi.sig_sig d.cm
  have i : Fin d.n := ⟨0, d.ok.hn⟩
  have key : ∀ c : E, (∀ i j, σ (d.Y.J j i) = c * d.Y.J i j) → ((ε : ℤ) : E) = c := fun c hc => by
    have e := congrFun (congrFun (conjT_frame c d.Y.J hc hss d.b.1) (Sum.inl i)) (Sum.inr i)
    rw [hε] at e
    simpa [Matrix.fromBlocks] using e
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · refine Or.inl ⟨hA, ?_⟩
    have e := key (-1) fun i j => by rw [hY, neg_one_mul]
    have e' : ((ε : ℤ) : E) = ((-1 : ℤ) : E) := by rw [e]; push_cast; rfl
    exact Units.ext (by simpa using Int.cast_injective (α := E) e')
  · refine Or.inr ⟨hA, ?_⟩
    have e := key 1 fun i j => by rw [hY, one_mul]
    have e' : ((ε : ℤ) : E) = ((1 : ℤ) : E) := by rw [e]; push_cast; rfl
    exact Units.ext (by simpa using Int.cast_injective (α := E) e')
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d`. Use `⟨fun hA => ?_, fun hA => ?_⟩` and prove the remaining obligations. Use `choose fr sg hfr using fun w => frame_of_sig (hA.sig w) d.ok.aniso`. Conclude with `⟨fr, sg, fun w => by rw [one_smul, hfr w]⟩`. Use `choose fr sg hfr using fun w => frame_of_sig (hA.sig w) d.ok.aniso`.

Use `⟨fr, sg, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[← hfr w, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem frEx_k : _root_.PositivityTheory.SiegelWeilFormula.Krd.FrEx_k := by
  intro F E _ _ _ _ _ σ d
  refine ⟨fun hA => ?_, fun hA => ?_⟩
  · choose fr sg hfr using fun w => frame_of_sig (hA.sig w) d.ok.aniso
    exact ⟨fr, sg, fun w => by rw [one_smul, hfr w]⟩
  · choose fr sg hfr using fun w => frame_of_sig (hA.sig w) d.ok.aniso
    refine ⟨fr, sg, fun w => ?_⟩
    rw [← hfr w, Matrix.mul_smul, Matrix.smul_mul]
end PositivityTheory.SiegelWeilFormula.Krd
end
end
