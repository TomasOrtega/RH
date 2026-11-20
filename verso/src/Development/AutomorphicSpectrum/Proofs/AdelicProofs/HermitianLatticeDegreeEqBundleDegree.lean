import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.GramMat

namespace GlobalTheory.CompanionTheory.Ar.Lines

open NumberField TensorProduct GroundTheory.Heights₂.Heights Matrix
open scoped ComplexOrder nonZeroDivisors

noncomputable section

/- English proof (translation)
Establish `he : ∀ j : Fin i, embVec σ (Pi.single j 1 : Fin i → L) = Pi.single j 1`. Introduce `j`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality.

Simplify using `[embVec]`. Simplify using `[embVec, Pi.single_eq_of_ne hk]`. Use extensionality with `a b`. Simplify using `[gramAt, he, Matrix.mulVec_single_one, Matrix.col_apply]`.
-/
theorem gramAt_standard {L : Type} [Field L] {i : ℕ} (h : Matrix (Fin i) (Fin i) ℂ) (σ : L →+* ℂ) :
    gramAt h σ (fun j : Fin i => (Pi.single j 1 : Fin i → L)) = h := by
  have he : ∀ j : Fin i, embVec σ (Pi.single j 1 : Fin i → L) = Pi.single j 1 := by
    intro j
    funext k
    by_cases hk : k = j
    · subst hk; simp [embVec]
    · simp [embVec, Pi.single_eq_of_ne hk]
  ext a b
  simp [gramAt, he, Matrix.mulVec_single_one, Matrix.col_apply]

/- English proof (translation)
Establish `hspanK : Submodule.span L (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → L)) = ⊤`. Establish `h : (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → L)) = Set.range (Pi.basisFun L (Fin i))`. Use `congr 1`. Use function extensionality and compare the values at `j`. Conclude with `(Pi.basisFun_apply _ _ _).symm`.

Rewrite using `[h]`. Conclude with `(Pi.basisFun L (Fin i)).span_eq`. Establish `hS : (Submodule.span (𝓞 L) (Set.range f)).map c = Submodule.span (𝓞 L) (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → L))`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Conclude with `congrArg _ (congrArg Set.range (funext hcf))`.

Establish `hA : (Fl.lattice ⊓ (Submodule.span L (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → L))).restrictScalars (𝓞 L)) = LinearMap.range c`. Rewrite using `[hspanK, hlat, Submodule.restrictScalars_top, inf_top_eq]`. Establish `hidx : genIndex (Fl.lattice ⊓ (Submodule.span L (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → L))).restrictScalars (𝓞 L)).toAddSubgroup (Submodule.span (𝓞 L) (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → L))).toAddSubgroup = (Nat.card (F ⧸ Submodule.span (𝓞 L) (Set. …`. Rewrite using `[hA, ← hS, genIndex]`. Establish `hle : ((Submodule.span (𝓞 L) (Set.range f)).map c).toAddSubgroup ≤ (LinearMap.range c).toAddSubgroup`.

Introduce and unpack `_ ⟨x, -, rfl⟩`. Conclude with `⟨x, rfl⟩`. Rewrite using `[AddSubgroup.relIndex_eq_one.mpr hle, LinearMap.range_eq_map, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup, AddSubgroup.relIndex_map_map_of_injective _ _ hc, Submodule.top_toAddSubgroup, AddSubgroup.relIndex_top_right]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Establish `hgram : ∀ σ : L →+* ℂ, (gramAt (Fl.metric σ) σ fun j : Fin i => (Pi.single j 1 : Fin i → L)).det.re = ‖HermitianBundle.gramDet B σ (fun j => (f j : B.carrier))‖`. Introduce `σ`. Establish `hd : HermitianBundle.gramDet B σ (fun j => (f j : B.carrier)) = (Fl.metric σ).det`. Rewrite using `[hmet σ]`. Both sides reduce to the same expression.

Rewrite using `[gramAt_standard, hd]`. Establish `hp : 0 < (Fl.metric σ).det` using `(Fl.posDef σ).det_pos`. Establish `hre : ((Fl.metric σ).det.re : ℂ) = (Fl.metric σ).det`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules.

Simplify using `using (Complex.lt_def.mp hp).2.symm ▸ rfl`. Rewrite using `[← hre, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]`. Conclude with `(Complex.lt_def.mp hp).1`. Simplify using `only [HermLattice.degree, subDegree, HermitianBundle.degreeWith, hidx, hgram]`.
-/
theorem degree_eq_degreeWith (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (F : Submodule (𝓞 L) B.carrier) (i : ℕ) (f : Fin i → F) (c : F →ₗ[𝓞 L] (Fin i → L))
    (Fl : HermLattice L i) (hf : LinearIndependent (𝓞 L) f) (hi : i = B.rank F)
    (hc : Function.Injective c) (hcf : ∀ j, c (f j) = Pi.single j 1)
    (hlat : Fl.lattice = LinearMap.range c)
    (hmet : ∀ σ, Fl.metric σ = gramMat B σ (fun j => (f j : B.carrier))) :
    Fl.degree = B.degreeWith F f := by
  have hspanK : Submodule.span L (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → L)) = ⊤ := by
    have h : (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → L)) =
        Set.range (Pi.basisFun L (Fin i)) := by
      congr 1; funext j; exact (Pi.basisFun_apply _ _ _).symm
    rw [h]
    exact (Pi.basisFun L (Fin i)).span_eq
  have hS : (Submodule.span (𝓞 L) (Set.range f)).map c =
      Submodule.span (𝓞 L) (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → L)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact congrArg _ (congrArg Set.range (funext hcf))
  have hA : (Fl.lattice ⊓ (Submodule.span L (Set.range fun j : Fin i =>
      (Pi.single j 1 : Fin i → L))).restrictScalars (𝓞 L)) = LinearMap.range c := by
    rw [hspanK, hlat, Submodule.restrictScalars_top, inf_top_eq]
  have hidx : genIndex
      (Fl.lattice ⊓ (Submodule.span L (Set.range fun j : Fin i =>
        (Pi.single j 1 : Fin i → L))).restrictScalars (𝓞 L)).toAddSubgroup
      (Submodule.span (𝓞 L) (Set.range fun j : Fin i =>
        (Pi.single j 1 : Fin i → L))).toAddSubgroup =
      (Nat.card (F ⧸ Submodule.span (𝓞 L) (Set.range f)) : ℝ) := by
    rw [hA, ← hS, genIndex]
    have hle : ((Submodule.span (𝓞 L) (Set.range f)).map c).toAddSubgroup ≤
        (LinearMap.range c).toAddSubgroup := by
      rintro _ ⟨x, -, rfl⟩
      exact ⟨x, rfl⟩
    rw [AddSubgroup.relIndex_eq_one.mpr hle, LinearMap.range_eq_map, Submodule.map_toAddSubgroup,
      Submodule.map_toAddSubgroup, AddSubgroup.relIndex_map_map_of_injective _ _ hc,
      Submodule.top_toAddSubgroup, AddSubgroup.relIndex_top_right]
    simp
    rfl
  have hgram : ∀ σ : L →+* ℂ,
      (gramAt (Fl.metric σ) σ fun j : Fin i => (Pi.single j 1 : Fin i → L)).det.re =
        ‖HermitianBundle.gramDet B σ (fun j => (f j : B.carrier))‖ := by
    intro σ
    have hd : HermitianBundle.gramDet B σ (fun j => (f j : B.carrier)) = (Fl.metric σ).det := by
      rw [hmet σ]
      rfl
    rw [gramAt_standard, hd]
    have hp : 0 < (Fl.metric σ).det := (Fl.posDef σ).det_pos
    have hre : ((Fl.metric σ).det.re : ℂ) = (Fl.metric σ).det := by
      apply Complex.ext
      · simp
      · simpa using (Complex.lt_def.mp hp).2.symm ▸ rfl
    rw [← hre, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    exact (Complex.lt_def.mp hp).1
  simp only [HermLattice.degree, subDegree, HermitianBundle.degreeWith, hidx, hgram]

end

end GlobalTheory.CompanionTheory.Ar.Lines
