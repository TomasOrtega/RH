import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CentComm

/- English proof (translation)
Use `set f := Matrix.toLin' A`. Establish `hc : f.charpoly = A.charpoly` using `Matrix.charpoly_toLin' A`. Establish `hfg : Commute f (Matrix.toLin' g)` using `hg.map Matrix.toLinAlgEquiv'`. Establish `hfh : Commute f (Matrix.toLin' h)` using `hh.map Matrix.toLinAlgEquiv'`. Establish `key : ∀ μ, Module.End.maxGenEigenspace f μ ≤ LinearMap.ker (Matrix.toLin' g * Matrix.toLin' h - Matrix.toLin' h * Matrix.toLin' g)` using `fun μ v hv => by`.

Establish `h1 : Module.finrank L (Module.End.maxGenEigenspace f μ) ≤ 1`. Rewrite using `[LinearMap.finrank_maxGenEigenspace_eq, hc]`. Conclude with `Polynomial.rootMultiplicity_le_one_of_separable hA μ`. Distinguish the cases in `h0 : v = 0`. Simplify using `[h0]`.

Establish `hs : ∀ w ∈ Module.End.maxGenEigenspace f μ, ∃ c : L, c • v = w` using `fun w hw => by`. Establish `h2 : Module.finrank L (Module.End.maxGenEigenspace f μ) = 1` using `le_antisymm h1 (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun h => h0 (congrArg Subtype.val h)⟩)`. Take `⟨c, hc⟩` from `(finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : Module.End.maxGenEigenspace f μ) fun h => h0 (congrArg Subtype.val h)).1 h2 ⟨w, hw⟩`. Conclude with `⟨c, congrArg Subtype.val hc⟩`. Take `⟨c, hc⟩` from `hs _ (Module.End.mapsTo_maxGenEigenspace_of_comm hfg μ hv)`.

Take `⟨d, hd⟩` from `hs _ (Module.End.mapsTo_maxGenEigenspace_of_comm hfh μ hv)`. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, ← hc, ← hd, map_smul, map_smul, ← hc, ← hd, smul_comm, sub_self]`. Establish `h3` using `iSup_le key`. Rewrite `h3` using `[Module.End.iSup_maxGenEigenspace_eq_top, top_le_iff, LinearMap.ker_eq_top, sub_eq_zero]`. Conclude with `Matrix.toLinAlgEquiv'.injective (by rw [map_mul, map_mul]; exact h3)`.
-/
theorem commute_of_commute_separable_of_isAlgClosed {L : Type} [Field L] [IsAlgClosed L] {n : ℕ}
    {A g h : Matrix (Fin n) (Fin n) L} (hA : A.charpoly.Separable) (hg : Commute A g) (hh : Commute A h) :
    Commute g h := by
  set f := Matrix.toLin' A
  have hc : f.charpoly = A.charpoly := Matrix.charpoly_toLin' A
  have hfg : Commute f (Matrix.toLin' g) := hg.map Matrix.toLinAlgEquiv'
  have hfh : Commute f (Matrix.toLin' h) := hh.map Matrix.toLinAlgEquiv'
  have key : ∀ μ, Module.End.maxGenEigenspace f μ ≤
      LinearMap.ker (Matrix.toLin' g * Matrix.toLin' h - Matrix.toLin' h * Matrix.toLin' g) := fun μ v hv => by
    have h1 : Module.finrank L (Module.End.maxGenEigenspace f μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq, hc]; exact Polynomial.rootMultiplicity_le_one_of_separable hA μ
    by_cases h0 : v = 0
    · simp [h0]
    have hs : ∀ w ∈ Module.End.maxGenEigenspace f μ, ∃ c : L, c • v = w := fun w hw => by
      have h2 : Module.finrank L (Module.End.maxGenEigenspace f μ) = 1 := le_antisymm h1
        (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun h => h0 (congrArg Subtype.val h)⟩)
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : Module.End.maxGenEigenspace f μ)
        fun h => h0 (congrArg Subtype.val h)).1 h2 ⟨w, hw⟩
      exact ⟨c, congrArg Subtype.val hc⟩
    obtain ⟨c, hc⟩ := hs _ (Module.End.mapsTo_maxGenEigenspace_of_comm hfg μ hv)
    obtain ⟨d, hd⟩ := hs _ (Module.End.mapsTo_maxGenEigenspace_of_comm hfh μ hv)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, ← hc, ← hd, map_smul,
      map_smul, ← hc, ← hd, smul_comm, sub_self]
  have h3 := iSup_le key
  rw [Module.End.iSup_maxGenEigenspace_eq_top, top_le_iff, LinearMap.ker_eq_top, sub_eq_zero] at h3
  exact Matrix.toLinAlgEquiv'.injective (by rw [map_mul, map_mul]; exact h3)

/- English proof (translation)
Use `set φ := algebraMap K (AlgebraicClosure K)`. Establish `hA' : (A.map φ).charpoly.Separable`. Rewrite using `[Matrix.charpoly_map]`. Conclude with `hA.map`. Establish `hg' : Commute (A.map φ) (g.map φ)`.

Unfold `Commute SemiconjBy`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, hg.eq]`. Establish `hh' : Commute (A.map φ) (h.map φ)`. Unfold `Commute SemiconjBy`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, hh.eq]`.

Use `commute_of_commute_separable_of_isAlgClosed hA' hg' hh'` as an intermediate fact. Unfold `Commute SemiconjBy at this ⊢`. Rewrite `this` using `[← Matrix.map_mul, ← Matrix.map_mul]`. Conclude with `Matrix.map_injective φ.injective this`.
-/
theorem commute_of_commute_separable {K : Type} [Field K] {n : ℕ} {A g h : Matrix (Fin n) (Fin n) K}
    (hA : A.charpoly.Separable) (hg : Commute A g) (hh : Commute A h) : Commute g h := by
  set φ := algebraMap K (AlgebraicClosure K)
  have hA' : (A.map φ).charpoly.Separable := by
    rw [Matrix.charpoly_map]; exact hA.map
  have hg' : Commute (A.map φ) (g.map φ) := by
    unfold Commute SemiconjBy; rw [← Matrix.map_mul, ← Matrix.map_mul, hg.eq]
  have hh' : Commute (A.map φ) (h.map φ) := by
    unfold Commute SemiconjBy; rw [← Matrix.map_mul, ← Matrix.map_mul, hh.eq]
  have := commute_of_commute_separable_of_isAlgClosed hA' hg' hh'
  unfold Commute SemiconjBy at this ⊢
  rw [← Matrix.map_mul, ← Matrix.map_mul] at this
  exact Matrix.map_injective φ.injective this

end GlobalTheory.BCT.CentComm

namespace GlobalTheory.BCT

/- English proof (translation)
Introduce `E _ _ _ _ n w y hy a ha b hb`. Establish `ha' : a.1.val * y.1.val = y.1.val * a.1.val` using `congrArg (fun z : UL n w => z.1.val) ha`. Establish `hb' : b.1.val * y.1.val = y.1.val * b.1.val` using `congrArg (fun z : UL n w => z.1.val) hb`. Use `CentComm.commute_of_commute_separable hy ha'.symm hb'.symm` as an intermediate fact. Conclude with `Subtype.ext (Units.ext this.eq)`.
-/
theorem centComm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (w : Pl E) (y : UL n w),
    y.1.val.charpoly.Separable → ∀ a ∈ twCent (MonoidHom.id (UL n w)) y, ∀ b ∈ twCent (MonoidHom.id (UL n w)) y,
      a * b = b * a := by
  intro E _ _ _ _ n w y hy a ha b hb
  have ha' : a.1.val * y.1.val = y.1.val * a.1.val := congrArg (fun z : UL n w => z.1.val) ha
  have hb' : b.1.val * y.1.val = y.1.val * b.1.val := congrArg (fun z : UL n w => z.1.val) hb
  have := CentComm.commute_of_commute_separable hy ha'.symm hb'.symm
  exact Subtype.ext (Units.ext this.eq)

end GlobalTheory.BCT
