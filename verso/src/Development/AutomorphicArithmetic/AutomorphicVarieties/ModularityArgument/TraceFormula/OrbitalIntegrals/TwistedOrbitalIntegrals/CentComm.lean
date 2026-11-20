import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

noncomputable section

open Module

namespace UpperTheory.V.Z.Tf.Orb

/- English proof (translation)
Establish `key : ∀ μ : L, ∀ v ∈ f.maxGenEigenspace μ, (x * y) v = (y * x) v`. Introduce `μ v hv`. Establish `h1 : finrank L (f.maxGenEigenspace μ) ≤ 1`. Rewrite using `[LinearMap.finrank_maxGenEigenspace_eq]`. Conclude with `Polynomial.rootMultiplicity_le_one_of_separable hf μ`.

Take `⟨w, hw⟩` from `finrank_le_one_iff.mp h1`. Establish `mx` using `Module.End.mapsTo_maxGenEigenspace_of_comm hx.symm μ`. Establish `my` using `Module.End.mapsTo_maxGenEigenspace_of_comm hy.symm μ`. Take `⟨c, hc⟩` from `hw ⟨v, hv⟩`. Take `⟨a, ha⟩` from `hw ⟨x w, mx w.2⟩`.

Take `⟨b, hb⟩` from `hw ⟨y w, my w.2⟩`. Establish `hc' : v = c • (w : V)` using `by simpa using (congrArg Subtype.val hc).symm`. Establish `ha' : x w = a • (w : V)` using `by simpa using (congrArg Subtype.val ha).symm`. Establish `hb' : y w = b • (w : V)` using `by simpa using (congrArg Subtype.val hb).symm`. Simplify using `only [hc', Module.End.mul_apply, map_smul, ha', hb', smul_smul, mul_comm a b]`.

Establish `htop` using `Module.End.iSup_maxGenEigenspace_eq_top f`. Establish `: (⊤ : Submodule L V) ≤ LinearMap.eqLocus (x * y) (y * x)`. Rewrite using `[← htop]`. Conclude with `iSup_le fun μ v hv => key μ v hv`. Conclude with `LinearMap.ext fun v => this Submodule.mem_top`.
-/
private theorem endComm {L V : Type} [Field L] [IsAlgClosed L] [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (f x y : Module.End L V) (hf : f.charpoly.Separable) (hx : Commute x f) (hy : Commute y f) : Commute x y := by
  have key : ∀ μ : L, ∀ v ∈ f.maxGenEigenspace μ, (x * y) v = (y * x) v := by
    intro μ v hv
    have h1 : finrank L (f.maxGenEigenspace μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq]
      exact Polynomial.rootMultiplicity_le_one_of_separable hf μ
    obtain ⟨w, hw⟩ := finrank_le_one_iff.mp h1
    have mx := Module.End.mapsTo_maxGenEigenspace_of_comm hx.symm μ
    have my := Module.End.mapsTo_maxGenEigenspace_of_comm hy.symm μ
    obtain ⟨c, hc⟩ := hw ⟨v, hv⟩
    obtain ⟨a, ha⟩ := hw ⟨x w, mx w.2⟩
    obtain ⟨b, hb⟩ := hw ⟨y w, my w.2⟩
    have hc' : v = c • (w : V) := by simpa using (congrArg Subtype.val hc).symm
    have ha' : x w = a • (w : V) := by simpa using (congrArg Subtype.val ha).symm
    have hb' : y w = b • (w : V) := by simpa using (congrArg Subtype.val hb).symm
    simp only [hc', Module.End.mul_apply, map_smul, ha', hb', smul_smul, mul_comm a b]
  have htop := Module.End.iSup_maxGenEigenspace_eq_top f
  have : (⊤ : Submodule L V) ≤ LinearMap.eqLocus (x * y) (y * x) := by
    rw [← htop]
    exact iSup_le fun μ v hv => key μ v hv
  exact LinearMap.ext fun v => this Submodule.mem_top

/- English proof (translation)
Introduce `K _ n A X Y hA hX hY`. Set `L` to `AlgebraicClosure K`. Set `φ : Matrix (Fin n) (Fin n) K →+* Module.End L (Fin n → L)` to `(Matrix.toLinAlgEquiv' (R := L) (n := Fin n)).toRingEquiv.toRingHom.comp (algebraMap K L).mapMatrix`. Establish `hφ : Function.Injective φ` using `(Matrix.toLinAlgEquiv' (R := L) (n := Fin n)).injective.comp (Matrix.map_injective (algebraMap K L).injective)`. Establish `hch : (φ A).charpoly = A.charpoly.map (algebraMap K L)`.

Rewrite using `[← Matrix.charpoly_map, ← Matrix.charpoly_toLin']`. Both sides reduce to the same expression. Establish `h` using `endComm (φ A) (φ X) (φ Y) (hch ▸ hA.map) (hX.map φ) (hY.map φ)`. Apply `hφ` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul]`.

Conclude with `h`.
-/
theorem centComm : CentComm := by
  intro K _ n A X Y hA hX hY
  let L := AlgebraicClosure K
  let φ : Matrix (Fin n) (Fin n) K →+* Module.End L (Fin n → L) :=
    (Matrix.toLinAlgEquiv' (R := L) (n := Fin n)).toRingEquiv.toRingHom.comp (algebraMap K L).mapMatrix
  have hφ : Function.Injective φ :=
    (Matrix.toLinAlgEquiv' (R := L) (n := Fin n)).injective.comp
      (Matrix.map_injective (algebraMap K L).injective)
  have hch : (φ A).charpoly = A.charpoly.map (algebraMap K L) := by
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_toLin']
    rfl
  have h := endComm (φ A) (φ X) (φ Y) (hch ▸ hA.map) (hX.map φ) (hY.map φ)
  apply hφ
  rw [map_mul, map_mul]
  exact h

end UpperTheory.V.Z.Tf.Orb
