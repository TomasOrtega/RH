import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace GrassmannianArithmeticVariety

/- English proof (translation)
Set `σ : Equiv.Perm (Fin j)` to `(Equiv.ofInjective h hh).trans ((Equiv.setCongr hr).trans (Equiv.ofInjective g hg).symm)`. Establish `hσ : ∀ i, g (σ i) = h i`. Introduce `i`. Simplify using `[σ, Equiv.apply_ofInjective_symm]`. Use `⟨Equiv.Perm.sign σ, ?_⟩` and prove the remaining obligations.

Establish `: A.submatrix id h = (A.submatrix id g).submatrix id σ`. Use extensionality with `r i`. Simplify using `[hσ]`. Rewrite using `[this, det_permute']`.
-/
theorem det_submatrix_sign {R : Type*} [CommRing R] {j N : ℕ} (A : Matrix (Fin j) (Fin N) R)
    (g h : Fin j → Fin N) (hg : Function.Injective g) (hh : Function.Injective h)
    (hr : Set.range h = Set.range g) :
    ∃ s : ℤˣ, (A.submatrix id h).det = ((s : ℤ) : R) * (A.submatrix id g).det := by
  let σ : Equiv.Perm (Fin j) :=
    (Equiv.ofInjective h hh).trans ((Equiv.setCongr hr).trans (Equiv.ofInjective g hg).symm)
  have hσ : ∀ i, g (σ i) = h i := by
    intro i
    simp [σ, Equiv.apply_ofInjective_symm]
  refine ⟨Equiv.Perm.sign σ, ?_⟩
  have : A.submatrix id h = (A.submatrix id g).submatrix id σ := by
    ext r i; simp [hσ]
  rw [this, det_permute']

def col {j m : ℕ} (a : Fin j) (b : Fin m) (i : Fin j) : Fin (j + m) :=
  if i = a then Fin.natAdd j b else Fin.castAdd m i

/- English proof (translation)
Introduce `x y hxy`. Simplify using `only [col] at hxy`. Use `split_ifs at hxy with h1 h2 h2`. Conclude with `h1.trans h2.symm`. Rewrite `hxy` using `[Fin.ext_iff]`.

Simplify using `at hxy`. Use linear arithmetic over natural numbers and integers. Rewrite `hxy` using `[Fin.ext_iff]`. Simplify using `at hxy`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Fin.ext_iff] at hxy; exact Fin.ext (by simpa using hxy)`.
-/
theorem col_injective {j m : ℕ} (a : Fin j) (b : Fin m) : Function.Injective (col a b) := by
  intro x y hxy
  simp only [col] at hxy
  split_ifs at hxy with h1 h2 h2
  · exact h1.trans h2.symm
  · rw [Fin.ext_iff] at hxy; simp at hxy; omega
  · rw [Fin.ext_iff] at hxy; simp at hxy; omega
  · rw [Fin.ext_iff] at hxy; exact Fin.ext (by simpa using hxy)

def idx {j m : ℕ} (a : Fin j) (b : Fin m) : PlIdx j m :=
  ⟨Finset.univ.map ⟨col a b, col_injective a b⟩, by simp⟩

/- English proof (translation)
Take `⟨s, hs⟩` from `det_submatrix_sign (onePipe Z) (col a b) _ (col_injective a b) ((idx a b).1.orderEmbOfFin (idx a b).2).injective (by`. Rewrite using `[Finset.range_orderEmbOfFin]`. Simplify using `[idx])`. Use `⟨s, ?_⟩` and prove the remaining obligations. Establish `hcol : (onePipe Z).submatrix id (col a b) = (1 : Matrix (Fin j) (Fin j) R).updateCol a (fun r => Z r b)`.

Use extensionality with `r i`. Distinguish the cases in `hi : i = a`. Simplify using `[col, onePipe, hi]`. Simplify using `[col, onePipe, hi]`. Rewrite using `[colsOf, hs, hcol, ← cramer_apply, cramer_one]`.

Both sides reduce to the same expression.
-/
theorem minor_idx {R : Type*} [CommRing R] {j m : ℕ} (Z : Matrix (Fin j) (Fin m) R)
    (a : Fin j) (b : Fin m) :
    ∃ s : ℤˣ, (colsOf (onePipe Z) (idx a b)).det = ((s : ℤ) : R) * Z a b := by
  obtain ⟨s, hs⟩ := det_submatrix_sign (onePipe Z) (col a b) _ (col_injective a b)
    ((idx a b).1.orderEmbOfFin (idx a b).2).injective (by
      rw [Finset.range_orderEmbOfFin]; simp [idx])
  refine ⟨s, ?_⟩
  have hcol : (onePipe Z).submatrix id (col a b) = (1 : Matrix (Fin j) (Fin j) R).updateCol a
      (fun r => Z r b) := by
    ext r i
    by_cases hi : i = a
    · simp [col, onePipe, hi]
    · simp [col, onePipe, hi]
  rw [colsOf, hs, hcol, ← cramer_apply, cramer_one]
  rfl

/- English proof (translation)
Establish `he : ((plAnchor j m).1.orderEmbOfFin (plAnchor j m).2 : Fin j → Fin (j + m)) = Fin.castAdd m` using `(Finset.orderEmbOfFin_unique _ (fun x => by simp [plAnchor]) (Fin.strictMono_castAdd m)).symm`. Use extensionality with `r i`. Simplify using `[colsOf, onePipe, he]`.
-/
theorem colsOf_anchor {R : Type*} [CommRing R] {j m : ℕ} (Z : Matrix (Fin j) (Fin m) R) :
    colsOf (onePipe Z) (plAnchor j m) = 1 := by
  have he : ((plAnchor j m).1.orderEmbOfFin (plAnchor j m).2 : Fin j → Fin (j + m)) =
      Fin.castAdd m :=
    (Finset.orderEmbOfFin_unique _ (fun x => by simp [plAnchor]) (Fin.strictMono_castAdd m)).symm
  ext r i
  simp [colsOf, onePipe, he]

end GrassmannianArithmeticVariety

open GrassmannianArithmeticVariety in

/- English proof (translation)
Introduce `f j m hf`. Set `e : Fin (f * j * m) ≃ Fin f × Fin j × Fin m` to `finProdFinEquiv.symm.trans ((finProdFinEquiv.symm.prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _))`. Set `φ` to `IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin f × Fin j × Fin m) ℚ) (GrassField f j m)`. Set `t : Fin (f * j * m) → GrassField f j m` to `fun i => φ (X (e i))`. Establish `anchor : ∀ τ, grassCoord f j m ⟨τ, plAnchor j m⟩ = 1`.

Introduce `τ`. Establish `hp : grassPolyCoord f j m ⟨τ, plAnchor j m⟩ = 1` using `(congrArg Matrix.det (colsOf_anchor _)).trans det_one`. Rewrite using `[grassCoord, hp, map_one]`. Establish `hmem : ∀ q : MvPolynomial (Fin f × Fin j × Fin m) ℚ, algebraMap _ (GrassField f j m) q ∈ IntermediateField.adjoin ℚ (Set.range t)`. Introduce `q`.

Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C c`. Rewrite using `[← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]`. Conclude with `IntermediateField.algebraMap_mem _ c`. Consider the case `add p q hp hq => rw [map_add]`.

Conclude with `add_mem hp hq`. Consider the case `mul_X p i hp`. Rewrite using `[map_mul]`. Conclude with `mul_mem hp (IntermediateField.subset_adjoin _ _ ⟨e.symm i, by simp [t, φ]⟩)`. Use `h (Fin f) (plBlocks f j m) (GrassField f j m) (grassCoord f j m) (fun _ => plAnchor j m) (f * j * m) t ⟨⟨0, hf⟩⟩ (fun τ => by rw [anchor]; exact one_ne_zero) ?_ ?_ ?_` and prove the remaining obligations.

Conclude with `((MvPolynomial.algebraicIndependent_X _ ℚ).map' (f := φ) (IsFractionRing.injective _ _)).comp e e.injective`. Introduce `i`. Break down `hi : e i with ⟨τ, a, b⟩` into its components or cases. Take `⟨s, hs⟩ : ∃ s : ℤˣ, grassPolyCoord f j m ⟨τ, idx a b⟩ = ((s : ℤ) : MvPolynomial (Fin f × Fin j × Fin m) ℚ) * X (τ, a, b)` from `minor_idx _ a b`. Establish `hr : grassCoord f j m ⟨τ, idx a b⟩ / grassCoord f j m ⟨τ, plAnchor j m⟩ ∈ IntermediateField.adjoin ℚ (coneRatios (grassCoord f j m) fun _ => plAnchor j m)` using `IntermediateField.subset_adjoin _ _ ⟨⟨τ, idx a b⟩, rfl⟩`.

Establish `hy : grassCoord f j m ⟨τ, idx a b⟩ = ((s : ℤ) : GrassField f j m) * t i`. Rewrite using `[grassCoord, hs, map_mul, map_intCast]`. Simplify using `[t, φ, hi]`. Rewrite `hr` using `[anchor, div_one, hy]`. Break down `Int.units_eq_one_or s with rfl | rfl` into its components or cases.

Simplify using `using hr`. Simplify using `using neg_mem hr`. Introduce and unpack `r ⟨⟨τ, I⟩, rfl⟩`. Establish `hr : grassCoord f j m ⟨τ, I⟩ / grassCoord f j m ⟨τ, plAnchor j m⟩ ∈ IntermediateField.adjoin ℚ (Set.range t)`. Rewrite using `[anchor, div_one]`.

Conclude with `hmem _`. Conclude with `isAlgebraic_algebraMap (R := IntermediateField.adjoin ℚ (Set.range t)) (A := GrassField f j m) ⟨_, hr⟩`.
-/
theorem GrassArithVar.proof (h : CoordConeArithVar.Statement) : GrassArithVar.Statement := by
  intro f j m hf
  let e : Fin (f * j * m) ≃ Fin f × Fin j × Fin m :=
    finProdFinEquiv.symm.trans
      ((finProdFinEquiv.symm.prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _))
  let φ := IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin f × Fin j × Fin m) ℚ) (GrassField f j m)
  let t : Fin (f * j * m) → GrassField f j m := fun i => φ (X (e i))
  have anchor : ∀ τ, grassCoord f j m ⟨τ, plAnchor j m⟩ = 1 := by
    intro τ
    have hp : grassPolyCoord f j m ⟨τ, plAnchor j m⟩ = 1 :=
      (congrArg Matrix.det (colsOf_anchor _)).trans det_one
    rw [grassCoord, hp, map_one]
  have hmem : ∀ q : MvPolynomial (Fin f × Fin j × Fin m) ℚ,
      algebraMap _ (GrassField f j m) q ∈ IntermediateField.adjoin ℚ (Set.range t) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact IntermediateField.algebraMap_mem _ c
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact mul_mem hp (IntermediateField.subset_adjoin _ _ ⟨e.symm i, by simp [t, φ]⟩)
  refine h (Fin f) (plBlocks f j m) (GrassField f j m) (grassCoord f j m) (fun _ => plAnchor j m)
    (f * j * m) t ⟨⟨0, hf⟩⟩ (fun τ => by rw [anchor]; exact one_ne_zero) ?_ ?_ ?_
  · exact ((MvPolynomial.algebraicIndependent_X _ ℚ).map' (f := φ)
      (IsFractionRing.injective _ _)).comp e e.injective
  · intro i
    rcases hi : e i with ⟨τ, a, b⟩
    obtain ⟨s, hs⟩ : ∃ s : ℤˣ, grassPolyCoord f j m ⟨τ, idx a b⟩ =
        ((s : ℤ) : MvPolynomial (Fin f × Fin j × Fin m) ℚ) * X (τ, a, b) :=
      minor_idx _ a b
    have hr : grassCoord f j m ⟨τ, idx a b⟩ / grassCoord f j m ⟨τ, plAnchor j m⟩ ∈
        IntermediateField.adjoin ℚ (coneRatios (grassCoord f j m) fun _ => plAnchor j m) :=
      IntermediateField.subset_adjoin _ _ ⟨⟨τ, idx a b⟩, rfl⟩
    have hy : grassCoord f j m ⟨τ, idx a b⟩ = ((s : ℤ) : GrassField f j m) * t i := by
      rw [grassCoord, hs, map_mul, map_intCast]
      simp [t, φ, hi]
    rw [anchor, div_one, hy] at hr
    rcases Int.units_eq_one_or s with rfl | rfl
    · simpa using hr
    · simpa using neg_mem hr
  · rintro r ⟨⟨τ, I⟩, rfl⟩
    have hr : grassCoord f j m ⟨τ, I⟩ / grassCoord f j m ⟨τ, plAnchor j m⟩ ∈
        IntermediateField.adjoin ℚ (Set.range t) := by
      rw [anchor, div_one]; exact hmem _
    exact isAlgebraic_algebraMap (R := IntermediateField.adjoin ℚ (Set.range t))
      (A := GrassField f j m) ⟨_, hr⟩

end

end GroundTheory.Heights₂.Heights
