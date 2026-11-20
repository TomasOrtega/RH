import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenericFibreVar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedOne
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedMixedNonneg
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPrincipalDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

def intNumMultilinear {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (I : Ideal (MRingOver ℚ ι)) (n : ℕ) (hI : NumbersDVR.IsMultiHomogIdeal I)
    (hr : NumbersDVR.IsRelevant I) (hd : FieldNumbers.relDim I = n) :
    MultilinearMap ℤ (fun _ : Fin n => K → ℤ) ℤ where
  toFun bs := NumbersDVR.intNum ℚ I bs
  map_update_add' := by
    intro inst bs i x y
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    exact FieldNumbers.IntNumAdd.full ℚ K ι I hI hr n hd bs i x y
  map_update_smul' := by
    intro inst bs i c x
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    let g : (K → ℤ) →+ ℤ := AddMonoidHom.mk' (fun x => NumbersDVR.intNum ℚ I (Function.update bs i x))
      fun x y => FieldNumbers.IntNumAdd.full ℚ K ι I hI hr n hd bs i x y
    exact map_zsmul g c x

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem intNumMultilinear_apply {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (I : Ideal (MRingOver ℚ ι)) (n : ℕ) (hI : NumbersDVR.IsMultiHomogIdeal I)
    (hr : NumbersDVR.IsRelevant I) (hd : FieldNumbers.relDim I = n) (bs : Fin n → K → ℤ) :
    intNumMultilinear I n hI hr hd bs = NumbersDVR.intNum ℚ I bs :=
  rfl

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D a n w p q hV hw hgw hpos hq`. Set `_ : LinearOrder K` to `LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective`. Set `_ : ∀ k, LinearOrder (ι k)` to `fun k => LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective`. Establish `hGa` using `(hFib K ι Ω y a n w hw hgw).1`. Establish `hPV` using `hVar K ι Ω y D hV`.

Establish `hP` using `(Bridge.isMultiProjPrime_iff _).mpr hPV.1`. Establish `hd : FieldNumbers.relDim (KH.genIdeal y) = D`. Rewrite using `[FieldNumbers.relDim_of_ringKrullDim_eq _ _ hPV.2]`. Simplify using `only [Nat.cast_add, add_sub_cancel_right]`. Both sides reduce to the same expression.

Use `set f := intNumMultilinear (KH.genIdeal y) D hP.multiHomog hP.relevant hd with hf`. Establish `hg : ∀ b, genDeg (mCoordIdeal y) D b = f (fun _ => b)` using `fun b => by`. Rewrite using `[hf, intNumMultilinear_apply, genDeg]`. Reduce the equality to equality of the corresponding arguments. Establish `key : ∀ s : Finset (Fin D), 0 ≤ f (s.piecewise (fun _ => a) fun _ _ => 1)`.

Introduce `s`. Use `hNonneg ℚ K ι (KH.genIdeal y) D (s.piecewise (fun _ => a) fun _ _ => 1) hPV fun i => by` as an intermediate fact. Distinguish the cases in `hi : i ∈ s`. Simplify `hGa` using `[Finset.piecewise, hi]`. Simplify `hOne ℚ K ι (KH.genIdeal y)` using `[Finset.piecewise, hi]`.

Rewrite using `[hf, intNumMultilinear_apply]`. Use `this` and compare the differences between its conclusion and the goal. Rewrite `hpos`, the goal using `[hg]`. Establish `hsplit : (fun _ : Fin D => (q : ℤ) • a + fun _ => (p : ℤ)) = (fun _ : Fin D => (q : ℤ) • a) + fun _ : Fin D => (p : ℤ) • fun _ : K => (1 : ℤ)`. Use function extensionality and compare the values at `i k`.

Simplify using the standard rewrite rules. Rewrite using `[hsplit, f.map_add_univ]`. Use `Finset.sum_pos' (fun s _ => ?_) ⟨Finset.univ, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Establish `hs : s.piecewise (fun _ : Fin D => (q : ℤ) • a) (fun _ => (p : ℤ) • fun _ : K => (1 : ℤ)) = fun i => (if i ∈ s then (q : ℤ) else p) • s.piecewise (fun _ => a) (fun _ _ => 1) i`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `by_cases hi : i ∈ s <;> simp [hi]`. Rewrite using `[hs, f.map_smul_univ]`. Apply the tactic sequence `exact smul_nonneg (Finset.prod_nonneg fun i _ => by split_ifs <;> positivity) (key s)`. Rewrite using `[Finset.piecewise_univ, show (fun _ : Fin D => (q : ℤ) • a) = fun i => (q : ℤ) • (fun _ : Fin D => a) i from rfl, f.map_smul_univ]`. Conclude with `smul_pos (Finset.prod_pos fun _ _ => by exact_mod_cast hq) hpos`.
-/
theorem GenDegTwist.proof (hFib : GenOnFibres.Statement) (hVar : GenericFibreVar.Statement)
    (hOne : GeneratedOne.Statement) (hNonneg : GeneratedMixedNonneg.Statement) :
    GenDegTwist.Statement := by
  intro K _ ι _ Ω _ y D a n w p q hV hw hgw hpos hq
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  have hGa := (hFib K ι Ω y a n w hw hgw).1
  have hPV := hVar K ι Ω y D hV
  have hP := (Bridge.isMultiProjPrime_iff _).mpr hPV.1
  have hd : FieldNumbers.relDim (KH.genIdeal y) = D := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq _ _ hPV.2]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  set f := intNumMultilinear (KH.genIdeal y) D hP.multiHomog hP.relevant hd with hf
  have hg : ∀ b, genDeg (mCoordIdeal y) D b = f (fun _ => b) := fun b => by
    rw [hf, intNumMultilinear_apply, genDeg]
    congr
  have key : ∀ s : Finset (Fin D), 0 ≤ f (s.piecewise (fun _ => a) fun _ _ => 1) := by
    intro s
    have := hNonneg ℚ K ι (KH.genIdeal y) D (s.piecewise (fun _ => a) fun _ _ => 1) hPV fun i => by
      by_cases hi : i ∈ s
      · simpa [Finset.piecewise, hi] using hGa
      · simpa [Finset.piecewise, hi] using hOne ℚ K ι (KH.genIdeal y)
    rw [hf, intNumMultilinear_apply]
    convert this
  rw [hg] at hpos ⊢
  have hsplit : (fun _ : Fin D => (q : ℤ) • a + fun _ => (p : ℤ)) =
      (fun _ : Fin D => (q : ℤ) • a) + fun _ : Fin D => (p : ℤ) • fun _ : K => (1 : ℤ) := by
    funext i k
    simp
  rw [hsplit, f.map_add_univ]
  refine Finset.sum_pos' (fun s _ => ?_) ⟨Finset.univ, Finset.mem_univ _, ?_⟩
  · have hs : s.piecewise (fun _ : Fin D => (q : ℤ) • a) (fun _ => (p : ℤ) • fun _ : K => (1 : ℤ)) =
        fun i => (if i ∈ s then (q : ℤ) else p) • s.piecewise (fun _ => a) (fun _ _ => 1) i := by
      funext i
      by_cases hi : i ∈ s <;> simp [hi]
    rw [hs, f.map_smul_univ]
    exact smul_nonneg (Finset.prod_nonneg fun i _ => by split_ifs <;> positivity) (key s)
  · rw [Finset.piecewise_univ, show (fun _ : Fin D => (q : ℤ) • a) = fun i => (q : ℤ) • (fun _ : Fin D => a) i
      from rfl, f.map_smul_univ]
    exact smul_pos (Finset.prod_pos fun _ _ => by exact_mod_cast hq) hpos

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
