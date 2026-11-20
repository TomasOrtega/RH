import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsVeroneseGraph
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
import GroundTheory.HeightsAndTheta.Heights.Intersections.QuotientMapImageZInjective
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartRankAdjoin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace VeroneseGraphDeg

/- English proof (translation)
Establish `h` using `Inter.AvoidRing.isMultiHomog_mul (Inter.AvoidRing.isMultiHomog_X (R := ℤ) (ι := GlobalTheory (Fin (D + 1))) () q.2.1.1) (Inter.AvoidRing.isMultiHomog_X (R := ℤ) (ι := GlobalTheory (Fin (D + 1))) () q.2.1.2)`. Establish `e : ((fun _ _ => 2 : Unit → Unit → ℕ) q.1) = Pi.single () 1 + Pi.single () 1`. Use function extensionality and compare the values at `k`. Consider the cases of `k`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Conclude with `h`.
-/
theorem isMultiHomog_forms (D : ℕ) (q : Ix (Veronese.Idx D)) :
    IsMultiHomog (Veronese.forms D q) ((fun _ _ => 2 : Unit → Unit → ℕ) q.1) := by
  have h := Inter.AvoidRing.isMultiHomog_mul
    (Inter.AvoidRing.isMultiHomog_X (R := ℤ) (ι := GlobalTheory (Fin (D + 1))) () q.2.1.1)
    (Inter.AvoidRing.isMultiHomog_X (R := ℤ) (ι := GlobalTheory (Fin (D + 1))) () q.2.1.2)
  have e : ((fun _ _ => 2 : Unit → Unit → ℕ) q.1) = Pi.single () 1 + Pi.single () 1 := by
    funext k
    cases k
    simp
  rw [e]
  exact h

def xc {D : ℕ} (i : Fin (D + 1)) : Σ k, Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)) k := ⟨Sum.inl (), i⟩

def yc {D : ℕ} (i j : Fin (D + 1)) (h : i ≤ j) : Σ k, Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)) k :=
  ⟨Sum.inr (), ⟨(i, j), h⟩⟩

abbrev Γ (D : ℕ) : Ideal (MRing (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)))) :=
  graphIdeal ⊥ (Veronese.forms D)

/- English proof (translation)
The claim follows from `eval₂Hom_X' _ _ _`.
-/
theorem graphMap_xc {D : ℕ} (i : Fin (D + 1)) :
    graphMap (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) (Veronese.forms D) (X (xc i)) =
      C (Ideal.Quotient.mk ⊥ (X ⟨(), i⟩)) :=
  eval₂Hom_X' _ _ _

/- English proof (translation)
The claim follows from `eval₂Hom_X' _ _ _`.
-/
theorem graphMap_yc {D : ℕ} (i j : Fin (D + 1)) (h : i ≤ j) :
    graphMap (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) (Veronese.forms D) (X (yc i j h)) =
      C (Ideal.Quotient.mk ⊥ (X ⟨(), i⟩ * X ⟨(), j⟩)) * X () :=
  eval₂Hom_X' _ _ _

/- English proof (translation)
Rewrite using `[Γ, graphIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, graphMap_xc, graphMap_xc, graphMap_yc, graphMap_yc]`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rel_mem (D : ℕ) (i : Fin (D + 1)) :
    (X (xc 0) * X (yc 0 i (Fin.zero_le i)) - X (xc i) * X (yc 0 0 le_rfl) :
        MRing (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)))) ∈ Γ D := by
  rw [Γ, graphIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, graphMap_xc, graphMap_xc, graphMap_yc,
    graphMap_yc]
  simp only [map_mul]
  ring

/- English proof (translation)
Rewrite using `[Γ, graphIdeal, RingHom.mem_ker, graphMap_yc]`. Use `mul_ne_zero ?_ (X_ne_zero _)` and prove the remaining obligations. Rewrite using `[Ne, C_eq_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]`. Conclude with `mul_ne_zero (X_ne_zero _) (X_ne_zero _)`.
-/
theorem veroneseFirstCoordinate_not_mem_graph (D : ℕ) :
    (X (yc 0 0 le_rfl) : MRing (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)))) ∉ Γ D := by
  rw [Γ, graphIdeal, RingHom.mem_ker, graphMap_yc]
  refine mul_ne_zero ?_ (X_ne_zero _)
  rw [Ne, C_eq_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
  exact mul_ne_zero (X_ne_zero _) (X_ne_zero _)

/- English proof (translation)
Rewrite using `[Γ, graphIdeal, RingHom.mem_ker, graphMap_xc, C_eq_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]`. Conclude with `X_ne_zero _`.
-/
theorem x_not_mem (D : ℕ) (i : Fin (D + 1)) :
    (X (xc i) : MRing (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)))) ∉ Γ D := by
  rw [Γ, graphIdeal, RingHom.mem_ker, graphMap_xc, C_eq_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
  exact X_ne_zero _

/- English proof (translation)
Introduce `h`. Apply `hp` to reduce the goal to its premises. Rewrite using `[← G.genericFibre_ker_target, RingHom.mem_ker, aeval_X]`. Conclude with `h`.
-/
theorem x'_ne_zero {D : ℕ} (G : GenFibre (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) (Γ D))
    (p : Σ k, Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)) k) (hp : (X p : MRing _) ∉ Γ D) :
    G.x' p ≠ 0 := by
  intro h
  apply hp
  rw [← G.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
  exact h

/- English proof (translation)
Establish `h0` using `x'_ne_zero G _ (x_not_mem D 0)`. Establish `h00` using `x'_ne_zero G _ (veroneseFirstCoordinate_not_mem_graph D)`. Establish `hr : aeval G.x' (X (xc 0) * X (yc 0 i (Fin.zero_le i)) - X (xc i) * X (yc 0 0 le_rfl) : MRing (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)))) = 0`. Rewrite using `[← RingHom.mem_ker, G.genericFibre_ker_target]`. Conclude with `rel_mem D i`.

Simplify using `only [map_sub, map_mul, aeval_X, sub_eq_zero] at hr`. Establish `c1 : G.x' (yc 0 i (Fin.zero_le i)) = algebraMap G.Φ G.Φ' (G.x ⟨(), ⟨(0, i), Fin.zero_le i⟩⟩)` using `G.compat ⟨(), ⟨(0, i), Fin.zero_le i⟩⟩`. Establish `c2 : G.x' (yc 0 0 le_rfl) = algebraMap G.Φ G.Φ' (G.x ⟨(), ⟨(0, 0), le_rfl⟩⟩)` using `G.compat ⟨(), ⟨(0, 0), le_rfl⟩⟩`. Rewrite using `[IntermediateField.mem_bot]`. Use `⟨G.x ⟨(), ⟨(0, i), Fin.zero_le i⟩⟩ / G.x ⟨(), ⟨(0, 0), le_rfl⟩⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_div₀, ← c1, ← c2, div_eq_div_iff h00 h0]`. Rewrite `hr` using `[mul_comm]`. Rewrite using `[hr, mul_comm]`.
-/
theorem ratio_mem {D : ℕ} (G : GenFibre (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) (Γ D))
    (i : Fin (D + 1)) : G.x' (xc i) / G.x' (xc 0) ∈ (⊥ : IntermediateField G.Φ G.Φ') := by
  have h0 := x'_ne_zero G _ (x_not_mem D 0)
  have h00 := x'_ne_zero G _ (veroneseFirstCoordinate_not_mem_graph D)
  have hr : aeval G.x' (X (xc 0) * X (yc 0 i (Fin.zero_le i)) - X (xc i) * X (yc 0 0 le_rfl) :
        MRing (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)))) = 0 := by
    rw [← RingHom.mem_ker, G.genericFibre_ker_target]
    exact rel_mem D i
  simp only [map_sub, map_mul, aeval_X, sub_eq_zero] at hr
  have c1 : G.x' (yc 0 i (Fin.zero_le i)) = algebraMap G.Φ G.Φ' (G.x ⟨(), ⟨(0, i), Fin.zero_le i⟩⟩) :=
    G.compat ⟨(), ⟨(0, i), Fin.zero_le i⟩⟩
  have c2 : G.x' (yc 0 0 le_rfl) = algebraMap G.Φ G.Φ' (G.x ⟨(), ⟨(0, 0), le_rfl⟩⟩) :=
    G.compat ⟨(), ⟨(0, 0), le_rfl⟩⟩
  rw [IntermediateField.mem_bot]
  refine ⟨G.x ⟨(), ⟨(0, i), Fin.zero_le i⟩⟩ / G.x ⟨(), ⟨(0, 0), le_rfl⟩⟩, ?_⟩
  rw [map_div₀, ← c1, ← c2, div_eq_div_iff h00 h0]
  rw [mul_comm] at hr
  rw [hr, mul_comm]

end VeroneseGraphDeg

open VeroneseGraphDeg in

/- English proof (translation)
Introduce `D hD`. Establish `hP : IsArithVar (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) (D + 1)` using `IndefiniteRowSideFullHecke.Inter.isArithVar_bot D`. Establish `hnv : ∀ u : Unit, ∃ j, Veronese.forms D ⟨u, j⟩ ∉ (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1)))))`. Introduce `u`. Use `⟨⟨(0, 0), le_rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Ideal.mem_bot]`. Conclude with `mul_ne_zero (X_ne_zero _) (X_ne_zero _)`. Establish `hΓ : IsArithVar (Γ D) (D + 1)` using `(hGr Unit (GlobalTheory (Fin (D + 1))) Unit (GlobalTheory (Veronese.Idx D)) ⊥ (D + 1) (Veronese.forms D) (fun _ _ => 2) hP (isMultiHomog_forms D) hnv).1`. Establish `hIm : IsArithVar (imageZ (inrV (ι` using `GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) (Γ D)) (D + 1) := by`. Rewrite using `[Γ, hImg D]`.

Conclude with `VeroneseArith.proof D hD`. Establish `: (Γ D).IsPrime` using `hΓ.2.1.1`. Set `G : GenFibre (inrV (ι` to `GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) (Γ D) := Inter.genFibreOf _ _`. Take `⟨J, hJ, -⟩` from `hEU G.Φ (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) (fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr)`. Establish `hpt : IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0` using `hDim Unit (GlobalTheory (Veronese.Idx D)) (Unit ⊕ Unit) (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr inrV _ (D + 1) 0 G isBlockMap_inr hΓ hIm`.

Set `ch : (k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) → fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr k` to `fun`. Consider the case `⟨Sum.inl _, _⟩ => (0 : Fin (D + 1))`. Consider the case `⟨Sum.inr u, h⟩ => absurd ⟨u, rfl⟩ h`. Establish `hz : ∀ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit), G.x' ⟨k.1, ch k⟩ ≠ 0`. Introduce and unpack `⟨(u | u), h⟩`.

Consider the cases of `u`. Conclude with `x'_ne_zero G _ (x_not_mem D 0)`. Conclude with `absurd ⟨u, rfl⟩ h`. Establish `hch : IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch`. Introduce `k`.

Rewrite using `[ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]`. Conclude with `hz k`. Use `⟨G, J, hJ, ?_⟩` and prove the remaining obligations. Rewrite using `[hJ.1 _ _ _ hpt hch]`. Establish `hdeg` using `Inter.ChartRankAdjoin.proof (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) (fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr) G.Φ G.Φ' (fun q => G.x' ⟨q.1.1, q.2⟩) ch hz hpt.1.2.1`.

Establish `hbot : IntermediateField.adjoin G.Φ (Set.range fun q : Σ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit), fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr k => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, ch q.1⟩) = ⊥`. Rewrite using `[eq_bot_iff, IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨⟨⟨(u | u), h⟩, i⟩, rfl⟩`. Consider the cases of `u`. Conclude with `ratio_mem G i`.

Conclude with `absurd ⟨u, rfl⟩ h`. Express the relevant statement in the definitionally equal form `((ptDeg (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch : ℕ) : ℤ) = 1`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, hdeg, hbot, IntermediateField.finrank_bot, Nat.cast_one]`.
-/
theorem VeroneseGraphDeg.proof (hGr : GraphStatement) (hImg : VeroneseGraphImage.Statement)
    (hDim : FibreDimStatement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι) :
    VeroneseGraphDeg.Statement := by
  intro D hD
  have hP : IsArithVar (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) (D + 1) := IndefiniteRowSideFullHecke.Inter.isArithVar_bot D
  have hnv : ∀ u : Unit, ∃ j, Veronese.forms D ⟨u, j⟩ ∉ (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) := by
    intro u
    refine ⟨⟨(0, 0), le_rfl⟩, ?_⟩
    rw [Ideal.mem_bot]
    exact mul_ne_zero (X_ne_zero _) (X_ne_zero _)
  have hΓ : IsArithVar (Γ D) (D + 1) :=
    (hGr Unit (GlobalTheory (Fin (D + 1))) Unit (GlobalTheory (Veronese.Idx D)) ⊥ (D + 1) (Veronese.forms D) (fun _ _ => 2) hP
      (isMultiHomog_forms D) hnv).1
  have hIm : IsArithVar (imageZ (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) (Γ D)) (D + 1) := by
    rw [Γ, hImg D]
    exact VeroneseArith.proof D hD
  have : (Γ D).IsPrime := hΓ.2.1.1
  let G : GenFibre (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) (Γ D) := Inter.genFibreOf _ _
  obtain ⟨J, hJ, -⟩ := hEU G.Φ (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr)
  have hpt : IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 :=
    hDim Unit (GlobalTheory (Veronese.Idx D)) (Unit ⊕ Unit) (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr
      inrV _ (D + 1) 0 G isBlockMap_inr hΓ hIm

  let ch : (k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) →
      fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr k := fun
    | ⟨Sum.inl _, _⟩ => (0 : Fin (D + 1))
    | ⟨Sum.inr u, h⟩ => absurd ⟨u, rfl⟩ h
  have hz : ∀ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit), G.x' ⟨k.1, ch k⟩ ≠ 0 := by
    rintro ⟨(u | u), h⟩
    · cases u
      exact x'_ne_zero G _ (x_not_mem D 0)
    · exact absurd ⟨u, rfl⟩ h
  have hch : IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch := by
    intro k
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]
    exact hz k
  refine ⟨G, J, hJ, ?_⟩
  rw [hJ.1 _ _ _ hpt hch]
  have hdeg := Inter.ChartRankAdjoin.proof (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr) G.Φ G.Φ'
    (fun q => G.x' ⟨q.1.1, q.2⟩) ch hz hpt.1.2.1
  have hbot : IntermediateField.adjoin G.Φ (Set.range fun q : Σ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit),
      fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr k =>
        G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, ch q.1⟩) = ⊥ := by
    rw [eq_bot_iff, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨⟨(u | u), h⟩, i⟩, rfl⟩
    · cases u
      exact ratio_mem G i
    · exact absurd ⟨u, rfl⟩ h
  change ((ptDeg (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch : ℕ) : ℤ) = 1
  rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, hdeg, hbot, IntermediateField.finrank_bot, Nat.cast_one]

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
