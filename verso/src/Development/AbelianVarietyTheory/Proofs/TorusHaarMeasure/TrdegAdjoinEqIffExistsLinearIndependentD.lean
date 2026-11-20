import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.TrdegPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HeightIntegralEstimates
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent

namespace GlobalTheory

open NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.AlgT

open scoped IntermediateField.algebraAdjoinAdjoin in

/- English proof (translation)
Use `set L := IntermediateField.adjoin K (Set.range x) with hL`. Establish `htow : Algebra.trdeg K L + Algebra.trdeg L F = D` using `(trdeg_add_eq K L (A := F)).trans hD`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite `htow` using `[h]`.

Establish `h0 : Algebra.trdeg L F = 0` using `(Cardinal.add_nat_inj D).mp (by rw [add_comm, htow, zero_add])`. Use `haveI : Algebra.IsAlgebraic L F := trdeg_eq_zero_iff.mp h0`. Use `haveI : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range x)) F := Algebra.IsAlgebraic.trans (Algebra.adjoin K (Set.range x)) L F`. Take `⟨t, ht, hb⟩` from `exists_isTranscendenceBasis_subset (R := K) (Set.range x)`. Establish `hc : Cardinal.mk t = Cardinal.mk (Fin D)`.

Rewrite using `[hb.cardinalMk_eq_trdeg, hD, Cardinal.mk_fin]`. Take `⟨e⟩` from `Cardinal.eq.mp hc`. Use `choose J hJ using fun k : Fin D => ht (e.symm k).2`. Use `haveI := hb.isAlgebraic_field`. Use `haveI : CharZero (IntermediateField.adjoin K (Set.range ((↑) : t → F))) := algebraRat.charZero _`.

Take `⟨b, hbD⟩` from `exists_basis_kaehler_of_algebraicIndependent hb.1`. Use `⟨J, ?_⟩` and prove the remaining obligations. Use `b.linearIndependent.comp e.symm e.symm.injective` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`.

Simplify using `only [Function.comp_apply, hbD, hJ]`. Introduce and unpack `⟨J, hJ⟩`. Establish `hind : AlgebraicIndependent K fun k => x (J k)` using `ReciprocityTheory.ChartRestriction.G.AR.differentialIndependence K F D _ hJ`. Set `y : Fin D → L` to `fun k => ⟨x (J k), IntermediateField.subset_adjoin K _ ⟨J k, rfl⟩⟩`. Establish `hy : AlgebraicIndependent K y` using `AlgebraicIndependent.of_comp L.val hind`.

Use `le_antisymm (htow ▸ le_self_add) ?_` and prove the remaining obligations. Simplify using `using hy.cardinalMk_le_trdeg`.
-/
theorem trdeg_adjoin_eq_iff_exists_linearIndependent_D {K F κ : Type} [Field K] [CharZero K]
    [Field F] [Algebra K F] {D : ℕ} (hD : Algebra.trdeg K F = D) (x : κ → F) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) = D ↔
      ∃ J : Fin D → κ, LinearIndependent F fun k => KaehlerDifferential.D K F (x (J k)) := by
  set L := IntermediateField.adjoin K (Set.range x) with hL
  have htow : Algebra.trdeg K L + Algebra.trdeg L F = D := (trdeg_add_eq K L (A := F)).trans hD
  constructor
  · intro h
    rw [h] at htow
    have h0 : Algebra.trdeg L F = 0 :=
      (Cardinal.add_nat_inj D).mp (by rw [add_comm, htow, zero_add])
    haveI : Algebra.IsAlgebraic L F := trdeg_eq_zero_iff.mp h0
    haveI : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range x)) F :=
      Algebra.IsAlgebraic.trans (Algebra.adjoin K (Set.range x)) L F
    obtain ⟨t, ht, hb⟩ := exists_isTranscendenceBasis_subset (R := K) (Set.range x)
    have hc : Cardinal.mk t = Cardinal.mk (Fin D) := by
      rw [hb.cardinalMk_eq_trdeg, hD, Cardinal.mk_fin]
    obtain ⟨e⟩ := Cardinal.eq.mp hc
    choose J hJ using fun k : Fin D => ht (e.symm k).2
    haveI := hb.isAlgebraic_field
    haveI : CharZero (IntermediateField.adjoin K (Set.range ((↑) : t → F))) :=
      algebraRat.charZero _
    obtain ⟨b, hbD⟩ := exists_basis_kaehler_of_algebraicIndependent hb.1
    refine ⟨J, ?_⟩
    have := b.linearIndependent.comp e.symm e.symm.injective
    convert this using 1
    funext k
    simp only [Function.comp_apply, hbD, hJ]
  · rintro ⟨J, hJ⟩
    have hind : AlgebraicIndependent K fun k => x (J k) :=
      ReciprocityTheory.ChartRestriction.G.AR.differentialIndependence K F D _ hJ
    let y : Fin D → L := fun k => ⟨x (J k), IntermediateField.subset_adjoin K _ ⟨J k, rfl⟩⟩
    have hy : AlgebraicIndependent K y := AlgebraicIndependent.of_comp L.val hind
    refine le_antisymm (htow ▸ le_self_add) ?_
    simpa using hy.cardinalMk_le_trdeg

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

/- English proof (translation)
Introduce `d c hD hw`. Establish `hone : ratio (Ω` using `Ω c) (d.w (d.jc c) c) (d.w (d.jc c) c) = 1 := by`. Establish `hex : ∃ a : Ω c, d.w (d.jc c) c = a • d.w (d.jc c) c` using `⟨1, (one_smul _ _).symm⟩`. Establish `h` using `hex.choose_spec`. Rewrite using `[ratio, dif_pos hex]`.

Conclude with `smul_left_injective (Ω c) hw (h.symm.trans (one_smul _ _).symm)`. Establish `heq : IntermediateField.adjoin K (Set.range fun j => ratio (Ω` using `Ω c) (d.w j c) (d.w (d.jc c) c)) = IntermediateField.adjoin K (Set.range (d.x c)) := by`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Break down `Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩` into its components or cases. Simplify using `only [hone]`. Conclude with `one_mem _`. Conclude with `IntermediateField.subset_adjoin K _ ⟨k, rfl⟩`. Apply `IntermediateField.adjoin.mono` to reduce the goal to its premises.

Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `⟨(d.jc c).succAbove k, rfl⟩`. Rewrite using `[TrdegD, heq]`. Conclude with `trdeg_adjoin_eq_iff_exists_linearIndependent_D hD (d.x c)`.
-/
theorem trdegD_iff_exists_linearIndependent_D :
    ∀ (d : Data K ι Ω WT A) (c : ι), Algebra.trdeg K (Ω c) = d.D → d.w (d.jc c) c ≠ 0 →
    (TrdegD d c ↔ ∃ J : Fin d.D → Fin d.N,
      LinearIndependent (Ω c) fun k => KaehlerDifferential.D K (Ω c) (d.x c (J k))) := by
  intro d c hD hw
  have hone : ratio (Ω := Ω c) (d.w (d.jc c) c) (d.w (d.jc c) c) = 1 := by
    have hex : ∃ a : Ω c, d.w (d.jc c) c = a • d.w (d.jc c) c := ⟨1, (one_smul _ _).symm⟩
    have h := hex.choose_spec
    rw [ratio, dif_pos hex]
    exact smul_left_injective (Ω c) hw (h.symm.trans (one_smul _ _).symm)
  have heq : IntermediateField.adjoin K (Set.range fun j =>
      ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) =
      IntermediateField.adjoin K (Set.range (d.x c)) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
      · simp only [hone]
        exact one_mem _
      · exact IntermediateField.subset_adjoin K _ ⟨k, rfl⟩
    · apply IntermediateField.adjoin.mono
      rintro _ ⟨k, rfl⟩
      exact ⟨(d.jc c).succAbove k, rfl⟩
  rw [TrdegD, heq]
  exact trdeg_adjoin_eq_iff_exists_linearIndependent_D hD (d.x c)

end GlobalTheory
