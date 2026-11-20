import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def LiftModel.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (N : K → ℤ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → KH.AmpleV ℚ (KH.genIdeal y) N →
    (∃ c : ℕ, 1 ≤ c ∧ KH.AmpleV ℚ (KH.genIdeal y) (c • N - fun _ => 1)) →
    (∀ ℓ : ℕ, ℓ.Prime → KH.AmpleV (ZMod ℓ) (fibreIdeal ℓ y) N) →
    ∃ (a : ℕ) (ι' : Type) (_ : Fintype ι') (x' : ι' → Ω),
      1 ≤ a ∧ (∀ j, x' j ∈ chartLat y (a • N) 1) ∧ KH.GeneratesOn y (a • N) x' ∧
        Birational (fun p : Σ _ : Unit, ι' => x' p.2)

section Inhabitant

abbrev PtIdx : Unit → Type := blockIdx fun _ : Unit ↦ 0

/- English proof (translation)
Use `⟨fun I => ?_⟩` and prove the remaining obligations. Establish `h` using `I.2.2`. Establish `hc : (I.1 ()).card ≤ 1`. Use `Finset.card_le_univ (α := Fin 1) (I.1 ())` as an intermediate fact. Simplify using `using this`.

Establish `hn` using `(I.2.1 ()).card_pos`. Establish `hs : ∑ k : Unit, ((I.1 k).card - 1) = (I.1 ()).card - 1` using `Fintype.sum_unique _`. Use linear arithmetic over natural numbers and integers.
-/
theorem cell_one_isEmpty : IsEmpty (KH.Cell Unit PtIdx 1) := by
  refine ⟨fun I => ?_⟩
  have h := I.2.2
  have hc : (I.1 ()).card ≤ 1 := by
    have := Finset.card_le_univ (α := Fin 1) (I.1 ())
    simpa using this
  have hn := (I.2.1 ()).card_pos
  have hs : ∑ k : Unit, ((I.1 k).card - 1) = (I.1 ()).card - 1 := Fintype.sum_unique _
  omega

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ => funext fun I => (cell_one_isEmpty.false I).elim⟩`.
-/
theorem cechC_one_subsingleton (S : Type) [CommRing S] (M : Type) [AddCommGroup M]
    [Module (MRingOver S PtIdx) M] : Subsingleton (KH.CechC S PtIdx M (0 + 1)) :=
  ⟨fun _ _ => funext fun I => (cell_one_isEmpty.false I).elim⟩

/- English proof (translation)
Establish `hX : IsMultiHomog (ι` using `PtIdx) (X ⟨(), 0⟩ : MRingOver S PtIdx) (fun _ => 1) := by`. Introduce `m hm k`. Rewrite `hm` using `[mem_support_iff, coeff_X]`. Use `split_ifs at hm with h`. Substitute `h` using the available equality.

Simplify using `[Finsupp.single_apply]`. Conclude with `absurd rfl hm`. Establish `h1 : IsMultiHomog (ι` using `PtIdx) (1 : MRingOver S PtIdx) (fun _ => 0) := by`. Introduce `m hm k`. Rewrite `hm` using `[mem_support_iff, coeff_one]`.

Use `split_ifs at hm with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Conclude with `absurd rfl hm`. Use `⟨1, le_rfl, ?_, fun e => ⟨0, fun c _ => ?_⟩⟩` and prove the remaining obligations.

Introduce `I`. Take `⟨i, hi⟩` from `I.2.1 ()`. Establish `hi0 : i = 0` using `Subsingleton.elim (α := Fin 1) i 0`. Substitute `hi0` using the available equality. Establish `hmon : (X ⟨(), 0⟩ : MRingOver S PtIdx) ∈ KH.cellMon S I.1` using `Submonoid.subset_closure ⟨(), 0, hi, rfl⟩`.

Use `⟨1, fun _ _ => LocalizedModule.mk (Ideal.Quotient.mk ⊥ (X ⟨(), 0⟩)) 1, fun _ => LocalizedModule.mk 1 ⟨X ⟨(), 0⟩, hmon⟩, fun _ => ⟨?_, ?_⟩, fun _ => ?_, ?_⟩` and prove the remaining obligations. Introduce `J _`. Use `Submodule.subset_span ⟨Ideal.Quotient.mk ⊥ (X ⟨(), 0⟩), 1, 0, ?_, ?_, rfl⟩` and prove the remaining obligations. Conclude with `h1`. Use `Submodule.subset_span ⟨X ⟨(), 0⟩, ⟨fun _ => by simp, ?_⟩, rfl⟩` and prove the remaining obligations.

Introduce `m hm k`. Use `hX m hm k` as an intermediate fact. Simplify using `using this`. Use `cechC_one_subsingleton S (MRingOver S PtIdx ⧸ (⊥ : Ideal (MRingOver S PtIdx)))` as an intermediate fact. Conclude with `LinearMap.mem_ker.mpr (Subsingleton.elim _ _)`.

Use `Submodule.subset_span ⟨1, ⟨X ⟨(), 0⟩, hmon⟩, fun _ => 1, hX, ?_, rfl⟩` and prove the remaining obligations. Use `Submodule.subset_span ⟨1, ⟨fun _ => by simp, ?_⟩, map_one _⟩` and prove the remaining obligations. Introduce `m hm k`. Use `h1 m hm k` as an intermediate fact. Simplify using `using this`.

Rewrite using `[Fin.sum_univ_one, LocalizedModule.mk_mul_mk, one_mul, mul_one]`. Establish `hq : (Ideal.Quotient.mk ⊥ (X ⟨(), 0⟩) : MRingOver S PtIdx ⧸ (⊥ : Ideal (MRingOver S PtIdx))) = (⟨X ⟨(), 0⟩, hmon⟩ : KH.cellMon S I.1) • (1 : MRingOver S PtIdx ⧸ (⊥ : Ideal (MRingOver S PtIdx)))`. Rewrite using `[Submonoid.smul_def, Algebra.smul_def, mul_one]`. Both sides reduce to the same expression. Rewrite using `[hq, LocalizedModule.mk_cancel]`.

Conclude with `OreLocalization.one_def.symm`. Use `cechC_one_subsingleton S (MRingOver S PtIdx ⧸ (⊥ : Ideal (MRingOver S PtIdx)))` as an intermediate fact. Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ a`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective _ b`.

Rewrite using `[Subsingleton.elim a b]`.
-/
theorem ampleV_point (S : Type) [CommRing S] :
    KH.AmpleV S (⊥ : Ideal (MRingOver S PtIdx)) (fun _ => 1) := by
  classical
  have hX : IsMultiHomog (ι := PtIdx) (X ⟨(), 0⟩ : MRingOver S PtIdx) (fun _ => 1) := by
    intro m hm k
    rw [mem_support_iff, coeff_X] at hm
    split_ifs at hm with h
    · subst h
      simp [Finsupp.single_apply]
    · exact absurd rfl hm
  have h1 : IsMultiHomog (ι := PtIdx) (1 : MRingOver S PtIdx) (fun _ => 0) := by
    intro m hm k
    rw [mem_support_iff, coeff_one] at hm
    split_ifs at hm with h
    · subst h
      simp
    · exact absurd rfl hm
  refine ⟨1, le_rfl, ?_, fun e => ⟨0, fun c _ => ?_⟩⟩
  · intro I
    obtain ⟨i, hi⟩ := I.2.1 ()
    have hi0 : i = 0 := Subsingleton.elim (α := Fin 1) i 0
    subst hi0
    have hmon : (X ⟨(), 0⟩ : MRingOver S PtIdx) ∈ KH.cellMon S I.1 :=
      Submonoid.subset_closure ⟨(), 0, hi, rfl⟩
    refine ⟨1, fun _ _ => LocalizedModule.mk (Ideal.Quotient.mk ⊥ (X ⟨(), 0⟩)) 1,
      fun _ => LocalizedModule.mk 1 ⟨X ⟨(), 0⟩, hmon⟩, fun _ => ⟨?_, ?_⟩, fun _ => ?_, ?_⟩
    · intro J _
      refine Submodule.subset_span ⟨Ideal.Quotient.mk ⊥ (X ⟨(), 0⟩), 1, 0, ?_, ?_, rfl⟩
      · exact h1
      · refine Submodule.subset_span ⟨X ⟨(), 0⟩, ⟨fun _ => by simp, ?_⟩, rfl⟩
        intro m hm k
        have := hX m hm k
        simpa using this
    · have := cechC_one_subsingleton S (MRingOver S PtIdx ⧸ (⊥ : Ideal (MRingOver S PtIdx)))
      exact LinearMap.mem_ker.mpr (Subsingleton.elim _ _)
    · refine Submodule.subset_span ⟨1, ⟨X ⟨(), 0⟩, hmon⟩, fun _ => 1, hX, ?_, rfl⟩
      refine Submodule.subset_span ⟨1, ⟨fun _ => by simp, ?_⟩, map_one _⟩
      intro m hm k
      have := h1 m hm k
      simpa using this
    · rw [Fin.sum_univ_one, LocalizedModule.mk_mul_mk, one_mul, mul_one]
      have hq : (Ideal.Quotient.mk ⊥ (X ⟨(), 0⟩) : MRingOver S PtIdx ⧸ (⊥ : Ideal (MRingOver S PtIdx))) =
          (⟨X ⟨(), 0⟩, hmon⟩ : KH.cellMon S I.1) • (1 : MRingOver S PtIdx ⧸ (⊥ : Ideal (MRingOver S PtIdx))) := by
        rw [Submonoid.smul_def, Algebra.smul_def, mul_one]
        rfl
      rw [hq, LocalizedModule.mk_cancel]
      exact OreLocalization.one_def.symm
  · have := cechC_one_subsingleton S (MRingOver S PtIdx ⧸ (⊥ : Ideal (MRingOver S PtIdx)))
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Subsingleton.elim a b]

/- English proof (translation)
Establish `hP : mCoordIdeal (ι` using `PtIdx) unitPoint = ⊥ := mCoordIdeal_unitPoint`. Use `⟨unitPoint_isArithVar, unitPoint_birational, ?_, ⟨2, by norm_num, ?_⟩, fun ℓ _ => ?_⟩` and prove the remaining obligations. Rewrite using `[KH.genIdeal, hP, Ideal.map_bot]`. Conclude with `ampleV_point ℚ`. Establish `h2 : (2 • (fun _ => (1 : ℤ)) - fun _ => 1 : Unit → ℤ) = fun _ => 1` using `by funext; simp`.

Rewrite using `[h2, KH.genIdeal, hP, Ideal.map_bot]`. Conclude with `ampleV_point ℚ`. Rewrite using `[fibreIdeal, hP, Ideal.map_bot]`. Conclude with `ampleV_point (ZMod ℓ)`.
-/
theorem LiftModel.hyps_inhabited :
    IsArithVar (mCoordIdeal (ι := PtIdx) unitPoint) (0 + 1) ∧ Birational (ι := PtIdx) unitPoint ∧
      KH.AmpleV ℚ (KH.genIdeal (ι := PtIdx) unitPoint) (fun _ => 1) ∧
      (∃ c : ℕ, 1 ≤ c ∧ KH.AmpleV ℚ (KH.genIdeal (ι := PtIdx) unitPoint) (c • (fun _ => (1 : ℤ)) - fun _ => 1)) ∧
      ∀ ℓ : ℕ, ℓ.Prime → KH.AmpleV (ZMod ℓ) (fibreIdeal (ι := PtIdx) ℓ unitPoint) (fun _ => 1) := by
  have hP : mCoordIdeal (ι := PtIdx) unitPoint = ⊥ := mCoordIdeal_unitPoint
  refine ⟨unitPoint_isArithVar, unitPoint_birational, ?_, ⟨2, by norm_num, ?_⟩, fun ℓ _ => ?_⟩
  · rw [KH.genIdeal, hP, Ideal.map_bot]
    exact ampleV_point ℚ
  · have h2 : (2 • (fun _ => (1 : ℤ)) - fun _ => 1 : Unit → ℤ) = fun _ => 1 := by
      funext; simp
    rw [h2, KH.genIdeal, hP, Ideal.map_bot]
    exact ampleV_point ℚ
  · rw [fibreIdeal, hP, Ideal.map_bot]
    exact ampleV_point (ZMod ℓ)

end Inhabitant

end GroundTheory.Heights₂.Heights.HilbertSamuel
