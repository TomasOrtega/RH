import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeTestPointMembershipStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeImageBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeSecondGoodnessStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeAnnihilatorLatticeHoldsStatement
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨1, R.one_mem, e, h, (one_smul _ _).symm⟩`.
-/
theorem mem_span {E : Type} [AddCommGroup E] [Module Ω E] (R : Subalgebra o Ω) {S : Set E} {e : E}
    (h : e ∈ S) : e ∈ spanOver R S :=
  AddSubgroup.subset_closure ⟨1, R.one_mem, e, h, (one_smul _ _).symm⟩

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show algebraMap Ω C (w * v i) = algebraMap Ω C w * algebraMap Ω C (v i)`. Rewrite using `[map_mul]`.
-/
theorem bc_smul {C : Type} [Field C] [Algebra Ω C] {ι : Type} (w : Ω) (v : ι → Ω) :
    bcMap Ω C ι (w • v) = algebraMap Ω C w • bcMap Ω C ι v := by
  funext i
  show algebraMap Ω C (w * v i) = algebraMap Ω C w * algebraMap Ω C (v i)
  rw [map_mul]

/- English proof (translation)
Take `⟨c, hc, e⟩` from `hw`. Use `⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_one, e, mul_smul]`. Conclude with `hL.1 c hc _ hv`.
-/
theorem pow_one_smul_mem {E : Type} [AddCommGroup E] [Module Ω E] {R : Subalgebra o Ω} {N : ℕ}
    {L : AddSubgroup E} (hL : LocFree R N L) {p : ℕ} {w : Ω} (hw : ∃ c ∈ R, (p : Ω) = c * w) {v : E}
    (hv : w • v ∈ L) : ∃ m : ℕ, (p : Ω) ^ m • v ∈ L := by
  obtain ⟨c, hc, e⟩ := hw
  refine ⟨1, ?_⟩
  rw [pow_one, e, mul_smul]
  exact hL.1 c hc _ hv

end GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence

open GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence in

/- English proof (translation)
Introduce `o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hb hp hN hF hI φ hT hG hG2 τ`. Establish `hle` using `GlobalTheory.T.hodge_annihilator_lattice_holds D R p w χ hc hb hp hN hF hI φ hT hG`. Establish `hbc1` using `GlobalTheory.T.lattice_image_base_change D R p w χ hc hb hG hle`. Take `⟨hf2, hbc2⟩` from `GlobalTheory.T.lattice_second_goodness D R p w χ hc hb hG hG2 hle`. Establish `hp0` using `hc.1`.

Establish `hw` using `hc.2.2.1`. Take `⟨flie, -, fom, -⟩` from `hb.free τ`. Take `⟨i1, i2, i3, i4⟩` from `hb.incl τ`. Use `⟨le_antisymm (fun v hv => ?_) (fun v hv => ?_), le_antisymm (fun v hv => ?_) (fun v hv => ?_)⟩` and prove the remaining obligations. Use `GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI _ _ fom v (pow_one_smul_mem fom hw ?_) ?_` and prove the remaining obligations.

Take `⟨⟨b, c⟩, ⟨h, -⟩, rfl⟩` from `hv`. Conclude with `i3 (((hb.del τ).2.1 c).1 ⟨b, h⟩)`. Introduce `C _ _ _ _ RC hRC`. Establish `h : bcMap Ω C _ v ∈ (D.bc RC).imH RC p τ (fun a => algebraMap Ω C (χ τ a))`. Rewrite using `[hbc1 C RC hRC.2.2.2 τ]`.

Conclude with `mem_span RC ⟨v, hv, rfl⟩`. Establish `e` using `(hT C RC hRC).im τ`. Conclude with `e.le h`. Use `GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI _ _ (hG2.im τ) v (pow_one_smul_mem (hG2.im τ) hw ?_) ?_` and prove the remaining obligations. Conclude with `⟨(0, w • v), ⟨((hb.del τ).2.2.1 _).2 (i4 hv), zero_mem _, trivial⟩, rfl⟩`.

Introduce `C _ _ _ _ RC hRC`. Rewrite using `[← hbc1 C RC hRC.2.2.2 τ]`. Establish `e` using `(hT C RC hRC).im τ`. Conclude with `e.ge (mem_span RC ⟨v, hv, rfl⟩)`. Use `show w • v ∈ D.lie τ`.

Use `GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI _ _ flie _ (pow_one_smul_mem flie hw ?_) ?_` and prove the remaining obligations. Take `⟨⟨a, b⟩, ⟨h, -⟩, rfl⟩` from `hv`. Conclude with `i2 (((hb.gam τ).1 a).1 ⟨b, h⟩)`. Introduce `C _ _ _ _ RC hRC`. Establish `h : bcMap Ω C _ v ∈ (D.bc RC).kerH RC p τ (fun a => algebraMap Ω C (χ τ a))`.

Rewrite using `[((hbc2 C RC hRC.2.2.2).2 τ).1]`. Conclude with `mem_span RC ⟨v, hv, rfl⟩`. Establish `e` using `(hT C RC hRC).ker τ`. Rewrite using `[bc_smul]`. Conclude with `e.le h`.

Establish `hv' : w • v ∈ D.lie τ` using `hv`. Use `GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI _ _ (hf2 τ).1 v (pow_one_smul_mem (hf2 τ).1 hw ?_) ?_` and prove the remaining obligations. Conclude with `⟨(w • v, 0), ⟨((hb.gam τ).2.2 _).2 (i1 hv'), trivial, zero_mem _⟩, rfl⟩`. Introduce `C _ _ _ _ RC hRC`. Rewrite using `[← ((hbc2 C RC hRC.2.2.2).2 τ).1]`.

Establish `e` using `(hT C RC hRC).ker τ`. Use `e.ge ?_` and prove the remaining obligations. Use `show algebraMap Ω C w • bcMap Ω C _ v ∈ (D.bc RC).lie τ`. Rewrite using `[← bc_smul]`. Conclude with `mem_span RC ⟨_, hv', rfl⟩`.
-/
theorem GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence.main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → D.Good₂ R p χ → ∀ τ, D.imH R p τ (χ τ) = D.om τ ∧ D.kerH R p τ (χ τ) = divLat w (D.lie τ) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hb hp hN hF hI φ hT hG hG2 τ
  have hle := GlobalTheory.T.hodge_annihilator_lattice_holds D R p w χ hc hb hp hN hF hI φ hT hG
  have hbc1 := GlobalTheory.T.lattice_image_base_change D R p w χ hc hb hG hle
  obtain ⟨hf2, hbc2⟩ := GlobalTheory.T.lattice_second_goodness D R p w χ hc hb hG hG2 hle
  have hp0 := hc.1
  have hw := hc.2.2.1
  obtain ⟨flie, -, fom, -⟩ := hb.free τ
  obtain ⟨i1, i2, i3, i4⟩ := hb.incl τ
  refine ⟨le_antisymm (fun v hv => ?_) (fun v hv => ?_), le_antisymm (fun v hv => ?_) (fun v hv => ?_)⟩
  · refine GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI _ _ fom v (pow_one_smul_mem fom hw ?_) ?_
    · obtain ⟨⟨b, c⟩, ⟨h, -⟩, rfl⟩ := hv
      exact i3 (((hb.del τ).2.1 c).1 ⟨b, h⟩)
    · intro C _ _ _ _ RC hRC
      have h : bcMap Ω C _ v ∈ (D.bc RC).imH RC p τ (fun a => algebraMap Ω C (χ τ a)) := by
        rw [hbc1 C RC hRC.2.2.2 τ]
        exact mem_span RC ⟨v, hv, rfl⟩
      have e := (hT C RC hRC).im τ
      exact e.le h
  · refine GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI _ _ (hG2.im τ) v (pow_one_smul_mem (hG2.im τ) hw ?_) ?_
    · exact ⟨(0, w • v), ⟨((hb.del τ).2.2.1 _).2 (i4 hv), zero_mem _, trivial⟩, rfl⟩
    · intro C _ _ _ _ RC hRC
      rw [← hbc1 C RC hRC.2.2.2 τ]
      have e := (hT C RC hRC).im τ
      exact e.ge (mem_span RC ⟨v, hv, rfl⟩)
  · show w • v ∈ D.lie τ
    refine GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI _ _ flie _ (pow_one_smul_mem flie hw ?_) ?_
    · obtain ⟨⟨a, b⟩, ⟨h, -⟩, rfl⟩ := hv
      exact i2 (((hb.gam τ).1 a).1 ⟨b, h⟩)
    · intro C _ _ _ _ RC hRC
      have h : bcMap Ω C _ v ∈ (D.bc RC).kerH RC p τ (fun a => algebraMap Ω C (χ τ a)) := by
        rw [((hbc2 C RC hRC.2.2.2).2 τ).1]
        exact mem_span RC ⟨v, hv, rfl⟩
      have e := (hT C RC hRC).ker τ
      rw [bc_smul]
      exact e.le h
  · have hv' : w • v ∈ D.lie τ := hv
    refine GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI _ _ (hf2 τ).1 v (pow_one_smul_mem (hf2 τ).1 hw ?_) ?_
    · exact ⟨(w • v, 0), ⟨((hb.gam τ).2.2 _).2 (i1 hv'), trivial, zero_mem _⟩, rfl⟩
    · intro C _ _ _ _ RC hRC
      rw [← ((hbc2 C RC hRC.2.2.2).2 τ).1]
      have e := (hT C RC hRC).ker τ
      refine e.ge ?_
      show algebraMap Ω C w • bcMap Ω C _ v ∈ (D.bc RC).lie τ
      rw [← bc_smul]
      exact mem_span RC ⟨_, hv', rfl⟩
