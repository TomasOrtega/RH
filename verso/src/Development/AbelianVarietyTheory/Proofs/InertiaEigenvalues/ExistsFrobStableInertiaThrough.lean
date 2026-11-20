import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.DPotCrisStableAndExistsPotentiallyCrystallineDat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentat
open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

noncomputable section

namespace GlobalTheory

section InertialCharacters

variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

/- English proof (translation)
Simplify using `[PotCrysData.Eig, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]`.
-/
theorem inertialEig_mem_iff (ρ : Representation LL G V) (I : Subgroup G) (a : I →* LLˣ)
    (w : V ⊗[Qp] B) :
    w ∈ PC.Eig ρ I a ↔ w ∈ PC.Dpcris ρ ∧ ∀ g : I, actVB PC.PD ρ (g : G) w = ((a g : LLˣ) : LL) • w := by
  simp [PotCrysData.Eig, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [actVB]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem actVB_one_apply (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    actVB PC.PD ρ 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add a b ha hb => simp only [map_add, ha, hb]

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a0 T' ha0 ih`. Establish `hba0 : b ≠ a0` using `fun h => hb (h ▸ Finset.mem_insert_self _ _)`. Establish `hbT : b ∉ T'` using `fun h => hb (Finset.mem_insert_of_mem h)`.

Establish `ih'` using `ih hbT`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : ∃ g : I, b g ≠ a0 g := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hba0 (MonoidHom.ext h)`.

Establish `hne : ((b g : LLˣ) : LL) - ((a0 g : LLˣ) : LL) ≠ 0`. Introduce `h`. Conclude with `hg (Units.ext (sub_eq_zero.mp h))`. Use `set f : V ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B := actVB PC.PD ρ (g : G) - ((a0 g : LLˣ) : LL) • LinearMap.id with hf`. Establish `hfE : ∀ (a : I →* LLˣ) w, w ∈ PC.Eig ρ I a → f w = (((a g : LLˣ) : LL) - ((a0 g : LLˣ) : LL)) • w`.

Introduce `a w hw`. Rewrite `hw` using `[inertialEig_mem_iff]`. Simplify using `[hf, hw.2 g, sub_smul]`. Establish `hmapT : ∀ z ∈ (⨆ a ∈ T', PC.Eig ρ I a), f z ∈ (⨆ a ∈ T', PC.Eig ρ I a)`. Introduce `z hz`.

Establish `: (⨆ a ∈ T', PC.Eig ρ I a) ≤ (⨆ a ∈ T', PC.Eig ρ I a).comap f`. Use `iSup₂_le fun a ha w hw => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_comap, hfE a w hw]`. Conclude with `Submodule.smul_mem _ _ ((le_iSup₂ (f := fun a (_ : a ∈ T') => PC.Eig ρ I a) a ha) hw)`. Conclude with `this hz`.

Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Rewrite `hx` using `[Submodule.mem_inf]`. Take `⟨hxb, hxs⟩` from `hx`. Rewrite `hxs` using `[Finset.iSup_insert, Submodule.mem_sup]`.

Take `⟨y, hy, z, hz, rfl⟩` from `hxs`. Establish `hfx : f (y + z) = (((b g : LLˣ) : LL) - ((a0 g : LLˣ) : LL)) • (y + z)` using `hfE b _ hxb`. Establish `hfy : f y = 0` using `by rw [hfE a0 y hy, sub_self, zero_smul]`. Establish `hmem : (((b g : LLˣ) : LL) - ((a0 g : LLˣ) : LL)) • (y + z) ∈ PC.Eig ρ I b ⊓ (⨆ a ∈ T', PC.Eig ρ I a)`. Use `⟨Submodule.smul_mem _ _ hxb, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hfx, map_add, hfy, zero_add]`. Conclude with `hmapT z hz`. Rewrite `hmem` using `[ih']`. Rewrite `hmem`, the goal using `[Submodule.mem_bot]`. Conclude with `(smul_eq_zero.mp hmem).resolve_left hne`.
-/
theorem inertialEig_inf_iSup_eq_bot (ρ : Representation LL G V) (I : Subgroup G) (b : I →* LLˣ)
    (T : Finset (I →* LLˣ)) (hb : b ∉ T) :
    PC.Eig ρ I b ⊓ (⨆ a ∈ T, PC.Eig ρ I a) = ⊥ := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a0 T' ha0 ih =>
    have hba0 : b ≠ a0 := fun h => hb (h ▸ Finset.mem_insert_self _ _)
    have hbT : b ∉ T' := fun h => hb (Finset.mem_insert_of_mem h)
    have ih' := ih hbT
    obtain ⟨g, hg⟩ : ∃ g : I, b g ≠ a0 g := by
      by_contra h
      push_neg at h
      exact hba0 (MonoidHom.ext h)
    have hne : ((b g : LLˣ) : LL) - ((a0 g : LLˣ) : LL) ≠ 0 := by
      intro h
      exact hg (Units.ext (sub_eq_zero.mp h))
    set f : V ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B :=
      actVB PC.PD ρ (g : G) - ((a0 g : LLˣ) : LL) • LinearMap.id with hf
    have hfE : ∀ (a : I →* LLˣ) w, w ∈ PC.Eig ρ I a →
        f w = (((a g : LLˣ) : LL) - ((a0 g : LLˣ) : LL)) • w := by
      intro a w hw
      rw [inertialEig_mem_iff] at hw
      simp [hf, hw.2 g, sub_smul]
    have hmapT : ∀ z ∈ (⨆ a ∈ T', PC.Eig ρ I a), f z ∈ (⨆ a ∈ T', PC.Eig ρ I a) := by
      intro z hz
      have : (⨆ a ∈ T', PC.Eig ρ I a) ≤ (⨆ a ∈ T', PC.Eig ρ I a).comap f := by
        refine iSup₂_le fun a ha w hw => ?_
        rw [Submodule.mem_comap, hfE a w hw]
        exact Submodule.smul_mem _ _ ((le_iSup₂ (f := fun a (_ : a ∈ T') => PC.Eig ρ I a) a ha) hw)
      exact this hz
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxb, hxs⟩ := hx
    rw [Finset.iSup_insert, Submodule.mem_sup] at hxs
    obtain ⟨y, hy, z, hz, rfl⟩ := hxs
    have hfx : f (y + z) = (((b g : LLˣ) : LL) - ((a0 g : LLˣ) : LL)) • (y + z) := hfE b _ hxb
    have hfy : f y = 0 := by rw [hfE a0 y hy, sub_self, zero_smul]
    have hmem : (((b g : LLˣ) : LL) - ((a0 g : LLˣ) : LL)) • (y + z) ∈
        PC.Eig ρ I b ⊓ (⨆ a ∈ T', PC.Eig ρ I a) := by
      refine ⟨Submodule.smul_mem _ _ hxb, ?_⟩
      rw [← hfx, map_add, hfy, zero_add]
      exact hmapT z hz
    rw [ih'] at hmem
    rw [Submodule.mem_bot] at hmem ⊢
    exact (smul_eq_zero.mp hmem).resolve_left hne

/- English proof (translation)
Introduce `c`. Take `⟨c', hc'⟩` from `PC.stableK₀' F c`. Establish `hg'` using `hg c'`. Establish `hFinv : PC.PD.actB F⁻¹ (algebraMap K₀' B c') = algebraMap K₀' B c`. Rewrite using `[← hc', ← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply]`.

Rewrite using `[map_mul, map_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hc', hg', hFinv]`.
-/
theorem conj_mem_Iner (F : G) (g : G) (hg : g ∈ PC.Iner) : F⁻¹ * g * F ∈ PC.Iner := by
  intro c
  obtain ⟨c', hc'⟩ := PC.stableK₀' F c
  have hg' := hg c'
  have hFinv : PC.PD.actB F⁻¹ (algebraMap K₀' B c') = algebraMap K₀' B c := by
    rw [← hc', ← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply]
  rw [map_mul, map_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hc', hg', hFinv]

def inerConj (F : G) : PC.Iner →* PC.Iner where
  toFun g := ⟨F⁻¹ * (g : G) * F, conj_mem_Iner PC F g g.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_assoc]

/- English proof (translation)
Set `Sig : Finset (PC.Iner →* LLˣ)` to `insert 1 (S.filter (fun a => ∃ x, PC.Eig (ρ x) PC.Iner a ≠ ⊥))`. Establish `hSigS : Sig ⊆ S`. Introduce `a ha`. Break down `Finset.mem_insert.mp ha with rfl | ha` into its components or cases. Conclude with `h1`.

Conclude with `(Finset.mem_filter.mp ha).1`. Use `⟨Sig, hSigS, Finset.mem_insert_self _ _, ?_, ?_⟩` and prove the remaining obligations. Introduce `a ha`. Break down `Finset.mem_insert.mp ha with rfl | ha` into its components or cases. Conclude with `⟨1, Finset.mem_insert_self _ _, fun g h _ => by simp⟩`.

Take `⟨haS, x, hx⟩` from `Finset.mem_filter.mp ha`. Set `b : PC.Iner →* LLˣ` to `a.comp (inerConj PC F)`. Use `⟨b, ?_, ?_⟩` and prove the remaining obligations. Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hx`. Rewrite `hv` using `[inertialEig_mem_iff]`.

Use `set u := actVB PC.PD (ρ x) F v with hu`. Establish `huD : u ∈ PC.Dpcris (ρ x)` using `pc_Dpcris_stable PC (ρ x) F hv.1`. Establish `hu0 : u ≠ 0`. Introduce `h`. Apply `hv0` to reduce the goal to its premises.

Establish `: actVB PC.PD (ρ x) F⁻¹ u = v`. Rewrite using `[hu, ← pc_actVB_mul, inv_mul_cancel, actVB_one_apply]`. Rewrite using `[← this, h, map_zero]`. Establish `huE : u ∈ PC.Eig (ρ x) PC.Iner b`. Rewrite using `[inertialEig_mem_iff]`.

Use `⟨huD, fun g => ?_⟩` and prove the remaining obligations. Establish `e : (g : G) * F = F * (F⁻¹ * (g : G) * F)` using `by group`. Establish `hc` using `hv.2 (inerConj PC F g)`. Rewrite using `[hu, ← pc_actVB_mul, e, pc_actVB_mul]`. Express the relevant statement in the definitionally equal form `actVB PC.PD (ρ x) F (actVB PC.PD (ρ x) ((inerConj PC F g : PC.Iner) : G) v) = _`.

Rewrite using `[hc, map_smul]`. Both sides reduce to the same expression. Establish `hbS : b ∈ S`. Assume the negation of the conclusion as `hbS`. Establish `hbot` using `inertialEig_inf_iSup_eq_bot PC (ρ x) PC.Iner b S hbS`.

Apply `hu0` to reduce the goal to its premises. Establish `: u ∈ PC.Eig (ρ x) PC.Iner b ⊓ (⨆ a ∈ S, PC.Eig (ρ x) PC.Iner a)`. Use `⟨huE, ?_⟩` and prove the remaining obligations. Rewrite using `[← (hS x).2.2]`. Conclude with `huD`.

Rewrite `this` using `[hbot]`. Conclude with `(Submodule.mem_bot LL).mp this`. Apply `Finset.mem_insert_of_mem` to reduce the goal to its premises. Use `Finset.mem_filter.mpr ⟨hbS, x, ?_⟩` and prove the remaining obligations. Introduce `h`.

Apply `hu0` to reduce the goal to its premises. Use `huE` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `(Submodule.mem_bot LL).mp this`. Introduce `g h hh`.

Express the relevant statement in the definitionally equal form `a (inerConj PC F g) = a h`. Use `congr 1`. Use `ext`. Conclude with `hh.symm`. Introduce `x`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a ha g hg`. Break down `Finset.mem_insert.mp ha with rfl | ha` into its components or cases. Both sides reduce to the same expression. Conclude with `(hS x).1 a (Finset.mem_filter.mp ha).1 g hg`.

Introduce `a ha`. Break down `Finset.mem_insert.mp ha with rfl | ha` into its components or cases. Simplify using the standard rewrite rules. Conclude with `(hS x).2.1 a (Finset.mem_filter.mp ha).1`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[(hS x).2.2]`. Use `iSup₂_le fun a ha => ?_` and prove the remaining obligations. Distinguish the cases in `h0 : PC.Eig (ρ x) PC.Iner a = ⊥`. Rewrite using `[h0]`. Conclude with `bot_le`.

Establish `haSig : a ∈ Sig` using `Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨ha, x, h0⟩)`. Conclude with `le_iSup₂ (f := fun a (_ : a ∈ Sig) => PC.Eig (ρ x) PC.Iner a) a haSig`. Conclude with `iSup₂_le fun a _ => inf_le_left`.
-/
theorem exists_frobStable_inertiaThrough {ι : Type} (ρ : ι → Representation LL G V) (F : G)
    (S : Finset (PC.Iner →* LLˣ)) (h1 : 1 ∈ S) (hS : ∀ x, PC.InertiaThrough (ρ x) S) :
    ∃ Sig : Finset (PC.Iner →* LLˣ), Sig ⊆ S ∧ 1 ∈ Sig ∧ FrobStable PC.Iner F Sig ∧
      ∀ x, PC.InertiaThrough (ρ x) Sig := by
  classical
  let Sig : Finset (PC.Iner →* LLˣ) :=
    insert 1 (S.filter (fun a => ∃ x, PC.Eig (ρ x) PC.Iner a ≠ ⊥))
  have hSigS : Sig ⊆ S := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact h1
    · exact (Finset.mem_filter.mp ha).1
  refine ⟨Sig, hSigS, Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨1, Finset.mem_insert_self _ _, fun g h _ => by simp⟩
    obtain ⟨haS, x, hx⟩ := Finset.mem_filter.mp ha
    let b : PC.Iner →* LLˣ := a.comp (inerConj PC F)
    refine ⟨b, ?_, ?_⟩
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hx
      rw [inertialEig_mem_iff] at hv
      set u := actVB PC.PD (ρ x) F v with hu
      have huD : u ∈ PC.Dpcris (ρ x) := pc_Dpcris_stable PC (ρ x) F hv.1
      have hu0 : u ≠ 0 := by
        intro h
        apply hv0
        have : actVB PC.PD (ρ x) F⁻¹ u = v := by
          rw [hu, ← pc_actVB_mul, inv_mul_cancel, actVB_one_apply]
        rw [← this, h, map_zero]
      have huE : u ∈ PC.Eig (ρ x) PC.Iner b := by
        rw [inertialEig_mem_iff]
        refine ⟨huD, fun g => ?_⟩
        have e : (g : G) * F = F * (F⁻¹ * (g : G) * F) := by group
        have hc := hv.2 (inerConj PC F g)
        rw [hu, ← pc_actVB_mul, e, pc_actVB_mul]
        change actVB PC.PD (ρ x) F (actVB PC.PD (ρ x) ((inerConj PC F g : PC.Iner) : G) v) = _
        rw [hc, map_smul]
        rfl
      have hbS : b ∈ S := by
        by_contra hbS
        have hbot := inertialEig_inf_iSup_eq_bot PC (ρ x) PC.Iner b S hbS
        apply hu0
        have : u ∈ PC.Eig (ρ x) PC.Iner b ⊓ (⨆ a ∈ S, PC.Eig (ρ x) PC.Iner a) := by
          refine ⟨huE, ?_⟩
          rw [← (hS x).2.2]
          exact huD
        rw [hbot] at this
        exact (Submodule.mem_bot LL).mp this
      apply Finset.mem_insert_of_mem
      refine Finset.mem_filter.mpr ⟨hbS, x, ?_⟩
      intro h
      apply hu0
      have := huE
      rw [h] at this
      exact (Submodule.mem_bot LL).mp this
    · intro g h hh
      change a (inerConj PC F g) = a h
      congr 1
      ext
      exact hh.symm
  · intro x
    refine ⟨?_, ?_, ?_⟩
    · intro a ha g hg
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rfl
      · exact (hS x).1 a (Finset.mem_filter.mp ha).1 g hg
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · simp
      · exact (hS x).2.1 a (Finset.mem_filter.mp ha).1
    · apply le_antisymm
      · rw [(hS x).2.2]
        refine iSup₂_le fun a ha => ?_
        by_cases h0 : PC.Eig (ρ x) PC.Iner a = ⊥
        · rw [h0]; exact bot_le
        · have haSig : a ∈ Sig := Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨ha, x, h0⟩)
          exact le_iSup₂ (f := fun a (_ : a ∈ Sig) => PC.Eig (ρ x) PC.Iner a) a haSig
      · exact iSup₂_le fun a _ => inf_le_left

end InertialCharacters

/- English proof (translation)
Use `intros`. Apply the tactic sequence `apply exists_frobStable_inertiaThrough <;> assumption`.
-/
theorem frobStable_inertial_subset : ∀ {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K] [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {ι : Type} (ρ : ι → Representation LL G V) (F : G) (S : Finset (PC.Iner →* LLˣ)),
    1 ∈ S → (∀ x, PC.InertiaThrough (ρ x) S) →
    ∃ Sig : Finset (PC.Iner →* LLˣ), Sig ⊆ S ∧ 1 ∈ Sig ∧ FrobStable PC.Iner F Sig ∧
      ∀ x, PC.InertiaThrough (ρ x) Sig := by
  intros
  apply exists_frobStable_inertiaThrough <;> assumption

end GlobalTheory
