import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqIntegralSpanGenerato
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DivisiblePontryaginAnnihilatorDuality

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SelfDualFirstProj

variable {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))

instance charZero_Fv : CharZero (Fv F v) :=
  (RingHom.charZero_iff (algebraMap F (Fv F v)).injective).1 inferInstance

/- English proof (translation)
The claim follows from `Valued.isOpen_valuationSubring _`.
-/
theorem isOpen_integers : IsOpen ((v.adicCompletionIntegers F : Set (Fv F v))) :=
  Valued.isOpen_valuationSubring _

/- English proof (translation)
Use `haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v`. Set `O` to `v.adicCompletionIntegers F`. Set `S : AddSubgroup (Fv F v)` to `(O.toSubring.toAddSubgroup).comap (AddMonoidHom.mulLeft c⁻¹)`. Set `H : AddSubgroup O` to `S.comap (O.toSubring.subtype.toAddMonoidHom)`. Establish `hS : IsOpen (S : Set (Fv F v))` using `(isOpen_integers v).preimage (continuous_const.mul continuous_id)`.

Establish `hH : IsOpen (H : Set O)` using `hS.preimage continuous_subtype_val`. Set `H' : OpenAddSubgroup O` to `⟨H, hH⟩`. Establish `: Finite (O ⧸ H)` using `AddSubgroup.instFiniteQuotientOfSeparatelyContinuousAddOfCompactSpace H'`. Establish `hne : H.index ≠ 0` using `AddSubgroup.index_ne_zero_of_finite`. Use `⟨H.index, Nat.pos_of_ne_zero hne, ?_⟩` and prove the remaining obligations.

Establish `hm` using `H.nsmul_index_mem (1 : O)`. Simplify `hm` using `[H, S]`.
-/
theorem exists_nat_mem (c : Fv F v) (hc : c ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ c⁻¹ * (n : Fv F v) ∈ v.adicCompletionIntegers F := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  let O := v.adicCompletionIntegers F
  let S : AddSubgroup (Fv F v) := (O.toSubring.toAddSubgroup).comap (AddMonoidHom.mulLeft c⁻¹)
  let H : AddSubgroup O := S.comap (O.toSubring.subtype.toAddMonoidHom)
  have hS : IsOpen (S : Set (Fv F v)) :=
    (isOpen_integers v).preimage (continuous_const.mul continuous_id)
  have hH : IsOpen (H : Set O) := hS.preimage continuous_subtype_val
  let H' : OpenAddSubgroup O := ⟨H, hH⟩
  have : Finite (O ⧸ H) := AddSubgroup.instFiniteQuotientOfSeparatelyContinuousAddOfCompactSpace H'
  have hne : H.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  refine ⟨H.index, Nat.pos_of_ne_zero hne, ?_⟩
  have hm := H.nsmul_index_mem (1 : O)
  simpa [H, S] using hm

/- English proof (translation)
Use `haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v`. Set `U : Set (Fv F v)` to `(v.adicCompletionIntegers F : Set (Fv F v))`. Establish `hUo : IsOpen U` using `isOpen_integers v`. Establish `hUc : IsCompact U` using `isCompact_iff_compactSpace.mpr inferInstance`. Establish `hc : (n : Fv F v) ≠ 0` using `by exact_mod_cast hn.ne'`.

Set `V : U → Set (Fv F v)` to `fun x => (fun y => (y - (x : Fv F v)) * (n : Fv F v)⁻¹) ⁻¹' U`. Establish `hVo : ∀ x, IsOpen (V x)` using `fun x => hUo.preimage ((continuous_id.sub continuous_const).mul continuous_const)`. Establish `hcov : U ⊆ ⋃ x, V x`. Introduce `y hy`. Use `Set.mem_iUnion.2 ⟨⟨y, hy⟩, ?_⟩` and prove the remaining obligations.

Use `show (y - y) * (n : Fv F v)⁻¹ ∈ U`. Rewrite using `[sub_self, zero_mul]`. Conclude with `(v.adicCompletionIntegers F).zero_mem`. Take `⟨t, ht⟩` from `hUc.elim_finite_subcover V hVo hcov`. Use `⟨(fun x : U => (x : Fv F v)) '' (t : Set U), (t.finite_toSet).image _, ?_⟩` and prove the remaining obligations.

Introduce `y hy`. Use `ht hy` as an intermediate fact. Simplify using `only [Set.mem_iUnion] at this`. Take `⟨x, hxt, hyx⟩` from `this`. Use `⟨x, ⟨x, hxt, rfl⟩, (y - (x : Fv F v)) * (n : Fv F v)⁻¹, hyx, ?_⟩` and prove the remaining obligations.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_finite_residues (n : ℕ) (hn : 0 < n) :
    ∃ R : Set (Fv F v), R.Finite ∧ ∀ y ∈ v.adicCompletionIntegers F,
      ∃ r ∈ R, ∃ u ∈ v.adicCompletionIntegers F, y = r + (n : Fv F v) * u := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  let U : Set (Fv F v) := (v.adicCompletionIntegers F : Set (Fv F v))
  have hUo : IsOpen U := isOpen_integers v
  have hUc : IsCompact U := isCompact_iff_compactSpace.mpr inferInstance
  have hc : (n : Fv F v) ≠ 0 := by exact_mod_cast hn.ne'
  let V : U → Set (Fv F v) := fun x => (fun y => (y - (x : Fv F v)) * (n : Fv F v)⁻¹) ⁻¹' U
  have hVo : ∀ x, IsOpen (V x) := fun x =>
    hUo.preimage ((continuous_id.sub continuous_const).mul continuous_const)
  have hcov : U ⊆ ⋃ x, V x := by
    intro y hy
    refine Set.mem_iUnion.2 ⟨⟨y, hy⟩, ?_⟩
    show (y - y) * (n : Fv F v)⁻¹ ∈ U
    rw [sub_self, zero_mul]
    exact (v.adicCompletionIntegers F).zero_mem
  obtain ⟨t, ht⟩ := hUc.elim_finite_subcover V hVo hcov
  refine ⟨(fun x : U => (x : Fv F v)) '' (t : Set U), (t.finite_toSet).image _, ?_⟩
  intro y hy
  have := ht hy
  simp only [Set.mem_iUnion] at this
  obtain ⟨x, hxt, hyx⟩ := this
  refine ⟨x, ⟨x, hxt, rfl⟩, (y - (x : Fv F v)) * (n : Fv F v)⁻¹, hyx, ?_⟩
  field_simp
  ring

/- English proof (translation)
Take `⟨R, hR, h⟩` from `exists_finite_residues v n hn`. Use `haveI := hR.to_subtype`. Use `⟨Set.range (fun f : κ → R => fun i => (f i : Fv F v)), Set.finite_range _, ?_⟩` and prove the remaining obligations. Introduce `t ht`. Use `choose r hr u hu hru using fun i => h (t i) (ht i)`.

Use `⟨fun i => r i, ⟨fun i => ⟨r i, hr i⟩, rfl⟩, u, hu, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]`. Conclude with `hru i`.
-/
theorem exists_finite_residues_pi {κ : Type} [Fintype κ] (n : ℕ) (hn : 0 < n) :
    ∃ R : Set (κ → Fv F v), R.Finite ∧ ∀ t : κ → Fv F v, (∀ i, t i ∈ v.adicCompletionIntegers F) →
      ∃ r ∈ R, ∃ u : κ → Fv F v, (∀ i, u i ∈ v.adicCompletionIntegers F) ∧ t = r + n • u := by
  obtain ⟨R, hR, h⟩ := exists_finite_residues v n hn
  haveI := hR.to_subtype
  refine ⟨Set.range (fun f : κ → R => fun i => (f i : Fv F v)), Set.finite_range _, ?_⟩
  intro t ht
  choose r hr u hu hru using fun i => h (t i) (ht i)
  refine ⟨fun i => r i, ⟨fun i => ⟨r i, hr i⟩, rfl⟩, u, hu, ?_⟩
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]
  exact hru i

/- English proof (translation)
Introduce `F _ _ v κ _ _ ψk Λ c hc hψ hself hbd η hη`. Set `O` to `v.adicCompletionIntegers F`. Establish `ψ1 : ∀ x : Fv F v, x ∈ O → ψk x = 1` using `fun x hx => by`. Simplify using `using (hψ x).2 hx 1 O.one_mem`. Establish `dotO : ∀ u w : κ → Fv F v, (∀ i, u i ∈ O) → (∀ i, w i ∈ O) → u ⬝ᵥ w ∈ O`.

Introduce `u w hu hw`. Conclude with `O.toSubring.sum_mem fun i _ => O.toSubring.mul_mem (hu i) (hw i)`. Set `L₀ : AddSubgroup (κ → Fv F v)` to `AddSubgroup.pi Set.univ (fun _ => O.toSubring.toAddSubgroup)`. Establish `hL₀ : ∀ x, x ∈ L₀ ↔ ∀ i, x i ∈ O` using `fun x => by`. Simplify using `[L₀, AddSubgroup.mem_pi]`.

Set `P : AddSubgroup (κ → Fv F v)` to `Λ.map (AddMonoidHom.fst _ _)`. Establish `hP : ∀ x, x ∈ P ↔ ∃ y, (x, y) ∈ Λ` using `fun x => by`. Simplify using `only [P, AddSubgroup.mem_map, AddMonoidHom.coe_fst]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨l, hl, rfl⟩`.

Conclude with `⟨l.2, hl⟩`. Introduce and unpack `⟨y, hy⟩`. Conclude with `⟨(x, y), hy, rfl⟩`. Establish `LB : ∀ u₁ u₂ : κ → Fv F v, (∀ i, u₁ i ∈ O) → (∀ i, u₂ i ∈ O) → (c • u₁, c • u₂) ∈ Λ`. Introduce `u₁ u₂ h₁ h₂`.

Use `(hself _).2 fun l hl => ψ1 _ ?_` and prove the remaining obligations. Establish `e1 : (c • u₁) ⬝ᵥ l.2 = u₁ ⬝ᵥ (c • l.2)` using `by rw [smul_dotProduct, dotProduct_smul]`. Establish `e2 : l.1 ⬝ᵥ (c • u₂) = (c • l.1) ⬝ᵥ u₂` using `by rw [smul_dotProduct, dotProduct_smul]`. Simplify using `only`. Rewrite using `[e1, e2]`.

Conclude with `O.toSubring.sub_mem (dotO _ _ h₁ fun i => (hbd l hl i).2) (dotO _ _ (fun i => (hbd l hl i).1) h₂)`. Establish `hsingle : ∀ i (t : Fv F v), t ∈ O → ∀ j, (Pi.single i t : κ → Fv F v) j ∈ O`. Introduce `i t ht j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality.

Simplify using `using ht`. Simplify using `[Pi.single_apply, h, O.zero_mem]`. Establish `hcη : ∀ i, c * η i ∈ O`. Introduce `i`. Use `(hψ _).1 fun t ht => ?_` and prove the remaining obligations.

Establish `hb : ((0 : κ → Fv F v), c • Pi.single i t) ∈ Λ`. Use `LB 0 (Pi.single i t) (fun _ => O.zero_mem) (hsingle i t ht)` as an intermediate fact. Simplify using `using this`. Use `hη _ hb` as an intermediate fact. Rewrite `this` using `[dotProduct_smul, dotProduct_single, smul_eq_mul, ← mul_assoc]`. Then use the resulting hypothesis.

Take `⟨N, hN, hNc⟩` from `GlobalTheory.SelfDualFirstProj.exists_nat_mem v c hc`. Establish `hNeq : ∀ z : Fv F v, (N : Fv F v) * z = (c⁻¹ * N) * (c * z)` using `fun z => by`. Clear the denominators using the available nonvanishing facts. Establish `bich : GlobalTheory.PlaceModel.IsBichar (fun x y : κ → Fv F v => ψk (x ⬝ᵥ y))` using `⟨fun a b y => by simp only [add_dotProduct, AddChar.map_add_eq_mul], fun a y z => by simp only [dotProduct_add, AddChar.map_add_eq_mul], fun y => by simp, fun a => by simp⟩`. Establish `hmem : η ∈ P`.

Use `GlobalTheory.DualTransfer.mem_of_double_annihilator (fun x y => ψk (x ⬝ᵥ y)) bich ⊤ ⊤ L₀ L₀ P le_top le_top le_top ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ N hN ?_ ?_ η trivial ?_ ?_` and prove the remaining obligations. Introduce `u hu y hy`. Conclude with `ψ1 _ (dotO _ _ ((hL₀ u).1 hu) ((hL₀ y).1 hy))`. Introduce `x _ h`. Use `(hL₀ x).2 fun i => (hψ _).1 fun t ht => ?_` and prove the remaining obligations.

Use `h (Pi.single i t) ((hL₀ _).2 (hsingle i t ht))` as an intermediate fact. Rewrite `this` using `[dotProduct_single]`. Then use the resulting hypothesis. Introduce `y _ h`. Use `(hL₀ y).2 fun i => (hψ _).1 fun t ht => ?_` and prove the remaining obligations. Use `h (Pi.single i t) ((hL₀ _).2 (hsingle i t ht))` as an intermediate fact.

Rewrite `this` using `[single_dotProduct, mul_comm]`. Then use the resulting hypothesis. Introduce `k hk x _`. Use `⟨((k : Fv F v)⁻¹) • x, trivial, ?_⟩` and prove the remaining obligations. Establish `hk0 : (k : Fv F v) ≠ 0` using `by exact_mod_cast hk.ne'`. Rewrite using `[← Nat.cast_smul_eq_nsmul (Fv F v), smul_smul, mul_inv_cancel₀ hk0, one_smul]`.

Introduce `k hk x _`. Use `⟨((k : Fv F v)⁻¹) • x, trivial, ?_⟩` and prove the remaining obligations. Establish `hk0 : (k : Fv F v) ≠ 0` using `by exact_mod_cast hk.ne'`. Rewrite using `[← Nat.cast_smul_eq_nsmul (Fv F v), smul_smul, mul_inv_cancel₀ hk0, one_smul]`. Introduce `k hk t t' h`.

Establish `hk0 : (k : Fv F v) ≠ 0` using `by exact_mod_cast hk.ne'`. Use function extensionality and compare the values at `i`. Use `congrFun h i` as an intermediate fact. Simplify using `only [Pi.smul_apply, nsmul_eq_mul] at this`. Conclude with `mul_left_cancel₀ hk0 this`.

Introduce `k hk`. Take `⟨R, hR, h⟩` from `GlobalTheory.SelfDualFirstProj.exists_finite_residues_pi (κ := κ) v k hk`. Conclude with `⟨R, hR, fun t ht => by`. Take `⟨r, hr, u, hu, e⟩` from `h t ((hL₀ t).1 ht)`. Conclude with `⟨r, hr, u, (hL₀ u).2 hu, e⟩⟩`.

Introduce `k hk`. Take `⟨R, hR, h⟩` from `GlobalTheory.SelfDualFirstProj.exists_finite_residues_pi (κ := κ) v k hk`. Conclude with `⟨R, hR, fun t ht => by`. Take `⟨r, hr, u, hu, e⟩` from `h t ((hL₀ t).1 ht)`. Conclude with `⟨r, hr, u, (hL₀ u).2 hu, e⟩⟩`.

Introduce `u hu`. Establish `hu'` using `(hL₀ u).1 hu`. Use `(hP _).2 ⟨c • (0 : κ → Fv F v), ?_⟩` and prove the remaining obligations. Use `LB ((c⁻¹ * N) • u) 0 (fun i => O.toSubring.mul_mem hNc (hu' i)) (fun _ => O.zero_mem)` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Introduce `u hu`. Take `⟨y, hy⟩` from `(hP u).1 hu`.

Use `(hL₀ _).2 fun i => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, nsmul_eq_mul]`. Rewrite using `[hNeq]`. Conclude with `O.toSubring.mul_mem hNc (hbd _ hy i).1`. Use `(hL₀ _).2 fun i => ?_` and prove the remaining obligations.

Simplify using `only [Pi.smul_apply, nsmul_eq_mul]`. Rewrite using `[hNeq]`. Conclude with `O.toSubring.mul_mem hNc (hcη i)`. Introduce `y _ h`. Use `hη y ((hself _).2 fun l hl => ?_)` and prove the remaining obligations.

Simplify using `only [zero_dotProduct, zero_sub, AddChar.map_neg_eq_inv]`. Rewrite using `[h l.1 ((hP _).2 ⟨l.2, hl⟩), inv_one]`. Take `⟨y, hy⟩` from `(hP η).1 hmem`. Conclude with `⟨y, hy⟩`.
-/
theorem exists_pair_of_annihilator : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ]
    [DecidableEq κ] (ψk : AddChar (Fv F v) ℂ) (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v), c ≠ 0 →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψk (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) →
    (∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψk (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1) →
    (∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F) →
    ∀ η : κ → Fv F v, (∀ b : κ → Fv F v, ((0 : κ → Fv F v), b) ∈ Λ → ψk (η ⬝ᵥ b) = 1) → ∃ y, (η, y) ∈ Λ := by
  intro F _ _ v κ _ _ ψk Λ c hc hψ hself hbd η hη
  let O := v.adicCompletionIntegers F
  have ψ1 : ∀ x : Fv F v, x ∈ O → ψk x = 1 := fun x hx => by
    simpa using (hψ x).2 hx 1 O.one_mem
  have dotO : ∀ u w : κ → Fv F v, (∀ i, u i ∈ O) → (∀ i, w i ∈ O) → u ⬝ᵥ w ∈ O := by
    intro u w hu hw
    exact O.toSubring.sum_mem fun i _ => O.toSubring.mul_mem (hu i) (hw i)
  let L₀ : AddSubgroup (κ → Fv F v) := AddSubgroup.pi Set.univ (fun _ => O.toSubring.toAddSubgroup)
  have hL₀ : ∀ x, x ∈ L₀ ↔ ∀ i, x i ∈ O := fun x => by
    simp [L₀, AddSubgroup.mem_pi]
  let P : AddSubgroup (κ → Fv F v) := Λ.map (AddMonoidHom.fst _ _)
  have hP : ∀ x, x ∈ P ↔ ∃ y, (x, y) ∈ Λ := fun x => by
    simp only [P, AddSubgroup.mem_map, AddMonoidHom.coe_fst]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact ⟨l.2, hl⟩
    · rintro ⟨y, hy⟩; exact ⟨(x, y), hy, rfl⟩

  have LB : ∀ u₁ u₂ : κ → Fv F v, (∀ i, u₁ i ∈ O) → (∀ i, u₂ i ∈ O) → (c • u₁, c • u₂) ∈ Λ := by
    intro u₁ u₂ h₁ h₂
    refine (hself _).2 fun l hl => ψ1 _ ?_
    have e1 : (c • u₁) ⬝ᵥ l.2 = u₁ ⬝ᵥ (c • l.2) := by rw [smul_dotProduct, dotProduct_smul]
    have e2 : l.1 ⬝ᵥ (c • u₂) = (c • l.1) ⬝ᵥ u₂ := by rw [smul_dotProduct, dotProduct_smul]
    simp only
    rw [e1, e2]
    exact O.toSubring.sub_mem (dotO _ _ h₁ fun i => (hbd l hl i).2) (dotO _ _ (fun i => (hbd l hl i).1) h₂)
  have hsingle : ∀ i (t : Fv F v), t ∈ O → ∀ j, (Pi.single i t : κ → Fv F v) j ∈ O := by
    intro i t ht j
    by_cases h : j = i
    · subst h; simpa using ht
    · simp [Pi.single_apply, h, O.zero_mem]

  have hcη : ∀ i, c * η i ∈ O := by
    intro i
    refine (hψ _).1 fun t ht => ?_
    have hb : ((0 : κ → Fv F v), c • Pi.single i t) ∈ Λ := by
      have := LB 0 (Pi.single i t) (fun _ => O.zero_mem) (hsingle i t ht)
      simpa using this
    have := hη _ hb
    rwa [dotProduct_smul, dotProduct_single, smul_eq_mul, ← mul_assoc] at this
  obtain ⟨N, hN, hNc⟩ := GlobalTheory.SelfDualFirstProj.exists_nat_mem v c hc
  have hNeq : ∀ z : Fv F v, (N : Fv F v) * z = (c⁻¹ * N) * (c * z) := fun z => by
    field_simp
  have bich : GlobalTheory.PlaceModel.IsBichar (fun x y : κ → Fv F v => ψk (x ⬝ᵥ y)) :=
    ⟨fun a b y => by simp only [add_dotProduct, AddChar.map_add_eq_mul],
     fun a y z => by simp only [dotProduct_add, AddChar.map_add_eq_mul],
     fun y => by simp, fun a => by simp⟩
  have hmem : η ∈ P := by
    refine GlobalTheory.DualTransfer.mem_of_double_annihilator (fun x y => ψk (x ⬝ᵥ y)) bich ⊤ ⊤ L₀ L₀ P
      le_top le_top le_top ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ N hN ?_ ?_ η trivial ?_ ?_
    · intro u hu y hy
      exact ψ1 _ (dotO _ _ ((hL₀ u).1 hu) ((hL₀ y).1 hy))
    · intro x _ h
      refine (hL₀ x).2 fun i => (hψ _).1 fun t ht => ?_
      have := h (Pi.single i t) ((hL₀ _).2 (hsingle i t ht))
      rwa [dotProduct_single] at this
    · intro y _ h
      refine (hL₀ y).2 fun i => (hψ _).1 fun t ht => ?_
      have := h (Pi.single i t) ((hL₀ _).2 (hsingle i t ht))
      rwa [single_dotProduct, mul_comm] at this
    · intro k hk x _
      refine ⟨((k : Fv F v)⁻¹) • x, trivial, ?_⟩
      have hk0 : (k : Fv F v) ≠ 0 := by exact_mod_cast hk.ne'
      rw [← Nat.cast_smul_eq_nsmul (Fv F v), smul_smul, mul_inv_cancel₀ hk0, one_smul]
    · intro k hk x _
      refine ⟨((k : Fv F v)⁻¹) • x, trivial, ?_⟩
      have hk0 : (k : Fv F v) ≠ 0 := by exact_mod_cast hk.ne'
      rw [← Nat.cast_smul_eq_nsmul (Fv F v), smul_smul, mul_inv_cancel₀ hk0, one_smul]
    · intro k hk t t' h
      have hk0 : (k : Fv F v) ≠ 0 := by exact_mod_cast hk.ne'
      funext i
      have := congrFun h i
      simp only [Pi.smul_apply, nsmul_eq_mul] at this
      exact mul_left_cancel₀ hk0 this
    · intro k hk
      obtain ⟨R, hR, h⟩ := GlobalTheory.SelfDualFirstProj.exists_finite_residues_pi (κ := κ) v k hk
      exact ⟨R, hR, fun t ht => by
        obtain ⟨r, hr, u, hu, e⟩ := h t ((hL₀ t).1 ht)
        exact ⟨r, hr, u, (hL₀ u).2 hu, e⟩⟩
    · intro k hk
      obtain ⟨R, hR, h⟩ := GlobalTheory.SelfDualFirstProj.exists_finite_residues_pi (κ := κ) v k hk
      exact ⟨R, hR, fun t ht => by
        obtain ⟨r, hr, u, hu, e⟩ := h t ((hL₀ t).1 ht)
        exact ⟨r, hr, u, (hL₀ u).2 hu, e⟩⟩
    · intro u hu
      have hu' := (hL₀ u).1 hu
      refine (hP _).2 ⟨c • (0 : κ → Fv F v), ?_⟩
      have := LB ((c⁻¹ * N) • u) 0 (fun i => O.toSubring.mul_mem hNc (hu' i)) (fun _ => O.zero_mem)
      convert this using 2
      funext i
      simp only [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul]
      field_simp
    · intro u hu
      obtain ⟨y, hy⟩ := (hP u).1 hu
      refine (hL₀ _).2 fun i => ?_
      simp only [Pi.smul_apply, nsmul_eq_mul]
      rw [hNeq]
      exact O.toSubring.mul_mem hNc (hbd _ hy i).1
    · refine (hL₀ _).2 fun i => ?_
      simp only [Pi.smul_apply, nsmul_eq_mul]
      rw [hNeq]
      exact O.toSubring.mul_mem hNc (hcη i)
    · intro y _ h
      refine hη y ((hself _).2 fun l hl => ?_)
      simp only [zero_dotProduct, zero_sub, AddChar.map_neg_eq_inv]
      rw [h l.1 ((hP _).2 ⟨l.2, hl⟩), inv_one]
  obtain ⟨y, hy⟩ := (hP η).1 hmem
  exact ⟨y, hy⟩

end GlobalTheory.SelfDualFirstProj
