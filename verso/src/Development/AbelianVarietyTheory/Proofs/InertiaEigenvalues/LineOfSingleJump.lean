import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFilteredStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SecondTwistSmallIffExactlyAtAndFinClause
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyClosedOfDictClosed

noncomputable section

namespace GlobalTheory.TwistJump

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

section Act

variable {Qp BdR LL A : Type} [Field Qp] [CommRing BdR] [Algebra Qp BdR] [Field LL] [Algebra Qp LL]
  [CommRing A] [Algebra Qp A] [Algebra LL A] [IsScalarTower Qp LL A]
  (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def mulR : BdR →ₐ[Qp] Module.End LL (V ⊗[Qp] BdR) where
  toFun b := AlgebraTensorModule.map LinearMap.id (LinearMap.mulLeft Qp b)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]
  map_zero' := by ext; simp
  map_add' a b := by ext; simp [add_mul, tmul_add]
  commutes' c := by ext; simp [Algebra.smul_def, ← tmul_smul]

def act (ε : A →ₐ[LL] LL) : A ⊗[Qp] BdR →ₐ[LL] Module.End LL (V ⊗[Qp] BdR) :=
  Algebra.TensorProduct.lift ((Algebra.ofId LL _).comp ε) (mulR V)
    fun a b => Algebra.commute_algebraMap_left (ε a) (mulR (LL := LL) V b)

variable {V}

/- English proof (translation)
Simplify using `[act, mulR, Algebra.ofId_apply]`.
-/
theorem act_tmul (ε : A →ₐ[LL] LL) (a : A) (b : BdR) (y : V ⊗[Qp] BdR) :
    act V ε (a ⊗ₜ b) y =
      ε a • AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp b) y := by
  simp [act, mulR, Algebra.ofId_apply]

end Act

section Periods

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {A : Type} [CommRing A] [Algebra Qp A] [Algebra LL A] [IsScalarTower Qp LL A]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

/- English proof (translation)
Simplify using `only [FildR, DdRE, DdR, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`.
-/
theorem mem_fildR (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) (y : V ⊗[Qp] BdR) :
    y ∈ FildR PD ρ τ a ↔ ((∀ g, actVdR PD ρ g y = y) ∧ ∀ c : K, mulVdR (LL := LL) c y = τ c • y) ∧
      y ∈ FilV PD (LL := LL) (V := V) a := by
  simp only [FildR, DdRE, DdR, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

def gal (g : G) : A ⊗[Qp] BdR →ₐ[LL] A ⊗[Qp] BdR :=
  Algebra.TensorProduct.map (AlgHom.id LL A) ((PD.actdR g).toAlgHom.restrictScalars Qp)

/- English proof (translation)
Proceed by induction on `r using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]`. Consider the case `tmul a b`. Simplify using `only [gal, Algebra.TensorProduct.map_tmul, act_tmul, map_smul, AlgHom.id_apply]`.

Use `congr 1`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul v x => simp [actVdR]`.
-/
theorem actVdR_act (ε : A →ₐ[LL] LL) (ρ : Representation LL G V) (g : G) (r : A ⊗[Qp] BdR)
    (y : V ⊗[Qp] BdR) :
    actVdR PD ρ g (act V ε r y) = act V ε (gal PD (LL := LL) g r) (actVdR PD ρ g y) := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul a b =>
    simp only [gal, Algebra.TensorProduct.map_tmul, act_tmul, map_smul, AlgHom.id_apply]
    congr 1
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul v x => simp [actVdR]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, smul_add]`. Consider the case `tmul v x => simp [actVdR, h, smul_tmul']`.
-/
theorem actVdR_twist (ρ ρ' : Representation LL G V) (g : G) (c : LL) (h : ∀ x, ρ' g x = c • ρ g x)
    (y : V ⊗[Qp] BdR) : actVdR PD ρ' g y = c • actVdR PD ρ g y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul v x => simp [actVdR, h, smul_tmul']

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, smul_add]`. Consider the case `tmul v x => simp [actVdR, gal, h, smul_tmul']`.
-/
theorem actVdR_char (ν : Representation LL G A) (g : G) (c : LL) (h : ∀ x, ν g x = c • x)
    (y : A ⊗[Qp] BdR) : actVdR PD ν g y = c • gal PD (LL := LL) g y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul v x => simp [actVdR, gal, h, smul_tmul']

/- English proof (translation)
Rewrite using `[act_tmul, map_one, one_smul, mulVdR]`.
-/
theorem mulVdR_eq_act (ε : A →ₐ[LL] LL) (c : K) (y : V ⊗[Qp] BdR) :
    mulVdR (LL := LL) c y = act V ε ((1 : A) ⊗ₜ algebraMap K BdR c) y := by
  rw [act_tmul, map_one, one_smul, mulVdR]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy, mul_add]`. Consider the case `tmul v x => simp`.
-/
theorem map_mulLeft (b : BdR) (y : A ⊗[Qp] BdR) :
    AlgebraTensorModule.map (LinearMap.id : A →ₗ[LL] A) (LinearMap.mulLeft Qp b) y =
      ((1 : A) ⊗ₜ b) * y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]
  | tmul v x => simp

/- English proof (translation)
Take `⟨r, rfl⟩` from `hr`. Take `⟨y, rfl⟩` from `hy`. Proceed by induction on `r using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simpa only [map_add, LinearMap.add_apply] using add_mem ha hb`.

Consider the case `tmul c b`. Rewrite using `[AlgebraTensorModule.map_tmul, act_tmul]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy => simpa only [map_add] using add_mem hx hy`. Consider the case `tmul v x`. Use `⟨v ⊗ₜ ⟨b.1 * x.1, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[add_comm]`. Conclude with `PD.Fil_mul _ _ _ _ b.2 x.2`.
-/
theorem act_mem_filV (ε : A →ₐ[LL] LL) {a k : ℤ} {r : A ⊗[Qp] BdR} {y : V ⊗[Qp] BdR}
    (hr : r ∈ FilV PD (LL := LL) (V := A) k) (hy : y ∈ FilV PD (LL := LL) (V := V) a) :
    act V ε r y ∈ FilV PD (LL := LL) (V := V) (a + k) := by
  obtain ⟨r, rfl⟩ := hr
  obtain ⟨y, rfl⟩ := hy
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simpa only [map_add, LinearMap.add_apply] using add_mem ha hb
  | tmul c b =>
    rw [AlgebraTensorModule.map_tmul, act_tmul]
    refine Submodule.smul_mem _ _ ?_
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using add_mem hx hy
    | tmul v x =>
      refine ⟨v ⊗ₜ ⟨b.1 * x.1, ?_⟩, rfl⟩
      rw [add_comm]
      exact PD.Fil_mul _ _ _ _ b.2 x.2

/- English proof (translation)
Take `⟨r, rfl⟩` from `hr`. Take `⟨y, rfl⟩` from `hy`. Proceed by induction on `r using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simpa only [map_add, add_mul] using add_mem ha hb`.

Consider the case `tmul c b`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simpa only [map_add, mul_add] using add_mem hx hy`. Consider the case `tmul v x`.

Use `⟨(c * v) ⊗ₜ ⟨b.1 * x.1, ?_⟩, by simp⟩` and prove the remaining obligations. Rewrite using `[add_comm]`. Conclude with `PD.Fil_mul _ _ _ _ b.2 x.2`.
-/
theorem mul_mem_filV {a k : ℤ} {r y : A ⊗[Qp] BdR}
    (hr : r ∈ FilV PD (LL := LL) (V := A) k) (hy : y ∈ FilV PD (LL := LL) (V := A) a) :
    r * y ∈ FilV PD (LL := LL) (V := A) (a + k) := by
  obtain ⟨r, rfl⟩ := hr
  obtain ⟨y, rfl⟩ := hy
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simpa only [map_add, add_mul] using add_mem ha hb
  | tmul c b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add, mul_add] using add_mem hx hy
    | tmul v x =>
      refine ⟨(c * v) ⊗ₜ ⟨b.1 * x.1, ?_⟩, by simp⟩
      rw [add_comm]
      exact PD.Fil_mul _ _ _ _ b.2 x.2

/- English proof (translation)
Use `haveI := PD.finK`. Use `haveI : Algebra.FormallyUnramified Qp K := Algebra.FormallyUnramified.of_isSeparable Qp K`. Set `f : K ⊗[Qp] K →ₐ[Qp] A ⊗[Qp] BdR` to `Algebra.TensorProduct.map ((IsScalarTower.toAlgHom Qp LL A).comp τ) (IsScalarTower.toAlgHom Qp K BdR)`. Establish `hf : ∀ a b, f (a ⊗ₜ b) = algebraMap LL A (τ a) ⊗ₜ algebraMap K BdR b` using `fun _ _ => rfl`. Use `⟨f (Algebra.FormallyUnramified.elem Qp K), ?_, fun g => ?_, fun c => ?_, fun y hy => ?_⟩` and prove the remaining obligations.

Generalize the expression as in `Algebra.FormallyUnramified.elem Qp K = z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simpa only [map_add] using add_mem ha hb`. Consider the case `tmul a b`.

Use `⟨algebraMap LL A (τ a) ⊗ₜ ⟨algebraMap K BdR b, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `(PD.Fil 0).smul_mem _ PD.one_mem`. Generalize the expression as in `Algebra.FormallyUnramified.elem Qp K = z`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul a b => simp [hf, gal]`. Use `congrArg f (Algebra.FormallyUnramified.one_tmul_mul_elem (R := Qp) c)` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul, hf, hf, map_one, map_one, map_one]`.

Rewrite using `[this, Algebra.smul_def]`. Both sides reduce to the same expression. Establish `: ∀ z, act V ε (f z) y = τ (Algebra.TensorProduct.lmul' Qp z) • y`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, add_smul]`. Consider the case `tmul a b`. Rewrite using `[hf, act_tmul, AlgHom.commutes]`. Express the relevant statement in the definitionally equal form `τ a • mulVdR (LL := LL) b y = _`.

Rewrite using `[hy, smul_smul]`. Simplify using the standard rewrite rules. Rewrite using `[this, Algebra.FormallyUnramified.lmul_elem, map_one, one_smul]`.
-/
theorem exists_idem [Algebra.IsSeparable Qp K] (ε : A →ₐ[LL] LL) (τ : K →ₐ[Qp] LL) :
    ∃ u : A ⊗[Qp] BdR, u ∈ FilV PD (LL := LL) (V := A) 0 ∧ (∀ g, gal PD (LL := LL) g u = u) ∧
      (∀ c : K, ((1 : A) ⊗ₜ algebraMap K BdR c) * u = τ c • u) ∧
      ∀ y : V ⊗[Qp] BdR, (∀ c : K, mulVdR (LL := LL) c y = τ c • y) → act V ε u y = y := by
  haveI := PD.finK
  haveI : Algebra.FormallyUnramified Qp K := Algebra.FormallyUnramified.of_isSeparable Qp K
  let f : K ⊗[Qp] K →ₐ[Qp] A ⊗[Qp] BdR :=
    Algebra.TensorProduct.map ((IsScalarTower.toAlgHom Qp LL A).comp τ) (IsScalarTower.toAlgHom Qp K BdR)
  have hf : ∀ a b, f (a ⊗ₜ b) = algebraMap LL A (τ a) ⊗ₜ algebraMap K BdR b := fun _ _ => rfl
  refine ⟨f (Algebra.FormallyUnramified.elem Qp K), ?_, fun g => ?_, fun c => ?_, fun y hy => ?_⟩
  · generalize Algebra.FormallyUnramified.elem Qp K = z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simpa only [map_add] using add_mem ha hb
    | tmul a b =>
      refine ⟨algebraMap LL A (τ a) ⊗ₜ ⟨algebraMap K BdR b, ?_⟩, rfl⟩
      rw [Algebra.algebraMap_eq_smul_one]
      exact (PD.Fil 0).smul_mem _ PD.one_mem
  · generalize Algebra.FormallyUnramified.elem Qp K = z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b => simp [hf, gal]
  · have := congrArg f (Algebra.FormallyUnramified.one_tmul_mul_elem (R := Qp) c)
    rw [map_mul, map_mul, hf, hf, map_one, map_one, map_one] at this
    rw [this, Algebra.smul_def]
    rfl
  · have : ∀ z, act V ε (f z) y = τ (Algebra.TensorProduct.lmul' Qp z) • y := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, add_smul]
      | tmul a b =>
        rw [hf, act_tmul, AlgHom.commutes]
        change τ a • mulVdR (LL := LL) b y = _
        rw [hy, smul_smul]
        simp
    rw [this, Algebra.FormallyUnramified.lmul_elem, map_one, one_smul]

/- English proof (translation)
Use `haveI := GlobalTheory.Cmp.SmallJumps.finite_ddRE_of_multV PD ν τ {b} (by simp) fun a => by`. Apply the tactic sequence `rw [h, Multiset.count_singleton]; split_ifs <;> simp`. Use `haveI : ∀ a, FiniteDimensional LL (FildR PD ν τ a) := fun a => Submodule.finiteDimensional_of_le (S₂ := DdRE PD ν τ) inf_le_left`. Establish `anti : Antitone (FildR PD ν τ)` using `fun a a' haa => inf_le_inf_left _ (GlobalTheory.Cmp.SmallJumps.filV_anti PD haa)`. Establish `st : ∀ a, a ≠ b → FildR PD ν τ (a + 1) = FildR PD ν τ a` using `fun a ha => by`.

Use `h a` as an intermediate fact. Rewrite `this` using `[if_neg ha, multV]`. Conclude with `Submodule.eq_of_le_of_finrank_eq (anti (by omega)) (by omega)`. Establish `up : ∀ a, b + 1 ≤ a → FildR PD ν τ a = FildR PD ν τ (b + 1)` using `fun a ha => by`. Proceed by induction on `a, ha using Int.le_induction with`.

Consider the case `base => rfl`. Consider the case `succ a ha ih => rw [st a (by omega), ih]`. Establish `down : ∀ a ≤ b, FildR PD ν τ a = FildR PD ν τ b` using `fun a ha => by`. Proceed by induction on `a, ha using Int.le_induction_down with`. Consider the case `base => rfl`.

Consider the case `pred a ha ih => rw [← st (a - 1) (by omega), sub_add_cancel, ih]`. Establish `bot : FildR PD ν τ (b + 1) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Use `GlobalTheory.Cmp.JumpDict.filV_sep PD (LL := LL) x fun a => ?_` and prove the remaining obligations.

Break down `le_total a (b + 1) with ha | ha` into its components or cases. Conclude with `(anti ha hx).2`. Conclude with `(up a ha ▸ hx : x ∈ FildR PD ν τ a).2`. Establish `one : finrank LL (FildR PD ν τ b) = 1`. Use `h b` as an intermediate fact.

Rewrite `this` using `[if_pos rfl, multV, bot, finrank_bot]`. Use linear arithmetic over natural numbers and integers. Take `⟨d, -, hd⟩` from `finrank_eq_one_iff'.1 one`. Use `⟨d, d.2, fun a y hy => ?_⟩` and prove the remaining obligations. Break down `le_or_gt a b with ha | ha` into its components or cases.

Take `⟨c, hc⟩` from `hd ⟨y, down a ha ▸ hy⟩`. Conclude with `⟨c, (congrArg Subtype.val hc).symm, fun h' => absurd ha (by omega)⟩`. Rewrite `hy` using `[up a ha, bot]`. Conclude with `⟨0, by rw [zero_smul]; exact hy, fun _ => rfl⟩`.
-/
theorem line_of_single_jump (ν : Representation LL G V) (τ : K →ₐ[Qp] LL) (b : ℤ)
    (h : ∀ a : ℤ, multV PD ν τ a = if a = b then 1 else 0) :
    ∃ d ∈ FildR PD ν τ b, ∀ a, ∀ y ∈ FildR PD ν τ a, ∃ c : LL, y = c • d ∧ (b < a → c = 0) := by
  haveI := GlobalTheory.Cmp.SmallJumps.finite_ddRE_of_multV PD ν τ {b} (by simp) fun a => by
    rw [h, Multiset.count_singleton]; split_ifs <;> simp
  haveI : ∀ a, FiniteDimensional LL (FildR PD ν τ a) := fun a =>
    Submodule.finiteDimensional_of_le (S₂ := DdRE PD ν τ) inf_le_left
  have anti : Antitone (FildR PD ν τ) := fun a a' haa =>
    inf_le_inf_left _ (GlobalTheory.Cmp.SmallJumps.filV_anti PD haa)
  have st : ∀ a, a ≠ b → FildR PD ν τ (a + 1) = FildR PD ν τ a := fun a ha => by
    have := h a
    rw [if_neg ha, multV] at this
    exact Submodule.eq_of_le_of_finrank_eq (anti (by omega)) (by omega)
  have up : ∀ a, b + 1 ≤ a → FildR PD ν τ a = FildR PD ν τ (b + 1) := fun a ha => by
    induction a, ha using Int.le_induction with
    | base => rfl
    | succ a ha ih => rw [st a (by omega), ih]
  have down : ∀ a ≤ b, FildR PD ν τ a = FildR PD ν τ b := fun a ha => by
    induction a, ha using Int.le_induction_down with
    | base => rfl
    | pred a ha ih => rw [← st (a - 1) (by omega), sub_add_cancel, ih]
  have bot : FildR PD ν τ (b + 1) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    refine GlobalTheory.Cmp.JumpDict.filV_sep PD (LL := LL) x fun a => ?_
    rcases le_total a (b + 1) with ha | ha
    · exact (anti ha hx).2
    · exact (up a ha ▸ hx : x ∈ FildR PD ν τ a).2
  have one : finrank LL (FildR PD ν τ b) = 1 := by
    have := h b
    rw [if_pos rfl, multV, bot, finrank_bot] at this
    omega
  obtain ⟨d, -, hd⟩ := finrank_eq_one_iff'.1 one
  refine ⟨d, d.2, fun a y hy => ?_⟩
  rcases le_or_gt a b with ha | ha
  · obtain ⟨c, hc⟩ := hd ⟨y, down a ha ▸ hy⟩
    exact ⟨c, (congrArg Subtype.val hc).symm, fun h' => absurd ha (by omega)⟩
  · rw [up a ha, bot] at hy
    exact ⟨0, by rw [zero_smul]; exact hy, fun _ => rfl⟩

/- English proof (translation)
Introduce `y hy`. Rewrite `hy`, the goal using `[mem_fildR]`. Use `⟨⟨fun g => hg g y (hy.1.1 g), fun c => ?_⟩, act_mem_filV PD ε hr hy.2⟩` and prove the remaining obligations. Rewrite using `[mulVdR_eq_act ε, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply, ← mulVdR_eq_act ε, hy.1.2, map_smul]`.
-/
theorem act_maps (ε : A →ₐ[LL] LL) (ρ ρ' : Representation LL G V) (τ : K →ₐ[Qp] LL) {a k : ℤ}
    {r : A ⊗[Qp] BdR} (hr : r ∈ FilV PD (LL := LL) (V := A) k)
    (hg : ∀ g y, actVdR PD ρ g y = y → actVdR PD ρ' g (act V ε r y) = act V ε r y) :
    ∀ y ∈ FildR PD ρ τ a, act V ε r y ∈ FildR PD ρ' τ (a + k) := by
  intro y hy
  rw [mem_fildR] at hy ⊢
  refine ⟨⟨fun g => hg g y (hy.1.1 g), fun c => ?_⟩, act_mem_filV PD ε hr hy.2⟩
  rw [mulVdR_eq_act ε, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply,
    ← mulVdR_eq_act ε, hy.1.2, map_smul]

/- English proof (translation)
Take `⟨u, hu0, hug, huc, hu1⟩` from `exists_idem PD (V := V) ε τ`. Take `⟨p, hp, hline⟩` from `line_of_single_jump PD ν τ b h`. Establish `hχ : ∀ g, χ g ≠ 0` using `fun g h0 => by`. Use `congrArg ε (ν.self_inv_apply g 1)` as an intermediate fact. Rewrite `this` using `[hν, h0, zero_smul, map_zero, map_one]`.

Conclude with `zero_ne_one this`. Establish `hud : ∀ i, u * d i ∈ FildR PD ν τ (k i)` using `fun i => by`. Rewrite using `[mem_fildR]`. Use `⟨⟨fun g => ?_, fun c => ?_⟩, by simpa using mul_mem_filV PD hu0 (hd i).2.1⟩` and prove the remaining obligations. Use `(hd i).1` as an intermediate fact.

Simplify using `only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this`. Establish `h2` using `this g`. Rewrite `h2`, the goal using `[actVdR_char PD ν g _ (hν g)]`. Rewrite using `[map_mul, hug, ← mul_smul_comm, h2]`. Rewrite using `[mulVdR, map_mulLeft, ← mul_assoc, huc, smul_mul_assoc]`.

Use `choose c hc hc0 using fun i => hline _ _ (hud i)`. Set `s : A ⊗[Qp] BdR` to `∑ i, c i • ((1 : A) ⊗ₜ β i)`. Establish `hs : s ∈ FilV PD (LL` using `LL) (V := A) (-b) := by`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Break down `le_or_gt (k i) b with hk | hk` into its components or cases.

Use `Submodule.smul_mem _ _ (GlobalTheory.Cmp.SmallJumps.filV_anti PD (by omega : -b ≤ 0 - k i) ?_)` and prove the remaining obligations. Conclude with `⟨1 ⊗ₜ ⟨β i, (hd i).2.2⟩, rfl⟩`. Rewrite using `[hc0 i hk, zero_smul]`. Conclude with `Submodule.zero_mem _`. Establish `hsp : s * p = u`.

Rewrite using `[← mul_one u, h1, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mulLeft, mul_left_comm, hc, smul_mul_assoc, mul_smul_comm]`. Rewrite `hp` using `[mem_fildR]`. Establish `hpg : ∀ g, χ g • gal PD (LL` using `LL) g p = p := fun g => by`.

Rewrite using `[← actVdR_char PD ν g _ (hν g), hp.1.1]`. Establish `hsg : ∀ g, gal PD (LL` using `LL) g (u * s) = χ g • (u * s) := fun g => by`. Establish `h2` using `congrArg (gal PD (LL := LL) g) hsp`. Rewrite `h2` using `[map_mul, hug]`. Rewrite using `[map_mul, hug]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hpg, hsp]`. Use `_ = χ g • (gal PD (LL := LL) g s * gal PD (LL := LL) g p * s) := by`. Rewrite using `[mul_smul_comm, smul_mul_assoc]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [h2]`. Establish `f1` using `act_maps PD ε ρ ρ' τ (a := a) hp.2 fun g y hy => by`. Rewrite using `[actVdR_twist PD ρ ρ' g _ (hρ g), actVdR_act, hy, ← LinearMap.smul_apply, ← map_smul, hpg]`. Establish `f2` using `act_maps PD ε ρ' ρ τ (a := a + b) (mul_mem_filV PD hu0 hs) fun g y hy => by`.

Rewrite `hy` using `[actVdR_twist PD ρ ρ' g _ (hρ g)]`. Rewrite using `[actVdR_act, hsg, map_smul, LinearMap.smul_apply, ← map_smul, hy]`. Rewrite `f2` using `[show a + b + (-b + 0) = a by ring]`. Establish `hinv : ∀ y : V ⊗[Qp] BdR, (∀ c : K, mulVdR (LL` using `LL) c y = τ c • y) → act V ε (p * (u * s)) y = y := fun y hy => by`. Rewrite using `[show p * (u * s) = u * (s * p) by ring, hsp, map_mul, Module.End.mul_apply, hu1 y hy, hu1 y hy]`.

Use `LinearEquiv.finrank_eq (LinearEquiv.ofLinear ((act V ε (u * s)).restrict f2) ((act V ε p).restrict f1) ?_ ?_)` and prove the remaining obligations. Use extensionality with `y`. Use `hinv y ((mem_fildR PD ρ τ _ _).1 y.2).1.2` as an intermediate fact. Rewrite `this` using `[mul_comm, map_mul]`. Then use the resulting hypothesis. Use extensionality with `y`.

Use `hinv y ((mem_fildR PD ρ' τ _ _).1 y.2).1.2` as an intermediate fact. Rewrite `this` using `[map_mul]`. Then use the resulting hypothesis.
-/
theorem finrank_twist [Algebra.IsSeparable Qp K] (ε : A →ₐ[LL] LL)
    (ρ ρ' : Representation LL G V) (ν : Representation LL G A) (χ : G → LL)
    (hν : ∀ g x, ν g x = χ g • x) (hρ : ∀ g x, ρ' g x = χ g • ρ g x)
    {m : ℕ} (k : Fin m → ℤ) (β : Fin m → BdR) (d : Fin m → A ⊗[Qp] BdR)
    (hd : ∀ i, d i ∈ DdR PD ν ∧ d i ∈ FilV PD (LL := LL) (V := A) (k i) ∧ β i ∈ PD.Fil (0 - k i))
    (h1 : (1 : A ⊗[Qp] BdR) =
      ∑ i, AlgebraTensorModule.map (LinearMap.id : A →ₗ[LL] A) (LinearMap.mulLeft Qp (β i)) (d i))
    (τ : K →ₐ[Qp] LL) (b : ℤ) (h : ∀ a : ℤ, multV PD ν τ a = if a = b then 1 else 0) (a : ℤ) :
    finrank LL (FildR PD ρ' τ (a + b)) = finrank LL (FildR PD ρ τ a) := by
  obtain ⟨u, hu0, hug, huc, hu1⟩ := exists_idem PD (V := V) ε τ
  obtain ⟨p, hp, hline⟩ := line_of_single_jump PD ν τ b h
  have hχ : ∀ g, χ g ≠ 0 := fun g h0 => by
    have := congrArg ε (ν.self_inv_apply g 1)
    rw [hν, h0, zero_smul, map_zero, map_one] at this
    exact zero_ne_one this
  have hud : ∀ i, u * d i ∈ FildR PD ν τ (k i) := fun i => by
    rw [mem_fildR]
    refine ⟨⟨fun g => ?_, fun c => ?_⟩, by simpa using mul_mem_filV PD hu0 (hd i).2.1⟩
    · have := (hd i).1
      simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at this
      have h2 := this g
      rw [actVdR_char PD ν g _ (hν g)] at h2 ⊢
      rw [map_mul, hug, ← mul_smul_comm, h2]
    · rw [mulVdR, map_mulLeft, ← mul_assoc, huc, smul_mul_assoc]
  choose c hc hc0 using fun i => hline _ _ (hud i)
  let s : A ⊗[Qp] BdR := ∑ i, c i • ((1 : A) ⊗ₜ β i)
  have hs : s ∈ FilV PD (LL := LL) (V := A) (-b) := by
    refine Submodule.sum_mem _ fun i _ => ?_
    rcases le_or_gt (k i) b with hk | hk
    · refine Submodule.smul_mem _ _ (GlobalTheory.Cmp.SmallJumps.filV_anti PD (by omega : -b ≤ 0 - k i) ?_)
      exact ⟨1 ⊗ₜ ⟨β i, (hd i).2.2⟩, rfl⟩
    · rw [hc0 i hk, zero_smul]
      exact Submodule.zero_mem _
  have hsp : s * p = u := by
    rw [← mul_one u, h1, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mulLeft, mul_left_comm, hc, smul_mul_assoc, mul_smul_comm]
  rw [mem_fildR] at hp
  have hpg : ∀ g, χ g • gal PD (LL := LL) g p = p := fun g => by
    rw [← actVdR_char PD ν g _ (hν g), hp.1.1]
  have hsg : ∀ g, gal PD (LL := LL) g (u * s) = χ g • (u * s) := fun g => by
    have h2 := congrArg (gal PD (LL := LL) g) hsp
    rw [map_mul, hug] at h2
    rw [map_mul, hug]
    calc u * gal PD (LL := LL) g s = s * (χ g • gal PD (LL := LL) g p) * gal PD (LL := LL) g s := by
          rw [hpg, hsp]
      _ = χ g • (gal PD (LL := LL) g s * gal PD (LL := LL) g p * s) := by
          rw [mul_smul_comm, smul_mul_assoc]; congr 1; ring
      _ = _ := by rw [h2]
  have f1 := act_maps PD ε ρ ρ' τ (a := a) hp.2 fun g y hy => by
    rw [actVdR_twist PD ρ ρ' g _ (hρ g), actVdR_act, hy, ← LinearMap.smul_apply, ← map_smul, hpg]
  have f2 := act_maps PD ε ρ' ρ τ (a := a + b) (mul_mem_filV PD hu0 hs) fun g y hy => by
    rw [actVdR_twist PD ρ ρ' g _ (hρ g)] at hy
    rw [actVdR_act, hsg, map_smul, LinearMap.smul_apply, ← map_smul, hy]
  rw [show a + b + (-b + 0) = a by ring] at f2
  have hinv : ∀ y : V ⊗[Qp] BdR, (∀ c : K, mulVdR (LL := LL) c y = τ c • y) →
      act V ε (p * (u * s)) y = y := fun y hy => by
    rw [show p * (u * s) = u * (s * p) by ring, hsp, map_mul, Module.End.mul_apply, hu1 y hy, hu1 y hy]
  refine LinearEquiv.finrank_eq (LinearEquiv.ofLinear ((act V ε (u * s)).restrict f2)
    ((act V ε p).restrict f1) ?_ ?_)
  · ext y
    have := hinv y ((mem_fildR PD ρ τ _ _).1 y.2).1.2
    rwa [mul_comm, map_mul] at this
  · ext y
    have := hinv y ((mem_fildR PD ρ' τ _ _).1 y.2).1.2
    rwa [map_mul] at this

end Periods

/- English proof (translation)
Introduce `l _ P AI T K LL V _ _ _ _ _ ρ ρ' ν χ hν hρ hdR τ b h a`. Use `haveI := (P.PD K).finK`. Take `⟨m, k, β, d, hd, h1⟩` from `GlobalTheory.T.deRham_comparison_isFiltered l P AI T K LL (Fin 1 → ↥LL.1) ν hdR 0 1 ⟨1 ⊗ₜ ⟨1, (P.PD K).one_mem⟩, rfl⟩`. Establish `key` using `finrank_twist (P.PD K) (Pi.evalAlgHom ↥LL.1 (fun _ : Fin 1 => ↥LL.1) 0) ρ ρ' ν χ hν hρ k β d hd h1 τ b h`. Rewrite using `[multV, multV, add_right_comm, key, key]`.
-/
theorem multV_twist_char : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ ρ' : Representation ↥LL.1 ↥(GK K) V) (ν : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1)) (χ : ↥(GK K) → ↥LL.1), (∀ g x, ν g x = χ g • x) → (∀ g x, ρ' g x = χ g • ρ g x) → IsDR (P.PD K) ν → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), (∀ a : ℤ, multV (P.PD K) ν τ a = if a = b then 1 else 0) → ∀ a : ℤ, multV (P.PD K) ρ' τ (a + b) = multV (P.PD K) ρ τ a := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ ρ' ν χ hν hρ hdR τ b h a
  haveI := (P.PD K).finK
  obtain ⟨m, k, β, d, hd, h1⟩ := GlobalTheory.T.deRham_comparison_isFiltered l P AI T K LL (Fin 1 → ↥LL.1) ν hdR 0 1
    ⟨1 ⊗ₜ ⟨1, (P.PD K).one_mem⟩, rfl⟩
  have key := finrank_twist (P.PD K) (Pi.evalAlgHom ↥LL.1 (fun _ : Fin 1 => ↥LL.1) 0) ρ ρ' ν χ hν hρ
    k β d hd h1 τ b h
  rw [multV, multV, add_right_comm, key, key]

end GlobalTheory.TwistJump
