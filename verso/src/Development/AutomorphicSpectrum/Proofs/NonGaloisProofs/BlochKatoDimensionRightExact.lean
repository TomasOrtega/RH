import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SurjectiveHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTmulOneOfFrobFixedOfMemFilZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OfShortExact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamSubrepQuotientAndStrictness

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

namespace GlobalTheory.CompanionTheory.BKDim

section LinAlg

variable {L E F : Type} [Field L] [AddCommGroup E] [Module L E] [AddCommGroup F] [Module L F]

/- English proof (translation)
Establish `h` using `LinearMap.rank_range_add_rank_ker (f.domRestrict X)`. Rewrite `h` using `[LinearMap.range_domRestrict, LinearMap.ker_domRestrict]`. Rewrite using `[← h]`. Use `congr 1`. Establish `e : (X ⊓ LinearMap.ker f).comap X.subtype = (LinearMap.ker f).comap X.subtype`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[← e]`. Conclude with `(Submodule.comapSubtypeEquivOfLe (inf_le_left : X ⊓ LinearMap.ker f ≤ X)).rank_eq.symm`.
-/
theorem rank_map_add (X : Submodule L E) (f : E →ₗ[L] F) :
    Module.rank L ↥(X.map f) + Module.rank L ↥(X ⊓ LinearMap.ker f) = Module.rank L ↥X := by
  have h := LinearMap.rank_range_add_rank_ker (f.domRestrict X)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  rw [← h]
  congr 1
  have e : (X ⊓ LinearMap.ker f).comap X.subtype = (LinearMap.ker f).comap X.subtype := by
    ext x; simp
  rw [← e]
  exact (Submodule.comapSubtypeEquivOfLe (inf_le_left : X ⊓ LinearMap.ker f ≤ X)).rank_eq.symm

/- English proof (translation)
Rewrite using `[← Module.rank_lt_aleph0_iff, ← rank_map_add X f]`. Conclude with `Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 _ _) (Module.rank_lt_aleph0 _ _)`.
-/
theorem finite_of_map_of_ker (X : Submodule L E) (f : E →ₗ[L] F) [Module.Finite L ↥(X.map f)]
    [Module.Finite L ↥(X ⊓ LinearMap.ker f)] : Module.Finite L ↥X := by
  rw [← Module.rank_lt_aleph0_iff, ← rank_map_add X f]
  exact Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 _ _) (Module.rank_lt_aleph0 _ _)

/- English proof (translation)
Establish `h` using `LinearMap.finrank_range_add_finrank_ker (f.domRestrict X)`. Rewrite `h` using `[LinearMap.range_domRestrict, LinearMap.ker_domRestrict]`. Rewrite using `[← h]`. Use `congr 1`. Establish `e : (X ⊓ LinearMap.ker f).comap X.subtype = (LinearMap.ker f).comap X.subtype`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[← e]`. Conclude with `(Submodule.comapSubtypeEquivOfLe (inf_le_left : X ⊓ LinearMap.ker f ≤ X)).finrank_eq.symm`.
-/
theorem finrank_map_add (X : Submodule L E) (f : E →ₗ[L] F) [Module.Finite L ↥X] :
    finrank L ↥(X.map f) + finrank L ↥(X ⊓ LinearMap.ker f) = finrank L ↥X := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict X)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  rw [← h]
  congr 1
  have e : (X ⊓ LinearMap.ker f).comap X.subtype = (LinearMap.ker f).comap X.subtype := by
    ext x; simp
  rw [← e]
  exact (Submodule.comapSubtypeEquivOfLe (inf_le_left : X ⊓ LinearMap.ker f ≤ X)).finrank_eq.symm

def prodEquiv (p : Submodule L E) (q : Submodule L F) : ↥(p.prod q) ≃ₗ[L] ↥p × ↥q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), y.1.2, y.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

end LinAlg

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma actVB_tmul' (g : G) (v : V) (b : B) :
    actVB PD ρ g (v ⊗ₜ[Qp] b) = ρ g v ⊗ₜ[Qp] PD.actB g b := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma actVdR_tmul' (g : G) (v : V) (b : BdR) :
    actVdR PD ρ g (v ⊗ₜ[Qp] b) = ρ g v ⊗ₜ[Qp] PD.actdR g b := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma φVB_tmul' (v : V) (b : B) :
    φVB PD (LL := LL) (V := V) (v ⊗ₜ[Qp] b) = v ⊗ₜ[Qp] PD.φ b := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma ιV_tmul' (v : V) (b : B) :
    ιV PD (LL := LL) (V := V) (v ⊗ₜ[Qp] b) = v ⊗ₜ[Qp] PD.ι b := rfl

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul v b => rw [actVB_tmul', φVB_tmul', φVB_tmul', actVB_tmul', PD.φ_comm]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
lemma φVB_actVB' (g : G) (x : V ⊗[Qp] B) :
    φVB PD (LL := LL) (V := V) (actVB PD ρ g x) = actVB PD ρ g (φVB PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => rw [actVB_tmul', φVB_tmul', φVB_tmul', actVB_tmul', PD.φ_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul v b => rw [actVB_tmul', ιV_tmul', ιV_tmul', actVdR_tmul', PD.ι_comm]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
lemma ιV_actVB' (g : G) (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g x) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => rw [actVB_tmul', ιV_tmul', ιV_tmul', actVdR_tmul', PD.ι_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul v b`. Rewrite using `[actVB_tmul', actVB_tmul', actVB_tmul', map_mul, map_mul]`. Both sides reduce to the same expression.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
lemma actVB_mul' (g h : G) (x : V ⊗[Qp] B) :
    actVB PD ρ (g * h) x = actVB PD ρ g (actVB PD ρ h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b =>
    rw [actVB_tmul', actVB_tmul', actVB_tmul', map_mul, map_mul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Take `⟨z, rfl⟩` from `hy`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero, Submodule.zero_mem]`. Consider the case `tmul v b`. Conclude with `⟨ρ g v ⊗ₜ[Qp] ⟨PD.actdR g b.1, PD.Fil_G g a _ b.2⟩, rfl⟩`.

Consider the case `add x y hx hy`. Rewrite using `[map_add, map_add]`. Conclude with `Submodule.add_mem _ hx hy`.
-/
lemma actVdR_mem_FilV' (g : G) (a : ℤ) (y : V ⊗[Qp] BdR)
    (hy : y ∈ FilV PD (LL := LL) (V := V) a) :
    actVdR PD ρ g y ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨z, rfl⟩ := hy
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Submodule.zero_mem]
  | tmul v b =>
    exact ⟨ρ g v ⊗ₜ[Qp] ⟨PD.actdR g b.1, PD.Fil_G g a _ b.2⟩, rfl⟩
  | add x y hx hy =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ hx hy

include PD in
/- English proof (translation)
Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nontrivial_iff_subsingleton]`. Apply `PD.not_mem_filtration_two` to reduce the goal to its premises. Rewrite using `[Subsingleton.elim PD.t 0, map_zero]`. Conclude with `Submodule.zero_mem _`.
-/
lemma nontrivial_B' : Nontrivial B := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply PD.not_mem_filtration_two
  rw [Subsingleton.elim PD.t 0, map_zero]
  exact Submodule.zero_mem _

include PD in
/- English proof (translation)
Use `haveI := nontrivial_B' PD`. Take `⟨f, hf⟩` from `Module.Projective.exists_dual_eq_one Qp (one_ne_zero : (1 : B) ≠ 0)`. Use `congrArg (fun z => TensorProduct.rid Qp V (LinearMap.lTensor V f z)) h` as an intermediate fact. Simplify `this` using `[hf]`.
-/
lemma tmul_one_injective' {v w : V} (h : v ⊗ₜ[Qp] (1 : B) = w ⊗ₜ[Qp] (1 : B)) : v = w := by
  haveI := nontrivial_B' PD
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one Qp (one_ne_zero : (1 : B) ≠ 0)
  have := congrArg (fun z => TensorProduct.rid Qp V (LinearMap.lTensor V f z)) h
  simpa [hf] using this

/- English proof (translation)
Establish `e₁ : actVB PD ρ g d₁ - d₁ = 0` using `(Submodule.mem_iInf _).1 h₁ g`. Establish `e₂ : actVdR PD ρ g d₂ - d₂ = 0` using `(Submodule.mem_iInf _).1 h₂ g`. Rewrite `e₁` using `[← hx, map_sub]`. Rewrite `e₂` using `[← hxy, map_sub]`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[map_sub, φVB_actVB', ← sub_eq_zero, ← neg_eq_zero, ← e₁]`. Normalize the expressions using the abelian group laws. Establish `: ιV PD (LL` using `LL) (V := V) (actVB PD ρ g x - x) = actVdR PD ρ g y - y := by`. Rewrite using `[map_sub, ιV_actVB', ← sub_eq_zero, ← e₂]`. Normalize the expressions using the abelian group laws.

Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ (actVdR_mem_FilV' PD ρ g 0 y hy) hy`.
-/
lemma sub_fixed_mem (d₁ : V ⊗[Qp] B) (h₁ : d₁ ∈ Dcris PD ρ) (d₂ : V ⊗[Qp] BdR) (h₂ : d₂ ∈ DdR PD ρ)
    (x : V ⊗[Qp] B) (y : V ⊗[Qp] BdR) (hy : y ∈ FilV PD (LL := LL) (V := V) 0)
    (hx : x - φVB PD (LL := LL) (V := V) x = d₁) (hxy : ιV PD (LL := LL) (V := V) x - y = d₂)
    (g : G) :
    φVB PD (LL := LL) (V := V) (actVB PD ρ g x - x) = actVB PD ρ g x - x ∧
      ιV PD (LL := LL) (V := V) (actVB PD ρ g x - x) ∈ FilV PD (LL := LL) (V := V) 0 := by
  have e₁ : actVB PD ρ g d₁ - d₁ = 0 := (Submodule.mem_iInf _).1 h₁ g
  have e₂ : actVdR PD ρ g d₂ - d₂ = 0 := (Submodule.mem_iInf _).1 h₂ g
  rw [← hx, map_sub] at e₁
  rw [← hxy, map_sub] at e₂
  constructor
  · rw [map_sub, φVB_actVB', ← sub_eq_zero, ← neg_eq_zero, ← e₁]
    abel
  · have : ιV PD (LL := LL) (V := V) (actVB PD ρ g x - x) = actVdR PD ρ g y - y := by
      rw [map_sub, ιV_actVB', ← sub_eq_zero, ← e₂]
      abel
    rw [this]
    exact Submodule.sub_mem _ (actVdR_mem_FilV' PD ρ g 0 y hy) hy

/- English proof (translation)
Apply `tmul_one_injective' PD` to reduce the goal to its premises. Establish `e : ρ g (c h) ⊗ₜ[Qp] (1 : B) = actVB PD ρ g (c h ⊗ₜ[Qp] (1 : B))`. Rewrite using `[actVB_tmul', map_one]`. Rewrite using `[add_tmul, e, hc, hc, hc, map_sub, actVB_mul']`. Normalize the expressions using the abelian group laws.
-/
lemma cocycle_of_tmul_one (x : V ⊗[Qp] B) (c : G → V)
    (hc : ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) (g h : G) :
    c (g * h) = c g + ρ g (c h) := by
  apply tmul_one_injective' PD
  have e : ρ g (c h) ⊗ₜ[Qp] (1 : B) = actVB PD ρ g (c h ⊗ₜ[Qp] (1 : B)) := by
    rw [actVB_tmul', map_one]
  rw [add_tmul, e, hc, hc, hc, map_sub, actVB_mul']
  abel

/- English proof (translation)
Use `(Submodule.mem_iInf _).2 fun g => ?_` and prove the remaining obligations. Establish `h1 : φVB PD (LL` using `LL) (V := V) (c g ⊗ₜ[Qp] (1 : B)) = c g ⊗ₜ[Qp] (1 : B) := by`. Simplify using `[φVB]`. Rewrite `h1` using `[hx g, map_sub, φVB_actVB']`. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_sub, sub_sub_sub_comm, h1, sub_self]`.
-/
theorem sub_φ_mem_Dcris (c : G → V) (x : V ⊗[Qp] B)
    (hx : ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) :
    x - φVB PD (LL := LL) (V := V) x ∈ Dcris PD ρ := by
  refine (Submodule.mem_iInf _).2 fun g => ?_
  have h1 : φVB PD (LL := LL) (V := V) (c g ⊗ₜ[Qp] (1 : B)) = c g ⊗ₜ[Qp] (1 : B) := by
    simp [φVB]
  rw [hx g, map_sub, φVB_actVB'] at h1
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_sub, sub_sub_sub_comm, h1,
    sub_self]

/- English proof (translation)
Rewrite using `[← ιV_actVB', ← map_sub, ← hx g]`. Establish `h1 : ιV PD (LL` using `LL) (V := V) (c g ⊗ₜ[Qp] (1 : B)) = c g ⊗ₜ[Qp] (1 : BdR) := by`. Simplify using `[ιV]`. Rewrite using `[h1]`. Conclude with `⟨c g ⊗ₜ[Qp] ⟨1, PD.one_mem⟩, rfl⟩`.
-/
theorem act_ιV_sub_mem (c : G → V) (x : V ⊗[Qp] B)
    (hx : ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) (g : G) :
    actVdR PD ρ g (ιV PD (LL := LL) (V := V) x) - ιV PD (LL := LL) (V := V) x ∈
      FilV PD (LL := LL) (V := V) 0 := by
  rw [← ιV_actVB', ← map_sub, ← hx g]
  have h1 : ιV PD (LL := LL) (V := V) (c g ⊗ₜ[Qp] (1 : B)) = c g ⊗ₜ[Qp] (1 : BdR) := by
    simp [ιV]
  rw [h1]
  exact ⟨c g ⊗ₜ[Qp] ⟨1, PD.one_mem⟩, rfl⟩

/- English proof (translation)
Establish `hA : ∀ u : V ⊗[Qp] B, ∃ x : V ⊗[Qp] B, x - φVB PD (LL` using `LL) (V := V) x = u := by`. Introduce `u`. Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `tmul v b`.

Take `⟨x, -, -, hx, -⟩` from `h b 0`. Conclude with `⟨v ⊗ₜ x, by rw [φVB_tmul', ← TensorProduct.tmul_sub, hx]⟩`. Consider the case `add u u' hu hu'`. Take `⟨x, hx⟩` from `hu`. Take `⟨x', hx'⟩` from `hu'`.

Use `⟨x + x', ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, ← hx, ← hx']`. Normalize the expressions using the abelian group laws. Establish `hB : ∀ w : V ⊗[Qp] BdR, ∃ x : V ⊗[Qp] B, φVB PD (LL` using `LL) (V := V) x = x ∧ ιV PD (LL := LL) (V := V) x - w ∈ FilV PD (LL := LL) (V := V) 0 := by`. Introduce `w`.

Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp, by simp⟩`. Consider the case `tmul v b`. Take `⟨x, y, hy, hx, hxy⟩` from `h 0 b`. Use `⟨v ⊗ₜ x, by rw [φVB_tmul', ← sub_eq_zero.1 hx], ?_⟩` and prove the remaining obligations.

Rewrite using `[ιV_tmul', ← TensorProduct.tmul_sub, ← hxy, sub_sub_cancel]`. Conclude with `⟨v ⊗ₜ ⟨y, hy⟩, rfl⟩`. Consider the case `add w w' hw hw'`. Take `⟨x, hx, hy⟩` from `hw`. Take `⟨x', hx', hy'⟩` from `hw'`.

Use `⟨x + x', by rw [map_add, hx, hx'], ?_⟩` and prove the remaining obligations. Use `Submodule.add_mem _ hy hy'` as an intermediate fact. Rewrite using `[map_add]`. Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws.

Take `⟨x₀, hx₀⟩` from `hA u`. Take `⟨x₁, hx₁, hy⟩` from `hB (w - ιV PD (LL := LL) (V := V) x₀)`. Use `⟨x₀ + x₁, _, hy, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, hx₁, ← hx₀]`. Normalize the expressions using the abelian group laws.

Rewrite using `[map_add]`. Normalize the expressions using the abelian group laws.
-/
theorem tensor_onto
    (h : ∀ (u : B) (w : BdR), ∃ (x : B) (y : BdR), y ∈ PD.Fil 0 ∧ x - PD.φ x = u ∧ PD.ι x - y = w)
    (u : V ⊗[Qp] B) (w : V ⊗[Qp] BdR) :
    ∃ (x : V ⊗[Qp] B) (y : V ⊗[Qp] BdR), y ∈ FilV PD (LL := LL) (V := V) 0 ∧
      x - φVB PD (LL := LL) (V := V) x = u ∧ ιV PD (LL := LL) (V := V) x - y = w := by
  have hA : ∀ u : V ⊗[Qp] B, ∃ x : V ⊗[Qp] B, x - φVB PD (LL := LL) (V := V) x = u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul v b =>
      obtain ⟨x, -, -, hx, -⟩ := h b 0
      exact ⟨v ⊗ₜ x, by rw [φVB_tmul', ← TensorProduct.tmul_sub, hx]⟩
    | add u u' hu hu' =>
      obtain ⟨x, hx⟩ := hu
      obtain ⟨x', hx'⟩ := hu'
      refine ⟨x + x', ?_⟩
      rw [map_add, ← hx, ← hx']
      abel
  have hB : ∀ w : V ⊗[Qp] BdR, ∃ x : V ⊗[Qp] B, φVB PD (LL := LL) (V := V) x = x ∧
      ιV PD (LL := LL) (V := V) x - w ∈ FilV PD (LL := LL) (V := V) 0 := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | tmul v b =>
      obtain ⟨x, y, hy, hx, hxy⟩ := h 0 b
      refine ⟨v ⊗ₜ x, by rw [φVB_tmul', ← sub_eq_zero.1 hx], ?_⟩
      rw [ιV_tmul', ← TensorProduct.tmul_sub, ← hxy, sub_sub_cancel]
      exact ⟨v ⊗ₜ ⟨y, hy⟩, rfl⟩
    | add w w' hw hw' =>
      obtain ⟨x, hx, hy⟩ := hw
      obtain ⟨x', hx', hy'⟩ := hw'
      refine ⟨x + x', by rw [map_add, hx, hx'], ?_⟩
      have := Submodule.add_mem _ hy hy'
      rw [map_add]
      convert this using 1
      abel
  obtain ⟨x₀, hx₀⟩ := hA u
  obtain ⟨x₁, hx₁, hy⟩ := hB (w - ιV PD (LL := LL) (V := V) x₀)
  refine ⟨x₀ + x₁, _, hy, ?_, ?_⟩
  · rw [map_add, hx₁, ← hx₀]
    abel
  · rw [map_add]
    abel

end General

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

section Res

variable (L : Type) [Field L] [Algebra Qp L] [Algebra L LL] [Module L V] [IsScalarTower L LL V]
  [IsScalarTower Qp L V] (ρ : Representation LL G V)

def res : Representation L G V where
  toFun g := (ρ g).restrictScalars L
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Dcris, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]`. Both sides reduce to the same expression.
-/
theorem Dcris_res : Dcris PD (res L ρ) = (Dcris PD ρ).restrictScalars L := by
  ext x
  simp only [Dcris, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply]
  rfl

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [DdR, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]`. Both sides reduce to the same expression.
-/
theorem DdR_res : DdR PD (res L ρ) = (DdR PD ρ).restrictScalars L := by
  ext x
  simp only [DdR, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply]
  rfl

/- English proof (translation)
Unfold `IsCrys at h ⊢`. Rewrite using `[Dcris_res]`. Express the relevant statement in the definitionally equal form `finrank L ↥(Dcris PD ρ) = _`. Rewrite using `[← Module.finrank_mul_finrank L LL ↥(Dcris PD ρ), ← Module.finrank_mul_finrank L LL V, h, mul_left_comm]`.
-/
theorem isCrys_res (h : IsCrys PD ρ) : IsCrys PD (res L ρ) := by
  unfold IsCrys at h ⊢
  rw [Dcris_res]
  change finrank L ↥(Dcris PD ρ) = _
  rw [← Module.finrank_mul_finrank L LL ↥(Dcris PD ρ), ← Module.finrank_mul_finrank L LL V, h,
    mul_left_comm]

/- English proof (translation)
Unfold `IsDR at h ⊢`. Rewrite `h` using `[DdR_res]`. Express the relevant statement in the definitionally equal form `finrank L ↥(DdR PD ρ) = _ at h`. Rewrite `h` using `[← Module.finrank_mul_finrank L LL ↥(DdR PD ρ), ← Module.finrank_mul_finrank L LL V, mul_left_comm]`. Conclude with `Nat.eq_of_mul_eq_mul_left Module.finrank_pos h`.
-/
theorem isDR_of_res [FiniteDimensional L LL] (h : IsDR PD (res L ρ)) : IsDR PD ρ := by
  unfold IsDR at h ⊢
  rw [DdR_res] at h
  change finrank L ↥(DdR PD ρ) = _ at h
  rw [← Module.finrank_mul_finrank L LL ↥(DdR PD ρ), ← Module.finrank_mul_finrank L LL V,
    mul_left_comm] at h
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h

end Res

variable (f : V →ₗ[LL] V')

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [φVB]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem map_φVB (x : V ⊗[Qp] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) (φVB PD (LL := LL) x) =
      φVB PD (LL := LL) (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [φVB]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [ιV]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem map_ιV (x : V ⊗[Qp] B) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (ιV PD (LL := LL) x) =
      ιV PD (LL := LL) (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [ιV]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Take `⟨z, rfl⟩` from `hy`. Use `⟨AlgebraTensorModule.map f LinearMap.id z, ?_⟩` and prove the remaining obligations. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem map_mem_FilV {a : ℤ} {y : V ⊗[Qp] BdR} (hy : y ∈ FilV PD (LL := LL) (V := V) a) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) y ∈ FilV PD (LL := LL) (V := V') a := by
  obtain ⟨z, rfl⟩ := hy
  refine ⟨AlgebraTensorModule.map f LinearMap.id z, ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [actVB, hf]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem map_actVB {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (g : G) (x : V ⊗[Qp] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) (actVB PD ρ g x) =
      actVB PD ρ' g (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, hf]
  | add x y hx hy => simp only [map_add, hx, hy]

include PD in
/- English proof (translation)
Establish `h1 : (1 : B) ≠ 0` using `fun h0 => PD.not_mem_filtration_two (by`. Rewrite using `[← mul_one PD.t, h0, mul_zero, map_zero]`. Conclude with `Submodule.zero_mem _)`. Take `⟨φ, hφ⟩` from `Module.Projective.exists_dual_eq_one Qp h1`. Use `congrArg (fun z => TensorProduct.rid Qp V (LinearMap.lTensor V φ z)) h` as an intermediate fact.

Simplify `this` using `[hφ]`.
-/
theorem tmul_one_injective {v w : V} (h : v ⊗ₜ[Qp] (1 : B) = w ⊗ₜ[Qp] (1 : B)) : v = w := by
  have h1 : (1 : B) ≠ 0 := fun h0 => PD.not_mem_filtration_two (by
    rw [← mul_one PD.t, h0, mul_zero, map_zero]; exact Submodule.zero_mem _)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one Qp h1
  have := congrArg (fun z => TensorProduct.rid Qp V (LinearMap.lTensor V φ z)) h
  simpa [hφ] using this

end Generic

/- English proof (translation)
Set `L : FinExt l` to `⟨⊥, inferInstance⟩`. Use `letI : Algebra ↥L.1 LL := ((algebraMap ℚ_[l] LL).comp (IntermediateField.botEquiv ℚ_[l] (Om l)).toRingEquiv.toRingHom).toAlgebra`. Use `haveI : IsScalarTower ℚ_[l] ↥L.1 LL := IsScalarTower.of_algebraMap_eq fun x => (congrArg (algebraMap ℚ_[l] LL) ((IntermediateField.botEquiv ℚ_[l] (Om l)).commutes x)).symm`. Use `haveI : FiniteDimensional ↥L.1 LL := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _`. Use `letI : Module ↥L.1 V := Module.compHom V (algebraMap ↥L.1 LL)`.

Use `letI : Module ↥L.1 V' := Module.compHom V' (algebraMap ↥L.1 LL)`. Use `haveI : IsScalarTower ↥L.1 LL V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl`. Use `haveI : IsScalarTower ↥L.1 LL V' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl`. Use `haveI : IsScalarTower ℚ_[l] ↥L.1 V := IsScalarTower.to₁₂₄ ℚ_[l] ↥L.1 LL V`. Use `haveI : IsScalarTower ℚ_[l] ↥L.1 V' := IsScalarTower.to₁₂₄ ℚ_[l] ↥L.1 LL V'`.

Use `haveI : FiniteDimensional ↥L.1 V := Module.Finite.trans LL V`. Use `haveI : FiniteDimensional ↥L.1 V' := Module.Finite.trans LL V'`. Establish `hc` using `isCrys_res (P.PD K) ↥L.1 ρ h`. Establish `hd` using `(GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T K L V _ hc).1`. Take `⟨-, h1⟩` from `(GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI T K L V (res ↥L.1 ρ) V' (res ↥L.1 ρ') (f.restrictScalars ↥L.1) hf).2 hs hc`.

Take `⟨h2, h3⟩` from `(GlobalTheory.DRSubQuot.deRham_sub_quot l P AI T K L V (res ↥L.1 ρ) V' (res ↥L.1 ρ') (f.restrictScalars ↥L.1) hf).2 hs hd`. Rewrite `h1` using `[Dcris_res, Dcris_res]`. Rewrite `h3` using `[DdR_res, DdR_res]`. Use `⟨isDR_of_res (P.PD K) ↥L.1 ρ' h2, h1, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `GlobalTheory.DRFil.exists_mem_FilV (P.PD K) (LL := ↥L.1) y`.

Take `⟨x, hx, hxy⟩` from `h3 a y ⟨hy, ha⟩`. Conclude with `⟨x, hx.1, hxy⟩`.
-/
theorem lift_periods {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [FiniteDimensional LL V] (ρ : Representation LL ↥(GK K) V)
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL ↥(GK K) V') (f : V →ₗ[LL] V')
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (hs : Function.Surjective f) (h : IsCrys (P.PD K) ρ) :
    IsDR (P.PD K) ρ' ∧
      (∀ y ∈ Dcris (P.PD K) ρ', ∃ x ∈ Dcris (P.PD K) ρ,
        AlgebraTensorModule.map f (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B) x = y) ∧
      ∀ y ∈ DdR (P.PD K) ρ', ∃ x ∈ DdR (P.PD K) ρ,
        AlgebraTensorModule.map f (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR) x = y := by
  let L : FinExt l := ⟨⊥, inferInstance⟩
  letI : Algebra ↥L.1 LL :=
    ((algebraMap ℚ_[l] LL).comp (IntermediateField.botEquiv ℚ_[l] (Om l)).toRingEquiv.toRingHom).toAlgebra
  haveI : IsScalarTower ℚ_[l] ↥L.1 LL := IsScalarTower.of_algebraMap_eq fun x =>
    (congrArg (algebraMap ℚ_[l] LL) ((IntermediateField.botEquiv ℚ_[l] (Om l)).commutes x)).symm
  haveI : FiniteDimensional ↥L.1 LL := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  letI : Module ↥L.1 V := Module.compHom V (algebraMap ↥L.1 LL)
  letI : Module ↥L.1 V' := Module.compHom V' (algebraMap ↥L.1 LL)
  haveI : IsScalarTower ↥L.1 LL V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower ↥L.1 LL V' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower ℚ_[l] ↥L.1 V := IsScalarTower.to₁₂₄ ℚ_[l] ↥L.1 LL V
  haveI : IsScalarTower ℚ_[l] ↥L.1 V' := IsScalarTower.to₁₂₄ ℚ_[l] ↥L.1 LL V'
  haveI : FiniteDimensional ↥L.1 V := Module.Finite.trans LL V
  haveI : FiniteDimensional ↥L.1 V' := Module.Finite.trans LL V'
  have hc := isCrys_res (P.PD K) ↥L.1 ρ h
  have hd := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T K L V _ hc).1
  obtain ⟨-, h1⟩ := (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l P AI T K L V (res ↥L.1 ρ) V' (res ↥L.1 ρ')
    (f.restrictScalars ↥L.1) hf).2 hs hc
  obtain ⟨h2, h3⟩ := (GlobalTheory.DRSubQuot.deRham_sub_quot l P AI T K L V (res ↥L.1 ρ) V' (res ↥L.1 ρ')
    (f.restrictScalars ↥L.1) hf).2 hs hd
  rw [Dcris_res, Dcris_res] at h1
  rw [DdR_res, DdR_res] at h3
  refine ⟨isDR_of_res (P.PD K) ↥L.1 ρ' h2, h1, fun y hy => ?_⟩
  obtain ⟨a, ha⟩ := GlobalTheory.DRFil.exists_mem_FilV (P.PD K) (LL := ↥L.1) y
  obtain ⟨x, hx, hxy⟩ := h3 a y ⟨hy, ha⟩
  exact ⟨x, hx.1, hxy⟩

section Count

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

/- English proof (translation)
Simplify using `only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`.
-/
theorem mem_Dcris {x : V ⊗[Qp] B} : x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]

/- English proof (translation)
Simplify using `only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`.
-/
theorem mem_DdR {x : V ⊗[Qp] BdR} : x ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g x = x := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [actVB, actVdR, ιV, PD.ι_comm]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem ιV_actVB (g : G) (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (actVB PD ρ g x) = actVdR PD ρ g (ιV PD (LL := LL) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, actVdR, ιV, PD.ι_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [actVB, φVB, PD.φ_comm]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem φVB_actVB (g : G) (x : V ⊗[Qp] B) :
    φVB PD (LL := LL) (actVB PD ρ g x) = actVB PD ρ g (φVB PD (LL := LL) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, φVB, PD.φ_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Use extensionality with `v`. Simplify using `only [H0V, cob, LinearMap.ker_pi]`.
-/
theorem ker_cob : LinearMap.ker (cob ρ) = H0V ρ := by
  ext v
  simp only [H0V, cob, LinearMap.ker_pi]

variable [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

def Triples : Submodule LL ((G → V) × (V ⊗[Qp] B) × (V ⊗[Qp] BdR)) where
  carrier := {t | t.1 ∈ finiteCocycles PD ρ ∧ (∀ g, t.1 g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g t.2.1 - t.2.1) ∧
    t.2.2 ∈ FilV PD (LL := LL) (V := V) 0 ∧ ιV PD (LL := LL) t.2.1 - t.2.2 ∈ DdR PD ρ}
  zero_mem' := ⟨Submodule.zero_mem _, fun g => by simp, Submodule.zero_mem _, by simp⟩
  add_mem' := by
    rintro a b ⟨h1, h2, h3, h4⟩ ⟨k1, k2, k3, k4⟩
    refine ⟨Submodule.add_mem _ h1 k1, fun g => ?_, Submodule.add_mem _ h3 k3, ?_⟩
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_tmul, h2, k2, map_add]
      abel
    · have := Submodule.add_mem _ h4 k4
      simp only [Prod.fst_add, Prod.snd_add, map_add]
      convert this using 1
      abel
  smul_mem' := by
    rintro c a ⟨h1, h2, h3, h4⟩
    refine ⟨Submodule.smul_mem _ c h1, fun g => ?_, Submodule.smul_mem _ c h3, ?_⟩
    · simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul, ← smul_sub, ← h2]
      rfl
    · have := Submodule.smul_mem _ c h4
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, ← smul_sub]
      exact this

/- English proof (translation)
Set `β : ((G → V) × (V ⊗[Qp] B) × (V ⊗[Qp] BdR)) →ₗ[LL] (V ⊗[Qp] B) × (V ⊗[Qp] BdR)` to `(((LinearMap.id - φVB PD (LL := LL) (V := V)) ∘ₗ LinearMap.fst LL _ _).prod (ιV PD (LL := LL) (V := V) ∘ₗ LinearMap.fst LL _ _ - LinearMap.snd LL _ _)) ∘ₗ LinearMap.snd LL _ _`. Establish `hβ : ∀ t, β t = (t.2.1 - φVB PD (LL` using `LL) (V := V) t.2.1, ιV PD (LL := LL) (V := V) t.2.1 - t.2.2) := fun t => rfl`. Set `j : V →ₗ[LL] V ⊗[Qp] B` to `(AlgebraTensorModule.mk Qp LL V B).flip 1`. Establish `hj : ∀ v, j v = v ⊗ₜ[Qp] (1 : B)` using `fun v => rfl`. Set `α : V →ₗ[LL] ((G → V) × (V ⊗[Qp] B) × (V ⊗[Qp] BdR))` to `(cob ρ).prod (j.prod (ιV PD (LL := LL) (V := V) ∘ₗ j))`.

Establish `hα : ∀ v, α v = (fun g => ρ g v - v, v ⊗ₜ[Qp] (1 : B), ιV PD (LL` using `LL) (V := V) (v ⊗ₜ[Qp] (1 : B))) := fun v => rfl`. Establish `hact : ∀ g (v : V), actVB PD ρ g (v ⊗ₜ[Qp] (1 : B)) = ρ g v ⊗ₜ[Qp] (1 : B)`. Introduce `g v`. Simplify using `[actVB]`. Establish `hφ1 : ∀ v : V, φVB PD (LL` using `LL) (V := V) (v ⊗ₜ[Qp] (1 : B)) = v ⊗ₜ[Qp] (1 : B) := by`.

Introduce `v`. Simplify using `[φVB]`. Establish `hcob : ∀ v : V, cob ρ v ∈ finiteCocycles PD ρ`. Introduce `v`. Use `⟨⟨hc v, fun g h => ?_⟩, v ⊗ₜ[Qp] (1 : B), fun g => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `ρ (g * h) v - v = (ρ g v - v) + ρ g (ρ h v - v)`. Rewrite using `[map_mul, Module.End.mul_apply, map_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[hact, ← sub_tmul]`. Both sides reduce to the same expression.

Establish `e1 : (Triples PD ρ).map β = (Dcris PD ρ).prod (DdR PD ρ)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨t, ⟨-, h2, -, h4⟩, rfl⟩`. Rewrite using `[hβ]`. Use `⟨(mem_Dcris PD ρ).2 fun g => ?_, h4⟩` and prove the remaining obligations.

Establish `h5` using `hφ1 (t.1 g)`. Rewrite `h5` using `[h2, map_sub, φVB_actVB]`. Express the relevant statement in the definitionally equal form `actVB PD ρ g (_ - _) = _ - _`. Rewrite using `[map_sub, sub_eq_sub_iff_sub_eq_sub, h5]`. Introduce and unpack `⟨d₁, d₂⟩ ⟨h1, h2⟩`.

Take `⟨x, y, c, k1, k2, k3, k4, k5⟩` from `hd d₁ h1 d₂ h2`. Use `⟨(c, x, y), ⟨k4, k5, k1, ?_⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ιV PD (LL := LL) (V := V) x - y ∈ _`. Rewrite using `[k3]`. Conclude with `h2`.

Rewrite using `[hβ, ← k2, ← k3]`. Establish `e2 : Triples PD ρ ⊓ LinearMap.ker β = LinearMap.range α`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `⟨c, x, y⟩ ⟨⟨-, h2, h3, -⟩, h5⟩`. Establish `h6 : β (c, x, y) = 0` using `h5`.

Rewrite `h6` using `[hβ, Prod.mk_eq_zero, sub_eq_zero, sub_eq_zero]`. Take `⟨h6, h7⟩` from `h6`. Simplify using `only at h2 h3 h6 h7`. Take `⟨v, rfl⟩` from `hk x h6.symm (h7 ▸ h3)`. Use `⟨v, ?_⟩` and prove the remaining obligations.

Rewrite using `[hα, h7]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Apply `tmul_one_injective' PD` to reduce the goal to its premises. Rewrite using `[h2, hact, sub_tmul]`.

Introduce and unpack `_ ⟨v, rfl⟩`. Use `⟨⟨hcob v, fun g => ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hα] dsimp only`. Rewrite using `[hact, sub_tmul]`. Use `⟨v ⊗ₜ ⟨1, PD.one_mem⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hα]`. Simplify using `[ιV]`. Rewrite using `[hα]`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `β (α v) = 0`.

Rewrite using `[hβ, hα]`. Simplify using `[hφ1]`. Establish `hαi : Function.Injective α`. Introduce `v w h`. Rewrite `h` using `[hα, hα]`.

Conclude with `tmul_one_injective' PD (congrArg (fun t => t.2.1) h)`. Establish `e3 : (Triples PD ρ).map (LinearMap.fst LL _ _) = finiteCocycles PD ρ`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨t, ht, rfl⟩`. Conclude with `ht.1`.

Introduce `c hc'`. Take `⟨x, hx⟩` from `hc'.2`. Take `⟨d, h1, h2⟩` from `hl c x hx`. Use `⟨(c, x, ιV PD (LL := LL) (V := V) x - d), ⟨hc', hx, h2, ?_⟩, rfl⟩` and prove the remaining obligations. Simplify using `using h1`.

Establish `e4 : Triples PD ρ ⊓ LinearMap.ker (LinearMap.fst LL _ _) = ((Dcris PD ρ).prod (DdR PD ρ ⊓ FilV PD (LL` using `LL) (V := V) 0)).map (LinearMap.inr LL _ _) := by`. Establish `hι : ∀ x ∈ Dcris PD ρ, ιV PD (LL` using `LL) (V := V) x ∈ DdR PD ρ := fun x hx => (mem_DdR PD ρ).2 fun g => by rw [← ιV_actVB, (mem_Dcris PD ρ).1 hx g]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `⟨c, x, y⟩ ⟨⟨-, h2, h3, h4⟩, h5⟩`. Establish `h6 : c = 0` using `h5`.

Substitute `h6` using the available equality. Establish `hx : x ∈ Dcris PD ρ` using `(mem_Dcris PD ρ).2 fun g => by`. Use `h2 g` as an intermediate fact. Simplify using `only [Pi.zero_apply, zero_tmul] at this`. Conclude with `sub_eq_zero.1 this.symm`.

Use `⟨(x, y), ⟨hx, ?_, h3⟩, rfl⟩` and prove the remaining obligations. Use `Submodule.sub_mem _ (hι x hx) h4` as an intermediate fact. Simplify using `using this`. Introduce and unpack `_ ⟨⟨x, y⟩, ⟨hx, hy, hy'⟩, rfl⟩`. Use `⟨⟨Submodule.zero_mem _, fun g => ?_, hy', Submodule.sub_mem _ (hι x hx) hy⟩, rfl⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(0 : V) ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x`. Rewrite using `[(mem_Dcris PD ρ).1 hx g, sub_self, zero_tmul]`. Use `haveI : Module.Finite LL ↥((Triples PD ρ).map β) := by`. Rewrite using `[e1]`. Conclude with `Module.Finite.equiv (prodEquiv _ _).symm`.

Use `haveI : Module.Finite LL ↥(Triples PD ρ ⊓ LinearMap.ker β) := by`. Rewrite using `[e2]`. Use `infer_instance`. Use `haveI : Module.Finite LL ↥(Triples PD ρ) := finite_of_map_of_ker _ β`. Use `haveI : Module.Finite LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0) := Submodule.finiteDimensional_of_le inf_le_left`.

Use `haveI : Module.Finite LL ↥(finiteCocycles PD ρ) := by`. Rewrite using `[← e3]`. Use `infer_instance`. Establish `d1` using `finrank_map_add (Triples PD ρ) β`. Rewrite `d1` using `[e1, e2, (prodEquiv _ _).finrank_eq, Module.finrank_prod, LinearMap.finrank_range_of_inj hαi]`.

Establish `d2` using `finrank_map_add (Triples PD ρ) (LinearMap.fst LL _ _)`. Rewrite `d2` using `[e3, e4, ← (Submodule.equivMapOfInjective _ LinearMap.inr_injective _).finrank_eq, (prodEquiv _ _).finrank_eq, Module.finrank_prod]`. Establish `d3` using `Submodule.finrank_quotient_add_finrank ((B1 ρ).comap (finiteCocycles PD ρ).subtype)`. Establish `hle : B1 ρ ≤ finiteCocycles PD ρ`. Introduce and unpack `_ ⟨v, rfl⟩`.

Conclude with `hcob v`. Rewrite `d3` using `[(Submodule.comapSubtypeEquivOfLe hle).finrank_eq]`. Establish `d4` using `LinearMap.finrank_range_add_finrank_ker (cob ρ)`. Rewrite `d4` using `[ker_cob]`. Express the relevant statement in the definitionally equal form `finrank LL ↥(B1 ρ) + _ = _ at d4`.

Express the relevant statement in the definitionally equal form `finrank LL (FiniteCohomology PD ρ) + _ = _ at d3`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_H1fV [Module.Finite LL V] [Module.Finite LL ↥(Dcris PD ρ)]
    [Module.Finite LL ↥(DdR PD ρ)] (hc : ∀ v, Continuous fun g => ρ g v - v)
    (hk : ∀ x : V ⊗[Qp] B, φVB PD (LL := LL) (V := V) x = x →
      ιV PD (LL := LL) (V := V) x ∈ FilV PD (LL := LL) (V := V) 0 → ∃ v : V, x = v ⊗ₜ[Qp] (1 : B))
    (hd : ∀ d₁ ∈ Dcris PD ρ, ∀ d₂ ∈ DdR PD ρ, ∃ (x : V ⊗[Qp] B) (y : V ⊗[Qp] BdR) (c : G → V),
      y ∈ FilV PD (LL := LL) (V := V) 0 ∧ x - φVB PD (LL := LL) (V := V) x = d₁ ∧
      ιV PD (LL := LL) (V := V) x - y = d₂ ∧ c ∈ finiteCocycles PD ρ ∧
      ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x)
    (hl : ∀ (c : G → V) (x : V ⊗[Qp] B), (∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) →
      ∃ d ∈ DdR PD ρ, ιV PD (LL := LL) (V := V) x - d ∈ FilV PD (LL := LL) (V := V) 0) :
    (finrank LL (FiniteCohomology PD ρ) : ℤ) = finrank LL ↥(H0V ρ) +
      ((finrank LL ↥(DdR PD ρ) : ℤ) - finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0)) := by
  let β : ((G → V) × (V ⊗[Qp] B) × (V ⊗[Qp] BdR)) →ₗ[LL] (V ⊗[Qp] B) × (V ⊗[Qp] BdR) :=
    (((LinearMap.id - φVB PD (LL := LL) (V := V)) ∘ₗ LinearMap.fst LL _ _).prod
      (ιV PD (LL := LL) (V := V) ∘ₗ LinearMap.fst LL _ _ - LinearMap.snd LL _ _)) ∘ₗ
      LinearMap.snd LL _ _
  have hβ : ∀ t, β t = (t.2.1 - φVB PD (LL := LL) (V := V) t.2.1,
      ιV PD (LL := LL) (V := V) t.2.1 - t.2.2) := fun t => rfl
  let j : V →ₗ[LL] V ⊗[Qp] B := (AlgebraTensorModule.mk Qp LL V B).flip 1
  have hj : ∀ v, j v = v ⊗ₜ[Qp] (1 : B) := fun v => rfl
  let α : V →ₗ[LL] ((G → V) × (V ⊗[Qp] B) × (V ⊗[Qp] BdR)) :=
    (cob ρ).prod (j.prod (ιV PD (LL := LL) (V := V) ∘ₗ j))
  have hα : ∀ v, α v = (fun g => ρ g v - v, v ⊗ₜ[Qp] (1 : B),
      ιV PD (LL := LL) (V := V) (v ⊗ₜ[Qp] (1 : B))) := fun v => rfl
  have hact : ∀ g (v : V), actVB PD ρ g (v ⊗ₜ[Qp] (1 : B)) = ρ g v ⊗ₜ[Qp] (1 : B) := by
    intro g v; simp [actVB]
  have hφ1 : ∀ v : V, φVB PD (LL := LL) (V := V) (v ⊗ₜ[Qp] (1 : B)) = v ⊗ₜ[Qp] (1 : B) := by
    intro v; simp [φVB]
  have hcob : ∀ v : V, cob ρ v ∈ finiteCocycles PD ρ := by
    intro v
    refine ⟨⟨hc v, fun g h => ?_⟩, v ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
    · change ρ (g * h) v - v = (ρ g v - v) + ρ g (ρ h v - v)
      rw [map_mul, Module.End.mul_apply, map_sub]; abel
    · rw [hact, ← sub_tmul]; rfl
  have e1 : (Triples PD ρ).map β = (Dcris PD ρ).prod (DdR PD ρ) := by
    apply le_antisymm
    · rintro _ ⟨t, ⟨-, h2, -, h4⟩, rfl⟩
      rw [hβ]
      refine ⟨(mem_Dcris PD ρ).2 fun g => ?_, h4⟩
      have h5 := hφ1 (t.1 g)
      rw [h2, map_sub, φVB_actVB] at h5
      change actVB PD ρ g (_ - _) = _ - _
      rw [map_sub, sub_eq_sub_iff_sub_eq_sub, h5]
    · rintro ⟨d₁, d₂⟩ ⟨h1, h2⟩
      obtain ⟨x, y, c, k1, k2, k3, k4, k5⟩ := hd d₁ h1 d₂ h2
      refine ⟨(c, x, y), ⟨k4, k5, k1, ?_⟩, ?_⟩
      · change ιV PD (LL := LL) (V := V) x - y ∈ _
        rw [k3]; exact h2
      · rw [hβ, ← k2, ← k3]
  have e2 : Triples PD ρ ⊓ LinearMap.ker β = LinearMap.range α := by
    apply le_antisymm
    · rintro ⟨c, x, y⟩ ⟨⟨-, h2, h3, -⟩, h5⟩
      have h6 : β (c, x, y) = 0 := h5
      rw [hβ, Prod.mk_eq_zero, sub_eq_zero, sub_eq_zero] at h6
      obtain ⟨h6, h7⟩ := h6
      dsimp only at h2 h3 h6 h7
      obtain ⟨v, rfl⟩ := hk x h6.symm (h7 ▸ h3)
      refine ⟨v, ?_⟩
      rw [hα, h7]
      congr 1
      funext g
      apply tmul_one_injective' PD
      rw [h2, hact, sub_tmul]
    · rintro _ ⟨v, rfl⟩
      refine ⟨⟨hcob v, fun g => ?_, ?_, ?_⟩, ?_⟩
      · rw [hα]
        dsimp only
        rw [hact, sub_tmul]
      · refine ⟨v ⊗ₜ ⟨1, PD.one_mem⟩, ?_⟩
        rw [hα]
        simp [ιV]
      · rw [hα]
        simp
      · change β (α v) = 0
        rw [hβ, hα]
        simp [hφ1]
  have hαi : Function.Injective α := by
    intro v w h
    rw [hα, hα] at h
    exact tmul_one_injective' PD (congrArg (fun t => t.2.1) h)
  have e3 : (Triples PD ρ).map (LinearMap.fst LL _ _) = finiteCocycles PD ρ := by
    apply le_antisymm
    · rintro _ ⟨t, ht, rfl⟩
      exact ht.1
    · intro c hc'
      obtain ⟨x, hx⟩ := hc'.2
      obtain ⟨d, h1, h2⟩ := hl c x hx
      refine ⟨(c, x, ιV PD (LL := LL) (V := V) x - d), ⟨hc', hx, h2, ?_⟩, rfl⟩
      simpa using h1
  have e4 : Triples PD ρ ⊓ LinearMap.ker (LinearMap.fst LL _ _) =
      ((Dcris PD ρ).prod (DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0)).map (LinearMap.inr LL _ _) := by
    have hι : ∀ x ∈ Dcris PD ρ, ιV PD (LL := LL) (V := V) x ∈ DdR PD ρ := fun x hx =>
      (mem_DdR PD ρ).2 fun g => by rw [← ιV_actVB, (mem_Dcris PD ρ).1 hx g]
    apply le_antisymm
    · rintro ⟨c, x, y⟩ ⟨⟨-, h2, h3, h4⟩, h5⟩
      have h6 : c = 0 := h5
      subst h6
      have hx : x ∈ Dcris PD ρ := (mem_Dcris PD ρ).2 fun g => by
        have := h2 g
        simp only [Pi.zero_apply, zero_tmul] at this
        exact sub_eq_zero.1 this.symm
      refine ⟨(x, y), ⟨hx, ?_, h3⟩, rfl⟩
      have := Submodule.sub_mem _ (hι x hx) h4
      simpa using this
    · rintro _ ⟨⟨x, y⟩, ⟨hx, hy, hy'⟩, rfl⟩
      refine ⟨⟨Submodule.zero_mem _, fun g => ?_, hy', Submodule.sub_mem _ (hι x hx) hy⟩, rfl⟩
      change (0 : V) ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x
      rw [(mem_Dcris PD ρ).1 hx g, sub_self, zero_tmul]
  haveI : Module.Finite LL ↥((Triples PD ρ).map β) := by
    rw [e1]; exact Module.Finite.equiv (prodEquiv _ _).symm
  haveI : Module.Finite LL ↥(Triples PD ρ ⊓ LinearMap.ker β) := by
    rw [e2]; infer_instance
  haveI : Module.Finite LL ↥(Triples PD ρ) := finite_of_map_of_ker _ β
  haveI : Module.Finite LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0) :=
    Submodule.finiteDimensional_of_le inf_le_left
  haveI : Module.Finite LL ↥(finiteCocycles PD ρ) := by
    rw [← e3]; infer_instance
  have d1 := finrank_map_add (Triples PD ρ) β
  rw [e1, e2, (prodEquiv _ _).finrank_eq, Module.finrank_prod,
    LinearMap.finrank_range_of_inj hαi] at d1
  have d2 := finrank_map_add (Triples PD ρ) (LinearMap.fst LL _ _)
  rw [e3, e4, ← (Submodule.equivMapOfInjective _ LinearMap.inr_injective _).finrank_eq,
    (prodEquiv _ _).finrank_eq, Module.finrank_prod] at d2
  have d3 := Submodule.finrank_quotient_add_finrank ((B1 ρ).comap (finiteCocycles PD ρ).subtype)
  have hle : B1 ρ ≤ finiteCocycles PD ρ := by
    rintro _ ⟨v, rfl⟩; exact hcob v
  rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at d3
  have d4 := LinearMap.finrank_range_add_finrank_ker (cob ρ)
  rw [ker_cob] at d4
  change finrank LL ↥(B1 ρ) + _ = _ at d4
  change finrank LL (FiniteCohomology PD ρ) + _ = _ at d3
  omega

end Count

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL]

/- English proof (translation)
Introduce `d₁ h₁ d₂ h₂`. Take `⟨x, y, hy, hx, hxy⟩` from `tensor_onto PD (LL := LL) h1 d₁ d₂`. Establish `key : ∀ g, ∃ v : A.V, actVB PD A.ρ g x - x = v ⊗ₜ[Qp] (1 : B)` using `fun g => GlobalTheory.exists_tmul_one_of_frob_fixed_of_mem_fil_zero PD _ (sub_fixed_mem PD A.ρ d₁ h₁ d₂ h₂ x y hy hx hxy g).1 (sub_fixed_mem PD A.ρ d₁ h₁ d₂ h₂ x y hy hx hxy g).2`. Use `choose c hc using key`. Establish `hc' : ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD A.ρ g x - x` using `fun g => (hc g).symm`.

Establish `hcont : Continuous c` using `h6 LL O hO A 0 Fin.elim0 Fin.elim0 (fun i => i.elim0) x c (fun g => by rw [Finset.univ_eq_empty, Finset.sum_empty, zero_add]; exact hc' g)`. Conclude with `⟨x, y, c, hy, hx, hxy, ⟨⟨hcont, cocycle_of_tmul_one PD A.ρ x c hc'⟩, x, hc'⟩, hc'⟩`.
-/
theorem connecting
    (h1 : ∀ (u : B) (w : BdR), ∃ (x : B) (y : BdR), y ∈ PD.Fil 0 ∧ x - PD.φ x = u ∧ PD.ι x - y = w)
    (h6 : LocalSituation.contCore PD) (hO : GoodO (Qp := Qp) LL O) (A : GRep G Qp LL O) :
    ∀ d₁ ∈ Dcris PD A.ρ, ∀ d₂ ∈ DdR PD A.ρ, ∃ (x : A.V ⊗[Qp] B) (y : A.V ⊗[Qp] BdR) (c : G → A.V),
      y ∈ FilV PD (LL := LL) (V := A.V) 0 ∧ x - φVB PD (LL := LL) (V := A.V) x = d₁ ∧
      ιV PD (LL := LL) (V := A.V) x - y = d₂ ∧ c ∈ finiteCocycles PD A.ρ ∧
      ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD A.ρ g x - x := by
  intro d₁ h₁ d₂ h₂
  obtain ⟨x, y, hy, hx, hxy⟩ := tensor_onto PD (LL := LL) h1 d₁ d₂
  have key : ∀ g, ∃ v : A.V, actVB PD A.ρ g x - x = v ⊗ₜ[Qp] (1 : B) := fun g =>
    GlobalTheory.exists_tmul_one_of_frob_fixed_of_mem_fil_zero PD _
      (sub_fixed_mem PD A.ρ d₁ h₁ d₂ h₂ x y hy hx hxy g).1
      (sub_fixed_mem PD A.ρ d₁ h₁ d₂ h₂ x y hy hx hxy g).2
  choose c hc using key
  have hc' : ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD A.ρ g x - x := fun g => (hc g).symm
  have hcont : Continuous c :=
    h6 LL O hO A 0 Fin.elim0 Fin.elim0 (fun i => i.elim0) x c
      (fun g => by rw [Finset.univ_eq_empty, Finset.sum_empty, zero_add]; exact hc' g)
  exact ⟨x, y, c, hy, hx, hxy, ⟨⟨hcont, cocycle_of_tmul_one PD A.ρ x c hc'⟩, x, hc'⟩, hc'⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `GlobalTheory.DRFil.exists_mem_FilV PD (LL := LL) (ιV PD (LL := LL) (V := A.V) x)`. Take `⟨w, hw, hw'⟩` from `h5 LL O hO A hA a 0 _ ha (act_ιV_sub_mem PD A.ρ c x hx)`. Conclude with `⟨w, hw.1, hw'⟩`.
-/
theorem lift_fil (h5 : LocalSituation.TateFilteredInvariants PD) (hO : GoodO (Qp := Qp) LL O) (A : GRep G Qp LL O)
    (hA : IsDR PD A.ρ) (c : G → A.V) (x : A.V ⊗[Qp] B)
    (hx : ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD A.ρ g x - x) :
    ∃ d ∈ DdR PD A.ρ, ιV PD (LL := LL) (V := A.V) x - d ∈ FilV PD (LL := LL) (V := A.V) 0 := by
  obtain ⟨a, ha⟩ := GlobalTheory.DRFil.exists_mem_FilV PD (LL := LL) (ιV PD (LL := LL) (V := A.V) x)
  obtain ⟨w, hw, hw'⟩ := h5 LL O hO A hA a 0 _ ha (act_ιV_sub_mem PD A.ρ c x hx)
  exact ⟨w, hw.1, hw'⟩

/- English proof (translation)
Introduce `LL _ _ _ O _ _ hO A hA`. Take `⟨⟨k1, -⟩, ⟨k2, -⟩, -⟩` from `h7 LL O hO A`. Use `finrank_H1fV PD A.ρ (fun v => ?_) (GlobalTheory.exists_tmul_one_of_frob_fixed_of_mem_fil_zero PD) (connecting PD h1 h6 hO A) (lift_fil PD h5 hO A hA)` and prove the remaining obligations. Simplify using `only [sub_eq_add_neg]`. Conclude with `(A.cont v).add continuous_const`.
-/
theorem bkADim_of_core
    (h1 : ∀ (u : B) (w : BdR), ∃ (x : B) (y : BdR), y ∈ PD.Fil 0 ∧ x - PD.φ x = u ∧ PD.ι x - y = w)
    (h5 : LocalSituation.TateFilteredInvariants PD) (h6 : LocalSituation.contCore PD) (h7 : LocalSituation.fontCore PD) : LocalSituation.bkADim PD := by
  intro LL _ _ _ O _ _ hO A hA
  obtain ⟨⟨k1, -⟩, ⟨k2, -⟩, -⟩ := h7 LL O hO A
  refine finrank_H1fV PD A.ρ (fun v => ?_)
    (GlobalTheory.exists_tmul_one_of_frob_fixed_of_mem_fil_zero PD) (connecting PD h1 h6 hO A)
    (lift_fil PD h5 hO A hA)
  simp only [sub_eq_add_neg]
  exact (A.cont v).add continuous_const

end Core

/- English proof (translation)
Introduce `LL _ _ _ O _ _ hO A A' f hf hs hA _ c' hc'`. Use `haveI := hO.2.1`. Take `⟨hdr, hl1, hl2⟩` from `lift_periods T K LL A.ρ A'.ρ f hf hs hA`. Take `⟨-, x', hx'⟩` from `hc'`. Establish `hd1` using `sub_φ_mem_Dcris (P.PD K) A'.ρ c' x' hx'`.

Take `⟨d₂', hd2, hfil⟩` from `lift_fil (P.PD K) h5 hO A' hdr c' x' hx'`. Take `⟨d₁, hd₁, e₁⟩` from `hl1 _ hd1`. Take `⟨d₂, hd₂, e₂⟩` from `hl2 _ hd2`. Take `⟨x, y, c, hy, hx1, hx2, hc, hcx⟩` from `connecting (P.PD K) h1 h6 hO A d₁ hd₁ d₂ hd₂`. Use `⟨c, hc, ?_⟩` and prove the remaining obligations.

Rewrite `e₁` using `[← hx1, map_sub, map_φVB]`. Rewrite `e₂` using `[← hx2, map_sub, map_ιV]`. Take `⟨v, hv⟩` from `GlobalTheory.exists_tmul_one_of_frob_fixed_of_mem_fil_zero (P.PD K) (LL := LL) (AlgebraTensorModule.map f (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B) x - x') (by rw [map_sub, eq_comm, sub_eq_sub_iff_sub_eq_sub]; exact e₁) (by`. Use `Submodule.sub_mem _ (map_mem_FilV (P.PD K) f hy) hfil` as an intermediate fact. Rewrite `this` using `[← e₂]`.

Rewrite using `[map_sub]`. Use `this using 1` and compare the differences between its conclusion and the goal. Use the proof step `abel)`. Use `⟨v, funext fun g => tmul_one_injective (P.PD K) ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (AlgebraTensorModule.map f (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B)) (hcx g)`.

Rewrite `h1` using `[map_sub, map_actVB (P.PD K) f hf, AlgebraTensorModule.map_tmul, LinearMap.id_apply]`. Establish `h2 : actVB (P.PD K) A'.ρ g (v ⊗ₜ[ℚ_[l]] (1 : P.R.B)) = A'.ρ g v ⊗ₜ[ℚ_[l]] (1 : P.R.B)`. Simplify using `[actVB]`. Express the relevant statement in the definitionally equal form `(A'.ρ g v - v) ⊗ₜ[ℚ_[l]] (1 : P.R.B) = (f (c g) - c' g) ⊗ₜ[ℚ_[l]] (1 : P.R.B)`. Rewrite using `[sub_tmul, sub_tmul, h1, hx', ← h2, ← hv, map_sub]`.

Normalize the expressions using the abelian group laws.
-/
theorem bkARightExact_of_core {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}
    (T : LocTied l P AI) (K : FinExt l)
    (h1 : ∀ (u : P.R.B) (w : P.R.BdR), ∃ (x : P.R.B) (y : P.R.BdR), y ∈ (P.PD K).Fil 0 ∧
      x - (P.PD K).φ x = u ∧ (P.PD K).ι x - y = w)
    (h5 : LocalSituation.TateFilteredInvariants (P.PD K)) (h6 : LocalSituation.contCore (P.PD K)) : LocalSituation.bkARightExact (P.PD K) := by
  intro LL _ _ _ O _ _ hO A A' f hf hs hA _ c' hc'
  haveI := hO.2.1
  obtain ⟨hdr, hl1, hl2⟩ := lift_periods T K LL A.ρ A'.ρ f hf hs hA
  obtain ⟨-, x', hx'⟩ := hc'
  have hd1 := sub_φ_mem_Dcris (P.PD K) A'.ρ c' x' hx'
  obtain ⟨d₂', hd2, hfil⟩ := lift_fil (P.PD K) h5 hO A' hdr c' x' hx'
  obtain ⟨d₁, hd₁, e₁⟩ := hl1 _ hd1
  obtain ⟨d₂, hd₂, e₂⟩ := hl2 _ hd2
  obtain ⟨x, y, c, hy, hx1, hx2, hc, hcx⟩ := connecting (P.PD K) h1 h6 hO A d₁ hd₁ d₂ hd₂
  refine ⟨c, hc, ?_⟩
  rw [← hx1, map_sub, map_φVB] at e₁
  rw [← hx2, map_sub, map_ιV] at e₂
  obtain ⟨v, hv⟩ := GlobalTheory.exists_tmul_one_of_frob_fixed_of_mem_fil_zero (P.PD K) (LL := LL)
    (AlgebraTensorModule.map f (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B) x - x')
    (by rw [map_sub, eq_comm, sub_eq_sub_iff_sub_eq_sub]; exact e₁)
    (by
      have := Submodule.sub_mem _ (map_mem_FilV (P.PD K) f hy) hfil
      rw [← e₂] at this
      rw [map_sub]
      convert this using 1
      abel)
  refine ⟨v, funext fun g => tmul_one_injective (P.PD K) ?_⟩
  have h1 := congrArg (AlgebraTensorModule.map f (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B)) (hcx g)
  rw [map_sub, map_actVB (P.PD K) f hf, AlgebraTensorModule.map_tmul, LinearMap.id_apply] at h1
  have h2 : actVB (P.PD K) A'.ρ g (v ⊗ₜ[ℚ_[l]] (1 : P.R.B)) = A'.ρ g v ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
    simp [actVB]
  change (A'.ρ g v - v) ⊗ₜ[ℚ_[l]] (1 : P.R.B) = (f (c g) - c' g) ⊗ₜ[ℚ_[l]] (1 : P.R.B)
  rw [sub_tmul, sub_tmul, h1, hx', ← h2, ← hv, map_sub]
  abel

/- English proof (translation)
Introduce `D h5 h6 h7 l _ K`. Establish `h1` using `GlobalTheory.FundSeq.surjective_half D l K`. Conclude with `⟨bkADim_of_core _ h1 (h5 l K) (h6 l K) (h7 l K), bkARightExact_of_core (D.locT l) K h1 (h5 l K) (h6 l K)⟩`.
-/
theorem bkADim_and_bkARightExact : ∀ D : D7, LocalSituation.adm5 D → LocalSituation.adm6 D → LocalSituation.adm7 D →
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l),
      LocalSituation.bkADim ((D.loc l).PD K) ∧ LocalSituation.bkARightExact ((D.loc l).PD K) := by
  intro D h5 h6 h7 l _ K
  have h1 := GlobalTheory.FundSeq.surjective_half D l K
  exact ⟨bkADim_of_core _ h1 (h5 l K) (h6 l K) (h7 l K),
    bkARightExact_of_core (D.locT l) K h1 (h5 l K) (h6 l K)⟩

end GlobalTheory.CompanionTheory.BKDim
