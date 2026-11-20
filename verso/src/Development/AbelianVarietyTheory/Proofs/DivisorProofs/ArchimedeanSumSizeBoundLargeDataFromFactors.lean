import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryConjSplitSupportedFiniteAdelicPoi
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetOperatorBoundAtEmbeddingOfComplexOpNormSq

namespace DeltaFormSums
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
noncomputable section
namespace GlobalTheory.CompanionTheory.InfAssembly
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.UG

/- English proof (translation)
Establish `hγ : cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1.1 * V.gram * γ.1.1 = V.gram` using `γ.2`. Establish `hq : GlobalTheory.ConjSplit.ratPt D V γ.1 hγ ∈ GQ V` using `Subgroup.mem_subgroupOf.2 ⟨γ.1, γ.2, rfl⟩`. Set `y` to `GlobalTheory.AdelicU.projFin _ _ (GlobalTheory.ConjSplit.ratPt D V γ.1 hγ)`. Establish `he : Lev.finE V (GlobalTheory.AdelicU.ofFin _ _ y) = Lev.finE V (GlobalTheory.ConjSplit.ratPt D V γ.1 hγ)`. Establish `e : finHom V (GlobalTheory.AdelicU.ofFin _ _ y) = finHom V (GlobalTheory.ConjSplit.ratPt D V γ.1 hγ)` using `congrArg (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram) (GlobalTheory.AdelicU.projFin_ofFin D.sp.cm.sig V.gram y)`.

Conclude with `congrArg (bc (Lev.swapAE D)) e`. Use `⟨⟨GlobalTheory.AdelicU.ofFin _ _ y, GlobalTheory.AdelicU.mem_finPts.2 (GlobalTheory.AdelicU.projInf_ofFin _ _ y)⟩, ⟨_, hq, he.symm⟩, he.trans ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.ConjSplit.finE_ratPt_units D V γ.1 hγ`.
-/
theorem exists_ratFin {D : D7} (V : HSp D) (γ : UR D.sp.cm V.gram) :
    ∃ x' : GfC V, x' ∈ ratFin V ∧ finG V x' = bc (inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) γ.1 := by
  have hγ : cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1.1 * V.gram * γ.1.1 = V.gram := γ.2
  have hq : GlobalTheory.ConjSplit.ratPt D V γ.1 hγ ∈ GQ V := Subgroup.mem_subgroupOf.2 ⟨γ.1, γ.2, rfl⟩
  let y := GlobalTheory.AdelicU.projFin _ _ (GlobalTheory.ConjSplit.ratPt D V γ.1 hγ)
  have he : Lev.finE V (GlobalTheory.AdelicU.ofFin _ _ y) = Lev.finE V (GlobalTheory.ConjSplit.ratPt D V γ.1 hγ) := by
    have e : finHom V (GlobalTheory.AdelicU.ofFin _ _ y) = finHom V (GlobalTheory.ConjSplit.ratPt D V γ.1 hγ) :=
      congrArg (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram) (GlobalTheory.AdelicU.projFin_ofFin D.sp.cm.sig V.gram y)
    exact congrArg (bc (Lev.swapAE D)) e
  refine ⟨⟨GlobalTheory.AdelicU.ofFin _ _ y, GlobalTheory.AdelicU.mem_finPts.2 (GlobalTheory.AdelicU.projInf_ofFin _ _ y)⟩,
    ⟨_, hq, he.symm⟩, he.trans ?_⟩
  exact GlobalTheory.ConjSplit.finE_ratPt_units D V γ.1 hγ

/- English proof (translation)
Break down `Set.eq_empty_or_nonempty {γ : UR D.sp.cm (Xp G).gram | a⁻¹ * ((ratIn G γ)⁻¹ * finG (Xp G) x) ∈ G.Kplus} with h | ⟨γ₀, h₀⟩` into its components or cases. Rewrite using `[h]`. Conclude with `Set.finite_empty`. Use `haveI : Finite {γ : ratFin (Xp G) // finG (Xp G) (x⁻¹ * γ * x) ∈ G.Kplus} := Nat.finite_of_card_ne_zero hx`. Use `choose e he he' using exists_ratFin (Xp G)`.

Establish `hinj : Function.Injective (ratIn G)` using `fun γ γ' h => by haveI : Nontrivial (Formalism.L2.Herm.Af D.host.F) := by`. Take `⟨P, hP⟩` from `Ideal.exists_maximal (𝓞 D.host.F)`. Establish `hne : P ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)`. Conclude with `(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F ⟨P, hP.isPrime, hne⟩).toRingHom.domain_nontrivial`. Use `Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))` and prove the remaining obligations.

Apply `Formalism.UG.P.inclE_injective D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F)` to reduce the goal to its premises. Establish `h2` using `congrArg (fun g : GLf G => g.val i j) h`. Simplify `h2` using `[ratIn, bc]`. Set `f : {γ : UR D.sp.cm (Xp G).gram // a⁻¹ * ((ratIn G γ)⁻¹ * finG (Xp G) x) ∈ G.Kplus} → {γ : ratFin (Xp G) // finG (Xp G) (x⁻¹ * γ * x) ∈ G.Kplus}` to `fun γ => ⟨⟨e (γ₀ * γ.1⁻¹), he _⟩, by`. Establish `h1` using `G.Kplus.mul_mem (G.Kplus.inv_mem h₀) γ.2`.

Establish `e1 : finG (Xp G) (x⁻¹ * e (γ₀ * γ.1⁻¹) * x) = (a⁻¹ * ((ratIn G γ₀)⁻¹ * finG (Xp G) x))⁻¹ * (a⁻¹ * ((ratIn G γ.1)⁻¹ * finG (Xp G) x))`. Establish `e2 : finG (Xp G) (e (γ₀ * γ.1⁻¹)) = ratIn G γ₀ * (ratIn G γ.1)⁻¹`. Rewrite using `[he', ← map_inv, ← map_mul]`. Both sides reduce to the same expression. Rewrite using `[map_mul, map_mul, e2, map_inv]`.

Use `group`. Rewrite using `[e1]`. Conclude with `h1⟩`. Establish `hf : Function.Injective f` using `fun γ γ' h => by`. Establish `h1 : e (γ₀ * γ.1⁻¹) = e (γ₀ * γ'.1⁻¹)` using `congrArg (fun z => (z.1.1 : FinPt G (.top 0))) h`.

Establish `h2` using `congrArg (finG (Xp G)) h1`. Rewrite `h2` using `[he', he']`. Establish `h3 : γ₀ * γ.1⁻¹ = γ₀ * γ'.1⁻¹` using `hinj h2`. Conclude with `Subtype.ext (inv_injective (mul_left_cancel h3))`. Conclude with `Set.finite_coe_iff.1 (Finite.of_injective f hf)`.
-/
theorem delta_fin {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (x : FinPt G (.top 0))
    (hx : gamOrd (Xp G) G.Kplus x ≠ 0) (a : GLf G) :
    {γ : UR D.sp.cm (Xp G).gram | a⁻¹ * ((ratIn G γ)⁻¹ * finG (Xp G) x) ∈ G.Kplus}.Finite := by
  classical
  rcases Set.eq_empty_or_nonempty {γ : UR D.sp.cm (Xp G).gram | a⁻¹ * ((ratIn G γ)⁻¹ * finG (Xp G) x) ∈ G.Kplus} with h | ⟨γ₀, h₀⟩
  · rw [h]; exact Set.finite_empty
  haveI : Finite {γ : ratFin (Xp G) // finG (Xp G) (x⁻¹ * γ * x) ∈ G.Kplus} := Nat.finite_of_card_ne_zero hx
  choose e he he' using exists_ratFin (Xp G)
  have hinj : Function.Injective (ratIn G) := fun γ γ' h => by
    haveI : Nontrivial (Formalism.L2.Herm.Af D.host.F) := by
      obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
      have hne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
      exact (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F ⟨P, hP.isPrime, hne⟩).toRingHom.domain_nontrivial
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    apply Formalism.UG.P.inclE_injective D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F)
    have h2 := congrArg (fun g : GLf G => g.val i j) h
    simpa [ratIn, bc] using h2
  let f : {γ : UR D.sp.cm (Xp G).gram // a⁻¹ * ((ratIn G γ)⁻¹ * finG (Xp G) x) ∈ G.Kplus} →
      {γ : ratFin (Xp G) // finG (Xp G) (x⁻¹ * γ * x) ∈ G.Kplus} := fun γ =>
    ⟨⟨e (γ₀ * γ.1⁻¹), he _⟩, by
      have h1 := G.Kplus.mul_mem (G.Kplus.inv_mem h₀) γ.2
      have e1 : finG (Xp G) (x⁻¹ * e (γ₀ * γ.1⁻¹) * x) = (a⁻¹ * ((ratIn G γ₀)⁻¹ * finG (Xp G) x))⁻¹ *
          (a⁻¹ * ((ratIn G γ.1)⁻¹ * finG (Xp G) x)) := by
        have e2 : finG (Xp G) (e (γ₀ * γ.1⁻¹)) = ratIn G γ₀ * (ratIn G γ.1)⁻¹ := by
          rw [he', ← map_inv, ← map_mul]; rfl
        rw [map_mul, map_mul, e2, map_inv]
        group
      rw [e1]; exact h1⟩
  have hf : Function.Injective f := fun γ γ' h => by
    have h1 : e (γ₀ * γ.1⁻¹) = e (γ₀ * γ'.1⁻¹) := congrArg (fun z => (z.1.1 : FinPt G (.top 0))) h
    have h2 := congrArg (finG (Xp G)) h1
    rw [he', he'] at h2
    have h3 : γ₀ * γ.1⁻¹ = γ₀ * γ'.1⁻¹ := hinj h2
    exact Subtype.ext (inv_injective (mul_left_cancel h3))
  exact Set.finite_coe_iff.1 (Finite.of_injective f hf)

/- English proof (translation)
Unfold `deltaForm`. Rewrite using `[finsum_eq_sum_of_support_subset (s := hA.toFinset)]`. Conclude with `Finset.sum_congr rfl fun γ h => if_pos (hA.mem_toFinset.1 h)`. Introduce `γ h`. Rewrite `h` using `[Function.mem_support]`.

Simplify using `only [Finset.coe_sort_coe, Set.Finite.coe_toFinset]`. Assume the negation of the conclusion as `h'`. Conclude with `h (if_neg h')`.
-/
theorem deltaForm_sum {Γ A K M : Type} [Group Γ] [Group A] [Field K] [AddCommGroup M] [Module K M]
    (ι : Γ →* A) (U : Subgroup A) (ρ : Γ →* Module.End K M) (x g : A) (hA : {γ | x⁻¹ * ((ι γ)⁻¹ * g) ∈ U}.Finite) (v : M) :
    deltaForm ι U ρ x v g = ∑ γ ∈ hA.toFinset, ρ γ v := by
  classical
  unfold deltaForm
  rw [finsum_eq_sum_of_support_subset (s := hA.toFinset)]
  · exact Finset.sum_congr rfl fun γ h => if_pos (hA.mem_toFinset.1 h)
  · intro γ h
    rw [Function.mem_support] at h
    simp only [Finset.coe_sort_coe, Set.Finite.coe_toFinset]
    by_contra h'
    exact h (if_neg h')

/- English proof (translation)
Establish `hA` using `delta_fin G x hx (rp.x cl)`. Establish `e : rp.delta cl (∑ i, w i • b i) (finG (Xp G) x) = ∑ i, w i • rp.delta cl (b i) (finG (Xp G) x)`. Simplify using `only [ClassReps.delta, deltaForm_sum _ _ _ _ _ hA, map_sum, map_smul, Finset.smul_sum]`. Conclude with `Finset.sum_comm`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [psiC, e, map_sum, LinearMap.map_smulₛₗ, Submodule.coe_sum, Submodule.coe_smul]`.
-/
theorem psiC_delta_lin {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (rp : ClassReps G) (cl : G.ClPlus)
    (x : FinPt G (.top 0)) (hx : gamOrd (Xp G) G.Kplus x ≠ 0) {ι : Type} [Fintype ι] (w : ι → D.what₂.LL) (b : ι → WtSp G) :
    psiC (rp.delta cl (∑ i, w i • b i)) x = ∑ i, D.what₂.embLL (w i) • psiC (rp.delta cl (b i)) x := by
  have hA := delta_fin G x hx (rp.x cl)
  have e : rp.delta cl (∑ i, w i • b i) (finG (Xp G) x) = ∑ i, w i • rp.delta cl (b i) (finG (Xp G) x) := by
    simp only [ClassReps.delta, deltaForm_sum _ _ _ _ _ hA, map_sum, map_smul, Finset.smul_sum]
    exact Finset.sum_comm
  apply Subtype.ext
  simp only [psiC, e, map_sum, LinearMap.map_smulₛₗ, Submodule.coe_sum, Submodule.coe_smul]

def RatLe {D : D7} (σ : D.what₂.LL →+* ℂ) (z : ℂ) (r : ℝ) : Prop := ∃ y, D.what₂.embLL y = z ∧ ‖σ y‖ ≤ r

section Rat
variable {D : D7} {σ : D.what₂.LL →+* ℂ}

/- English proof (translation)
The claim follows from `let ⟨y, e, h⟩ := h ⟨y, e, h.trans hr⟩`.
-/
theorem RatLe.mono {z : ℂ} {r r' : ℝ} (h : RatLe σ z r) (hr : r ≤ r') : RatLe σ z r' :=
  let ⟨y, e, h⟩ := h
  ⟨y, e, h.trans hr⟩

/- English proof (translation)
Take `⟨y, e, hy⟩` from `h`. Take `⟨y', e', hy'⟩` from `h'`. Conclude with `⟨y * y', by rw [map_mul, e, e'], by`. Rewrite using `[map_mul, norm_mul]`. Conclude with `mul_le_mul hy hy' (norm_nonneg _) ((norm_nonneg _).trans hy)⟩`.
-/
theorem RatLe.mul {z z' : ℂ} {r r' : ℝ} (h : RatLe σ z r) (h' : RatLe σ z' r') : RatLe σ (z * z') (r * r') := by
  obtain ⟨y, e, hy⟩ := h
  obtain ⟨y', e', hy'⟩ := h'
  exact ⟨y * y', by rw [map_mul, e, e'], by
    rw [map_mul, norm_mul]; exact mul_le_mul hy hy' (norm_nonneg _) ((norm_nonneg _).trans hy)⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨0, by simp, by simp⟩`. Consider the case `insert a s ha ih`. Take `⟨y, e, hy⟩` from `h a (Finset.mem_insert_self _ _)`. Take `⟨y', e', hy'⟩` from `ih fun i hi => h i (Finset.mem_insert_of_mem hi)`.

Use `⟨y + y', by rw [Finset.sum_insert ha, map_add, e, e'], ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.card_insert_of_notMem ha, map_add]`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem RatLe.sum {ι : Type} (s : Finset ι) {z : ι → ℂ} {r : ℝ} (hr : 0 ≤ r) (h : ∀ i ∈ s, RatLe σ (z i) r) :
    RatLe σ (∑ i ∈ s, z i) (s.card * r) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨y, e, hy⟩ := h a (Finset.mem_insert_self _ _)
    obtain ⟨y', e', hy'⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine ⟨y + y', by rw [Finset.sum_insert ha, map_add, e, e'], ?_⟩
    rw [Finset.card_insert_of_notMem ha, map_add]
    push_cast
    calc _ ≤ ‖σ y‖ + ‖σ y'‖ := norm_add_le _ _
      _ ≤ r + s.card * r := add_le_add hy hy'
      _ = _ := by ring

/- English proof (translation)
Use `⟨(n : D.what₂.LL)⁻¹, by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[map_inv₀, map_natCast, norm_inv, Complex.norm_natCast]`. Break down `Nat.eq_zero_or_pos n with rfl | h` into its components or cases. Simplify using the standard rewrite rules. Conclude with `inv_le_one_of_one_le₀ (by exact_mod_cast h)`.
-/
theorem RatLe.nat_inv (n : ℕ) : RatLe σ ((n : ℂ)⁻¹) 1 := by
  refine ⟨(n : D.what₂.LL)⁻¹, by simp, ?_⟩
  rw [map_inv₀, map_natCast, norm_inv, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp
  · exact inv_le_one_of_one_le₀ (by exact_mod_cast h)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨1, by simp, by simp⟩`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha]`. Simplify using `using (h a (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem RatLe.prod_one {ι : Type} (s : Finset ι) {z : ι → ℂ} (h : ∀ i ∈ s, RatLe σ (z i) 1) :
    RatLe σ (∏ i ∈ s, z i) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    simpa using (h a (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Rat

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro _ v B h`. Simplify `h` using `[chainTo]`. Consider the case `succ n ih`.

Introduce `hn v B h`. Use `hk n (by omega) _ _ (ih (by omega) v B h)` as an intermediate fact. Establish `e : Real.exp (((n + 1 : ℕ) : ℝ) * g) * B = Real.exp g * (Real.exp (n * g) * B)`. Rewrite using `[← mul_assoc, ← Real.exp_add]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `this`.
-/
theorem chain_le {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (k : ∀ j, V j →ₗ[ℂ] V (j + 1))
    (P : ∀ j, V j → ℝ → Prop) (g : ℝ) (m : ℕ)
    (hk : ∀ j, j < m → ∀ B v, P j v B → P (j + 1) (k j v) (Real.exp g * B)) :
    ∀ n, n ≤ m → ∀ v B, P 0 v B → P n (chainTo k n v) (Real.exp (n * g) * B) := by
  intro n
  induction n with
  | zero => intro _ v B h; simpa [chainTo] using h
  | succ n ih =>
    intro hn v B h
    have := hk n (by omega) _ _ (ih (by omega) v B h)
    have e : Real.exp (((n + 1 : ℕ) : ℝ) * g) * B = Real.exp g * (Real.exp (n * g) * B) := by
      rw [← mul_assoc, ← Real.exp_add]; congr 2; push_cast; ring
    rw [e]; exact this

section Lin

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} {S : GridChoice W U} {t : T} {Φ : G.Datum}

/- English proof (translation)
Use `haveI := h.cls β`. Use `haveI : Fintype (S.Classes t Φ β) := Fintype.ofFinite _`. Simplify using `only [GridChoice.classSum, finsum_eq_sum_of_fintype, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[hΨ c, map_sum, LinearMap.sum_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, LinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem classSum_lin (h : S.SumOK t Φ) (β : CosFam G t) (τ : PureDat G t →₀ ℂ) {ι : Type} [Fintype ι] (a : ι → ℂ)
    (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (Ψi : ι → FinPt G (.top 0) → VV ℂ (wt G (.top 0)))
    (Fo : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m)))
    (hΨ : ∀ c : S.Classes t Φ β, Ψ (S.ptTop c 0) = ∑ i, a i • Ψi i (S.ptTop c 0)) :
    S.classSum Φ β τ Ψ Fo = ∑ i, a i * S.classSum Φ β τ (Ψi i) Fo := by
  haveI := h.cls β
  haveI : Fintype (S.Classes t Φ β) := Fintype.ofFinite _
  simp only [GridChoice.classSum, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hΨ c, map_sum, LinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Set `τ : CosFam G t → PureDat G t →₀ ℂ` to `fun β => if hβ : β ∈ S.supp t Φ then (h.ex β hβ).choose else 0`. Establish `hτ : ∀ β ∈ S.supp t Φ, S.IsExpansion t Φ β (τ β)` using `fun β hβ => by`. Simplify `(h.ex β hβ).choose_spec` using `[τ, hβ]`. Simplify using `only [h.vCore_eq τ hτ, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun β _ => ?_` and prove the remaining obligations. Rewrite using `[classSum_lin h β (τ β) a Ψ Ψi Fo (hΨ β), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vCore_lin (h : S.SumOK t Φ) {ι : Type} [Fintype ι] (a : ι → ℂ)
    (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (Ψi : ι → FinPt G (.top 0) → VV ℂ (wt G (.top 0)))
    (Fo : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m)))
    (hΨ : ∀ (β : CosFam G t) (c : S.Classes t Φ β), Ψ (S.ptTop c 0) = ∑ i, a i • Ψi i (S.ptTop c 0)) :
    S.vCore t Φ Ψ Fo = ∑ i, a i * S.vCore t Φ (Ψi i) Fo := by
  classical
  let τ : CosFam G t → PureDat G t →₀ ℂ := fun β => if hβ : β ∈ S.supp t Φ then (h.ex β hβ).choose else 0
  have hτ : ∀ β ∈ S.supp t Φ, S.IsExpansion t Φ β (τ β) := fun β hβ => by
    simpa [τ, hβ] using (h.ex β hβ).choose_spec
  simp only [h.vCore_eq τ hτ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [classSum_lin h β (τ β) a Ψ Ψi Fo (hΨ β), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Establish `h1` using `h.gam β c`. Rewrite `h1` using `[GridChoice.invGam]`. Establish `h2` using `(Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul h1)) ⟨0, hm⟩ (Finset.mem_univ _)`. Establish `e : S.ptTop c 0 = (c.1 ⟨0, hm⟩).out`. Simplify using `[GridChoice.ptTop, Function.update_of_ne hm.ne, hm]`.

Rewrite using `[e]`. Introduce `h0`. Apply `h2` to reduce the goal to its premises. Establish `: gamOrd (G.V (.top 0)) (S.levTop t Φ β 0 hm) (c.1 ⟨0, hm⟩).out = 0` using `h0`. Simplify using `[this]`.
-/
theorem gamOrd_ptTop (h : S.SumOK t Φ) (hm : 0 < D.R.m) (β : CosFam G t) (c : S.Classes t Φ β) :
    gamOrd (Xp G) G.Kplus (S.ptTop c 0) ≠ 0 := by
  have h1 := h.gam β c
  rw [GridChoice.invGam] at h1
  have h2 := (Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul h1)) ⟨0, hm⟩ (Finset.mem_univ _)
  have e : S.ptTop c 0 = (c.1 ⟨0, hm⟩).out := by
    simp [GridChoice.ptTop, Function.update_of_ne hm.ne, hm]
  rw [e]
  intro h0
  apply h2
  have : gamOrd (G.V (.top 0)) (S.levTop t Φ β 0 hm) (c.1 ⟨0, hm⟩).out = 0 := h0
  simp [this]

end Lin

/- English proof (translation)
Simplify using `only [vPair]`. Rewrite using `[vCore_lin h (fun i => D.what₂.embLL (w i)) _ (fun i => psiC (ch.rp.delta cl (b i))) _ fun β c => psiC_delta_lin ch.rp cl _ (gamOrd_ptTop h hm β c) w b, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem vPair_delta_lin {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (hm : 0 < D.R.m)
    {Φ : ch.G.Datum} {t : T} (h : ch.S.SumOK t Φ) (cl : ch.G.ClPlus) (u : (R.HX t).H) {ι : Type} [Fintype ι] (w : ι → D.what₂.LL)
    (b : ι → WtSp ch.G) :
    vPair ch.W ch.S t u (ch.rp.delta cl (∑ i, w i • b i)) Φ =
      ∑ i, D.what₂.embLL (w i) * vPair ch.W ch.S t u (ch.rp.delta cl (b i)) Φ := by
  simp only [vPair]
  rw [vCore_lin h (fun i => D.what₂.embLL (w i)) _ (fun i => psiC (ch.rp.delta cl (b i))) _
    fun β c => psiC_delta_lin ch.rp cl _ (gamOrd_ptTop h hm β c) w b, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

section Base

open MvPolynomial Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry

variable {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι]

/- English proof (translation)
Take `⟨Q, hQ⟩` from `bVVfun_int K lam i`. Establish `e1 : map σ (bVVfun K lam i) = map (Int.castRingHom ℂ) Q`. Rewrite using `[hQ, MvPolynomial.map_map]`. Use `congr 2`. Conclude with `RingHom.ext_int _ _`.

Establish `e2 : σ (extNorm K lam) = extNorm ℂ lam`. Rewrite using `[pb_extNorm_eq, pb_extNorm_eq, extNormB, extNormB, map_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← GlobalTheory.Proof.TensorMapDescent.fockB_map, Formalism.L2.DIV.map_extremal]`. Establish `h1 : (map σ).comp (Formalism.GradedWeylDivisibility.blockAct K (n` using `n) fun τ => (G τ)ᵀ).toRingHom = (Formalism.GradedWeylDivisibility.blockAct ℂ (n := n) fun τ => ((G τ).map σ)ᵀ).toRingHom.comp (map σ) := by`.

Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using the standard rewrite rules. Introduce `v`. Simplify using `[blockAct_X]`.

Establish `h2 : ∀ y, map σ (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) y) = Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((G τ).map σ)ᵀ) (map σ y)` using `fun y => congrArg (fun ψ : Pol K ι n →+* Pol ℂ ι n => ψ y) h1`. Establish `h3 : σ (gramTw lam G) = gramTw lam fun τ => (G τ).map σ`. Unfold `gramTw`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Rewrite using `[map_zpow₀, RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[pairK_apply, pairK_apply, pairP_apply, pairP_apply, GlobalTheory.CoefModel.mapVV_coe, GlobalTheory.CoefModel.mapVV_coe, bVV_coe, bVV_coe, fockL_apply, fockL_apply, map_mul, map_div₀, h3, e2, ← h2]`. Use `congr 1`. Rewrite using `[e1, pb_fockS_int, ← e1, GlobalTheory.Proof.TensorMapDescent.fockB_map, hQ, pb_fockS_int]`.
-/
theorem pairK_map_basis {n : ℕ} (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K) (i j : VVIdx lam) :
    pairK lam (fun τ => (G τ).map σ) (GlobalTheory.CoefModel.mapVV σ lam (bVV K lam i)) (GlobalTheory.CoefModel.mapVV σ lam (bVV K lam j)) =
      σ (pairK lam G (bVV K lam i) (bVV K lam j)) := by
  obtain ⟨Q, hQ⟩ := bVVfun_int K lam i
  have e1 : map σ (bVVfun K lam i) = map (Int.castRingHom ℂ) Q := by
    rw [hQ, MvPolynomial.map_map]
    congr 2
    exact RingHom.ext_int _ _
  have e2 : σ (extNorm K lam) = extNorm ℂ lam := by
    rw [pb_extNorm_eq, pb_extNorm_eq, extNormB, extNormB, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← GlobalTheory.Proof.TensorMapDescent.fockB_map, Formalism.L2.DIV.map_extremal]
  have h1 : (map σ).comp (Formalism.GradedWeylDivisibility.blockAct K (n := n) fun τ => (G τ)ᵀ).toRingHom =
      (Formalism.GradedWeylDivisibility.blockAct ℂ (n := n) fun τ => ((G τ).map σ)ᵀ).toRingHom.comp (map σ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro v
      simp [blockAct_X]
  have h2 : ∀ y, map σ (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) y) =
      Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((G τ).map σ)ᵀ) (map σ y) := fun y =>
    congrArg (fun ψ : Pol K ι n →+* Pol ℂ ι n => ψ y) h1
  have h3 : σ (gramTw lam G) = gramTw lam fun τ => (G τ).map σ := by
    unfold gramTw
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, RingHom.map_det]
    rfl
  rw [pairK_apply, pairK_apply, pairP_apply, pairP_apply, GlobalTheory.CoefModel.mapVV_coe, GlobalTheory.CoefModel.mapVV_coe, bVV_coe, bVV_coe,
    fockL_apply, fockL_apply, map_mul, map_div₀, h3, e2, ← h2]
  congr 1
  rw [e1, pb_fockS_int, ← e1, GlobalTheory.Proof.TensorMapDescent.fockB_map, hQ, pb_fockS_int]

end Base

section Ana

/- English proof (translation)
Establish `hc : p.IsComplex` using `IsTotallyComplex.isComplex p`. Establish `hr : ¬ ComplexEmbedding.IsReal p.embedding` using `InfinitePlace.isComplex_iff.1 hc`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, (starRingEnd ℂ) (p.embedding a) ≠ p.embedding a := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hr (RingHom.ext fun x => h x)`. Use `set α := p.embedding a with hα`. Establish `him : α.im ≠ 0` using `fun h0 => ha (Complex.conj_eq_iff_im.2 h0)`. Set `f : ℝ × ℝ → ℂ` to `fun q => (q.1 : ℂ) + (q.2 : ℂ) * α`. Establish `hf : Continuous f` using `by fun_prop`.

Establish `hs : Function.Surjective f` using `fun z => by`. Use `⟨(z.re - z.im / α.im * α.re, z.im / α.im), ?_⟩` and prove the remaining obligations. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[f]`. Simplify using `[f]`.

Clear the denominators using the available nonvanishing facts. Establish `hq : DenseRange (fun q : ℚ × ℚ => ((q.1 : ℝ), (q.2 : ℝ)))` using `Rat.denseRange_cast.prodMap Rat.denseRange_cast`. Establish `h1` using `hs.denseRange.comp hq hf`. Use `Dense.mono ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨q, rfl⟩`.

Use `⟨(q.1 : K) + (q.2 : K) * a, ?_⟩` and prove the remaining obligations. Simplify using `[f, hα]`.
-/
theorem denseRange_embedding {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (p : InfinitePlace K) :
    DenseRange p.embedding := by
  have hc : p.IsComplex := IsTotallyComplex.isComplex p
  have hr : ¬ ComplexEmbedding.IsReal p.embedding := InfinitePlace.isComplex_iff.1 hc
  obtain ⟨a, ha⟩ : ∃ a, (starRingEnd ℂ) (p.embedding a) ≠ p.embedding a := by
    by_contra h
    push_neg at h
    exact hr (RingHom.ext fun x => h x)
  set α := p.embedding a with hα
  have him : α.im ≠ 0 := fun h0 => ha (Complex.conj_eq_iff_im.2 h0)
  let f : ℝ × ℝ → ℂ := fun q => (q.1 : ℂ) + (q.2 : ℂ) * α
  have hf : Continuous f := by fun_prop
  have hs : Function.Surjective f := fun z => by
    refine ⟨(z.re - z.im / α.im * α.re, z.im / α.im), ?_⟩
    apply Complex.ext
    · simp [f]
    · simp [f]; field_simp
  have hq : DenseRange (fun q : ℚ × ℚ => ((q.1 : ℝ), (q.2 : ℝ))) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have h1 := hs.denseRange.comp hq hf
  refine Dense.mono ?_ h1
  rintro _ ⟨q, rfl⟩
  refine ⟨(q.1 : K) + (q.2 : K) * a, ?_⟩
  simp [f, hα]

/- English proof (translation)
Establish `h` using `dense_pi (Set.univ : Set (Fin N)) (s := fun _ => Set.range p.embedding) fun i _ => denseRange_embedding p`. Use `h.mono ?_` and prove the remaining obligations. Introduce `y hy`. Use `choose x hx using fun i => hy i (Set.mem_univ i)`. Conclude with `⟨x, funext hx⟩`.
-/
theorem denseRange_pi {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (p : InfinitePlace K) (N : ℕ) :
    DenseRange (fun (x : Fin N → K) i => p.embedding (x i)) := by
  have h := dense_pi (Set.univ : Set (Fin N)) (s := fun _ => Set.range p.embedding) fun i _ => denseRange_embedding p
  refine h.mono ?_
  intro y hy
  choose x hx using fun i => hy i (Set.mem_univ i)
  exact ⟨x, funext hx⟩

/- English proof (translation)
Rewrite using `[← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]`. Simplify using `only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.conj_mul']`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem star_mul_form {N n : ℕ} (A : Matrix (Fin n) (Fin N) ℂ) (y : Fin N → ℂ) :
    star y ⬝ᵥ ((Aᴴ * A) *ᵥ y) = ((∑ i, ‖(A *ᵥ y) i‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.conj_mul']
  push_cast
  rfl

/- English proof (translation)
Rewrite using `[star_mul_form, Complex.ofReal_re, EuclideanSpace.norm_sq_eq]`.
-/
theorem norm_toLp_sq {N n : ℕ} (A : Matrix (Fin n) (Fin N) ℂ) (y : Fin N → ℂ) :
    ‖(WithLp.toLp 2 (A *ᵥ y) : EuclideanSpace ℂ (Fin n))‖ ^ 2 = (star y ⬝ᵥ ((Aᴴ * A) *ᵥ y)).re := by
  rw [star_mul_form, Complex.ofReal_re, EuclideanSpace.norm_sq_eq]

/- English proof (translation)
Use `set T := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (X'⁻¹ * M * X)) with hT`. It suffices to establish `h1 : ‖T‖ ≤ Real.sqrt B by`. Combine the equalities or inequalities in the displayed calculation. Use `T.opNorm_le_bound (Real.sqrt_nonneg _) fun w => ?_` and prove the remaining obligations. Set `g : (Fin N → ℂ) → EuclideanSpace ℂ (Fin N)` to `fun y => WithLp.toLp 2 (X⁻¹ *ᵥ y)`.

Establish `hXX : X * X⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hX`. Establish `hXX' : X⁻¹ * X = 1` using `Matrix.nonsing_inv_mul _ hX`. Establish `hgc : Continuous g`. Establish `: Continuous fun y : Fin N → ℂ => X⁻¹ *ᵥ y` using `Continuous.matrix_mulVec continuous_const continuous_id`. Conclude with `(PiLp.continuous_toLp 2 _).comp this`.

Establish `hgs : Function.Surjective g` using `fun w => ⟨X *ᵥ w.ofLp, by`. Simplify using `only [g, Matrix.mulVec_mulVec, hXX', Matrix.one_mulVec]⟩`. Establish `hd : DenseRange (g ∘ Subtype.val : S → _)` using `hgs.denseRange.comp hS.denseRange_val hgc`. Establish `hcl : IsClosed {w | ‖T w‖ ≤ Real.sqrt B * ‖w‖}` using `isClosed_le (by fun_prop) (by fun_prop)`. Use `hcl.closure_subset_iff.2 ?_ (hd w)` and prove the remaining obligations.

Introduce and unpack `_ ⟨⟨y, hy⟩, rfl⟩`. Establish `e : T (g y) = WithLp.toLp 2 (X'⁻¹ *ᵥ (M *ᵥ y))`. Simplify using `only [hT, g, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]`. Use `congr 2`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, hXX, Matrix.mul_one]`.

Use `(sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1 ?_` and prove the remaining obligations. Simplify using `only [Function.comp]`. Rewrite using `[e, mul_pow, Real.sq_sqrt hB, norm_toLp_sq]`. Establish `e2 : ‖g y‖ ^ 2 = (star y ⬝ᵥ (((X⁻¹)ᴴ * X⁻¹) *ᵥ y)).re` using `norm_toLp_sq _ _`. Rewrite using `[e2]`.

Conclude with `h y hy`.
-/
theorem opNorm_sq_le {N n : ℕ} {X : Matrix (Fin N) (Fin N) ℂ} {X' : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X.det)
    (M : Matrix (Fin n) (Fin N) ℂ) {B : ℝ} (hB : 0 ≤ B) {S : Set (Fin N → ℂ)} (hS : Dense S)
    (h : ∀ y ∈ S, (star (M *ᵥ y) ⬝ᵥ (((X'⁻¹)ᴴ * X'⁻¹) *ᵥ (M *ᵥ y))).re ≤ B * (star y ⬝ᵥ (((X⁻¹)ᴴ * X⁻¹) *ᵥ y)).re) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (X'⁻¹ * M * X))‖ ^ 2 ≤ B := by
  set T := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (X'⁻¹ * M * X)) with hT
  suffices h1 : ‖T‖ ≤ Real.sqrt B by
    calc ‖T‖ ^ 2 ≤ Real.sqrt B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = B := Real.sq_sqrt hB
  refine T.opNorm_le_bound (Real.sqrt_nonneg _) fun w => ?_
  let g : (Fin N → ℂ) → EuclideanSpace ℂ (Fin N) := fun y => WithLp.toLp 2 (X⁻¹ *ᵥ y)
  have hXX : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv _ hX
  have hXX' : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul _ hX
  have hgc : Continuous g := by
    have : Continuous fun y : Fin N → ℂ => X⁻¹ *ᵥ y := Continuous.matrix_mulVec continuous_const continuous_id
    exact (PiLp.continuous_toLp 2 _).comp this
  have hgs : Function.Surjective g := fun w => ⟨X *ᵥ w.ofLp, by
    simp only [g, Matrix.mulVec_mulVec, hXX', Matrix.one_mulVec]⟩
  have hd : DenseRange (g ∘ Subtype.val : S → _) := hgs.denseRange.comp hS.denseRange_val hgc
  have hcl : IsClosed {w | ‖T w‖ ≤ Real.sqrt B * ‖w‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  refine hcl.closure_subset_iff.2 ?_ (hd w)
  rintro _ ⟨⟨y, hy⟩, rfl⟩
  have e : T (g y) = WithLp.toLp 2 (X'⁻¹ *ᵥ (M *ᵥ y)) := by
    simp only [hT, g, LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
    congr 2
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hXX, Matrix.mul_one]
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1 ?_
  simp only [Function.comp]
  rw [e, mul_pow, Real.sq_sqrt hB, norm_toLp_sq]
  have e2 : ‖g y‖ ^ 2 = (star y ⬝ᵥ (((X⁻¹)ᴴ * X⁻¹) *ᵥ y)).re := norm_toLp_sq _ _
  rw [e2]
  exact h y hy

/- English proof (translation)
Establish `hcl : IsClosed {c : Fin n → ℂ | ‖y ⬝ᵥ c‖ ^ 2 ≤ B * (star c ⬝ᵥ (G *ᵥ c)).re}`. Use `isClosed_le ?_ ?_` and prove the remaining obligations. Conclude with `((continuous_const.dotProduct continuous_id).norm).pow 2`. Conclude with `continuous_const.mul (Complex.continuous_re.comp ((continuous_star).dotProduct (Continuous.matrix_mulVec continuous_const continuous_id)))`. Establish `hall : ∀ c : Fin n → ℂ, ‖y ⬝ᵥ c‖ ^ 2 ≤ B * (star c ⬝ᵥ (G *ᵥ c)).re` using `fun c => hcl.closure_subset_iff.2 h (hS c)`.

Establish `hu : IsUnit (Aᴴ * A).det`. Rewrite using `[Matrix.det_mul, Matrix.det_conjTranspose]`. Conclude with `(hA.star).mul hA`. Establish `hGu : IsUnit G.det`. Rewrite `hu` using `[hG, Matrix.det_transpose]`.

Conclude with `(Matrix.isUnit_nonsing_inv_det_iff).1 hu`. Use `set c := G⁻¹ *ᵥ star y with hc`. Establish `e1 : star y ⬝ᵥ ((Aᴴ * A) *ᵥ y) = y ⬝ᵥ c`. Rewrite using `[hG, Matrix.mulVec_transpose, dotProduct_comm, hc, Matrix.dotProduct_mulVec]`. Establish `e2 : star c ⬝ᵥ (G *ᵥ c) = star (y ⬝ᵥ c)`.

Rewrite using `[hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hGu, Matrix.one_mulVec, ← hc, Matrix.star_dotProduct_star]`. Use `set r : ℝ := ∑ i, ‖(A *ᵥ y) i‖ ^ 2 with hr`. Establish `e3` using `star_mul_form A y`. Establish `hr0 : 0 ≤ r` using `Finset.sum_nonneg fun _ _ => by positivity`. Establish `hs : y ⬝ᵥ c = (r : ℂ)` using `by rw [← e1, e3]`.

Establish `h1` using `hall c`. Rewrite `h1` using `[e2, hs]`. Simplify using `only [Complex.norm_real, Real.norm_eq_abs, sq_abs, RCLike.star_def, Complex.conj_ofReal, Complex.ofReal_re] at h1`. Rewrite using `[e3, Complex.ofReal_re]`. Express the relevant statement in the definitionally equal form `r ≤ B`.

Break down `hr0.eq_or_lt with h0 | h0` into its components or cases. Rewrite using `[← h0]`. Conclude with `hB`. Establish `: r * r ≤ B * r` using `by nlinarith`. Conclude with `le_of_mul_le_mul_right this h0`.
-/
theorem dual_le {n : ℕ} {G A : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A.det) (hG : Aᴴ * A = (G⁻¹)ᵀ) (y : Fin n → ℂ) {B : ℝ} (hB : 0 ≤ B)
    {S : Set (Fin n → ℂ)} (hS : Dense S) (h : ∀ c ∈ S, ‖y ⬝ᵥ c‖ ^ 2 ≤ B * (star c ⬝ᵥ (G *ᵥ c)).re) :
    (star y ⬝ᵥ ((Aᴴ * A) *ᵥ y)).re ≤ B := by
  have hcl : IsClosed {c : Fin n → ℂ | ‖y ⬝ᵥ c‖ ^ 2 ≤ B * (star c ⬝ᵥ (G *ᵥ c)).re} := by
    refine isClosed_le ?_ ?_
    · exact ((continuous_const.dotProduct continuous_id).norm).pow 2
    · exact continuous_const.mul (Complex.continuous_re.comp
        ((continuous_star).dotProduct (Continuous.matrix_mulVec continuous_const continuous_id)))
  have hall : ∀ c : Fin n → ℂ, ‖y ⬝ᵥ c‖ ^ 2 ≤ B * (star c ⬝ᵥ (G *ᵥ c)).re :=
    fun c => hcl.closure_subset_iff.2 h (hS c)
  have hu : IsUnit (Aᴴ * A).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    exact (hA.star).mul hA
  have hGu : IsUnit G.det := by
    rw [hG, Matrix.det_transpose] at hu
    exact (Matrix.isUnit_nonsing_inv_det_iff).1 hu
  set c := G⁻¹ *ᵥ star y with hc
  have e1 : star y ⬝ᵥ ((Aᴴ * A) *ᵥ y) = y ⬝ᵥ c := by
    rw [hG, Matrix.mulVec_transpose, dotProduct_comm, hc, Matrix.dotProduct_mulVec]
  have e2 : star c ⬝ᵥ (G *ᵥ c) = star (y ⬝ᵥ c) := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hGu, Matrix.one_mulVec, ← hc, Matrix.star_dotProduct_star]
  set r : ℝ := ∑ i, ‖(A *ᵥ y) i‖ ^ 2 with hr
  have e3 := star_mul_form A y
  have hr0 : 0 ≤ r := Finset.sum_nonneg fun _ _ => by positivity
  have hs : y ⬝ᵥ c = (r : ℂ) := by rw [← e1, e3]
  have h1 := hall c
  rw [e2, hs] at h1
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, RCLike.star_def, Complex.conj_ofReal, Complex.ofReal_re] at h1
  rw [e3, Complex.ofReal_re]
  change r ≤ B
  rcases hr0.eq_or_lt with h0 | h0
  · rw [← h0]; exact hB
  · have : r * r ≤ B * r := by nlinarith
    exact le_of_mul_le_mul_right this h0

/- English proof (translation)
Establish `hu : IsUnit (Aᴴ * A).det`. Rewrite using `[Matrix.det_mul, Matrix.det_conjTranspose]`. Conclude with `(hA.star).mul hA`. Establish `hGu : IsUnit G.det`. Rewrite `hu` using `[hG, Matrix.det_transpose]`.

Conclude with `(Matrix.isUnit_nonsing_inv_det_iff).1 hu`. Use `set d := G *ᵥ c with hd`. Establish `hcd : G⁻¹ *ᵥ d = c`. Rewrite using `[hd, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hGu, Matrix.one_mulVec]`. Establish `e1` using `star_mul_form A (star d)`.

Rewrite `e1` using `[hG, Matrix.mulVec_transpose, star_star, dotProduct_comm, ← Matrix.dotProduct_mulVec, hcd]`. Establish `e2 : star c ⬝ᵥ d = star (star d ⬝ᵥ c)`. Rewrite using `[← Matrix.star_dotProduct_star, star_star]`. Rewrite using `[e2, e1]`. Simplify using `only [RCLike.star_def, Complex.conj_ofReal, Complex.ofReal_re]`.

Conclude with `Finset.sum_nonneg fun _ _ => by positivity`.
-/
theorem dual_pos {n : ℕ} {G A : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A.det) (hG : Aᴴ * A = (G⁻¹)ᵀ) (c : Fin n → ℂ) :
    0 ≤ (star c ⬝ᵥ (G *ᵥ c)).re := by
  have hu : IsUnit (Aᴴ * A).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    exact (hA.star).mul hA
  have hGu : IsUnit G.det := by
    rw [hG, Matrix.det_transpose] at hu
    exact (Matrix.isUnit_nonsing_inv_det_iff).1 hu
  set d := G *ᵥ c with hd
  have hcd : G⁻¹ *ᵥ d = c := by
    rw [hd, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hGu, Matrix.one_mulVec]
  have e1 := star_mul_form A (star d)
  rw [hG, Matrix.mulVec_transpose, star_star, dotProduct_comm, ← Matrix.dotProduct_mulVec, hcd] at e1
  have e2 : star c ⬝ᵥ d = star (star d ⬝ᵥ c) := by
    rw [← Matrix.star_dotProduct_star, star_star]
  rw [e2, e1]
  simp only [RCLike.star_def, Complex.conj_ofReal, Complex.ofReal_re]
  exact Finset.sum_nonneg fun _ _ => by positivity

end Ana

section Blocks

variable {K : Type} [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type} (σ : K →+* ℂ)
  (lam : ι → DomWeight n) (e : Fin N ≃ C × VVIdx lam) (Gd : ι → Matrix (Fin n) (Fin n) K)

def blk (c : Fin N → ℂ) (b : C) : VV ℂ lam := ∑ k, c (e.symm (b, k)) • GlobalTheory.CoefModel.mapVV σ lam (bVV K lam k)

/- English proof (translation)
Simplify using `[valAt, Module.Basis.equivFun_symm_apply, LinearMap.funLeft_apply]`.
-/
theorem valAt_eq (c : Fin N → K) (b : C) : valAt lam e b c = ∑ k, c (e.symm (b, k)) • bVV K lam k := by
  simp [valAt, Module.Basis.equivFun_symm_apply, LinearMap.funLeft_apply]

/- English proof (translation)
Rewrite using `[valAt_eq, blk, map_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => LinearMap.map_smulₛₗ _ _ _`.
-/
theorem mapVV_valAt (c : Fin N → K) (b : C) :
    GlobalTheory.CoefModel.mapVV σ lam (valAt lam e b c) = blk σ lam e (fun a => σ (c a)) b := by
  rw [valAt_eq, blk, map_sum]
  exact Finset.sum_congr rfl fun k _ => LinearMap.map_smulₛₗ _ _ _

/- English proof (translation)
Use `set m := fun k => GlobalTheory.CoefModel.mapVV σ lam (bVV K lam k) with hm`. Use `set pk := fun k k' => pairK lam (fun τ => (Gd τ).map σ) (m k) (m k') with hpk`. Establish `hM : ∀ a a', ((sumGram lam e Gd).map σ) a a' = if (e a).1 = (e a').1 then pk (e a).2 (e a').2 else 0`. Introduce `a a'`. Simplify using `only [Matrix.map_apply, sumGram, Matrix.of_apply]`.

Use `split_ifs`. Conclude with `(pairK_map_basis σ lam Gd _ _).symm`. Conclude with `map_zero σ`. Establish `hR : ∀ b, pairK lam (fun τ => (Gd τ).map σ) (blk σ lam e c b) (blk σ lam e c b) = ∑ k, ∑ k', star (c (e.symm (b, k))) * (pk k k' * c (e.symm (b, k')))`. Introduce `b`.

Simplify using `only [blk, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, hpk, hm, RingHom.id_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_` and prove the remaining obligations. Simplify using `only [starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [hR, dotProduct, Matrix.mulVec, Pi.star_apply]`. Rewrite using `[← Equiv.sum_comp e.symm, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum]`. Use `congr 1`.

Rewrite using `[← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_eq_single b]`. Use `Finset.sum_congr rfl fun k' _ => ?_` and prove the remaining obligations. Rewrite using `[hM]`. Simplify using the standard rewrite rules. Introduce `b' _ hb`.

Use `Finset.sum_eq_zero fun k' _ => ?_` and prove the remaining obligations. Rewrite using `[hM]`. Simplify using `[hb.symm]`. Simplify using the standard rewrite rules.
-/
theorem form_eq [Fintype C] (c : Fin N → ℂ) :
    star c ⬝ᵥ (((sumGram lam e Gd).map σ) *ᵥ c) =
      ∑ b, pairK lam (fun τ => (Gd τ).map σ) (blk σ lam e c b) (blk σ lam e c b) := by
  classical
  set m := fun k => GlobalTheory.CoefModel.mapVV σ lam (bVV K lam k) with hm
  set pk := fun k k' => pairK lam (fun τ => (Gd τ).map σ) (m k) (m k') with hpk
  have hM : ∀ a a', ((sumGram lam e Gd).map σ) a a' = if (e a).1 = (e a').1 then pk (e a).2 (e a').2 else 0 := by
    intro a a'
    simp only [Matrix.map_apply, sumGram, Matrix.of_apply]
    split_ifs
    · exact (pairK_map_basis σ lam Gd _ _).symm
    · exact map_zero σ
  have hR : ∀ b, pairK lam (fun τ => (Gd τ).map σ) (blk σ lam e c b) (blk σ lam e c b) =
      ∑ k, ∑ k', star (c (e.symm (b, k))) * (pk k k' * c (e.symm (b, k'))) := by
    intro b
    simp only [blk, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, hpk, hm,
      RingHom.id_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
    simp only [starRingEnd_apply]
    ring
  simp only [hR, dotProduct, Matrix.mulVec, Pi.star_apply]
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun k' _ => ?_
    rw [hM]
    simp
  · intro b' _ hb
    refine Finset.sum_eq_zero fun k' _ => ?_
    rw [hM]
    simp [hb.symm]
  · simp

/- English proof (translation)
Establish `h` using `hp fun a => if (e a).1 = b then c a else 0`. Rewrite `h` using `[form_eq, Finset.sum_eq_single b]`. Establish `e1 : blk σ lam e (fun a => if (e a).1 = b then c a else 0) b = blk σ lam e c b` using `Finset.sum_congr rfl fun k _ => by simp`. Rewrite `h` using `[e1]`. Conclude with `h`.

Introduce `b' _ hb`. Establish `e1 : blk σ lam e (fun a => if (e a).1 = b then c a else 0) b' = 0` using `Finset.sum_eq_zero fun k _ => by simp [hb]`. Rewrite using `[e1]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem nrm_blk_nonneg [Fintype C] (hp : ∀ c : Fin N → ℂ, 0 ≤ (star c ⬝ᵥ (((sumGram lam e Gd).map σ) *ᵥ c)).re) (c : Fin N → ℂ) (b : C) :
    0 ≤ (pairK lam (fun τ => (Gd τ).map σ) (blk σ lam e c b) (blk σ lam e c b)).re := by
  classical
  have h := hp fun a => if (e a).1 = b then c a else 0
  rw [form_eq, Finset.sum_eq_single b] at h
  · have e1 : blk σ lam e (fun a => if (e a).1 = b then c a else 0) b = blk σ lam e c b :=
      Finset.sum_congr rfl fun k _ => by simp
    rw [e1] at h
    exact h
  · intro b' _ hb
    have e1 : blk σ lam e (fun a => if (e a).1 = b then c a else 0) b' = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hb]
    rw [e1]; simp
  · simp

end Blocks

section Place

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

/- English proof (translation)
Simplify using `only [GridChoice.pairAt, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun d _ => rfl`.
-/
theorem pairAt_apply {Φ : ch.G.Datum} {t : T} {β : CosFam ch.G t} (τ : PureDat ch.G t →₀ ℂ) (c : ch.S.Classes t Φ β) (u v) :
    ch.S.pairAt τ c u v = ∑ d ∈ τ.support, τ d * lastPair ch.G (ch.S.colMap d (ch.S.ptTop c) u) (ch.S.rowMap d (ch.S.ptRow c) v) := by
  simp only [GridChoice.pairAt, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun d _ => rfl

/- English proof (translation)
Establish `hex : ∀ β ∈ ch.S.supp A.μ0 Φ, ∃ τ, IsCosetExpansion ch.S.toGridChoice A.μ0 Φ β (expDepth ch.S.toGridChoice A.μ0 Φ β) τ` using `fun β hβ => (hD A.μ0 Φ β hβ).1`. Set `τ : CosFam ch.G A.μ0 → PureDat ch.G A.μ0 →₀ ℂ` to `fun β => if h : β ∈ ch.S.supp A.μ0 Φ then (hex β h).choose else 0`. Establish `hτ : ∀ β (h : β ∈ ch.S.supp A.μ0 Φ), IsCosetExpansion ch.S.toGridChoice A.μ0 Φ β (expDepth ch.S.toGridChoice A.μ0 Φ β) (τ β)` using `fun β h => by simpa [τ, h] using (hex β h).choose_spec`. Rewrite using `[hOK.vCore_eq τ fun β h => (hτ β h).2.1]`. Establish `hcard : ((hOK.fin.toFinset.card : ℕ) : ℝ) ≤ nB`.

Rewrite using `[← Set.ncard_eq_toFinset_card _ hOK.fin]`. Conclude with `hB`. Establish `hnn : 0 ≤ nC * (nD * (rT * rP))` using `mul_nonneg hnC (mul_nonneg hnD (mul_nonneg hrT hrP))`. Use `(RatLe.sum _ hnn fun β hβ => ?_).mono (mul_le_mul_of_nonneg_right hcard hnn)` and prove the remaining obligations. Establish `hβ' : β ∈ ch.S.supp A.μ0 Φ` using `hOK.fin.mem_toFinset.1 hβ`.

Use `haveI := hOK.cls β`. Use `haveI : Fintype (ch.S.Classes A.μ0 Φ β) := Fintype.ofFinite _`. Establish `hcc : ((Finset.univ : Finset (ch.S.Classes A.μ0 Φ β)).card : ℝ) ≤ nC`. Rewrite using `[Finset.card_univ, ← Nat.card_eq_fintype_card]`. Conclude with `hC β hβ'`.

Establish `hnn' : 0 ≤ nD * (rT * rP)` using `mul_nonneg hnD (mul_nonneg hrT hrP)`. Rewrite using `[GridChoice.classSum, finsum_eq_sum_of_fintype, Finset.mul_sum]`. Use `(RatLe.sum _ hnn' fun c _ => ?_).mono (mul_le_mul_of_nonneg_right hcc hnn')` and prove the remaining obligations. Rewrite using `[pairAt_apply, Finset.mul_sum, Finset.mul_sum]`. Establish `hrr : 0 ≤ rT * rP` using `mul_nonneg hrT hrP`.

Use `(RatLe.sum _ hrr fun d hd => ?_).mono (mul_le_mul_of_nonneg_right (hN β hβ' _ (hτ β hβ')) hrr)` and prove the remaining obligations. Take `⟨x, y, e⟩` from `(hτ β hβ').coef_eq hd`. Establish `hg : RatLe σ (ch.S.invGam c) 1`. Rewrite using `[GridChoice.invGam, ← one_mul (1 : ℝ)]`. Conclude with `RatLe.mul (RatLe.prod_one _ fun _ _ => RatLe.nat_inv _) (RatLe.prod_one _ fun _ _ => RatLe.nat_inv _)`.

Use `(hg.mul ((hT β hβ' x y).mul (hP β d ⟨hβ', _, hτ β hβ', hd⟩ c)))` as an intermediate fact. Rewrite `this` using `[one_mul]`. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vCore_ratLe {σ : D.what₂.LL →+* ℂ} {Φ : ch.G.Datum} (hOK : ch.S.SumOK A.μ0 Φ) (hD : DepthAt ch)
    (Ψ : FinPt ch.G (.top 0) → VV ℂ (wt ch.G (.top 0))) (Fo : FinPt ch.G (.grid 0 D.R.m) → VV ℂ (listedWt ch.G (.grid 0 D.R.m)))
    {nB nC nD rT rP : ℝ} (hrT : 0 ≤ rT) (hrP : 0 ≤ rP) (hnC : 0 ≤ nC) (hnD : 0 ≤ nD)
    (hB : ((ch.S.supp A.μ0 Φ).ncard : ℝ) ≤ nB)
    (hC : ∀ β ∈ ch.S.supp A.μ0 Φ, (Nat.card (ch.S.Classes A.μ0 Φ β) : ℝ) ≤ nC)
    (hN : ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ τ, IsCosetExpansion ch.S.toGridChoice A.μ0 Φ β (expDepth ch.S.toGridChoice A.μ0 Φ β) τ →
      (τ.support.card : ℝ) ≤ nD)
    (hT : ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ x y, RatLe σ ((∏ v, ((ch.S.term A.μ0 Φ β v).coef : ℂ)) *
      ∏ v, (ch.S.term A.μ0 Φ β v).datum (ch.S.colAt A.μ0 v x) (ch.S.rowAt A.μ0 v y)) rT)
    (hP : ∀ β, ∀ d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ c : ch.S.Classes A.μ0 Φ β,
      RatLe σ (lastPair ch.G (ch.S.colMap d (ch.S.ptTop c) (Ψ (ch.S.ptTop c 0))) (ch.S.rowMap d (ch.S.ptRow c) (Fo (ch.S.ptRow c 0)))) rP) :
    RatLe σ (ch.S.vCore A.μ0 Φ Ψ Fo) (nB * (nC * (nD * (rT * rP)))) := by
  classical
  have hex : ∀ β ∈ ch.S.supp A.μ0 Φ, ∃ τ, IsCosetExpansion ch.S.toGridChoice A.μ0 Φ β (expDepth ch.S.toGridChoice A.μ0 Φ β) τ :=
    fun β hβ => (hD A.μ0 Φ β hβ).1
  let τ : CosFam ch.G A.μ0 → PureDat ch.G A.μ0 →₀ ℂ := fun β => if h : β ∈ ch.S.supp A.μ0 Φ then (hex β h).choose else 0
  have hτ : ∀ β (h : β ∈ ch.S.supp A.μ0 Φ), IsCosetExpansion ch.S.toGridChoice A.μ0 Φ β (expDepth ch.S.toGridChoice A.μ0 Φ β) (τ β) :=
    fun β h => by simpa [τ, h] using (hex β h).choose_spec
  rw [hOK.vCore_eq τ fun β h => (hτ β h).2.1]
  have hcard : ((hOK.fin.toFinset.card : ℕ) : ℝ) ≤ nB := by
    rw [← Set.ncard_eq_toFinset_card _ hOK.fin]; exact hB
  have hnn : 0 ≤ nC * (nD * (rT * rP)) := mul_nonneg hnC (mul_nonneg hnD (mul_nonneg hrT hrP))
  refine (RatLe.sum _ hnn fun β hβ => ?_).mono (mul_le_mul_of_nonneg_right hcard hnn)
  have hβ' : β ∈ ch.S.supp A.μ0 Φ := hOK.fin.mem_toFinset.1 hβ
  haveI := hOK.cls β
  haveI : Fintype (ch.S.Classes A.μ0 Φ β) := Fintype.ofFinite _
  have hcc : ((Finset.univ : Finset (ch.S.Classes A.μ0 Φ β)).card : ℝ) ≤ nC := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hC β hβ'
  have hnn' : 0 ≤ nD * (rT * rP) := mul_nonneg hnD (mul_nonneg hrT hrP)
  rw [GridChoice.classSum, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine (RatLe.sum _ hnn' fun c _ => ?_).mono (mul_le_mul_of_nonneg_right hcc hnn')
  rw [pairAt_apply, Finset.mul_sum, Finset.mul_sum]
  have hrr : 0 ≤ rT * rP := mul_nonneg hrT hrP
  refine (RatLe.sum _ hrr fun d hd => ?_).mono (mul_le_mul_of_nonneg_right (hN β hβ' _ (hτ β hβ')) hrr)
  obtain ⟨x, y, e⟩ := (hτ β hβ').coef_eq hd
  have hg : RatLe σ (ch.S.invGam c) 1 := by
    rw [GridChoice.invGam, ← one_mul (1 : ℝ)]
    exact RatLe.mul (RatLe.prod_one _ fun _ _ => RatLe.nat_inv _) (RatLe.prod_one _ fun _ _ => RatLe.nat_inv _)
  have := (hg.mul ((hT β hβ' x y).mul (hP β d ⟨hβ', _, hτ β hβ', hd⟩ c)))
  rw [one_mul] at this
  convert this using 1
  rw [e]; ring

/- English proof (translation)
Establish `h1` using `chain_le (V := fun j => VV ℂ (wt ch.G (.top j))) (fun j => if h : j < D.R.m then ch.S.Z.kkMap 1 (d.1 ⟨j, h⟩) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) else 0) (fun j v B => NrmLe _ p.embedding v B) (g p) D.R.m (fun j hj B v h => by`. Simplify using `only [dif_pos hj]`. Conclude with `hg p Φ β d hd c ⟨j, hj⟩ B v h) D.R.m le_rfl _ Bu hu`. Establish `h2` using `chain_le (V := fun i => VV ℂ (wt ch.G (.grid i D.R.m))) (fun i => if h : i < D.R.m then ch.S.Z.kkMap 1 (d.2 ⟨i, h⟩) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) else 0) (fun j v B => NrmLe _ p.embedding v B) (g' p) D.R.m (fun j hj B v h => by`. Simplify using `only [dif_pos hj]`.

Conclude with `hg' p Φ β d hd c ⟨j, hj⟩ B v h) D.R.m le_rfl _ Bf hv`. Take `⟨y, e, hy⟩` from `hP p.embedding _ _ _ _ h1 h2`. Conclude with `⟨y, e, Real.le_sqrt_of_sq_le hy⟩`.
-/
theorem pair_ratLe (C b : ℝ) (p : InfinitePlace D.what₂.LL) {g g' : InfinitePlace D.what₂.LL → ℝ} {Φ : ch.G.Datum} {β : CosFam ch.G A.μ0}
    {d : PureDat ch.G A.μ0} (hd : Occurs ch.S.toGridChoice A.μ0 Φ β d) (c : ch.S.Classes A.μ0 Φ β)
    (hg : ∀ (p : InfinitePlace D.what₂.LL) Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (j : Fin D.R.m) B v,
      NrmLe _ p.embedding v B →
        NrmLe _ p.embedding (ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) v) (Real.exp (g p) * B))
    (hg' : ∀ (p : InfinitePlace D.what₂.LL) Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (i : Fin D.R.m) B v,
      NrmLe _ p.embedding v B →
        NrmLe _ p.embedding (ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) v) (Real.exp (g' p) * B))
    (hP : InfPairAt ch C b) {u v} {Bu Bf : ℝ}
    (hu : NrmLe _ p.embedding (rhoVr (tauE D) _ (ch.S.N.fr (.top 0))⁻¹ u) Bu)
    (hv : NrmLe _ p.embedding (rhoVr (tauE D) _ (ch.S.N.fr (.grid 0 D.R.m))⁻¹ (funOf (listedWt ch.G (.grid 0 D.R.m)) v)) Bf) :
    RatLe p.embedding (lastPair ch.G (ch.S.colMap d (ch.S.ptTop c) u) (ch.S.rowMap d (ch.S.ptRow c) v))
      (Real.sqrt (Real.exp (aOne ch.G C b) * (Real.exp (D.R.m * g p) * Bu) * (Real.exp (D.R.m * g' p) * Bf))) := by
  have h1 := chain_le (V := fun j => VV ℂ (wt ch.G (.top j)))
    (fun j => if h : j < D.R.m then ch.S.Z.kkMap 1 (d.1 ⟨j, h⟩) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) else 0)
    (fun j v B => NrmLe _ p.embedding v B) (g p) D.R.m
    (fun j hj B v h => by
      simp only [dif_pos hj]
      exact hg p Φ β d hd c ⟨j, hj⟩ B v h) D.R.m le_rfl _ Bu hu
  have h2 := chain_le (V := fun i => VV ℂ (wt ch.G (.grid i D.R.m)))
    (fun i => if h : i < D.R.m then ch.S.Z.kkMap 1 (d.2 ⟨i, h⟩) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) else 0)
    (fun j v B => NrmLe _ p.embedding v B) (g' p) D.R.m
    (fun j hj B v h => by
      simp only [dif_pos hj]
      exact hg' p Φ β d hd c ⟨j, hj⟩ B v h) D.R.m le_rfl _ Bf hv
  obtain ⟨y, e, hy⟩ := hP p.embedding _ _ _ _ h1 h2
  exact ⟨y, e, Real.le_sqrt_of_sq_le hy⟩

/- English proof (translation)
Establish `h1` using `vCore_ratLe ch (σ := p.embedding) hOK hD (psiC Ψ) (ch.S.formC A.μ0 u) (nB := Real.exp (D.R.m * aOne ch.G C b)) (nC := Real.exp (D.R.m * aOne ch.G C b)) (nD := Real.exp (D.R.m * aOne ch.G C b)) (rT := Real.exp (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * sig ch.G)) (rP := Real.sqrt ( …`. Conclude with `(RatLe.mul (hS p.embedding) h1)`.
-/
theorem vPair_ratLe (C b : ℝ) (hA : 0 ≤ D.R.m * aOne ch.G C b) (p : InfinitePlace D.what₂.LL) {g g' : InfinitePlace D.what₂.LL → ℝ} {Φ : ch.G.Datum}
    (hOK : ch.S.SumOK A.μ0 Φ) (hD : DepthAt ch) (hS : InfScalAt ch C b) (hT : InfTensAt ch C) (hN : InfCountAt ch C b)
    (hC : InfClassAt ch C b)
    (hg : ∀ (p : InfinitePlace D.what₂.LL) Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (j : Fin D.R.m) B v,
      NrmLe _ p.embedding v B →
        NrmLe _ p.embedding (ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) v) (Real.exp (g p) * B))
    (hg' : ∀ (p : InfinitePlace D.what₂.LL) Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (i : Fin D.R.m) B v,
      NrmLe _ p.embedding v B →
        NrmLe _ p.embedding (ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) v) (Real.exp (g' p) * B))
    (hP : InfPairAt ch C b) (Ψ : GLf ch.G → WtSp ch.G) (u : (R.HX A.μ0).H) {Bu Bf : ℝ}
    (hu : ∀ x, NrmLe _ p.embedding (topVal ch.S.toGridChoice Ψ x) Bu)
    (hv : ∀ y, NrmLe _ p.embedding (rowVal ch.S.toGridChoice (ch.S.formC A.μ0 u y)) Bf) :
    RatLe p.embedding (vPair ch.W ch.S A.μ0 u Ψ Φ) (Real.exp (D.R.m * aOne ch.G C b) * (Real.exp (D.R.m * aOne ch.G C b) *
      (Real.exp (D.R.m * aOne ch.G C b) * (Real.exp (D.R.m * aOne ch.G C b) * (Real.exp (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * sig ch.G) *
        Real.sqrt (Real.exp (aOne ch.G C b) * (Real.exp (D.R.m * g p) * Bu) * (Real.exp (D.R.m * g' p) * Bf))))))) := by
  have h1 := vCore_ratLe ch (σ := p.embedding) hOK hD (psiC Ψ) (ch.S.formC A.μ0 u)
    (nB := Real.exp (D.R.m * aOne ch.G C b)) (nC := Real.exp (D.R.m * aOne ch.G C b)) (nD := Real.exp (D.R.m * aOne ch.G C b))
    (rT := Real.exp (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * sig ch.G))
    (rP := Real.sqrt (Real.exp (aOne ch.G C b) * (Real.exp (D.R.m * g p) * Bu) * (Real.exp (D.R.m * g' p) * Bf)))
    (Real.exp_pos _).le (Real.sqrt_nonneg _) (Real.exp_pos _).le (Real.exp_pos _).le
    (hN.2 Φ).1 (hC.2 Φ) (hN.2 Φ).2 (fun β hβ x y => hT p.embedding Φ β hβ x y)
    (fun β d hd c => pair_ratLe ch C b p hd c hg hg' hP (hu _) (hv _))
  exact (RatLe.mul (hS p.embedding) h1)

end Place

end GlobalTheory.CompanionTheory.InfAssembly

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
noncomputable section
namespace GlobalTheory.CompanionTheory.InfAssembly
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.UG

section Place

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply]`. Simplify using `[Matrix.mulVec_single, Pi.basisFun_apply]`.
-/
theorem toMatrix_basis {K : Type} [Field K] {N n : ℕ} (V : Matrix (Fin n) (Fin N) K) :
    LinearMap.toMatrix (Pi.basisFun K (Fin N)) (Pi.basisFun K (Fin n)) V.mulVecLin = V := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp [Matrix.mulVec_single, Pi.basisFun_apply]

/- English proof (translation)
Use `set σ := p.embedding with hσ`. Use `set ea := Real.exp (D.R.m * aOne ch.G C sb) with hea`. Use `set es := Real.exp (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * sig ch.G) with hes`. Use `set e1 := Real.exp (aOne ch.G C sb) with he1`. Use `set eg := Real.exp (D.R.m * g p) with heg`.

Use `set eg' := Real.exp (D.R.m * g' p) with heg'`. Establish `hea0 : 0 < ea` using `Real.exp_pos _`. Establish `hes0 : 0 < es` using `Real.exp_pos _`. Establish `he10 : 0 < e1` using `Real.exp_pos _`. Establish `heg0 : 0 < eg` using `Real.exp_pos _`.

Establish `heg'0 : 0 < eg'` using `Real.exp_pos _`. Break down `isEmpty_or_nonempty (Fin ch.n) with h0 | ⟨⟨a0⟩⟩` into its components or cases. Simplify using `[dotProduct]`. Use `set k0 := (ch.e a0).2 with hk0`. Use `haveI : Finite (TestIx ch.G) := Finite.of_injective (fun b => ch.e.symm (b, k0)) fun b b' h => by`.

Simplify using `using h`. Use `letI : Fintype (TestIx ch.G) := Fintype.ofFinite _`. Use `set nb : TestIx ch.G → ℝ := fun b => nrm (LaP ch.G) (fun τ => (gramKd (emb D) (Xp ch.G).gram τ).map σ) (GlobalTheory.CoefModel.mapVV σ _ (valAt (LaP ch.G) ch.e b c)) with hnb`. Establish `hnb0 : ∀ b, 0 ≤ nb b` using `fun b => by`. Simplify using `only [hnb, nrm, mapVV_valAt]`.

Conclude with `nrm_blk_nonneg σ (LaP ch.G) ch.e _ hp _ b`. Establish `hsum : ∑ b, nb b = (star (fun a => σ (c a)) ⬝ᵥ (((formGram ch.G ch.e).map σ) *ᵥ fun a => σ (c a))).re`. Rewrite using `[formGram, form_eq, Complex.re_sum]`. Conclude with `Finset.sum_congr rfl fun b _ => by simp only [hnb, nrm, mapVV_valAt]`. Establish `hb : ∀ b, ∃ z : D.what₂.LL, z = (∑ k, c (ch.e.symm (b, k)) * yv (ch.e.symm (b, k))) ∧ ‖σ z‖ ^ 2 ≤ (ea ^ 8 * es ^ 2 * e1 * eg * eg') * Bf * nb b`.

Introduce `b`. Establish `hOKb : ch.S.SumOK A.μ0 b.1`. Use `hOK (ch.e.symm (b, k0))` as an intermediate fact. Simplify `this` using `[Choice.Phi, datumOf]`. Take `⟨z, ez, hz⟩` from `vPair_ratLe ch C sb hA p hOKb hD hS hT hN hC hg hg' hP (ch.rp.delta b.2 (valAt (LaP ch.G) ch.e b c)) u (Bu := nb b) (Bf := Bf) (fun x => hPsi σ b.2 _ x) hv`.

Use `⟨z, ?_, ?_⟩` and prove the remaining obligations. Apply `D.what₂.embLL.injective` to reduce the goal to its premises. Rewrite using `[ez, valAt_eq, vPair_delta_lin ch hm hOKb b.2 u, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hy]`.

Simplify using the standard rewrite rules. Establish `hin : 0 ≤ e1 * (eg * nb b) * (eg' * Bf)`. Use `hnb0 b` as an intermediate fact. Check the signs of the components of the expression. Establish `hz2 : ‖σ z‖ ≤ ea * (ea * (ea * (ea * (es * Real.sqrt (e1 * (eg * nb b) * (eg' * Bf))))))` using `hz`.

Use `(pow_le_pow_left₀ (norm_nonneg _) hz2 2).trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using `only [mul_pow, Real.sq_sqrt hin]`. Expand and normalize the polynomial expressions, which then agree. Use `choose z hz hz' using hb`. Establish `hdot : (fun a => σ (yv a)) ⬝ᵥ (fun a => σ (c a)) = ∑ b, σ (z b)`.

Simplify using `only [dotProduct]`. Rewrite using `[← Equiv.sum_comp ch.e.symm, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[hz, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, mul_comm]`. Establish `hcard : (Fintype.card (TestIx ch.G) : ℝ) ≤ ea * ea`. Rewrite using `[← Nat.card_eq_fintype_card, Nat.card_prod]`. Use `push_cast`. Conclude with `mul_le_mul hN.1 hC.1 (by positivity) hea0.le`.

Establish `hE : 0 ≤ ea ^ 8 * es ^ 2 * e1 * eg * eg'` using `by positivity`. Rewrite using `[hdot, ← hsum]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem test_bound (C sb : ℝ) (hm : 0 < D.R.m) (hA : 0 ≤ D.R.m * aOne ch.G C sb) (p : InfinitePlace D.what₂.LL)
    {g g' : InfinitePlace D.what₂.LL → ℝ}
    (hOK : ∀ a, ch.S.SumOK A.μ0 (ch.Phi a)) (hD : DepthAt ch) (hS : InfScalAt ch C sb) (hT : InfTensAt ch C) (hN : InfCountAt ch C sb)
    (hC : InfClassAt ch C sb)
    (hg : ∀ (p : InfinitePlace D.what₂.LL) Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (j : Fin D.R.m) B v,
      NrmLe _ p.embedding v B →
        NrmLe _ p.embedding (ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) v) (Real.exp (g p) * B))
    (hg' : ∀ (p : InfinitePlace D.what₂.LL) Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (i : Fin D.R.m) B v,
      NrmLe _ p.embedding v B →
        NrmLe _ p.embedding (ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) v) (Real.exp (g' p) * B))
    (hP : InfPairAt ch C sb) (hPsi : InfPsiAt ch)
    (hp : ∀ c : Fin ch.n → ℂ, 0 ≤ (star c ⬝ᵥ (((formGram ch.G ch.e).map p.embedding) *ᵥ c)).re)
    (u : (R.HX A.μ0).H) {Bf : ℝ} (hBf : 0 ≤ Bf)
    (hv : ∀ y, NrmLe _ p.embedding (rowVal ch.S.toGridChoice (ch.S.formC A.μ0 u y)) Bf)
    (yv : Fin ch.n → D.what₂.LL)
    (hy : ∀ a, D.what₂.embLL (yv a) = vPair ch.W ch.S A.μ0 u (ch.rp.delta (ch.e a).1.2 (bVV D.what₂.LL (LaP ch.G) (ch.e a).2)) (ch.e a).1.1)
    (c : Fin ch.n → D.what₂.LL) :
    ‖(fun a => p.embedding (yv a)) ⬝ᵥ (fun a => p.embedding (c a))‖ ^ 2 ≤
      (Real.exp (D.R.m * aOne ch.G C sb) ^ 10 * Real.exp (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * sig ch.G) ^ 2 * Real.exp (aOne ch.G C sb) *
        Real.exp (D.R.m * g p) * Real.exp (D.R.m * g' p)) * Bf *
        (star (fun a => p.embedding (c a)) ⬝ᵥ (((formGram ch.G ch.e).map p.embedding) *ᵥ fun a => p.embedding (c a))).re := by
  classical
  set σ := p.embedding with hσ
  set ea := Real.exp (D.R.m * aOne ch.G C sb) with hea
  set es := Real.exp (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * sig ch.G) with hes
  set e1 := Real.exp (aOne ch.G C sb) with he1
  set eg := Real.exp (D.R.m * g p) with heg
  set eg' := Real.exp (D.R.m * g' p) with heg'
  have hea0 : 0 < ea := Real.exp_pos _
  have hes0 : 0 < es := Real.exp_pos _
  have he10 : 0 < e1 := Real.exp_pos _
  have heg0 : 0 < eg := Real.exp_pos _
  have heg'0 : 0 < eg' := Real.exp_pos _
  rcases isEmpty_or_nonempty (Fin ch.n) with h0 | ⟨⟨a0⟩⟩
  · simp [dotProduct]
  set k0 := (ch.e a0).2 with hk0
  haveI : Finite (TestIx ch.G) := Finite.of_injective (fun b => ch.e.symm (b, k0)) fun b b' h => by
    simpa using h
  letI : Fintype (TestIx ch.G) := Fintype.ofFinite _
  set nb : TestIx ch.G → ℝ := fun b => nrm (LaP ch.G) (fun τ => (gramKd (emb D) (Xp ch.G).gram τ).map σ)
    (GlobalTheory.CoefModel.mapVV σ _ (valAt (LaP ch.G) ch.e b c)) with hnb
  have hnb0 : ∀ b, 0 ≤ nb b := fun b => by
    simp only [hnb, nrm, mapVV_valAt]
    exact nrm_blk_nonneg σ (LaP ch.G) ch.e _ hp _ b
  have hsum : ∑ b, nb b = (star (fun a => σ (c a)) ⬝ᵥ (((formGram ch.G ch.e).map σ) *ᵥ fun a => σ (c a))).re := by
    rw [formGram, form_eq, Complex.re_sum]
    exact Finset.sum_congr rfl fun b _ => by simp only [hnb, nrm, mapVV_valAt]
  have hb : ∀ b, ∃ z : D.what₂.LL, z = (∑ k, c (ch.e.symm (b, k)) * yv (ch.e.symm (b, k))) ∧
      ‖σ z‖ ^ 2 ≤ (ea ^ 8 * es ^ 2 * e1 * eg * eg') * Bf * nb b := by
    intro b
    have hOKb : ch.S.SumOK A.μ0 b.1 := by
      have := hOK (ch.e.symm (b, k0))
      simpa [Choice.Phi, datumOf] using this
    obtain ⟨z, ez, hz⟩ := vPair_ratLe ch C sb hA p hOKb hD hS hT hN hC hg hg' hP (ch.rp.delta b.2 (valAt (LaP ch.G) ch.e b c)) u
      (Bu := nb b) (Bf := Bf) (fun x => hPsi σ b.2 _ x) hv
    refine ⟨z, ?_, ?_⟩
    · apply D.what₂.embLL.injective
      rw [ez, valAt_eq, vPair_delta_lin ch hm hOKb b.2 u, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, hy]
      simp
    · have hin : 0 ≤ e1 * (eg * nb b) * (eg' * Bf) := by
        have := hnb0 b
        positivity
      have hz2 : ‖σ z‖ ≤ ea * (ea * (ea * (ea * (es * Real.sqrt (e1 * (eg * nb b) * (eg' * Bf)))))) := hz
      refine (pow_le_pow_left₀ (norm_nonneg _) hz2 2).trans (le_of_eq ?_)
      simp only [mul_pow, Real.sq_sqrt hin]
      ring
  choose z hz hz' using hb
  have hdot : (fun a => σ (yv a)) ⬝ᵥ (fun a => σ (c a)) = ∑ b, σ (z b) := by
    simp only [dotProduct]
    rw [← Equiv.sum_comp ch.e.symm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hz, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, mul_comm]
  have hcard : (Fintype.card (TestIx ch.G) : ℝ) ≤ ea * ea := by
    rw [← Nat.card_eq_fintype_card, Nat.card_prod]
    push_cast
    exact mul_le_mul hN.1 hC.1 (by positivity) hea0.le
  have hE : 0 ≤ ea ^ 8 * es ^ 2 * e1 * eg * eg' := by positivity
  rw [hdot, ← hsum]
  calc ‖∑ b, σ (z b)‖ ^ 2 ≤ (∑ b, ‖σ (z b)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (Finset.univ : Finset (TestIx ch.G)).card * ∑ b, ‖σ (z b)‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ (ea * ea) * ∑ b, (ea ^ 8 * es ^ 2 * e1 * eg * eg') * Bf * nb b :=
      mul_le_mul hcard (Finset.sum_le_sum fun b _ => hz' b) (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
    _ = _ := by
      rw [← Finset.mul_sum]
      ring

/- English proof (translation)
Use `set σ := p.embedding with hσ`. Use `set E := Real.exp (D.R.m * aOne ch.G C sb) ^ 11 * Real.exp (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * sig ch.G) ^ 2 * Real.exp (aOne ch.G C sb) * Real.exp (D.R.m * g p) * Real.exp (D.R.m * g' p) with hE`. Establish `hE0 : 0 ≤ E` using `by positivity`. Establish `hunit : IsUnit ((X' p)⁻¹).det` using `(Matrix.isUnit_nonsing_inv_det_iff).2 (hTL.1 p).1`. Establish `hGm : ((X' p)⁻¹)ᴴ * (X' p)⁻¹ = (((formGram ch.G ch.e).map σ)⁻¹)ᵀ`.

Rewrite using `[(hTL.1 p).2, Matrix.transpose_map]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `((formGram ch.G ch.e)⁻¹).map σ = ((formGram ch.G ch.e).map σ)⁻¹`. Rewrite using `[Matrix.inv_def, Matrix.inv_def, Ring.inverse_eq_inv', Ring.inverse_eq_inv']`. Use extensionality with `i j`.

Establish `h1` using `congrFun (congrFun (RingHom.map_adjugate σ (formGram ch.G ch.e)) i) j`. Establish `h2` using `RingHom.map_det σ (formGram ch.G ch.e)`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply] at h1 h2`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, h2, ← h1]`. Establish `hp` using `dual_pos hunit hGm`.

Unfold `Formalism.HN.opNormAt`. Rewrite using `[toMatrix_basis]`. Use `opNorm_sq_le (hX p).1 (V.map σ) hE0 (denseRange_pi p _) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Simplify using `only []`.

Rewrite using `[(hX p).2]`. Use `set Q := (star (fun i => σ (x i)) ⬝ᵥ (((A.fam.R A.μ0).HV (A.fam.lvl F.P0 F.ψ0)).map σ).mulVec fun i => σ (x i)).re with hQ`. Establish `hQ0 : 0 ≤ Q`. Rewrite using `[hQ, ← (hX p).2, star_mul_form, Complex.ofReal_re]`. Conclude with `Finset.sum_nonneg fun _ _ => by positivity`.

Establish `hy : (V.map σ) *ᵥ (fun i => σ (x i)) = fun a => σ (V.mulVec x a)` using `funext fun a => (RingHom.map_mulVec σ V x a).symm`. Rewrite using `[hy]`. Use `dual_le hunit hGm _ (mul_nonneg hE0 hQ0) (denseRange_pi p _) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨c, rfl⟩`. Establish `h1` using `test_bound ch C sb hm hA p hOK hD hS hT hN hC hg hg' hP hPsi hp (R.jX A.μ0 (formOf F A.μ0 x)) (Bf := Real.exp (D.R.m * aOne ch.G C sb) * Q) (by positivity) (fun y => hForm σ x y) (V.mulVec x) (fun a => hV x a) c`.

Use `h1.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[hE]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem opNorm_bound {F : Face D A} (C sb : ℝ) (hm : 0 < D.R.m) (hA : 0 ≤ D.R.m * aOne ch.G C sb) (p : InfinitePlace D.what₂.LL)
    {g g' : InfinitePlace D.what₂.LL → ℝ}
    (hOK : ∀ a, ch.S.SumOK A.μ0 (ch.Phi a)) (hD : DepthAt ch) (hS : InfScalAt ch C sb) (hT : InfTensAt ch C) (hN : InfCountAt ch C sb)
    (hC : InfClassAt ch C sb)
    (hg : ∀ (p : InfinitePlace D.what₂.LL) Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (j : Fin D.R.m) B v,
      NrmLe _ p.embedding v B →
        NrmLe _ p.embedding (ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) v) (Real.exp (g p) * B))
    (hg' : ∀ (p : InfinitePlace D.what₂.LL) Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (i : Fin D.R.m) B v,
      NrmLe _ p.embedding v B →
        NrmLe _ p.embedding (ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) v) (Real.exp (g' p) * B))
    (hP : InfPairAt ch C sb) (hPsi : InfPsiAt ch) (hForm : InfFormAt F ch C sb)
    {X' : InfinitePlace D.what₂.LL → Matrix (Fin ch.n) (Fin ch.n) ℂ} {M : Submodule (𝓞 D.what₂.LL) (Fin ch.n → D.what₂.LL)}
    (hTL : IsTestLat ch.G ch.rp ch.n ch.e X' M)
    {X : InfinitePlace D.what₂.LL → Matrix (Fin ((A.fam.R A.μ0).nV (A.fam.lvl F.P0 F.ψ0))) (Fin ((A.fam.R A.μ0).nV (A.fam.lvl F.P0 F.ψ0))) ℂ}
    (hX : IsMetric ((A.fam.R A.μ0).HV (A.fam.lvl F.P0 F.ψ0)) X)
    {V : Matrix (Fin ch.n) (Fin ((A.fam.R A.μ0).nV (A.fam.lvl F.P0 F.ψ0))) D.what₂.LL}
    (hV : ∀ x a, D.what₂.embLL (V.mulVec x a) = vK ch A.μ0 (formOf F A.μ0 x) a) :
    Formalism.HN.opNormAt (Pi.basisFun _ _) X (Pi.basisFun _ _) X' p V.mulVecLin ^ 2 ≤
      Real.exp (D.R.m * aOne ch.G C sb) ^ 11 * Real.exp (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * sig ch.G) ^ 2 * Real.exp (aOne ch.G C sb) *
        Real.exp (D.R.m * g p) * Real.exp (D.R.m * g' p) := by
  set σ := p.embedding with hσ
  set E := Real.exp (D.R.m * aOne ch.G C sb) ^ 11 * Real.exp (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * sig ch.G) ^ 2 *
    Real.exp (aOne ch.G C sb) * Real.exp (D.R.m * g p) * Real.exp (D.R.m * g' p) with hE
  have hE0 : 0 ≤ E := by positivity
  have hunit : IsUnit ((X' p)⁻¹).det := (Matrix.isUnit_nonsing_inv_det_iff).2 (hTL.1 p).1
  have hGm : ((X' p)⁻¹)ᴴ * (X' p)⁻¹ = (((formGram ch.G ch.e).map σ)⁻¹)ᵀ := by
    rw [(hTL.1 p).2, Matrix.transpose_map]
    congr 1
    change ((formGram ch.G ch.e)⁻¹).map σ = ((formGram ch.G ch.e).map σ)⁻¹
    rw [Matrix.inv_def, Matrix.inv_def, Ring.inverse_eq_inv', Ring.inverse_eq_inv']
    ext i j
    have h1 := congrFun (congrFun (RingHom.map_adjugate σ (formGram ch.G ch.e)) i) j
    have h2 := RingHom.map_det σ (formGram ch.G ch.e)
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at h1 h2
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, h2, ← h1]
  have hp := dual_pos hunit hGm
  unfold Formalism.HN.opNormAt
  rw [toMatrix_basis]
  refine opNorm_sq_le (hX p).1 (V.map σ) hE0 (denseRange_pi p _) ?_
  rintro _ ⟨x, rfl⟩
  simp only []
  rw [(hX p).2]
  set Q := (star (fun i => σ (x i)) ⬝ᵥ (((A.fam.R A.μ0).HV (A.fam.lvl F.P0 F.ψ0)).map σ).mulVec fun i => σ (x i)).re with hQ
  have hQ0 : 0 ≤ Q := by
    rw [hQ, ← (hX p).2, star_mul_form, Complex.ofReal_re]
    exact Finset.sum_nonneg fun _ _ => by positivity
  have hy : (V.map σ) *ᵥ (fun i => σ (x i)) = fun a => σ (V.mulVec x a) := funext fun a => (RingHom.map_mulVec σ V x a).symm
  rw [hy]
  refine dual_le hunit hGm _ (mul_nonneg hE0 hQ0) (denseRange_pi p _) ?_
  rintro _ ⟨c, rfl⟩
  have h1 := test_bound ch C sb hm hA p hOK hD hS hT hN hC hg hg' hP hPsi hp (R.jX A.μ0 (formOf F A.μ0 x))
    (Bf := Real.exp (D.R.m * aOne ch.G C sb) * Q) (by positivity) (fun y => hForm σ x y) (V.mulVec x) (fun a => hV x a) c
  refine h1.trans (le_of_eq ?_)
  rw [hE]
  ring

/- English proof (translation)
Establish `h1` using `InfinitePlace.card_add_two_mul_card_eq_rank D.what₂.LL`. Establish `h2` using `IsTotallyComplex.nrRealPlaces_eq_zero D.what₂.LL`. Establish `h3` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces D.what₂.LL`. Establish `h4 : Module.finrank ℚ D.what₂.LL = 2 * Formalism.HN.nPl D.what₂.LL`. Rewrite using `[Formalism.HN.nPl, h3, ← h1, h2]`.

Simplify using the standard rewrite rules. Establish `h5 : 0 < Module.finrank ℚ D.what₂.LL` using `Module.finrank_pos`. Establish `h6 : (Formalism.HN.nPl D.what₂.LL : ℝ) ≠ 0`. Establish `: Formalism.HN.nPl D.what₂.LL ≠ 0` using `fun h => by rw [h4, h] at h5; simp at h5`. Conclude with `this` after adjusting the coercions.

Rewrite using `[Formalism.PairingDivisionLocalBalance.meanInf, h4]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem meanInf_eq (g : InfinitePlace D.what₂.LL → ℝ) :
    Formalism.PairingDivisionLocalBalance.meanInf D.what₂.LL g = (1 / (Formalism.HN.nPl D.what₂.LL : ℝ)) * ∑ v, g v := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank D.what₂.LL
  have h2 := IsTotallyComplex.nrRealPlaces_eq_zero D.what₂.LL
  have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces D.what₂.LL
  have h4 : Module.finrank ℚ D.what₂.LL = 2 * Formalism.HN.nPl D.what₂.LL := by
    rw [Formalism.HN.nPl, h3, ← h1, h2]; simp
  have h5 : 0 < Module.finrank ℚ D.what₂.LL := Module.finrank_pos
  have h6 : (Formalism.HN.nPl D.what₂.LL : ℝ) ≠ 0 := by
    have : Formalism.HN.nPl D.what₂.LL ≠ 0 := fun h => by rw [h4, h] at h5; simp at h5
    exact_mod_cast this
  rw [Formalism.PairingDivisionLocalBalance.meanInf, h4]
  push_cast
  field_simp

/- English proof (translation)
Use `norm_pos_iff.2 fun h => hV ?_` and prove the remaining obligations. Establish `h1 : X'⁻¹ * V.map σ * X = 0`. Establish `h2` using `(LinearEquiv.map_eq_zero_iff LinearMap.toContinuousLinearMap).1 h`. Conclude with `(LinearEquiv.map_eq_zero_iff Matrix.toEuclideanLin).1 h2`. Establish `h3 : V.map σ = 0`.

Establish `h4 : X' * (X'⁻¹ * V.map σ * X) * X⁻¹ = V.map σ`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX', Matrix.one_mul]`. Rewrite using `[← h4, h1]`. Simplify using the standard rewrite rules. Use extensionality with `i j`.

Use `congrFun (congrFun h3 i) j` as an intermediate fact. Simplify using `using this`.
-/
theorem opNormAt_pos {N n : ℕ} {X : Matrix (Fin N) (Fin N) ℂ} {X' : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X.det) (hX' : IsUnit X'.det)
    {σ : D.what₂.LL →+* ℂ} {V : Matrix (Fin n) (Fin N) D.what₂.LL} (hV : V ≠ 0) :
    0 < ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (X'⁻¹ * V.map σ * X))‖ := by
  refine norm_pos_iff.2 fun h => hV ?_
  have h1 : X'⁻¹ * V.map σ * X = 0 := by
    have h2 := (LinearEquiv.map_eq_zero_iff LinearMap.toContinuousLinearMap).1 h
    exact (LinearEquiv.map_eq_zero_iff Matrix.toEuclideanLin).1 h2
  have h3 : V.map σ = 0 := by
    have h4 : X' * (X'⁻¹ * V.map σ * X) * X⁻¹ = V.map σ := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX, Matrix.mul_one, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hX', Matrix.one_mul]
    rw [← h4, h1]; simp
  ext i j
  have := congrFun (congrFun h3 i) j
  simpa using this

/- English proof (translation)
Introduce `X' M hTL X hX V hV`. Take `⟨g, hgm, hg⟩` from `hTop`. Take `⟨g', hgm', hg'⟩` from `hRow`. Establish `hm2 : 2 ≤ D.R.m` using `D.R.two_le_m`. Establish `hm : 0 < D.R.m` using `by omega`.

Establish `hm1 : (1 : ℝ) ≤ D.R.m` using `by exact_mod_cast hm`. Establish `hsig : 0 ≤ sig ch.G` using `Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)`. Establish `hl : 0 ≤ Real.log sb` using `Real.log_nonneg hb`. Establish `hb0 : 0 ≤ sb` using `by linarith`. Use `set t1 := C * D.R.f * bigN D * sb * Real.log sb with ht1`.

Use `set t2 := C * D.R.m * (bigN D : ℝ) ^ 2 * sig ch.G with ht2`. Establish `ht10 : 0 ≤ t1`. Use `mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 ?_) (Nat.cast_nonneg _)) hb0) hl` and prove the remaining obligations. Conclude with `Nat.cast_nonneg _`. Establish `ht20 : 0 ≤ t2` using `mul_nonneg (mul_nonneg (mul_nonneg hC0 (Nat.cast_nonneg _)) (by positivity)) hsig`.

Establish `hAe : aOne ch.G C sb = t1 + t2` using `rfl`. Establish `hA16 : aOne ch.G (16 * C) sb = 16 * (t1 + t2)`. Rewrite using `[aOne, ht1, ht2]`. Expand and normalize the polynomial expressions, which then agree. Use `set Aa := aOne ch.G C sb with hAa`.

Establish `hA0 : 0 ≤ Aa` using `by rw [hAe]; exact add_nonneg ht10 ht20`. Establish `hmA : 0 ≤ (D.R.m : ℝ) * Aa` using `mul_nonneg (by linarith) hA0`. Use `set Sg := C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * sig ch.G with hSg`. Establish `hSle : Sg ≤ D.R.m * Aa`. Establish `: Sg = D.R.m * t2` using `by rw [hSg, ht2]; ring`.

Rewrite using `[this, hAe]`. Conclude with `mul_le_mul_of_nonneg_left (by linarith) (by linarith)`. Use `set Lb : InfinitePlace D.what₂.LL → ℝ := fun p => 11 * (D.R.m * Aa) + 2 * Sg + Aa + D.R.m * g p + D.R.m * g' p with hLb`. Establish `hexp : ∀ p, Formalism.HN.opNormAt (Pi.basisFun _ _) X (Pi.basisFun _ _) X' p V.mulVecLin ^ 2 ≤ Real.exp (Lb p)` using `fun p => by`. Use `(opNorm_bound ch C sb hm hmA p hOK hD hS hT hN hC hg hg' hP hPsi hForm hTL hX hV).trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]`. Use `congr 1`. Establish `hnPl : 0 ≤ (1 / (Formalism.HN.nPl D.what₂.LL : ℝ))` using `by positivity`. Establish `hmean : (1 / (Formalism.HN.nPl D.what₂.LL : ℝ)) * ∑ p, g p ≤ Aa` using `by rw [← meanInf_eq]; exact hgm`. Establish `hmean' : (1 / (Formalism.HN.nPl D.what₂.LL : ℝ)) * ∑ p, g' p ≤ Aa` using `by rw [← meanInf_eq]; exact hgm'`.

Establish `hpl : 0 < (Formalism.HN.nPl D.what₂.LL : ℝ)`. Establish `: 0 < Formalism.HN.nPl D.what₂.LL` using `Fintype.card_pos`. Conclude with `this` after adjusting the coercions. Establish `hfin : 0 ≤ (D.R.m : ℝ) * aOne ch.G (16 * C) sb`. Rewrite using `[hA16, ← hAe]`.

Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[Formalism.HN.htMap]`. Distinguish the cases in `hV0 : V = 0`. Substitute `hV0` using the available equality. Establish `h0 : ∀ v, Formalism.HN.opNormAt (Pi.basisFun _ _) X (Pi.basisFun _ _) X' v (0 : Matrix (Fin ch.n) _ D.what₂.LL).mulVecLin = 0` using `fun v => by`.

Simplify using `[Formalism.HN.opNormAt]`. Simplify using `only [h0]`. Simplify using `using hfin`. Establish `hlog : ∀ p, Real.log (Formalism.HN.opNormAt (Pi.basisFun _ _) X (Pi.basisFun _ _) X' p V.mulVecLin ^ 2) ≤ Lb p` using `fun p => by`. Establish `hpos : 0 < Formalism.HN.opNormAt (Pi.basisFun _ _) X (Pi.basisFun _ _) X' p V.mulVecLin`.

Unfold `Formalism.HN.opNormAt`. Rewrite using `[toMatrix_basis]`. Conclude with `opNormAt_pos (hX p).1 (hTL.1 p).1 hV0`. Conclude with `(Real.log_le_iff_le_exp (by positivity)).2 (hexp p)`. Establish `hs : (1 / (Formalism.HN.nPl D.what₂.LL : ℝ)) * ∑ p, Lb p = 11 * (D.R.m * Aa) + 2 * Sg + Aa + D.R.m * ((1 / (Formalism.HN.nPl D.what₂.LL : ℝ)) * ∑ p, g p) + D.R.m * ((1 / (Formalism.HN.nPl D.what₂.LL : ℝ)) * ∑ p, g' p)`.

Establish `hc : ((Fintype.card (InfinitePlace D.what₂.LL) : ℕ) : ℝ) = Formalism.HN.nPl D.what₂.LL` using `rfl`. Simplify using `only [hLb, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, hc]`. Clear the denominators using the available nonvanishing facts. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hA16, ← hAe]`.

Establish `h1` using `mul_le_mul_of_nonneg_left hmean (by linarith : (0 : ℝ) ≤ D.R.m)`. Establish `h2` using `mul_le_mul_of_nonneg_left hmean' (by linarith : (0 : ℝ) ≤ D.R.m)`. Establish `h3 : Aa ≤ D.R.m * Aa` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem infAt_of (F : Face D A) (C sb : ℝ) (hC0 : 0 ≤ C) (hb : 1 ≤ sb)
    (hOK : ∀ a, ch.S.SumOK A.μ0 (ch.Phi a)) (hD : DepthAt ch) (hS : InfScalAt ch C sb) (hT : InfTensAt ch C) (hN : InfCountAt ch C sb)
    (hC : InfClassAt ch C sb) (hTop : InfTopAt ch C sb) (hRow : InfRowAt ch C sb) (hP : InfPairAt ch C sb) (hPsi : InfPsiAt ch)
    (hForm : InfFormAt F ch C sb) : InfAt F ch (16 * C) sb := by
  intro X' M hTL X hX V hV
  obtain ⟨g, hgm, hg⟩ := hTop
  obtain ⟨g', hgm', hg'⟩ := hRow
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hm : 0 < D.R.m := by omega
  have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hsig : 0 ≤ sig ch.G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hl : 0 ≤ Real.log sb := Real.log_nonneg hb
  have hb0 : 0 ≤ sb := by linarith
  set t1 := C * D.R.f * bigN D * sb * Real.log sb with ht1
  set t2 := C * D.R.m * (bigN D : ℝ) ^ 2 * sig ch.G with ht2
  have ht10 : 0 ≤ t1 := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 ?_) (Nat.cast_nonneg _)) hb0) hl
    exact Nat.cast_nonneg _
  have ht20 : 0 ≤ t2 := mul_nonneg (mul_nonneg (mul_nonneg hC0 (Nat.cast_nonneg _)) (by positivity)) hsig
  have hAe : aOne ch.G C sb = t1 + t2 := rfl
  have hA16 : aOne ch.G (16 * C) sb = 16 * (t1 + t2) := by
    rw [aOne, ht1, ht2]; ring
  set Aa := aOne ch.G C sb with hAa
  have hA0 : 0 ≤ Aa := by rw [hAe]; exact add_nonneg ht10 ht20
  have hmA : 0 ≤ (D.R.m : ℝ) * Aa := mul_nonneg (by linarith) hA0
  set Sg := C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * sig ch.G with hSg
  have hSle : Sg ≤ D.R.m * Aa := by
    have : Sg = D.R.m * t2 := by rw [hSg, ht2]; ring
    rw [this, hAe]
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  set Lb : InfinitePlace D.what₂.LL → ℝ := fun p => 11 * (D.R.m * Aa) + 2 * Sg + Aa + D.R.m * g p + D.R.m * g' p with hLb
  have hexp : ∀ p, Formalism.HN.opNormAt (Pi.basisFun _ _) X (Pi.basisFun _ _) X' p V.mulVecLin ^ 2 ≤ Real.exp (Lb p) := fun p => by
    refine (opNorm_bound ch C sb hm hmA p hOK hD hS hT hN hC hg hg' hP hPsi hForm hTL hX hV).trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
  have hnPl : 0 ≤ (1 / (Formalism.HN.nPl D.what₂.LL : ℝ)) := by positivity
  have hmean : (1 / (Formalism.HN.nPl D.what₂.LL : ℝ)) * ∑ p, g p ≤ Aa := by rw [← meanInf_eq]; exact hgm
  have hmean' : (1 / (Formalism.HN.nPl D.what₂.LL : ℝ)) * ∑ p, g' p ≤ Aa := by rw [← meanInf_eq]; exact hgm'
  have hpl : 0 < (Formalism.HN.nPl D.what₂.LL : ℝ) := by
    have : 0 < Formalism.HN.nPl D.what₂.LL := Fintype.card_pos
    exact_mod_cast this
  have hfin : 0 ≤ (D.R.m : ℝ) * aOne ch.G (16 * C) sb := by
    rw [hA16, ← hAe]; nlinarith
  rw [Formalism.HN.htMap]
  by_cases hV0 : V = 0
  · subst hV0
    have h0 : ∀ v, Formalism.HN.opNormAt (Pi.basisFun _ _) X (Pi.basisFun _ _) X' v (0 : Matrix (Fin ch.n) _ D.what₂.LL).mulVecLin = 0 := fun v => by
      simp [Formalism.HN.opNormAt]
    simp only [h0]
    simpa using hfin
  have hlog : ∀ p, Real.log (Formalism.HN.opNormAt (Pi.basisFun _ _) X (Pi.basisFun _ _) X' p V.mulVecLin ^ 2) ≤ Lb p := fun p => by
    have hpos : 0 < Formalism.HN.opNormAt (Pi.basisFun _ _) X (Pi.basisFun _ _) X' p V.mulVecLin := by
      unfold Formalism.HN.opNormAt
      rw [toMatrix_basis]
      exact opNormAt_pos (hX p).1 (hTL.1 p).1 hV0
    exact (Real.log_le_iff_le_exp (by positivity)).2 (hexp p)
  have hs : (1 / (Formalism.HN.nPl D.what₂.LL : ℝ)) * ∑ p, Lb p =
      11 * (D.R.m * Aa) + 2 * Sg + Aa + D.R.m * ((1 / (Formalism.HN.nPl D.what₂.LL : ℝ)) * ∑ p, g p) +
        D.R.m * ((1 / (Formalism.HN.nPl D.what₂.LL : ℝ)) * ∑ p, g' p) := by
    have hc : ((Fintype.card (InfinitePlace D.what₂.LL) : ℕ) : ℝ) = Formalism.HN.nPl D.what₂.LL := rfl
    simp only [hLb, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, hc]
    field_simp
  calc _ ≤ (1 / (Formalism.HN.nPl D.what₂.LL : ℝ)) * ∑ p, Lb p := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => hlog p) hnPl
    _ = _ := hs
    _ ≤ _ := by
      rw [hA16, ← hAe]
      have h1 := mul_le_mul_of_nonneg_left hmean (by linarith : (0 : ℝ) ≤ D.R.m)
      have h2 := mul_le_mul_of_nonneg_left hmean' (by linarith : (0 : ℝ) ≤ D.R.m)
      have h3 : Aa ≤ D.R.m * Aa := by nlinarith
      linarith

end Place

/- English proof (translation)
Introduce and unpack `⟨c0, h0⟩ ⟨c1, h1⟩ ⟨c2, h2⟩ ⟨c3, h3⟩ ⟨c4, h4⟩ ⟨c5, h5⟩ ⟨c6, h6⟩ ⟨c7, h7⟩ ⟨c8, h8⟩ ⟨c9, h9⟩ ⟨c10, h10⟩`. Use `⟨max c0 (max c1 (max c2 (max c3 (max c4 (max c5 (max c6 (max c7 (max c8 (max c9 (c10)))))))))), fun CF hCF => ?_⟩` and prove the remaining obligations. Simplify using `only [max_le_iff] at hCF`. Take `⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩` from `hCF`. Take `⟨C1, h1⟩` from `h1 CF a1`.

Take `⟨C2, h2⟩` from `h2 CF a2`. Take `⟨C3, h3⟩` from `h3 CF a3`. Take `⟨C4, h4⟩` from `h4 CF a4`. Take `⟨C5, h5⟩` from `h5 CF a5`. Take `⟨C6, h6⟩` from `h6 CF a6`.

Take `⟨C7, h7⟩` from `h7 CF a7`. Take `⟨C8, h8⟩` from `h8 CF a8`. Take `⟨C9, h9⟩` from `h9 CF a9`. Take `⟨crystallineComparison, h10⟩` from `h10 CF a10`. Use `⟨16 * max 0 (max C1 (max C2 (max C3 (max C4 (max C5 (max C6 (max C7 (max C8 (max C9 (crystallineComparison)))))))))), fun ε C hC => ?_⟩` and prove the remaining obligations.

Establish `hC' : max 0 (max C1 (max C2 (max C3 (max C4 (max C5 (max C6 (max C7 (max C8 (max C9 (crystallineComparison)))))))))) ≤ C / 16` using `by linarith`. Simplify using `only [max_le_iff] at hC'`. Take `⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩` from `hC'`. Take `⟨x0, h0⟩` from `h0 ε CF a0`. Take `⟨x1, h1⟩` from `h1 ε (C / 16) b1`.

Take `⟨x2, h2⟩` from `h2 ε (C / 16) b2`. Take `⟨x3, h3⟩` from `h3 ε (C / 16) b3`. Take `⟨x4, h4⟩` from `h4 ε (C / 16) b4`. Take `⟨x5, h5⟩` from `h5 ε (C / 16) b5`. Take `⟨x6, h6⟩` from `h6 ε (C / 16) b6`.

Take `⟨x7, h7⟩` from `h7 ε (C / 16) b7`. Take `⟨x8, h8⟩` from `h8 ε (C / 16) b8`. Take `⟨x9, h9⟩` from `h9 ε (C / 16) b9`. Take `⟨x10, h10⟩` from `h10 ε (C / 16) b10`. Use `⟨max x0 (max x1 (max x2 (max x3 (max x4 (max x5 (max x6 (max x7 (max x8 (max x9 (x10)))))))))), ?_⟩` and prove the remaining obligations.

Introduce `D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hSet ch hIs hAt hFd`. Simplify using `only [max_le_iff] at hx`. Take `⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10⟩` from `hx`. Establish `hb : 1 ≤ large₂.sc.b` using `Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)`. Establish `h` using `infAt_of ch F (C / 16) large₂.sc.b b0 hb (fun a => h0 D large₂ hε y0 Γ Pl0 T A Ks R F hSet ch hIs hAt _ a) (h1 D large₂ hε y1 Γ Pl0 T A Ks R F hSet ch hIs hAt hFd) (h2 D large₂ hε y2 Γ Pl0 T A Ks R F hSet ch hIs hAt hFd) (h3 D large₂ hε y3 Γ Pl0 T A Ks R F hSet ch hIs hAt hFd) (h …`.

Rewrite `h` using `[show 16 * (C / 16) = C by ring]`. Then use the resulting hypothesis.
-/
theorem infK_of_factors : SumOKK → DepthK → InfScalK → InfTensK → InfCountK → InfClassK → InfTopK → InfRowK → InfPairK → InfPsiK →
    InfFormK → InfK := by
  rintro ⟨c0, h0⟩ ⟨c1, h1⟩ ⟨c2, h2⟩ ⟨c3, h3⟩ ⟨c4, h4⟩ ⟨c5, h5⟩ ⟨c6, h6⟩ ⟨c7, h7⟩ ⟨c8, h8⟩ ⟨c9, h9⟩ ⟨c10, h10⟩
  refine ⟨max c0 (max c1 (max c2 (max c3 (max c4 (max c5 (max c6 (max c7 (max c8 (max c9 (c10)))))))))), fun CF hCF => ?_⟩
  simp only [max_le_iff] at hCF
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hCF
  obtain ⟨C1, h1⟩ := h1 CF a1
  obtain ⟨C2, h2⟩ := h2 CF a2
  obtain ⟨C3, h3⟩ := h3 CF a3
  obtain ⟨C4, h4⟩ := h4 CF a4
  obtain ⟨C5, h5⟩ := h5 CF a5
  obtain ⟨C6, h6⟩ := h6 CF a6
  obtain ⟨C7, h7⟩ := h7 CF a7
  obtain ⟨C8, h8⟩ := h8 CF a8
  obtain ⟨C9, h9⟩ := h9 CF a9
  obtain ⟨crystallineComparison, h10⟩ := h10 CF a10
  refine ⟨16 * max 0 (max C1 (max C2 (max C3 (max C4 (max C5 (max C6 (max C7 (max C8 (max C9 (crystallineComparison)))))))))), fun ε C hC => ?_⟩
  have hC' : max 0 (max C1 (max C2 (max C3 (max C4 (max C5 (max C6 (max C7 (max C8 (max C9 (crystallineComparison)))))))))) ≤ C / 16 := by linarith
  simp only [max_le_iff] at hC'
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := hC'
  obtain ⟨x0, h0⟩ := h0 ε CF a0
  obtain ⟨x1, h1⟩ := h1 ε (C / 16) b1
  obtain ⟨x2, h2⟩ := h2 ε (C / 16) b2
  obtain ⟨x3, h3⟩ := h3 ε (C / 16) b3
  obtain ⟨x4, h4⟩ := h4 ε (C / 16) b4
  obtain ⟨x5, h5⟩ := h5 ε (C / 16) b5
  obtain ⟨x6, h6⟩ := h6 ε (C / 16) b6
  obtain ⟨x7, h7⟩ := h7 ε (C / 16) b7
  obtain ⟨x8, h8⟩ := h8 ε (C / 16) b8
  obtain ⟨x9, h9⟩ := h9 ε (C / 16) b9
  obtain ⟨x10, h10⟩ := h10 ε (C / 16) b10
  refine ⟨max x0 (max x1 (max x2 (max x3 (max x4 (max x5 (max x6 (max x7 (max x8 (max x9 (x10)))))))))), ?_⟩
  intro D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hSet ch hIs hAt hFd
  simp only [max_le_iff] at hx
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10⟩ := hx
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)
  have h := infAt_of ch F (C / 16) large₂.sc.b b0 hb (fun a => h0 D large₂ hε y0 Γ Pl0 T A Ks R F hSet ch hIs hAt _ a)
    (h1 D large₂ hε y1 Γ Pl0 T A Ks R F hSet ch hIs hAt hFd)
    (h2 D large₂ hε y2 Γ Pl0 T A Ks R F hSet ch hIs hAt hFd)
    (h3 D large₂ hε y3 Γ Pl0 T A Ks R F hSet ch hIs hAt hFd)
    (h4 D large₂ hε y4 Γ Pl0 T A Ks R F hSet ch hIs hAt hFd)
    (h5 D large₂ hε y5 Γ Pl0 T A Ks R F hSet ch hIs hAt hFd)
    (h6 D large₂ hε y6 Γ Pl0 T A Ks R F hSet ch hIs hAt hFd)
    (h7 D large₂ hε y7 Γ Pl0 T A Ks R F hSet ch hIs hAt hFd)
    (h8 D large₂ hε y8 Γ Pl0 T A Ks R F hSet ch hIs hAt hFd)
    (h9 D large₂ hε y9 Γ Pl0 T A Ks R F hSet ch hIs hAt hFd)
    (h10 D large₂ hε y10 Γ Pl0 T A Ks R F hSet ch hIs hAt hFd)
  rwa [show 16 * (C / 16) = C by ring] at h

end GlobalTheory.CompanionTheory.InfAssembly

end
end

end DeltaFormSums
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
/- English proof (translation)
Apply the tactic sequence `first | exact @DeltaFormSums.GlobalTheory.CompanionTheory.InfAssembly.infK_of_factors | exact DeltaFormSums.GlobalTheory.CompanionTheory.InfAssembly.infK_of_factors | (intros; apply DeltaFormSums.GlobalTheory.CompanionTheory.InfAssembly.infK_of_factors <;> assumption)`.
-/
theorem _root_.GlobalTheory.Adopt.archimedeanSumSizeBound_largeData_from_factors : SumOKK → DepthK → InfScalK → InfTensK → InfCountK → InfClassK → InfTopK → InfRowK → InfPairK → InfPsiK → InfFormK → InfK := by
  first | exact @DeltaFormSums.GlobalTheory.CompanionTheory.InfAssembly.infK_of_factors | exact DeltaFormSums.GlobalTheory.CompanionTheory.InfAssembly.infK_of_factors | (intros; apply DeltaFormSums.GlobalTheory.CompanionTheory.InfAssembly.infK_of_factors <;> assumption)

end
