import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsPosConstLagrangeCondition
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkFilLetter

noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

open Formalism.BasicNotions

def boxM {n : ℕ} (d : ℕ) (b : ZMod n → ℕ) (S η : ℕ) (i : ZMod n) : ℕ :=
  if (i.val + d) % 2 = 0 then b i + S else η

def boxH {n : ℕ} (d : ℕ) (b : ZMod n → ℕ) (S η : ℕ) (i : ZMod n) : ℕ :=
  if (i.val + d) % 2 = 0 then η else b i + S

section Out

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable [NeZero n] (W : LocWach PD LL O v n)

/- English proof (translation)
Take `⟨-, hp, -, -, -, -, -, -, hA, -⟩` from `hS`. Establish `h1` using `hA i`. Establish `hp' : (1 : ℝ) < (PD.p : ℝ)` using `by exact_mod_cast (show 1 < PD.p by omega)`. Establish `hl : 0 ≤ Formalism.MainNotions.RamifiedCoefficientChains.lam PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η)`. Unfold `Formalism.MainNotions.RamifiedCoefficientChains.lam`.

Break down `Nat.eq_zero_or_pos (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) with h | h` into its components or cases. Rewrite using `[h]`. Simplify using the standard rewrite rules. Establish `hx : (1 : ℝ) ≤ 2 * ((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η : ℕ) : ℝ)`. Establish `: (1 : ℝ) ≤ ((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η : ℕ) : ℝ)` using `by exact_mod_cast h`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `Real.logb_nonneg hp' hx` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hf : 0 ≤ ((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η : ℕ) : ℝ) * (2 * (PD.p : ℝ) - 1) / ((PD.p : ℝ) - 1) ^ 2`. Apply `div_nonneg _ (sq_nonneg _)` to reduce the goal to its premises.

Apply `mul_nonneg (Nat.cast_nonneg _)` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Establish `haR : 3 ≤ Formalism.MainNotions.RamifiedCoefficientChains.aR PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η)`. Unfold `Formalism.MainNotions.RamifiedCoefficientChains.aR`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `: (η : ℝ) < (b i : ℝ)` using `by linarith`. Conclude with `this` after adjusting the coercions.
-/
theorem rk_eta_lt {d : ℕ} {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ}
    {S η m : ℕ} (hS : Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m) (i : ZMod n) : η < b i := by
  obtain ⟨-, hp, -, -, -, -, -, -, hA, -⟩ := hS
  have h1 := hA i
  have hp' : (1 : ℝ) < (PD.p : ℝ) := by exact_mod_cast (show 1 < PD.p by omega)
  have hl : 0 ≤ Formalism.MainNotions.RamifiedCoefficientChains.lam PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) := by
    unfold Formalism.MainNotions.RamifiedCoefficientChains.lam
    rcases Nat.eq_zero_or_pos (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) with h | h
    · rw [h]
      simp
    · have hx : (1 : ℝ) ≤ 2 * ((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η : ℕ) : ℝ) := by
        have : (1 : ℝ) ≤ ((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η : ℕ) : ℝ) := by exact_mod_cast h
        linarith
      have := Real.logb_nonneg hp' hx
      linarith
  have hf : 0 ≤ ((Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η : ℕ) : ℝ) * (2 * (PD.p : ℝ) - 1) / ((PD.p : ℝ) - 1) ^ 2 := by
    apply div_nonneg _ (sq_nonneg _)
    apply mul_nonneg (Nat.cast_nonneg _)
    linarith
  have haR : 3 ≤ Formalism.MainNotions.RamifiedCoefficientChains.aR PD.p (Formalism.MainNotions.RamifiedCoefficientChains.hpar n b S + η) := by
    unfold Formalism.MainNotions.RamifiedCoefficientChains.aR
    linarith
  have : (η : ℝ) < (b i : ℝ) := by linarith
  exact_mod_cast this

/- English proof (translation)
Introduce `a ha`. Unfold `Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at ha`. Unfold `boxM boxH`. Use `split_ifs at ha ⊢ with h`. Break down `ha with ⟨h1, h2⟩ | ⟨h1, h2⟩` into its components or cases.

Apply the tactic sequence `constructor <;> push_cast at h1 h2 ⊢ <;> omega`. Apply the tactic sequence `constructor <;> push_cast at h1 h2 ⊢ <;> omega`. Break down `ha with ⟨h1, h2⟩ | ⟨h1, h2⟩` into its components or cases. Apply the tactic sequence `constructor <;> push_cast at h1 h2 ⊢ <;> omega`. Apply the tactic sequence `constructor <;> push_cast at h1 h2 ⊢ <;> omega`.
-/
theorem rk_win_box (d : ℕ) (b : ZMod n → ℕ) (S η : ℕ) (i : ZMod n) (hη : η < b i) :
    Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS d b S η i ⊆ Set.Icc (-(boxM d b S η i : ℤ)) (boxH d b S η i : ℤ) := by
  intro a ha
  unfold Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at ha
  unfold boxM boxH
  split_ifs at ha ⊢ with h
  · rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · constructor <;> push_cast at h1 h2 ⊢ <;> omega
    · constructor <;> push_cast at h1 h2 ⊢ <;> omega
  · rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · constructor <;> push_cast at h1 h2 ⊢ <;> omega
    · constructor <;> push_cast at h1 h2 ⊢ <;> omega

variable {d : ℕ} {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ}

/- English proof (translation)
Establish `hS'` using `hS`. Take `⟨-, -, -, -, -, -, hJ, -, -, -⟩` from `hS'`. Introduce `τ i hτ a ha`. Conclude with `rk_win_box d b S η i (rk_eta_lt W hS i) (hJ i τ hτ a ha)`.
-/
theorem rk_jumpsLet₁ (hS : Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m) :
    Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T₁ (boxM d b S η) (boxH d b S η) := by
  have hS' := hS
  obtain ⟨-, -, -, -, -, -, hJ, -, -, -⟩ := hS'
  intro τ i hτ a ha
  exact rk_win_box d b S η i (rk_eta_lt W hS i) (hJ i τ hτ a ha)

/- English proof (translation)
Take `⟨h1, h2, hon⟩` from `hS.2.2.2.2.2.1`. Introduce `a ha`. Conclude with `hS.2.2.2.2.2.2.1 i τ hτ a (rk_jump_of W hS.1.1 hE hC hQ F h1 h2 hon τ i hτ a ha)`.
-/
theorem rk_jumps₂ (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (hS : Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m) (i : ZMod n)
    (τ : K →ₐ[Qp] LL) (hτ : Formalism.MainNotions.LiftingTheory.Over W τ i) :
    JumpsInV PD T₂.ρ τ (Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS d b S η i) := by
  obtain ⟨h1, h2, hon⟩ := hS.2.2.2.2.2.1
  intro a ha
  exact hS.2.2.2.2.2.2.1 i τ hτ a (rk_jump_of W hS.1.1 hE hC hQ F h1 h2 hon τ i hτ a ha)

/- English proof (translation)
Introduce `τ i hτ a ha`. Conclude with `rk_win_box d b S η i (rk_eta_lt W hS i) (rk_jumps₂ W hE hC hQ hS i τ hτ a ha)`.
-/
theorem rk_jumpsLet₂ (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (hS : Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m) :
    Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T₂ (boxM d b S η) (boxH d b S η) := by
  intro τ i hτ a ha
  exact rk_win_box d b S η i (rk_eta_lt W hS i) (rk_jumps₂ W hE hC hQ hS i τ hτ a ha)

/- English proof (translation)
Establish `hS'` using `hS`. Take `⟨-, -, -, -, -, ⟨-, hC2, -⟩, -, -, -, -⟩` from `hS'`. Use `haveI := T₂.fdim`. Use `haveI := PD.finK₀`. Establish `hle : DcrisL PD T₂.ρ (W.emb i) ≤ Dcris PD T₂.ρ`.

Unfold `Formalism.WeaklyAdmissibleFiltrations.DcrisL`. Conclude with `inf_le_left`. It suffices to establish `h : FiniteDimensional LL ↥(Dcris PD T₂.ρ) from Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)`. Break down `Nat.eq_zero_or_pos (finrank LL T₂.V) with h0 | h0` into its components or cases. Use `haveI : Subsingleton T₂.V := Module.finrank_zero_iff.mp h0 infer_instance`.

Apply `Module.finite_of_finrank_pos` to reduce the goal to its premises. Unfold `Formalism.WeaklyAdmissibleFiltrations.IsCrys at hC2`. Rewrite using `[hC2]`. Conclude with `Nat.mul_pos Module.finrank_pos h0`.
-/
theorem rk_fd_letter₂ (hS : Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m) (i : ZMod n) :
    FiniteDimensional LL ↥(DcrisL PD T₂.ρ (W.emb i)) := by
  have hS' := hS
  obtain ⟨-, -, -, -, -, ⟨-, hC2, -⟩, -, -, -, -⟩ := hS'
  haveI := T₂.fdim
  haveI := PD.finK₀
  have hle : DcrisL PD T₂.ρ (W.emb i) ≤ Dcris PD T₂.ρ := by
    unfold Formalism.WeaklyAdmissibleFiltrations.DcrisL
    exact inf_le_left
  suffices h : FiniteDimensional LL ↥(Dcris PD T₂.ρ) from
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  rcases Nat.eq_zero_or_pos (finrank LL T₂.V) with h0 | h0
  · haveI : Subsingleton T₂.V := Module.finrank_zero_iff.mp h0
    infer_instance
  · apply Module.finite_of_finrank_pos
    unfold Formalism.WeaklyAdmissibleFiltrations.IsCrys at hC2
    rw [hC2]
    exact Nat.mul_pos Module.finrank_pos h0

/- English proof (translation)
Establish `hle : FildR PD T.ρ τ (a + 1) ≤ FildR PD T.ρ τ a`. Unfold `Formalism.WeaklyAdmissibleFiltrations.FildR`. Use `inf_le_inf_left _ ?_` and prove the remaining obligations. Introduce `x hx`. Unfold `Formalism.WeaklyAdmissibleFiltrations.FilV at hx ⊢`.

Take `⟨y, rfl⟩` from `LinearMap.mem_range.mp hx`. Use `clear hx`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v f => exact LinearMap.mem_range.mpr ⟨v ⊗ₜ ⟨(f : BdR), PD.Fil_anti a f.2⟩, by simp⟩`.

Consider the case `add y z hy hz`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hy hz`. Establish `h0 : FildR PD T.ρ τ a ≤ DdRE PD T.ρ τ`. Unfold `Formalism.WeaklyAdmissibleFiltrations.FildR`.

Conclude with `inf_le_left`. Use `haveI hfin : FiniteDimensional LL ↥(FildR PD T.ρ τ a) := Module.Finite.of_injective (Submodule.inclusion h0) (Submodule.inclusion_injective h0)`. Establish `hr : finrank LL ↥(FildR PD T.ρ τ (a + 1)) ≤ finrank LL ↥(FildR PD T.ρ τ a)` using `LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective hle)`. Unfold `Formalism.WeaklyAdmissibleFiltrations.multV`. Use linear arithmetic over natural numbers and integers.
-/
theorem rk_multV_nonneg (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD T.ρ τ)]
    (a : ℤ) : 0 ≤ multV PD T.ρ τ a := by
  have hle : FildR PD T.ρ τ (a + 1) ≤ FildR PD T.ρ τ a := by
    unfold Formalism.WeaklyAdmissibleFiltrations.FildR
    refine inf_le_inf_left _ ?_
    intro x hx
    unfold Formalism.WeaklyAdmissibleFiltrations.FilV at hx ⊢
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    clear hx
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v f => exact LinearMap.mem_range.mpr ⟨v ⊗ₜ ⟨(f : BdR), PD.Fil_anti a f.2⟩, by simp⟩
    | add y z hy hz =>
      rw [map_add]
      exact Submodule.add_mem _ hy hz
  have h0 : FildR PD T.ρ τ a ≤ DdRE PD T.ρ τ := by
    unfold Formalism.WeaklyAdmissibleFiltrations.FildR
    exact inf_le_left
  haveI hfin : FiniteDimensional LL ↥(FildR PD T.ρ τ a) :=
    Module.Finite.of_injective (Submodule.inclusion h0) (Submodule.inclusion_injective h0)
  have hr : finrank LL ↥(FildR PD T.ρ τ (a + 1)) ≤ finrank LL ↥(FildR PD T.ρ τ a) :=
    LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective hle)
  unfold Formalism.WeaklyAdmissibleFiltrations.multV
  omega

/- English proof (translation)
Establish `hK` using `hS.1.1`. Establish `h2` using `hS.2.2.2.2.2.1.2.1`. Take `⟨τ, hτ⟩` from `rk_lift hK (W.emb i)`. Establish `hwin` using `rk_jumps₂ W hE hC hQ hS i τ hτ`. Establish `hsum` using `hS.2.2.2.2.2.2.2.1 i τ hτ`.

Take `⟨-, hτ'⟩` from `hQ hK T₂.V T₂.ρ h2`. Take `⟨hfd, -, hF⟩` from `hτ' τ`. Use `haveI := hfd`. Establish `hrk : ∀ a : ℤ, finrank LL ↥(FilCris PD T₂.ρ a ⊓ DcrisL PD T₂.ρ (W.emb i)) = finrank LL ↥(FildR PD T₂.ρ τ a)` using `fun a => by`. Rewrite using `[hF a, hτ]`.

Conclude with `LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (rk_ιV_inj PD) _)`. Establish `hD : finrank LL ↥(DcrisL PD T₂.ρ (W.emb i)) = finrank LL ↥(DdRE PD T₂.ρ τ)`. Rewrite using `[← rk_DcrisL_map W hK hQ T₂ h2 τ, hτ]`. Conclude with `LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (rk_ιV_inj PD) _)`. Take `⟨lo, hlo⟩` from `rk_fildR_lo PD T₂.ρ τ`.

Establish `hlo' : min lo (min (-(η : ℤ)) (b i : ℤ)) ≤ (b i : ℤ)` using `by omega`. Establish `htel` using `rk_sum_multV PD T₂.ρ τ (min lo (min (-(η : ℤ)) (b i : ℤ))) (b i : ℤ) hlo'`. Rewrite `htel` using `[hlo _ (min_le_left _ _)]`. Rewrite using `[hD, hrk, ← htel]`. Establish `hodd : ¬ ((i.val + d) % 2 = 0)` using `by omega`.

Combine the equalities or inequalities in the displayed calculation. Use `symm`. Apply `Finset.sum_subset (Finset.filter_subset _ _)` to reduce the goal to its premises. Introduce `a ha hna`. Apply `rk_multV_of_not_jump` to reduce the goal to its premises.

Introduce `hj`. Establish `hw` using `hwin a hj`. Simplify using `only [Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS, hodd, if_false, Set.mem_union, Set.mem_Icc] at hw`. Simplify using `only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc, not_and] at ha hna`. Use linear arithmetic over natural numbers and integers.

Use `_ ≤ ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV PD T₂.ρ τ a := Finset.sum_le_sum_of_subset_of_nonneg (fun a ha => (Finset.mem_filter.1 ha).2) (fun a _ _ => rk_multV_nonneg T₂ τ a)`. Use `_ ≤ m := hsum`.
-/
theorem rk_corank₂ (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (hS : Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m) (i : ZMod n)
    (hi : (i.val + d) % 2 = 1) :
    (finrank LL ↥(DcrisL PD T₂.ρ (W.emb i)) : ℤ) -
      finrank LL ↥(FilCris PD T₂.ρ (b i : ℤ) ⊓ DcrisL PD T₂.ρ (W.emb i)) ≤ m := by
  classical
  have hK := hS.1.1
  have h2 := hS.2.2.2.2.2.1.2.1
  obtain ⟨τ, hτ⟩ := rk_lift hK (W.emb i)
  have hwin := rk_jumps₂ W hE hC hQ hS i τ hτ
  have hsum := hS.2.2.2.2.2.2.2.1 i τ hτ
  obtain ⟨-, hτ'⟩ := hQ hK T₂.V T₂.ρ h2
  obtain ⟨hfd, -, hF⟩ := hτ' τ
  haveI := hfd
  have hrk : ∀ a : ℤ, finrank LL ↥(FilCris PD T₂.ρ a ⊓ DcrisL PD T₂.ρ (W.emb i)) =
      finrank LL ↥(FildR PD T₂.ρ τ a) := fun a => by
    rw [hF a, hτ]
    exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (rk_ιV_inj PD) _)
  have hD : finrank LL ↥(DcrisL PD T₂.ρ (W.emb i)) = finrank LL ↥(DdRE PD T₂.ρ τ) := by
    rw [← rk_DcrisL_map W hK hQ T₂ h2 τ, hτ]
    exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (rk_ιV_inj PD) _)
  obtain ⟨lo, hlo⟩ := rk_fildR_lo PD T₂.ρ τ
  have hlo' : min lo (min (-(η : ℤ)) (b i : ℤ)) ≤ (b i : ℤ) := by omega
  have htel := rk_sum_multV PD T₂.ρ τ (min lo (min (-(η : ℤ)) (b i : ℤ))) (b i : ℤ) hlo'
  rw [hlo _ (min_le_left _ _)] at htel
  rw [hD, hrk, ← htel]
  have hodd : ¬ ((i.val + d) % 2 = 0) := by omega
  calc ∑ a ∈ Finset.Ico (min lo (min (-(η : ℤ)) (b i : ℤ))) (b i : ℤ), multV PD T₂.ρ τ a
      = ∑ a ∈ (Finset.Ico (min lo (min (-(η : ℤ)) (b i : ℤ))) (b i : ℤ)).filter
          (fun a => a ∈ Finset.Icc (-(η : ℤ)) η), multV PD T₂.ρ τ a := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro a ha hna
        apply rk_multV_of_not_jump
        intro hj
        have hw := hwin a hj
        simp only [Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS, hodd, if_false, Set.mem_union, Set.mem_Icc] at hw
        simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc, not_and] at ha hna
        omega
    _ ≤ ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV PD T₂.ρ τ a :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun a ha => (Finset.mem_filter.1 ha).2)
          (fun a _ _ => rk_multV_nonneg T₂ τ a)
    _ ≤ m := hsum

/- English proof (translation)
Establish `h` using `rk_corank₂ W hE hC hQ hS i hi`. Use `haveI := rk_fd_letter₂ W hS i`. Use `set D := DcrisL PD T₂.ρ (W.emb i) with hD`. Use `set Fl := FilCris PD T₂.ρ (b i : ℤ) with hFl`. Establish `hrn` using `LinearMap.finrank_range_add_finrank_ker (Fl.mkQ ∘ₗ D.subtype)`.

Establish `hr : LinearMap.range (Fl.mkQ ∘ₗ D.subtype) = D.map Fl.mkQ`. Rewrite using `[LinearMap.range_comp, Submodule.range_subtype]`. Establish `hk : finrank LL ↥(LinearMap.ker (Fl.mkQ ∘ₗ D.subtype)) = finrank LL ↥(Fl ⊓ D)`. Rewrite using `[LinearMap.ker_comp, Submodule.ker_mkQ, ← inf_top_eq (Submodule.comap D.subtype Fl), ← Submodule.comap_subtype_self D, ← Submodule.comap_inf]`. Conclude with `(Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq`.

Rewrite `hrn` using `[hr, hk]`. Use linear arithmetic over natural numbers and integers.
-/
theorem rk_corankQ₂ (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (hS : Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m) (i : ZMod n)
    (hi : (i.val + d) % 2 = 1) :
    finrank LL ↥((DcrisL PD T₂.ρ (W.emb i)).map (FilCris PD T₂.ρ (b i : ℤ)).mkQ) ≤ m := by
  have h := rk_corank₂ W hE hC hQ hS i hi
  haveI := rk_fd_letter₂ W hS i
  set D := DcrisL PD T₂.ρ (W.emb i) with hD
  set Fl := FilCris PD T₂.ρ (b i : ℤ) with hFl
  have hrn := LinearMap.finrank_range_add_finrank_ker (Fl.mkQ ∘ₗ D.subtype)
  have hr : LinearMap.range (Fl.mkQ ∘ₗ D.subtype) = D.map Fl.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : finrank LL ↥(LinearMap.ker (Fl.mkQ ∘ₗ D.subtype)) = finrank LL ↥(Fl ⊓ D) := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, ← inf_top_eq (Submodule.comap D.subtype Fl),
      ← Submodule.comap_subtype_self D, ← Submodule.comap_inf]
    exact (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq
  rw [hr, hk] at hrn
  omega

/- English proof (translation)
Establish `h` using `rk_corankQ₂ W hE hC hQ hS i hi`. Substitute `hm` using the available equality. Use `haveI := rk_fd_letter₂ W hS i`. Establish `hbot : (DcrisL PD T₂.ρ (W.emb i)).map (FilCris PD T₂.ρ (b i : ℤ)).mkQ = ⊥` using `Submodule.finrank_eq_zero.mp (by omega)`. Introduce `x hx`.

Establish `hmem : (FilCris PD T₂.ρ (b i : ℤ)).mkQ x ∈ (DcrisL PD T₂.ρ (W.emb i)).map (FilCris PD T₂.ρ (b i : ℤ)).mkQ` using `Submodule.mem_map_of_mem hx`. Rewrite `hmem` using `[hbot]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).mp ((Submodule.mem_bot LL).mp hmem)`.
-/
theorem rk_corank_zero₂ (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (hS : Formalism.MainNotions.RamifiedCoefficientChains.SetCS W d T₁ T₂ F b S η m) (hm : m = 0)
    (i : ZMod n) (hi : (i.val + d) % 2 = 1) :
    DcrisL PD T₂.ρ (W.emb i) ≤ FilCris PD T₂.ρ (b i : ℤ) := by
  have h := rk_corankQ₂ W hE hC hQ hS i hi
  subst hm
  haveI := rk_fd_letter₂ W hS i
  have hbot : (DcrisL PD T₂.ρ (W.emb i)).map (FilCris PD T₂.ρ (b i : ℤ)).mkQ = ⊥ :=
    Submodule.finrank_eq_zero.mp (by omega)
  intro x hx
  have hmem : (FilCris PD T₂.ρ (b i : ℤ)).mkQ x ∈
      (DcrisL PD T₂.ρ (W.emb i)).map (FilCris PD T₂.ρ (b i : ℤ)).mkQ := Submodule.mem_map_of_mem hx
  rw [hbot] at hmem
  exact (Submodule.Quotient.mk_eq_zero _).mp ((Submodule.mem_bot LL).mp hmem)

end Out

end Formalism.MainNotions.N.Pv.LocalLengthBound
