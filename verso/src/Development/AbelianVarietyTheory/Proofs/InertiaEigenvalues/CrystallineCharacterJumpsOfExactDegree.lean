import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentsCrystallineLettersFinrank
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBoundsCrystallineDeRhamConcreteRings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.Per.CharJumps

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
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b`. Simplify using `[ιV, actVB, actVdR, AlgebraTensorModule.map_tmul, PD.ι_comm]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem ιV_act (g : G) (w : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g w) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp [ιV, actVB, actVdR, AlgebraTensorModule.map_tmul, PD.ι_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Simplify using `only [Dcris, DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hw ⊢`. Introduce `g`. Rewrite using `[← ιV_act, hw g]`.
-/
theorem ιV_mem_DdR {w : V ⊗[Qp] B} (hw : w ∈ Dcris PD ρ) :
    ιV PD (LL := LL) (V := V) w ∈ DdR PD ρ := by
  simp only [Dcris, DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero] at hw ⊢
  intro g
  rw [← ιV_act, hw g]

/- English proof (translation)
Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b`. Simplify using `[ιV, mulVB, mulVdR, AlgebraTensorModule.map_tmul, ← IsScalarTower.algebraMap_apply]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem ιV_mul (a : K₀) (w : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (mulVB (B := B) (V := V) (LL := LL) a w) =
      mulVdR (BdR := BdR) (V := V) (LL := LL) (algebraMap K₀ K a) (ιV PD (LL := LL) (V := V) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp [ιV, mulVB, mulVdR, AlgebraTensorModule.map_tmul, ← IsScalarTower.algebraMap_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Unfold `DcrisL at hw`. Unfold `DdRE`. Rewrite `hw`, the goal using `[Submodule.mem_inf]`. Use `⟨ιV_mem_DdR PD ρ hw.1, ?_⟩` and prove the remaining obligations. Establish `h2` using `hw.2`.

Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h2 ⊢`. Introduce `c`. Take `⟨a, rfl⟩` from `hs c`. Rewrite using `[← ιV_mul, h2 a, map_smul]`. Simplify using the standard rewrite rules.
-/
theorem ιV_mem_DdRE (hs : Function.Surjective (algebraMap K₀ K)) (τ : K →ₐ[Qp] LL)
    {w : V ⊗[Qp] B} (hw : w ∈ DcrisL PD ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))) :
    ιV PD (LL := LL) (V := V) w ∈ DdRE PD ρ τ := by
  unfold DcrisL at hw
  unfold DdRE
  rw [Submodule.mem_inf] at hw ⊢
  refine ⟨ιV_mem_DdR PD ρ hw.1, ?_⟩
  have h2 := hw.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at h2 ⊢
  intro c
  obtain ⟨a, rfl⟩ := hs c
  rw [← ιV_mul, h2 a, map_smul]
  simp

/- English proof (translation)
Introduce and unpack `_ ⟨y, rfl⟩`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v s`. Conclude with `⟨v ⊗ₜ ⟨(s : BdR), PD.Fil_anti a s.2⟩, by simp [AlgebraTensorModule.map_tmul]⟩`.

Consider the case `add x y hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`.
-/
theorem FilV_succ_le (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v s =>
    exact ⟨v ⊗ₜ ⟨(s : BdR), PD.Fil_anti a s.2⟩, by simp [AlgebraTensorModule.map_tmul]⟩
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/- English proof (translation)
The claim follows from `antitone_int_of_succ_le (FilV_succ_le PD)`.
-/
theorem FilV_anti : Antitone fun a : ℤ => FilV PD (LL := LL) (V := V) a :=
  antitone_int_of_succ_le (FilV_succ_le PD)

end General

end GlobalTheory.Per.CharJumps

namespace GlobalTheory.Per.CharJumps

/- English proof (translation)
Establish `hx0 : x ≠ 0` using `fun h => h2 (h ▸ (F (d + 1)).zero_mem)`. Establish `hspan : ∀ y ∈ D, ∃ c : LL, c • x = y`. Introduce `y hy`. Take `⟨c, hc⟩` from `(finrank_eq_one_iff_of_nonzero' (⟨x, hx⟩ : ↥D) (fun h => hx0 (congrArg Subtype.val h))).1 hD ⟨y, hy⟩`. Conclude with `⟨c, congrArg Subtype.val hc⟩`.

Use `split_ifs with hb`. Use `inf_eq_left.2 fun y hy => ?_` and prove the remaining obligations. Take `⟨c, rfl⟩` from `hspan y hy`. Conclude with `(F b).smul_mem c (hF hb h1)`. Rewrite using `[eq_bot_iff]`.

Introduce `y hy`. Rewrite `hy` using `[Submodule.mem_inf]`. Take `⟨c, rfl⟩` from `hspan _ hy.1`. Rewrite using `[Submodule.mem_bot]`. Distinguish the cases in `hc : c = 0`.

Simplify using `[hc]`. It suffices to derive a contradiction. Apply `h2` to reduce the goal to its premises. Establish `hxe : x = c⁻¹ • (c • x)` using `by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]`. Rewrite using `[hxe]`.

Conclude with `hF (by omega) ((F b).smul_mem _ hy.2)`.
-/
theorem inf_of_line {LL M : Type} [Field LL] [AddCommGroup M] [Module LL M] (D : Submodule LL M)
    (hD : finrank LL ↥D = 1) (F : ℤ → Submodule LL M) (hF : Antitone F) {x : M} (hx : x ∈ D)
    (d : ℤ) (h1 : x ∈ F d) (h2 : x ∉ F (d + 1)) (b : ℤ) :
    D ⊓ F b = if b ≤ d then D else ⊥ := by
  have hx0 : x ≠ 0 := fun h => h2 (h ▸ (F (d + 1)).zero_mem)
  have hspan : ∀ y ∈ D, ∃ c : LL, c • x = y := by
    intro y hy
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨x, hx⟩ : ↥D)
      (fun h => hx0 (congrArg Subtype.val h))).1 hD ⟨y, hy⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  split_ifs with hb
  · refine inf_eq_left.2 fun y hy => ?_
    obtain ⟨c, rfl⟩ := hspan y hy
    exact (F b).smul_mem c (hF hb h1)
  · rw [eq_bot_iff]
    intro y hy
    rw [Submodule.mem_inf] at hy
    obtain ⟨c, rfl⟩ := hspan _ hy.1
    rw [Submodule.mem_bot]
    by_cases hc : c = 0
    · simp [hc]
    · exfalso
      apply h2
      have hxe : x = c⁻¹ • (c • x) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [hxe]
      exact hF (by omega) ((F b).smul_mem _ hy.2)

/- English proof (translation)
Introduce `l _ P AI T K LL hA μ hμ d hw hcrys τ b`. Use `haveI := LL.2`. Use `haveI := K.2`. Establish `hdr : IsDR (P.PD K) (charRep μ)`. Set `A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)` to `{ V := ↥LL.1, ρ := charRep μ, cont := fun x => by show Continuous fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1) • LinearMap.id x`.

Conclude with `hμ.smul continuous_const }`. Conclude with `((GlobalTheory.Per.FontaineTied.fontCore_all_of_tied l P AI T K) ↥LL.1 ↥(OL LL) (GlobalTheory.LocalIntegers.good_integers l LL).1 A).2.2 hcrys`. Take `⟨-, -, hdim⟩` from `(GlobalTheory.Per.Components.components_finrank l P AI T K LL ↥LL.1 (charRep μ)).1 τ`. Establish `h1 : finrank ↥LL.1 ↥(DdRE (P.PD K) (charRep μ) τ) = 1`. Rewrite using `[hdim hdr, Module.finrank_self]`.

Establish `hs : Function.Surjective (algebraMap ↥(K0 K) ↥K.1)` using `fun c => ⟨⟨c.1, c.2, hA.1 c.2⟩, rfl⟩`. Take `⟨w, hwD, hin, hout⟩` from `hw τ`. Establish `hx` using `ιV_mem_DdRE (P.PD K) (charRep μ) hs τ hwD`. Establish `key` using `inf_of_line _ h1 _ (FilV_anti (P.PD K)) hx (d τ) hin hout`. Establish `fk : ∀ c : ℤ, (finrank ↥LL.1 ↥(FildR (P.PD K) (charRep μ) τ c) : ℤ) = if c ≤ d τ then 1 else 0`.

Introduce `c`. Unfold `FildR`. Rewrite using `[key c]`. Distinguish the cases in `hc : c ≤ d τ`. Rewrite using `[if_pos hc, if_pos hc, h1]`.

Both sides reduce to the same expression. Rewrite using `[if_neg hc, if_neg hc, finrank_bot]`. Both sides reduce to the same expression. Unfold `multV`. Rewrite using `[fk b, fk (b + 1)]`.

Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem jumps_of_exact_degree : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → ∀ d : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ, (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)), ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ) ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ + 1)) → IsCrys (P.PD K) (charRep μ) → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = d τ then 1 else 0 := by
  intro l _ P AI T K LL hA μ hμ d hw hcrys τ b
  haveI := LL.2
  haveI := K.2
  have hdr : IsDR (P.PD K) (charRep μ) := by
    let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
      { V := ↥LL.1, ρ := charRep μ,
        cont := fun x => by
          show Continuous fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1) • LinearMap.id x
          exact hμ.smul continuous_const }
    exact ((GlobalTheory.Per.FontaineTied.fontCore_all_of_tied l P AI T K) ↥LL.1 ↥(OL LL)
      (GlobalTheory.LocalIntegers.good_integers l LL).1 A).2.2 hcrys
  obtain ⟨-, -, hdim⟩ := (GlobalTheory.Per.Components.components_finrank l P AI T K LL ↥LL.1 (charRep μ)).1 τ
  have h1 : finrank ↥LL.1 ↥(DdRE (P.PD K) (charRep μ) τ) = 1 := by
    rw [hdim hdr, Module.finrank_self]
  have hs : Function.Surjective (algebraMap ↥(K0 K) ↥K.1) :=
    fun c => ⟨⟨c.1, c.2, hA.1 c.2⟩, rfl⟩
  obtain ⟨w, hwD, hin, hout⟩ := hw τ
  have hx := ιV_mem_DdRE (P.PD K) (charRep μ) hs τ hwD
  have key := inf_of_line _ h1 _ (FilV_anti (P.PD K)) hx (d τ) hin hout
  have fk : ∀ c : ℤ, (finrank ↥LL.1 ↥(FildR (P.PD K) (charRep μ) τ c) : ℤ) = if c ≤ d τ then 1 else 0 := by
    intro c
    unfold FildR
    rw [key c]
    by_cases hc : c ≤ d τ
    · rw [if_pos hc, if_pos hc, h1]
      rfl
    · rw [if_neg hc, if_neg hc, finrank_bot]
      rfl
  unfold multV
  rw [fk b, fk (b + 1)]
  split_ifs <;> omega

end GlobalTheory.Per.CharJumps
