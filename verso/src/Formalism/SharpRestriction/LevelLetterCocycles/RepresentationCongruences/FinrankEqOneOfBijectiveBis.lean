import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcGamLiftCore
import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Module

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

/- English proof (translation)
Assemble the required witnesses or components as `⟨x ⊗ₜ[Qp] (⟨y, hy⟩ : ↥((PD.Fil a).restrictScalars Qp)), by simp [TensorProduct.AlgebraTensorModule.map_tmul]⟩`.
-/
theorem tmul_mem_filtration (x : V) {y : BdR} {a : ℤ} (hy : y ∈ PD.Fil a) :
    x ⊗ₜ[Qp] y ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨x ⊗ₜ[Qp] (⟨y, hy⟩ : ↥((PD.Fil a).restrictScalars Qp)), by
    simp [TensorProduct.AlgebraTensorModule.map_tmul]⟩

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, Submodule.zero_mem _⟩`. Consider the case `tmul x y`. Take `⟨a, ha⟩` from `PD.Fil_exh y`. Conclude with `⟨a, tmul_mem_filtration x ha⟩`.

Consider the case `add x y hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Conclude with `⟨min a b, Submodule.add_mem _ (Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (min_le_left a b) ha) (Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (min_le_right a b) hb)⟩`.
-/
theorem filtration_exhaustive (z : V ⊗[Qp] BdR) : ∃ a, z ∈ FilV PD (LL := LL) (V := V) a := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul x y =>
    obtain ⟨a, ha⟩ := PD.Fil_exh y
    exact ⟨a, tmul_mem_filtration x ha⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, Submodule.add_mem _ (Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (min_le_left a b) ha)
      (Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (min_le_right a b) hb)⟩

end Gen

section Cores

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

/- English proof (translation)
The claim follows from `(LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hb).finrank_eq.symm.trans (Module.finrank_self K₀)`.
-/
theorem finrank_eq_one_of_bijective_bis (hb : Function.Bijective (algebraMap K₀ K)) : Module.finrank K₀ K = 1 :=
  (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hb).finrank_eq.symm.trans (Module.finrank_self K₀)

/- English proof (translation)
Establish `h3` using `(hH hA T hT i).2.2.1 d b hb 0 ⟨0, Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_zero W T i, (smul_zero _).symm⟩`. Use `choose sol hsol using fun k : Fin d => (h3 (Pi.single k 1)).1`. Use `⟨sol, hb, fun k => ⟨(hsol k).1, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[(hsol k).2]`. Use function extensionality and compare the values at `m`.

Distinguish the cases in `h : m = k`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem exists_horizontal_solutions (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) (i : ZMod n) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T i b) : ∃ sol, IsHor W T i b sol := by
  have h3 := (hH hA T hT i).2.2.1 d b hb 0
    ⟨0, Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_zero W T i, (smul_zero _).symm⟩
  choose sol hsol using fun k : Fin d => (h3 (Pi.single k 1)).1
  refine ⟨sol, hb, fun k => ⟨(hsol k).1, ?_⟩⟩
  rw [(hsol k).2]
  funext m
  by_cases h : m = k
  · subst h; simp
  · simp [h]

/- English proof (translation)
Introduce `hCA _ A _ T hT c`. Establish `hmod` using `((hP9 T hT.1 hCA.2.1 hCA.2.2).2.2 (finrank_eq_one_of_bijective_bis hCA.1)).2`. Take `⟨d, b, hb⟩` from `Formalism.MainNotions.UnusedSlot80.Relay2.frame_exists W T c hmod`. Take `⟨sol, hsol⟩` from `exists_horizontal_solutions W hH hCA T hT.1 c b hb`. Conclude with `⟨d, b, sol, hsol⟩`.
-/
theorem horizontal_frame_structure (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) :
    Formalism.MainNotions.N.FrobeniusPowerSeries.HorFrameCore W := by
  intro hCA _ A _ T hT c
  have hmod := ((hP9 T hT.1 hCA.2.1 hCA.2.2).2.2 (finrank_eq_one_of_bijective_bis hCA.1)).2
  obtain ⟨d, b, hb⟩ := Formalism.MainNotions.UnusedSlot80.Relay2.frame_exists W T c hmod
  obtain ⟨sol, hsol⟩ := exists_horizontal_solutions W hH hCA T hT.1 c b hb
  exact ⟨d, b, sol, hsol⟩

/- English proof (translation)
Set `E : K₀ ≃ₐ[Qp] K` to `AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hbij`. Use `⟨(W.emb c).comp E.symm.toAlgHom, ?_, fun x => ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Simplify using `only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]`. Use `congr 1`.

Conclude with `E.symm_apply_apply x`. Simplify using `only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]`. Use `congr 1`. Conclude with `E.symm_apply_apply x`.
-/
theorem exists_algHom_over_of_bijective_algebraMap (hbij : Function.Bijective (algebraMap K₀ K)) (c : ZMod n) :
    ∃ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ c ∧ ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x := by
  let E : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hbij
  refine ⟨(W.emb c).comp E.symm.toAlgHom, ?_, fun x => ?_⟩
  · ext x
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
    congr 1
    exact E.symm_apply_apply x
  · simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
    congr 1
    exact E.symm_apply_apply x

/- English proof (translation)
Unfold `dvO dv`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, pow_succ', Module.End.mul_apply]`.
-/
theorem frobenius_vector_succ (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (c₀ : Fin d → O) :
    dvO W T (e + 1) b c₀ = Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V) (dvO W T e b c₀) := by
  unfold dvO dv
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, pow_succ', Module.End.mul_apply]

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero => simp`. Consider the case `succ s ih => rw [← add_assoc, frobenius_vector_succ, ih, pow_succ', Module.End.mul_apply]`.
-/
theorem frobenius_vector_add (T : LocLat G Qp LL O) (e s : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (c₀ : Fin d → O) :
    dvO W T (e + s) b c₀ = ((Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) ^ s) (dvO W T e b c₀) := by
  induction s with
  | zero => simp
  | succ s ih => rw [← add_assoc, frobenius_vector_succ, ih, pow_succ', Module.End.mul_apply]

/- English proof (translation)
Unfold `dvO dv`. Use `Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `hbN : b m ∈ W.N T` using `(hb.1 m).1.1`. Establish `hbl : (letE c' : LetA O n) • b m = b m` using `Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T c' (hb.1 m).2`. Establish `hcl : cmpD W T (b m) ∈ DcrisL PD T.ρ (W.emb c')`.

Rewrite using `[Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hbN]`. Conclude with `Formalism.MainNotions.UnusedSlot80.ArcF.cmp_mem_letter W T c' hbN hbl`. Conclude with `Formalism.MainNotions.UnusedSlot80.ArcF.φVB_pow_letter W T c' hcl e`.
-/
theorem frobenius_vector_mem_dcris (T : LocLat G Qp LL O) (c' : ZMod n) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e : ℕ) (c₀ : Fin d → O) :
    dvO W T e b c₀ ∈ DcrisL PD T.ρ (W.emb (c' + (e : ZMod n))) := by
  unfold dvO dv
  refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
  have hbN : b m ∈ W.N T := (hb.1 m).1.1
  have hbl : (letE c' : LetA O n) • b m = b m := Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T c' (hb.1 m).2
  have hcl : cmpD W T (b m) ∈ DcrisL PD T.ρ (W.emb c') := by
    rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hbN]; exact Formalism.MainNotions.UnusedSlot80.ArcF.cmp_mem_letter W T c' hbN hbl
  exact Formalism.MainNotions.UnusedSlot80.ArcF.φVB_pow_letter W T c' hcl e

/- English proof (translation)
Establish `hι : ιV PD (LL` using `LL) (V := T.V) x ∈ DdRE PD T.ρ τ := Formalism.MainNotions.UnusedSlot80.LevR.ιDi_le W T c τ hover hsurj ⟨x, hxD, rfl⟩`. Establish `h1 : ιV PD (LL` using `LL) (V := T.V) x ∈ FildR PD T.ρ τ a := ⟨hι, hx.2⟩`. Establish `heq : FildR PD T.ρ τ (a + 1) = FildR PD T.ρ τ a`. Assume the negation of the conclusion as `hne`. Conclude with `hna hne`.

Rewrite `h1` using `[← heq]`. Conclude with `⟨hx.1, h1.2⟩`.
-/
theorem filtration_succ_of_not_jump (T : LocLat G Qp LL O) (c : ZMod n) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x) (hsurj : Function.Surjective (algebraMap K₀ K))
    (a : ℤ) (hna : ¬ IsJumpV PD T.ρ τ a) {x : T.V ⊗[Qp] B} (hxD : x ∈ DcrisL PD T.ρ (W.emb c))
    (hx : x ∈ FilCris PD T.ρ a) : x ∈ FilCris PD T.ρ (a + 1) := by
  have hι : ιV PD (LL := LL) (V := T.V) x ∈ DdRE PD T.ρ τ :=
    Formalism.MainNotions.UnusedSlot80.LevR.ιDi_le W T c τ hover hsurj ⟨x, hxD, rfl⟩
  have h1 : ιV PD (LL := LL) (V := T.V) x ∈ FildR PD T.ρ τ a := ⟨hι, hx.2⟩
  have heq : FildR PD T.ρ τ (a + 1) = FildR PD T.ρ τ a := by
    by_contra hne; exact hna hne
  rw [← heq] at h1
  exact ⟨hx.1, h1.2⟩

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro _`. Simplify using `using hx`. Consider the case `succ k ih`.

Introduce `hj`. Establish `h1` using `ih fun a ha hua => by have := hj a ha hua; push_cast at this; omega`. Use `filtration_succ_of_not_jump W T i τ hover hsurj (u + k) (fun hja => by have := hj _ hja (by omega); push_cast at this; omega) hxD h1` as an intermediate fact. Use `push_cast`. Rewrite using `[← add_assoc]` and apply the resulting hypothesis.
-/
theorem filtration_up_to_jumps (T : LocLat G Qp LL O) (i : ZMod n) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb i x) (hsurj : Function.Surjective (algebraMap K₀ K))
    {x : T.V ⊗[Qp] B} (hxD : x ∈ DcrisL PD T.ρ (W.emb i)) (u : ℤ) (hx : x ∈ FilCris PD T.ρ u) :
    ∀ k : ℕ, (∀ a, IsJumpV PD T.ρ τ a → u ≤ a → u + k ≤ a) → x ∈ FilCris PD T.ρ (u + k) := by
  intro k
  induction k with
  | zero => intro _; simpa using hx
  | succ k ih =>
    intro hj
    have h1 := ih fun a ha hua => by have := hj a ha hua; push_cast at this; omega
    have := filtration_succ_of_not_jump W T i τ hover hsurj (u + k)
      (fun hja => by have := hj _ hja (by omega); push_cast at this; omega) hxD h1
    push_cast; rwa [← add_assoc]

/- English proof (translation)
Take `⟨u₀, hu₀⟩` from `filtration_exhaustive (PD := PD) (LL := LL) (ιV PD (LL := LL) (V := T.V) x)`. Establish `hx0 : x ∈ FilCris PD T.ρ u₀` using `⟨hxD.1, hu₀⟩`. Distinguish the cases in `hle : u ≤ u₀`. Conclude with `Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ hle hx0`. Use `filtration_up_to_jumps W T i τ hover hsurj hxD u₀ hx0 (u - u₀).toNat (fun a ha _ => by have := hJ a ha; omega)` as an intermediate fact.

Rewrite `this` using `[show u₀ + ((u - u₀).toNat : ℤ) = u by omega]`. Then use the resulting hypothesis.
-/
theorem filtration_below_jumps (T : LocLat G Qp LL O) (i : ZMod n) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb i x) (hsurj : Function.Surjective (algebraMap K₀ K))
    (u : ℤ) (hJ : ∀ a, IsJumpV PD T.ρ τ a → u ≤ a) {x : T.V ⊗[Qp] B}
    (hxD : x ∈ DcrisL PD T.ρ (W.emb i)) : x ∈ FilCris PD T.ρ u := by
  obtain ⟨u₀, hu₀⟩ := filtration_exhaustive (PD := PD) (LL := LL) (ιV PD (LL := LL) (V := T.V) x)
  have hx0 : x ∈ FilCris PD T.ρ u₀ := ⟨hxD.1, hu₀⟩
  by_cases hle : u ≤ u₀
  · exact Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ hle hx0
  · have := filtration_up_to_jumps W T i τ hover hsurj hxD u₀ hx0 (u - u₀).toNat
      (fun a ha _ => by have := hJ a ha; omega)
    rwa [show u₀ + ((u - u₀).toNat : ℤ) = u by omega] at this

/- English proof (translation)
Introduce `hCA _ A hA c _ e _ _ T hT d b sol hb c₀ s hs`. Establish `hbf` using `hb.1`. Use `set c' : ZMod n := c - ((A.len c : ℕ) : ZMod n) with hc'`. Use `set i : ZMod n := c' + (e : ZMod n) - (s : ZMod n) with hidef`. Establish `hi : i = c' + ((e - s : ℕ) : ZMod n)` using `by rw [hidef]; push_cast [Nat.cast_sub hs.le]; ring`.

Take `⟨τ, hτ, hover⟩` from `exists_algHom_over_of_bijective_algebraMap W hCA.1 i`. Establish `hyD : dvO W T (e - s) b c₀ ∈ DcrisL PD T.ρ (W.emb i)`. Rewrite using `[hi]`. Conclude with `frobenius_vector_mem_dcris W T c' b hbf (e - s) c₀`. Establish `hye : ((φVB PD (LL` using `LL) (V := T.V)) ^ s) (dvO W T (e - s) b c₀) = dvO W T e b c₀ := by`.

Rewrite using `[← frobenius_vector_add, Nat.sub_add_cancel hs.le]`. Use `⟨fun u hu => ?_, fun bs hty hmem => ?_⟩` and prove the remaining obligations. Establish `hJ : ∀ a, IsJumpV PD T.ρ τ a → u ≤ a` using `fun a ha => hu a (hT.2 i τ hτ a ha)`. Conclude with `⟨_, ⟨filtration_below_jumps W T i τ hover hCA.1.2 u hJ hyD, hyD⟩, hye⟩`. Take `⟨y, ⟨hyF, hyD'⟩, hye'⟩` from `hmem`.

Establish `hok : A.η < bs` using `by have := hA.2.2.2.2.1 i; rw [hty] at this; exact this`. Establish `hup` using `filtration_up_to_jumps W T i τ hover hCA.1.2 hyD' _ hyF (bs - (A.η + 1)) (fun a ha hua => by`. Establish `hw` using `hT.2 i τ hτ a ha`. Rewrite `hw` using `[hty]`. Simplify using `only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at hw`.

Use the proof step `omega)`. Rewrite `hup` using `[show (A.η : ℤ) + 1 + ((bs - (A.η + 1) : ℕ) : ℤ) = (bs : ℤ) by omega]`. Conclude with `⟨y, ⟨hup, hyD'⟩, hye'⟩`.
-/
theorem arc_filtration_low : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcFilLowCore W := by
  intro hCA _ A hA c _ e _ _ T hT d b sol hb c₀ s hs
  have hbf := hb.1
  set c' : ZMod n := c - ((A.len c : ℕ) : ZMod n) with hc'
  set i : ZMod n := c' + (e : ZMod n) - (s : ZMod n) with hidef
  have hi : i = c' + ((e - s : ℕ) : ZMod n) := by rw [hidef]; push_cast [Nat.cast_sub hs.le]; ring
  obtain ⟨τ, hτ, hover⟩ := exists_algHom_over_of_bijective_algebraMap W hCA.1 i
  have hyD : dvO W T (e - s) b c₀ ∈ DcrisL PD T.ρ (W.emb i) := by
    rw [hi]; exact frobenius_vector_mem_dcris W T c' b hbf (e - s) c₀
  have hye : ((φVB PD (LL := LL) (V := T.V)) ^ s) (dvO W T (e - s) b c₀) = dvO W T e b c₀ := by
    rw [← frobenius_vector_add, Nat.sub_add_cancel hs.le]
  refine ⟨fun u hu => ?_, fun bs hty hmem => ?_⟩
  · have hJ : ∀ a, IsJumpV PD T.ρ τ a → u ≤ a := fun a ha => hu a (hT.2 i τ hτ a ha)
    exact ⟨_, ⟨filtration_below_jumps W T i τ hover hCA.1.2 u hJ hyD, hyD⟩, hye⟩
  · obtain ⟨y, ⟨hyF, hyD'⟩, hye'⟩ := hmem
    have hok : A.η < bs := by have := hA.2.2.2.2.1 i; rw [hty] at this; exact this
    have hup := filtration_up_to_jumps W T i τ hover hCA.1.2 hyD' _ hyF (bs - (A.η + 1))
      (fun a ha hua => by
        have hw := hT.2 i τ hτ a ha
        rw [hty] at hw
        simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at hw
        omega)
    rw [show (A.η : ℤ) + 1 + ((bs - (A.η + 1) : ℕ) : ℤ) = (bs : ℤ) by omega] at hup
    exact ⟨y, ⟨hup, hyD'⟩, hye'⟩

end Cores

end Formalism.MainNotions.N.Ln17
