import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThinLetterType
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.FilVSep
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPhiBridge
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.AcoordSumVecMul
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LemGBInImgIff

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

open scoped TensorProduct

namespace ArcLengthTwo

variable (W : LocWach PD LL O v n)

/- English proof (translation)
Establish `h : ∀ y, φVB PD (LL` using `LL) (V := V) y = ((PD.φ.toLinearMap.restrictScalars Qp).lTensor V) y := fun y => by`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x b => simp [φVB]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.

Establish `hi : Function.Injective (PD.φ.toLinearMap.restrictScalars Qp)` using `PD.φ_inj`. Introduce `a b hab`. Rewrite `hab` using `[h, h]`. Conclude with `Module.Flat.lTensor_preserves_injective_linearMap _ hi hab`.
-/
theorem φVB_inj {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] :
    Function.Injective (φVB PD (LL := LL) (V := V)) := by
  have h : ∀ y, φVB PD (LL := LL) (V := V) y = ((PD.φ.toLinearMap.restrictScalars Qp).lTensor V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [φVB]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hi : Function.Injective (PD.φ.toLinearMap.restrictScalars Qp) := PD.φ_inj
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hi hab

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x b => simp [Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap, φVB]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem crisMap_φ {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] (f : V →ₗ[LL] V') (x : V ⊗[Qp] B) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B f (φVB PD (LL := LL) (V := V) x) = φVB PD (LL := LL) (V := V') (Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap, φVB]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Simplify using `only [dv, map_sum, map_smul, pow_succ', Module.End.mul_apply]`.
-/
theorem dv_succ (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → LL) :
    dv W T (e + 1) b c₀ = φVB PD (LL := LL) (V := T.V) (dv W T e b c₀) := by
  simp only [dv, map_sum, map_smul, pow_succ', Module.End.mul_apply]

/- English proof (translation)
The claim follows from `dv_succ W T e b _`.
-/
theorem dvO_succ (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → O) :
    dvO W T (e + 1) b c₀ = φVB PD (LL := LL) (V := T.V) (dvO W T e b c₀) :=
  dv_succ W T e b _

/- English proof (translation)
Unfold `dvO`. Use `congr 1`. Use function extensionality and compare the values at `m`. Distinguish the cases in `h : m = k`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`.
-/
theorem dvO_single (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (k : Fin d) :
    dvO W T e b (Pi.single k 1) = dv W T e b (Pi.single k 1) := by
  unfold dvO
  congr 1
  funext m
  by_cases h : m = k
  · subst h; simp
  · simp [Pi.single_apply, h]

/- English proof (translation)
Unfold `dv`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single m (fun m' _ hm' => by simp [Pi.single_apply, hm']) (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem dv_eq_sum (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → LL) :
    dv W T e b c₀ = ∑ m, c₀ m • dv W T e b (Pi.single m 1) := by
  unfold dv
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_eq_single m (fun m' _ hm' => by simp [Pi.single_apply, hm']) (by simp)]
  simp

/- English proof (translation)
Simplify using `only [dvO, dv, map_sum, map_mul, Finset.smul_sum, Finset.sum_smul, smul_smul]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem dvO_lin (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) {I : Type} (s : Finset I)
    (a : I → O) (c₀ : I → Fin d → O) :
    dvO W T e b (fun m => ∑ i ∈ s, a i * c₀ i m) = ∑ i ∈ s, algebraMap O LL (a i) • dvO W T e b (c₀ i) := by
  simp only [dvO, dv, map_sum, map_mul, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

/- English proof (translation)
Simplify using `only [dvO, dv, map_mul, Finset.smul_sum, smul_smul]`.
-/
theorem dvO_smul (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (x : O) (c₀ : Fin d → O) :
    dvO W T e b (fun m => x * c₀ m) = algebraMap O LL x • dvO W T e b c₀ := by
  simp only [dvO, dv, map_mul, Finset.smul_sum, smul_smul]

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `hx`. Use `⟨y, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hac]`. Simplify using `using hy`. Simplify using the standard rewrite rules.
-/
theorem filS_φ (T : LocLat G Qp LL O) {a c : ZMod n} (hac : c - ((1 : ℕ) : ZMod n) = a) {u : ℤ}
    {x : T.V ⊗[Qp] B} (hx : x ∈ FilS W T a 0 u) : φVB PD (LL := LL) (V := T.V) x ∈ FilS W T c 1 u := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨y, ?_, ?_⟩
  · rw [hac]
    simpa using hy
  · simp

/- English proof (translation)
Take `⟨y, hy, hyx⟩` from `hx`. Establish `: y = x` using `φVB_inj (by simpa using hyx)`. Substitute `this` using the available equality. Use `⟨y, ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[← hac]`.

Simplify using `using hy`.
-/
theorem filS_φ_inv (T : LocLat G Qp LL O) {a c : ZMod n} (hac : c - ((1 : ℕ) : ZMod n) = a) {u : ℤ}
    {x : T.V ⊗[Qp] B} (hx : φVB PD (LL := LL) (V := T.V) x ∈ FilS W T c 1 u) : x ∈ FilS W T a 0 u := by
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := φVB_inj (by simpa using hyx)
  subst this
  refine ⟨y, ?_, by simp⟩
  rw [← hac]
  simpa using hy

/- English proof (translation)
The claim follows from `Submodule.map_mono (inf_le_inf_right _ (Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ h))`.
-/
theorem filS_anti (T : LocLat G Qp LL O) (a : ZMod n) (s : ℕ) {u u' : ℤ} (h : u ≤ u') :
    FilS W T a s u' ≤ FilS W T a s u :=
  Submodule.map_mono (inf_le_inf_right _ (Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ h))

/- English proof (translation)
Take `⟨κ, κ', H, a', hH, ha', hP⟩` from `h`. Use `⟨κ, κ', H, fun k => a * a' k, hH, fun k => ⟨mul_mem ha (ha' k).1, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ← (ha' k).2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hs : ∑ k, (a * a' k) • ((W.φD T) ^ e) (H k) = a • ∑ k, a' k • ((W.φD T) ^ e) (H k)`.

Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_smul _ _ _`. Rewrite using `[hs]`. Establish `key : lA W ^ κ' • (lA W ^ κ • Λ • (a • x) - a • ∑ k, a' k • ((W.φD T) ^ e) (H k)) = a • (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a' k • ((W.φD T) ^ e) (H k)))`. Rewrite using `[smul_sub, smul_sub, smul_sub, smul_comm a (lA W ^ κ') (lA W ^ κ • Λ • x), smul_comm a (lA W ^ κ) (Λ • x), smul_comm a Λ x, smul_comm a (lA W ^ κ')]`.

Rewrite using `[key]`. Conclude with `TypesA.inMultiple_smul W ha hP`.
-/
theorem RepVV_smulA {T : LocLat G Qp LL O} {c' : ZMod n} {e M : ℕ} {Λ : LetA O n} {d : ℕ}
    {b : Fin d → W.DD T} {sol : Fin d → ℕ → Fin d → LL} {a : LetA O n} (ha : a ∈ W.AΔ) {x : W.DD T}
    {f : Fin d → W.EE} (h : RepVV W T c' e M Λ b sol x f) :
    RepVV W T c' e M Λ b sol (a • x) (fun k => algebraMap (LetA O n) W.EE a * f k) := by
  obtain ⟨κ, κ', H, a', hH, ha', hP⟩ := h
  refine ⟨κ, κ', H, fun k => a * a' k, hH,
    fun k => ⟨mul_mem ha (ha' k).1, ?_⟩, ?_⟩
  · rw [map_mul, ← (ha' k).2]
    ring
  · have hs : ∑ k, (a * a' k) • ((W.φD T) ^ e) (H k) = a • ∑ k, a' k • ((W.φD T) ^ e) (H k) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => mul_smul _ _ _
    rw [hs]
    have key : lA W ^ κ' • (lA W ^ κ • Λ • (a • x) - a • ∑ k, a' k • ((W.φD T) ^ e) (H k)) =
        a • (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a' k • ((W.φD T) ^ e) (H k))) := by
      rw [smul_sub, smul_sub, smul_sub, smul_comm a (lA W ^ κ') (lA W ^ κ • Λ • x), smul_comm a (lA W ^ κ) (Λ • x),
        smul_comm a Λ x, smul_comm a (lA W ^ κ')]
    rw [key]
    exact TypesA.inMultiple_smul W ha hP

/- English proof (translation)
Use `W.γD_smul T g (algebraMap (LetA O n) W.EE a) x` as an intermediate fact. Rewrite `this` using `[algebraMap_smul, W.γE_ext, algebraMap_smul]`. Conclude with `this`.
-/
theorem γD_smulA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

/- English proof (translation)
Use function extensionality and compare the values at `k`. Distinguish the cases in `h : k = i`. Substitute `h` using the available equality. Simplify using `[LocWach.γA, letγ, letE]`. Simplify using `[LocWach.γA, letγ, letE, Pi.single_apply, h]`.
-/
theorem γA_letE (g : W.Gam) (i : ZMod n) : W.γA g (letE i : LetA O n) = letE i := by
  funext k
  by_cases h : k = i
  · subst h; simp [LocWach.γA, letγ, letE]
  · simp [LocWach.γA, letγ, letE, Pi.single_apply, h]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Distinguish the cases in `h : k = i`. Substitute `h` using the available equality. Simplify using `[letE]`. Simplify using `[letE, Pi.single_apply, h]`.
-/
theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  funext k
  by_cases h : k = i
  · subst h; simp [letE]
  · simp [letE, Pi.single_apply, h]

/- English proof (translation)
Use `⟨⟨Submodule.sum_mem _ fun δ _ => W.N_Γ T δ z hz, fun δ' hδ' => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Finset.sum_nbij' (δ' * ·) (δ'⁻¹ * ·) (fun g hg => TypesA.delF_mul W hδ' hg) (fun g hg => TypesA.delF_mul W (TypesA.delF_inv W hδ') hg) (fun g _ => by simp) (fun g _ => by simp) (fun g _ => ?_)` and prove the remaining obligations. Rewrite using `[W.γD_mul]`. Rewrite using `[Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun δ _ => ?_` and prove the remaining obligations. Rewrite using `[← γA_letE W δ a, ← γD_smulA, hza]`.
-/
theorem avg_props {T : LocLat G Qp LL O} (a : ZMod n) {z : W.DD T} (hz : z ∈ W.N T)
    (hza : (letE a : LetA O n) • z = z) :
    (∑ δ ∈ W.DelF, W.γD T δ z) ∈ W.NΔ T ∧
      (letE a : LetA O n) • (∑ δ ∈ W.DelF, W.γD T δ z) = ∑ δ ∈ W.DelF, W.γD T δ z := by
  refine ⟨⟨Submodule.sum_mem _ fun δ _ => W.N_Γ T δ z hz, fun δ' hδ' => ?_⟩, ?_⟩
  · rw [map_sum]
    refine Finset.sum_nbij' (δ' * ·) (δ'⁻¹ * ·) (fun g hg => TypesA.delF_mul W hδ' hg)
      (fun g hg => TypesA.delF_mul W (TypesA.delF_inv W hδ') hg) (fun g _ => by simp) (fun g _ => by simp)
      (fun g _ => ?_)
    rw [W.γD_mul]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [← γA_letE W δ a, ← γD_smulA, hza]

end ArcLengthTwo

end Formalism.MainNotions.N.FrobeniusPowerSeries
