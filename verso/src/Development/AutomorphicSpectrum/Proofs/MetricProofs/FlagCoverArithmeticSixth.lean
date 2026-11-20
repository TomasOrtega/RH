import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.BaseForm

variable {K : Type} {ι : K → Type}

def incl (S : K → Prop) : (Σ k : {k // S k}, ι k.1) → (Σ k, ι k) := fun q => ⟨q.1.1, q.2⟩

/- English proof (translation)
Introduce and unpack `⟨⟨k, hk⟩, i⟩ ⟨⟨k', hk'⟩, i'⟩ h`. Simplify using `only [incl, Sigma.mk.inj_iff] at h`. Take `⟨rfl, h2⟩` from `h`. Consider the cases of `h2`. Both sides reduce to the same expression.
-/
theorem incl_injective (S : K → Prop) : Function.Injective (incl (ι := ι) S) := by
  rintro ⟨⟨k, hk⟩, i⟩ ⟨⟨k', hk'⟩, i'⟩ h
  simp only [incl, Sigma.mk.inj_iff] at h
  obtain ⟨rfl, h2⟩ := h
  cases h2
  rfl

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[MvPolynomial.support_rename_of_injective (incl_injective S), Finset.mem_image]`. Take `⟨m₀, hm₀, rfl⟩` from `hm`. Distinguish the cases in `hk : S k`. Establish `he : Function.extend Subtype.val a 0 k = a ⟨k, hk⟩` using `Subtype.val_injective.extend_apply a 0 ⟨k, hk⟩`.

Rewrite using `[he, ← hD m₀ hm₀ ⟨k, hk⟩]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `Finsupp.mapDomain_apply (incl_injective S) m₀ ⟨⟨k, hk⟩, i⟩`. Rewrite using `[Function.extend_apply' _ _ _ (by rintro ⟨c, rfl⟩; exact hk c.2), Pi.zero_apply]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Use `Finsupp.mapDomain_notin_range _ _ ?_` and prove the remaining obligations. Introduce and unpack `⟨q, hq⟩`. Conclude with `hk ((Sigma.mk.inj_iff.mp hq).1 ▸ q.1.2)`.
-/
theorem isMultiHomog_rename_incl [Fintype K] [∀ k, Fintype (ι k)] (S : K → Prop)
    {D : MRing (fun k : {k // S k} => ι k.1)} {a : {k // S k} → ℕ} (hD : IsMultiHomog D a) :
    IsMultiHomog (rename (incl (ι := ι) S) D : MRing ι) (Function.extend Subtype.val a 0) := by
  classical
  intro m hm k
  rw [MvPolynomial.support_rename_of_injective (incl_injective S), Finset.mem_image] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  by_cases hk : S k
  · have he : Function.extend Subtype.val a 0 k = a ⟨k, hk⟩ := Subtype.val_injective.extend_apply a 0 ⟨k, hk⟩
    rw [he, ← hD m₀ hm₀ ⟨k, hk⟩]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finsupp.mapDomain_apply (incl_injective S) m₀ ⟨⟨k, hk⟩, i⟩
  · rw [Function.extend_apply' _ _ _ (by rintro ⟨c, rfl⟩; exact hk c.2), Pi.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨q, hq⟩
    exact hk ((Sigma.mk.inj_iff.mp hq).1 ▸ q.1.2)

/- English proof (translation)
Proceed by induction on `D using MvPolynomial.induction_on with`. Consider the case `C r => simp [mConeMap]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p q hp`. Rewrite using `[map_mul, map_mul, map_mul, map_mul, map_mul, hp]`.

Use `congr 1`. Apply the tactic sequence `simp only [mConeMap, aeval_X, map_mul, rename_C, rename_X, map_C, map_X, hy] <;> rfl`.
-/
theorem mConeMap_rename_incl {Ω Φ : Type} [Field Ω] [Field Φ] [Algebra Ω Φ] (S : K → Prop)
    (x : (Σ k : {k // S k}, ι k.1) → Ω) (y : (Σ k, ι k) → Φ)
    (hy : ∀ q, y (incl S q) = algebraMap Ω Φ (x q)) (D : MRing (fun k : {k // S k} => ι k.1)) :
    mConeMap y (rename (incl (ι := ι) S) D) =
      map (algebraMap Ω Φ) (rename Subtype.val (mConeMap x D)) := by
  induction D using MvPolynomial.induction_on with
  | C r => simp [mConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p q hp =>
    rw [map_mul, map_mul, map_mul, map_mul, map_mul, hp]
    congr 1
    simp only [mConeMap, aeval_X, map_mul, rename_C, rename_X, map_C, map_X, hy] <;> rfl

/- English proof (translation)
Introduce `hmem`. Apply `hD` to reduce the goal to its premises. Establish `e : mConeMap y (rename (incl (ι` using `ι) S) D) = 0 := hmem`. Rewrite `e` using `[mConeMap_rename_incl S x y hy D]`. Establish `e2 : rename Subtype.val (mConeMap x D) = 0` using `MvPolynomial.map_injective _ (algebraMap Ω Φ).injective (e.trans (map_zero _).symm)`.

Use `show mConeMap x D = 0`. Conclude with `MvPolynomial.rename_injective _ Subtype.val_injective (e2.trans (map_zero _).symm)`.
-/
theorem rename_incl_notMem {Ω Φ : Type} [Field Ω] [Field Φ] [Algebra Ω Φ] (S : K → Prop)
    (x : (Σ k : {k // S k}, ι k.1) → Ω) (y : (Σ k, ι k) → Φ)
    (hy : ∀ q, y (incl S q) = algebraMap Ω Φ (x q)) {D : MRing (fun k : {k // S k} => ι k.1)}
    (hD : D ∉ mCoordIdeal x) : (rename (incl (ι := ι) S) D : MRing ι) ∉ mCoordIdeal y := by
  intro hmem
  apply hD
  have e : mConeMap y (rename (incl (ι := ι) S) D) = 0 := hmem
  rw [mConeMap_rename_incl S x y hy D] at e
  have e2 : rename Subtype.val (mConeMap x D) = 0 :=
    MvPolynomial.map_injective _ (algebraMap Ω Φ).injective (e.trans (map_zero _).symm)
  show mConeMap x D = 0
  exact MvPolynomial.rename_injective _ Subtype.val_injective (e2.trans (map_zero _).symm)

/- English proof (translation)
Introduce `K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d _ _ D a hD hDx`. Use `⟨rename (incl (ι := ι) fun k => ∀ p, M.blk p ≠ some k) D, Function.extend Subtype.val a 0, isMultiHomog_rename_incl _ hD, rename_incl_notMem _ M.x y (fun q => M.y_base q) hDx, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[map_rename, eval_rename]`. Both sides reduce to the same expression.
-/
theorem exists_form : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ (D : MRing (baseIdx ι M.blk)) (a : NonPluckerBlocks M.blk → ℕ), IsMultiHomog D a → D ∉ mCoordIdeal M.x → ∃ (G : MRing ι) (a' : K → ℕ), IsMultiHomog G a' ∧ G ∉ mCoordIdeal y ∧ ∀ w : (Σ k, ι k) → ℂ, eval w (map (Int.castRingHom ℂ) G) = eval (basePart M.blk w) (map (Int.castRingHom ℂ) D) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d _ _ D a hD hDx
  refine ⟨rename (incl (ι := ι) fun k => ∀ p, M.blk p ≠ some k) D, Function.extend Subtype.val a 0,
    isMultiHomog_rename_incl _ hD, rename_incl_notMem _ M.x y (fun q => M.y_base q) hDx, fun w => ?_⟩
  rw [map_rename, eval_rename]
  rfl

end GlobalTheory.CompanionTheory.Ar.PB.BaseForm
