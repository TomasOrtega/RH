import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CocompactOfMemIffAdelic

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.UnipCocompact

open GlobalTheory.UnipFlagCore

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

omit [NumberField E] in

/- English proof (translation)
Use extensionality with `u`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨B, hB, hd, hX, hz⟩`. Establish `e : ((HA.mat _ σ J u).1 - 1) * adMat F X = adMat F X * (B - 1)`. Rewrite using `[Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]`.

Conclude with `congrArg (· - adMat F X) hX`. Use `⟨fun i => ⟨fun j => (B - 1) j i, fun j hij => ?_, ?_⟩, hz⟩` and prove the remaining obligations. Break down `(Fin.le_def.2 hij).eq_or_lt with e | e` into its components or cases. Substitute `e` using the available equality. Simplify using `[hd]`.

Simplify using `[hB e, e.ne']`. Use function extensionality and compare the values at `k`. Conclude with `congrFun (congrFun e k) i`. Introduce and unpack `⟨h1, h2⟩ choose a ha ha' using h1`. Establish `e : ((HA.mat _ σ J u).1 - 1) * adMat F X = adMat F X * Matrix.of (fun j i => a i j)`.

Use extensionality with `k i`. Conclude with `congrFun (ha' i) k`. Use `⟨1 + Matrix.of (fun j i => a i j), fun i j hij => ?_, fun i => ?_, ?_, h2⟩` and prove the remaining obligations. Establish `hij' : j < i` using `hij`. Simplify using `[ha j i hij'.le, hij'.ne']`.

Simplify using `[ha i i le_rfl]`. Rewrite using `[Matrix.mul_add, Matrix.mul_one, ← e, Matrix.sub_mul, Matrix.one_mul]`. Conclude with `(add_sub_cancel _ _).symm`.
-/
theorem unipMin_eq_radSet (X : Matrix (Fin n) (Fin r) E) :
    unipMin σ J X = radSet σ J X Fin.val := by
  ext u
  constructor
  · rintro ⟨B, hB, hd, hX, hz⟩
    have e : ((HA.mat _ σ J u).1 - 1) * adMat F X = adMat F X * (B - 1) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
      exact congrArg (· - adMat F X) hX
    refine ⟨fun i => ⟨fun j => (B - 1) j i, fun j hij => ?_, ?_⟩, hz⟩
    · rcases (Fin.le_def.2 hij).eq_or_lt with e | e
      · subst e; simp [hd]
      · simp [hB e, e.ne']
    · funext k
      exact congrFun (congrFun e k) i
  · rintro ⟨h1, h2⟩
    choose a ha ha' using h1
    have e : ((HA.mat _ σ J u).1 - 1) * adMat F X = adMat F X * Matrix.of (fun j i => a i j) := by
      ext k i
      exact congrFun (ha' i) k
    refine ⟨1 + Matrix.of (fun j i => a i j), fun i j hij => ?_, fun i => ?_, ?_, h2⟩
    · have hij' : j < i := hij
      simp [ha j i hij'.le, hij'.ne']
    · simp [ha i i le_rfl]
    · rw [Matrix.mul_add, Matrix.mul_one, ← e, Matrix.sub_mul, Matrix.one_mul]
      exact (add_sub_cancel _ _).symm

/- English proof (translation)
Take `⟨L, hL, hLL⟩` from `exists_dual hσ hJ X hC h0`. Establish `hd : ∀ j : Fin r, (j : ℕ) < r` using `fun j => j.2`. Establish `he` using `idem_complete hσ hJ X L hL h0 hLL`. Establish `hs` using `fam_st (adj_mul hσ hJ) (adj_adj hσ hJ) (idem (F := F) X L) (Fin.val : Fin r → ℕ) r`. Establish `h1` using `GlobalTheory.TwoStepUnipotent.st_one (adj_mul hσ hJ) (adj_adj hσ hJ)`.

Rewrite using `[mem_radSet_iff hσ hJ X L hL h0 hLL hd]`. Proceed by induction on `hg using Subgroup.closure_induction with`. Consider the case `mem x hx => exact (mem_radSet_iff hσ hJ X L hL h0 hLL hd x).1 hx`. Consider the case `one => exact (sub_self (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).symm ▸ zero_mem _`. Consider the case `mul x y _ _ hx hy`.

Establish `e : (HA.mat _ σ J (x * y)).1 = (HA.mat _ σ J x).1 * (HA.mat _ σ J y).1` using `rfl`. Rewrite using `[e]`. Generalize the expression as in `(HA.mat _ σ J x).1 = a at hx ⊢`. Generalize the expression as in `(HA.mat _ σ J y).1 = b at hy ⊢`. Establish `: a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1)` using `by noncomm_ring`.

Rewrite using `[this]`. Conclude with `add_mem (add_mem (raise_le 0 (raise_mul he 0 hx hy)) hx) hy`. Consider the case `inv x _ hx`. Use `raise_st (adj_mul hσ hJ) (adj_adj hσ hJ) hs 0 hx` as an intermediate fact. Rewrite `this` using `[map_sub, adj_mat hσ hJ, h1]`. Then use the resulting hypothesis.
-/
theorem closure_radSet_subset (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {X : Matrix (Fin n) (Fin r) E}
    (hC : LinearIndependent E Xᵀ) (h0 : cT (σ : E →+* E) X * J * X = 0) {g : HA (AF F) σ J}
    (hg : g ∈ Subgroup.closure (radSet σ J X Fin.val)) : g ∈ radSet σ J X Fin.val := by
  obtain ⟨L, hL, hLL⟩ := exists_dual hσ hJ X hC h0
  have hd : ∀ j : Fin r, (j : ℕ) < r := fun j => j.2
  have he := idem_complete hσ hJ X L hL h0 hLL
  have hs := fam_st (adj_mul hσ hJ) (adj_adj hσ hJ) (idem (F := F) X L) (Fin.val : Fin r → ℕ) r
  have h1 := GlobalTheory.TwoStepUnipotent.st_one (adj_mul hσ hJ) (adj_adj hσ hJ)
  rw [mem_radSet_iff hσ hJ X L hL h0 hLL hd]
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact (mem_radSet_iff hσ hJ X L hL h0 hLL hd x).1 hx
  | one => exact (sub_self (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).symm ▸ zero_mem _
  | mul x y _ _ hx hy =>
    have e : (HA.mat _ σ J (x * y)).1 = (HA.mat _ σ J x).1 * (HA.mat _ σ J y).1 := rfl
    rw [e]
    generalize (HA.mat _ σ J x).1 = a at hx ⊢
    generalize (HA.mat _ σ J y).1 = b at hy ⊢
    have : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
    rw [this]
    exact add_mem (add_mem (raise_le 0 (raise_mul he 0 hx hy)) hx) hy
  | inv x _ hx =>
    have := raise_st (adj_mul hσ hJ) (adj_adj hσ hJ) hs 0 hx
    rwa [map_sub, adj_mat hσ hJ, h1] at this

/- English proof (translation)
Establish `e : cT (σ : E →+* E) Y * J * X = 1`. Use `congrArg (cT (σ : E →+* E)) hW.xy` as an intermediate fact. Rewrite `this` using `[Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_cT' hσ hJ, cT_gram hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc]`. Then use the resulting hypothesis. Use `Matrix.mulVec_injective_iff.1 fun v w h => ?_` and prove the remaining obligations. Use `congrArg ((cT (σ : E →+* E) Y * J) *ᵥ ·) h` as an intermediate fact.

Simplify `this` using `only [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]`.
-/
theorem linearIndependent_of_isWittFrame (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J)
    {X Y : Matrix (Fin n) (Fin r) E} (hW : IsWittFrame σ J X Y) : LinearIndependent E Xᵀ := by
  have e : cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (cT (σ : E →+* E)) hW.xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_cT' hσ hJ, cT_gram hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  refine Matrix.mulVec_injective_iff.1 fun v w h => ?_
  have := congrArg ((cT (σ : E →+* E) Y * J) *ᵥ ·) h
  simpa only [Matrix.mulVec_mulVec, e, Matrix.one_mulVec] using this

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h n J hJ r X Y hW`. Establish `hσ` using `sigma_sigma h`. Establish `hC` using `linearIndependent_of_isWittFrame hσ hJ hW`. Take `⟨K, hK, hcov⟩` from `closure_radSet_cocompact hσ hJ X hC hW.xx Fin.val`. Establish `hsub : ∀ g : Subgroup.closure (radSet σ J X Fin.val), g.1 ∈ unipMin σ J X` using `fun g => by`.

Rewrite using `[unipMin_eq_radSet]`. Conclude with `closure_radSet_subset hσ hJ hC hW.xx g.2`. Use `⟨Subtype.val '' K, hK.image continuous_subtype_val, fun u hu => ?_⟩` and prove the remaining obligations. Rewrite `hu` using `[unipMin_eq_radSet]`. Take `⟨γ, hγ, k, hk, e⟩` from `hcov ⟨u, Subgroup.subset_closure hu⟩`.

Conclude with `⟨γ.1, hγ, hsub γ, k.1, ⟨k, hk, rfl⟩, hsub k, congrArg Subtype.val e⟩`.
-/
theorem unipMin_cocompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ C : Set (GAd σ J), IsCompact C ∧ ∀ u ∈ unipMin σ J X, ∃ δ ∈ ratPts σ J, δ ∈ unipMin σ J X ∧ ∃ c ∈ C, c ∈ unipMin σ J X ∧ u = δ * c := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW
  have hσ := sigma_sigma h
  have hC := linearIndependent_of_isWittFrame hσ hJ hW
  obtain ⟨K, hK, hcov⟩ := closure_radSet_cocompact hσ hJ X hC hW.xx Fin.val
  have hsub : ∀ g : Subgroup.closure (radSet σ J X Fin.val), g.1 ∈ unipMin σ J X := fun g => by
    rw [unipMin_eq_radSet]
    exact closure_radSet_subset hσ hJ hC hW.xx g.2
  refine ⟨Subtype.val '' K, hK.image continuous_subtype_val, fun u hu => ?_⟩
  rw [unipMin_eq_radSet] at hu
  obtain ⟨γ, hγ, k, hk, e⟩ := hcov ⟨u, Subgroup.subset_closure hu⟩
  exact ⟨γ.1, hγ, hsub γ, k.1, ⟨k, hk, rfl⟩, hsub k, congrArg Subtype.val e⟩

end GlobalTheory.CompanionTheory.UnipCocompact
