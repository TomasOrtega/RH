import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeApproximationUpwardIdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIteratedRealLineDerivUnitaryAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSmoothParabolicStatement

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.AutomorphicL2Unitary (LeftInv)
open GlobalTheory.Cusp (Cocompact constTermOn)
open scoped TensorProduct

namespace GlobalTheory.UAut.ConstAut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => exact h`. Consider the case `cons γ l ih`. Introduce `x hx g`.

Simplify using `only [List.foldr_cons, lineDer, mul_assoc, ih x hx]`.
-/
theorem leftInv_foldr {Γ : Subgroup (GAd σ J)} {φ : GAd σ J → ℂ} (h : LeftInv Γ φ) :
    ∀ l : List (ℝ → GAd σ J), LeftInv Γ (l.foldr lineDer φ) := by
  intro l
  induction l with
  | nil => exact h
  | cons γ l ih =>
    intro x hx g
    simp only [List.foldr_cons, lineDer, mul_assoc, ih x hx]

/- English proof (translation)
Establish `e` using `isRealLine_add F E σ h n J γ hγ 0 0`. Rewrite `e` using `[add_zero]`. Conclude with `mul_left_cancel (e.symm.trans (mul_one _).symm)`.
-/
theorem realLine_zero (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) : γ 0 = 1 := by
  have e := isRealLine_add F E σ h n J γ hγ 0 0
  rw [add_zero] at e
  exact mul_left_cancel (e.symm.trans (mul_one _).symm)

/- English proof (translation)
Establish `hd` using `(GlobalTheory.ThK.RealLineGrowthDerivative.differentiableAt_foldr_lineDer hs l hl hγ (g * γ t)).hasDerivAt`. Establish `e : ∀ s, g * γ t * γ (s - t) = g * γ s` using `fun s => by`. Rewrite using `[mul_assoc, ← isRealLine_add F E σ h n J γ hγ, add_sub_cancel]`. Establish `h2` using `HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact hd)`. Simplify using `only [e] at h2`.

Conclude with `h2`.
-/
theorem hasDerivAt_foldr (h : IsCMExt F E σ) {φ : GAd σ J → ℂ} (hs : IsSm σ J φ) {l : List (ℝ → GAd σ J)}
    (hl : ∀ γ ∈ l, IsRealLine σ J γ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (g : GAd σ J) (t : ℝ) :
    HasDerivAt (fun s => l.foldr lineDer φ (g * γ s)) ((γ :: l).foldr lineDer φ (g * γ t)) t := by
  have hd := (GlobalTheory.ThK.RealLineGrowthDerivative.differentiableAt_foldr_lineDer hs l hl hγ (g * γ t)).hasDerivAt
  have e : ∀ s, g * γ t * γ (s - t) = g * γ s := fun s => by
    rw [mul_assoc, ← isRealLine_add F E σ h n J γ hγ, add_sub_cancel]
  have h2 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact hd)
  simp only [e] at h2
  exact h2

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h n J hJ r C d hC H K φ c hH hφ hc`. Use `haveI := locallyCompact_unipFlag hJ (sigma_sigma h) hC d`. Establish `hφΓ : LeftInv (ratPts σ J ⊓ parFlag σ J C d) φ` using `fun γ hγ => hφ.left γ (hH hγ)`. Take `⟨hco, e⟩` from `hc.eq_constTermOn_par h hJ hC hφΓ`. Establish `hcont : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → Continuous (l.foldr lineDer φ)` using `GlobalTheory.T.continuous_iteratedRealLineDeriv_unitaryAdelic F E σ h n J hJ φ hφ.level hφ.cont hφ.smooth`.

Establish `hleft : ∀ l : List (ℝ → GAd σ J), LeftInv (ratPts σ J ⊓ parFlag σ J C d) (l.foldr lineDer φ)` using `leftInv_foldr hφΓ`. Establish `hder : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → l.foldr lineDer c = constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) (l.foldr lineDer φ)`. Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => intro _`.

Conclude with `e`. Consider the case `cons γ l ih`. Introduce `hl`. Establish `hl' : ∀ γ' ∈ l, IsRealLine σ J γ'` using `fun γ' h' => hl γ' (List.mem_cons_of_mem _ h')`. Establish `hγ : IsRealLine σ J γ` using `hl γ List.mem_cons_self`.

Use function extensionality and compare the values at `x`. Establish `hx` using `GlobalTheory.CuspLie.hasDerivAt_constTermOn hco (hleft l) (hcont l hl') (hleft (γ :: l)) (hcont (γ :: l) hl) (GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J γ hγ) (hasDerivAt_foldr h hφ.smooth hl' hγ) x`. Rewrite `hx` using `[realLine_zero h hγ, mul_one]`. Rewrite using `[List.foldr_cons, ih hl']`. Conclude with `hx.deriv`.

Establish `hct : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → IsConstTermOn σ J (unipFlag σ J C d) (l.foldr lineDer φ) (l.foldr lineDer c)`. Introduce `l hl`. Take `⟨c', hc', -⟩` from `existsUnique_isConstTermOn h hJ hC d (φ := l.foldr lineDer φ) fun γ hγ => hleft l γ ⟨hγ.1, unipFlag_le_parFlag hJ (sigma_sigma h) hC d hγ.2⟩`. Rewrite using `[hder l hl, ← (hc'.eq_constTermOn_par h hJ hC (hleft l)).2]` and apply the resulting hypothesis. Set `S : Submodule ℂ (GAd σ J → ℂ)` to `{ carrier := {f | LeftInv (ratPts σ J ⊓ parFlag σ J C d) f ∧ Continuous f} add_mem' := fun ha hb => ⟨fun γ hγ g => by simp [ha.1 γ hγ g, hb.1 γ hγ g], ha.2.add hb.2⟩ zero_mem' := ⟨fun _ _ _ => rfl, continuous_const⟩ smul_mem' := fun a f hf => ⟨fun γ hγ g => by simp [hf.1 γ hγ g], …`.

Set `Tl : S →ₗ[ℂ] (GAd σ J → ℂ)` to `{ toFun := fun f => constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) f.1 map_add' := fun a b => funext fun x => hco.constTermOn_add a.2.1 a.2.2 b.2.1 b.2.2 x map_smul' := fun a f => funext fun x => GlobalTheory.Cusp.constTermOn_smul a f.1 x }`. Establish `hfin : ∀ W : Submodule ℂ (GAd σ J → ℂ), FiniteDimensional ℂ W → FiniteDimensional ℂ ((W.comap S.subtype).map Tl)`. Introduce `W hW`. Use `haveI : FiniteDimensional ℂ (W.comap S.subtype) := FiniteDimensional.of_injective (S.subtype.restrict (q := W) fun _ hx => hx) fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : W => z.1) h))`. Use `infer_instance`.

Establish `hsum : ∀ (s : Finset (List (ℝ → GAd σ J))) (a : List (ℝ → GAd σ J) → ℂ), (∀ l ∈ s, ∀ γ ∈ l, IsRealLine σ J γ) → (∑ l ∈ s, a l • l.foldr lineDer φ) ∈ S ∧ constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) (∑ l ∈ s, a l • l.foldr lineDer φ) = ∑ l ∈ s, a l • constTermOn ( …`. Introduce `s a hs`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨S.zero_mem, funext fun x => by simp [GlobalTheory.Cusp.constTermOn]⟩`. Consider the case `insert i s hi ih`.

Rewrite using `[Finset.sum_insert hi, Finset.sum_insert hi]`. Take `⟨h1, h2⟩` from `ih fun l hl => hs l (Finset.mem_insert_of_mem hl)`. Establish `m : a i • i.foldr lineDer φ ∈ S` using `S.smul_mem _ ⟨hleft i, hcont i (hs i (Finset.mem_insert_self i s))⟩`. Use `⟨S.add_mem m h1, ?_⟩` and prove the remaining obligations. Rewrite using `[← h2]`.

Use function extensionality and compare the values at `x`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[hco.constTermOn_add m.1 m.2 h1.1 h1.2 x, GlobalTheory.Cusp.constTermOn_smul]`. Establish `hlevel : ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, c (g * k) = c g`. Take `⟨U, hU, hUk⟩` from `hφ.level`.

Use `⟨U, hU, fun k hk hf g => ?_⟩` and prove the remaining obligations. Rewrite using `[e, ← GlobalTheory.Cusp.constTermOn_mul_right]`. Conclude with `congrArg (fun f => constTermOn _ _ f g) (funext fun y => hUk k hk hf y)`. Establish `hkfin : GlobalTheory.Doubling.IsKFinite K c`. Take `⟨W, hW, hWk⟩` from `GlobalTheory.Doubling.isKFinite_iff.1 hφ.kfin`.

Use `GlobalTheory.Doubling.isKFinite_iff.2 ⟨_, hfin W hW, fun k hk => ⟨⟨fun g => φ (g * k), fun γ hγ g => by simp only [mul_assoc]; exact hφΓ γ hγ _, hφ.cont.comp (continuous_mul_right k)⟩, hWk k hk, funext fun g => ?_⟩⟩` and prove the remaining obligations. Use `show constTermOn _ _ (fun g => φ (g * k)) g = c (g * k)`. Rewrite using `[GlobalTheory.Cusp.constTermOn_mul_right, e]`. Establish `hzfin : FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z c})` using `by haveI := hfin (Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z φ}) hφ.zfin`. Use `Submodule.finiteDimensional_of_le (S₂ := ((Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z φ}).comap S.subtype).map Tl) (Submodule.span_le.2 ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨z, hz, rfl⟩`. Establish `hr : ∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ` using `hz.1`. Establish `hd1 : dop z φ = ∑ l ∈ z.support, z l • l.foldr lineDer φ` using `funext fun g => by`. Simplify using `[dop, Finsupp.sum, Finset.sum_apply]`. Establish `hd2 : dop z c = ∑ l ∈ z.support, z l • constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) (l.foldr lineDer φ)` using `funext fun g => by`.

Simplify using `only [dop, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun l hl => by rw [hder l (hr l hl)]`. Take `⟨m, hm⟩` from `hsum z.support (fun l => z l) hr`. Use `⟨⟨_, m⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show (∑ l ∈ z.support, z l • l.foldr lineDer φ) ∈ Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z φ}`.

Rewrite using `[← hd1]`. Conclude with `Submodule.subset_span ⟨z, hz, rfl⟩`. Use `show constTermOn _ _ _ = _`. Rewrite using `[hm, hd2]`. Establish `hgrowth : ∃ M : ℕ, ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → ∃ B : ℝ, ∀ g, ‖l.foldr lineDer c g‖ ≤ B * (height σ J g : ℝ) ^ M`.

Take `⟨M, hM⟩` from `hφ.growth`. Take `⟨K0, hK0, hs⟩` from `id hco`. Use `haveI := hco.isProbabilityMeasure`. Take `⟨A, hA⟩` from `(hK0.image continuous_subtype_val).exists_bound_of_continuousOn (f := fun x => (height σ J x : ℝ)) (NNReal.continuous_coe.comp (continuous_height_GAd σ J)).continuousOn`. Use `⟨M, fun l hl => ?_⟩` and prove the remaining obligations.

Take `⟨B, hB⟩` from `hM l hl`. Use `⟨max B 0 * max A 0 ^ M, fun g => ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ x : unipFlag σ J C d, ‖l.foldr lineDer φ ((x : GAd σ J) * g)‖ ≤ max B 0 * (max A 0 * (height σ J g : ℝ)) ^ M`. Introduce `x`. Take `⟨γ, hγ, hk⟩` from `hs x`.

Establish `e1 : l.foldr lineDer φ ((x : GAd σ J) * g) = l.foldr lineDer φ (((γ * x : unipFlag σ J C d) : GAd σ J) * g)`. Rewrite using `[Subgroup.coe_mul, mul_assoc]`. Conclude with `(hleft l _ hγ _).symm`. Establish `e2 : (height σ J ((γ * x : unipFlag σ J C d) : GAd σ J) : ℝ) ≤ max A 0`. Use `hA _ ⟨_, hk, rfl⟩` as an intermediate fact.

Rewrite `this` using `[Real.norm_eq_abs]`. Conclude with `(le_abs_self _).trans (this.trans (le_max_left _ _))`. Establish `e3 : (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ≤ max A 0 * height σ J g`. Combine the equalities or inequalities in the displayed calculation. Conclude with `height_mul_le σ J _ _` after adjusting the coercions.

Use `_ ≤ max A 0 * height σ J g := mul_le_mul_of_nonneg_right e2 (NNReal.coe_nonneg _)`. Rewrite using `[e1]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hder l hl]`. Use `(norm_integral_le_of_norm_le_const (μ := GlobalTheory.Cusp.probMeasure _ _) (.of_forall fun q => h1 q.out)).trans (le_of_eq ?_)` and prove the remaining obligations.

Simplify using `[mul_pow, mul_assoc]`. Conclude with `⟨⟨hc.leftInv h hJ hC hφΓ, hlevel, hc.continuous h hJ hC hφΓ hφ.cont, GlobalTheory.T.constant_term_smooth_parabolic F E σ h n J hJ r C d hC H K φ c hH hφ hc, hgrowth, hkfin, hzfin⟩, hct⟩`.
-/
theorem isAutOn_constTerm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (C : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ), IsIsoCols σ J C → ∀ (H K : Subgroup (GAd σ J)) (φ c : GAd σ J → ℂ), ratPts σ J ⊓ parFlag σ J C d ≤ H → IsAutOn σ J H K φ → IsConstTermOn σ J (unipFlag σ J C d) φ c → IsAutOn σ J (leftGrp σ J C d) K c ∧ ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → IsConstTermOn σ J (unipFlag σ J C d) (l.foldr lineDer φ) (l.foldr lineDer c) := by
  intro F E _ _ _ _ _ σ h n J hJ r C d hC H K φ c hH hφ hc
  classical
  haveI := locallyCompact_unipFlag hJ (sigma_sigma h) hC d
  have hφΓ : LeftInv (ratPts σ J ⊓ parFlag σ J C d) φ := fun γ hγ => hφ.left γ (hH hγ)
  obtain ⟨hco, e⟩ := hc.eq_constTermOn_par h hJ hC hφΓ
  have hcont : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → Continuous (l.foldr lineDer φ) :=
    GlobalTheory.T.continuous_iteratedRealLineDeriv_unitaryAdelic F E σ h n J hJ φ hφ.level hφ.cont hφ.smooth
  have hleft : ∀ l : List (ℝ → GAd σ J), LeftInv (ratPts σ J ⊓ parFlag σ J C d) (l.foldr lineDer φ) :=
    leftInv_foldr hφΓ
  have hder : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      l.foldr lineDer c = constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) (l.foldr lineDer φ) := by
    intro l
    induction l with
    | nil => intro _; exact e
    | cons γ l ih =>
      intro hl
      have hl' : ∀ γ' ∈ l, IsRealLine σ J γ' := fun γ' h' => hl γ' (List.mem_cons_of_mem _ h')
      have hγ : IsRealLine σ J γ := hl γ List.mem_cons_self
      funext x
      have hx := GlobalTheory.CuspLie.hasDerivAt_constTermOn hco (hleft l) (hcont l hl') (hleft (γ :: l)) (hcont (γ :: l) hl)
        (GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J γ hγ) (hasDerivAt_foldr h hφ.smooth hl' hγ) x
      rw [realLine_zero h hγ, mul_one] at hx
      rw [List.foldr_cons, ih hl']
      exact hx.deriv
  have hct : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      IsConstTermOn σ J (unipFlag σ J C d) (l.foldr lineDer φ) (l.foldr lineDer c) := by
    intro l hl
    obtain ⟨c', hc', -⟩ := existsUnique_isConstTermOn h hJ hC d (φ := l.foldr lineDer φ)
      fun γ hγ => hleft l γ ⟨hγ.1, unipFlag_le_parFlag hJ (sigma_sigma h) hC d hγ.2⟩
    rwa [hder l hl, ← (hc'.eq_constTermOn_par h hJ hC (hleft l)).2]
  let S : Submodule ℂ (GAd σ J → ℂ) :=
    { carrier := {f | LeftInv (ratPts σ J ⊓ parFlag σ J C d) f ∧ Continuous f}
      add_mem' := fun ha hb => ⟨fun γ hγ g => by simp [ha.1 γ hγ g, hb.1 γ hγ g], ha.2.add hb.2⟩
      zero_mem' := ⟨fun _ _ _ => rfl, continuous_const⟩
      smul_mem' := fun a f hf => ⟨fun γ hγ g => by simp [hf.1 γ hγ g], hf.2.const_smul a⟩ }
  let Tl : S →ₗ[ℂ] (GAd σ J → ℂ) :=
    { toFun := fun f => constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) f.1
      map_add' := fun a b => funext fun x => hco.constTermOn_add a.2.1 a.2.2 b.2.1 b.2.2 x
      map_smul' := fun a f => funext fun x => GlobalTheory.Cusp.constTermOn_smul a f.1 x }
  have hfin : ∀ W : Submodule ℂ (GAd σ J → ℂ), FiniteDimensional ℂ W →
      FiniteDimensional ℂ ((W.comap S.subtype).map Tl) := by
    intro W hW
    haveI : FiniteDimensional ℂ (W.comap S.subtype) := FiniteDimensional.of_injective
      (S.subtype.restrict (q := W) fun _ hx => hx) fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : W => z.1) h))
    infer_instance
  have hsum : ∀ (s : Finset (List (ℝ → GAd σ J))) (a : List (ℝ → GAd σ J) → ℂ),
      (∀ l ∈ s, ∀ γ ∈ l, IsRealLine σ J γ) →
      (∑ l ∈ s, a l • l.foldr lineDer φ) ∈ S ∧
      constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) (∑ l ∈ s, a l • l.foldr lineDer φ) =
        ∑ l ∈ s, a l • constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) (l.foldr lineDer φ) := by
    intro s a hs
    induction s using Finset.induction_on with
    | empty => exact ⟨S.zero_mem, funext fun x => by simp [GlobalTheory.Cusp.constTermOn]⟩
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      obtain ⟨h1, h2⟩ := ih fun l hl => hs l (Finset.mem_insert_of_mem hl)
      have m : a i • i.foldr lineDer φ ∈ S :=
        S.smul_mem _ ⟨hleft i, hcont i (hs i (Finset.mem_insert_self i s))⟩
      refine ⟨S.add_mem m h1, ?_⟩
      rw [← h2]
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hco.constTermOn_add m.1 m.2 h1.1 h1.2 x, GlobalTheory.Cusp.constTermOn_smul]
  have hlevel : ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧
      ∀ k ∈ U, k ∈ finPts σ J → ∀ g, c (g * k) = c g := by
    obtain ⟨U, hU, hUk⟩ := hφ.level
    refine ⟨U, hU, fun k hk hf g => ?_⟩
    rw [e, ← GlobalTheory.Cusp.constTermOn_mul_right]
    exact congrArg (fun f => constTermOn _ _ f g) (funext fun y => hUk k hk hf y)
  have hkfin : GlobalTheory.Doubling.IsKFinite K c := by
    obtain ⟨W, hW, hWk⟩ := GlobalTheory.Doubling.isKFinite_iff.1 hφ.kfin
    refine GlobalTheory.Doubling.isKFinite_iff.2 ⟨_, hfin W hW, fun k hk => ⟨⟨fun g => φ (g * k),
      fun γ hγ g => by simp only [mul_assoc]; exact hφΓ γ hγ _, hφ.cont.comp (continuous_mul_right k)⟩,
      hWk k hk, funext fun g => ?_⟩⟩
    show constTermOn _ _ (fun g => φ (g * k)) g = c (g * k)
    rw [GlobalTheory.Cusp.constTermOn_mul_right, e]
  have hzfin : FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z c}) := by
    haveI := hfin (Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z φ}) hφ.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := ((Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z φ}).comap S.subtype).map Tl) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    have hr : ∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ := hz.1
    have hd1 : dop z φ = ∑ l ∈ z.support, z l • l.foldr lineDer φ := funext fun g => by
      simp [dop, Finsupp.sum, Finset.sum_apply]
    have hd2 : dop z c = ∑ l ∈ z.support, z l •
        constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) (l.foldr lineDer φ) := funext fun g => by
      simp only [dop, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun l hl => by rw [hder l (hr l hl)]
    obtain ⟨m, hm⟩ := hsum z.support (fun l => z l) hr
    refine ⟨⟨_, m⟩, ?_, ?_⟩
    · show (∑ l ∈ z.support, z l • l.foldr lineDer φ) ∈ Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z φ}
      rw [← hd1]
      exact Submodule.subset_span ⟨z, hz, rfl⟩
    · show constTermOn _ _ _ = _
      rw [hm, hd2]
  have hgrowth : ∃ M : ℕ, ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      ∃ B : ℝ, ∀ g, ‖l.foldr lineDer c g‖ ≤ B * (height σ J g : ℝ) ^ M := by
    obtain ⟨M, hM⟩ := hφ.growth
    obtain ⟨K0, hK0, hs⟩ := id hco
    haveI := hco.isProbabilityMeasure
    obtain ⟨A, hA⟩ := (hK0.image continuous_subtype_val).exists_bound_of_continuousOn
      (f := fun x => (height σ J x : ℝ)) (NNReal.continuous_coe.comp (continuous_height_GAd σ J)).continuousOn
    refine ⟨M, fun l hl => ?_⟩
    obtain ⟨B, hB⟩ := hM l hl
    refine ⟨max B 0 * max A 0 ^ M, fun g => ?_⟩
    have h1 : ∀ x : unipFlag σ J C d, ‖l.foldr lineDer φ ((x : GAd σ J) * g)‖ ≤
        max B 0 * (max A 0 * (height σ J g : ℝ)) ^ M := by
      intro x
      obtain ⟨γ, hγ, hk⟩ := hs x
      have e1 : l.foldr lineDer φ ((x : GAd σ J) * g) =
          l.foldr lineDer φ (((γ * x : unipFlag σ J C d) : GAd σ J) * g) := by
        rw [Subgroup.coe_mul, mul_assoc]; exact (hleft l _ hγ _).symm
      have e2 : (height σ J ((γ * x : unipFlag σ J C d) : GAd σ J) : ℝ) ≤ max A 0 := by
        have := hA _ ⟨_, hk, rfl⟩
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans (this.trans (le_max_left _ _))
      have e3 : (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ≤ max A 0 * height σ J g :=
        calc (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ)
            ≤ height σ J ((γ * x : unipFlag σ J C d) : GAd σ J) * height σ J g := by
              exact_mod_cast height_mul_le σ J _ _
          _ ≤ max A 0 * height σ J g := mul_le_mul_of_nonneg_right e2 (NNReal.coe_nonneg _)
      rw [e1]
      calc _ ≤ B * (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ^ M := hB _
        _ ≤ max B 0 * (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ^ M :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (NNReal.coe_nonneg _) _)
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) e3 _) (le_max_right _ _)
    rw [hder l hl]
    refine (norm_integral_le_of_norm_le_const (μ := GlobalTheory.Cusp.probMeasure _ _) (.of_forall fun q => h1 q.out)).trans
      (le_of_eq ?_)
    simp [mul_pow, mul_assoc]
  exact ⟨⟨hc.leftInv h hJ hC hφΓ, hlevel, hc.continuous h hJ hC hφΓ hφ.cont,
    GlobalTheory.T.constant_term_smooth_parabolic F E σ h n J hJ r C d hC H K φ c hH hφ hc, hgrowth, hkfin, hzfin⟩, hct⟩

end GlobalTheory.UAut.ConstAut

end
