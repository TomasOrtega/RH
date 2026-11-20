import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale

open GlobalTheory
open scoped ContDiff

noncomputable section

namespace GlobalTheory

def imForm {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v w => (HermFrame.form H v w).im)
    (fun v v' w => by simp [HermFrame.form_add_left])
    (fun c v w => by
      rw [← Complex.coe_smul, HermFrame.form_smul_left]; simp)
    (fun v w w' => by simp [HermFrame.form_add_right])
    (fun c v w => by
      rw [← Complex.coe_smul, HermFrame.form_smul_right]; simp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem imForm_apply {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (v w : Fin g → ℂ) :
    imForm H v w = (HermFrame.form H v w).im := rfl

/- English proof (translation)
Rewrite using `[map_sum (imForm H), LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul (imForm H), LinearMap.smul_apply, map_sum, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s' _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem imForm_sum_sum {g : ℕ} {ι : Type*} [Fintype ι] (H : Matrix (Fin g) (Fin g) ℂ)
    (c d : ι → ℝ) (x : ι → Fin g → ℂ) :
    imForm H (∑ s, c s • x s) (∑ s, d s • x s) =
      ∑ s, ∑ s', c s * d s' * imForm H (x s) (x s') := by
  rw [map_sum (imForm H), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul (imForm H), LinearMap.smul_apply, map_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [map_smul, smul_eq_mul]
  ring

/- English proof (translation)
Rewrite using `[imForm_apply, imForm_apply, HermFrame.form_smul_left, HermFrame.form_single]`. Apply the tactic sequence `apply Complex.ext <;> simp`.
-/
theorem gram_entry_eq {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (i i' : Fin g) :
    H i i' = ((imForm H (Complex.I • Pi.single i 1) (Pi.single i' 1) : ℝ) : ℂ)
      + Complex.I * ((imForm H (Pi.single i 1) (Pi.single i' 1) : ℝ) : ℂ) := by
  rw [imForm_apply, imForm_apply, HermFrame.form_smul_left, HermFrame.form_single]
  apply Complex.ext <;> simp

/- English proof (translation)
Take `⟨S, hS, hSspan, hSli⟩` from `exists_linearIndependent ℝ (Set.range fun j => ζ j b₀)`. Establish `hfin : S.Finite` using `hSli.setFinite`. Use `haveI : Fintype S := hfin.fintype`. Use `choose t ht using (fun s : S => hS s.2)`. Set `B : Module.Basis S ℝ (Fin g → ℂ)` to `Module.Basis.mk hSli (by`.

Rewrite using `[Subtype.range_coe, hSspan, hspan])`. Set `Z : (Fin m → ℂ) → ((S → ℝ) →L[ℝ] (Fin g → ℂ))` to `fun b => ∑ s, (ContinuousLinearMap.proj s : (S → ℝ) →L[ℝ] ℝ).smulRight (ζ (t s) b)`. Establish `hZapp : ∀ b c, Z b c = ∑ s, c s • ζ (t s) b` using `fun b c => by`. Simplify using `[Z, ContinuousLinearMap.sum_apply]`. Establish `hZ : ContDiffAt ℝ ∞ Z b₀`.

Use `ContDiffAt.sum fun s _ => ?_` and prove the remaining obligations. Conclude with `(ContinuousLinearMap.smulRightL ℝ (S → ℝ) (Fin g → ℂ) (ContinuousLinearMap.proj s)).contDiff.contDiffAt.comp b₀ (hζ (t s))`. Set `e : (S → ℝ) ≃L[ℝ] (Fin g → ℂ)` to `B.equivFun.symm.toContinuousLinearEquiv`. Establish `hZ0 : Z b₀ = (e : (S → ℝ) →L[ℝ] (Fin g → ℂ))` using `by ext1 c`. Rewrite using `[hZapp]`.

Simplify using `only [e, LinearEquiv.coe_toContinuousLinearEquiv', ContinuousLinearEquiv.coe_coe]`. Simplify using `[Module.Basis.equivFun_symm_apply, B, ht]`. Establish `hinv : ContDiffAt ℝ ∞ (fun b => (Z b).inverse) b₀`. Establish `h1` using `contDiffAt_map_inverse (n := ∞) e`. Rewrite `h1` using `[← hZ0]`.

Conclude with `h1.comp b₀ hZ`. Establish `hev : ∀ᶠ b in nhds b₀, ∀ v, Z b ((Z b).inverse v) = v`. Establish `h1 : Set.range ((↑) : ((S → ℝ) ≃L[ℝ] (Fin g → ℂ)) → ((S → ℝ) →L[ℝ] (Fin g → ℂ))) ∈ nhds (Z b₀)`. Rewrite using `[hZ0]`. Conclude with `e.nhds`.

Use `filter_upwards [hZ.continuousAt h1] with b hb v`. Take `⟨e', he'⟩` from `hb`. Rewrite using `[← he']`. Simplify using the standard rewrite rules. Establish `hE : ∀ᶠ b in nhds b₀, ∀ s s', imForm (H b) (ζ (t s) b) (ζ (t s') b) = imForm (H b₀) (ζ (t s) b₀) (ζ (t s') b₀)` using `Filter.eventually_all.2 fun s => Filter.eventually_all.2 fun s' => hconst (t s) (t s')`.

Establish `hcoord : ∀ (v : Fin g → ℂ) (s : S), ContDiffAt ℝ ∞ (fun b => (Z b).inverse v s) b₀` using `fun v s => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s).contDiff.contDiffAt.comp b₀ (hinv.clm_apply contDiffAt_const)`. Establish `key : ∀ v w, ContDiffAt ℝ ∞ (fun b => imForm (H b) v w) b₀`. Introduce `v w`. Establish `hR : ContDiffAt ℝ ∞ (fun b => ∑ s, ∑ s', (Z b).inverse v s * (Z b).inverse w s' * imForm (H b₀) (ζ (t s) b₀) (ζ (t s') b₀)) b₀` using `ContDiffAt.sum fun s _ => ContDiffAt.sum fun s' _ => ((hcoord v s).mul (hcoord w s')).mul contDiffAt_const`. Use `hR.congr_of_eventuallyEq ?_` and prove the remaining obligations.

Use `filter_upwards [hev, hE] with b h1 h2`. Establish `h4 : imForm (H b) v w = imForm (H b) (Z b ((Z b).inverse v)) (Z b ((Z b).inverse w))`. Rewrite using `[h1 v, h1 w]`. Use `show imForm (H b) v w = _`. Rewrite using `[h4, hZapp, hZapp, imForm_sum_sum]`.

Use `Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_` and prove the remaining obligations. Rewrite using `[h2]`. Establish `hc : ∀ {f : (Fin m → ℂ) → ℝ}, ContDiffAt ℝ ∞ f b₀ → ContDiffAt ℝ ∞ (fun b => (f b : ℂ)) b₀` using `fun h => Complex.ofRealCLM.contDiff.contDiffAt.comp b₀ h`. Establish `h3 : (fun b => H b i i') = fun b => ((imForm (H b) (Complex.I • Pi.single i 1) (Pi.single i' 1) : ℝ) : ℂ) + Complex.I * ((imForm (H b) (Pi.single i 1) (Pi.single i' 1) : ℝ) : ℂ)`. Use function extensionality and compare the values at `fun b => gram_entry_eq (H b) i i'`.

Rewrite using `[h3]`. Conclude with `(hc (key _ _)).add (contDiffAt_const.mul (hc (key _ _)))`.
-/
theorem contDiffAt_gram_of_im_form_const (g m : ℕ) (J : Type)
    (ζ : J → (Fin m → ℂ) → (Fin g → ℂ)) (H : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (b₀ : Fin m → ℂ) (hζ : ∀ j, ContDiffAt ℝ ∞ (ζ j) b₀)
    (hspan : Submodule.span ℝ (Set.range fun j => ζ j b₀) = ⊤)
    (hconst : ∀ j k, ∀ᶠ b in nhds b₀, (HermFrame.form (H b) (ζ j b) (ζ k b)).im =
      (HermFrame.form (H b₀) (ζ j b₀) (ζ k b₀)).im) (i i' : Fin g) :
    ContDiffAt ℝ ∞ (fun b => H b i i') b₀ := by
  classical
  obtain ⟨S, hS, hSspan, hSli⟩ := exists_linearIndependent ℝ (Set.range fun j => ζ j b₀)
  have hfin : S.Finite := hSli.setFinite
  haveI : Fintype S := hfin.fintype
  choose t ht using (fun s : S => hS s.2)
  let B : Module.Basis S ℝ (Fin g → ℂ) := Module.Basis.mk hSli (by
    rw [Subtype.range_coe, hSspan, hspan])
  let Z : (Fin m → ℂ) → ((S → ℝ) →L[ℝ] (Fin g → ℂ)) := fun b =>
    ∑ s, (ContinuousLinearMap.proj s : (S → ℝ) →L[ℝ] ℝ).smulRight (ζ (t s) b)
  have hZapp : ∀ b c, Z b c = ∑ s, c s • ζ (t s) b := fun b c => by
    simp [Z, ContinuousLinearMap.sum_apply]
  have hZ : ContDiffAt ℝ ∞ Z b₀ := by
    refine ContDiffAt.sum fun s _ => ?_
    exact (ContinuousLinearMap.smulRightL ℝ (S → ℝ) (Fin g → ℂ)
      (ContinuousLinearMap.proj s)).contDiff.contDiffAt.comp b₀ (hζ (t s))
  let e : (S → ℝ) ≃L[ℝ] (Fin g → ℂ) := B.equivFun.symm.toContinuousLinearEquiv
  have hZ0 : Z b₀ = (e : (S → ℝ) →L[ℝ] (Fin g → ℂ)) := by
    ext1 c
    rw [hZapp]
    simp only [e, LinearEquiv.coe_toContinuousLinearEquiv', ContinuousLinearEquiv.coe_coe]
    simp [Module.Basis.equivFun_symm_apply, B, ht]
  have hinv : ContDiffAt ℝ ∞ (fun b => (Z b).inverse) b₀ := by
    have h1 := contDiffAt_map_inverse (n := ∞) e
    rw [← hZ0] at h1
    exact h1.comp b₀ hZ
  have hev : ∀ᶠ b in nhds b₀, ∀ v, Z b ((Z b).inverse v) = v := by
    have h1 : Set.range ((↑) : ((S → ℝ) ≃L[ℝ] (Fin g → ℂ)) → ((S → ℝ) →L[ℝ] (Fin g → ℂ))) ∈
        nhds (Z b₀) := by
      rw [hZ0]; exact e.nhds
    filter_upwards [hZ.continuousAt h1] with b hb v
    obtain ⟨e', he'⟩ := hb
    rw [← he']
    simp
  have hE : ∀ᶠ b in nhds b₀, ∀ s s', imForm (H b) (ζ (t s) b) (ζ (t s') b) =
      imForm (H b₀) (ζ (t s) b₀) (ζ (t s') b₀) :=
    Filter.eventually_all.2 fun s => Filter.eventually_all.2 fun s' => hconst (t s) (t s')
  have hcoord : ∀ (v : Fin g → ℂ) (s : S),
      ContDiffAt ℝ ∞ (fun b => (Z b).inverse v s) b₀ := fun v s =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s).contDiff.contDiffAt.comp b₀
      (hinv.clm_apply contDiffAt_const)
  have key : ∀ v w, ContDiffAt ℝ ∞ (fun b => imForm (H b) v w) b₀ := by
    intro v w
    have hR : ContDiffAt ℝ ∞ (fun b => ∑ s, ∑ s', (Z b).inverse v s * (Z b).inverse w s' *
        imForm (H b₀) (ζ (t s) b₀) (ζ (t s') b₀)) b₀ :=
      ContDiffAt.sum fun s _ => ContDiffAt.sum fun s' _ =>
        ((hcoord v s).mul (hcoord w s')).mul contDiffAt_const
    refine hR.congr_of_eventuallyEq ?_
    filter_upwards [hev, hE] with b h1 h2
    have h4 : imForm (H b) v w = imForm (H b) (Z b ((Z b).inverse v)) (Z b ((Z b).inverse w)) := by
      rw [h1 v, h1 w]
    show imForm (H b) v w = _
    rw [h4, hZapp, hZapp, imForm_sum_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    rw [h2]
  have hc : ∀ {f : (Fin m → ℂ) → ℝ}, ContDiffAt ℝ ∞ f b₀ →
      ContDiffAt ℝ ∞ (fun b => (f b : ℂ)) b₀ := fun h =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp b₀ h
  have h3 : (fun b => H b i i') = fun b =>
      ((imForm (H b) (Complex.I • Pi.single i 1) (Pi.single i' 1) : ℝ) : ℂ)
      + Complex.I * ((imForm (H b) (Pi.single i 1) (Pi.single i' 1) : ℝ) : ℂ) :=
    funext fun b => gram_entry_eq (H b) i i'
  rw [h3]
  exact (hc (key _ _)).add (contDiffAt_const.mul (hc (key _ _)))

end GlobalTheory
