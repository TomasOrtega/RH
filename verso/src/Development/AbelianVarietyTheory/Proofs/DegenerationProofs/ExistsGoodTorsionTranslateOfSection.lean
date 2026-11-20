import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsionImports
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UnitTheta

/- English proof (translation)
Establish `le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => f) j ≤ f ⁻¹ᵁ L.U (j 0)` using `fun j y hy => Set.mem_iInter.1 hy 0`. Set `u : ∀ j : Fin 1 → L.ι, Γ(Y, LB.wchart L (fun _ : Fin 1 => f) j)` to `fun j => (Y.presheaf.map (homOfLE (le j)).op).hom ((f.app _).hom (θ.f (j 0)))`. Establish `hu : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Y) (z : Z) j, ρ z ∈ LB.wchart L (fun _ : Fin 1 => f) j → gs ρ z _ (u j) = gs (ρ ≫ f) z _ (θ.f (j 0))` using `fun Z ρ z j h => (gs_res ρ z _ h _).trans (gs_pull ρ f z _ (le j h) _)`. Use `⟨⟨u, fun j j' => fn_ext fun y hy => ?_⟩, fun Z ρ z J hJ => hu Z ρ z _ (hJ.mem (fun _ : Fin 1 => f) ρ)⟩` and prove the remaining obligations. Use `(gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L (fun _ : Fin 1 => f) (fun _ => 1) (𝟙 Y) y j j' hy.1 hy.2))) (gs_res (𝟙 Y) y _ hy _))).symm)` and prove the remaining obligations.

Rewrite using `[Fin.prod_univ_one, zpow_one]`. Conclude with `(hu _ (𝟙 Y) y j hy.1).trans ((gs_compat θ (𝟙 Y ≫ f) y (le j hy.1) (le j' hy.2)).trans (congrArg (_ * ·) (hu _ (𝟙 Y) y j' hy.2).symm))`.
-/
theorem exists_pull_one {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (θ : LB.Sec L) :
    ∃ th : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => f) (fun _ => 1)),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Y) (z : Z) (J), Good L z J →
        sval th ρ z J = gs (ρ ≫ f) z _ (θ.f (J (ρ ≫ f))) := by
  have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => f) j ≤ f ⁻¹ᵁ L.U (j 0) :=
    fun j y hy => Set.mem_iInter.1 hy 0
  let u : ∀ j : Fin 1 → L.ι, Γ(Y, LB.wchart L (fun _ : Fin 1 => f) j) := fun j =>
    (Y.presheaf.map (homOfLE (le j)).op).hom ((f.app _).hom (θ.f (j 0)))
  have hu : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Y) (z : Z) j, ρ z ∈ LB.wchart L (fun _ : Fin 1 => f) j →
      gs ρ z _ (u j) = gs (ρ ≫ f) z _ (θ.f (j 0)) := fun Z ρ z j h =>
    (gs_res ρ z _ h _).trans (gs_pull ρ f z _ (le j h) _)
  refine ⟨⟨u, fun j j' => fn_ext fun y hy => ?_⟩, fun Z ρ z J hJ => hu Z ρ z _ (hJ.mem (fun _ : Fin 1 => f) ρ)⟩
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
    ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val
      (gm_linComb L (fun _ : Fin 1 => f) (fun _ => 1) (𝟙 Y) y j j' hy.1 hy.2))) (gs_res (𝟙 Y) y _ hy _))).symm)
  rw [Fin.prod_univ_one, zpow_one]
  exact (hu _ (𝟙 Y) y j hy.1).trans ((gs_compat θ (𝟙 Y ≫ f) y (le j hy.1) (le j' hy.2)).trans
    (congrArg (_ * ·) (hu _ (𝟙 Y) y j' hy.2).symm))

/- English proof (translation)
Introduce `hB hG S P θ κ _ _ r n hn hκ ⟨z, hz, p, hp⟩ b`. Take `⟨th, hth⟩` from `exists_pull_one P.L (snd (Over.mk r) P.A).left θ`. Establish `hne : SecM.ofSec P.A (a` using `1) (T := Over.mk r) th ≠ 0 := fun e => by`. Take `⟨y, -, hy⟩` from `Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback r P.A.hom) p z hp`. Set `y' : (Over.mk r ⊗ P.A).left` to `y`.

Take `⟨J, hJ, -⟩` from `exists_good P.L P.isLB y' (K := Empty) Empty.elim Empty.elim (·.elim) (·.elim)`. Establish `h₁ : (𝟙 _ ≫ (snd (Over.mk r) P.A).left) y' ∈ nonzeroLocus θ`. Rewrite using `[Category.id_comp]`. Conclude with `hy ▸ hz`. Establish `h₂` using `(AmpleSpan.mem_nonzeroLocus_iff_gs θ _ y' (hJ _)).1 h₁`.

Rewrite `h₂` using `[← hth _ _ y' J hJ]`. Establish `h₃ : th.f (fun _ => J (𝟙 _ ≫ (snd (Over.mk r) P.A).left)) = 0` using `congrArg (fun s : SecM P.A P.L 1 (Over.mk r) => s.1 _) e`. Rewrite `h₂` using `[sval, h₃]`. Conclude with `not_isUnit_zero ((congrArg IsUnit (GlobalTheory.UT.ExactTerm.gs_zero' _ _ _ (hJ.mem (fun _ : Fin 1 => (snd (Over.mk r) P.A).left) (𝟙 _)))).mp h₂)`. Take `⟨x, hx, hu⟩` from `GlobalTheory.UT.ExactTerm.exists_good_point hG hB P r hn hκ th hne b`.

Use `⟨x, hx, fun q _ => ?_⟩` and prove the remaining obligations. Take `⟨J, hJ, -⟩` from `exists_good P.L P.isLB q (K := Empty) Empty.elim Empty.elim (·.elim) (·.elim)`. Establish `h₁ : IsUnit (sval th (ptSecT P.A (b * x)).left q J)` using `hu q J hJ`. Establish `e : (ptSecT P.A (b * x)).left ≫ (snd (Over.mk r) P.A).left = (b * x).left`. Rewrite using `[← Over.comp_left, ptSecT, lift_snd]`.

Rewrite `h₁` using `[hth _ _ q J hJ, e]`. Conclude with `(AmpleSpan.mem_nonzeroLocus_iff_gs θ _ q (hJ _)).2 h₁`.
-/
theorem exists_good_point_of_sec : PolBaseChangeSt → GoodPtSt → ∀ (S : Scheme.{0}) (P : PolAV S) (θ : LB.Sec P.L) (κ : Type) [Field κ] [IsAlgClosed κ] (r : Sp κ ⟶ S) (n : ℕ), 2 ≤ n → (n : κ) ≠ 0 → (∃ z ∈ nonzeroLocus θ, P.A.hom z ∈ Set.range r) → ∀ b : Over.mk r ⟶ P.A, ∃ x : Over.mk r ⟶ P.A, x ^ n = 1 ∧ ⊤ ≤ (b * x).left ⁻¹ᵁ nonzeroLocus θ := by
  intro hB hG S P θ κ _ _ r n hn hκ ⟨z, hz, p, hp⟩ b
  obtain ⟨th, hth⟩ := exists_pull_one P.L (snd (Over.mk r) P.A).left θ
  have hne : SecM.ofSec P.A (a := 1) (T := Over.mk r) th ≠ 0 := fun e => by
    obtain ⟨y, -, hy⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback r P.A.hom) p z hp
    let y' : (Over.mk r ⊗ P.A).left := y
    obtain ⟨J, hJ, -⟩ := exists_good P.L P.isLB y' (K := Empty) Empty.elim Empty.elim (·.elim) (·.elim)
    have h₁ : (𝟙 _ ≫ (snd (Over.mk r) P.A).left) y' ∈ nonzeroLocus θ := by
      rw [Category.id_comp]; exact hy ▸ hz
    have h₂ := (AmpleSpan.mem_nonzeroLocus_iff_gs θ _ y' (hJ _)).1 h₁
    rw [← hth _ _ y' J hJ] at h₂
    have h₃ : th.f (fun _ => J (𝟙 _ ≫ (snd (Over.mk r) P.A).left)) = 0 :=
      congrArg (fun s : SecM P.A P.L 1 (Over.mk r) => s.1 _) e
    rw [sval, h₃] at h₂
    exact not_isUnit_zero ((congrArg IsUnit (GlobalTheory.UT.ExactTerm.gs_zero' _ _ _ (hJ.mem (fun _ : Fin 1 => (snd (Over.mk r) P.A).left) (𝟙 _)))).mp h₂)
  obtain ⟨x, hx, hu⟩ := GlobalTheory.UT.ExactTerm.exists_good_point hG hB P r hn hκ th hne b
  refine ⟨x, hx, fun q _ => ?_⟩
  obtain ⟨J, hJ, -⟩ := exists_good P.L P.isLB q (K := Empty) Empty.elim Empty.elim (·.elim) (·.elim)
  have h₁ : IsUnit (sval th (ptSecT P.A (b * x)).left q J) := hu q J hJ
  have e : (ptSecT P.A (b * x)).left ≫ (snd (Over.mk r) P.A).left = (b * x).left := by
    rw [← Over.comp_left, ptSecT, lift_snd]
  rw [hth _ _ q J hJ, e] at h₁
  exact (AmpleSpan.mem_nonzeroLocus_iff_gs θ _ q (hJ _)).2 h₁

end GlobalTheory.UnitTheta
end
