import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NotIsBlockProdZero
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.AnChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BlockRen

section Deriv

open scoped ContDiff

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

/- English proof (translation)
Unfold `I2.polyDeriv`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Use `congr 1`. Establish `hs : (Finsupp.toMultiset m).map u = (((Finsupp.toMultiset m).toList.map u : List W) : Multiset W)`. Rewrite using `[← Multiset.map_coe, Multiset.coe_toList]`.

Establish `hlen : ((Finsupp.toMultiset m).toList.map u).length = Multiset.card (Finsupp.toMultiset m)`. Rewrite using `[List.length_map, Multiset.length_toList]`. Rewrite using `[hs, mD_coe hθ, lD_eq θ x _ hlen]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Simplify using `[List.get_eq_getElem]`.
-/
theorem polyDeriv_eq_sum {θ : W → ℂ} {x : W} (hθ : ContDiffAt ℂ ω θ x) {T : Type}
    (P : MvPolynomial T ℂ) (u : T → W) :
    I2.polyDeriv P u θ x =
      ∑ m ∈ P.support, P.coeff m * mD θ x ((Finsupp.toMultiset m).map u) := by
  unfold I2.polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1

  have hs : (Finsupp.toMultiset m).map u = (((Finsupp.toMultiset m).toList.map u : List W) : Multiset W) := by
    rw [← Multiset.map_coe, Multiset.coe_toList]
  have hlen : ((Finsupp.toMultiset m).toList.map u).length = Multiset.card (Finsupp.toMultiset m) := by
    rw [List.length_map, Multiset.length_toList]
  rw [hs, mD_coe hθ, lD_eq θ x _ hlen]
  congr 1
  funext k
  simp [List.get_eq_getElem]

/- English proof (translation)
Rewrite using `[polyDeriv_eq_sum hθ, polyDeriv_eq_sum hθ, MvPolynomial.support_rename_of_injective hρ, Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective hρ h]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_rename_mapDomain ρ hρ, ← Finsupp.toMultiset_map, Multiset.map_map]`.
-/
theorem polyDeriv_rename {θ : W → ℂ} {x : W} (hθ : ContDiffAt ℂ ω θ x) {T κ : Type} (ρ : T → κ)
    (hρ : Function.Injective ρ) (P : MvPolynomial T ℂ) (v : κ → W) :
    I2.polyDeriv (MvPolynomial.rename ρ P) v θ x = I2.polyDeriv P (v ∘ ρ) θ x := by
  classical
  rw [polyDeriv_eq_sum hθ, polyDeriv_eq_sum hθ, MvPolynomial.support_rename_of_injective hρ,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective hρ h]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain ρ hρ, ← Finsupp.toMultiset_map, Multiset.map_map]

/- English proof (translation)
Set `e : W ≃L[ℂ] (Fin (Module.finrank ℂ W) → ℂ)` to `(Module.finBasis ℂ W).equivFun.toContinuousLinearEquiv`. Establish `hG : AnalyticOnNhd ℂ (F ∘ e.symm) Set.univ` using `ReciprocityTheory.AnForm.Osgood.osgood _ Set.univ _ isOpen_univ (hF.comp e.symm.differentiable).differentiableOn`. Establish `hA` using `(hG (e x) (Set.mem_univ _)).comp ((e : W →L[ℂ] (Fin (Module.finrank ℂ W) → ℂ)).analyticAt x)`. Establish `hFe : (F ∘ e.symm) ∘ e = F`. Use function extensionality and compare the values at `y`.

Simplify using the standard rewrite rules. Rewrite `hA` using `[hFe]`. Conclude with `hA.contDiffAt`.
-/
theorem contDiffAt_of_diff [FiniteDimensional ℂ W]
    {F : W → ℂ} (hF : Differentiable ℂ F) (x : W) : ContDiffAt ℂ ω F x := by

  let e : W ≃L[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    (Module.finBasis ℂ W).equivFun.toContinuousLinearEquiv
  have hG : AnalyticOnNhd ℂ (F ∘ e.symm) Set.univ :=
    ReciprocityTheory.AnForm.Osgood.osgood _ Set.univ _ isOpen_univ
      (hF.comp e.symm.differentiable).differentiableOn
  have hA := (hG (e x) (Set.mem_univ _)).comp
    ((e : W →L[ℂ] (Fin (Module.finrank ℂ W) → ℂ)).analyticAt x)
  have hFe : (F ∘ e.symm) ∘ e = F := by
    funext y
    simp
  rw [hFe] at hA
  exact hA.contDiffAt

end Deriv

/- English proof (translation)
Unfold `I2.polyDeriv`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hd : Multiset.card (Finsupp.toMultiset m) = d`. Establish `h` using `hP (MvPolynomial.mem_support_iff.mp hm)`.

Simplify using `[Finsupp.weight_apply] at h`. Rewrite using `[Finsupp.card_toMultiset]`. Conclude with `h`. Rewrite using `[ContinuousMultilinearMap.map_smul_univ (c := fun _ => c)]`. Establish `hc : (∏ _k : Fin (Multiset.card (Finsupp.toMultiset m)), c) = c ^ d`.

Rewrite using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin, hd]`. Rewrite using `[hc, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem polyDeriv_scale {J W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {P : MvPolynomial J ℂ} {d : ℕ}
    (hP : P.IsHomogeneous d) (c : ℂ) (u : J → W) (F : W → ℂ) (x : W) :
    I2.polyDeriv P (fun l => c • u l) F x = c ^ d * I2.polyDeriv P u F x := by
  unfold I2.polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_

  have hd : Multiset.card (Finsupp.toMultiset m) = d := by
    have h := hP (MvPolynomial.mem_support_iff.mp hm)
    simp [Finsupp.weight_apply] at h
    rw [Finsupp.card_toMultiset]
    exact h
  rw [ContinuousMultilinearMap.map_smul_univ (c := fun _ => c)]
  have hc : (∏ _k : Fin (Multiset.card (Finsupp.toMultiset m)), c) = c ^ d := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hd]
  rw [hc, smul_eq_mul]
  ring

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `MvPolynomial.IsHomogeneous.sum _ _ _ fun s _ => ?_` and prove the remaining obligations. Establish `hprod : (∏ a, (Matrix.of fun a b : Fin i => (MvPolynomial.X (f a b) : MvPolynomial J K)) (s a) a).IsHomogeneous i`. Establish `h` using `MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin i)) (fun a => (MvPolynomial.X (f (s a) a) : MvPolynomial J K)) (fun _ => 1) (fun a _ => MvPolynomial.isHomogeneous_X K _)`. Simplify using `using h`.

Break down `Int.units_eq_one_or (Equiv.Perm.sign s) with h | h` into its components or cases. Rewrite using `[h, one_smul]`. Conclude with `hprod`. Rewrite using `[h, Units.neg_smul, one_smul]`. Conclude with `hprod.neg`.
-/
theorem det_X_isHomogeneous {J K : Type} [CommRing K] (i : ℕ) (f : Fin i → Fin i → J) :
    (Matrix.of fun a b : Fin i => (MvPolynomial.X (f a b) : MvPolynomial J K)).det.IsHomogeneous i := by
  rw [Matrix.det_apply]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun s _ => ?_

  have hprod : (∏ a, (Matrix.of fun a b : Fin i => (MvPolynomial.X (f a b) : MvPolynomial J K)) (s a) a).IsHomogeneous i := by
    have h := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin i))
      (fun a => (MvPolynomial.X (f (s a) a) : MvPolynomial J K)) (fun _ => 1)
      (fun a _ => MvPolynomial.isHomogeneous_X K _)
    simpa using h
  rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
  · rw [h, one_smul]
    exact hprod
  · rw [h, Units.neg_smul, one_smul]
    exact hprod.neg

/- English proof (translation)
Introduce `E _ _ _ H Dw n K _ σ P hP dim rl hd hrl`. Take `⟨nb, bs0, hdisj, rfl⟩` from `hP`. Establish `hdeg : (∏ j, (bs0 j).poly K).IsHomogeneous (∑ j, (bs0 j).i * (bs0 j).c)`. Use `MvPolynomial.IsHomogeneous.prod _ _ _ fun j _ => ?_` and prove the remaining obligations. Conclude with `(det_X_isHomogeneous (K := K) (bs0 j).i (fun a b => (⟨(bs0 j).τ, Fin.castLE (bs0 j).hi a, (bs0 j).col b⟩ : LtN Dw n))).pow (bs0 j).c`.

Establish `hne : (∏ j, (bs0 j).poly K) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun j _ => GlobalTheory.BlockThInhab.poly_ne_zero Dw n K (bs0 j)`. Establish `htot : (∏ j, (bs0 j).poly K).totalDegree = ∑ j, (bs0 j).i * (bs0 j).c` using `hdeg.totalDegree hne`. Set `bs : Fin nb → I2.Block E n dim` to `fun j => ⟨rl (bs0 j).τ, (bs0 j).i, (bs0 j).hi.trans (hd _), (bs0 j).c, (bs0 j).hc, (bs0 j).col, (bs0 j).col_inj⟩`. Use `⟨hne, htot ▸ hdeg, nb, bs, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j j' hjj' a a'`.

Conclude with `hdisj j j' hjj' a a'`. Rewrite using `[htot]`. Both sides reduce to the same expression. Introduce `t F hF`. Rewrite using `[htot]`.

Set `ρ : LtN Dw n → I2.Letter n dim` to `fun ℓ => (ℓ.2.2, ⟨rl ℓ.1, Fin.castLE (hd ℓ.1) ℓ.2.1⟩)`. Establish `hρ : Function.Injective ρ`. Introduce and unpack `⟨τ, a, b⟩ ⟨τ', a', b'⟩ h`. Simplify using `only [ρ, Prod.mk.injEq, Sigma.mk.injEq] at h`. Take `⟨rfl, h1, h2⟩` from `h`.

Take `rfl` from `hrl h1`. Establish `h3` using `Fin.castLE_injective (hd τ) (eq_of_heq h2)`. Substitute `h3` using the available equality. Both sides reduce to the same expression. Establish `hP1 : MvPolynomial.rename ρ (MvPolynomial.map σ (∏ j, (bs0 j).poly K)) = I2.P1 bs`.

Simplify using `only [map_prod, I2.P1]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Bk.poly, I2.Block.poly, map_pow, RingHom.map_det, AlgHom.map_det]`. Use `congr 2`. Use extensionality with `a b`.

Simplify using `[ρ, bs]`. Establish `hhom : (I2.P1 bs).IsHomogeneous (∑ j, (bs0 j).i * (bs0 j).c)`. Use `MvPolynomial.IsHomogeneous.prod _ _ _ fun j _ => ?_` and prove the remaining obligations. Conclude with `(det_X_isHomogeneous (K := ℂ) (bs0 j).i (fun a b => (((bs0 j).col b, ⟨rl (bs0 j).τ, Fin.castLE ((bs0 j).hi.trans (hd _)) a⟩) : I2.Letter n dim))).pow (bs0 j).c`. Use `(polyDeriv_rename (contDiffAt_of_diff hF 0) ρ hρ _ (fun l => t • I2.dir l)).symm.trans ?_` and prove the remaining obligations.

Rewrite using `[hP1]`. Conclude with `polyDeriv_scale hhom t I2.dir F 0`.
-/
theorem blockProd_rename : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (K : Type) [Field K] (σ : K →+* ℂ) (P : MvPolynomial (LtN Dw n) K), IsBlockProd P → ∀ (dim : (E →+* ℂ) → ℕ) (rl : (E →+* ℂ) → (E →+* ℂ)) (hd : ∀ τ, Dw.mult τ ≤ dim (rl τ)), Function.Injective rl → P ≠ 0 ∧ P.IsHomogeneous P.totalDegree ∧ ∃ (nb : ℕ) (bs : Fin nb → I2.Block E n dim), I2.Disj bs ∧ I2.DF bs = P.totalDegree ∧ ∀ (t : ℂ) (F : (Fin n → I2.Vsp dim) → ℂ), Differentiable ℂ F → I2.polyDeriv (MvPolynomial.map σ P) (fun ℓ => t • I2.dir ((ℓ.2.2, ⟨rl ℓ.1, Fin.castLE (hd ℓ.1) ℓ.2.1⟩) : I2.Letter n dim)) F 0 = t ^ P.totalDegree * I2.polyDeriv (I2.P1 bs) I2.dir F 0 := by
  intro E _ _ _ H Dw n K _ σ P hP dim rl hd hrl
  obtain ⟨nb, bs0, hdisj, rfl⟩ := hP
  classical

  have hdeg : (∏ j, (bs0 j).poly K).IsHomogeneous (∑ j, (bs0 j).i * (bs0 j).c) := by
    refine MvPolynomial.IsHomogeneous.prod _ _ _ fun j _ => ?_
    exact (det_X_isHomogeneous (K := K) (bs0 j).i
      (fun a b => (⟨(bs0 j).τ, Fin.castLE (bs0 j).hi a, (bs0 j).col b⟩ : LtN Dw n))).pow (bs0 j).c
  have hne : (∏ j, (bs0 j).poly K) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => GlobalTheory.BlockThInhab.poly_ne_zero Dw n K (bs0 j)
  have htot : (∏ j, (bs0 j).poly K).totalDegree = ∑ j, (bs0 j).i * (bs0 j).c :=
    hdeg.totalDegree hne

  let bs : Fin nb → I2.Block E n dim := fun j =>
    ⟨rl (bs0 j).τ, (bs0 j).i, (bs0 j).hi.trans (hd _), (bs0 j).c, (bs0 j).hc, (bs0 j).col, (bs0 j).col_inj⟩
  refine ⟨hne, htot ▸ hdeg, nb, bs, ?_, ?_, ?_⟩
  · intro j j' hjj' a a'
    exact hdisj j j' hjj' a a'
  · rw [htot]
    rfl
  · intro t F hF
    rw [htot]
    let ρ : LtN Dw n → I2.Letter n dim := fun ℓ => (ℓ.2.2, ⟨rl ℓ.1, Fin.castLE (hd ℓ.1) ℓ.2.1⟩)
    have hρ : Function.Injective ρ := by
      rintro ⟨τ, a, b⟩ ⟨τ', a', b'⟩ h
      simp only [ρ, Prod.mk.injEq, Sigma.mk.injEq] at h
      obtain ⟨rfl, h1, h2⟩ := h
      obtain rfl := hrl h1
      have h3 := Fin.castLE_injective (hd τ) (eq_of_heq h2)
      subst h3
      rfl

    have hP1 : MvPolynomial.rename ρ (MvPolynomial.map σ (∏ j, (bs0 j).poly K)) = I2.P1 bs := by
      simp only [map_prod, I2.P1]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [Bk.poly, I2.Block.poly, map_pow, RingHom.map_det, AlgHom.map_det]
      congr 2
      ext a b
      simp [ρ, bs]
    have hhom : (I2.P1 bs).IsHomogeneous (∑ j, (bs0 j).i * (bs0 j).c) := by
      refine MvPolynomial.IsHomogeneous.prod _ _ _ fun j _ => ?_
      exact (det_X_isHomogeneous (K := ℂ) (bs0 j).i
        (fun a b => (((bs0 j).col b, ⟨rl (bs0 j).τ, Fin.castLE ((bs0 j).hi.trans (hd _)) a⟩) : I2.Letter n dim))).pow (bs0 j).c
    refine (polyDeriv_rename (contDiffAt_of_diff hF 0) ρ hρ _ (fun l => t • I2.dir l)).symm.trans ?_
    rw [hP1]
    exact polyDeriv_scale hhom t I2.dir F 0

end GlobalTheory.BlockRen
