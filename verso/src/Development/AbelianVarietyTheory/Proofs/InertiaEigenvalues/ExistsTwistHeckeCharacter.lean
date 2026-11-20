import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.IntegralSeries
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMapNormEquivariantBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteIdeleCharAtDeterminantRoots
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNthRootIdeleFinitePartOne
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Hilbert90FiniteIdelesCongruence
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNeZeroMulConjEqOfUnitary
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AntiCycRead

variable (D : D7)

def quo : (AE D)ˣ →* (Af D.host.F ⊗[D.host.F] D.host.E)ˣ :=
  MonoidHom.mk' (fun x => Units.map (finPart D).toMonoidHom x *
      (Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x)⁻¹)
    (fun x y => by simp only [map_mul, mul_inv]; exact mul_mul_mul_comm _ _ _ _)

/- English proof (translation)
Establish `hsv : ((Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D))` using `GlobalTheory.DetRootChar.finPart_sigR D x`. Rewrite using `[← hsv]`. Use `show ((Units.map (finPart D).toMonoidHom x * (Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x)⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) * _ = _`. Rewrite using `[← Units.val_mul, inv_mul_cancel_right]`. Both sides reduce to the same expression.
-/
theorem quo_mul (x : (AE D)ˣ) :
    ((quo D x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) *
        sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) = finPart D (x : AE D) := by
  have hsv : ((Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x :
      (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) := GlobalTheory.DetRootChar.finPart_sigR D x
  rw [← hsv]
  show ((Units.map (finPart D).toMonoidHom x * (Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x)⁻¹ :
      (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) * _ = _
  rw [← Units.val_mul, inv_mul_cancel_right]
  rfl

/- English proof (translation)
Use `set s : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ := Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x with hs`. Establish `hsv : (s : Af D.host.F ⊗[D.host.F] D.host.E) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D))`. Rewrite using `[hs]`. Conclude with `GlobalTheory.DetRootChar.finPart_sigR D x`. Establish `h1` using `quo_mul D x`.

Rewrite `h1`, `hu` using `[← hsv]`. Establish `: ((quo D x * s : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ)) = u * s` using `Units.ext (by simp [h1, hu])`. Conclude with `mul_right_cancel this`.
-/
theorem quo_eq_of (x : (AE D)ˣ) (u : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ)
    (hu : (u : Af D.host.F ⊗[D.host.F] D.host.E) * sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) =
      finPart D (x : AE D)) : quo D x = u := by
  set s : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ :=
    Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x with hs
  have hsv : (s : Af D.host.F ⊗[D.host.F] D.host.E) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) := by
    rw [hs]; exact GlobalTheory.DetRootChar.finPart_sigR D x
  have h1 := quo_mul D x
  rw [← hsv] at h1 hu
  have : ((quo D x * s : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ)) = u * s := Units.ext (by simp [h1, hu])
  exact mul_right_cancel this

/- English proof (translation)
Establish `h1` using `quo_mul D x`. Rewrite `h1` using `[hx, Units.val_one, one_mul]`. Take `⟨a, y, hy, hxy⟩` from `GlobalTheory.DetRootChar.exists_idF_mul D x h1`. Take `⟨m, hm, hδ⟩` from `hfin`. Take `⟨z, hz⟩` from `GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one D m hm y hy`.

Rewrite using `[hxy, map_mul, hF, mul_one, ← hz, map_pow, hδ]`.
-/
theorem ker_trivial (δ : (AE D)ˣ →* Circle) (hF : ∀ a, δ (idF D a) = 1) (hfin : ∃ m : ℕ, 0 < m ∧ ∀ x, δ x ^ m = 1)
    (x : (AE D)ˣ) (hx : quo D x = 1) : δ x = 1 := by
  have h1 := quo_mul D x
  rw [hx, Units.val_one, one_mul] at h1
  obtain ⟨a, y, hy, hxy⟩ := GlobalTheory.DetRootChar.exists_idF_mul D x h1
  obtain ⟨m, hm, hδ⟩ := hfin
  obtain ⟨z, hz⟩ := GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one D m hm y hy
  rw [hxy, map_mul, hF, mul_one, ← hz, map_pow, hδ]

/- English proof (translation)
Apply `quo_eq_of` to reduce the goal to its premises. Establish `hdet : ((Matrix.GeneralLinearGroup.det (finHom W g) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) = finPart D (matHom W g).1.det` using `(GlobalTheory.DetRootChar.finPart_det D W g).symm`. Rewrite using `[hdet, ← GlobalTheory.DetRootChar.finPart_sigR, ← RingHom.map_mul]`. Conclude with `(congrArg _ hx).symm`.
-/
theorem quo_of_isDetRoot (W : HSp D) (g : GA D W) (x : (AE D)ˣ) (hx : IsDetRoot W g x) :
    quo D x = Matrix.GeneralLinearGroup.det (finHom W g) := by
  apply quo_eq_of
  have hdet : ((Matrix.GeneralLinearGroup.det (finHom W g) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
      Af D.host.F ⊗[D.host.F] D.host.E) = finPart D (matHom W g).1.det :=
    (GlobalTheory.DetRootChar.finPart_det D W g).symm
  rw [hdet, ← GlobalTheory.DetRootChar.finPart_sigR, ← RingHom.map_mul]
  exact (congrArg _ hx).symm

end GlobalTheory.AntiCycRead

end

noncomputable section

namespace GlobalTheory.AntiCycRead

variable (D : D7)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem val_of_quo (χ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* Circle) (Y : (AE D)ˣ) :
    (((Circle.toUnits.comp χ) (quo D Y) : ℂˣ) : ℂ) = ((χ (quo D Y) : Circle) : ℂ) := by
  simp

/- English proof (translation)
Establish `hN : (x : Af D.host.F ⊗[D.host.F] D.host.E) * sigR (Af D.host.F) D.sp.cm.sig (x : Af D.host.F ⊗[D.host.F] D.host.E) = 1` using `hx`. Rewrite `hN` using `[hxa]`. Establish `ha : a * D.sp.cm.sig a = 1`. Apply `Algebra.TensorProduct.includeRight_injective (A := Af D.host.F) (R := D.host.F) (algebraMap D.host.F (Af D.host.F)).injective` to reduce the goal to its premises. Use `show (1 : Af D.host.F) ⊗ₜ[D.host.F] (a * D.sp.cm.sig a) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)`.

Rewrite using `[← Algebra.TensorProduct.one_def]`. Simplify `hN` using `[sigR]`. Establish `hu : a ∈ unitary D.host.E` using `⟨by rw [mul_comm]; exact ha, ha⟩`. Take `⟨w, hw0, hw⟩` from `GlobalTheory.NormOneHilbert90Units.exists_ne_zero_mul_conj_eq_of_unitary D ⟨a, hu⟩`. Use `⟨Units.mk0 w hw0, ?_⟩` and prove the remaining obligations.

Apply `quo_eq_of` to reduce the goal to its premises. Establish `hfY : finPart D ((Units.map (incA D).toMonoidHom (Units.mk0 w hw0) : (AE D)ˣ) : AE D) = (1 : Af D.host.F) ⊗ₜ[D.host.F] w` using `rfl`. Rewrite using `[hfY, hxa]`. Simplify using `only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Rewrite `hw` using `[← Formalism.BasicNotions.Examples₂.star_eq_conj]`.

Conclude with `congrArg _ hw`.
-/
theorem exists_rat (x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) (a : D.host.E)
    (hxa : (x : Af D.host.F ⊗[D.host.F] D.host.E) = 1 ⊗ₜ a) (hx : GlobalTheory.FinalJoin.NormOne x)
    [Nontrivial (Af D.host.F)] : ∃ w : D.host.Eˣ, quo D (Units.map (incA D).toMonoidHom w) = x := by
  have hN : (x : Af D.host.F ⊗[D.host.F] D.host.E) *
      sigR (Af D.host.F) D.sp.cm.sig (x : Af D.host.F ⊗[D.host.F] D.host.E) = 1 := hx
  rw [hxa] at hN
  have ha : a * D.sp.cm.sig a = 1 := by
    apply Algebra.TensorProduct.includeRight_injective (A := Af D.host.F) (R := D.host.F)
      (algebraMap D.host.F (Af D.host.F)).injective
    show (1 : Af D.host.F) ⊗ₜ[D.host.F] (a * D.sp.cm.sig a) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)
    rw [← Algebra.TensorProduct.one_def]
    simpa [sigR] using hN
  have hu : a ∈ unitary D.host.E := ⟨by rw [mul_comm]; exact ha, ha⟩
  obtain ⟨w, hw0, hw⟩ := GlobalTheory.NormOneHilbert90Units.exists_ne_zero_mul_conj_eq_of_unitary D ⟨a, hu⟩
  refine ⟨Units.mk0 w hw0, ?_⟩
  apply quo_eq_of
  have hfY : finPart D ((Units.map (incA D).toMonoidHom (Units.mk0 w hw0) : (AE D)ˣ) : AE D) =
      (1 : Af D.host.F) ⊗ₜ[D.host.F] w := rfl
  rw [hfY, hxa]
  simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [← Formalism.BasicNotions.Examples₂.star_eq_conj] at hw
  exact congrArg _ hw

/- English proof (translation)
Establish `hn : (x : Af D.host.F ⊗[D.host.F] D.host.E) * sigR (Af D.host.F) D.sp.cm.sig (x : Af D.host.F ⊗[D.host.F] D.host.E) = 1` using `hx`. Take `⟨y, y', hy, hy', hyy, hroot, q, hq, hqe⟩` from `GlobalTheory.T.exists_normOne_root_congruent_odd_hostField D N hN (x : Af D.host.F ⊗[D.host.F] D.host.E) w hw hwe hn`. Take `⟨Y, h1, h2, h3⟩` from `GlobalTheory.DetRootCong.exists_idele D y y' hyy`. Use `⟨Y, ⟨h1, h2 ▸ hy, h3 ▸ hy'⟩, ⟨q, hq, h2 ▸ hqe⟩, ?_⟩` and prove the remaining obligations. Apply `quo_eq_of` to reduce the goal to its premises.

Rewrite using `[h2]`. Conclude with `hroot.symm`.
-/
theorem exists_cong (N : ℕ) (hN : Odd N) (x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) (hx : GlobalTheory.FinalJoin.NormOne x)
    (w : Af D.host.F ⊗[D.host.F] D.host.E) (hw : w ∈ intAE D)
    (hwe : (x : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = N • w) :
    ∃ Y : (AE D)ˣ, FinUnit Y ∧ (∃ y ∈ intAE D, finPart D (Y : AE D) - 1 = N • y) ∧ quo D Y = x := by
  have hn : (x : Af D.host.F ⊗[D.host.F] D.host.E) *
      sigR (Af D.host.F) D.sp.cm.sig (x : Af D.host.F ⊗[D.host.F] D.host.E) = 1 := hx
  obtain ⟨y, y', hy, hy', hyy, hroot, q, hq, hqe⟩ :=
    GlobalTheory.T.exists_normOne_root_congruent_odd_hostField D N hN (x : Af D.host.F ⊗[D.host.F] D.host.E) w hw hwe hn
  obtain ⟨Y, h1, h2, h3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  refine ⟨Y, ⟨h1, h2 ▸ hy, h3 ▸ hy'⟩, ⟨q, hq, h2 ▸ hqe⟩, ?_⟩
  apply quo_eq_of
  rw [h2]
  exact hroot.symm

/- English proof (translation)
Take `⟨y, hy⟩` from `(GlobalTheory.IdeleNinety.finiteIdeles_normOne_eq_div_conj_with_congruence D).1 x hx`. Take `⟨Y, -, h1, -⟩` from `GlobalTheory.DetRootCong.exists_idele D (y : Af D.host.F ⊗[D.host.F] D.host.E) ((y⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : _) y.mul_inv`. Establish `hc : ((Formalism.L2.Pj.cjFin D y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) = sigR (Af D.host.F) D.sp.cm.sig (y : Af D.host.F ⊗[D.host.F] D.host.E)` using `GlobalTheory.IdeleNinety.coe_cjFin D y`. Use `⟨Y, ?_⟩` and prove the remaining obligations. Apply `quo_eq_of` to reduce the goal to its premises.

Rewrite using `[h1, ← hc, hy, ← Units.val_mul, div_mul_cancel]`.
-/
theorem exists_normOne (x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) (hx : GlobalTheory.FinalJoin.NormOne x) :
    ∃ Y : (AE D)ˣ, quo D Y = x := by
  obtain ⟨y, hy⟩ := (GlobalTheory.IdeleNinety.finiteIdeles_normOne_eq_div_conj_with_congruence D).1 x hx
  obtain ⟨Y, -, h1, -⟩ := GlobalTheory.DetRootCong.exists_idele D (y : Af D.host.F ⊗[D.host.F] D.host.E)
    ((y⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : _) y.mul_inv
  have hc : ((Formalism.L2.Pj.cjFin D y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      sigR (Af D.host.F) D.sp.cm.sig (y : Af D.host.F ⊗[D.host.F] D.host.E) :=
    GlobalTheory.IdeleNinety.coe_cjFin D y
  refine ⟨Y, ?_⟩
  apply quo_eq_of
  rw [h1, ← hc, hy, ← Units.val_mul, div_mul_cancel]

end GlobalTheory.AntiCycRead

end

noncomputable section

namespace GlobalTheory.AntiCycRead

/- English proof (translation)
Introduce `D W L _ σ p hp δ hH hF hfin hcong hval`. Take `⟨χ, hχ⟩` from `GlobalTheory.DetRootChar.circle_hom_factor (quo D) δ (ker_trivial D δ hF hfin)`. Establish `hxi : ∀ Y : (AE D)ˣ, (((Circle.toUnits.comp χ) (quo D Y) : ℂˣ) : ℂ) = ((δ Y : Circle) : ℂ)`. Introduce `Y`. Rewrite using `[val_of_quo, hχ]`.

Use `⟨Circle.toUnits.comp χ, ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `x a hxa hx`. Break down `subsingleton_or_nontrivial (Af D.host.F) with hs | hs` into its components or cases. Establish `h0 : ∀ z : Af D.host.F ⊗[D.host.F] D.host.E, z = 0`. Introduce `z`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rfl`. Consider the case `tmul b e => rw [Subsingleton.elim b 0, TensorProduct.zero_tmul]`. Consider the case `add u v hu hv => rw [hu, hv, add_zero]`. Establish `hx1 : x = 1` using `Units.ext ((h0 _).trans (h0 _).symm)`.

Rewrite using `[hx1, map_one]`. Take `⟨w, hw⟩` from `exists_rat D x a hxa hx`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[← hw, hxi, hH.2 w]`. Both sides reduce to the same expression.

Introduce and unpack `x hx ⟨w, hw, hwe⟩`. Take `⟨Y, hY, hYc, hQ⟩` from `exists_cong D p hp x hx w hw hwe`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[← hQ, hxi, hcong Y hY hYc]`. Both sides reduce to the same expression.

Introduce `x hx`. Take `⟨Y, hQ⟩` from `exists_normOne D x hx`. Take `⟨a, ha⟩` from `hval Y`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[← hQ, hxi]`.

Conclude with `ha`. Introduce `g x hx`. Rewrite using `[← quo_of_isDetRoot D W g x hx, hxi]`.
-/
theorem read_anticyc : ∀ (D : D7) (W : HSp D) (L : Type) [Field L] (σ : L →+* ℂ) (p : ℕ), Odd p → ∀ δ : (AE D)ˣ →* Circle, IsHeckeChar D δ → (∀ a, δ (Formalism.L2.Theta.idF D a) = 1) → (∃ m : ℕ, 0 < m ∧ ∀ x, δ x ^ m = 1) → (∀ x, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = p • y) → δ x = 1) → (∀ x, ∃ y : L, σ y = ((δ x : Circle) : ℂ)) → ∃ xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTwist σ p xi ∧ ∀ (g : GA D W) (x : (AE D)ˣ), IsDetRoot W g x → ((xi (Matrix.GeneralLinearGroup.det (finHom W g)) : ℂˣ) : ℂ) = ((δ x : Circle) : ℂ) := by
  intro D W L _ σ p hp δ hH hF hfin hcong hval
  obtain ⟨χ, hχ⟩ := GlobalTheory.DetRootChar.circle_hom_factor (quo D) δ (ker_trivial D δ hF hfin)
  have hxi : ∀ Y : (AE D)ˣ, (((Circle.toUnits.comp χ) (quo D Y) : ℂˣ) : ℂ) = ((δ Y : Circle) : ℂ) := by
    intro Y
    rw [val_of_quo, hχ]
  refine ⟨Circle.toUnits.comp χ, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x a hxa hx
    rcases subsingleton_or_nontrivial (Af D.host.F) with hs | hs
    · have h0 : ∀ z : Af D.host.F ⊗[D.host.F] D.host.E, z = 0 := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul b e => rw [Subsingleton.elim b 0, TensorProduct.zero_tmul]
        | add u v hu hv => rw [hu, hv, add_zero]
      have hx1 : x = 1 := Units.ext ((h0 _).trans (h0 _).symm)
      rw [hx1, map_one]
    obtain ⟨w, hw⟩ := exists_rat D x a hxa hx
    apply Units.ext
    rw [← hw, hxi, hH.2 w]
    rfl
  · rintro x hx ⟨w, hw, hwe⟩
    obtain ⟨Y, hY, hYc, hQ⟩ := exists_cong D p hp x hx w hw hwe
    apply Units.ext
    rw [← hQ, hxi, hcong Y hY hYc]
    rfl
  · intro x hx
    obtain ⟨Y, hQ⟩ := exists_normOne D x hx
    obtain ⟨a, ha⟩ := hval Y
    refine ⟨a, ?_⟩
    rw [← hQ, hxi]
    exact ha
  · intro g x hx
    rw [← quo_of_isDetRoot D W g x hx, hxi]

end GlobalTheory.AntiCycRead

end
