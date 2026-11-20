import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryMulVecEqOfFormEqStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabCosets

open GlobalTheory.RatDiscrete IsDedekindDomain

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]`.
-/
theorem map_mulVec_incl {E A : Type} [CommRing E] [CommRing A] (ι : E →+* A) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) E) (w : Fin n → E) :
    M.map ι *ᵥ (fun i => ι (w i)) = fun i => ι ((M *ᵥ w) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

/- English proof (translation)
Establish `hc : Formalism.UG.cT s (g.map ι) = (Formalism.UG.cT σ g).map ι`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, hι]`. Rewrite using `[hc, ← Matrix.map_mul, ← Matrix.map_mul, hg]`.
-/
theorem unitary_map {E A : Type} [CommRing E] [CommRing A] (σ : E →+* E) (s : A →+* A)
    (ι : E →+* A) (hι : ∀ e, s (ι e) = ι (σ e)) {n : ℕ} (J g : Matrix (Fin n) (Fin n) E)
    (hg : Formalism.UG.cT σ g * J * g = J) :
    Formalism.UG.cT s (g.map ι) * J.map ι * g.map ι = J.map ι := by
  have hc : Formalism.UG.cT s (g.map ι) = (Formalism.UG.cT σ g).map ι := by
    ext i j
    simp [Formalism.UG.cT, hι]
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hg]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, Matrix.conjTranspose_apply, starRingEnd_apply]`.
-/
theorem cT_star {E : Type} [CommRing E] [StarRing E] {n : ℕ} (g : Matrix (Fin n) (Fin n) E) :
    Formalism.UG.cT (starRingEnd E) g = gᴴ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply, starRingEnd_apply]

variable (I : AutInst)

/- English proof (translation)
Establish `hu : Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * γ = I.J` using `hγ`. Take `⟨-, hconj, -⟩` from `I.cm.cmUnram`. Establish `hinf : ∀ v, ∃ u : Formalism.REAL.UJ (I.ε v), uMat u = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v`. Introduce `v`. Establish `hQu : IsUnit (I.P v)` using `I.P_unit v`.

Establish `hQQ : I.P v * (I.P v)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hQu)`. Establish `hQQ' : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1`. Rewrite using `[← Matrix.conjTranspose_mul, hQQ, Matrix.conjTranspose_one]`. Establish `hNu : IsUnit ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))` using `γ.isUnit.map (I.φ v).mapMatrix`. Establish `hM : IsUnit ((I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)` using `((Matrix.isUnit_nonsing_inv_iff.2 hQu).mul hNu).mul hQu`.

Establish `hφ : ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * I.J.map (I.φ v) * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = I.J.map (I.φ v)`. Rewrite using `[← cT_star]`. Use `unitary_map (starRingEnd I.E) (starRingEnd ℂ) (I.φ v) (fun e => ?_) I.J _ hu` and prove the remaining obligations. Rewrite using `[starRingEnd_apply (x := e)]`. Conclude with `(hconj (I.φ v) e).symm`.

Establish `hin : ((I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)ᴴ * Formalism.REAL.Jm (I.ε v) * ((I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) = Formalism.REAL.Jm (I.ε v)`. Rewrite using `[← I.P_spec v]`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc ((I.P v)⁻¹ᴴ) ((I.P v)ᴴ), hQQ', Matrix.one_mul, ← Matrix.mul_assoc (I.P v) ((I.P v)⁻¹), hQQ, Matrix.one_mul]`. Rewrite using `[show ∀ X : Matrix (Fin I.n) (Fin I.n) ℂ, ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * (I.J.map (I.φ v) * ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * X)) = (((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * I.J.map (I.φ v) * (γ : Matrix (Fin I.n) (Fin I.n) I. …`.

Use `⟨⟨hM.unit, ?_⟩, hM.unit_spec⟩` and prove the remaining obligations. Use `show Formalism.REAL.inUJ (I.ε v) (hM.unit : Matrix (Fin I.n) (Fin I.n) ℂ)`. Unfold `Formalism.REAL.inUJ`. Rewrite using `[hM.unit_spec]`. Conclude with `hin`.

Establish `hsig : ∀ e : I.E, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F` using `I.F) (Af I.F) e) = Formalism.UG.inclE (F := I.F) (Af I.F) (starRingEnd I.E e) := by`. Introduce `e`. Use `first`. Consider the case `rfl`. Consider the case `simp [Formalism.UG.sigR, Formalism.UG.inclE, Formalism.BasicNotions.CMData.sig]`.

Establish `hfin : ∃ h : I.Gf, I.fmat h = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F` using `I.F) (Af I.F)) := by`. Use `⟨⟨Matrix.GeneralLinearGroup.map (Formalism.UG.inclE (F := I.F) (Af I.F)) γ, ?_⟩, rfl⟩` and prove the remaining obligations. Conclude with `unitary_map (starRingEnd I.E) (Formalism.UG.sigR I.cm.sig (Af I.F)) (Formalism.UG.inclE (F := I.F) (Af I.F)) hsig I.J _ hu`. Use `choose u hu' using hinf`. Take `⟨h, hh⟩` from `hfin`.

Use `⟨(u, h), ?_⟩` and prove the remaining obligations. Unfold `IsImage`. Conclude with `⟨hu', hh⟩`.
-/
theorem exists_isImage (γ : GL (Fin I.n) I.E) (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) :
    ∃ a, IsImage I (γ : Matrix (Fin I.n) (Fin I.n) I.E) a := by
  classical
  have hu : Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * γ = I.J := hγ
  obtain ⟨-, hconj, -⟩ := I.cm.cmUnram
  have hinf : ∀ v, ∃ u : Formalism.REAL.UJ (I.ε v),
      uMat u = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
    intro v
    have hQu : IsUnit (I.P v) := I.P_unit v
    have hQQ : I.P v * (I.P v)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hQu)
    have hQQ' : ((I.P v)⁻¹)ᴴ * (I.P v)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hQQ, Matrix.conjTranspose_one]
    have hNu : IsUnit ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) :=
      γ.isUnit.map (I.φ v).mapMatrix
    have hM : IsUnit ((I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) :=
      ((Matrix.isUnit_nonsing_inv_iff.2 hQu).mul hNu).mul hQu
    have hφ : ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * I.J.map (I.φ v) *
        (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = I.J.map (I.φ v) := by
      rw [← cT_star]
      refine unitary_map (starRingEnd I.E) (starRingEnd ℂ) (I.φ v) (fun e => ?_) I.J _ hu
      rw [starRingEnd_apply (x := e)]
      exact (hconj (I.φ v) e).symm
    have hin : ((I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)ᴴ *
        Formalism.REAL.Jm (I.ε v) * ((I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) =
        Formalism.REAL.Jm (I.ε v) := by
      rw [← I.P_spec v]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((I.P v)⁻¹ᴴ) ((I.P v)ᴴ), hQQ', Matrix.one_mul,
        ← Matrix.mul_assoc (I.P v) ((I.P v)⁻¹), hQQ, Matrix.one_mul]
      rw [show ∀ X : Matrix (Fin I.n) (Fin I.n) ℂ, ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ *
          (I.J.map (I.φ v) * ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * X)) =
          (((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * I.J.map (I.φ v) *
            (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) * X from
          fun X => by simp only [Matrix.mul_assoc], hφ]
    refine ⟨⟨hM.unit, ?_⟩, hM.unit_spec⟩
    show Formalism.REAL.inUJ (I.ε v) (hM.unit : Matrix (Fin I.n) (Fin I.n) ℂ)
    unfold Formalism.REAL.inUJ
    rw [hM.unit_spec]
    exact hin
  have hsig : ∀ e : I.E, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) e) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (starRingEnd I.E e) := by
    intro e
    first
    | rfl
    | simp [Formalism.UG.sigR, Formalism.UG.inclE, Formalism.BasicNotions.CMData.sig]
  have hfin : ∃ h : I.Gf, I.fmat h =
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
    refine ⟨⟨Matrix.GeneralLinearGroup.map (Formalism.UG.inclE (F := I.F) (Af I.F)) γ, ?_⟩, rfl⟩
    exact unitary_map (starRingEnd I.E) (Formalism.UG.sigR I.cm.sig (Af I.F))
      (Formalism.UG.inclE (F := I.F) (Af I.F)) hsig I.J _ hu
  choose u hu' using hinf
  obtain ⟨h, hh⟩ := hfin
  refine ⟨(u, h), ?_⟩
  unfold IsImage
  exact ⟨hu', hh⟩

/- English proof (translation)
Establish `hhalf : (2 : I.E)⁻¹ ∉ (algebraMap (𝓞 I.E) I.E).range`. Introduce and unpack `⟨z, hz⟩`. Establish `hint : IsIntegral ℤ ((2 : I.E)⁻¹)`. Rewrite using `[← hz]`. Conclude with `z.isIntegral_coe`.

Establish `h2 : (2 : I.E)⁻¹ = algebraMap ℚ I.E (2 : ℚ)⁻¹` using `by simp`. Rewrite `hint` using `[h2, isIntegral_algebraMap_iff (algebraMap ℚ I.E).injective]`. Take `⟨m, hm⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hint`. Simplify using `only [algebraMap_int_eq, eq_intCast] at hm`. Establish `h3 : ((m * 2 : ℤ) : ℚ) = 1`.

Use `push_cast`. Rewrite using `[hm]`. Evaluate the numerical expressions. Establish `h4 : m * 2 = 1` using `by exact_mod_cast h3`. Use linear arithmetic over natural numbers and integers.

Introduce `x y hxy`. Use function extensionality and compare the values at `i`. Establish `h : Formalism.UG.inclE (F` using `I.F) (Af I.F) (x i) = Formalism.UG.inclE (F := I.F) (Af I.F) (y i) := congrFun hxy i`. Assume the negation of the conclusion as `hne`. Apply `hhalf` to reduce the goal to its premises.

Apply `GlobalTheory.PointLattice.mem_range_of_incl (F := I.F)` to reduce the goal to its premises. Establish `hd : x i - y i ≠ 0` using `sub_ne_zero.2 hne`. Establish `e : (x i - y i) * (2 * (x i - y i))⁻¹ = (2 : I.E)⁻¹`. Rewrite using `[mul_inv, mul_left_comm, mul_inv_cancel₀ hd, mul_one]`. Rewrite using `[← e, map_mul, map_sub, h, sub_self, zero_mul]`.

Conclude with `Subring.zero_mem _`.
-/
theorem afVec_injective {m : ℕ} : Function.Injective (afVec I (m := m)) := by
  have hhalf : (2 : I.E)⁻¹ ∉ (algebraMap (𝓞 I.E) I.E).range := by
    rintro ⟨z, hz⟩
    have hint : IsIntegral ℤ ((2 : I.E)⁻¹) := by
      rw [← hz]
      exact z.isIntegral_coe
    have h2 : (2 : I.E)⁻¹ = algebraMap ℚ I.E (2 : ℚ)⁻¹ := by simp
    rw [h2, isIntegral_algebraMap_iff (algebraMap ℚ I.E).injective] at hint
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    simp only [algebraMap_int_eq, eq_intCast] at hm
    have h3 : ((m * 2 : ℤ) : ℚ) = 1 := by
      push_cast
      rw [hm]
      norm_num
    have h4 : m * 2 = 1 := by exact_mod_cast h3
    omega
  intro x y hxy
  funext i
  have h : Formalism.UG.inclE (F := I.F) (Af I.F) (x i) = Formalism.UG.inclE (F := I.F) (Af I.F) (y i) :=
    congrFun hxy i
  by_contra hne
  apply hhalf
  apply GlobalTheory.PointLattice.mem_range_of_incl (F := I.F)
  have hd : x i - y i ≠ 0 := sub_ne_zero.2 hne
  have e : (x i - y i) * (2 * (x i - y i))⁻¹ = (2 : I.E)⁻¹ := by
    rw [mul_inv, mul_left_comm, mul_inv_cancel₀ hd, mul_one]
  rw [← e, map_mul, map_sub, h, sub_self, zero_mul]
  exact Subring.zero_mem _

variable {I}

/- English proof (translation)
Take `⟨-, h2⟩` from `h`. Rewrite using `[h2]`. Unfold `afVec`. Conclude with `map_mulVec_incl _ γ y`.
-/
theorem fmat_mulVec {γ a} (h : IsImage I γ a) (y : Fin I.n → I.E) :
    I.fmat a.2 *ᵥ afVec I y = afVec I (γ *ᵥ y) := by
  obtain ⟨-, h2⟩ := h
  rw [h2]
  unfold afVec
  exact map_mulVec_incl _ γ y

/- English proof (translation)
Take `⟨h1, -⟩` from `h`. Rewrite using `[h1 v]`. Unfold `infVec`. Establish `hQQ : I.P v * (I.P v)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_assoc _ (I.P v), hQQ, Matrix.mul_one, ← Matrix.mulVec_mulVec, map_mulVec_incl]`.
-/
theorem uMat_mulVec {γ a} (h : IsImage I γ a) (y : Fin I.n → I.E) (v) :
    uMat (a.1 v) *ᵥ infVec I v y = infVec I v (γ *ᵥ y) := by
  obtain ⟨h1, -⟩ := h
  rw [h1 v]
  unfold infVec
  have hQQ : I.P v * (I.P v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc _ (I.P v), hQQ, Matrix.mul_one, ← Matrix.mulVec_mulVec,
    map_mulVec_incl]

/- English proof (translation)
Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]`.
-/
theorem length_mulVec {γ : Matrix (Fin I.n) (Fin I.n) I.E} (h : γᴴ * I.J * γ = I.J) (y : Fin I.n → I.E) :
    star (γ *ᵥ y) ⬝ᵥ (I.J *ᵥ (γ *ᵥ y)) = star y ⬝ᵥ (I.J *ᵥ y) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

/- English proof (translation)
Establish `hmem : ∀ h' : I.Gf, (γ *ᵥ y ∈ lamX I (1, a.2 * h') ↔ y ∈ lamX I (1, h'))`. Introduce `h'`. Rewrite using `[(GlobalTheory.PointLattice.lamX_selfDual I _).1, (GlobalTheory.PointLattice.lamX_selfDual I _).1]`. Establish `e1 : (fun i => Formalism.UG.inclE (F` using `I.F) (Af I.F) ((γ *ᵥ y) i)) = I.fmat a.2 *ᵥ afVec I y := (fmat_mulVec h y).symm`. Establish `e2 : I.fmat ((1, a.2 * h') : I.GA).2⁻¹ * I.fmat a.2 = I.fmat ((1, h') : I.GA).2⁻¹` using `by show I.fmat (a.2 * h')⁻¹ * I.fmat a.2 = I.fmat h'⁻¹`.

Simplify using `only [AutInst.fmat, _root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, Subgroup.coe_inv, Units.inv_mul, Matrix.mul_one]`. Rewrite using `[e1, Matrix.mulVec_mulVec, e2]`. Both sides reduce to the same expression. Unfold `gaussAt`. Use `congr 1`.

Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[← uMat_mulVec h y v, Prod.fst_mul, Pi.mul_apply]`. Use `congr 2`. Use `show ((((a.1 v * g.1 v : Formalism.REAL.UJ (I.ε v)) : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ) : Matrix (Fin I.n) (Fin I.n) ℂ))⁻¹ *ᵥ (uMat (a.1 v) *ᵥ infVec I v y) = (uMat (g.1 v))⁻¹ *ᵥ infVec I v y`. Rewrite using `[Subgroup.coe_mul, ← Matrix.coe_units_inv, ← Matrix.coe_units_inv, _root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`.

Distinguish the cases in `hy : y ∈ lamX I (1, g.2)`. Establish `h1 : a.2 * g.2 ∈ {h' : I.Gf | γ *ᵥ y ∈ lamX I (1, h')}` using `(hmem g.2).2 hy`. Establish `h2 : g.2 ∈ {h' : I.Gf | y ∈ lamX I (1, h')}` using `hy`. Simplify using `only [Prod.snd_mul, Set.indicator_of_mem h1, Set.indicator_of_mem h2, Pi.one_apply]`. Establish `h1 : a.2 * g.2 ∉ {h' : I.Gf | γ *ᵥ y ∈ lamX I (1, h')}` using `fun h0 => hy ((hmem g.2).1 h0)`.

Establish `h2 : g.2 ∉ {h' : I.Gf | y ∈ lamX I (1, h')}` using `hy`. Simplify using `only [Prod.snd_mul, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]`.
-/
theorem gaussAt_mul {γ a} (h : IsImage I γ a) (y : Fin I.n → I.E) (g : I.GA) :
    gaussAt I (γ *ᵥ y) (a * g) = gaussAt I y g := by
  have hmem : ∀ h' : I.Gf, (γ *ᵥ y ∈ lamX I (1, a.2 * h') ↔ y ∈ lamX I (1, h')) := by
    intro h'
    rw [(GlobalTheory.PointLattice.lamX_selfDual I _).1, (GlobalTheory.PointLattice.lamX_selfDual I _).1]
    have e1 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((γ *ᵥ y) i)) = I.fmat a.2 *ᵥ afVec I y :=
      (fmat_mulVec h y).symm
    have e2 : I.fmat ((1, a.2 * h') : I.GA).2⁻¹ * I.fmat a.2 = I.fmat ((1, h') : I.GA).2⁻¹ := by
      show I.fmat (a.2 * h')⁻¹ * I.fmat a.2 = I.fmat h'⁻¹
      simp only [AutInst.fmat, _root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc,
        Subgroup.coe_inv, Units.inv_mul, Matrix.mul_one]
    rw [e1, Matrix.mulVec_mulVec, e2]
    rfl
  unfold gaussAt
  congr 1
  · refine Finset.prod_congr rfl fun v _ => ?_
    rw [← uMat_mulVec h y v, Prod.fst_mul, Pi.mul_apply]
    congr 2
    show ((((a.1 v * g.1 v : Formalism.REAL.UJ (I.ε v)) : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ) :
      Matrix (Fin I.n) (Fin I.n) ℂ))⁻¹ *ᵥ (uMat (a.1 v) *ᵥ infVec I v y) = (uMat (g.1 v))⁻¹ *ᵥ infVec I v y
    rw [Subgroup.coe_mul, ← Matrix.coe_units_inv, ← Matrix.coe_units_inv, _root_.mul_inv_rev, Units.val_mul,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  · by_cases hy : y ∈ lamX I (1, g.2)
    · have h1 : a.2 * g.2 ∈ {h' : I.Gf | γ *ᵥ y ∈ lamX I (1, h')} := (hmem g.2).2 hy
      have h2 : g.2 ∈ {h' : I.Gf | y ∈ lamX I (1, h')} := hy
      simp only [Prod.snd_mul, Set.indicator_of_mem h1, Set.indicator_of_mem h2, Pi.one_apply]
    · have h1 : a.2 * g.2 ∉ {h' : I.Gf | γ *ᵥ y ∈ lamX I (1, h')} := fun h0 => hy ((hmem g.2).1 h0)
      have h2 : g.2 ∉ {h' : I.Gf | y ∈ lamX I (1, h')} := hy
      simp only [Prod.snd_mul, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]

/- English proof (translation)
Establish `hL : lamX I g = lamX I (1, g.2)`. Rewrite using `[GlobalTheory.PointLattice.lamX_eq_globLat, GlobalTheory.PointLattice.lamX_eq_globLat]`. Establish `hF : ∀ y : Fin I.n → I.E, ENNReal.ofReal (∏ v, gauss (((uMat (g.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y i))) = ∏ v, ENNReal.ofReal (gauss ((uMat (g.1 v))⁻¹ *ᵥ infVec I v y))`. Introduce `y`. Rewrite using `[ENNReal.ofReal_prod_of_nonneg (fun v _ => (gauss_pos _).le)]`.

Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec]`. Both sides reduce to the same expression. Establish `h1` using `tsum_subtype {y : Fin I.n → I.E | y ∈ lamX I g ∧ star y ⬝ᵥ (I.J *ᵥ y) = β} (fun y => ENNReal.ofReal (∏ v, gauss (((uMat (g.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y i))))`. Establish `h2` using `tsum_subtype {y : Fin I.n → I.E | star y ⬝ᵥ (I.J *ᵥ y) = β} (fun y => gaussAt I y g)`.

Unfold `GlobalTheory.GaussMean.gaussSum`. Use `h1.trans (Eq.trans ?_ h2.symm)` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `y`. Apply the tactic sequence `by_cases hy : y ∈ lamX I (1, g.2) <;> by_cases hq : star y ⬝ᵥ (I.J *ᵥ y) = β <;>`.

Simplify using `[Set.indicator, gaussAt, hL, hF, hy, hq]`.
-/
theorem gaussSum_eq (β : I.E) (g : I.GA) :
    gaussSum I β g = ∑' y : {y : Fin I.n → I.E // star y ⬝ᵥ (I.J *ᵥ y) = β}, gaussAt I y.1 g := by
  classical
  have hL : lamX I g = lamX I (1, g.2) := by
    rw [GlobalTheory.PointLattice.lamX_eq_globLat, GlobalTheory.PointLattice.lamX_eq_globLat]
  have hF : ∀ y : Fin I.n → I.E,
      ENNReal.ofReal (∏ v, gauss (((uMat (g.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y i))) =
        ∏ v, ENNReal.ofReal (gauss ((uMat (g.1 v))⁻¹ *ᵥ infVec I v y)) := by
    intro y
    rw [ENNReal.ofReal_prod_of_nonneg (fun v _ => (gauss_pos _).le)]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Matrix.mulVec_mulVec]
    rfl
  have h1 := tsum_subtype {y : Fin I.n → I.E | y ∈ lamX I g ∧ star y ⬝ᵥ (I.J *ᵥ y) = β}
    (fun y => ENNReal.ofReal (∏ v, gauss (((uMat (g.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y i))))
  have h2 := tsum_subtype {y : Fin I.n → I.E | star y ⬝ᵥ (I.J *ᵥ y) = β} (fun y => gaussAt I y g)
  unfold GlobalTheory.GaussMean.gaussSum
  refine h1.trans (Eq.trans ?_ h2.symm)
  congr 1
  funext y
  by_cases hy : y ∈ lamX I (1, g.2) <;> by_cases hq : star y ⬝ᵥ (I.J *ᵥ y) = β <;>
    simp [Set.indicator, gaussAt, hL, hF, hy, hq]

/- English proof (translation)
Introduce `I s x hx`. Establish `hUJ : ∀ δ : GL (Fin I.n) I.E, δ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ↔ (δ : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * δ = I.J`. Introduce `δ`. Rewrite using `[← cT_star]`. Conclude with `Iff.rfl`.

Establish `hJ : I.Jᴴ = I.J`. Rewrite using `[← cT_star]`. Conclude with `I.J_herm`. Establish `hne : star x ⬝ᵥ (I.J *ᵥ x) ≠ 0`. Rewrite using `[hx]`.

Unfold `sgn`. Apply the tactic sequence `split <;> simp`. Establish `hE : Countable I.E` using `Function.Injective.countable (Module.finBasis ℚ I.E).equivFun.injective`. Establish `hW : ∀ y : {y : Fin I.n → I.E // star y ⬝ᵥ (I.J *ᵥ y) = sgn I.E s}, ∃ δ : GL (Fin I.n) I.E, δ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧ (δ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ x = y.1`. Introduce `y`.

Take `⟨m, hm, hmx⟩` from `GlobalTheory.T.exists_unitary_mulVec_eq_of_form_eq' I.E I.n I.J hJ I.J_det x y.1 (hx.trans y.2.symm) hne`. Establish `hdet : IsUnit m.det`. Establish `hd` using `congrArg Matrix.det hm`. Rewrite `hd` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]`. Use `isUnit_iff_ne_zero.2 fun h0 => I.J_det ?_` and prove the remaining obligations.

Simplify `hd.symm` using `[h0]`. Establish `hmU : IsUnit m` using `(Matrix.isUnit_iff_isUnit_det m).2 hdet`. Use `⟨hmU.unit, (hUJ _).2 ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hmU.unit_spec]`. Conclude with `hm`.

Rewrite using `[hmU.unit_spec]`. Conclude with `hmx`. Use `choose δ hδU hδx using hW`. Establish `hR : ∀ y, ∃ a, IsImage I (((δ y)⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) a` using `fun y => exists_isImage I _ (inv_mem (hδU y))`. Use `choose r hr using hR`.

Establish `hrF : ∀ y, r y ∈ I.GFset`. Introduce `y`. Take `⟨h1, h2⟩` from `hr y`. Conclude with `⟨(δ y)⁻¹, inv_mem (hδU y), h1, h2⟩`. Use `⟨{y : Fin I.n → I.E // star y ⬝ᵥ (I.J *ᵥ y) = sgn I.E s}, inferInstance, r, hrF, ?_, ?_⟩` and prove the remaining obligations.

Introduce `γ hγ`. Take `⟨d, hdU, hd1, hd2⟩` from `id hγ`. Establish `hdI : IsImage I (d : Matrix (Fin I.n) (Fin I.n) I.E) γ`. Unfold `IsImage`. Conclude with `⟨hd1, hd2⟩`.

Establish `key : ∀ y, γ * (r y)⁻¹ ∈ stabF I x ↔ (d : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y.1 = x`. Introduce `y`. Establish `hi : IsImage I ((d : Matrix (Fin I.n) (Fin I.n) I.E) * (δ y : Matrix (Fin I.n) (Fin I.n) I.E)) (γ * (r y)⁻¹)`. Establish `hinv` using `isImage_inv I (hr y)`. Rewrite `hinv` using `[inv_inv]`.

Conclude with `isImage_mul I hdI hinv`. Establish `hmemF : γ * (r y)⁻¹ ∈ I.GFset` using `(ratSub I).mul_mem (show γ ∈ ratSub I from hγ) ((ratSub I).inv_mem (show r y ∈ ratSub I from hrF y))`. Unfold `stabF`. Rewrite using `[Set.mem_setOf_eq, fmat_mulVec hi, ← Matrix.mulVec_mulVec, hδx y]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨-, hx'⟩`. Conclude with `afVec_injective I hx'`. Introduce `hx'`. Conclude with `⟨hmemF, by rw [hx']⟩`. Establish `hd' : ((d⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * ((d⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) = I.J` using `(hUJ _).1 (inv_mem hdU)`.

Use `⟨⟨((d⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ x, by rw [length_mulVec hd', hx]⟩, (key _).2 ?_, fun y hy => ?_⟩` and prove the remaining obligations. Use `show (d : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ (((d⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ x) = x`. Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Apply `Subtype.ext show y.1 = ((d⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ x` to reduce the goal to its premises. Rewrite using `[← (key y).1 hy, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`.

Introduce `g`. Rewrite using `[gaussSum_eq]`. Use `tsum_congr fun y => ?_` and prove the remaining obligations. Rewrite using `[← gaussAt_mul (hr y) y.1 g]`. Use `congr 1`.

Rewrite using `[← hδx y, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`.
-/
theorem gaussSum_cosets : ∀ (I : AutInst) (s : Bool) (x : Fin I.n → I.E), star x ⬝ᵥ (I.J *ᵥ x) = sgn I.E s → ∃ (ι : Type) (_ : Countable ι) (r : ι → I.GA), (∀ i, r i ∈ I.GFset) ∧ (∀ γ ∈ I.GFset, ∃! i, γ * (r i)⁻¹ ∈ stabF I x) ∧ ∀ g, gaussSum I (sgn I.E s) g = ∑' i, gaussAt I x (r i * g) := by
  intro I s x hx
  classical
  have hUJ : ∀ δ : GL (Fin I.n) I.E, δ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ↔
      (δ : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * δ = I.J := by
    intro δ
    rw [← cT_star]
    exact Iff.rfl
  have hJ : I.Jᴴ = I.J := by
    rw [← cT_star]
    exact I.J_herm
  have hne : star x ⬝ᵥ (I.J *ᵥ x) ≠ 0 := by
    rw [hx]
    unfold sgn
    split <;> simp
  have hE : Countable I.E :=
    Function.Injective.countable (Module.finBasis ℚ I.E).equivFun.injective
  have hW : ∀ y : {y : Fin I.n → I.E // star y ⬝ᵥ (I.J *ᵥ y) = sgn I.E s}, ∃ δ : GL (Fin I.n) I.E,
      δ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧ (δ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ x = y.1 := by
    intro y
    obtain ⟨m, hm, hmx⟩ := GlobalTheory.T.exists_unitary_mulVec_eq_of_form_eq' I.E I.n I.J hJ I.J_det x y.1 (hx.trans y.2.symm) hne
    have hdet : IsUnit m.det := by
      have hd := congrArg Matrix.det hm
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at hd
      refine isUnit_iff_ne_zero.2 fun h0 => I.J_det ?_
      simpa [h0] using hd.symm
    have hmU : IsUnit m := (Matrix.isUnit_iff_isUnit_det m).2 hdet
    refine ⟨hmU.unit, (hUJ _).2 ?_, ?_⟩
    · rw [hmU.unit_spec]
      exact hm
    · rw [hmU.unit_spec]
      exact hmx
  choose δ hδU hδx using hW
  have hR : ∀ y, ∃ a, IsImage I (((δ y)⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) a :=
    fun y => exists_isImage I _ (inv_mem (hδU y))
  choose r hr using hR
  have hrF : ∀ y, r y ∈ I.GFset := by
    intro y
    obtain ⟨h1, h2⟩ := hr y
    exact ⟨(δ y)⁻¹, inv_mem (hδU y), h1, h2⟩
  refine ⟨{y : Fin I.n → I.E // star y ⬝ᵥ (I.J *ᵥ y) = sgn I.E s}, inferInstance, r, hrF, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨d, hdU, hd1, hd2⟩ := id hγ
    have hdI : IsImage I (d : Matrix (Fin I.n) (Fin I.n) I.E) γ := by
      unfold IsImage
      exact ⟨hd1, hd2⟩
    have key : ∀ y, γ * (r y)⁻¹ ∈ stabF I x ↔ (d : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y.1 = x := by
      intro y
      have hi : IsImage I ((d : Matrix (Fin I.n) (Fin I.n) I.E) * (δ y : Matrix (Fin I.n) (Fin I.n) I.E))
          (γ * (r y)⁻¹) := by
        have hinv := isImage_inv I (hr y)
        rw [inv_inv] at hinv
        exact isImage_mul I hdI hinv
      have hmemF : γ * (r y)⁻¹ ∈ I.GFset :=
        (ratSub I).mul_mem (show γ ∈ ratSub I from hγ) ((ratSub I).inv_mem (show r y ∈ ratSub I from hrF y))
      unfold stabF
      rw [Set.mem_setOf_eq, fmat_mulVec hi, ← Matrix.mulVec_mulVec, hδx y]
      constructor
      · rintro ⟨-, hx'⟩
        exact afVec_injective I hx'
      · intro hx'
        exact ⟨hmemF, by rw [hx']⟩
    have hd' : ((d⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J *
        ((d⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) = I.J := (hUJ _).1 (inv_mem hdU)
    refine ⟨⟨((d⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ x, by rw [length_mulVec hd', hx]⟩,
      (key _).2 ?_, fun y hy => ?_⟩
    · show (d : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ (((d⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    · apply Subtype.ext
      show y.1 = ((d⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ x
      rw [← (key y).1 hy, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  · intro g
    rw [gaussSum_eq]
    refine tsum_congr fun y => ?_
    rw [← gaussAt_mul (hr y) y.1 g]
    congr 1
    rw [← hδx y, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

end GlobalTheory.StabCosets
