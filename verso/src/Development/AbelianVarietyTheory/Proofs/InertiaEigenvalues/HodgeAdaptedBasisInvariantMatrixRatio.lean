import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeStructureOfAdaptedInvariantFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.InvRatio

/- English proof (translation)
Establish `e : Q'.map σ = Q.map σ * c.map σ` using `by rw [← hc, Matrix.map_mul]`. Establish `: Q * c.map σ = Q * c`. Rewrite using `[hc, ← h1, Matrix.mul_assoc, ← e, h2]`. Conclude with `hQu.mul_left_cancel this`.
-/
theorem fixed_of_inv {A : Type} [CommRing A] {d : ℕ} (σ : A →+* A) (R Q Q' c : Matrix (Fin d) (Fin d) A)
    (hQu : IsUnit Q) (hc : Q * c = Q') (h1 : R * Q.map σ = Q) (h2 : R * Q'.map σ = Q') : c.map σ = c := by
  have e : Q'.map σ = Q.map σ * c.map σ := by rw [← hc, Matrix.map_mul]
  have : Q * c.map σ = Q * c := by
    rw [hc, ← h1, Matrix.mul_assoc, ← e, h2]
  exact hQu.mul_left_cancel this

end GlobalTheory.BKLim.InvRatio

open GlobalTheory.BKLim.InvRatio in

/- English proof (translation)
Introduce `l _ K bk C hI d ρ Q hQu hQ H`. Take `⟨-, hinj, hF, -⟩` from `BdRField.bdR_isField l`. Take `⟨u, hu, -⟩` from `AdaptedHodge.xi_unit_fil C (bk.ev bk.E) bk.span_ev`. Use `set ι := algebraMap (Per.BdRp l) (Per.BdR l) with hι`. Establish `hz : ∀ z : ℤ_[l], ι (C.o (zOm l z)) = Per.zD l z`.

Introduce `z`. Simplify using `only [zOm, RingHom.comp_apply, hι]`. Conclude with `(congrArg ι (C.o_sec.z z)).trans (GlobalTheory.RingIface.zD_eq_alg l z).symm`. Establish `hHinv : ∀ g : ↥(GK K), (ρ g).map (Per.zD l) * H.Q.map (Per.σD (g : GQ l)) = H.Q`. Introduce `g`.

Establish `h` using `H.inv g g.2`. Establish `e : ((ρ g).map (zOm l)).map (ι.comp C.o) = (ρ g).map (Per.zD l)`. Use extensionality with `i j`. Simplify using `[hz]`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.

Use `set dg : Fin d → Per.BdR l := fun k => ((u⁻¹ ^ H.q : (Per.BdR l)ˣ) : Per.BdR l) * (u : Per.BdR l) ^ H.p k with hdg`. Establish `hQH : H.Q = H.V.map ι * Matrix.diagonal dg`. Use extensionality with `i k`. Rewrite using `[Matrix.mul_diagonal, Matrix.map_apply]`. Establish `h` using `H.Q_eq i k`.

Rewrite `h` using `[map_mul, map_pow, ← hι, ← hu]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one, one_mul]`. Use `_ = ι (H.V i k) * dg k := by rw [h, hdg]; ring`. Establish `hHu : IsUnit H.Q`.

Rewrite using `[hQH]`. Use `IsUnit.mul ?_ ?_` and prove the remaining obligations. Conclude with `H.unit.map (ι.mapMatrix)`. Rewrite using `[Matrix.isUnit_diagonal, Pi.isUnit_iff]`. Introduce `k`.

Conclude with `(Units.isUnit _).mul ((Units.isUnit u).pow _)`. Take `⟨Qi, hQi⟩ : ∃ Qi, Q * Qi = 1` from `⟨_, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hQu)⟩`. Take `⟨Hi, hHi⟩ : ∃ Hi, H.Q * Hi = 1` from `⟨_, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hHu)⟩`. Use `set c₀ := Qi * H.Q with hc₀`. Use `set c₀' := Hi * Q with hc₀'`.

Establish `e0 : Q * c₀ = H.Q` using `by rw [hc₀, ← Matrix.mul_assoc, hQi, Matrix.one_mul]`. Establish `e0' : H.Q * c₀' = Q` using `by rw [hc₀', ← Matrix.mul_assoc, hHi, Matrix.one_mul]`. Establish `fix0 : ∀ g ∈ GK K, ∀ i j, Per.σD g (c₀ i j) = c₀ i j`. Introduce `g hg i j`. Use `fixed_of_inv (Per.σD g) _ Q H.Q c₀ hQu e0 (hQ ⟨g, hg⟩) (hHinv ⟨g, hg⟩)` as an intermediate fact.

Conclude with `congrFun (congrFun this i) j`. Establish `fix0' : ∀ g ∈ GK K, ∀ i j, Per.σD g (c₀' i j) = c₀' i j`. Introduce `g hg i j`. Use `fixed_of_inv (Per.σD g) _ H.Q Q c₀' hHu e0' (hHinv ⟨g, hg⟩) (hQ ⟨g, hg⟩)` as an intermediate fact. Conclude with `congrFun (congrFun this i) j`.

Use `choose x hxK hx using fun i j => hI K (c₀ i j) (fun g hg => fix0 g hg i j)`. Use `choose x' hxK' hx' using fun i j => hI K (c₀' i j) (fun g hg => fix0' g hg i j)`. Use `haveI : Nontrivial (Per.BdR l) := hF.nontrivial`. Establish `hoinj : Function.Injective C.oD` using `C.oD.injective`. Establish `hm : (Matrix.of x).map C.oD = c₀` using `by ext i j; simp [hx]`.

Establish `hm' : (Matrix.of x').map C.oD = c₀'` using `by ext i j; simp [hx']`. Use `⟨Matrix.of x, Matrix.of x', hxK, hxK', ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : c₀ * c₀' = 1`. Rewrite using `[hc₀, hc₀', Matrix.mul_assoc, ← Matrix.mul_assoc H.Q, hHi, Matrix.one_mul]`. Conclude with `mul_eq_one_comm.1 hQi`.

Establish `h2 : (Matrix.of x * Matrix.of x').map C.oD = (1 : Matrix (Fin d) (Fin d) (Om l)).map C.oD`. Rewrite using `[Matrix.map_mul, hm, hm', h1, Matrix.map_one _ (map_zero _) (map_one _)]`. Use extensionality with `i j`. Conclude with `hoinj (congrFun (congrFun h2 i) j)`. Rewrite using `[hm, e0]`.
-/
theorem GlobalTheory.BKLim.invMatrix_ratio : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), C.InvdR → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (Q : Matrix (Fin d) (Fin d) (Per.BdR l)), IsUnit Q → (∀ g : ↥(GK K), (ρ g).map (Per.zD l) * Q.map (Per.σD (g : GQ l)) = Q) → ∀ H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K, ∃ c c' : Matrix (Fin d) (Fin d) (Om l), (∀ i j, c i j ∈ K.1) ∧ (∀ i j, c' i j ∈ K.1) ∧ c * c' = 1 ∧ H.Q = Q * c.map C.oD := by
  intro l _ K bk C hI d ρ Q hQu hQ H
  obtain ⟨-, hinj, hF, -⟩ := BdRField.bdR_isField l
  obtain ⟨u, hu, -⟩ := AdaptedHodge.xi_unit_fil C (bk.ev bk.E) bk.span_ev
  set ι := algebraMap (Per.BdRp l) (Per.BdR l) with hι

  have hz : ∀ z : ℤ_[l], ι (C.o (zOm l z)) = Per.zD l z := by
    intro z
    simp only [zOm, RingHom.comp_apply, hι]
    exact (congrArg ι (C.o_sec.z z)).trans (GlobalTheory.RingIface.zD_eq_alg l z).symm
  have hHinv : ∀ g : ↥(GK K), (ρ g).map (Per.zD l) * H.Q.map (Per.σD (g : GQ l)) = H.Q := by
    intro g
    have h := H.inv g g.2
    have e : ((ρ g).map (zOm l)).map (ι.comp C.o) = (ρ g).map (Per.zD l) := by
      ext i j; simp [hz]
    rwa [e] at h

  set dg : Fin d → Per.BdR l := fun k => ((u⁻¹ ^ H.q : (Per.BdR l)ˣ) : Per.BdR l) * (u : Per.BdR l) ^ H.p k with hdg
  have hQH : H.Q = H.V.map ι * Matrix.diagonal dg := by
    ext i k
    rw [Matrix.mul_diagonal, Matrix.map_apply]
    have h := H.Q_eq i k
    rw [map_mul, map_pow, ← hι, ← hu] at h
    calc H.Q i k = ((u⁻¹ ^ H.q : (Per.BdR l)ˣ) : Per.BdR l) * ((u : Per.BdR l) ^ H.q * H.Q i k) := by
          rw [← mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one, one_mul]
      _ = ι (H.V i k) * dg k := by rw [h, hdg]; ring
  have hHu : IsUnit H.Q := by
    rw [hQH]
    refine IsUnit.mul ?_ ?_
    · exact H.unit.map (ι.mapMatrix)
    · rw [Matrix.isUnit_diagonal, Pi.isUnit_iff]
      intro k
      exact (Units.isUnit _).mul ((Units.isUnit u).pow _)

  obtain ⟨Qi, hQi⟩ : ∃ Qi, Q * Qi = 1 := ⟨_, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hQu)⟩
  obtain ⟨Hi, hHi⟩ : ∃ Hi, H.Q * Hi = 1 := ⟨_, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hHu)⟩
  set c₀ := Qi * H.Q with hc₀
  set c₀' := Hi * Q with hc₀'
  have e0 : Q * c₀ = H.Q := by rw [hc₀, ← Matrix.mul_assoc, hQi, Matrix.one_mul]
  have e0' : H.Q * c₀' = Q := by rw [hc₀', ← Matrix.mul_assoc, hHi, Matrix.one_mul]
  have fix0 : ∀ g ∈ GK K, ∀ i j, Per.σD g (c₀ i j) = c₀ i j := by
    intro g hg i j
    have := fixed_of_inv (Per.σD g) _ Q H.Q c₀ hQu e0 (hQ ⟨g, hg⟩) (hHinv ⟨g, hg⟩)
    exact congrFun (congrFun this i) j
  have fix0' : ∀ g ∈ GK K, ∀ i j, Per.σD g (c₀' i j) = c₀' i j := by
    intro g hg i j
    have := fixed_of_inv (Per.σD g) _ H.Q Q c₀' hHu e0' (hHinv ⟨g, hg⟩) (hQ ⟨g, hg⟩)
    exact congrFun (congrFun this i) j
  choose x hxK hx using fun i j => hI K (c₀ i j) (fun g hg => fix0 g hg i j)
  choose x' hxK' hx' using fun i j => hI K (c₀' i j) (fun g hg => fix0' g hg i j)
  haveI : Nontrivial (Per.BdR l) := hF.nontrivial
  have hoinj : Function.Injective C.oD := C.oD.injective
  have hm : (Matrix.of x).map C.oD = c₀ := by ext i j; simp [hx]
  have hm' : (Matrix.of x').map C.oD = c₀' := by ext i j; simp [hx']
  refine ⟨Matrix.of x, Matrix.of x', hxK, hxK', ?_, ?_⟩
  · have h1 : c₀ * c₀' = 1 := by
      rw [hc₀, hc₀', Matrix.mul_assoc, ← Matrix.mul_assoc H.Q, hHi, Matrix.one_mul]
      exact mul_eq_one_comm.1 hQi
    have h2 : (Matrix.of x * Matrix.of x').map C.oD = (1 : Matrix (Fin d) (Fin d) (Om l)).map C.oD := by
      rw [Matrix.map_mul, hm, hm', h1, Matrix.map_one _ (map_zero _) (map_one _)]
    ext i j
    exact hoinj (congrFun (congrFun h2 i) j)
  · rw [hm, e0]

end
