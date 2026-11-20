import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittSt
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSKfOrb
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittOEv
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AlgWitt
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittGS
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LamAE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter
  Matrix Formalism.L2.SG.Pf.NcS.KfOrbPf Formalism.L2.SG.Pf.NcS.IntWittAlg
open scoped TensorProduct

section Main

/- English proof (translation)
Simplify using `[sigR, inclR]`.
-/
theorem sigR_inclR' {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

/- English proof (translation)
Simplify using `only [Formalism.UG.hform, map_sum, map_mul, JR, Matrix.map_apply, sigR_inclR']`. Both sides reduce to the same expression.
-/
theorem hform_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    Formalism.UG.hform (sigR R σ) (JR R J) (fun i => inclR R (x i)) (fun i => inclR R (y i)) =
      inclR R (Formalism.UG.hform (σ : E →+* E) J x y) := by
  simp only [Formalism.UG.hform, map_sum, map_mul, JR, Matrix.map_apply, sigR_inclR']
  rfl

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J a X0 Λ hCM hJ hT hLat d b`. Establish `: FiniteDimensional F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Take `⟨L, hLL, rfl⟩` from `hLat`. Establish `hσ : ∀ z, σ (σ z) = z` using `PI.VolStabS.sigma_invol σ hCM.2.2.2`. Establish `hJh : Formalism.UG.IsHerm (σ : E →+* E) J`.

Unfold `Formalism.UG.IsHerm Formalism.UG.cT`. Use extensionality with `i j`. Simplify using `only [Matrix.transpose_apply, Matrix.map_apply]`. Conclude with `hJ.1 i j`. Take `⟨P, Q, hQP, hPo, hPd⟩` from `hD E (σ : E →+* E) hσ two_ne_zero n J hJh a X0 hT`.

Use `set Z0 : Fin a → Fin n → E := fun i => ∑ l, P i l • X0 l with hZ0`. Establish `hZ0e : ∀ i, Z0 i = ∑ l, P i l • X0 l` using `fun i => rfl`. Establish `hX0e : ∀ c, X0 c = ∑ l, Q c l • Z0 l` using `fun c => by`. Use function extensionality and compare the values at `k`. Simplify using `only [hZ0, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Establish `hm : ∀ m, ∑ l, Q c l * (P l m * X0 m k) = (if c = m then 1 else 0) * X0 m k`. Introduce `m`. Repeatedly rewrite using `[← mul_assoc, ← Finset.sum_mul]`. Rewrite using `[← Matrix.mul_apply, hQP, Matrix.one_apply]`.

Repeatedly rewrite using `[hm]`. Simplify using the standard rewrite rules. Set `δ : Fin a → E` to `fun i => Formalism.UG.hform (σ : E →+* E) J (Z0 i) (Z0 i)`. Establish `hδσ : ∀ i, σ (δ i) = δ i` using `fun i => hform_conj (σ : E →+* E) J hσ hJh _ _`. Establish `hJi : J⁻¹ * J = 1` using `Matrix.nonsing_inv_mul J (isUnit_iff_ne_zero.2 hJ.2)`.

Use `filter_upwards [ev_latLoc_std L hLL, eventually_all.2 fun k => ev_oev (F := F) (b k), eventually_all.2 fun i => eventually_all.2 fun j => ev_oev (F := F) (J i j), eventually_all.2 fun i => eventually_all.2 fun j => ev_oev (F := F) (J⁻¹ i j), eventually_all.2 fun i => ev_oev (F := …`. Introduce `X hX hgram`. Set `O` to `oevRing (E := E) v`. Establish `hXO : ∀ c k, X c k ∈ O`. Introduce `c k`.

Use `show X c k ∈ OEv (E := E) v`. Rewrite using `[← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr (X c k)]`. Use `Submodule.sum_mem _ fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.basis_apply]`. Conclude with `oev_smul' v (hX c k l) (hbv l)`.

Set `s` to `sigR (Fv F v) σ`. Establish `hs : ∀ z, s (s z) = z` using `PI.VolStabS.sigR_invol (Fv F v) σ hσ`. Establish `hsO : ∀ z ∈ O, s z ∈ O`. Introduce `z hz`. Conclude with `oev_sigR v σ hz`.

Set `Jv` to `JR (F := F) (Fv F v) J`. Set `Jv'` to `JR (F := F) (Fv F v) J⁻¹`. Establish `hJJ : Jv' * Jv = 1` using `by show J⁻¹.map (inclR (F := F) (Fv F v)) * J.map (inclR (F := F) (Fv F v)) = 1`. Rewrite using `[← Matrix.map_mul, hJi, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hJvh : Formalism.UG.IsHerm s Jv`.

Unfold `Formalism.UG.IsHerm Formalism.UG.cT`. Use extensionality with `i j`. Simplify using `only [Matrix.transpose_apply, Matrix.map_apply, Jv, JR, s, sigR_inclR']`. Rewrite using `[hJ.1 i j]`. Set `y : Fin a → Fin n → Fv F v ⊗[F] E` to `fun i k => inclR (F := F) (Fv F v) (Z0 i k)`.

Set `x : Fin a → Fin n → Fv F v ⊗[F] E` to `fun i => ∑ l, inclR (F := F) (Fv F v) (P i l) • X l`. Establish `hxO : ∀ i k, x i k ∈ O`. Introduce `i k`. Simplify using `only [x, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `O.sum_mem fun l _ => O.mul_mem (hPv i l) (hXO l k)`.

Establish `hyy : ∀ i j, Formalism.UG.hform s Jv (y i) (y j) = if i = j then inclR (F` using `F) (Fv F v) (δ i) else 0 := by`. Introduce `i j`. Rewrite using `[show Formalism.UG.hform s Jv (y i) (y j) = inclR (F := F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (Z0 i) (Z0 j)) from hform_inclR _ σ J _ _]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Both sides reduce to the same expression. Rewrite using `[hPo i j h, map_zero]`. Establish `hXX : ∀ l m, Formalism.UG.hform s Jv (X l) (X m) = inclR (F` using `F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (X0 l) (X0 m)) := by`. Introduce `l m`. Conclude with `congrFun (congrFun hgram l) m`.

Establish `hxx : ∀ i j, Formalism.UG.hform s Jv (x i) (x j) = if i = j then inclR (F` using `F) (Fv F v) (δ i) else 0 := by`. Introduce `i j`. Establish `e1 : Formalism.UG.hform s Jv (x i) (x j) = inclR (F` using `F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (Z0 i) (Z0 j)) := by`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [x]`.

Rewrite using `[hform_sum_left]`. Repeatedly rewrite using `[hform_sum_right, hXX, s, sigR_inclR']`. Use `_ = _ := by`. Rewrite using `[hZ0e i, hZ0e j, hform_sum_left]`. Repeatedly rewrite using `[hform_sum_right]`.

Simplify using `only [map_sum, map_mul]`. Both sides reduce to the same expression. Rewrite using `[e1]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Both sides reduce to the same expression. Rewrite using `[hPo i j h, map_zero]`. Take `⟨g, hg, hgO, hgiO, hgy⟩` from `hA (Fv F v ⊗[F] E) s O hs hsO n Jv Jv' hJvh hJJ hJv hJiv a (fun i => inclR (F := F) (Fv F v) (δ i)) (fun i => inclR (F := F) (Fv F v) (δ i)⁻¹) hδv hδiv (fun i => by rw [← map_mul, mul_inv_cancel₀ (hPd i), map_one]) hlam x y hxO hZv hxx hyy`. Use `⟨(⟨g, hg⟩ : HR (Fv F v) σ J), ?_, ?_⟩` and prove the remaining obligations. Use `show ∀ w, w ∈ latLoc (E := E) v (L : Set (Fin n → E)) ↔ (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ w ∈ latLoc (E := E) v (L : Set (Fin n → E))`.

Rewrite using `[hstd]`. Introduce `w`. Prove the components needed by the constructor for the conclusion. Introduce `hw`. Conclude with `mem_std_of_oev v _ fun i => mulVec_mem O _ hgO w (fun k => mem_oev_of_std v w hw k) i`.

Introduce `hw`. Establish `e : w = ((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ ((g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ w)`. Rewrite using `[mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]`. Rewrite using `[e]`. Conclude with `mem_std_of_oev v _ fun i => mulVec_mem O _ hgiO _ (fun k => mem_oev_of_std v _ hw k) i`.

Use function extensionality and compare the values at `c show (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ ratTup (F := F) (Fv F v) X0 c = X c`. Establish `e1 : ratTup (F` using `F) (Fv F v) X0 c = ∑ l, inclR (F := F) (Fv F v) (Q c l) • y l := by`. Use function extensionality and compare the values at `k`. Simplify using `only [ratTup, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, y]`. Rewrite using `[hX0e c]`.

Simplify using `[Finset.sum_apply, map_sum, map_mul]`. Rewrite using `[e1, mulVec_sum]`. Repeatedly rewrite using `[mulVec_smul, hgy]`. Use function extensionality and compare the values at `k`. Simplify using `only [x, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Establish `hm : ∀ m, ∑ l, inclR (F` using `F) (Fv F v) (Q c l) * (inclR (F := F) (Fv F v) (P l m) * X m k) = (if c = m then 1 else 0) * X m k := by`. Introduce `m`. Repeatedly rewrite using `[← mul_assoc, ← Finset.sum_mul, ← map_mul, ← map_sum]`. Rewrite using `[← Matrix.mul_apply, hQP, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Repeatedly rewrite using `[hm]`. Simplify using the standard rewrite rules.
-/
theorem intWittAE_of (hA : AlgWitt) (hD : HermDiag) (hL : LamAE) : LocSBPf.IntWittAE := by
  intro F E _ _ _ _ _ σ n J a X0 Λ hCM hJ hT hLat d b
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨L, hLL, rfl⟩ := hLat
  have hσ : ∀ z, σ (σ z) = z := PI.VolStabS.sigma_invol σ hCM.2.2.2
  have hJh : Formalism.UG.IsHerm (σ : E →+* E) J := by
    unfold Formalism.UG.IsHerm Formalism.UG.cT
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply]
    exact hJ.1 i j
  obtain ⟨P, Q, hQP, hPo, hPd⟩ := hD E (σ : E →+* E) hσ two_ne_zero n J hJh a X0 hT
  set Z0 : Fin a → Fin n → E := fun i => ∑ l, P i l • X0 l with hZ0
  have hZ0e : ∀ i, Z0 i = ∑ l, P i l • X0 l := fun i => rfl
  have hX0e : ∀ c, X0 c = ∑ l, Q c l • Z0 l := fun c => by
    funext k
    simp only [hZ0, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hm : ∀ m, ∑ l, Q c l * (P l m * X0 m k) = (if c = m then 1 else 0) * X0 m k := by
      intro m
      simp_rw [← mul_assoc, ← Finset.sum_mul]
      rw [← Matrix.mul_apply, hQP, Matrix.one_apply]
    simp_rw [hm]
    simp
  let δ : Fin a → E := fun i => Formalism.UG.hform (σ : E →+* E) J (Z0 i) (Z0 i)
  have hδσ : ∀ i, σ (δ i) = δ i := fun i => hform_conj (σ : E →+* E) J hσ hJh _ _
  have hJi : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J (isUnit_iff_ne_zero.2 hJ.2)
  filter_upwards [ev_latLoc_std L hLL,
    eventually_all.2 fun k => ev_oev (F := F) (b k),
    eventually_all.2 fun i => eventually_all.2 fun j => ev_oev (F := F) (J i j),
    eventually_all.2 fun i => eventually_all.2 fun j => ev_oev (F := F) (J⁻¹ i j),
    eventually_all.2 fun i => ev_oev (F := F) (δ i),
    eventually_all.2 fun i => ev_oev (F := F) (δ i)⁻¹,
    eventually_all.2 fun i => eventually_all.2 fun j => ev_oev (F := F) (P i j),
    eventually_all.2 fun i => eventually_all.2 fun j => ev_oev (F := F) (Z0 i j),
    eventually_all.2 fun i => hL F E σ hCM (δ i) (hδσ i) (hPd i)]
    with v hstd hbv hJv hJiv hδv hδiv hPv hZv hlam
  intro X hX hgram
  let O := oevRing (E := E) v
  have hXO : ∀ c k, X c k ∈ O := by
    intro c k
    show X c k ∈ OEv (E := E) v
    rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr (X c k)]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [Algebra.TensorProduct.basis_apply]
    exact oev_smul' v (hX c k l) (hbv l)
  let s := sigR (Fv F v) σ
  have hs : ∀ z, s (s z) = z := PI.VolStabS.sigR_invol (Fv F v) σ hσ
  have hsO : ∀ z ∈ O, s z ∈ O := by
    intro z hz
    exact oev_sigR v σ hz
  let Jv := JR (F := F) (Fv F v) J
  let Jv' := JR (F := F) (Fv F v) J⁻¹
  have hJJ : Jv' * Jv = 1 := by
    show J⁻¹.map (inclR (F := F) (Fv F v)) * J.map (inclR (F := F) (Fv F v)) = 1
    rw [← Matrix.map_mul, hJi, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJvh : Formalism.UG.IsHerm s Jv := by
    unfold Formalism.UG.IsHerm Formalism.UG.cT
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Jv, JR, s, sigR_inclR']
    rw [hJ.1 i j]
  let y : Fin a → Fin n → Fv F v ⊗[F] E := fun i k => inclR (F := F) (Fv F v) (Z0 i k)
  let x : Fin a → Fin n → Fv F v ⊗[F] E := fun i => ∑ l, inclR (F := F) (Fv F v) (P i l) • X l
  have hxO : ∀ i k, x i k ∈ O := by
    intro i k
    simp only [x, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact O.sum_mem fun l _ => O.mul_mem (hPv i l) (hXO l k)
  have hyy : ∀ i j, Formalism.UG.hform s Jv (y i) (y j) = if i = j then inclR (F := F) (Fv F v) (δ i) else 0 := by
    intro i j
    rw [show Formalism.UG.hform s Jv (y i) (y j) = inclR (F := F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (Z0 i) (Z0 j)) from
      hform_inclR _ σ J _ _]
    split_ifs with h
    · subst h; rfl
    · rw [hPo i j h, map_zero]
  have hXX : ∀ l m, Formalism.UG.hform s Jv (X l) (X m) =
      inclR (F := F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (X0 l) (X0 m)) := by
    intro l m
    exact congrFun (congrFun hgram l) m
  have hxx : ∀ i j, Formalism.UG.hform s Jv (x i) (x j) = if i = j then inclR (F := F) (Fv F v) (δ i) else 0 := by
    intro i j
    have e1 : Formalism.UG.hform s Jv (x i) (x j) = inclR (F := F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (Z0 i) (Z0 j)) := by
      calc Formalism.UG.hform s Jv (x i) (x j)
          = ∑ l, inclR (F := F) (Fv F v) (σ (P i l)) * ∑ m, inclR (F := F) (Fv F v) (P j m) *
              inclR (F := F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (X0 l) (X0 m)) := by
            simp only [x]
            rw [hform_sum_left]
            simp_rw [hform_sum_right, hXX, s, sigR_inclR']
        _ = _ := by
            rw [hZ0e i, hZ0e j, hform_sum_left]
            simp_rw [hform_sum_right]
            simp only [map_sum, map_mul]
            rfl
    rw [e1]
    split_ifs with h
    · subst h; rfl
    · rw [hPo i j h, map_zero]
  obtain ⟨g, hg, hgO, hgiO, hgy⟩ := hA (Fv F v ⊗[F] E) s O hs hsO n Jv Jv' hJvh hJJ hJv hJiv a
    (fun i => inclR (F := F) (Fv F v) (δ i)) (fun i => inclR (F := F) (Fv F v) (δ i)⁻¹) hδv hδiv
    (fun i => by rw [← map_mul, mul_inv_cancel₀ (hPd i), map_one])
    hlam x y hxO hZv hxx hyy
  refine ⟨(⟨g, hg⟩ : HR (Fv F v) σ J), ?_, ?_⟩
  · show ∀ w, w ∈ latLoc (E := E) v (L : Set (Fin n → E)) ↔
      (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ w ∈ latLoc (E := E) v (L : Set (Fin n → E))
    rw [hstd]
    intro w
    constructor
    · intro hw
      exact mem_std_of_oev v _ fun i => mulVec_mem O _ hgO w (fun k => mem_oev_of_std v w hw k) i
    · intro hw
      have e : w = ((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ
          ((g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ w) := by
        rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
      rw [e]
      exact mem_std_of_oev v _ fun i => mulVec_mem O _ hgiO _ (fun k => mem_oev_of_std v _ hw k) i
  · funext c
    show (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ ratTup (F := F) (Fv F v) X0 c = X c
    have e1 : ratTup (F := F) (Fv F v) X0 c = ∑ l, inclR (F := F) (Fv F v) (Q c l) • y l := by
      funext k
      simp only [ratTup, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, y]
      rw [hX0e c]
      simp [Finset.sum_apply, map_sum, map_mul]
    rw [e1, mulVec_sum]
    simp_rw [mulVec_smul, hgy]
    funext k
    simp only [x, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hm : ∀ m, ∑ l, inclR (F := F) (Fv F v) (Q c l) * (inclR (F := F) (Fv F v) (P l m) * X m k) =
        (if c = m then 1 else 0) * X m k := by
      intro m
      simp_rw [← mul_assoc, ← Finset.sum_mul, ← map_mul, ← map_sum]
      rw [← Matrix.mul_apply, hQP, Matrix.one_apply]
      split_ifs <;> simp
    simp_rw [hm]
    simp

end Main

/- English proof (translation)
The claim follows from `intWittAE_of IntWittAlg.algWitt IntWittAlg.hermDiag lamAE`.
-/
theorem integral_witt_almost_everywhere : Formalism.L2.SG.Pf.NcS.LocSBPf.IntWittAE :=
  intWittAE_of IntWittAlg.algWitt IntWittAlg.hermDiag lamAE

end Formalism.L2.SG.Pf.NcS.IntWittPf
