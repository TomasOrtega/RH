import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRho
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRedKer

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.AllRowsRhoX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
  Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.AllRowsRho
  Formalism.L2.SG.AllRowsOf Formalism.MainNotions.ArithmeticCylinders

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Rewrite using `[← X.n_eq]`. Conclude with `exists_redBasis (I := X.B.I) (w := wB X (D.naut.plGw kv.1 kv.2)) (hp := D.host.g_prime kv.1) (hcard := by rw [card_wB, card_res_host])`.
-/
theorem exists_b (kv : Σ k : Fin 2, D.nd.PlG k) :
    ∃ b : Fin D.R.r → Fin X.B.I.n → X.B.I.E, IsRedBasis0 X.B.I (wB X (D.naut.plGw kv.1 kv.2)) b := by
  rw [← X.n_eq]
  exact exists_redBasis (I := X.B.I) (w := wB X (D.naut.plGw kv.1 kv.2)) (hp := D.host.g_prime kv.1)
    (hcard := by rw [card_wB, card_res_host])

def redBX (kv : Σ k : Fin 2, D.nd.PlG k) : RedB X.B.I D.R.r where
  w := wB X (D.naut.plGw kv.1 kv.2)
  p := D.host.g kv.1
  hp := D.host.g_prime kv.1
  hcard := by rw [card_wB, card_res_host]
  hm := X.n_eq.symm
  b := Classical.choose (exists_b X kv)
  hb := Classical.choose_spec (exists_b X kv)

def rhoX : KSub X.B.I →* G0g D.nd := MonoidHom.pi fun kv => rhoB (redBX X kv)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rhoX_apply (x : KSub X.B.I) (kv : Σ k : Fin 2, D.nd.PlG k) : rhoX X x kv = rhoB (redBX X kv) x := rfl

/- English proof (translation)
Introduce `kv`. Conclude with `(redMat_iff X _ _ _ _).mpr (redMat0_of (I := X.B.I) (hb := (redBX X kv).hb) (h := rhoB_spec (redBX X kv) x))`.
-/
theorem goodAt_rhoX (x : KSub X.B.I) : GoodAt X x (rhoX X x) := by
  intro kv
  exact (redMat_iff X _ _ _ _).mpr (redMat0_of (I := X.B.I) (hb := (redBX X kv).hb) (h := rhoB_spec (redBX X kv) x))

/- English proof (translation)
Establish `hc : Nat.card (𝓞 X.B.I.E ⧸ (wB X (D.naut.plGw kv.1 kv.2)).asIdeal) = D.host.g kv.1` using `(redBX X kv).hcard`. Establish `h0 : ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E ⧸ (wB X (D.naut.plGw kv.1 kv.2)).asIdeal) = 0`. Establish `h1` using `card_nsmul_eq_zero' (G := 𝓞 X.B.I.E ⧸ (wB X (D.naut.plGw kv.1 kv.2)).asIdeal) (x := 1)`. Rewrite `h1` using `[hc]`. Simplify using `using h1`.

Establish `hk : ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E) ∈ (wB X (D.naut.plGw kv.1 kv.2)).asIdeal`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `h0`. Establish `key : ∀ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ (wB X (D.naut.plGw kv.1 kv.2)).asIdeal → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 X.B.I.E) ∈ (wB X (D.naut.plGw kv.1 kv.2)).asIdeal`. Introduce `k hk'`.

Use `fin_cases k`. Simplify `Ideal.mul_mem_right _ _ hk'` using `[Nat.cast_mul]`. Simplify `Ideal.mul_mem_left _ _ hk'` using `[Nat.cast_mul]`. Rewrite using `[X.g_eq]`. Conclude with `key kv.1 hk`.
-/
theorem level_mem_wB (kv : Σ k : Fin 2, D.nd.PlG k) :
    ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ (wB X (D.naut.plGw kv.1 kv.2)).asIdeal := by
  have hc : Nat.card (𝓞 X.B.I.E ⧸ (wB X (D.naut.plGw kv.1 kv.2)).asIdeal) = D.host.g kv.1 :=
    (redBX X kv).hcard
  have h0 : ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E ⧸ (wB X (D.naut.plGw kv.1 kv.2)).asIdeal) = 0 := by
    have h1 := card_nsmul_eq_zero' (G := 𝓞 X.B.I.E ⧸ (wB X (D.naut.plGw kv.1 kv.2)).asIdeal) (x := 1)
    rw [hc] at h1
    simpa using h1
  have hk : ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E) ∈ (wB X (D.naut.plGw kv.1 kv.2)).asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact h0
  have key : ∀ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ (wB X (D.naut.plGw kv.1 kv.2)).asIdeal →
      ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 X.B.I.E) ∈ (wB X (D.naut.plGw kv.1 kv.2)).asIdeal := by
    intro k hk'
    fin_cases k
    · simpa [Nat.cast_mul] using Ideal.mul_mem_right _ _ hk'
    · simpa [Nat.cast_mul] using Ideal.mul_mem_left _ _ hk'
  rw [X.g_eq]
  exact key kv.1 hk

/- English proof (translation)
Use `haveI : Fact (1 < R.p) := ⟨R.hp.one_lt⟩`. Introduce `i`. Establish `hsum : ∑ j, ((((1 : Matrix (Fin m) (Fin m) (ZMod R.p)) j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (R.b j) = iv I (R.b i)`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[Matrix.one_apply_eq, ZMod.val_one]`.

Introduce `j _ hj`. Simplify using `[Matrix.one_apply_ne hj]`. Introduce `hi`. Conclude with `absurd (Finset.mem_univ i) hi`. Rewrite using `[hsum]`.

Conclude with `h i`.
-/
theorem redMatB_one_of {I : AutInst} {m : ℕ} (R : RedB I m) {x : I.Gf}
    (h : ∀ i, I.fmat x *ᵥ iv I (R.b i) - iv I (R.b i) ∈ Lq I R.w) :
    RedMatB I R.w R.p R.b x (1 : Matrix (Fin m) (Fin m) (ZMod R.p)) := by
  haveI : Fact (1 < R.p) := ⟨R.hp.one_lt⟩
  intro i
  have hsum : ∑ j, ((((1 : Matrix (Fin m) (Fin m) (ZMod R.p)) j i).val : ℕ) : I.E ⊗[I.F] Af I.F) •
      iv I (R.b j) = iv I (R.b i) := by
    rw [Finset.sum_eq_single i]
    · simp [Matrix.one_apply_eq, ZMod.val_one]
    · intro j _ hj
      simp [Matrix.one_apply_ne hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hsum]
  exact h i

/- English proof (translation)
Establish `hRK : Formalism.L2.SG.AllRowsOf.RedKer X` using `Formalism.L2.SG.AllRowsOf.redKer_of (X := X) (Formalism.L2.SG.AllRowsOf.redKerOne_of (X := X) (Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X 0) (Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X 1))`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1` using `goodAt_rhoX X x`. Rewrite `h1` using `[h]`.

Conclude with `(hRK x x.2).1 h1`. Introduce `hx`. Establish `hK : (x : X.B.I.Gf) ∈ X.B.I.Kset` using `x.2`. Establish `hG` using `Formalism.L2.SG.AllRowsOf.goodAt_one_of_mem_Kg (X := X) hx`. Use function extensionality and compare the values at `kv`.

Rewrite using `[rhoX_apply]`. Apply `Units.ext` to reduce the goal to its premises. Establish `hR0` using `(redMat_iff X _ _ _ _).mp (hG kv)`. Establish `hR1` using `hR0`. Simplify using `only [Pi.one_apply, Units.val_one] at hR1`.

Establish `hA` using `Formalism.L2.SG.Pf.AllRowsRedKerA.stepA (I := X.B.I) (redBX X kv).hp (redBX X kv).hcard hK hR1`. Establish `hB : RedMatB X.B.I (redBX X kv).w (redBX X kv).p (redBX X kv).b x 1` using `redMatB_one_of (redBX X kv) fun i => by`. Establish `h1` using `hA _ (PIW.AdelClassFin.DictLat.iv_mem X.B.I ((redBX X kv).hb.1 i))`. Rewrite `h1` using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Then use the resulting hypothesis. Establish `h2` using `matB_eq (redBX X kv) hK hB`.

Use `show ((rhoB (redBX X kv) x : GL (Fin D.R.r) (ZMod (redBX X kv).p)) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (redBX X kv).p)) = ((1 : GL (Fin D.R.r) (ZMod (redBX X kv).p)) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (redBX X kv).p))`. Rewrite using `[Units.val_one]`. Conclude with `h2`.
-/
theorem rhoX_eq_one_iff (x : KSub X.B.I) : rhoX X x = 1 ↔ (x : X.B.I.Gf) ∈ X.B.I.Kg X.B.g := by
  have hRK : Formalism.L2.SG.AllRowsOf.RedKer X :=
    Formalism.L2.SG.AllRowsOf.redKer_of (X := X) (Formalism.L2.SG.AllRowsOf.redKerOne_of (X := X)
      (Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X 0) (Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X 1))
  constructor
  · intro h
    have h1 := goodAt_rhoX X x
    rw [h] at h1
    exact (hRK x x.2).1 h1
  · intro hx
    have hK : (x : X.B.I.Gf) ∈ X.B.I.Kset := x.2
    have hG := Formalism.L2.SG.AllRowsOf.goodAt_one_of_mem_Kg (X := X) hx
    funext kv
    rw [rhoX_apply]
    apply Units.ext
    have hR0 := (redMat_iff X _ _ _ _).mp (hG kv)
    have hR1 := hR0
    simp only [Pi.one_apply, Units.val_one] at hR1
    have hA := Formalism.L2.SG.Pf.AllRowsRedKerA.stepA (I := X.B.I) (redBX X kv).hp (redBX X kv).hcard hK hR1
    have hB : RedMatB X.B.I (redBX X kv).w (redBX X kv).p (redBX X kv).b x 1 :=
      redMatB_one_of (redBX X kv) fun i => by
        have h1 := hA _ (PIW.AdelClassFin.DictLat.iv_mem X.B.I ((redBX X kv).hb.1 i))
        rwa [Matrix.sub_mulVec, Matrix.one_mulVec] at h1
    have h2 := matB_eq (redBX X kv) hK hB
    show ((rhoB (redBX X kv) x : GL (Fin D.R.r) (ZMod (redBX X kv).p)) :
        Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (redBX X kv).p)) =
      ((1 : GL (Fin D.R.r) (ZMod (redBX X kv).p)) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (redBX X kv).p))
    rw [Units.val_one]
    exact h2

/- English proof (translation)
Unfold `ES`. Simplify using `only [Finsupp.coe_equivFunOnFinite_symm]`. Use `finsum_congr fun a => ?_` and prove the remaining obligations. Use `split_ifs`. Use `Finset.prod_congr rfl fun kv _ => ?_` and prove the remaining obligations.

Conclude with `coeff_conj_of_central (D.ntypes.eSer_central kv.1 _) (γ kv) (P kv)`. Both sides reduce to the same expression.
-/
theorem ES_conj (S : Set (Tup2 D)) (γ P : G0g D.nd) : (ES S).coeff (P⁻¹ * γ * P) = (ES S).coeff γ := by
  unfold ES
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  refine finsum_congr fun a => ?_
  split_ifs
  · refine Finset.prod_congr rfl fun kv _ => ?_
    exact coeff_conj_of_central (D.ntypes.eSer_central kv.1 _) (γ kv) (P kv)
  · rfl

/- English proof (translation)
Establish `h : (x : X.B.I.Gf) ∈ X.B.I.Kset ∧ ∃ γ : G0g D.nd, GoodAt X x γ` using `⟨x.2, rhoX X x, goodAt_rhoX X x⟩`. Unfold `egA`. Rewrite using `[dif_pos h]`. Use `congr 1`. Establish `hγ` using `Classical.choose_spec h.2`.

Establish `hP : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ∃ P : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), (Classical.choose h.2) kv = P⁻¹ * rhoX X x kv * P`. Introduce `kv`. Establish `h1` using `(redMat_iff X _ _ _ _).mp (goodAt_rhoX X x kv)`. Establish `h2` using `(redMat_iff X _ _ _ _).mp (hγ kv)`. Conclude with `Formalism.L2.SG.Pf.RedConj0Pf.reduction_conjugacy X.B.I _ _ (redBX X kv).hp (redBX X kv).hcard D.R.r (redBX X kv).hm x _ _ h1 h2`.

Use `choose P hP using hP`. Establish `e1 : Classical.choose h.2 = P⁻¹ * rhoX X x * P`. Use function extensionality and compare the values at `kv`. Rewrite using `[hP kv]`. Both sides reduce to the same expression.

Rewrite using `[e1, ha]`.
-/
theorem egA_rhoX (a : MonoidAlgebra ℂ (G0g D.nd)) (ha : ∀ γ P : G0g D.nd, a.coeff (P⁻¹ * γ * P) = a.coeff γ)
    (x : KSub X.B.I) : egA X a x = a.coeff (rhoX X x) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) := by
  have h : (x : X.B.I.Gf) ∈ X.B.I.Kset ∧ ∃ γ : G0g D.nd, GoodAt X x γ :=
    ⟨x.2, rhoX X x, goodAt_rhoX X x⟩
  unfold egA
  rw [dif_pos h]
  congr 1
  have hγ := Classical.choose_spec h.2
  have hP : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ∃ P : GL (Fin D.R.r) (ZMod (D.host.g kv.1)),
      (Classical.choose h.2) kv = P⁻¹ * rhoX X x kv * P := by
    intro kv
    have h1 := (redMat_iff X _ _ _ _).mp (goodAt_rhoX X x kv)
    have h2 := (redMat_iff X _ _ _ _).mp (hγ kv)
    exact Formalism.L2.SG.Pf.RedConj0Pf.reduction_conjugacy X.B.I _ _ (redBX X kv).hp (redBX X kv).hcard D.R.r
      (redBX X kv).hm x _ _ h1 h2
  choose P hP using hP
  have e1 : Classical.choose h.2 = P⁻¹ * rhoX X x * P := by
    funext kv
    rw [hP kv]
    rfl
  rw [e1, ha]

def RhoSurj : Prop := ∀ (D : D7) (X : HidaSetting D), Function.Surjective (rhoX X)

end Formalism.L2.SG.Pf.AllRowsRhoX
