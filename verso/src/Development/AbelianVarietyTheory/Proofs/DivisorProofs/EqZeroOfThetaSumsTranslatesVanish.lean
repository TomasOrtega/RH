import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpSumCoeffEqZeroOfVanishing

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ThetaSep
variable (F : Type) [Field F] [NumberField F]

def arch (s : mixedEmbedding.mixedSpace F) : AF F := ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm s, 0)

def fstH : AF F →+* InfiniteAdeleRing F := RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

def sndH : AF F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

def evH : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (fstH F)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evI_eq (a : AF F) : evI F a = evH F a := rfl

/- English proof (translation)
Introduce `u hu`. Establish `h1 : fstH F u = 0` using `(InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)`. Rewrite using `[smul_eq_mul]`. Conclude with `Prod.ext (show fstH F (u * a) = 0 by rw [map_mul, h1, zero_mul]) (show sndH F (u * a) = 0 by rw [map_mul, ha, mul_zero])`.
-/
theorem at_of_snd {a : AF F} (ha : sndH F a = 0) : At (evI F) a := by
  intro u hu
  have h1 : fstH F u = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  rw [smul_eq_mul]
  exact Prod.ext (show fstH F (u * a) = 0 by rw [map_mul, h1, zero_mul])
    (show sndH F (u * a) = 0 by rw [map_mul, ha, mul_zero])

/- English proof (translation)
Rewrite using `[InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]`. Both sides reduce to the same expression.
-/
theorem evH_algebraMap (x : F) : evH F (algebraMap F (AF F) x) = mixedEmbedding F x := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]; rfl

/- English proof (translation)
The claim follows from `(InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply s`.
-/
theorem evH_arch (s : mixedEmbedding.mixedSpace F) : evH F (arch F s) = s :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply s

/- English proof (translation)
Simplify using `only [dotProduct, map_sum, map_mul]`. Conclude with `Finset.sum_eq_zero fun i _ => by rw [show sndH F (arch F (s i)) = 0 from rfl, mul_zero]`.
-/
theorem snd_dot {κ : Type} [Fintype κ] (ξ : κ → F) (s : κ → mixedEmbedding.mixedSpace F) :
    sndH F ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ (fun i => arch F (s i))) = 0 := by
  simp only [dotProduct, map_sum, map_mul]
  exact Finset.sum_eq_zero fun i _ => by rw [show sndH F (arch F (s i)) = 0 from rfl, mul_zero]

/- English proof (translation)
Simplify using `only [dotProduct, map_sum, map_mul, evH_algebraMap, evH_arch]`.
-/
theorem evH_dot {κ : Type} [Fintype κ] (ξ : κ → F) (s : κ → mixedEmbedding.mixedSpace F) :
    evH F ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ (fun i => arch F (s i))) = ∑ i, mixedEmbedding F (ξ i) * s i := by
  simp only [dotProduct, map_sum, map_mul, evH_algebraMap, evH_arch]

/- English proof (translation)
Rewrite using `[show (1 : mixedEmbedding.mixedSpace F) = algebraMap ℝ _ 1 from (map_one _).symm, Algebra.trace_algebraMap, mixedEmbedding.finrank]`. Simplify using `[Module.finrank_pos.ne']`.
-/
theorem trace_one_ne : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) 1 ≠ 0 := by
  rw [show (1 : mixedEmbedding.mixedSpace F) = algebraMap ℝ _ 1 from (map_one _).symm, Algebra.trace_algebraMap,
    mixedEmbedding.finrank]
  simp [Module.finrank_pos.ne']

def trA : F →+ ℝ :=
  (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).toAddMonoidHom.comp (mixedEmbedding F).toAddMonoidHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem trA_apply (z : F) : trA F z = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (mixedEmbedding F z) := rfl

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hz : ∀ z : F, trA F (d * z) = 0`. Introduce `z`. Rewrite using `[← b.sum_repr z, Finset.mul_sum, map_sum]`. Conclude with `Finset.sum_eq_zero fun k _ => by rw [mul_smul_comm, map_rat_smul, hd, smul_zero]`.

Establish `h1` using `hz d⁻¹`. Rewrite `h1` using `[mul_inv_cancel₀ hne, trA_apply, map_one]`. Conclude with `trace_one_ne F h1`.
-/
theorem eq_zero_of_trA {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ F) (d : F) (hd : ∀ k, trA F (d * b k) = 0) :
    d = 0 := by
  by_contra hne
  have hz : ∀ z : F, trA F (d * z) = 0 := by
    intro z
    rw [← b.sum_repr z, Finset.mul_sum, map_sum]
    exact Finset.sum_eq_zero fun k _ => by rw [mul_smul_comm, map_rat_smul, hd, smul_zero]
  have h1 := hz d⁻¹
  rw [mul_inv_cancel₀ hne, trA_apply, map_one] at h1
  exact trace_one_ne F h1

/- English proof (translation)
Rewrite using `[← e.sum_comp, Fintype.sum_prod_type, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, LinearMap.map_smul, smul_eq_mul, ← map_mul, Equiv.symm_apply_apply, trA_apply, mul_comm]`.
-/
theorem trace_sum {κ ι : Type} [Fintype κ] [Fintype ι] {N : ℕ} (e : κ × ι ≃ Fin N) (b : ι → F) (ξ : κ → F)
    (t : Fin N → ℝ) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, mixedEmbedding F (ξ i) * ∑ k, t (e (i, k)) • mixedEmbedding F (b k)) =
      ∑ j, trA F (ξ (e.symm j).1 * b (e.symm j).2) * t j := by
  rw [← e.sum_comp, Fintype.sum_prod_type, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, LinearMap.map_smul, smul_eq_mul, ← map_mul, Equiv.symm_apply_apply, trA_apply, mul_comm]

/- English proof (translation)
Introduce `F _ _ ψ hψ κ _ h hh hθ`. Use function extensionality and compare the values at `x`. Set `b` to `Module.finBasis ℚ F`. Set `e` to `Fintype.equivFin (κ × Fin (Module.finrank ℚ F))`. Set `lam : (κ → F) → Fin (Fintype.card (κ × Fin (Module.finrank ℚ F))) → ℝ` to `fun ξ j => -trA F (ξ (e.symm j).1 * b (e.symm j).2)`.

Set `c : (κ → F) → ℂ` to `fun ξ => h ((fun i => algebraMap F (AF F) (ξ i)) + x)`. Establish `hc : Summable c`. Establish `hs` using `summable_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F x hh)`. Conclude with `hs`. Establish `hinj : Function.Injective lam`.

Introduce `ξ ξ' hl`. Use function extensionality and compare the values at `i`. Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_trA F b _ fun k => ?_` and prove the remaining obligations. Use `congrFun hl (e (i, k))` as an intermediate fact.

Simplify using `only [lam, Equiv.symm_apply_apply, neg_inj] at this`. Rewrite using `[sub_mul, map_sub, this, sub_self]`. Establish `hsum : ∀ t : Fin (Fintype.card (κ × Fin (Module.finrank ℚ F))) → ℝ, ∑' ξ, c ξ * Complex.exp (2 * Real.pi * Complex.I * ∑ j, (lam ξ j : ℂ) * (t j : ℂ)) = 0`. Introduce `t`. Set `s : κ → mixedEmbedding.mixedSpace F` to `fun i => ∑ k, t (e (i, k)) • mixedEmbedding F (b k)`.

Set `y : κ → AF F` to `fun i => arch F (s i)`. Establish `hψ0 : ψ (⅟(2 : AF F) * (x ⬝ᵥ y)) ≠ 0`. Establish `h2` using `AddChar.map_add_eq_mul ψ (⅟(2 : AF F) * (x ⬝ᵥ y)) (-(⅟(2 : AF F) * (x ⬝ᵥ y)))`. Rewrite `h2` using `[add_neg_cancel, AddChar.map_zero_eq_one]`. Conclude with `left_ne_zero_of_mul_eq_one h2.symm`.

Establish `key : ∀ ξ : κ → F, schr ψ (x, y) h (fun i => algebraMap F (AF F) (ξ i)) = ψ (⅟(2 : AF F) * (x ⬝ᵥ y)) * (c ξ * Complex.exp (2 * Real.pi * Complex.I * ∑ j, (lam ξ j : ℂ) * (t j : ℂ)))`. Introduce `ξ`. Simplify using `only [schr]`. Rewrite using `[AddChar.map_add_eq_mul, hψ.2.2 _ (at_of_snd F (snd_dot F ξ s)), evI_eq, evH_dot, trace_sum F e b ξ t]`. Establish `harg : -(2 * Real.pi * Complex.I) * ((∑ j, trA F (ξ (e.symm j).1 * b (e.symm j).2) * t j : ℝ) : ℂ) = 2 * Real.pi * Complex.I * ∑ j, (lam ξ j : ℂ) * (t j : ℂ)`.

Simplify using `only [lam, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_neg, neg_mul, Finset.sum_neg_distrib]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[harg]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : thetaSum F (schr ψ (x, y) h) = ψ (⅟(2 : AF F) * (x ⬝ᵥ y)) * ∑' ξ, c ξ * Complex.exp (2 * Real.pi * Complex.I * ∑ j, (lam ξ j : ℂ) * (t j : ℂ))`.

Unfold `thetaSum`. Rewrite using `[← tsum_mul_left]`. Conclude with `tsum_congr key`. Establish `h0` using `hθ x y`. Rewrite `h0` using `[h1]`.

Conclude with `(mul_eq_zero.1 h0).resolve_left hψ0`. Use `GlobalTheory.ExpSumUniq.coeff_eq_zero _ _ lam c hinj hc hsum 0` as an intermediate fact. Establish `e0 : (fun i : κ => algebraMap F (AF F) ((0 : κ → F) i)) + x = x` using `by funext i; simp`. Simplify using `only [c] at this`. Rewrite `this` using `[e0]`.

Conclude with `this`.
-/
theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (h : (κ → AF F) → ℂ), h ∈ schA F κ → (∀ x y : κ → AF F, thetaSum F (schr ψ (x, y) h) = 0) → h = 0 := by
  intro F _ _ ψ hψ κ _ h hh hθ
  funext x
  classical
  let b := Module.finBasis ℚ F
  let e := Fintype.equivFin (κ × Fin (Module.finrank ℚ F))
  let lam : (κ → F) → Fin (Fintype.card (κ × Fin (Module.finrank ℚ F))) → ℝ :=
    fun ξ j => -trA F (ξ (e.symm j).1 * b (e.symm j).2)
  let c : (κ → F) → ℂ := fun ξ => h ((fun i => algebraMap F (AF F) (ξ i)) + x)
  have hc : Summable c := by
    have hs := summable_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F x hh)
    exact hs
  have hinj : Function.Injective lam := by
    intro ξ ξ' hl
    funext i
    rw [← sub_eq_zero]
    refine eq_zero_of_trA F b _ fun k => ?_
    have := congrFun hl (e (i, k))
    simp only [lam, Equiv.symm_apply_apply, neg_inj] at this
    rw [sub_mul, map_sub, this, sub_self]
  have hsum : ∀ t : Fin (Fintype.card (κ × Fin (Module.finrank ℚ F))) → ℝ,
      ∑' ξ, c ξ * Complex.exp (2 * Real.pi * Complex.I * ∑ j, (lam ξ j : ℂ) * (t j : ℂ)) = 0 := by
    intro t
    let s : κ → mixedEmbedding.mixedSpace F := fun i => ∑ k, t (e (i, k)) • mixedEmbedding F (b k)
    let y : κ → AF F := fun i => arch F (s i)
    have hψ0 : ψ (⅟(2 : AF F) * (x ⬝ᵥ y)) ≠ 0 := by
      have h2 := AddChar.map_add_eq_mul ψ (⅟(2 : AF F) * (x ⬝ᵥ y)) (-(⅟(2 : AF F) * (x ⬝ᵥ y)))
      rw [add_neg_cancel, AddChar.map_zero_eq_one] at h2
      exact left_ne_zero_of_mul_eq_one h2.symm
    have key : ∀ ξ : κ → F, schr ψ (x, y) h (fun i => algebraMap F (AF F) (ξ i)) =
        ψ (⅟(2 : AF F) * (x ⬝ᵥ y)) * (c ξ * Complex.exp (2 * Real.pi * Complex.I * ∑ j, (lam ξ j : ℂ) * (t j : ℂ))) := by
      intro ξ
      simp only [schr]
      rw [AddChar.map_add_eq_mul, hψ.2.2 _ (at_of_snd F (snd_dot F ξ s)), evI_eq, evH_dot, trace_sum F e b ξ t]
      have harg : -(2 * Real.pi * Complex.I) * ((∑ j, trA F (ξ (e.symm j).1 * b (e.symm j).2) * t j : ℝ) : ℂ) =
          2 * Real.pi * Complex.I * ∑ j, (lam ξ j : ℂ) * (t j : ℂ) := by
        simp only [lam, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_neg, neg_mul, Finset.sum_neg_distrib]
        ring
      rw [harg]
      ring
    have h1 : thetaSum F (schr ψ (x, y) h) =
        ψ (⅟(2 : AF F) * (x ⬝ᵥ y)) * ∑' ξ, c ξ * Complex.exp (2 * Real.pi * Complex.I * ∑ j, (lam ξ j : ℂ) * (t j : ℂ)) := by
      unfold thetaSum
      rw [← tsum_mul_left]
      exact tsum_congr key
    have h0 := hθ x y
    rw [h1] at h0
    exact (mul_eq_zero.1 h0).resolve_left hψ0
  have := GlobalTheory.ExpSumUniq.coeff_eq_zero _ _ lam c hinj hc hsum 0
  have e0 : (fun i : κ => algebraMap F (AF F) ((0 : κ → F) i)) + x = x := by funext i; simp
  simp only [c] at this
  rw [e0] at this
  exact this

end GlobalTheory.ThetaSep
