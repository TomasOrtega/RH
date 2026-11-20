import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergDerivativeArchimedeanDirectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open scoped Classical

noncomputable section

open IsDedekindDomain

namespace GlobalTheory.HeisDerivFormula

variable {F : Type} [Field F] [NumberField F]

variable (F) in

def evIHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

/- English proof (translation)
The claim follows from `map_add (evIHom F) a b`.
-/
theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b := map_add (evIHom F) a b

/- English proof (translation)
The claim follows from `map_mul (evIHom F) a b`.
-/
theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b := map_mul (evIHom F) a b

/- English proof (translation)
The claim follows from `RingHom.map_dotProduct (evIHom F) v w`.
-/
theorem evI_dot {κ : Type} [Fintype κ] (v w : κ → AF F) :
    evI F (v ⬝ᵥ w) = (fun i => evI F (v i)) ⬝ᵥ fun i => evI F (w i) :=
  RingHom.map_dotProduct (evIHom F) v w

/- English proof (translation)
Simplify using `[evI, realAd]`.
-/
theorem evI_realAd (t : ℝ) : evI F (realAd F t) = algebraMap ℝ _ t := by simp [evI, realAd]

/- English proof (translation)
Simplify using `[realAd]`.
-/
theorem snd_realAd (t : ℝ) : (realAd F t).2 = 0 := by simp [realAd]

variable (F) in

def ofInf (y : mixedEmbedding.mixedSpace F) : AF F :=
  (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

/- English proof (translation)
Simplify using `[evI, ofInf]`.
-/
theorem evI_ofInf (y : mixedEmbedding.mixedSpace F) : evI F (ofInf F y) = y := by simp [evI, ofInf]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem snd_ofInf (y : mixedEmbedding.mixedSpace F) : (ofInf F y).2 = 0 := rfl

variable (F) in

def rInt (κ : Type) (z : κ → AF F) : ℂ := (GlobalTheory.SchANonzero.intPts F κ).indicator 1 (fun i => (z i).2)

/- English proof (translation)
Unfold `rInt`. Rewrite using `[Set.indicator_of_mem]`. Both sides reduce to the same expression. Introduce `i _ v show (z i).2 v ∈ v.adicCompletionIntegers F`. Rewrite using `[hz i]`.

Use `show (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F`. Conclude with `zero_mem (v.adicCompletionIntegers F)`.
-/
theorem rInt_eq_one {κ : Type} (z : κ → AF F) (hz : ∀ i, (z i).2 = 0) : rInt F κ z = 1 := by
  unfold rInt
  rw [Set.indicator_of_mem]
  · rfl
  · intro i _ v
    show (z i).2 v ∈ v.adicCompletionIntegers F
    rw [hz i]
    show (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
    exact zero_mem (v.adicCompletionIntegers F)

/- English proof (translation)
Use `⟨fun x z hz => ?_, Submodule.subset_span ⟨g, _, GlobalTheory.SchANonzero.indicator_intPts_mem_SB F κ, rfl⟩⟩` and prove the remaining obligations. Establish `h2 : ∀ i, (z i).2 = 0`. Introduce `i`. Set `c : AF F` to `((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))`. Establish `hc : evI F c = 0` using `map_zero _`.

Establish `h3 : c * z i = 0` using `congrFun (hz c hc) i`. Establish `h4` using `congrArg Prod.snd h3`. Conclude with `(one_mul _).symm.trans h4`. Unfold `rInt`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Use `show (x i).2 + (z i).2 = (x i).2`. Rewrite using `[h2 i, add_zero]`.
-/
theorem rest_rInt {κ : Type} [Fintype κ] (g : SInf F κ) :
    Rest (evI F) (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) (rInt F κ) := by
  refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨g, _, GlobalTheory.SchANonzero.indicator_intPts_mem_SB F κ, rfl⟩⟩
  have h2 : ∀ i, (z i).2 = 0 := by
    intro i
    let c : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))
    have hc : evI F c = 0 := map_zero _
    have h3 : c * z i = 0 := congrFun (hz c hc) i
    have h4 := congrArg Prod.snd h3
    exact (one_mul _).symm.trans h4
  unfold rInt
  congr 1
  funext i
  show (x i).2 + (z i).2 = (x i).2
  rw [h2 i, add_zero]

/- English proof (translation)
Unfold `GlobalTheory.WeilM.schr`. Simplify using `only [Prod.smul_fst, Prod.smul_snd]`. Establish `hp : (fun i => ofInf F (y i)) ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b)) = realAd F t * ((fun i => ofInf F (y i)) ⬝ᵥ b + ⅟(2 : AF F) * (realAd F t * (a ⬝ᵥ b)))`. Simplify using `only [dotProduct_smul, smul_dotProduct, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hAt : At (evI F) (realAd F t * ((fun i => ofInf F (y i)) ⬝ᵥ b + ⅟(2 : AF F) * (realAd F t * (a ⬝ᵥ b))))`. Introduce `c hc`. Establish `hc1 : c.1 = 0` using `(InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hc`. Establish `h0 : c * realAd F t = 0` using `Prod.ext (by show c.1 * (realAd F t).1 = 0; rw [hc1, zero_mul]) (by show c.2 * (realAd F t).2 = 0; rw [snd_realAd, mul_zero])`. Rewrite using `[smul_eq_mul, ← mul_assoc, h0, zero_mul]`.

Establish `hy : (fun i => evI F (ofInf F (y i))) = y` using `funext fun i => evI_ofInf (y i)`. Establish `he : evI F (realAd F t * ((fun i => ofInf F (y i)) ⬝ᵥ b + ⅟(2 : AF F) * (realAd F t * (a ⬝ᵥ b)))) = t • ((y ⬝ᵥ fun i => evI F (b i)) + t • (evI F ⅟(2 : AF F) * ((fun i => evI F (a i)) ⬝ᵥ fun i => evI F (b i))))`. Rewrite using `[evI_mul, evI_add, evI_mul, evI_mul, evI_dot, evI_dot, hy, evI_realAd, Algebra.smul_def, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Establish `htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (realAd F t * ((fun i => ofInf F (y i)) ⬝ᵥ b + ⅟(2 : AF F) * (realAd F t * (a ⬝ᵥ b))))) = t * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ fun i => evI F (b i)) + t ^ 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace …`.

Rewrite using `[he, map_smul, map_add, map_smul, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hg : (fun i => evI F (((fun i => ofInf F (y i)) + realAd F t • a) i)) = y + t • fun i => evI F (a i)`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[evI_add, evI_mul, evI_realAd, evI_ofInf, Algebra.smul_def]`. Establish `hr : rInt F κ ((fun i => ofInf F (y i)) + realAd F t • a) = 1`. Use `rInt_eq_one _ fun i => ?_` and prove the remaining obligations. Use `show (0 : FiniteAdeleRing (𝓞 F) F) + (realAd F t).2 * (a i).2 = 0`. Rewrite using `[snd_realAd, zero_mul, add_zero]`.

Rewrite using `[hp, hψ.2.2 _ hAt, htr]`. Unfold `tens`. Rewrite using `[hg, hr, mul_one]`.
-/
theorem schr_line {κ : Type} [Fintype κ] [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (g : SInf F κ) (a b : κ → AF F) (y : κ → mixedEmbedding.mixedSpace F) (t : ℝ) :
    GlobalTheory.WeilM.schr ψ (realAd F t • (a, b)) (tens (evI F) (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) (rInt F κ))
      (fun i => ofInf F (y i)) =
    Complex.exp (-(2 * Real.pi * Complex.I) *
      ((t * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ fun i => evI F (b i)) +
        t ^ 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (evI F ⅟(2 : AF F) * ((fun i => evI F (a i)) ⬝ᵥ fun i => evI F (b i))) : ℝ) : ℂ)) *
      g (y + t • fun i => evI F (a i)) := by
  unfold GlobalTheory.WeilM.schr
  simp only [Prod.smul_fst, Prod.smul_snd]
  have hp : (fun i => ofInf F (y i)) ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b)) =
      realAd F t * ((fun i => ofInf F (y i)) ⬝ᵥ b + ⅟(2 : AF F) * (realAd F t * (a ⬝ᵥ b))) := by
    simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
  have hAt : At (evI F) (realAd F t * ((fun i => ofInf F (y i)) ⬝ᵥ b + ⅟(2 : AF F) * (realAd F t * (a ⬝ᵥ b)))) := by
    intro c hc
    have hc1 : c.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hc
    have h0 : c * realAd F t = 0 := Prod.ext (by show c.1 * (realAd F t).1 = 0; rw [hc1, zero_mul])
      (by show c.2 * (realAd F t).2 = 0; rw [snd_realAd, mul_zero])
    rw [smul_eq_mul, ← mul_assoc, h0, zero_mul]
  have hy : (fun i => evI F (ofInf F (y i))) = y := funext fun i => evI_ofInf (y i)
  have he : evI F (realAd F t * ((fun i => ofInf F (y i)) ⬝ᵥ b + ⅟(2 : AF F) * (realAd F t * (a ⬝ᵥ b)))) =
      t • ((y ⬝ᵥ fun i => evI F (b i)) +
        t • (evI F ⅟(2 : AF F) * ((fun i => evI F (a i)) ⬝ᵥ fun i => evI F (b i)))) := by
    rw [evI_mul, evI_add, evI_mul, evI_mul, evI_dot, evI_dot, hy, evI_realAd, Algebra.smul_def, Algebra.smul_def]
    ring
  have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (evI F (realAd F t * ((fun i => ofInf F (y i)) ⬝ᵥ b + ⅟(2 : AF F) * (realAd F t * (a ⬝ᵥ b))))) =
      t * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ fun i => evI F (b i)) +
        t ^ 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (evI F ⅟(2 : AF F) * ((fun i => evI F (a i)) ⬝ᵥ fun i => evI F (b i))) := by
    rw [he, map_smul, map_add, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hg : (fun i => evI F (((fun i => ofInf F (y i)) + realAd F t • a) i)) = y + t • fun i => evI F (a i) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [evI_add, evI_mul, evI_realAd, evI_ofInf, Algebra.smul_def]
  have hr : rInt F κ ((fun i => ofInf F (y i)) + realAd F t • a) = 1 := by
    refine rInt_eq_one _ fun i => ?_
    show (0 : FiniteAdeleRing (𝓞 F) F) + (realAd F t).2 * (a i).2 = 0
    rw [snd_realAd, zero_mul, add_zero]
  rw [hp, hψ.2.2 _ hAt, htr]
  unfold tens
  rw [hg, hr, mul_one]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n d X W M ψ hψ g h u _ hD y`. Use `set A : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u).1 i) with hA`. Use `set TY : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ fun i => evI F ((M.co.e u).2 i)) with hTY`. Use `set TC : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F ⅟(2 : AF F) * (A ⬝ᵥ fun i => evI F ((M.co.e u).2 i))) with hTC`. Establish `h1` using `hD (rInt F _) (rest_rInt g) (fun i => ofInf F (y i))`.

Establish `hfun : (fun t => M.heisLine ψ u t (tens (evI F) (g : _ → ℂ) (rInt F _)) (fun i => ofInf F (y i))) = fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * TY + t ^ 2 * TC : ℝ) : ℂ)) * g (y + t • A)`. Use function extensionality and compare the values at `t`. Unfold `Model.heisLine GlobalTheory.WeilM.Darboux.rho`. Rewrite using `[LinearEquiv.map_smul]`. Conclude with `schr_line ψ hψ g _ _ y t`.

Establish `hval : tens (evI F) (h : _ → ℂ) (rInt F _) (fun i => ofInf F (y i)) = h y`. Unfold `tens`. Rewrite using `[rInt_eq_one _ fun i => snd_ofInf (y i), mul_one]`. Use `congr 1`. Conclude with `funext fun i => evI_ofInf (y i)`.

Establish `hL : HasDerivAt (fun t : ℝ => t * TY + t ^ 2 * TC) TY 0`. Establish `h2` using `((hasDerivAt_id' (0 : ℝ)).mul_const TY).add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const TC)`. Conclude with `h2.congr_deriv (by simp)`. Establish `hE` using `(hL.ofReal_comp.const_mul (-(2 * Real.pi * Complex.I))).cexp`. Establish `hl : HasDerivAt (fun t : ℝ => y + t • A) A 0`.

Simplify using `using ((hasDerivAt_id' (0 : ℝ)).smul_const A).const_add y`. Establish `hG : HasDerivAt (fun t : ℝ => g (y + t • A)) (fderiv ℝ (g : _ → ℂ) y A) 0` using `(g.differentiableAt.hasFDerivAt).comp_hasDerivAt_of_eq 0 hl (by simp)`. Establish `hder` using `hE.mul hG`. Rewrite `h1` using `[hfun]`. Use `h1.unique hder` as an intermediate fact.

Rewrite `this` using `[hval]`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem heisLine_deriv_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (g h : SInf F (Fin n × Fin d)) (u : Matrix (Fin n) (Fin d) (AE F E)), At (evI F) u →
    ActsD (evI F) (M.heisLine ψ u) g h → ∀ (y : Fin n × Fin d → mixedEmbedding.mixedSpace F),
    h y = fderiv ℝ (g : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) y (fun i => evI F ((M.co.e u).1 i)) +
      (-(2 * Real.pi * Complex.I) *
        ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ fun i => evI F ((M.co.e u).2 i)) : ℝ) : ℂ)) * g y := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ g h u _ hD y
  set A : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u).1 i) with hA
  set TY : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ fun i => evI F ((M.co.e u).2 i)) with hTY
  set TC : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
    (evI F ⅟(2 : AF F) * (A ⬝ᵥ fun i => evI F ((M.co.e u).2 i))) with hTC
  have h1 := hD (rInt F _) (rest_rInt g) (fun i => ofInf F (y i))
  have hfun : (fun t => M.heisLine ψ u t (tens (evI F) (g : _ → ℂ) (rInt F _)) (fun i => ofInf F (y i))) =
      fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * TY + t ^ 2 * TC : ℝ) : ℂ)) * g (y + t • A) := by
    funext t
    unfold Model.heisLine GlobalTheory.WeilM.Darboux.rho
    rw [LinearEquiv.map_smul]
    exact schr_line ψ hψ g _ _ y t
  have hval : tens (evI F) (h : _ → ℂ) (rInt F _) (fun i => ofInf F (y i)) = h y := by
    unfold tens
    rw [rInt_eq_one _ fun i => snd_ofInf (y i), mul_one]
    congr 1
    exact funext fun i => evI_ofInf (y i)
  have hL : HasDerivAt (fun t : ℝ => t * TY + t ^ 2 * TC) TY 0 := by
    have h2 := ((hasDerivAt_id' (0 : ℝ)).mul_const TY).add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const TC)
    exact h2.congr_deriv (by simp)
  have hE := (hL.ofReal_comp.const_mul (-(2 * Real.pi * Complex.I))).cexp
  have hl : HasDerivAt (fun t : ℝ => y + t • A) A 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const A).const_add y
  have hG : HasDerivAt (fun t : ℝ => g (y + t • A)) (fderiv ℝ (g : _ → ℂ) y A) 0 :=
    (g.differentiableAt.hasFDerivAt).comp_hasDerivAt_of_eq 0 hl (by simp)
  have hder := hE.mul hG
  rw [hfun] at h1
  have := h1.unique hder
  rw [hval] at this
  rw [this]
  simp
  ring

end GlobalTheory.HeisDerivFormula
